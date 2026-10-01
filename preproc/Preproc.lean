/-!
# Preproc, the preprocessor of Core C++

A language of its own, run before the Core C++ compiler, and a valid input of
the preprocessor of `g++`. It reads a file as a sequence of lines and never
lexes or parses Core C++. The design is `preproc/ccpp-preproc.md`.

```
File  = Group ;
Group = { Line | Cond } ;
Line  = "#include" "<" Header ">" NL | "#define" FlagId NL | Text ;
Cond  = Test FlagId NL Group [ "#else" NL Group ] "#endif" NL ;
Test  = "#ifdef" | "#ifndef" ;
```

Every line satisfies the lexical rules, including the lines of a branch that
is not selected and the lines of every header. The output replaces each
`#include` by the preprocessed contents of the Core C++ header, and every other
directive line and every line of a branch that is not selected by an empty
line. It keeps the other text lines unchanged.
-/

namespace Preproc

/-- A position in a source file, for error messages. -/
structure Loc where
  file : String
  line : Nat

def Loc.err (l : Loc) (msg : String) : String := s!"{l.file}:{l.line}: {msg}"

inductive Directive where
  | include (h : String)
  | define (f : String)
  | ifdef (f : String)
  | ifndef (f : String)
  | else_
  | endif

inductive Line where
  | text (s : String)
  | dir (d : Directive)

/-- A parsed group. A conditional keeps whether it has an `#else`, so that the
output has one line for each line of the source. -/
inductive Item where
  | text (s : String)
  | include (loc : Loc) (h : String)
  | define (f : String)
  | cond (neg : Bool) (f : String) (thenI : List Item) (hasElse : Bool) (elseI : List Item)

/-! ## Lexical rules -/

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The words of a line, the maximal runs of letters, digits and `_`. -/
def words (cs : List Char) : List String :=
  let rec go : Nat → List Char → List String → List String
    | 0, _, acc => acc.reverse
    | _ + 1, [], acc => acc.reverse
    | k + 1, c :: cs, acc =>
      if isWordChar c then
        let w := c :: cs.takeWhile isWordChar
        go k (cs.dropWhile isWordChar) (String.ofList w :: acc)
      else go k cs acc
  go (cs.length + 1) cs []

def isInfix (pat : List Char) (cs : List Char) : Bool :=
  let rec go : Nat → List Char → Bool
    | 0, _ => false
    | _ + 1, [] => pat.isEmpty
    | k + 1, d :: ds => (d :: ds).take pat.length == pat || go k ds
  go (cs.length + 1) cs

/-- Rule 4. A flag has the prefix `CCPP_`, a nonempty rest of letters, digits and
`_`, and no `__`, since identifiers with `__` are reserved. -/
def isFlag (f : String) : Bool :=
  let cs := f.toList
  cs.take 5 == "CCPP_".toList && cs.length > 5 && cs.all isWordChar && !isInfix "__".toList cs

/-- Rule 3. No backslash, `/*`, `'` or `"`, which could splice lines, hide lines
in a comment, or open a literal. -/
def checkChars (loc : Loc) (cs : List Char) : Except String Unit := do
  if cs.contains '\\' then throw (loc.err "a backslash, which could splice lines")
  if isInfix "/*".toList cs then throw (loc.err "/*, which could hide lines in a comment")
  if cs.contains '\'' || cs.contains '"' then throw (loc.err "a quote, which could open a literal")

def isBlank (c : Char) : Bool := c == ' ' || c == '\t'

/-- The words of a directive after `#`, and the header of an `#include <h>`. -/
def directive (loc : Loc) (cs : List Char) : Except String Directive := do
  let cs := (cs.dropWhile isBlank).drop 1 |>.dropWhile isBlank
  let name := String.ofList (cs.takeWhile isWordChar)
  let rest := (cs.dropWhile isWordChar).dropWhile isBlank
  let only (d : Directive) : Except String Directive :=
    if rest.all isBlank then pure d else throw (loc.err s!"text after #{name}")
  let flag (mk : String → Directive) : Except String Directive := do
    let f := String.ofList (rest.takeWhile isWordChar)
    unless isFlag f do throw (loc.err s!"#{name} needs a flag CCPP_X without __, not '{f}'")
    unless ((rest.dropWhile isWordChar).all isBlank) do throw (loc.err s!"text after the flag of #{name}")
    return mk f
  match name with
  | "include" =>
    match rest with
    | '<' :: more =>
      let h := more.takeWhile (· != '>')
      let after := more.dropWhile (· != '>')
      unless after.take 1 == ['>'] && (after.drop 1).all isBlank && !h.isEmpty
          && h.all isWordChar do
        throw (loc.err "#include needs the form #include <header>")
      return .include (String.ofList h)
    | _ => throw (loc.err "#include needs the form #include <header>")
  | "define" => flag .define
  | "ifdef" => flag .ifdef
  | "ifndef" => flag .ifndef
  | "else" => only .else_
  | "endif" => only .endif
  | _ => throw (loc.err s!"#{name} is not a directive of Preproc")

/-- Rules 1 to 5 on one line. -/
def lexLine (loc : Loc) (s : String) : Except String Line := do
  let cs := s.toList
  checkChars loc cs
  match cs.dropWhile isBlank with
  | '#' :: _ => return .dir (← directive loc cs)
  | '%' :: ':' :: _ => throw (loc.err "a line that starts with %:, which C++ reads as #")
  | _ =>
    if (words cs).any (fun w => w.toList.take 5 == "CCPP_".toList) then
      throw (loc.err "a word with the prefix CCPP_, which is reserved for flags")
    return .text s

/-- The lines of a text, without the empty line after a final newline. -/
def lines (src : String) : List String :=
  let ls := src.splitOn "\n"
  if ls.getLast? == some "" then ls.dropLast else ls

/-! ## Parsing -/

inductive Stop where
  | eof
  | else_ (loc : Loc)
  | endif (loc : Loc)

mutual

/-- A group, up to the end of the input or the next `#else` or `#endif`. -/
def group : Nat → List (Loc × Line) → Except String (List Item × Stop × List (Loc × Line))
  | 0, _ => throw "Preproc fuel exhausted"
  | _ + 1, [] => return ([], .eof, [])
  | k + 1, (loc, l) :: ls =>
    match l with
    | .text s => do
      let (is, st, rest) ← group k ls
      return (.text s :: is, st, rest)
    | .dir (.include h) => do
      let (is, st, rest) ← group k ls
      return (.include loc h :: is, st, rest)
    | .dir (.define f) => do
      let (is, st, rest) ← group k ls
      return (.define f :: is, st, rest)
    | .dir (.ifdef f) => condRest k loc false f ls
    | .dir (.ifndef f) => condRest k loc true f ls
    | .dir .else_ => return ([], .else_ loc, ls)
    | .dir .endif => return ([], .endif loc, ls)

/-- The rest of a conditional after its test line, then the rest of the group. -/
def condRest : Nat → Loc → Bool → String → List (Loc × Line) →
    Except String (List Item × Stop × List (Loc × Line))
  | 0, _, _, _, _ => throw "Preproc fuel exhausted"
  | k + 1, loc, neg, f, ls => do
    let (thenI, st, rest) ← group k ls
    let (hasElse, elseI, rest) ← match st with
      | .endif _ => pure (false, [], rest)
      | .else_ _ => do
        let (elseI, st, rest) ← group k rest
        match st with
        | .endif _ => pure (true, elseI, rest)
        | .else_ l => throw (l.err "a second #else")
        | .eof => throw (loc.err "#ifdef or #ifndef without #endif")
      | .eof => throw (loc.err "#ifdef or #ifndef without #endif")
    let (is, st, rest) ← group k rest
    return (.cond neg f thenI hasElse elseI :: is, st, rest)

end

/-- The items of a file, after the lexical rules on every line. -/
def parse (file src : String) : Except String (List Item) := do
  let ls ← (lines src).zipIdx.mapM fun (s, i) => do
    let loc : Loc := ⟨file, i + 1⟩
    return (loc, ← lexLine loc s)
  let (is, st, _) ← group (2 * ls.length + 2) ls
  match st with
  | .eof => return is
  | .else_ l => throw (l.err "#else without #ifdef or #ifndef")
  | .endif l => throw (l.err "#endif without #ifdef or #ifndef")

/-! ## Meaning

The judgement φ ⊢ G ⇒ t, φ′ of the design, with t a list of output lines. -/

/-- The number of source lines of a group, for the empty lines of a branch that
is not selected. -/
partial def Item.size : Item → Nat
  | .cond _ _ t hasElse e =>
    2 + (t.map Item.size).sum + (if hasElse then 1 + (e.map Item.size).sum else 0)
  | _ => 1

/-- An output line, and whether it comes from a header. -/
abbrev OutLine := String × Bool

def blank (is : List Item) : List OutLine := List.replicate ((is.map Item.size).sum) ("", false)

/-- The environment of the translation, the directory of the Core C++ headers
and the depth of inclusion, which bounds a cycle of headers without a guard. -/
structure Env where
  includeDir : System.FilePath
  depth : Nat := 0

abbrev M := ExceptT String IO

mutual

/-- The judgement φ ⊢ G ⇒ t, φ′ on a group, item by item, threading φ. -/
partial def run (env : Env) (φ : List String) : List Item → M (List OutLine × List String)
  | [] => return ([], φ)
  | i :: is => do
    let (t, φ) ← runItem env φ i
    let (ts, φ) ← run env φ is
    return (t ++ ts, φ)

/-- The judgement on one item.

```
──────────────────────────── (P-Define)
φ ⊢ #define F ⇒ ε, φ ∪ {F}

φ ⊢ H(h) ⇒ t, φ′
──────────────────────────── (P-Include)
φ ⊢ #include <h> ⇒ t, φ′

F ∈ φ    φ ⊢ G₁ ⇒ t, φ′
─────────────────────────────────────── (P-IfdefT)
φ ⊢ #ifdef F G₁ #else G₂ #endif ⇒ t, φ′

F ∉ φ    φ ⊢ G₂ ⇒ t, φ′
─────────────────────────────────────── (P-IfdefF)
φ ⊢ #ifdef F G₁ #else G₂ #endif ⇒ t, φ′
```

The directive `#ifndef` swaps the premises. A text line gives itself, marked
when it comes from a header. An `#include` gives the output of the header.
Every other directive line and every line of a branch that is not selected
gives an empty line. -/
partial def runItem (env : Env) (φ : List String) : Item → M (List OutLine × List String)
  | .text s => return ([(s, env.depth > 0)], φ)
  -- (P-Define)  φ ⊢ #define F ⇒ ε, φ ∪ {F}
  | .define f => return ([("", false)], if φ.contains f then φ else φ ++ [f])
  -- (P-Include)  φ ⊢ H(h) ⇒ t, φ′ gives φ ⊢ #include <h> ⇒ t, φ′
  | .include loc h => do
    if env.depth ≥ 64 then throw (loc.err s!"headers nested more than 64 deep at <{h}>")
    let path := env.includeDir / h
    unless ← path.pathExists do throw (loc.err s!"<{h}> is not a header of Core C++")
    let is ← match parse path.toString (← IO.FS.readFile path) with
      | .ok is => pure is
      | .error e => throw e
    run { env with depth := env.depth + 1 } φ is
  -- (P-IfdefT), (P-IfdefF), and the same with the premises swapped for #ifndef
  | .cond neg f thenI hasElse elseI => do
    let selected := (φ.contains f) != neg
    let (t, φ) ← if selected then run env φ thenI else pure (blank thenI, φ)
    let (e, φ) ← if selected then pure (blank elseI, φ) else run env φ elseI
    return ([("", false)] ++ t ++ (if hasElse then [("", false)] ++ e else []) ++ [("", false)], φ)

end

/-- The lines of the output T(p) of a file under the flags φ₀, each marked with
whether it comes from a header. -/
def translateLines (includeDir : System.FilePath) (φ₀ : List String) (file src : String) :
    IO (Except String (List OutLine)) := do
  match parse file src with
  | .error e => return .error e
  | .ok is =>
    match ← (run ⟨includeDir, 0⟩ φ₀ is).run with
    | .ok (t, _) => return .ok t
    | .error e => return .error e

/-- The output T(p) of a file under the flags φ₀. -/
def translate (includeDir : System.FilePath) (φ₀ : List String) (file src : String) :
    IO (Except String String) := do
  return (← translateLines includeDir φ₀ file src).map fun t =>
    "\n".intercalate (t.map (·.1)) ++ "\n"

end Preproc
