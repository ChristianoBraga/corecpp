import CoreCpp.LL1

/-!
# Grammars in EBNF files

The notation of the files, a variant of ISO/IEC 14977 with concatenation by
juxtaposition.

    grammar = { rule } ;
    rule    = identifier "=" alt ";" ;
    alt     = seq { "|" seq } ;
    seq     = { factor } ;
    factor  = identifier | terminal | "[" alt "]" | "{" alt "}" | "(" alt ")" ;

A terminal is written between double or single quotes. An identifier that is
the left side of some rule is a nonterminal, and any other identifier is a
token class, a terminal such as `ident` or `NAME` that the scanner produces.
`[ X ]` is an option, `{ X }` a repetition, and an empty sequence is ε.
Comments are written `(* … *)`. The first rule gives the start symbol unless
the caller names another.
-/

namespace CoreCpp.EbnfFile

open CoreCpp.LL1

/-! ## Reading -/

inductive Tok where
  | ident (s : String)
  | term (s : String)
  | sym (c : Char)
  deriving Repr, BEq, Inhabited

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The tokens of an EBNF text. -/
def tokens (src : String) : Except String (List Tok) :=
  let rec go : Nat → List Char → List Tok → Except String (List Tok)
    | 0, _, acc => .ok acc.reverse
    | _ + 1, [], acc => .ok acc.reverse
    | k + 1, '(' :: '*' :: cs, acc =>
      let rec skip : Nat → List Char → Option (List Char)
        | 0, _ => none
        | _ + 1, [] => none
        | _ + 1, '*' :: ')' :: cs => some cs
        | j + 1, _ :: cs => skip j cs
      match skip (cs.length + 1) cs with
      | some rest => go k rest acc
      | none => .error "unclosed comment"
    | k + 1, c :: cs, acc =>
      if c.isWhitespace then go k cs acc
      else if c == '"' || c == '\'' then
        let body := cs.takeWhile (· != c)
        match cs.drop body.length with
        | _ :: rest => go k rest (.term (String.ofList body) :: acc)
        | [] => .error "unclosed terminal"
      else if c.isAlpha || c == '_' then
        let body := cs.takeWhile isIdentChar
        go k (cs.drop body.length) (.ident (String.ofList (c :: body)) :: acc)
      else if "=|[]{}();".contains c then go k cs (.sym c :: acc)
      else .error s!"unexpected character {c}"
  go (src.length + 1) src.toList []

abbrev P := StateT (List Tok) (Except String)

def peek : P (Option Tok) := return (← get).head?

def next : P Tok := do
  match ← get with
  | t :: ts => set ts; return t
  | [] => throw "unexpected end of grammar"

def expect (c : Char) : P Unit := do
  match ← next with
  | .sym d => if c == d then return else throw s!"expected {c}, found {d}"
  | t => throw s!"expected {c}, found {repr t}"

mutual

partial def alt : P (Ebnf String) := do
  let mut alts := [← seq]
  while (← peek) == some (.sym '|') do
    discard next
    alts := alts ++ [← seq]
  return match alts with
    | [a] => a
    | _ => .alt alts

partial def seq : P (Ebnf String) := do
  let mut items : List (Ebnf String) := []
  repeat
    match ← peek with
    | some (.ident _) | some (.term _) | some (.sym '[') | some (.sym '{') | some (.sym '(') =>
      items := items ++ [← factor]
    | _ => break
  return match items with
    | [e] => e
    | _ => .seq items

partial def factor : P (Ebnf String) := do
  match ← next with
  | .ident s => return .n s
  | .term s => return .t s
  | .sym '[' => let e ← alt; expect ']'; return .opt e
  | .sym '{' => let e ← alt; expect '}'; return .star e
  | .sym '(' =>
    let e ← alt; expect ')'
    -- A group of one alternative is that alternative. A group of several
    -- stays an alternative, which becomes an auxiliary nonterminal.
    return e
  | t => throw s!"unexpected {repr t}"

end

partial def rules : P (List (Rule String)) := do
  let mut acc : List (Rule String) := []
  while (← peek).isSome do
    match ← next with
    | .ident name =>
      expect '='
      let e ← alt
      expect ';'
      acc := acc ++ [⟨name, e⟩]
    | t => throw s!"expected a rule name, found {repr t}"
  return acc

mutual

/-- Identifiers without a rule become token classes. -/
def resolve (defined : List String) : Ebnf String → Ebnf String
  | .t a => .t a
  | .n A => if defined.contains A then .n A else .t A
  | .seq es => .seq (resolveAll defined es)
  | .alt es => .alt (resolveAll defined es)
  | .star e => .star (resolve defined e)
  | .opt e => .opt (resolve defined e)

def resolveAll (defined : List String) : List (Ebnf String) → List (Ebnf String)
  | [] => []
  | e :: es => resolve defined e :: resolveAll defined es

end

/-- The rules of an EBNF text. -/
def parse (src : String) : Except String (List (Rule String)) := do
  let (rs, rest) ← rules.run (← tokens src)
  unless rest.isEmpty do throw "text after the last rule"
  let defined := rs.map (·.lhs)
  return rs.map fun r => ⟨r.lhs, resolve defined r.rhs⟩

/-- The rules of an EBNF file. -/
def load (path : System.FilePath) : IO (List (Rule String)) := do
  match parse (← IO.FS.readFile path) with
  | .ok rs => return rs
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- The grammar of an EBNF file, translated directly to BNF or, with `dfa`,
through one DFA per rule. The start symbol is `start`, by default the left
side of the first rule. -/
def loadGrammar (path : System.FilePath) (start : Option String := none) (dfa := false) :
    IO (Grammar String) := do
  let rs ← load path
  let some first := rs.head? | throw (IO.userError s!"{path}: no rule")
  let s := start.getD first.lhs
  return if dfa then translateDfa s rs else translate s rs

/-! ## Printing -/

def quote (a : String) : String :=
  if a.contains '"' then s!"'{a}'" else s!"\"{a}\""

mutual

/-- An expression in EBNF. Token classes print as bare identifiers. A nested
alternative is always parenthesised, so reading the text back gives the same
auxiliary nonterminals. -/
def render (classes : List String) : Ebnf String → String
  | .t a => if classes.contains a then a else quote a
  | .n A => A
  | .seq es => " ".intercalate (renderAll classes es)
  | .alt es => "( " ++ " | ".intercalate (renderAll classes es) ++ " )"
  | .star e => "{ " ++ render classes e ++ " }"
  | .opt e => "[ " ++ render classes e ++ " ]"

def renderAll (classes : List String) : List (Ebnf String) → List String
  | [] => []
  | e :: es => render classes e :: renderAll classes es

end

/-- A rule in EBNF, one alternative per line when the right side is an
alternative. -/
def renderRule (classes : List String) (r : Rule String) : String :=
  match r.rhs with
  | .alt es =>
    let pad := "".pushn ' ' (r.lhs.length + 1)
    s!"{r.lhs} = " ++ s!"\n{pad}| ".intercalate (renderAll classes es) ++ s!"\n{pad};"
  | e => s!"{r.lhs} = {render classes e} ;"

def renderRules (classes : List String) (rs : List (Rule String)) : String :=
  "\n".intercalate (rs.map (renderRule classes)) ++ "\n"

/-! ## A scanner driven by the grammar -/

/-- The terminals of a grammar that are not token classes. -/
def literals (g : Grammar String) (classes : List String) : List String :=
  g.terminals.filter (!classes.contains ·)

/-- A scanner for the programs of a grammar. White space separates tokens. A
word of letters, digits and `_` that starts with a letter is a literal of the
grammar when it spells one, with `fold` ignoring case, and the class `ident`
otherwise. A run of digits is the class `number`. Any other text is the
longest literal of the grammar that starts there. -/
def scan (g : Grammar String) (classes : List String) (ident number : String)
    (fold : Bool) (src : String) : Except String (List String) :=
  let lits := literals g classes
  let words := lits.filter fun s => s.any Char.isAlpha
  let syms := (lits.filter fun s => !s.any Char.isAlpha).mergeSort (·.length ≥ ·.length)
  let norm (w : String) := if fold then w.toLower else w
  let rec go : Nat → List Char → List String → Except String (List String)
    | 0, _, acc => .ok acc.reverse
    | _ + 1, [], acc => .ok acc.reverse
    | k + 1, c :: cs, acc =>
      if c.isWhitespace then go k cs acc
      else if c.isAlpha then
        let w := String.ofList (c :: cs.takeWhile isIdentChar)
        let rest := cs.dropWhile isIdentChar
        match words.find? (norm · == norm w) with
        | some kw => go k rest (kw :: acc)
        | none => go k rest (ident :: acc)
      else if c.isDigit then go k (cs.dropWhile Char.isDigit) (number :: acc)
      else
        match syms.find? (fun s => (c :: cs).take s.length == s.toList) with
        | some s => go k ((c :: cs).drop s.length) (s :: acc)
        | none => .error s!"unexpected character {c}"
  go (src.length + 1) src.toList []

end CoreCpp.EbnfFile
