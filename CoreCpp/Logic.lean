/-!
# A small logic language, for Unit VII

The logic paradigm has no counterpart in Core C++, so the course gives it a
language of its own, small enough to fit one lecture and written in the same
notation as the rest. A program is a set of Horn clauses, a query is a list of
atoms, and the meaning of a query is given by the SLD resolution judgment

    P, θ ⊢ G ⇒ θ'

read as, under the program P and the substitution θ, the goal list G succeeds
with the answer substitution θ'. Each rule is in the comment of the case that
implements it. The selected atom is always the leftmost one, and the clauses
are tried in the order they are written, which is the depth first search with
backtracking of Prolog. A depth bound on the derivation keeps the search
finite, so a left recursive program yields no answer instead of diverging.

Outside the language. Negation, the cut, assert and retract, arithmetic
beyond the built in `is` and the comparisons, and the occurs check is on,
unlike most Prolog systems.
-/

namespace CoreCpp
namespace Logic

/-- A term. A constant is a functor of no arguments, `fn "a" []`, and a list
is built from the functor `.` and the constant `[]`, as in Prolog. -/
inductive Term where
  /-- A logic variable, written with an uppercase initial in the source. -/
  | var (n : String)
  /-- An integer. -/
  | num (n : Int)
  /-- A compound term, the functor and its arguments. -/
  | fn  (f : String) (args : List Term)
  deriving Repr, BEq, Inhabited

/-- An atom, a predicate symbol applied to terms. The built in predicates
`is`, `<`, `>`, `<=`, `>=` and `=` are atoms like any other, and the
resolution judgment gives them rules of their own. -/
structure Atom where
  /-- The predicate symbol. -/
  pred : String
  /-- The arguments. -/
  args : List Term
  deriving Repr, BEq, Inhabited

/-- A Horn clause, `head :- body`. A fact is a clause with an empty body. -/
structure Clause where
  /-- The head of the clause. -/
  head : Atom
  /-- The body, the atoms that must succeed for the head to hold. -/
  body : List Atom
  deriving Repr, BEq, Inhabited

/-- A program, a list of clauses in the order they are written, which is the
order the search tries them. -/
abbrev LProgram := List Clause

/-- A substitution, a finite map from variables to terms. It is kept
triangular, so `resolve` follows the chain of a variable to its value. -/
abbrev Subst := List (String × Term)

/-! ## Printing -/

mutual

/-- The term as the source writes it, with lists in bracket notation. -/
partial def Term.toStr : Term → String
  | .var x => x
  | .num n => toString n
  | .fn "[]" [] => "[]"
  | .fn "." [h, t] =>
    let (xs, rest) := Term.listParts (.fn "." [h, t])
    match rest with
    | none => s!"[{", ".intercalate xs}]"
    | some r => s!"[{", ".intercalate xs}|{r.toStr}]"
  | .fn f [] => f
  | .fn f as => s!"{f}({", ".intercalate (as.map Term.toStr)})"

/-- The elements of a list term already printed, and the tail when the list
does not end in `[]`, as in `[H|T]`. -/
partial def Term.listParts : Term → List String × Option Term
  | .fn "." [h, tl] =>
    let (xs, rest) := Term.listParts tl
    (h.toStr :: xs, rest)
  | .fn "[]" [] => ([], none)
  | other => ([], some other)

end

instance : ToString Term := ⟨Term.toStr⟩

def Atom.toStr (a : Atom) : String :=
  if a.args.isEmpty then a.pred
  else s!"{a.pred}({", ".intercalate (a.args.map Term.toStr)})"

instance : ToString Atom := ⟨Atom.toStr⟩

/-! ## Substitution and unification -/

/-- The value of a term under θ, with every variable followed to the end of
its chain. -/
partial def resolve (θ : Subst) : Term → Term
  | .var x => match θ.lookup x with
    | some t => resolve θ t
    | none => .var x
  | .num n => .num n
  | .fn f as => .fn f (as.map (resolve θ))

/-- Whether the variable x occurs in the term under θ, the occurs check that
keeps a substitution acyclic. -/
partial def occurs (θ : Subst) (x : String) : Term → Bool
  | .var y =>
    x == y || (match θ.lookup y with | some t => occurs θ x t | none => false)
  | .num _ => false
  | .fn _ as => as.any (occurs θ x)

/-- The unification judgment, Robinson's algorithm with the occurs check.

    ─────────────────── (U-Var)         x not bound in θ, x does not occur in t
    θ ⊢ x ≐ t ⇒ θ[x ↦ t]

    ─────────────── (U-Num)             ────────────────────────── (U-Fn)
    θ ⊢ n ≐ n ⇒ θ                       θ ⊢ f(s₁…sₖ) ≐ f(t₁…tₖ) ⇒ θ'

where θ' unifies the arguments left to right. Nothing else unifies. -/
partial def unify (θ : Subst) : Term → Term → Option Subst
  | .var x, t =>
    match θ.lookup x with
    | some u => unify θ u t
    | none =>
      match t with
      | .var y =>
        if x == y then some θ
        else match θ.lookup y with
          | some u => unify θ (.var x) u
          | none => some ((x, .var y) :: θ)
      | _ => if occurs θ x t then none else some ((x, t) :: θ)
  | t, .var x => unify θ (.var x) t
  | .num a, .num b => if a == b then some θ else none
  | .fn f as, .fn g bs =>
    if f == g && as.length == bs.length then
      (as.zip bs).foldlM (fun θ (a, b) => unify θ a b) θ
    else none
  | _, _ => none

/-- Unification of two atoms, which is the unification of the terms that
carry their arguments. -/
def unifyAtom (θ : Subst) (a b : Atom) : Option Subst :=
  if a.pred == b.pred && a.args.length == b.args.length then
    unify θ (.fn a.pred a.args) (.fn b.pred b.args)
  else none

/-! ## Renaming apart -/

/-- Every variable of the term with the mark n, so that one use of a clause
shares no variable with another. -/
partial def renameTerm (n : Nat) : Term → Term
  | .var x => .var s!"{x}#{n}"
  | .num k => .num k
  | .fn f as => .fn f (as.map (renameTerm n))

def renameAtom (n : Nat) (a : Atom) : Atom :=
  ⟨a.pred, a.args.map (renameTerm n)⟩

/-- A fresh variant of the clause, the renaming apart the resolution rule
asks for. -/
def renameClause (n : Nat) (c : Clause) : Clause :=
  ⟨renameAtom n c.head, c.body.map (renameAtom n)⟩

/-! ## Arithmetic -/

/-- The value of an arithmetic term under θ, the function the built in `is`
and the comparisons use. A term that is not arithmetic, an unbound variable
among them, has no value, and the goal that asked for it fails. -/
partial def evalArith (θ : Subst) (t : Term) : Option Int :=
  match resolve θ t with
  | .num n => some n
  | .fn "+" [a, b] => do return (← evalArith θ a) + (← evalArith θ b)
  | .fn "-" [a, b] => do return (← evalArith θ a) - (← evalArith θ b)
  | .fn "*" [a, b] => do return (← evalArith θ a) * (← evalArith θ b)
  | .fn "-" [a] => do return -(← evalArith θ a)
  | .fn "/" [a, b] => do
    let n ← evalArith θ a
    let d ← evalArith θ b
    if d == 0 then none else return n.tdiv d
  | .fn "mod" [a, b] => do
    let n ← evalArith θ a
    let d ← evalArith θ b
    if d == 0 then none else return n.tmod d
  | _ => none

/-- The comparison the built in predicate names, or none when the predicate
is not a comparison. -/
def compareOp : String → Option (Int → Int → Bool)
  | ">" => some (· > ·)
  | "<" => some (· < ·)
  | ">=" => some (· ≥ ·)
  | "=<" => some (· ≤ ·)
  | "=:=" => some (· == ·)
  | "=\\=" => some (· != ·)
  | _ => none

/-! ## SLD resolution -/

mutual

/-- The answers of the goal list under the program, by SLD resolution with
the leftmost atom selected and the clauses tried in the order they are
written. The natural number is the remaining depth of the derivation, and the
state is the counter that renames clauses apart.

    ───────────── (SLD-Empty)
    P, θ ⊢ ε ⇒ θ

    (H :- B₁ … Bₘ) variante nova de uma cláusula de P
    θ ⊢ A ≐ H ⇒ θ₁    P, θ₁ ⊢ B₁ … Bₘ G ⇒ θ'
    ─────────────────────────────────────────────── (SLD-Resolve)
    P, θ ⊢ A G ⇒ θ'

    eval(θ, t) = n    θ ⊢ s ≐ n ⇒ θ₁    P, θ₁ ⊢ G ⇒ θ'
    ─────────────────────────────────────────────── (SLD-Is)
    P, θ ⊢ (s is t) G ⇒ θ'

    eval(θ, s) = m    eval(θ, t) = n    m ⋈ n    P, θ ⊢ G ⇒ θ'
    ───────────────────────────────────────────────────────── (SLD-Compare)
    P, θ ⊢ (s ⋈ t) G ⇒ θ'

    θ ⊢ s ≐ t ⇒ θ₁    P, θ₁ ⊢ G ⇒ θ'
    ──────────────────────────────── (SLD-Unify)
    P, θ ⊢ (s = t) G ⇒ θ'

A goal list with no derivation of depth at most the bound yields no answer,
which is how the implementation answers a left recursive program. -/
partial def solve (p : LProgram) : Nat → Subst → List Atom → StateM Nat (List Subst)
  | _, θ, [] => return [θ]
  | 0, _, _ :: _ => return []
  | d + 1, θ, a :: gs => do
    match a.pred, a.args with
    | "is", [s, t] =>
      match evalArith θ t with
      | none => return []
      | some n =>
        match unify θ s (.num n) with
        | none => return []
        | some θ₁ => solve p d θ₁ gs
    | "=", [s, t] =>
      match unify θ s t with
      | none => return []
      | some θ₁ => solve p d θ₁ gs
    | pred, [s, t] =>
      match compareOp pred with
      | some op =>
        match evalArith θ s, evalArith θ t with
        | some m, some n => if op m n then solve p d θ gs else return []
        | _, _ => return []
      | none => resolveAtom p d θ a gs
    | _, _ => resolveAtom p d θ a gs

/-- The clause rule of the judgment, tried on every clause of the program in
the order they are written, which is where backtracking happens. -/
partial def resolveAtom (p : LProgram) (d : Nat) (θ : Subst) (a : Atom)
    (gs : List Atom) : StateM Nat (List Subst) := do
  let mut answers : List Subst := []
  for c in p do
    let n ← get
    set (n + 1)
    let c' := renameClause n c
    match unifyAtom θ a c'.head with
    | none => pure ()
    | some θ₁ => answers := answers ++ (← solve p d θ₁ (c'.body ++ gs))
  return answers

end

/-- The variables of a term, in order of first occurrence. -/
partial def Term.vars : Term → List String
  | .var x => [x]
  | .num _ => []
  | .fn _ as => as.flatMap Term.vars

/-- The variables of a goal list, in order of first occurrence, without
repetition. These are the variables an answer reports. -/
def goalVars (gs : List Atom) : List String :=
  (gs.flatMap fun a => a.args.flatMap Term.vars).foldl
    (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The answer of a derivation, the value of each variable of the query. -/
def answerOf (θ : Subst) (vars : List String) : List (String × Term) :=
  vars.map fun x => (x, resolve θ (.var x))

/-- The answers of a query, at most `limit` of them, each the value of the
variables of the query. An empty list means the query failed, and a list with
one empty answer means it succeeded with nothing to report. -/
def query (p : LProgram) (gs : List Atom) (depth : Nat := 200) (limit : Nat := 10) :
    List (List (String × Term)) :=
  let vars := goalVars gs
  let answers := (solve p depth [] gs).run' 0
  (answers.map (answerOf · vars)).take limit


/-! ## Concrete syntax

A source file holds clauses and queries, in the notation of Prolog. A name
with a lowercase initial is a functor or a predicate symbol, a name with an
uppercase initial or an underscore is a variable, `:-` separates the head of a
clause from its body, `?-` opens a query, `%` opens a comment, and a full stop
ends both. The grammar below is the one the parser implements, one function
per nonterminal, as everywhere else in this project.

```
File    ::= Item*
Item    ::= Goal '.' | Goal ':-' Goals '.' | '?-' Goals '.'
Goals   ::= Goal ( ',' Goal )*
Goal    ::= Expr ( RelOp Expr )?
RelOp   ::= 'is' | '=' | '>' | '<' | '>=' | '=<' | '=:=' | '=\='
Expr    ::= MulExpr ( ( '+' | '-' ) MulExpr )*
MulExpr ::= Primary ( ( '*' | '/' | 'mod' ) Primary )*
Primary ::= Num | Var | Name ( '(' Expr ( ',' Expr )* ')' )?
          | '(' Expr ')' | '-' Primary | List
List    ::= '[' ']' | '[' Expr ( ',' Expr )* ( '|' Expr )? ']'
```
-/

namespace Parse

/-- A token of the logic language. -/
inductive LTok where
  /-- A name with a lowercase initial, a functor or a predicate symbol. -/
  | name (s : String)
  /-- A variable, written with an uppercase initial or an underscore. -/
  | vr   (s : String)
  /-- An integer literal. -/
  | num  (n : Int)
  /-- An operator or a piece of punctuation. -/
  | sym  (s : String)
  /-- The end of the input. -/
  | eof
  deriving Repr, BEq, Inhabited

def LTok.toStr : LTok → String
  | .name s | .vr s | .sym s => s
  | .num n => toString n
  | .eof => "<end of input>"

instance : ToString LTok := ⟨LTok.toStr⟩

def syms3 : List String := ["=:=", "=\\="]
def syms2 : List String := [":-", "?-", ">=", "=<"]
def syms1 : List String :=
  ["(", ")", "[", "]", ",", ".", "|", "+", "-", "*", "/", ">", "<", "="]

def isNameStart (c : Char) : Bool := c.isLower
def isVarStart (c : Char) : Bool := c.isUpper || c == '_'
def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

private def takeWhile (p : Char → Bool) : List Char → String × List Char
  | [] => ("", [])
  | c :: cs =>
    if p c then
      let (s, rest) := takeWhile p cs
      (String.singleton c ++ s, rest)
    else ("", c :: cs)

private def matchSym (ss : List String) (cs : List Char) : Option (String × List Char) :=
  ss.findSome? fun s =>
    if cs.take s.length == s.toList then some (s, cs.drop s.length) else none

private partial def skipLine : List Char → List Char
  | [] => []
  | '\n' :: cs => cs
  | _ :: cs => skipLine cs

/-- The lexer of the logic language, a finite automaton with the longest
match rule, as the Core C++ one. -/
partial def lexLoop (cs : List Char) (acc : Array LTok) : Except String (Array LTok) :=
  match cs with
  | [] => .ok (acc.push .eof)
  | c :: rest =>
    if c.isWhitespace then lexLoop rest acc
    else if c == '%' then lexLoop (skipLine rest) acc
    else if c.isDigit then
      let (ds, rest') := takeWhile Char.isDigit cs
      lexLoop rest' (acc.push (.num (Int.ofNat ds.toNat!)))
    else if isNameStart c then
      let (w, rest') := takeWhile isWordChar cs
      lexLoop rest' (acc.push (.name w))
    else if isVarStart c then
      let (w, rest') := takeWhile isWordChar cs
      lexLoop rest' (acc.push (.vr w))
    else
      match matchSym syms3 cs |>.orElse fun _ =>
            matchSym syms2 cs |>.orElse fun _ => matchSym syms1 cs with
      | some (s, rest') => lexLoop rest' (acc.push (.sym s))
      | none => .error s!"unexpected character '{c}'"

def lex (input : String) : Except String (Array LTok) :=
  lexLoop input.toList #[]

structure PState where
  toks : Array LTok
  pos  : Nat := 0

abbrev P := StateT PState (Except String)

def peek : P LTok := do
  let s ← get
  return s.toks.getD s.pos .eof

def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

def fail (msg : String) : P α := do
  let t ← peek
  let s ← get
  throw s!"syntax error at token {s.pos} ('{t}'): {msg}"

def expectSym (x : String) : P Unit := do
  if (← peek) == .sym x then advance else fail s!"expected '{x}'"

def acceptSym (x : String) : P Bool := do
  if (← peek) == .sym x then advance; return true else return false

/-- The infix relation the token names, when it is one. -/
def relOf : LTok → Option String
  | .name "is" => some "is"
  | .sym s => if ["=", ">", "<", ">=", "=<", "=:=", "=\\="].contains s then some s else none
  | _ => none

mutual

/-- `Expr ::= MulExpr ( ( '+' | '-' ) MulExpr )*` -/
partial def expr : P Term := do
  let mut l ← mulExpr
  repeat
    match ← peek with
    | .sym "+" => advance; let r ← mulExpr; l := .fn "+" [l, r]
    | .sym "-" => advance; let r ← mulExpr; l := .fn "-" [l, r]
    | _ => break
  return l

/-- `MulExpr ::= Primary ( ( '*' | '/' | 'mod' ) Primary )*` -/
partial def mulExpr : P Term := do
  let mut l ← primary
  repeat
    match ← peek with
    | .sym "*" => advance; let r ← primary; l := .fn "*" [l, r]
    | .sym "/" => advance; let r ← primary; l := .fn "/" [l, r]
    | .name "mod" => advance; let r ← primary; l := .fn "mod" [l, r]
    | _ => break
  return l

/-- `Primary ::= Num | Var | Name Args? | '(' Expr ')' | '-' Primary | List` -/
partial def primary : P Term := do
  match ← peek with
  | .num n => advance; return .num n
  | .vr x => advance; return .var x
  | .sym "-" => advance; return .fn "-" [← primary]
  | .sym "(" => advance; let e ← expr; expectSym ")"; return e
  | .sym "[" => advance; listTerm
  | .name f =>
    advance
    if ← acceptSym "(" then
      let mut as := [← expr]
      while ← acceptSym "," do
        as := as ++ [← expr]
      expectSym ")"
      return .fn f as
    else return .fn f []
  | _ => fail "expected a term"

/-- `List ::= ']' | Expr ( ',' Expr )* ( '|' Expr )? ']'`, after the `[`. -/
partial def listTerm : P Term := do
  if ← acceptSym "]" then return .fn "[]" []
  let mut items := [← expr]
  while ← acceptSym "," do
    items := items ++ [← expr]
  let tail ← if ← acceptSym "|" then expr else pure (.fn "[]" [])
  expectSym "]"
  return items.foldr (fun h t => .fn "." [h, t]) tail

end

/-- `Goal ::= Expr ( RelOp Expr )?`, an atom either way. -/
def goal : P Atom := do
  let l ← expr
  match relOf (← peek) with
  | some r =>
    advance
    let rhs ← expr
    return ⟨r, [l, rhs]⟩
  | none =>
    match l with
    | .fn f as => return ⟨f, as⟩
    | _ => fail "a goal is an atom, not a term"

/-- `Goals ::= Goal ( ',' Goal )*` -/
def goals : P (List Atom) := do
  let mut gs := [← goal]
  while ← acceptSym "," do
    gs := gs ++ [← goal]
  return gs

/-- One clause or one query, with the full stop that ends it. -/
def item : P (Clause ⊕ List Atom) := do
  if ← acceptSym "?-" then
    let gs ← goals
    expectSym "."
    return .inr gs
  let h ← goal
  if ← acceptSym ":-" then
    let b ← goals
    expectSym "."
    return .inl ⟨h, b⟩
  expectSym "."
  return .inl ⟨h, []⟩

/-- `File ::= Item*`, the clauses in order and the queries in order. -/
def file : P (LProgram × List (List Atom)) := do
  let mut cs : LProgram := []
  let mut qs : List (List Atom) := []
  while (← peek) != .eof do
    match ← item with
    | .inl c => cs := cs ++ [c]
    | .inr q => qs := qs ++ [q]
  return (cs, qs)

end Parse

/-- Reads a source file of the logic language, its clauses and its queries. -/
def parse (input : String) : Except String (LProgram × List (List Atom)) := do
  let toks ← Parse.lex input
  let (r, s) ← (Parse.file).run { toks }
  if s.toks.getD s.pos .eof == .eof then return r
  else throw s!"unconsumed input from token {s.pos}"

/-- One query with its answers, as the command line prints them. An answer
with no variables is `true`, and a query with no answer is `false`. -/
def answersToString (gs : List Atom) (answers : List (List (String × Term))) : String :=
  let header := s!"?- {", ".intercalate (gs.map Atom.toStr)}."
  if answers.isEmpty then s!"{header}\nfalse"
  else
    let lines := answers.map fun a =>
      if a.isEmpty then "true"
      else "; ".intercalate (a.map fun (x, t) => s!"{x} = {t}")
    s!"{header}\n{"\n".intercalate lines}"

end Logic
end CoreCpp
