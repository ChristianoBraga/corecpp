import CoreCpp.Ebnf

/-!
# The LL(1) construction on the grammars of Wikipedia and Hovemeyer

The grammars are the files `tests/ll1/grammars/wikipedia-*.ebnf` and
`tests/ll1/grammars/hovemeyer-*.ebnf`, and the sentences are the files of
`tests/ll1/programs/wikipedia/` and `tests/ll1/programs/hovemeyer/`. The
expected sets, tables, derivations and conflicts are those of the sources.
Production numbers of the sources start at 1, and indices here start at 0.
`ε` is not a member of the computed FIRST sets, and the nullable nonterminals
are listed apart. Run from the root of the repository with
`lake env lean tests/ll1/Classic.lean`.
-/

open CoreCpp.LL1 CoreCpp.EbnfFile

def grammar (name : String) : IO (Grammar String) :=
  loadGrammar s!"tests/ll1/grammars/{name}.ebnf"

def sentence (g : Grammar String) (path : String) : IO (Except String (List Nat)) := do
  match scan g [] "ident" "number" false (← IO.FS.readFile s!"tests/ll1/programs/{path}") with
  | .ok toks => return g.parse g.table id toks
  | .error e => return .error e

def setEq [BEq α] (xs ys : List α) : Bool := xs.all ys.contains && ys.all xs.contains

def check (b : Bool) (what : String) : IO Unit :=
  unless b do throw (IO.userError s!"failed: {what}")

/-! ## Wikipedia, LL parser -/

#eval show IO Unit from do
  let g ← grammar "wikipedia-paren"
  -- `S` with `(` gives rule 2, `S` with `a` rule 1, `F` with `a` rule 3.
  check (setEq g.table [(("S", some "("), [1]), (("S", some "a"), [0]), (("F", some "a"), [2])]) "table"
  check g.isLL1 "LL(1)"
  -- The input `( a + a )` has the rule sequence [2, 1, 3, 3] of the article.
  check ((← sentence g "wikipedia/sum.txt").toOption == some [1, 0, 2, 2]) "derivation"
  check (← sentence g "wikipedia/missing-operand.txt").toOption.isNone "missing operand"
  check (← sentence g "wikipedia/two-atoms.txt").toOption.isNone "two atoms"
  IO.println "wikipedia-paren ok"

#eval show IO Unit from do
  let g ← grammar "wikipedia-conflict1"
  -- FIRST(A) is {a, ε} and FOLLOW(A) is {a}, so `A` with `a` selects both.
  check (setEq (g.first.get "A") ["a"]) "FIRST"
  check (g.nullable.contains "A") "nullable"
  check (setEq (g.follow.get "A") [some "a"]) "FOLLOW"
  check (g.conflicts.map (·.1) == [("A", some "a")]) "conflict"
  IO.println "wikipedia-conflict1 ok"

#eval show IO Unit from do
  let g ← grammar "wikipedia-conflict2"
  check (setEq (g.conflicts.map (·.1)) [("S", some "a"), ("S", none)]) "conflicts"
  IO.println "wikipedia-conflict2 ok"

/-! ## Hovemeyer, lecture 9 -/

#eval show IO Unit from do
  let g ← grammar "hovemeyer-first"
  -- FIRST(A) = {a, b, c, d, ε}.
  check (setEq (g.first.get "A") ["a", "b", "c", "d"]) "FIRST"
  check (g.nullable.contains "A") "nullable"
  IO.println "hovemeyer-first ok"

#eval show IO Unit from do
  let g ← grammar "hovemeyer-follow"
  -- FOLLOW(A) = {eof} and FOLLOW(B) = {c, f, h}.
  check (setEq (g.follow.get "A") [none]) "FOLLOW(A)"
  check (setEq (g.follow.get "B") [some "c", some "f", some "h"]) "FOLLOW(B)"
  IO.println "hovemeyer-follow ok"

#eval show IO Unit from do
  let g ← grammar "hovemeyer-expr"
  check (setEq (g.first.get "E") ["i", "n"]) "FIRST(E)"
  check (setEq (g.first.get "Eprime") ["+", "-"]) "FIRST(E')"
  check (setEq (g.first.get "T") ["i", "n"]) "FIRST(T)"
  check (setEq (g.first.get "Tprime") ["*", "/"]) "FIRST(T')"
  check (setEq (g.first.get "F") ["i", "n"]) "FIRST(F)"
  check (setEq g.nullable ["Eprime", "Tprime"]) "nullable"
  check (setEq (g.follow.get "E") [none]) "FOLLOW(E)"
  check (setEq (g.follow.get "Eprime") [none]) "FOLLOW(E')"
  check (setEq (g.follow.get "T") [some "+", some "-", none]) "FOLLOW(T)"
  check (setEq (g.follow.get "Tprime") [some "+", some "-", none]) "FOLLOW(T')"
  check (setEq (g.follow.get "F") [some "*", some "/", some "+", some "-", none]) "FOLLOW(F)"
  -- The table of the lecture, row by row.
  check (setEq g.table [
    (("E", some "i"), [0]), (("E", some "n"), [0]),
    (("Eprime", some "+"), [1]), (("Eprime", some "-"), [2]), (("Eprime", none), [3]),
    (("T", some "i"), [4]), (("T", some "n"), [4]),
    (("Tprime", some "+"), [7]), (("Tprime", some "-"), [7]), (("Tprime", some "*"), [5]),
    (("Tprime", some "/"), [6]), (("Tprime", none), [7]),
    (("F", some "i"), [8]), (("F", some "n"), [9])]) "table"
  check g.isLL1 "LL(1)"
  check ((← sentence g "hovemeyer/sum-product.txt").toOption ==
    some [0, 4, 8, 7, 1, 4, 9, 5, 8, 7, 3]) "derivation"
  check (← sentence g "hovemeyer/two-operators.txt").toOption.isNone "two operators"
  check (← sentence g "hovemeyer/empty.txt").toOption.isNone "empty"
  match ← sentence g "hovemeyer/difference.txt" with
  | .ok d =>
    let toks := (scan g [] "ident" "number" false "i - n").toOption.get!
    check (g.tree toks d).isSome "tree"
  | .error e => throw (IO.userError e)
  IO.println "hovemeyer-expr ok"
