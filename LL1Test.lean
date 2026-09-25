import CoreCpp.LL1

/-!
# Tests of the LL(1) construction on published grammars

Each grammar comes from a public source, with the sets, table, derivation or
conflict the source gives. Production numbers of the sources start at 1, and
indices here start at 0. `ε` is not a member of the sets computed here, whose
nullable nonterminals are listed apart. Run with `lake env lean LL1Test.lean`.

* Wikipedia, LL parser, https://en.wikipedia.org/wiki/LL_parser
* Hovemeyer, Lecture 9, LL(1) parsing, Johns Hopkins 601.428/628, 2022,
  https://jhucompilers.github.io/fall2022/lectures/lecture09-public.pdf
-/

open CoreCpp.LL1

/-- A grammar in BNF over string terminals. A name is a nonterminal when it is
the left side of some production. -/
def bnf (start : String) (ps : List (String × List String)) : Grammar String :=
  let nts := ps.map (·.1)
  ⟨start, ps.map fun (A, rhs) => ⟨A, rhs.map fun x => if nts.contains x then .n x else .t x⟩⟩

def setEq [BEq α] (xs ys : List α) : Bool := xs.all ys.contains && ys.all xs.contains

def tokens (s : String) : List String := (s.splitOn " ").filter (· != "")

def run (g : Grammar String) (s : String) : Except String (List Nat) :=
  g.parse g.table id (tokens s)

/-! ## Wikipedia, the grammar of the section "Concrete example" -/

def wiki : Grammar String := bnf "S" [("S", ["F"]), ("S", ["(", "S", "+", "F", ")"]), ("F", ["a"])]

-- The table of the article, `S` with `(` gives 2, `S` with `a` gives 1, `F` with `a` gives 3.
#guard setEq wiki.table [(("S", some "("), [1]), (("S", some "a"), [0]), (("F", some "a"), [2])]
#guard wiki.isLL1
-- The input `( a + a )` has the rule sequence [2, 1, 3, 3] of the article.
#guard (run wiki "( a + a )").toOption == some [1, 0, 2, 2]
#guard (run wiki "( a + )").toOption.isNone
#guard (run wiki "a a").toOption.isNone

/-! ## Wikipedia, the two grammars the article gives as not LL(1) -/

def wikiConflict1 : Grammar String := bnf "S" [("S", ["A", "a", "b"]), ("A", ["a"]), ("A", [])]

-- FIRST(A) is {a, ε} and FOLLOW(A) is {a}, so `A` with `a` selects both productions.
#guard setEq (wikiConflict1.first.get "A") ["a"]
#guard wikiConflict1.nullable.contains "A"
#guard setEq (wikiConflict1.follow.get "A") [some "a"]
#guard !wikiConflict1.isLL1
#guard wikiConflict1.conflicts.map (·.1) == [("A", some "a")]

def wikiConflict2 : Grammar String := bnf "S" [
  ("S", ["A"]), ("S", ["B"]),
  ("A", ["a", "A", "b"]), ("A", []),
  ("B", ["a", "B", "b", "b"]), ("B", [])]

#guard !wikiConflict2.isLL1
#guard setEq (wikiConflict2.conflicts.map (·.1)) [("S", some "a"), ("S", none)]

/-! ## Hovemeyer, the FIRST example -/

def jhuFirst : Grammar String := bnf "A" [
  ("A", ["a"]), ("A", ["B"]), ("A", ["C"]),
  ("B", ["b"]), ("B", []),
  ("C", ["c", "e"]), ("C", ["d", "e"])]

-- FIRST(A) = {a, b, c, d, ε}.
#guard setEq (jhuFirst.first.get "A") ["a", "b", "c", "d"]
#guard jhuFirst.nullable.contains "A"

/-! ## Hovemeyer, the FOLLOW example -/

def jhuFollow : Grammar String := bnf "A" [
  ("A", ["a", "B", "c"]), ("A", ["C"]),
  ("C", ["d", "B", "G", "f"]),
  ("B", ["g"]),
  ("G", ["h"]), ("G", [])]

-- FOLLOW(A) = {eof} and FOLLOW(B) = {c, f, h}.
#guard setEq (jhuFollow.follow.get "A") [none]
#guard setEq (jhuFollow.follow.get "B") [some "c", some "f", some "h"]

/-! ## Hovemeyer, the expression grammar, its sets and its table -/

def jhuExpr : Grammar String := bnf "E" [
  ("E", ["T", "E'"]),
  ("E'", ["+", "T", "E'"]), ("E'", ["-", "T", "E'"]), ("E'", []),
  ("T", ["F", "T'"]),
  ("T'", ["*", "F", "T'"]), ("T'", ["/", "F", "T'"]), ("T'", []),
  ("F", ["i"]), ("F", ["n"])]

#guard setEq (jhuExpr.first.get "E") ["i", "n"]
#guard setEq (jhuExpr.first.get "E'") ["+", "-"]
#guard setEq (jhuExpr.first.get "T") ["i", "n"]
#guard setEq (jhuExpr.first.get "T'") ["*", "/"]
#guard setEq (jhuExpr.first.get "F") ["i", "n"]
#guard setEq jhuExpr.nullable ["E'", "T'"]
#guard setEq (jhuExpr.follow.get "E") [none]
#guard setEq (jhuExpr.follow.get "E'") [none]
#guard setEq (jhuExpr.follow.get "T") [some "+", some "-", none]
#guard setEq (jhuExpr.follow.get "T'") [some "+", some "-", none]
#guard setEq (jhuExpr.follow.get "F") [some "*", some "/", some "+", some "-", none]

-- The table of the lecture, row by row.
#guard setEq jhuExpr.table [
  (("E", some "i"), [0]), (("E", some "n"), [0]),
  (("E'", some "+"), [1]), (("E'", some "-"), [2]), (("E'", none), [3]),
  (("T", some "i"), [4]), (("T", some "n"), [4]),
  (("T'", some "+"), [7]), (("T'", some "-"), [7]), (("T'", some "*"), [5]),
  (("T'", some "/"), [6]), (("T'", none), [7]),
  (("F", some "i"), [8]), (("F", some "n"), [9])]
#guard jhuExpr.isLL1

-- The leftmost derivation of `i + n * i`.
#guard (run jhuExpr "i + n * i").toOption == some [0, 4, 8, 7, 1, 4, 9, 5, 8, 7, 3]
#guard (run jhuExpr "i + * n").toOption.isNone
#guard (run jhuExpr "").toOption.isNone
#guard (jhuExpr.tree (tokens "i - n") [0, 4, 8, 7, 2, 4, 9, 7, 3]).isSome

