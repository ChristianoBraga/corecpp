import CoreCpp.Ebnf

/-!
# The LL(1) construction on the grammars of three languages of Wirth

The grammars are `pl0.ebnf`, `oberon0.ebnf`, `oberon0-factored.ebnf` and
`oberon07.ebnf` of `tests/ll1/grammars/`, and the programs are the files of
`tests/ll1/programs/pl0/` and `tests/ll1/programs/oberon0/`. Run from the root
of the repository with `lake env lean tests/ll1/Wirth.lean`.

* PL/0, Wikipedia, https://en.wikipedia.org/wiki/PL/0, sections Grammar and
  Examples.
* Oberon-0, Wirth, Compiler Construction, revised edition of May 2017,
  chapter 6, p. 30, with the module `Samples` of the same page,
  https://people.inf.ethz.ch/wirth/CompilerConstruction/CompilerConstruction1.pdf
* Oberon-07, Wirth, The Programming Language Oberon, revision 3.5.2016,
  Appendix, https://people.inf.ethz.ch/wirth/Oberon/Oberon07.Report.pdf
-/

open CoreCpp.LL1 CoreCpp.EbnfFile

def grammar (name start : String) : IO (Grammar String) :=
  loadGrammar s!"tests/ll1/grammars/{name}.ebnf" (some start)

def classes : List String := ["ident", "number", "string"]

/-- Whether the program of a file parses. PL/0 keywords ignore case. -/
def accepts (g : Grammar String) (fold : Bool) (path : String) : IO Bool := do
  match scan g classes "ident" "number" fold (← IO.FS.readFile s!"tests/ll1/programs/{path}") with
  | .ok toks => return (g.parse g.table id toks).toOption.isSome
  | .error _ => return false

def setEq [BEq α] (xs ys : List α) : Bool := xs.all ys.contains && ys.all xs.contains

/-- The conflicts, each named by its rule and lookahead, without the index of
the auxiliary nonterminal. -/
def conflictsAt (g : Grammar String) : List (String × Look String) :=
  g.conflicts.map fun ((A, a), _) => ((A.splitOn ".").head!, a)

def check (b : Bool) (what : String) : IO Unit :=
  unless b do throw (IO.userError s!"failed: {what}")

/-! ## PL/0 -/

#eval show IO Unit from do
  let g ← grammar "pl0" "program"
  check g.isLL1 "LL(1)"
  check (← accepts g true "pl0/squares.pl0") "squares"
  check (← accepts g true "pl0/compilerbau.pl0") "compilerbau"
  -- The primes program writes `write arg`, which the grammar lacks. The
  -- article says that `write` corresponds to `!`.
  check (!(← accepts g true "pl0/primes.pl0")) "primes rejected"
  check (← accepts g true "pl0/primes-bang.pl0") "primes with !"
  check (!(← accepts g true "pl0/syntax-error.pl0")) "syntax error"
  IO.println "pl0 ok"

/-! ## Oberon-0 -/

#eval show IO Unit from do
  let g ← grammar "oberon0" "module"
  -- As published, assignment and ProcedureCall both start with ident, the
  -- only conflict of the grammar.
  check (conflictsAt g == [("statement", some "ident")]) "one conflict"
  let f ← grammar "oberon0-factored" "module"
  check f.isLL1 "factored LL(1)"
  -- The module of the book uses three forms outside the syntax of the same
  -- page, the export mark `*`, the function call `eot()` in a factor and the
  -- typing slip `x.4`. Without them the module parses.
  check (!(← accepts f false "oberon0/samples.mod")) "samples rejected"
  check (← accepts f false "oberon0/samples-fixed.mod") "samples fixed"
  IO.println "oberon0 ok"

/-! ## Oberon-07 -/

#eval show IO Unit from do
  let g ← grammar "oberon07" "module"
  -- Three conflicts. In statement, assignment and ProcedureCall both start
  -- with a designator. In qualident, [ident "."] ident cannot tell a module
  -- prefix from the identifier itself on ident. In designator, the selector
  -- "(" qualident ")" of a type guard and ActualParameters both start with (.
  check (setEq (conflictsAt g)
    [("statement", some "ident"), ("designator", some "("), ("qualident", some "ident")]) "conflicts"
  IO.println "oberon07 ok"
