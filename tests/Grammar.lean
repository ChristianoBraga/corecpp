import CoreCpp

/-!
# The grammar of Core C++ from its EBNF file, a round trip

`grammar/core-cpp.ebnf` is the source of the grammar. `lake exe ebnf2lean`
writes it as `CoreCpp/GrammarRules.lean`, whose `rules` the theorem
`isLL1_grammar` is about. The checks below confirm that the committed module
is the output of the generator on the file, and that printing `rules` in EBNF
gives the text of the file back. Run from the root of the repository with
`lake env lean tests/Grammar.lean`.
-/

open CoreCpp.LL1 CoreCpp.EbnfFile CoreCpp.Grammar

def check (b : Bool) (what : String) : IO Unit :=
  unless b do throw (IO.userError s!"failed: {what}")

def ebnfPath : String := "grammar/core-cpp.ebnf"

/-- The text of the file after its leading comments. -/
def body (src : String) : String :=
  let lines := src.splitOn "\n"
  "\n".intercalate (lines.dropWhile fun l => l.startsWith "(*" || l.isEmpty)

#eval show IO Unit from do
  let src ← IO.FS.readFile ebnfPath
  let fromFile := ofEbnf (← load ebnfPath)
  -- EBNF to Lean. The committed module is the output of the generator.
  check (leanModule ebnfPath fromFile == (← IO.FS.readFile "CoreCpp/GrammarRules.lean"))
    "CoreCpp/GrammarRules.lean is the output of lake exe ebnf2lean"
  -- Lean to EBNF. Printing the rules of the module gives the rules of the file.
  check (renderRules classes (toEbnf rules) == body src) "the rules print as the file"
  -- Both give the same BNF, the grammar of the theorem.
  check ((translate "Program" fromFile).prods == grammar.prods) "same BNF"
  check (translate "Program" fromFile).isLL1 "LL(1) from the file"
  IO.println s!"{rules.length} rules, round trip ok"
