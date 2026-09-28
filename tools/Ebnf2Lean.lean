import CoreCpp.Ebnf
import CoreCpp.GrammarTerm

/-!
# The generator of `CoreCpp/GrammarRules.lean`

`lake exe ebnf2lean [input] [output]` reads the grammar of Core C++ from an
EBNF file, `grammar/core-cpp.ebnf` by default. It writes the Lean module that
defines `CoreCpp.Grammar.rules`, `CoreCpp/GrammarRules.lean` by default.
-/

open CoreCpp.EbnfFile CoreCpp.Grammar

def main (args : List String) : IO UInt32 := do
  let input := args.getD 0 "grammar/core-cpp.ebnf"
  let output := args.getD 1 "CoreCpp/GrammarRules.lean"
  let rs ← load input
  IO.FS.writeFile output (leanModule input (ofEbnf rs))
  IO.println s!"{output}, {rs.length} rules from {input}"
  return 0
