import CoreCpp.Token
import CoreCpp.Lexer
import CoreCpp.LL1
import CoreCpp.GrammarTerm
import CoreCpp.GrammarRules

/-!
# The grammar of Core C++ as an LL(1) grammar

The grammar is the EBNF file `grammar/core-cpp.ebnf`, the grammar of the
blueprint rule by rule over token classes. `lake exe ebnf2lean` writes it as
the module `CoreCpp/GrammarRules.lean`, which defines `rules`. The
translation of `LL1.lean` gives its BNF form, the table follows, and the
theorem `isLL1_grammar` states that the table has no conflict. The predictive
parser of `LL1.lean` then recognises Core C++ programs from the tokens of the
lexer.
-/

namespace CoreCpp.Grammar

open CoreCpp.LL1

/-- The grammar in BNF. -/
def grammar : LL1.Grammar Term := translate "Program" rules

/-- The predictive parsing table of the grammar. -/
def table : Table Term := grammar.table

/-- The grammar of Core C++ is LL(1). The table has no entry with two
productions. The proof evaluates `Grammar.isLL1` with `native_decide`, which
trusts the compiled evaluation. -/
theorem isLL1_grammar : grammar.isLL1 = true := by native_decide

/-- The leftmost derivation of a program by the predictive parser, from the
tokens of the lexer without the end token. -/
def derive (src : String) : Except String (List Nat) := do
  let toks := (← lex src).toList.filter (· != .eof)
  grammar.parse table Term.ofToken toks

/-- The derivation tree of a program. -/
def parseTree (src : String) : Except String (Tree Token) := do
  let toks := (← lex src).toList.filter (· != .eof)
  let d ← grammar.parse table Term.ofToken toks
  match grammar.tree toks d with
  | some t => return t
  | none => throw "the derivation does not match the input"

end CoreCpp.Grammar
