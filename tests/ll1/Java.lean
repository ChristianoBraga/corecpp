import CoreCpp.Ebnf

/-!
# The LL(1) construction on the grammar of Java of JLS 7, chapter 18

The grammar is `tests/ll1/grammars/java7.ebnf`, generated from the HTML of The
Java Language Specification, Java SE 7 Edition, chapter 18, Syntax,
https://docs.oracle.com/javase/specs/jls/se7/html/jls-18.html. The chapter
gives the grammar that is the basis of the reference implementation and says
of it "Note that it is not an LL(1) grammar". The chapter writes the rules
ForInit and ForUpdate over one right side, which the file repeats for each.
No program is parsed, since the grammar is not LL(1). Run from the root of
the repository with `lake env lean tests/ll1/Java.lean`.
-/

open CoreCpp.LL1 CoreCpp.EbnfFile

def check (b : Bool) (what : String) : IO Unit :=
  unless b do throw (IO.userError s!"failed: {what}")

/-- The rules with a conflict, each with the number of conflicting lookaheads. -/
def conflictRules (g : Grammar String) : List (String × Nat) :=
  let names := g.conflicts.map fun ((A, _), _) => (A.splitOn ".").head!
  names.eraseDups.map fun A => (A, names.count A)

-- Conflicts in 26 rules, of five kinds by the text of the chapter.
-- Left recursion, EnumConstants ::= EnumConstant | EnumConstants , EnumConstant
-- and AnnotationTypeElementDeclarations, of the same form.
-- Common prefix, the five alternatives of Selector that start with ".".
-- A repetition followed by an option on the same token, { . Identifier } [. *]
-- of ImportDeclaration.
-- The dangling else of if ParExpression Statement [else Statement].
-- Alternatives that start with IDENTIFIER, in BlockStatement a local variable
-- declaration, a labelled statement and an expression statement.
#eval show IO Unit from do
  let rs ← load "tests/ll1/grammars/java7.ebnf"
  check (rs.length == 124) "124 rules"
  let g ← loadGrammar "tests/ll1/grammars/java7.ebnf" (some "CompilationUnit")
  check (g.prods.length == 536) "536 productions"
  check (g.conflicts.length == 105) "105 conflicts"
  check ((conflictRules g).length == 26) "26 rules"
  IO.println (conflictRules g)
