import CoreCpp.Token
import CoreCpp.Lexer
import CoreCpp.LL1

/-!
# The grammar of Core C++ as an LL(1) grammar

The EBNF grammar of the blueprint, rule by rule, over token classes. The
translation of `LL1.lean` gives its BNF form, the table follows, and the
theorem `isLL1_grammar` states that the table has no conflict. The predictive
parser of `LL1.lean` then recognises Core C++ programs from the tokens of the
lexer.
-/

namespace CoreCpp.Grammar

open CoreCpp.LL1

/-- A terminal of the grammar, a token class. Reserved words and symbols stand
for themselves, identifiers and literals for their class. -/
inductive Term where
  | kw (s : String)
  | sym (s : String)
  | typeId
  | varId
  | intLit
  deriving Repr, BEq, DecidableEq, Hashable

/-- The class of a token. The end of input has no class, since the parser
reads the end marker from the end of the list. -/
def Term.ofToken : Token → Term
  | .kw s => .kw s
  | .sym s => .sym s
  | .typeId _ => .typeId
  | .varId _ => .varId
  | .intLit _ => .intLit
  | .eof => .sym "<eof>"

private def k (s : String) : Ebnf Term := .t (.kw s)
private def s (x : String) : Ebnf Term := .t (.sym x)
private def n (A : String) : Ebnf Term := .n A
private def TypeId : Ebnf Term := .t .typeId
private def VarId : Ebnf Term := .t .varId
private def IntLit : Ebnf Term := .t .intLit
private def seq (es : List (Ebnf Term)) : Ebnf Term := .seq es
private def alt (es : List (Ebnf Term)) : Ebnf Term := .alt es
private def star (e : Ebnf Term) : Ebnf Term := .star e
private def opt (e : Ebnf Term) : Ebnf Term := .opt e
private def r (A : String) (e : Ebnf Term) : Rule Term := ⟨A, e⟩

/-- `( X ( , X )* )?`, a possibly empty list separated by commas. -/
private def commaList (e : Ebnf Term) : Ebnf Term := opt (seq [e, star (seq [s ",", e])])

/-- The rules of the grammar, in the order of the blueprint. -/
def rules : List (Rule Term) := [
  r "Program" (star (n "Declaration")),
  r "Declaration" (alt [
    seq [k "namespace", TypeId, s "{", star (n "Declaration"), s "}"],
    seq [k "template", s "<", k "typename", TypeId, s ">", n "Class"],
    n "Class",
    n "Function"]),
  r "Class" (seq [k "class", TypeId, opt (seq [s ":", k "public", n "ClassType"]),
    s "{", star (n "Section"), s "}", s ";"]),
  r "Section" (seq [alt [k "public", k "private"], s ":", star (n "Member")]),
  r "Member" (alt [
    seq [k "virtual", alt [
      seq [n "Type", VarId, n "Params", n "Block"],
      seq [s "~", TypeId, s "(", s ")", n "Block"]]],
    seq [s "~", TypeId, s "(", s ")", n "Block"],
    seq [alt [
        n "BasicType",
        seq [k "std::function", s "<", n "Type", s "(", commaList (n "Type"), s ")", s ">"],
        seq [k "std::vector", s "<", n "Type", s ">", opt (s "*")]],
      opt (s "&"), n "MemberRest"],
    seq [TypeId, alt [
      seq [n "Params", n "Block"],
      seq [n "ClassTypeRest", opt (s "*"), opt (s "&"), n "MemberRest"]]]]),
  r "MemberRest" (alt [
    seq [VarId, alt [s ";", seq [n "Params", opt (k "override"), n "Block"]]],
    seq [k "operator", n "Op", n "Params", n "Block"]]),
  r "Op" (alt [s "+", s "-", s "*", s "/", s "%", s "==", s "!=", s "<", s "<=",
    s ">", s ">=", seq [s "[", s "]"]]),
  r "Function" (seq [n "Type", VarId, n "Params", n "Block"]),
  r "Params" (seq [s "(", commaList (n "Param"), s ")"]),
  r "Param" (seq [n "Type", VarId]),
  r "Type" (seq [alt [
      n "BasicType",
      seq [alt [n "ClassType", seq [k "std::vector", s "<", n "Type", s ">"]], opt (s "*")],
      seq [k "std::function", s "<", n "Type", s "(", commaList (n "Type"), s ")", s ">"]],
    opt (s "&")]),
  r "BasicType" (alt [k "int", k "bool", k "void"]),
  r "ClassType" (seq [TypeId, n "ClassTypeRest"]),
  r "ClassTypeRest" (seq [star (seq [s "::", TypeId]),
    opt (seq [s "<", n "Type", star (seq [s ",", n "Type"]), s ">"])]),
  r "Block" (seq [s "{", star (n "Statement"), s "}"]),
  r "Statement" (alt [
    n "Block",
    seq [k "if", s "(", n "Expr", s ")", n "Block", opt (seq [k "else", n "Block"])],
    seq [k "while", s "(", n "Expr", s ")", n "Block"],
    seq [k "for", s "(", n "ForInit", s ";", n "Expr", s ";", n "ExprStatement", s ")", n "Block"],
    seq [k "return", opt (n "ArgExpr"), s ";"],
    seq [k "delete", n "Expr", s ";"],
    seq [n "LocalDecl", s ";"],
    seq [n "ExprStatement", s ";"]]),
  r "LocalDecl" (alt [
    seq [k "auto", VarId, s "=", n "Expr"],
    seq [n "Type", VarId, s "=", n "ArgExpr"]]),
  r "ForInit" (alt [n "LocalDecl", n "ExprStatement"]),
  r "ExprStatement" (seq [n "Expr", opt (seq [s "=", n "Expr"])]),
  r "Expr" (seq [n "OrExpr", opt (seq [s "?", n "Expr", s ":", n "Expr"])]),
  r "OrExpr" (seq [n "AndExpr", star (seq [s "||", n "AndExpr"])]),
  r "AndExpr" (seq [n "EqExpr", star (seq [s "&&", n "EqExpr"])]),
  r "EqExpr" (seq [n "RelExpr", star (seq [alt [s "==", s "!="], n "RelExpr"])]),
  r "RelExpr" (seq [n "AddExpr", star (seq [alt [s "<", s "<=", s ">", s ">="], n "AddExpr"])]),
  r "AddExpr" (seq [n "MulExpr", star (seq [alt [s "+", s "-"], n "MulExpr"])]),
  r "MulExpr" (seq [n "UnaryExpr", star (seq [alt [s "*", s "/", s "%"], n "UnaryExpr"])]),
  r "UnaryExpr" (alt [seq [alt [s "!", s "-", s "*"], n "UnaryExpr"], n "PostfixExpr"]),
  r "PostfixExpr" (seq [n "Primary", star (alt [
    seq [s "[", n "Expr", s "]"],
    seq [s ".", VarId],
    seq [s "->", VarId],
    n "Args"])]),
  r "Primary" (alt [IntLit, k "true", k "false", k "nullptr", k "this", VarId,
    seq [s "(", n "Expr", s ")"],
    seq [k "new", alt [n "ClassType", seq [k "std::vector", s "<", n "Type", s ">"]], n "Args"]]),
  r "Args" (seq [s "(", commaList (n "ArgExpr"), s ")"]),
  r "ArgExpr" (alt [n "Lambda", n "Expr"]),
  r "Lambda" (seq [s "[=]", n "Params", s "->", n "Type", n "Block"])]

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
