import CoreCpp.Token
import CoreCpp.Lexer
import CoreCpp.Syntax

/-!
# Core C++ parser, subset

Recursive descent, one function per nonterminal, over the `Array Token`
produced by the lexer. Each function reads the next token and chooses the
production by it. The subset covers basic types, expressions, commands and
functions.
-/

namespace CoreCpp

structure PState where
  toks : Array Token
  pos  : Nat := 0

abbrev P := StateT PState (Except String)

namespace P

def peek : P Token := do
  let s ← get
  return s.toks.getD s.pos .eof

def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

def fail (msg : String) : P α := do
  let t ← peek
  let s ← get
  throw s!"syntax error at token {s.pos} ('{t}'): {msg}"

/-- Consumes token `t` or fails. -/
def expect (t : Token) : P Unit := do
  if (← peek) == t then advance else fail s!"expected '{t}'"

def expectSym (s : String) : P Unit := expect (.sym s)

/-- Consumes `t` if it is the next token, and reports whether it did. -/
def accept (t : Token) : P Bool := do
  if (← peek) == t then advance; return true else return false

def acceptSym (s : String) : P Bool := accept (.sym s)

def varId : P String := do
  match ← peek with
  | .varId x => advance; return x
  | _ => fail "expected variable identifier"

end P

open P

/-- `BasicType ::= 'int' | 'bool' | 'void'` -/
def basicType : P Ty := do
  match ← peek with
  | .kw "int"  => advance; return .int
  | .kw "bool" => advance; return .bool
  | .kw "void" => advance; return .void
  | _ => fail "expected basic type"

def isTypeStart : Token → Bool
  | .kw "int" | .kw "bool" | .kw "void" => true
  | _ => false

mutual

/-- `Expr ::= OrExpr ( '?' Expr ':' Expr )?` -/
partial def expr : P Expr := do
  let c ← orExpr
  if ← acceptSym "?" then
    let t ← expr
    expectSym ":"
    let e ← expr
    return .cond c t e
  else return c

/-- `OrExpr ::= AndExpr ( '||' AndExpr )*` -/
partial def orExpr : P Expr := do
  let mut l ← andExpr
  while ← acceptSym "||" do
    let r ← andExpr
    l := .binop .or l r
  return l

/-- `AndExpr ::= EqExpr ( '&&' EqExpr )*` -/
partial def andExpr : P Expr := do
  let mut l ← eqExpr
  while ← acceptSym "&&" do
    let r ← eqExpr
    l := .binop .and l r
  return l

/-- `EqExpr ::= RelExpr ( ( '==' | '!=' ) RelExpr )*` -/
partial def eqExpr : P Expr := do
  let mut l ← relExpr
  repeat
    match ← peek with
    | .sym "==" => advance; let r ← relExpr; l := .binop .eq l r
    | .sym "!=" => advance; let r ← relExpr; l := .binop .ne l r
    | _ => break
  return l

/-- `RelExpr ::= AddExpr ( ( '<' | '<=' | '>' | '>=' ) AddExpr )*` -/
partial def relExpr : P Expr := do
  let mut l ← addExpr
  repeat
    match ← peek with
    | .sym "<"  => advance; let r ← addExpr; l := .binop .lt l r
    | .sym "<=" => advance; let r ← addExpr; l := .binop .le l r
    | .sym ">"  => advance; let r ← addExpr; l := .binop .gt l r
    | .sym ">=" => advance; let r ← addExpr; l := .binop .ge l r
    | _ => break
  return l

/-- `AddExpr ::= MulExpr ( ( '+' | '-' ) MulExpr )*` -/
partial def addExpr : P Expr := do
  let mut l ← mulExpr
  repeat
    match ← peek with
    | .sym "+" => advance; let r ← mulExpr; l := .binop .add l r
    | .sym "-" => advance; let r ← mulExpr; l := .binop .sub l r
    | _ => break
  return l

/-- `MulExpr ::= UnaryExpr ( ( '*' | '/' | '%' ) UnaryExpr )*` -/
partial def mulExpr : P Expr := do
  let mut l ← unaryExpr
  repeat
    match ← peek with
    | .sym "*" => advance; let r ← unaryExpr; l := .binop .mul l r
    | .sym "/" => advance; let r ← unaryExpr; l := .binop .div l r
    | .sym "%" => advance; let r ← unaryExpr; l := .binop .mod l r
    | _ => break
  return l

/-- `UnaryExpr ::= ( '!' | '-' ) UnaryExpr | PostfixExpr` -/
partial def unaryExpr : P Expr := do
  match ← peek with
  | .sym "!" => advance; return .unop .not (← unaryExpr)
  | .sym "-" => advance; return .unop .neg (← unaryExpr)
  | _ => postfixExpr

/-- `PostfixExpr ::= Primary Args?`, in this subset only the function call. -/
partial def postfixExpr : P Expr := do
  let p ← primary
  match p, ← peek with
  | .var f, .sym "(" => return .call f (← args)
  | _, _ => return p

/-- `Primary ::= IntLit | 'true' | 'false' | VarId | '(' Expr ')'` -/
partial def primary : P Expr := do
  match ← peek with
  | .intLit n  => advance; return .intLit n
  | .kw "true"  => advance; return .boolLit true
  | .kw "false" => advance; return .boolLit false
  | .varId x   => advance; return .var x
  | .sym "("   => advance; let e ← expr; expectSym ")"; return e
  | _ => fail "expected primary expression"

/-- `Args ::= '(' ( Expr ( ',' Expr )* )? ')'` -/
partial def args : P (List Expr) := do
  expectSym "("
  if ← acceptSym ")" then return []
  let mut acc := [← expr]
  while ← acceptSym "," do
    acc := acc ++ [← expr]
  expectSym ")"
  return acc

end

/-- `ExprStatement ::= Expr ( '=' Expr )?`, an assignment command or an expression as statement. -/
def exprStatement : P Cmd := do
  let l ← expr
  if ← acceptSym "=" then
    let r ← expr
    return .assign l r
  else return .exprStmt l

/-- `LocalDecl ::= 'auto' VarId '=' Expr | Type VarId '=' Expr` -/
def localDecl : P Cmd := do
  if ← accept (.kw "auto") then
    let x ← varId
    expectSym "="
    return .declAuto x (← expr)
  else
    let t ← basicType
    let x ← varId
    expectSym "="
    return .decl t x (← expr)

/-- `ForInit ::= LocalDecl | ExprStatement` -/
def forInit : P Cmd := do
  match ← peek with
  | .kw "auto" => localDecl
  | t => if isTypeStart t then localDecl else exprStatement

mutual

/-- `Block ::= '{' Statement* '}'` -/
partial def block : P (List Cmd) := do
  expectSym "{"
  let mut acc : List Cmd := []
  while (← peek) != .sym "}" do
    if (← peek) == .eof then fail "unclosed block"
    acc := acc ++ [← statement]
  expectSym "}"
  return acc

/-- `Statement`, a command or an expression statement, chosen by the first token. -/
partial def statement : P Cmd := do
  match ← peek with
  | .sym "{" => return .block (← block)
  | .kw "if" =>
    advance; expectSym "("
    let c ← expr
    expectSym ")"
    let t ← block
    let e ← if ← accept (.kw "else") then block else pure []
    return .ite c t e
  | .kw "while" =>
    advance; expectSym "("
    let c ← expr
    expectSym ")"
    return .while c (← block)
  | .kw "for" =>
    advance; expectSym "("
    let i ← forInit
    expectSym ";"
    let c ← expr
    expectSym ";"
    let s ← exprStatement
    expectSym ")"
    return .for i c s (← block)
  | .kw "return" =>
    advance
    if ← acceptSym ";" then return .ret none
    let e ← expr
    expectSym ";"
    return .ret (some e)
  | .kw "auto" =>
    let d ← localDecl
    expectSym ";"
    return d
  | t =>
    if isTypeStart t then
      let d ← localDecl
      expectSym ";"
      return d
    else
      let s ← exprStatement
      expectSym ";"
      return s

end

/-- `Param ::= Type VarId` -/
def param : P Param := do
  let t ← basicType
  let x ← varId
  return ⟨t, x⟩

/-- `Params ::= '(' ( Param ( ',' Param )* )? ')'` -/
def params : P (List Param) := do
  expectSym "("
  if ← acceptSym ")" then return []
  let mut acc := [← param]
  while ← acceptSym "," do
    acc := acc ++ [← param]
  expectSym ")"
  return acc

/-- `Function ::= Type VarId Params Block` -/
def function : P Fun := do
  let t ← basicType
  let f ← varId
  let ps ← params
  let b ← block
  return ⟨t, f, ps, b⟩

/-- `Program ::= Function*` -/
partial def program : P Program := do
  let mut acc : List Fun := []
  while (← peek) != .eof do
    acc := acc ++ [← function]
  return acc

/-- Runs a parser on a string, requiring the whole input to be consumed. -/
def runParser (p : P α) (input : String) : Except String α := do
  let toks ← lex input
  let (a, s) ← p.run { toks }
  if s.toks.getD s.pos .eof == .eof then return a
  else throw s!"unconsumed input from token {s.pos} ('{s.toks.getD s.pos .eof}')"

def parseExpr      : String → Except String Expr    := runParser expr
def parseStatement : String → Except String Cmd    := runParser statement
def parseProgram   : String → Except String Program := runParser program

end CoreCpp
