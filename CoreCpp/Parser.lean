import CoreCpp.Token
import CoreCpp.Lexer
import CoreCpp.Syntax

/-!
# Core C++ parser, subset

Recursive descent over the `Array Token` that the lexer produces. Each
nonterminal has its own function, except `Section` and `MemberRest`, which
`classRest` and `member` read inline. A function chooses the production by the
next token, and `member` also looks at the token after it. The subset covers
basic, class, pointer, library and function types, expressions, lambdas in
their three positions, commands, `delete`, classes with sections, fields,
methods, constructors, destructors and single inheritance, namespaces and
functions with parameters by value and by reference. Three left factorings
keep the grammar LL(1). In `Member` a `TypeId` opens a constructor when `(`
follows it and a type otherwise. In `ExprStatement` an assignment and an
expression statement share the prefix `Expr`, and the token `=` decides. In
`Declaration` a class with a body and a class declared without one share the
keyword `class`, and the case of the name decides.

The library carries no syntax of its own. `namespace std` is an ordinary
namespace and `std::vector<int>` an ordinary qualified name, which the lexer
opens by marking `std` as an `NsId`, and the case of the last component says
whether the name is a class of the program or one of the library.

A namespace is flattened at parse time. Inside `namespace N { … }` every class
declared is named `N::C`, and every unqualified class name mentioned in a type
or in `new` is read as `N::C`. A class of an enclosing scope is reached only
by its qualified name.
-/

namespace CoreCpp

/-- The state of a parser, the tokens, the position of the next one, the
enclosing namespaces and the origin of each token. -/
structure PState where
  /-- The tokens from the lexer, ending in `eof`. -/
  toks : Array Token
  /-- The index of the next token in `toks`. -/
  pos  : Nat := 0
  /-- The prefix of the enclosing namespaces, `N::M::`, empty at top level. -/
  ns   : String := ""
  /-- Whether each token comes from a header of Core C++. -/
  hdr  : Array Bool := #[]

/-- The type of the parsers. A value of `P α` reads the tokens of a `PState`
from its position, advances it, and gives an `α` or fails with a message. -/
abbrev P := StateT PState (Except String)

namespace P

def peek : P Token := do
  let s ← get
  return s.toks.getD s.pos .eof

/-- The token k positions ahead, `eof` past the end. -/
def peekAt (k : Nat) : P Token := do
  let s ← get
  return s.toks.getD (s.pos + k) .eof

def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

/-- A class name as written, qualified by the enclosing namespaces when it
carries no `::` of its own. -/
def qualify (n : String) : P String := do
  let s ← get
  return if (n.splitOn "::").length > 1 then n else s.ns ++ n

/-- Whether the next token comes from a header of Core C++. -/
def inHeader : P Bool := do
  let s ← get
  return s.hdr.getD s.pos false

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

def typeId : P String := do
  match ← peek with
  | .typeId x => advance; return x
  | _ => fail "expected type identifier"

/-- A namespace identifier, an identifier the lexer marked because `::`
follows it. -/
def nsId : P String := do
  match ← peek with
  | .nsId x => advance; return x
  | _ => fail "expected namespace identifier"

/-- A name of either case, the head of a namespace and the last component of a
qualified name. -/
def name : P String := do
  match ← peek with
  | .typeId x | .varId x => advance; return x
  | _ => fail "expected a name"

end P

open P

/-- `BasicType ::= 'int' | 'bool' | 'void'` -/
def basicType : P Ty := do
  match ← peek with
  | .kw "int"  => advance; return .int
  | .kw "bool" => advance; return .bool
  | .kw "void" => advance; return .void
  | _ => fail "expected basic type"

/-- The tokens that open a `Type`, and therefore a declaration. No expression
starts with one of them. -/
def isTypeStart : Token → Bool
  | .kw "int" | .kw "bool" | .kw "void" | .nsId _ | .typeId _ => true
  | _ => false

mutual

/-- `TemplateArgs ::= '<' TemplateArg ( ',' TemplateArg )* '>'`. -/
partial def templateArgs : P (List Ty) := do
  expectSym "<"
  let mut ts := [← templateArg]
  while ← acceptSym "," do
    ts := ts ++ [← templateArg]
  expectSym ">"
  return ts

/-- `QualTail ::= NsId '::' QualTail | Name TemplateArgs?`, the rest of a
qualified name after a namespace. The case of the last component says which
type it is. An uppercase one names a class of the program, so `Geometry::Shape`
is a class type, and a lowercase one names a class of the library, whose names
are lowercase, so `std::vector<int>` is a library type. -/
partial def qualTail (pre : String) : P Ty := do
  match ← peek with
  | .nsId n => advance; expectSym "::"; qualTail (pre ++ n ++ "::")
  | .typeId n =>
    advance
    let base := pre ++ n
    if (← peek) == .sym "<" then
      let ts ← templateArgs
      if ts.length != 1 then fail "a class template of this subset has one type parameter"
      return .cls s!"{base}<{ts.head!}>"
    return .cls base
  | .varId n =>
    advance
    let base := pre ++ n
    if (← peek) == .sym "<" then return .lib base (← templateArgs)
    fail s!"{base} names a class of the library, which takes its arguments in angle brackets"
  | _ => fail "expected a name after ::"

/-- `ClassType ::= NsId '::' QualTail | TypeId TemplateArgs?`, a class name
possibly qualified by namespaces and possibly instantiating a class template.
The instantiation is named by the chain the design prints for the type, so
`Stack<int>` in the source and the expanded class have the same name, and
`Templates.instantiate` adds the class before the program is checked. -/
partial def classType : P Ty := do
  match ← peek with
  | .nsId n => advance; expectSym "::"; qualTail (n ++ "::")
  | _ =>
    let n ← typeId
    let base ← qualify n
    if (← peek) == .sym "<" then
      let ts ← templateArgs
      if ts.length != 1 then fail "a class template of this subset has one type parameter"
      return .cls s!"{base}<{ts.head!}>"
    return .cls base

/-- The name of a class type, for the places that take no library type. -/
partial def className : P String := do
  match ← classType with
  | .cls n => return n
  | t => fail s!"{t} is a type of the library, not a class of the program"

/-- `TemplateArg ::= Type ( '(' ( Type ( ',' Type )* )? ')' )?`, a type or a
function type, as `int(int)` in `std::function<int(int)>`. -/
partial def templateArg : P Ty := do
  let t ← type
  if !(← acceptSym "(") then return t
  let mut ps : List Ty := []
  if !(← acceptSym ")") then
    ps := [← type]
    while ← acceptSym "," do
      ps := ps ++ [← type]
    expectSym ")"
  return .fn t ps

/-- `Type ::= BasicType | ClassType '*'?`. -/
partial def type : P Ty := do
  match ← peek with
  | .typeId _ | .nsId _ =>
    let c ← classType
    if ← acceptSym "*" then return .ptr c else return c
  | _ => basicType

end

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

/-- `UnaryExpr ::= ( '!' | '-' | '*' ) UnaryExpr | PostfixExpr` -/
partial def unaryExpr : P Expr := do
  match ← peek with
  | .sym "!" => advance; return .unop .not (← unaryExpr)
  | .sym "-" => advance; return .unop .neg (← unaryExpr)
  | .sym "*" => advance; return .deref (← unaryExpr)
  | _ => postfixExpr

/-- `PostfixExpr ::= Primary ( '[' Expr ']' | '.' VarId | '->' VarId | Args )*`.
`Args` after a variable is the call `f(…)`, of the function named `f`, of the
function value bound to `f` or of the method `f` of `this`, and after any other
postfix expression it is the call of a function value, `callFn`. `.m(…)` and
`->m(…)` are method calls, with the static class left for the type checker. -/
partial def postfixExpr : P Expr := do
  let mut e ← primary
  repeat
    match e, ← peek with
    | .var f, .sym "(" => e := .call f (← args) none
    | _, .sym "(" => e := .callFn e (← args)
    | _, .sym "[" => advance; let i ← expr; expectSym "]"; e := .index e i
    | _, .sym "." =>
      advance; let f ← varId
      if (← peek) == .sym "(" then e := .methodCall e false f (← args) none none else e := .field e f
    | _, .sym "->" =>
      advance; let f ← varId
      if (← peek) == .sym "(" then e := .methodCall e true f (← args) none none else e := .arrow e f
    | _, _ => break
  return e

/-- `Primary ::= IntLit | 'true' | 'false' | 'nullptr' | 'this' | VarId | '(' Expr ')'
| 'new' ClassType Args` -/
partial def primary : P Expr := do
  match ← peek with
  | .intLit n  => advance; return .intLit n
  | .kw "true"  => advance; return .boolLit true
  | .kw "false" => advance; return .boolLit false
  | .kw "nullptr" => advance; return .nullptr
  | .kw "this" => advance; return .this
  | .varId x   => advance; return .var x
  | .sym "("   => advance; let e ← expr; expectSym ")"; return e
  | .kw "new"  =>
    advance
    match ← classType with
    | .cls c => return .newObj c (← args)
    | t => return .newLib t (← args)
  | _ => fail "expected primary expression"

/-- `Args ::= '(' ( ArgExpr ( ',' ArgExpr )* )? ')'` -/
partial def args : P (List Expr) := do
  expectSym "("
  if ← acceptSym ")" then return []
  let mut acc := [← argExpr]
  while ← acceptSym "," do
    acc := acc ++ [← argExpr]
  expectSym ")"
  return acc

/-- `ArgExpr ::= Lambda | Expr`. The lambda is an argument expression and not
a primary, so it occurs only as argument, as initialiser of a declaration and
as the expression of `return`. -/
partial def argExpr : P Expr := do
  if (← peek) == .sym "[=]" then lambda else expr

/-- `Lambda ::= '[=]' Params '->' Type Block`. The parameters are by value. -/
partial def lambda : P Expr := do
  expectSym "[=]"
  let ps ← params
  if ps.any (·.byRef) then fail "lambda parameters are by value in this subset"
  expectSym "->"
  let r ← type
  let b ← block
  return .lambda ps r b

/-- `Param ::= Type '&'? VarId`. With `&` the parameter is by reference. -/
partial def param : P Param := do
  let t ← type
  let isRef ← acceptSym "&"
  let x ← varId
  return ⟨t, x, isRef⟩

/-- `Params ::= '(' ( Param ( ',' Param )* )? ')'` -/
partial def params : P (List Param) := do
  expectSym "("
  if ← acceptSym ")" then return []
  let mut acc := [← param]
  while ← acceptSym "," do
    acc := acc ++ [← param]
  expectSym ")"
  return acc

/-- `ExprStatement ::= Expr ( '=' Expr )?`, an assignment command or an expression as statement. -/
partial def exprStatement : P Cmd := do
  let l ← expr
  if ← acceptSym "=" then
    let r ← expr
    return .assign l r
  else return .exprStmt l

/-- `LocalDecl ::= 'auto' VarId '=' Expr | Type '&'? VarId '=' ArgExpr`. With
`&` the declaration is a local reference. A lambda initialises only a typed
declaration, never an `auto` one. -/
partial def localDecl : P Cmd := do
  if ← accept (.kw "auto") then
    let x ← varId
    expectSym "="
    return .declAuto x (← expr)
  else
    let t ← type
    let isRef ← acceptSym "&"
    let x ← varId
    expectSym "="
    let e ← argExpr
    return if isRef then .declRef t x e else .decl t x e

/-- `ForInit ::= LocalDecl | ExprStatement` -/
partial def forInit : P Cmd := do
  match ← peek with
  | .kw "auto" => localDecl
  | t => if isTypeStart t then localDecl else exprStatement

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
    let e ← argExpr
    expectSym ";"
    return .ret (some e)
  | .kw "delete" =>
    advance
    let e ← expr
    expectSym ";"
    return .delete e none
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

/-- `Function ::= Type VarId Params ( Block | ';' )`. A function without a
body is a declaration of the library, as `void assert(bool condition);` of
`<cassert>`, and only a header holds it. -/
def function : P Decl := do
  let h ← inHeader
  let t ← type
  let f ← varId
  let ps ← params
  if ← acceptSym ";" then
    if !h then fail s!"the declaration of {f} without a body belongs to a header of Core C++"
    return .libFn f t ps
  let b ← block
  return .fn ⟨t, f, ps, b⟩


/-- The members of a class as the parser reads them, one constructor at a time. -/
inductive MemberItem where
  | field  (f : Field)
  | method (m : Method)
  | ctor   (c : Ctor)
  | dtor   (d : Dtor)

/-- The operators a class may overload, the production `Op` of the design. -/
def operatorName : P String := do
  match ← peek with
  | .sym "[" => advance; expectSym "]"; return "operator[]"
  | .sym s =>
    if ["+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">="].contains s then
      advance; return s!"operator{s}"
    else fail "expected an operator that a class may overload"
  | _ => fail "expected an operator that a class may overload"

/-- `Member ::= 'virtual' ( Type '&'? MemberRest | '~' TypeId '(' ')' Block )
| '~' TypeId '(' ')' Block | TypeId Params Block | Type '&'? MemberRest` with
`MemberRest ::= VarId ( ';' | Params 'override'? Block ) | 'operator' Op Params Block`.
The first factoring of the design. A `TypeId` followed by `(` opens the
constructor, which must be named after the class, and a `TypeId` followed by
anything else opens a type. The `&` after the type marks a member that
returns a reference, so a call to it denotes a location, and it never
appears on a field. -/
partial def member (cls : String) (vis : Vis) : P MemberItem := do
  let destructor (isVirtual : Bool) : P MemberItem := do
    expectSym "~"
    let n ← typeId
    if (← qualify n) != cls then fail s!"destructor named {n} in class {cls}"
    expectSym "("; expectSym ")"
    let b ← block
    return .dtor ⟨b, isVirtual⟩
  -- After the type of a member, its `&`, its name and the rest. A field is
  -- the only form that ends in `;`, and it takes no `&`.
  let afterType (isVirtual : Bool) (t : Ty) : P MemberItem := do
    let isRef ← acceptSym "&"
    if ← accept (.kw "operator") then
      let name ← operatorName
      let ps ← params
      let b ← block
      return .method ⟨name, t, ps, b, vis, isVirtual, false, isRef⟩
    let name ← varId
    if (← peek) == .sym ";" then
      if isRef then fail "a field is not a reference in this subset"
      advance
      return .field ⟨t, name, vis⟩
    let ps ← params
    let ovr ← accept (.kw "override")
    let b ← block
    return .method ⟨name, t, ps, b, vis, isVirtual, ovr, isRef⟩
  let methodRest (isVirtual : Bool) : P MemberItem := do
    afterType isVirtual (← type)
  match ← peek with
  | .kw "virtual" =>
    advance
    if (← peek) == .sym "~" then destructor true else methodRest true
  | .sym "~" => destructor false
  | .typeId n =>
    if (← peekAt 1) == .sym "(" then
      advance
      if (← qualify n) != cls then fail s!"constructor named {n} in class {cls}"
      let ps ← params
      let b ← block
      return .ctor ⟨ps, b⟩
    else afterType false (← type)
  | _ => afterType false (← type)

/-- `ClassRest ::= ( ':' 'public' ClassType )? '{' Member* Section* '}' ';'` with
`Section ::= ( 'public' | 'private' ) ':' Member*`, the class after its name.
Members before any section label are private, as in C++. -/
partial def classRest (name : String) : P ClassDecl := do
  let base ← if ← acceptSym ":" then
      expect (.kw "public")
      pure (some (← className))
    else pure none
  expectSym "{"
  let mut vis : Vis := .priv
  let mut fields : List Field := []
  let mut methods : List Method := []
  let mut ctor : Option Ctor := none
  let mut dtor : Option Dtor := none
  while (← peek) != .sym "}" do
    match ← peek with
    | .eof => fail "unclosed class"
    | .kw "public" => advance; expectSym ":"; vis := .pub
    | .kw "private" => advance; expectSym ":"; vis := .priv
    | _ =>
      match ← member name vis with
      | .field f => fields := fields ++ [f]
      | .method m => methods := methods ++ [m]
      | .ctor c =>
        if ctor.isSome then fail s!"class {name} has two constructors"
        if vis != .pub then fail s!"the constructor of {name} must be public"
        ctor := some c
      | .dtor d =>
        if dtor.isSome then fail s!"class {name} has two destructors"
        dtor := some d
  expectSym "}"
  expectSym ";"
  return ⟨name, base, fields, methods, ctor, dtor⟩

/-- `Class ::= 'class' TypeId ClassRest`. -/
partial def classDecl : P ClassDecl := do
  expect (.kw "class")
  classRest (← qualify (← typeId))

mutual

/-- `Declaration ::= 'namespace' Name '{' Declaration* '}'
| 'template' '<' 'typename' TypeId ( ',' 'typename' TypeId )* '>'
  'class' ( TypeId ClassRest | VarId ';' ) | Class | Function`.
A namespace holds classes, templates and namespaces, and its name is of either
case, since the library opens `namespace std`. Its declarations are flattened
into the program with qualified names. A class declared without a body is a
class of the library, named in lowercase, which an intrinsic implements. -/
partial def declaration : P (List Decl) := do
  match ← peek with
  | .kw "class" => return [.cls (← classDecl)]
  | .kw "template" =>
    advance
    expectSym "<"
    expect (.kw "typename")
    let mut ps := [← typeId]
    while ← acceptSym "," do
      expect (.kw "typename")
      ps := ps ++ [← typeId]
    expectSym ">"
    expect (.kw "class")
    -- After `class` the case of the name decides. A type identifier opens a
    -- class of the program, with its body. A variable identifier opens a
    -- class declared without a body, which the library names in lowercase and
    -- an intrinsic implements.
    match ← peek with
    | .varId n =>
      advance
      expectSym ";"
      if ps.length == 0 then fail "a class template declares at least one parameter"
      return [.libTmpl (← qualify n) ps]
    | _ =>
      if ps.length != 1 then fail "a class template of this subset has one type parameter"
      return [.tmpl ps.head! (← classRest (← qualify (← typeId)))]
  | .kw "namespace" =>
    let h ← inHeader
    advance
    let n ← name
    -- C++ leaves a program that adds declarations to namespace std undefined
    -- (N4659 §20.5.4.2.1, paragraph 1), so only a header of Core C++ opens it.
    if n == "std" && !h then fail "namespace std belongs to the headers of Core C++"
    expectSym "{"
    let outer := (← get).ns
    modify fun s => { s with ns := outer ++ n ++ "::" }
    let mut acc : List Decl := []
    while (← peek) != .sym "}" do
      if (← peek) == .eof then fail "unclosed namespace"
      if (← peek) != .kw "class" && (← peek) != .kw "namespace" && (← peek) != .kw "template" then
        fail "a namespace holds classes, templates and namespaces in this subset"
      acc := acc ++ (← declaration)
    expectSym "}"
    modify fun s => { s with ns := outer }
    return acc
  | _ => return [← function]

end

/-- `Program ::= Declaration*` -/
partial def program : P Program := do
  let mut acc : List Decl := []
  while (← peek) != .eof do
    acc := acc ++ (← declaration)
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

/-- Parses the output of Preproc, a list of lines each marked with whether it
comes from a header. No token spans two lines, so each line is lexed alone. -/
def parseUnit (lines : List (String × Bool)) : Except String Program := do
  let mut toks : Array Token := #[]
  let mut hdr : Array Bool := #[]
  for (l, h) in lines do
    let ts := (← lex l).pop
    toks := toks ++ ts
    hdr := hdr ++ Array.replicate ts.size h
  let (a, s) ← program.run { toks := toks.push .eof, hdr }
  if s.toks.getD s.pos .eof == .eof then return a
  else throw s!"unconsumed input from token {s.pos} ('{s.toks.getD s.pos .eof}')"

end CoreCpp
