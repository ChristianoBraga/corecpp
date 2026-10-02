import CoreCpp.Token
import CoreCpp.Lexer
import CoreCpp.Syntax

/-!
# Core C++ parser, subset

Recursive descent over the `Array Token` that the lexer produces, one function
per nonterminal of `grammar/core-cpp.ebnf`, named after it. Five nonterminals
have no function of their own. The function `classRest` reads `Section`
inline, `member` reads `MemberRest`, and `postfixExpr` reads `Chain`, `After`
and `ChainNoCall`.
Three functions carry another name, `classDecl` for `Class`, `operatorName` for
`Op` and `P.name` for `Name`. A function chooses the production by the next
token, and `member` also looks at the token after it. The subset covers
basic, class, pointer, library and function types, expressions, lambdas in
their three positions, commands, `delete`, classes with sections, fields,
methods, constructors, destructors and single inheritance, namespaces and
functions with parameters by value and by reference. Three left factorings
keep the grammar LL(1). In `Member` a `TypeId` opens a constructor when `(`
follows it and a type otherwise. In `ExprStatement` an assignment and an
expression statement share the prefix `Expr`, and the token `=` decides. In
`Declaration` a class template with a body and a class template of the library
without one share the prefix up to `class`, and the case of the name decides.

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

/-- A name of either case, the name of a namespace and the last component of a
qualified name.

```
Name = TypeId | VarId ;
```
-/
def name : P String := do
  match ← peek with
  | .typeId x | .varId x => advance; return x
  | _ => fail "expected a name"

end P

open P

/--
```
BasicType = "int" | "bool" | "void" ;
```
-/
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

/--
```
TemplateArgs = "<" TemplateArg { "," TemplateArg } ">" ;
```
-/
partial def templateArgs : P (List Ty) := do
  expectSym "<"
  let mut ts := [← templateArg]
  while ← acceptSym "," do
    ts := ts ++ [← templateArg]
  expectSym ">"
  return ts

/-- The rest of a qualified name after a namespace.

```
QualTail = NsId "::" QualTail | Name [ TemplateArgs ] ;
```

The case of the last component says which type it is. An uppercase one names a
class of the program, so `Geometry::Shape` is a class type, and a lowercase one
names a class of the library, whose names are lowercase, so `std::vector<int>`
is a library type. A class of the program takes one template argument at most,
and a class of the library always takes its arguments. -/
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

/-- A class name possibly qualified by namespaces and possibly instantiating a
class template.

```
ClassType = NsId "::" QualTail | TypeId [ TemplateArgs ] ;
```

The function reads an unqualified name in the enclosing namespace, and a class
template takes one template argument. The name of the instantiation is the
string `Ty.toString` prints for the type, so `Stack<int>` in the source and the
expanded class have the same name, and `Templates.instantiate` adds the class
before the type checker runs. -/
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

/-- The name of a class type, for the base of a class, which is never a type
of the library. -/
partial def className : P String := do
  match ← classType with
  | .cls n => return n
  | t => fail s!"{t} is a type of the library, not a class of the program"

/-- A type or a function type, as `int(int)` in `std::function<int(int)>`.

```
TemplateArg = Type [ "(" [ Type { "," Type } ] ")" ] ;
```
-/
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

/--
```
Type = BasicType | ClassType [ "*" ] ;
```
-/
partial def type : P Ty := do
  match ← peek with
  | .typeId _ | .nsId _ =>
    let c ← classType
    if ← acceptSym "*" then return .ptr c else return c
  | _ => basicType

end

mutual

/--
```
Expr = OrExpr [ "?" Expr ":" Expr ] ;
```
-/
partial def expr : P Expr := do
  let c ← orExpr
  if ← acceptSym "?" then
    let t ← expr
    expectSym ":"
    let e ← expr
    return .cond c t e
  else return c

/--
```
OrExpr = AndExpr { "||" AndExpr } ;
```
-/
partial def orExpr : P Expr := do
  let mut l ← andExpr
  while ← acceptSym "||" do
    let r ← andExpr
    l := .binop .or l r
  return l

/--
```
AndExpr = EqExpr { "&&" EqExpr } ;
```
-/
partial def andExpr : P Expr := do
  let mut l ← eqExpr
  while ← acceptSym "&&" do
    let r ← eqExpr
    l := .binop .and l r
  return l

/--
```
EqExpr = RelExpr { ( "==" | "!=" ) RelExpr } ;
```
-/
partial def eqExpr : P Expr := do
  let mut l ← relExpr
  repeat
    match ← peek with
    | .sym "==" => advance; let r ← relExpr; l := .binop .eq l r
    | .sym "!=" => advance; let r ← relExpr; l := .binop .ne l r
    | _ => break
  return l

/--
```
RelExpr = AddExpr { ( "<" | "<=" | ">" | ">=" ) AddExpr } ;
```
-/
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

/--
```
AddExpr = MulExpr { ( "+" | "-" ) MulExpr } ;
```
-/
partial def addExpr : P Expr := do
  let mut l ← mulExpr
  repeat
    match ← peek with
    | .sym "+" => advance; let r ← mulExpr; l := .binop .add l r
    | .sym "-" => advance; let r ← mulExpr; l := .binop .sub l r
    | _ => break
  return l

/--
```
MulExpr = UnaryExpr { ( "*" | "/" | "%" ) UnaryExpr } ;
```
-/
partial def mulExpr : P Expr := do
  let mut l ← unaryExpr
  repeat
    match ← peek with
    | .sym "*" => advance; let r ← unaryExpr; l := .binop .mul l r
    | .sym "/" => advance; let r ← unaryExpr; l := .binop .div l r
    | .sym "%" => advance; let r ← unaryExpr; l := .binop .mod l r
    | _ => break
  return l

/--
```
UnaryExpr = ( "!" | "-" | "*" ) UnaryExpr | PostfixExpr ;
```
-/
partial def unaryExpr : P Expr := do
  match ← peek with
  | .sym "!" => advance; return .unop .not (← unaryExpr)
  | .sym "-" => advance; return .unop .neg (← unaryExpr)
  | .sym "*" => advance; return .deref (← unaryExpr)
  | _ => postfixExpr

/-- A primary expression and its chain, with `Chain`, `After` and `ChainNoCall`
read inline by the loop.

```
PostfixExpr = Primary Chain ;
Chain = [ ( "[" Expr "]" Chain | "." VarId After
          | "->" VarId After | Args Chain ) ] ;
After = Args Chain | ChainNoCall ;
ChainNoCall = [ ( "[" Expr "]" Chain | "." VarId After
                | "->" VarId After ) ] ;
```

An `Args` after a variable is the call `f(…)`, of the function named `f`, of the
`std::function` a reference `f` names or of the method `f` of `this`, and after
any other postfix expression it is the call of the `std::function` that
expression denotes, `callFn`, as in `(*f)(ē)`. The forms `.m(…)`
and `->m(…)` are method calls, with the static class left for the type checker, and
a field access never takes `Args` directly. -/
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

/-- A primary expression. After `new`, a class of the program gives `newObj` and
a type of the library gives `newLib`.

```
Primary = IntLit | "true" | "false" | "nullptr" | "this" | VarId
        | "(" Expr ")" | "new" ClassType Args ;
```
-/
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

/--
```
Args = "(" [ ArgExpr { "," ArgExpr } ] ")" ;
```
-/
partial def args : P (List Expr) := do
  expectSym "("
  if ← acceptSym ")" then return []
  let mut acc := [← argExpr]
  while ← acceptSym "," do
    acc := acc ++ [← argExpr]
  expectSym ")"
  return acc

/-- The lambda is an argument expression and not a primary, so it occurs only as
argument, as initialiser of a declaration with a type and as the expression of
`return`.

```
ArgExpr = Lambda | Expr ;
```
-/
partial def argExpr : P Expr := do
  if (← peek) == .sym "[=]" then lambda else expr

/-- The parameters of a lambda are by value.

```
Lambda = "[=]" Params "->" Type Block ;
```
-/
partial def lambda : P Expr := do
  expectSym "[=]"
  let ps ← params
  if ps.any (·.byRef) then fail "lambda parameters are by value in this subset"
  expectSym "->"
  let r ← type
  let b ← block
  return .lambda ps r b

/-- With `&` the parameter is by reference.

```
Param = Type [ "&" ] VarId ;
```
-/
partial def param : P Param := do
  let t ← type
  let isRef ← acceptSym "&"
  let x ← varId
  return ⟨t, x, isRef⟩

/--
```
Params = "(" [ Param { "," Param } ] ")" ;
```
-/
partial def params : P (List Param) := do
  expectSym "("
  if ← acceptSym ")" then return []
  let mut acc := [← param]
  while ← acceptSym "," do
    acc := acc ++ [← param]
  expectSym ")"
  return acc

/-- An assignment command or an expression as statement, told apart by `=`.

```
ExprStatement = Expr [ "=" Expr ] ;
```
-/
partial def exprStatement : P Cmd := do
  let l ← expr
  if ← acceptSym "=" then
    let r ← expr
    return .assign l r
  else return .exprStmt l

/-- With `&` the declaration is a local reference. A lambda initialises only a
typed declaration, never an `auto` one.

```
LocalDecl = "auto" VarId "=" Expr
          | Type [ "&" ] VarId "=" ArgExpr ;
```
-/
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

/-- A declaration when the first token opens a type, by `isTypeStart`, and an
expression statement otherwise.

```
ForInit = LocalDecl | ExprStatement ;
```
-/
partial def forInit : P Cmd := do
  match ← peek with
  | .kw "auto" => localDecl
  | t => if isTypeStart t then localDecl else exprStatement

/--
```
Block = "{" { Statement } "}" ;
```
-/
partial def block : P (List Cmd) := do
  expectSym "{"
  let mut acc : List Cmd := []
  while (← peek) != .sym "}" do
    if (← peek) == .eof then fail "unclosed block"
    acc := acc ++ [← statement]
  expectSym "}"
  return acc

/-- A command or an expression statement, chosen by the first token. A token that
opens a type, by `isTypeStart`, opens a declaration.

```
Statement = Block
          | "if" "(" Expr ")" Block [ "else" Block ]
          | "while" "(" Expr ")" Block
          | "for" "(" ForInit ";" Expr ";" ExprStatement ")" Block
          | "return" [ ArgExpr ] ";"
          | "delete" Expr ";"
          | LocalDecl ";"
          | ExprStatement ";" ;
```
-/
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

/-- A function without a body is a declaration of the library, as
`void assert(bool condition);` of `<cassert>`, and only a header holds it.

```
Function = Type VarId Params ( Block | ";" ) ;
```
-/
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

/-- The operators a class may overload, the nonterminal `Op`.

```
Op = "+" | "-" | "*" | "/" | "%" | "==" | "!="
   | "<" | "<=" | ">" | ">=" | "[" "]" ;
```
-/
def operatorName : P String := do
  match ← peek with
  | .sym "[" => advance; expectSym "]"; return "operator[]"
  | .sym s =>
    if ["+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">="].contains s then
      advance; return s!"operator{s}"
    else fail "expected an operator that a class may overload"
  | _ => fail "expected an operator that a class may overload"

/-- A member of a class, with `MemberRest` read inline by `afterType`.

```
Member = "virtual" ( Type [ "&" ] MemberRest
                   | "~" TypeId "(" ")" Block )
       | "~" TypeId "(" ")" Block
       | ( BasicType | NsId "::" QualTail [ "*" ] ) [ "&" ] MemberRest
       | TypeId ( Params Block
                | [ TemplateArgs ] [ "*" ] [ "&" ] MemberRest ) ;
MemberRest = VarId ( ";" | Params [ "override" ] Block )
           | "operator" Op Params Block ;
```

The first factoring of the grammar. A `TypeId` followed by `(` opens the
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
      if isVirtual then fail s!"field {name} is virtual, only a method or a destructor is"
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

/-- The class after its name, with `Section` read inline.

```
ClassRest = [ ":" "public" ClassType ] "{" { Member } { Section } "}" ";" ;
Section = ( "public" | "private" ) ":" { Member } ;
```

Members before any section label are private, as in C++. The base is a class of
the program. A class has at most one constructor and at most one destructor, both
public. A field is never virtual. -/
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
        if vis != .pub then fail s!"the destructor of {name} must be public"
        dtor := some d
  expectSym "}"
  expectSym ";"
  return ⟨name, base, fields, methods, ctor, dtor⟩

/-- The class name is read in the enclosing namespace.

```
Class = "class" TypeId ClassRest ;
```
-/
partial def classDecl : P ClassDecl := do
  expect (.kw "class")
  classRest (← qualify (← typeId))

mutual

/--
```
Declaration = "namespace" Name "{" { Declaration } "}"
            | "template" "<" "typename" TypeId
                { "," "typename" TypeId } ">"
                "class" ( TypeId ClassRest | VarId ";" )
            | Class
            | Function ;
```

A namespace holds classes, templates and namespaces, and its name is of either
case, since the library opens `namespace std`, which only a header of Core C++
opens. The function flattens its declarations into the program with qualified
names. A class template with a body has one type parameter. A class template declared
without a body is a class of the library, named in lowercase, which a module
of the library implements. -/
partial def declaration : P (List Decl) := do
  match ← peek with
  | .kw "class" => return [.cls (← classDecl)]
  | .kw "template" =>
    let h ← inHeader
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
    -- a module of the library implements.
    match ← peek with
    | .varId n =>
      advance
      expectSym ";"
      if !h then fail s!"the declaration of class template {n} without a body belongs to a header of Core C++"
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

/-- A sequence of declarations up to `eof`.

```
Program = { Declaration } ;
```
-/
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
comes from a header. No token spans two lines, so the automaton runs on each
line alone. The pass `Lexer.qualifiers` runs once on the tokens of the whole
unit, so it marks `std` at the end of a line before a `::` on the next. -/
def parseUnit (lines : List (String × Bool)) : Except String Program := do
  let mut toks : Array Token := #[]
  let mut hdr : Array Bool := #[]
  for (l, h) in lines do
    let ts := (← Lexer.run l.toList #[]).pop
    toks := toks ++ ts
    hdr := hdr ++ Array.replicate ts.size h
  let (a, s) ← program.run { toks := Lexer.qualifiers (toks.push .eof), hdr }
  if s.toks.getD s.pos .eof == .eof then return a
  else throw s!"unconsumed input from token {s.pos} ('{s.toks.getD s.pos .eof}')"

end CoreCpp
