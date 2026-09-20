/-!
# Core C++ abstract syntax, subset

Basic types, class and pointer types, vectors, function types, expressions,
lambdas, commands, classes with fields and functions. A statement is a command or an expression
followed by `;`. Assignment is a command. One tree per nonterminal of the
grammar in section 4 of the language design.
-/

namespace CoreCpp

/-- Types. `cls` is a class type, reached only through a pointer, `ptr` a
pointer type, `vec` the type of `std::vector<τ>`, also reached only through a
pointer, `fn ret params` the type `std::function<ret(params)>` of function
values, and `nullT` the type of `nullptr`, which converts to any pointer type
and never names a variable. -/
inductive Ty where
  | int | bool | void
  | cls (name : String)
  | ptr (t : Ty)
  | vec (t : Ty)
  | fn (ret : Ty) (params : List Ty)
  | nullT
  deriving Repr, BEq, Inhabited

/-- Object types are class and vector types. Their values live in the store
and are never copied, so no variable, parameter or result has an object
type. -/
def Ty.isObject : Ty → Bool
  | .cls _ | .vec _ => true
  | _ => false

/-- Function types, the types of closures. -/
def Ty.isFn : Ty → Bool
  | .fn .. => true
  | _ => false

inductive UnOp where
  | not | neg
  deriving Repr, BEq, DecidableEq

inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or
  deriving Repr, BEq, DecidableEq

/-- A parameter. `byRef` marks a `τ&` parameter, bound to the location of the
argument instead of to a fresh copy. -/
structure Param where
  ty    : Ty
  name  : String
  byRef : Bool := false
  deriving Repr, BEq, Inhabited

mutual

/-- Expressions. Function call is included because `Args` is part of
`PostfixExpr`. `field` is `e.f`, `arrow` is `e->f`, `deref` is `*e` and
`index` is `e[i]`. `newObj C` is `new C()` and `newVec τ n` is
`new std::vector<τ>(n)`. `lambda ps τ c` is `[=](ps) -> τ { c }`, which the
grammar admits only as an argument, as the initialiser of a declaration and
as the expression of `return`. `callFn e args` calls the function value `e`,
and `call f args` calls the function named `f`, or the function value bound to
`f` when `f` is a variable in scope. -/
inductive Expr where
  | intLit  (n : Int)
  | boolLit (b : Bool)
  | nullptr
  | var     (x : String)
  | unop    (op : UnOp) (e : Expr)
  | binop   (op : BinOp) (l r : Expr)
  | cond    (c t e : Expr)
  | call    (f : String) (args : List Expr)
  | newObj  (c : String)
  | newVec  (t : Ty) (n : Expr)
  | field   (e : Expr) (f : String)
  | arrow   (e : Expr) (f : String)
  | deref   (e : Expr)
  | index   (e i : Expr)
  | lambda  (params : List Param) (ret : Ty) (body : List Cmd)
  | callFn  (f : Expr) (args : List Expr)
  deriving Repr, BEq, Inhabited

/-- Commands. A block is a list of commands. `exprStmt` is the statement that
evaluates an expression and discards its value. `declRef` is the local
reference `τ& x = e`, a second name for the location `e` denotes. -/
inductive Cmd where
  | block    (cs : List Cmd)
  | ite      (c : Expr) (t : List Cmd) (e : List Cmd)
  | while    (c : Expr) (body : List Cmd)
  | for      (init : Cmd) (c : Expr) (step : Cmd) (body : List Cmd)
  | ret      (e : Option Expr)
  | decl     (ty : Ty) (x : String) (init : Expr)
  | declRef  (ty : Ty) (x : String) (init : Expr)
  | declAuto (x : String) (init : Expr)
  | assign   (lhs rhs : Expr)
  | exprStmt (e : Expr)
  deriving Repr, BEq, Inhabited

end

mutual

/-- The variables an expression mentions, the candidates for capture by a
lambda. A nested lambda contributes its own free variables, its parameters
excluded. -/
partial def Expr.vars : Expr → List String
  | .var x => [x]
  | .unop _ e | .deref e | .field e _ | .arrow e _ | .newVec _ e => e.vars
  | .binop _ a b | .index a b => a.vars ++ b.vars
  | .cond a b c => a.vars ++ b.vars ++ c.vars
  | .call _ es => es.flatMap Expr.vars
  | .callFn f es => f.vars ++ es.flatMap Expr.vars
  | .lambda ps _ b => (b.flatMap Cmd.vars).filter fun x => !(ps.any (·.name == x))
  | .intLit _ | .boolLit _ | .nullptr | .newObj _ => []

partial def Cmd.vars : Cmd → List String
  | .block cs => cs.flatMap Cmd.vars
  | .ite c t e => c.vars ++ t.flatMap Cmd.vars ++ e.flatMap Cmd.vars
  | .while c b => c.vars ++ b.flatMap Cmd.vars
  | .for i c s b => i.vars ++ c.vars ++ s.vars ++ b.flatMap Cmd.vars
  | .ret none => []
  | .ret (some e) | .exprStmt e | .decl _ _ e | .declRef _ _ e | .declAuto _ e => e.vars
  | .assign l r => l.vars ++ r.vars

end

structure Fun where
  ret    : Ty
  name   : String
  params : List Param
  body   : List Cmd
  deriving Repr, BEq, Inhabited

/-- A class with public fields only. Methods, constructors and destructors
come in UD V. -/
structure ClassDecl where
  name   : String
  fields : List (Ty × String)
  deriving Repr, BEq, Inhabited

/-- Top level declarations. -/
inductive Decl where
  | cls (c : ClassDecl)
  | fn  (f : Fun)
  deriving Repr, BEq, Inhabited

/-- A program is a list of declarations. There are no global variables. -/
abbrev Program := List Decl

def Program.funs (p : Program) : List Fun :=
  p.filterMap fun | .fn f => some f | _ => none

def Program.classes (p : Program) : List ClassDecl :=
  p.filterMap fun | .cls c => some c | _ => none

def Program.lookupClass (p : Program) (c : String) : Option ClassDecl :=
  p.classes.find? (·.name == c)

def ClassDecl.fieldType (c : ClassDecl) (f : String) : Option Ty :=
  (c.fields.find? (·.2 == f)).map (·.1)

end CoreCpp
