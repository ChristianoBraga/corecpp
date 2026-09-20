/-!
# Core C++ abstract syntax, subset

Basic types, class and pointer types, vectors, expressions, commands,
classes with fields and functions. A statement is a command or an expression
followed by `;`. Assignment is a command. One tree per nonterminal of the
grammar in section 4 of the language design.
-/

namespace CoreCpp

/-- Types. `cls` is a class type, reached only through a pointer, `ptr` a
pointer type, `vec` the type of `std::vector<τ>`, also reached only through a
pointer, and `nullT` the type of `nullptr`, which converts to any pointer type
and never names a variable. -/
inductive Ty where
  | int | bool | void
  | cls (name : String)
  | ptr (t : Ty)
  | vec (t : Ty)
  | nullT
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Object types are class and vector types. Their values live in the store
and are never copied, so no variable, parameter or result has an object
type. -/
def Ty.isObject : Ty → Bool
  | .cls _ | .vec _ => true
  | _ => false

inductive UnOp where
  | not | neg
  deriving Repr, BEq, DecidableEq

inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or
  deriving Repr, BEq, DecidableEq

/-- Expressions. Function call is included because `Args` is part of
`PostfixExpr`. `field` is `e.f`, `arrow` is `e->f`, `deref` is `*e` and
`index` is `e[i]`. `newObj C` is `new C()` and `newVec τ n` is
`new std::vector<τ>(n)`. -/
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
  deriving Repr, BEq, Inhabited

/-- Commands. A block is a list of commands. `exprStmt` is the statement that
evaluates an expression and discards its value. -/
inductive Cmd where
  | block    (cs : List Cmd)
  | ite      (c : Expr) (t : List Cmd) (e : List Cmd)
  | while    (c : Expr) (body : List Cmd)
  | for      (init : Cmd) (c : Expr) (step : Cmd) (body : List Cmd)
  | ret      (e : Option Expr)
  | decl     (ty : Ty) (x : String) (init : Expr)
  | declAuto (x : String) (init : Expr)
  | assign   (lhs rhs : Expr)
  | exprStmt (e : Expr)
  deriving Repr, BEq, Inhabited

structure Param where
  ty   : Ty
  name : String
  deriving Repr, BEq, Inhabited

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
