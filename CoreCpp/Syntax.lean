/-!
# Core C++ abstract syntax, subset

Basic types, class and pointer types, vectors, function types, expressions,
lambdas, commands, classes with fields, methods, constructors, destructors and
single inheritance, and functions. A statement is a command or an expression
followed by `;`. Assignment and `delete` are commands. One tree per
nonterminal of the grammar in section 4 of the language design. Namespaces
are flattened by the parser into qualified class names, `N::C`.
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
`f` when `f` is a variable in scope, or the method `f` of `this` inside a
class. `newObj C args` is `new C(args)`, which allocates the object and runs
the constructor. `this` is the location of the receiver inside a method.
`methodCall e arrow m args static` is `e.m(args)` when `arrow` is false and
`e->m(args)` when it is true. The field `static` is the class of the receiver
as the type checker sees it, filled by `Typing.annotate` and `none` as the
parser leaves it, the datum the evaluator needs to tell a dispatched call from
a static one. -/
inductive Expr where
  | intLit  (n : Int)
  | boolLit (b : Bool)
  | nullptr
  | var     (x : String)
  | unop    (op : UnOp) (e : Expr)
  | binop   (op : BinOp) (l r : Expr)
  | cond    (c t e : Expr)
  | call    (f : String) (args : List Expr)
  | newObj  (c : String) (args : List Expr)
  | newVec  (t : Ty) (n : Expr)
  | this
  | methodCall (recv : Expr) (arrow : Bool) (m : String) (args : List Expr) (static : Option String)
  | field   (e : Expr) (f : String)
  | arrow   (e : Expr) (f : String)
  | deref   (e : Expr)
  | index   (e i : Expr)
  | lambda  (params : List Param) (ret : Ty) (body : List Cmd)
  | callFn  (f : Expr) (args : List Expr)
  deriving Repr, BEq, Inhabited

/-- Commands. A block is a list of commands. `exprStmt` is the statement that
evaluates an expression and discards its value. `declRef` is the local
reference `τ& x = e`, a second name for the location `e` denotes. `delete e
static` is `delete e;`, with `static` the class of the pointer as the type
checker sees it, filled by `Typing.annotate`. -/
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
  | delete   (e : Expr) (static : Option String)
  deriving Repr, BEq, Inhabited

end

mutual

/-- The variables an expression mentions, the candidates for capture by a
lambda. A nested lambda contributes its own free variables, its parameters
excluded. -/
partial def Expr.vars : Expr → List String
  | .var x => [x]
  | .this => ["this"]
  | .unop _ e | .deref e | .field e _ | .arrow e _ | .newVec _ e => e.vars
  | .binop _ a b | .index a b => a.vars ++ b.vars
  | .cond a b c => a.vars ++ b.vars ++ c.vars
  | .call _ es | .newObj _ es => es.flatMap Expr.vars
  | .callFn f es | .methodCall f _ _ es _ => f.vars ++ es.flatMap Expr.vars
  | .lambda ps _ b => (b.flatMap Cmd.vars).filter fun x => !(ps.any (·.name == x))
  | .intLit _ | .boolLit _ | .nullptr => []

partial def Cmd.vars : Cmd → List String
  | .block cs => cs.flatMap Cmd.vars
  | .ite c t e => c.vars ++ t.flatMap Cmd.vars ++ e.flatMap Cmd.vars
  | .while c b => c.vars ++ b.flatMap Cmd.vars
  | .for i c s b => i.vars ++ c.vars ++ s.vars ++ b.flatMap Cmd.vars
  | .ret none => []
  | .ret (some e) | .exprStmt e | .decl _ _ e | .declRef _ _ e | .declAuto _ e | .delete e _ => e.vars
  | .assign l r => l.vars ++ r.vars

end

structure Fun where
  ret    : Ty
  name   : String
  params : List Param
  body   : List Cmd
  deriving Repr, BEq, Inhabited

/-- Visibility of a member. Members before any section label are private, as
in C++. -/
inductive Vis where
  | pub | priv
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A field of a class. -/
structure Field where
  ty   : Ty
  name : String
  vis  : Vis := .pub
  deriving Repr, BEq, Inhabited

/-- A method, defined inside the class. `isVirtual` marks `virtual`, which
makes the call dispatch by the class tag of the receiver, and `isOverride`
marks `override`, required on a method that redefines a `virtual` one. -/
structure Method where
  name       : String
  ret        : Ty
  params     : List Param
  body       : List Cmd
  vis        : Vis := .pub
  isVirtual  : Bool := false
  isOverride : Bool := false
  deriving Repr, BEq, Inhabited

/-- The constructor of a class, named after the class and run by `new` after
the fields are allocated. -/
structure Ctor where
  params : List Param
  body   : List Cmd
  deriving Repr, BEq, Inhabited

/-- The destructor of a class, `~C()`, run by `delete` before the locations of
the object leave the store. -/
structure Dtor where
  body      : List Cmd
  isVirtual : Bool := false
  deriving Repr, BEq, Inhabited

/-- A class, with an optional base class, fields, methods, at most one
constructor and at most one destructor. Names are qualified by their
namespace, `N::C`. -/
structure ClassDecl where
  name    : String
  base    : Option String := none
  fields  : List Field
  methods : List Method := []
  ctor    : Option Ctor := none
  dtor    : Option Dtor := none
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

/-- The chain of a class, the class itself, its base, the base of the base
and so on. A cycle or an unknown base ends the chain, and the type checker
rejects both. -/
partial def Program.chain (p : Program) (c : String) (fuel : Nat := 64) : List ClassDecl :=
  match fuel, p.lookupClass c with
  | 0, _ | _, none => []
  | fuel + 1, some cd =>
    match cd.base with
    | none => [cd]
    | some b => cd :: p.chain b fuel

/-- Every field of a class, the fields of the root base first, each with the
class that declares it. -/
def Program.allFields (p : Program) (c : String) : List (Field × String) :=
  (p.chain c).reverse.flatMap fun cd => cd.fields.map fun f => (f, cd.name)

/-- The field f as seen from class c, with the class that declares it. -/
def Program.findField (p : Program) (c f : String) : Option (Field × String) :=
  (p.allFields c).find? (·.1.name == f)

/-- The method m as seen from class c, the nearest declaration in the chain,
with the class that declares it. -/
def Program.findMethod (p : Program) (c m : String) : Option (Method × String) :=
  (p.chain c).findSome? fun cd => (cd.methods.find? (·.name == m)).map (·, cd.name)

/-- d is c or derives from c. -/
def Program.subclass (p : Program) (d c : String) : Bool :=
  (p.chain d).any (·.name == c)

/-- Some class in the chain of c declares a virtual destructor, so `delete`
through a pointer to c reaches the destructor of the tag. -/
def Program.hasVirtualDtor (p : Program) (c : String) : Bool :=
  (p.chain c).any fun cd => cd.dtor.any (·.isVirtual)

end CoreCpp
