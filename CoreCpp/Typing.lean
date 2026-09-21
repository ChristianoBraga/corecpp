import CoreCpp.Syntax
import CoreCpp.Pretty
import CoreCpp.Templates

/-!
# Static semantics of Core C++, subset

The judgment Γ ⊢ e : τ for expressions, Γ ⊢ₗ e : τ for the expressions that
denote a location, and Γ ⊢ c ⊣ Γ' for commands, where Γ' is Γ extended by the
declarations of c, so that a declaration reaches the following commands of a
sequence and a block discards the extension. Functions are checked against
their declared return type. The class table of the program is a parameter of
every judgment. Each rule is in the comment of the case that implements it.

Object types, classes and vectors, have no values. An expression of object
type occurs only as the operand of `.`, `[]` or `*`, never as a variable, a
parameter, a result, an operand or an argument.

A lambda expression has no type of its own. It is checked against the
`std::function` type expected at one of its three positions, argument,
initialiser and `return`, by the judgment Γ ⊢ e ◁ τ, "e is acceptable at
type τ", which for every other expression is Γ ⊢ e : τ' with τ' ≈ τ. Inside a
lambda body the captured variables are read only, recorded by the `const` mark
of their bindings in Γ.

Classes have sections, fields, methods, a constructor and a destructor, and
single inheritance. Inside a method the binding `this ↦ C*` of Γ tells the
current class, so a private member is reachable exactly when `this` has the
declaring class, and an unqualified field or method name denotes the member
of `this`. A pointer to a derived class is accepted where a pointer to its
base is expected, subsumption, the only conversion between class types. A
derived class redefines a method only when the base declares it `virtual`,
and then marks it `override`, so the method reached from the static type and
the one reached from the class tag coincide for every non virtual method.

Functions and methods are overloaded by the type of the arguments. A name
denotes an overload set, and a call selects the candidate that accepts the
arguments, the exact one when several accept. Two overloads of one name
differ in arity or in a parameter of a type other than `std::function`, so a
lambda argument never decides a call. An infix operator on an operand of
class type, and the indexing of an object, are the calls of the members
`operator⊕` and `operator[]`, which the type checker rewrites. A member may
return `τ&`, and then a call to it denotes a location, which is what makes
`v[i] = x` work on a class of the subset.

Class templates are expanded before checking, by `Templates.instantiate`. A
template is never checked, only its instantiations are.

After checking, `annotate` fills in the static class of every method call,
the signature of the overload every call selects and the `delete`s, the data
the evaluator needs for dispatch and for the destructor check, since ρ and σ
carry no types.

Not checked here, and left to the evaluator as `missingReturn`, is that every
path of a non-void function ends in a return.
-/

namespace CoreCpp

/-- A binding of Γ. `const` marks a variable captured by copy in a lambda body,
which the body may read and not write. -/
structure TBind where
  ty    : Ty
  const : Bool := false
  deriving Repr, BEq, Inhabited

/-- Typing context Γ, a finite map from identifiers to types. -/
abbrev TEnv := List (String × TBind)

def TEnv.lookup (Γ : TEnv) (x : String) : Option Ty :=
  (Γ.find? (·.1 == x)).map (·.2.ty)

def TEnv.isConst (Γ : TEnv) (x : String) : Bool :=
  ((Γ.find? (·.1 == x)).map (·.2.const)).getD false

/-- Γ[x ↦ τ] -/
def TEnv.bind (Γ : TEnv) (x : String) (t : Ty) : TEnv := (x, ⟨t, false⟩) :: Γ

/-- Γ with every binding marked read only, the context of a lambda body. -/
def TEnv.captured (Γ : TEnv) : TEnv := Γ.map fun (x, b) => (x, { b with const := true })

/-- The current class, the class of `this` when Γ binds it, inside a method,
a constructor or a destructor. -/
def TEnv.self (Γ : TEnv) : Option String :=
  match Γ.lookup "this" with
  | some (.ptr (.cls c)) => some c
  | _ => none

inductive TypeError where
  | undeclaredVariable (x : String)
  | undeclaredFunction (f : String)
  | duplicateFunction (f : String)
  | duplicateClass (c : String)
  | unknownClass (c : String)
  | unknownField (c f : String)
  | arity (f : String) (expected got : Nat)
  | mismatch (context : String) (expected got : Ty)
  | notLvalue (e : Expr)
  | voidValue (e : Expr)
  | objectValue (e : Expr) (t : Ty)
  | objectByValue (context : String) (t : Ty)
  | functionStored (context : String) (t : Ty)
  | notPointer (e : Expr) (t : Ty)
  | notObject (e : Expr) (t : Ty)
  | notVector (e : Expr) (t : Ty)
  | notFunction (e : Expr) (t : Ty)
  | lambdaPosition (e : Expr)
  | lambdaMismatch (expected : Ty)
  | constCapture (x : String)
  | refArgument (f x : String) (e : Expr)
  | badOperand (op : String) (t : Ty)
  | returnOutside
  | missingMain
  | unknownMethod (c m : String)
  | privateMember (c m : String)
  | noConstructor (c : String)
  | baseConstructorParams (c b : String)
  | redefinesNonVirtual (c m : String)
  | overrideWithoutVirtual (c m : String)
  | signatureMismatch (c m : String)
  | unknownBase (c b : String)
  | cyclicInheritance (c : String)
  | duplicateMember (c m : String)
  | fieldRedeclared (c f : String)
  | thisOutside
  | notDeletable (e : Expr) (t : Ty)
  | noOverload (f : String)
  | ambiguousCall (f : String)
  | indistinguishable (f : String)
  | refReturnNotLvalue (m : String) (e : Expr)
  | operatorArity (c m : String)
  | instantiation (msg : String)
  deriving Repr

def TypeError.toString : TypeError → String
  | .undeclaredVariable x => s!"undeclared variable {x}"
  | .undeclaredFunction f => s!"undeclared function {f}"
  | .duplicateFunction f  => s!"function {f} declared twice"
  | .duplicateClass c     => s!"class {c} declared twice"
  | .unknownClass c       => s!"unknown class {c}"
  | .unknownField c f     => s!"class {c} has no field {f}"
  | .arity f e g          => s!"call to {f} with {g} arguments, expected {e}"
  | .mismatch c e g       => s!"{c}: expected {e}, got {g}"
  | .notLvalue e          => s!"expression does not denote a location: {e}"
  | .voidValue e          => s!"void expression used as a value: {e}"
  | .objectValue e t      => s!"object of type {t} used as a value: {e}"
  | .objectByValue c t    => s!"{c} has the object type {t}, objects live behind pointers"
  | .functionStored c t   => s!"{c} has the function type {t}, function values live in variables and parameters only"
  | .notPointer e t       => s!"{e} has type {t}, not a pointer"
  | .notObject e t        => s!"{e} has type {t}, not a class"
  | .notVector e t        => s!"{e} has type {t}, not a vector"
  | .notFunction e t      => s!"{e} has type {t}, not a std::function"
  | .lambdaPosition e     => s!"a lambda occurs only as argument, initialiser or return expression: {e}"
  | .lambdaMismatch t     => s!"a lambda must be typed against a std::function type, got {t}"
  | .constCapture x       => s!"{x} is captured by copy and read only inside the lambda"
  | .refArgument f x e    => s!"argument for the reference parameter {x} of {f} does not denote a location: {e}"
  | .badOperand op t      => s!"operator {op} applied to {t}"
  | .returnOutside        => "return outside a function"
  | .missingMain          => "no function int main()"
  | .unknownMethod c m    => s!"class {c} has no method {m}"
  | .privateMember c m    => s!"{m} is a private member of {c}"
  | .noConstructor c      => s!"class {c} has no constructor for these arguments"
  | .baseConstructorParams c b => s!"the base {b} of {c} has a constructor with parameters, and there is no initialiser list"
  | .redefinesNonVirtual c m => s!"{c} redefines the method {m}, which the base does not declare virtual"
  | .overrideWithoutVirtual c m => s!"{c} marks {m} override, but no base declares a virtual {m}"
  | .signatureMismatch c m => s!"the method {m} of {c} has a signature different from the one it overrides"
  | .unknownBase c b      => s!"class {c} derives from the unknown class {b}"
  | .cyclicInheritance c  => s!"the inheritance chain of {c} is cyclic"
  | .duplicateMember c m  => s!"class {c} declares {m} twice"
  | .fieldRedeclared c f  => s!"class {c} redeclares the field {f} of a base"
  | .thisOutside          => "this outside a class"
  | .notDeletable e t     => s!"delete of {e} of type {t}, not a pointer to an object"
  | .noOverload f         => s!"no overload of {f} accepts these arguments"
  | .ambiguousCall f      => s!"the call of {f} is ambiguous, more than one overload accepts these arguments"
  | .indistinguishable f  => s!"two declarations of {f} are not distinguished by a parameter of a type other than std::function"
  | .refReturnNotLvalue m e => s!"{m} returns a reference, and {e} does not denote a location"
  | .operatorArity c m    => s!"the operator {m} of {c} does not have the arity of the operator"
  | .instantiation msg    => msg

instance : ToString TypeError := ⟨TypeError.toString⟩

abbrev T (α : Type) := Except TypeError α

namespace Typing

/-- Requires a type that has values, neither void nor an object type. -/
def value (e : Expr) (t : Ty) : T Ty :=
  if t == .void then .error (.voidValue e)
  else if t.isObject then .error (.objectValue e t)
  else .ok t

/-- τ ≈ τ', the type τ of a value is accepted where τ' is expected. Equal
types, nullptr against a pointer type, or, by subsumption, a pointer to a
derived class where a pointer to its base is expected. These and the lambda
to `std::function` are the only implicit conversions. -/
def compat (p : Program) : Ty → Ty → Bool
  | .nullT, .ptr _ => true
  | .ptr _, .nullT => true
  | .ptr (.cls d), .ptr (.cls b) => d == b || p.subclass d b
  | t₁, t₂ => t₁ == t₂

/-- Two overloads of one name are declared together only when they differ in
arity or in a parameter of a type other than `std::function`, the check 5 of
the design. The restriction keeps a lambda argument from deciding a call,
which would ask for the type of the lambda before the candidate is known.

    arities differ, or ∃ i. pᵢ ≠ qᵢ and neither pᵢ nor qᵢ is std::function
    ──────────────────────────────────────────────────────────────────── (Distinguishable)
    the two declarations are overloads                                          -/
def distinguishable (ps qs : List Param) : Bool :=
  ps.length != qs.length ||
    (ps.zip qs).any fun (a, b) => a.ty != b.ty && !a.ty.isFn && !b.ty.isFn

/-- τ₁ ≈ τ₂ in either direction, for comparison and for the branches of `?:`. -/
def related (p : Program) (t₁ t₂ : Ty) : Bool := compat p t₁ t₂ || compat p t₂ t₁

/-- Requires that a variable, parameter or result type has values. A `τ&`
parameter and a local reference bind the location of their argument, so an
object type is admissible there and nowhere else, which is how a member takes
an object without copying it. -/
def storable (context : String) (t : Ty) : T Unit :=
  if t.isObject || t == .nullT then .error (.objectByValue context t) else .ok ()

/-- Requires a type a binding may have, an object type included when the
binding is a reference. -/
def bindable (context : String) (byRef : Bool) (t : Ty) : T Unit :=
  if byRef && t.isObject then .ok () else storable context t

/-- Fields and vector elements hold basic values and pointers, never function
values, which have no default value in this subset. -/
def noFunction (context : String) (t : Ty) : T Unit :=
  match t with
  | .fn .. => .error (.functionStored context t)
  | _ => .ok ()

/-- A type mentioned in a declaration names only declared classes, and a
function type has a storable or void result and storable parameters. -/
partial def wellFormed (p : Program) : Ty → T Unit
  | .cls c => if (p.lookupClass c).isSome then .ok () else .error (.unknownClass c)
  | .ptr t | .vec t => wellFormed p t
  | .fn r ps => do
    if r != .void then storable "result of a std::function" r
    wellFormed p r
    for t in ps do
      storable "parameter of a std::function" t
      wellFormed p t
  | _ => .ok ()

mutual

/-- Γ ⊢ e : τ -/
partial def expr (p : Program) (Γ : TEnv) : Expr → T Ty
  /-  ─────────────── (T-Lit)      ─────────────── (T-BoolLit)      ───────────────────── (T-Null)
      Γ ⊢ n : int                  Γ ⊢ b : bool                     Γ ⊢ nullptr : nullptr_t   -/
  | .intLit _  => .ok .int
  | .boolLit _ => .ok .bool
  | .nullptr   => .ok .nullT
  /-  Γ(x) = τ                     x ∉ Γ    Γ(this) = C*    Γ ⊢ this->x : τ
      ─────────── (T-Var)          ─────────────────────────────────────── (T-VarField)
      Γ ⊢ x : τ                    Γ ⊢ x : τ                                   -/
  | .var x =>
    match Γ.lookup x with
    | some t => .ok t
    | none   =>
      match Γ.self with
      | some c => if (p.findField c x).isSome then fieldType p Γ c x else .error (.undeclaredVariable x)
      | none => .error (.undeclaredVariable x)
  /-  Γ(this) = C*
      ──────────────── (T-This)      only inside a method, a constructor or a destructor
      Γ ⊢ this : C*                                                                -/
  | .this =>
    match Γ.lookup "this" with
    | some t => .ok t
    | none => .error .thisOutside
  /-  Γ ⊢ e : bool                 Γ ⊢ e : int
      ────────────── (T-Not)       ────────────── (T-Neg)                           -/
  | .unop .not e => do
    let t ← expr p Γ e
    if t == .bool then .ok .bool else .error (.badOperand "!" t)
  | .unop .neg e => do
    let t ← expr p Γ e
    if t == .int then .ok .int else .error (.badOperand "-" t)
  /-  Γ ⊢ e₁ : bool    Γ ⊢ e₂ : bool
      ──────────────────────────────── (T-Logic, ⊙ ∈ {&&, ||})
      Γ ⊢ e₁ ⊙ e₂ : bool                                                           -/
  | .binop op e₁ e₂ => do
    let t₁ ← expr p Γ e₁
    /-  Γ ⊢ e₁ : C    C has operator⊕ visible from Γ    Γ ⊢ e₁.operator⊕(e₂) : τ
        ──────────────────────────────────────────────────────────────────── (T-OpBin)
        Γ ⊢ e₁ ⊕ e₂ : τ

        The left operand decides, so no operator on int or bool changes
        meaning, and && and || are not overloaded.                           -/
    if op != .and && op != .or then
      if let .cls _ := t₁ then
        return ← methodCall p Γ e₁ false s!"operator{op.toString}" [e₂]
    let t₂ ← expr p Γ e₂
    match op with
    | .and | .or =>
      if t₁ == .bool && t₂ == .bool then .ok .bool
      else .error (.badOperand op.toString (if t₁ != .bool then t₁ else t₂))
    /-  Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
        ──────────────────────────── (T-Arith, ⊕ ∈ {+, −, ×, /, %})
        Γ ⊢ e₁ ⊕ e₂ : int                                                          -/
    | .add | .sub | .mul | .div | .mod =>
      if t₁ == .int && t₂ == .int then .ok .int
      else .error (.badOperand op.toString (if t₁ != .int then t₁ else t₂))
    /-  Γ ⊢ e₁ : τ₁    Γ ⊢ e₂ : τ₂    τ₁ ≈ τ₂    τ₁, τ₂ ∈ {int, bool, τ*, nullptr_t}
        ──────────────────────────────────────────────────────────────────── (T-Eq, ⋈ ∈ {==, !=})
        Γ ⊢ e₁ ⋈ e₂ : bool                                                         -/
    | .eq | .ne =>
      if related p t₁ t₂ && t₁ != .void && !t₁.isObject && !t₁.isFn then .ok .bool
      else .error (.mismatch s!"operands of {op.toString}" t₁ t₂)
    /-  Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
        ──────────────────────────── (T-Rel, ⋈ ∈ {<, <=, >, >=})
        Γ ⊢ e₁ ⋈ e₂ : bool                                                         -/
    | .lt | .le | .gt | .ge =>
      if t₁ == .int && t₂ == .int then .ok .bool
      else .error (.badOperand op.toString (if t₁ != .int then t₁ else t₂))
  /-  Γ ⊢ e₁ : bool    Γ ⊢ e₂ : τ    Γ ⊢ e₃ : τ    τ has values
      ────────────────────────────────────────────────────── (T-Cond)
      Γ ⊢ e₁ ? e₂ : e₃ : τ                                                         -/
  | .cond e₁ e₂ e₃ => do
    let t₁ ← expr p Γ e₁
    if t₁ != .bool then throw (.mismatch "condition" .bool t₁)
    let t₂ ← value e₂ (← expr p Γ e₂)
    let t₃ ← value e₃ (← expr p Γ e₃)
    if t₂ == t₃ then .ok t₂
    else if compat p t₂ t₃ then .ok t₃
    else if compat p t₃ t₂ then .ok t₂
    else .error (.mismatch "branches of ?:" t₂ t₃)
  /-  Γ(f) = std::function<τ(τ₁, …, τₖ)>    Γ ⊢ eᵢ ◁ τᵢ for each i
      ─────────────────────────────────────────────────────────── (T-CallFn)     a variable f bound to a
      Γ ⊢ f(e₁, …, eₖ) : τ                                                        function value hides the
                                                                                 function named f
      f ∉ Γ    f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c }), the overload T-Overload selects
      Γ ⊢ eᵢ ◁ τᵢ for each parameter by value    Γ ⊢ₗ eⱼ : τⱼ for each parameter τⱼ& xⱼ
      ────────────────────────────────────────────────────────────────────────────── (T-Call)
      Γ ⊢ f(e₁, …, eₖ) : τ                                                         -/
  | .call f es _ => do
    match Γ.lookup f with
    | some t => callValue p Γ (.var f) t es
    | none =>
      if (p.funsNamed f).isEmpty then
        /-  f ∉ Γ    f not a function    Γ(this) = C*    Γ ⊢ this->f(e₁, …, eₖ) : τ
            ──────────────────────────────────────────────────────────────────── (T-CallThis)
            Γ ⊢ f(e₁, …, eₖ) : τ                                                        -/
        match Γ.self with
        | some c => if !(p.findMethods c f).isEmpty then methodCall p Γ .this true f es else throw (.undeclaredFunction f)
        | none => throw (.undeclaredFunction f)
      else return (← resolveFun p Γ f es).ret
  /-  Γ ⊢ e : std::function<τ(τ₁, …, τₖ)>    Γ ⊢ eᵢ ◁ τᵢ for each i
      ─────────────────────────────────────────────────────────── (T-CallFn)
      Γ ⊢ e(e₁, …, eₖ) : τ                                                         -/
  | .callFn fe es => do
    let t ← expr p Γ fe
    callValue p Γ fe t es
  /-  A lambda has no type of its own. Outside its three positions it is an
      error, see `lambdaAt` for Γ ⊢ [=](…) -> τ { c } ◁ std::function<…>.        -/
  | e@(.lambda ..) => .error (.lambdaPosition e)
  /-  Γ ⊢ₗ e : τ
      ────────────── (T-LocOf)      internal, the annotation of the return of a
      Γ ⊢ &e : τ                    member that returns a reference              -/
  | .locOf e => lval p Γ e
  /-  C ↦ class C { … C(p₁ x₁, …, pₖ xₖ) { c } … }    arguments as in T-Call
      ──────────────────────────────────────────────────────────────── (T-New)
      Γ ⊢ new C(e₁, …, eₖ) : C*

      A class without a constructor is created by new C() alone.                    -/
  | .newObj c es => do
    let some cd := p.lookupClass c | throw (.unknownClass c)
    match cd.ctor with
    | none => if es.isEmpty then pure () else throw (.noConstructor c)
    | some k =>
      if k.params.length != es.length then throw (.noConstructor c)
      checkArgs p Γ c k.params es
    return .ptr (.cls c)
  /-  Γ ⊢ e : C    C has τ m(p₁ x₁, …, pₖ xₖ), visible from Γ    arguments as in T-Call
      ────────────────────────────────────────────────────────────────────────── (T-Method)
      Γ ⊢ e.m(e₁, …, eₖ) : τ

      Γ ⊢ e : C*    C has τ m(…), visible from Γ    arguments as in T-Call
      ──────────────────────────────────────────────────────────────── (T-MethodArrow)
      Γ ⊢ e->m(e₁, …, eₖ) : τ

      A private method is visible only when Γ(this) is the class that
      declares it. The method is the nearest one in the chain of C.              -/
  | .methodCall recv arrow m es _ _ => methodCall p Γ recv arrow m es
  /-  Γ ⊢ n : int    τ has values    τ not a function type
      ──────────────────────────────────────────────────── (T-NewVec)
      Γ ⊢ new std::vector<τ>(n) : std::vector<τ>*                                  -/
  | .newVec t n => do
    let tn ← expr p Γ n
    if tn != .int then throw (.mismatch "size of std::vector" .int tn)
    storable "element of std::vector" t
    noFunction "element of std::vector" t
    wellFormed p t
    return .ptr (.vec t)
  /-  Γ ⊢ e : C    C ↦ class C { … τ f; … }
      ──────────────────────────────────── (T-Field)
      Γ ⊢ e.f : τ                                                                  -/
  | .field e f => do
    let t ← expr p Γ e
    let .cls c := t | throw (.notObject e t)
    fieldType p Γ c f
  /-  Γ ⊢ e : C*    C ↦ class C { … τ f; … }
      ────────────────────────────────────── (T-Arrow)      e->f abbreviates (*e).f
      Γ ⊢ e->f : τ                                                                 -/
  | .arrow e f => do
    let t ← expr p Γ e
    let .ptr (.cls c) := t | throw (.notPointer e t)
    fieldType p Γ c f
  /-  Γ ⊢ e : τ*
      ──────────── (T-Deref)
      Γ ⊢ *e : τ                                                                   -/
  | .deref e => do
    let t ← expr p Γ e
    let .ptr t' := t | throw (.notPointer e t)
    return t'
  /-  Γ ⊢ e : std::vector<τ>    Γ ⊢ i : int
      ─────────────────────────────────────── (T-Index)
      Γ ⊢ e[i] : τ                                                                 -/
  /-  Γ ⊢ e : C    C has operator[] visible from Γ    Γ ⊢ e.operator[](i) : τ
      ──────────────────────────────────────────────────────────────────── (T-OpIndex)
      Γ ⊢ e[i] : τ                                                                 -/
  | .index e i => do
    let t ← expr p Γ e
    match t with
    | .vec t' =>
      let ti ← expr p Γ i
      if ti != .int then throw (.mismatch "index" .int ti)
      return t'
    | .cls _ => methodCall p Γ e false "operator[]" [i]
    | _ => throw (.notVector e t)

/-- The call of a function value of type t with the arguments es, shared by
`T-CallFn` on a variable and on any other expression. -/
partial def callValue (p : Program) (Γ : TEnv) (fe : Expr) (t : Ty) (es : List Expr) : T Ty := do
  let .fn r ps := t | throw (.notFunction fe t)
  if ps.length != es.length then throw (.arity fe.toString ps.length es.length)
  for (τ, e) in ps.zip es do
    accept p Γ s!"argument of {fe}" e τ
  return r

/-- Γ ⊢ e ◁ τ, e is acceptable at type τ. For a lambda, `lambdaAt`. For any
other expression, Γ ⊢ e : τ' with τ' ≈ τ and τ' with values.

    Γ ⊢ e : τ'    τ' ≈ τ    τ' has values
    ───────────────────────────────────── (Accept)
    Γ ⊢ e ◁ τ                                                                      -/
partial def accept (p : Program) (Γ : TEnv) (context : String) (e : Expr) (τ : Ty) : T Unit := do
  match e with
  | .lambda ps r b => lambdaAt p Γ ps r b τ
  | _ =>
    let t ← value e (← expr p Γ e)
    if !compat p t τ then throw (.mismatch context τ t)

/-- Γ ⊢ [=](τ₁ x₁, …, τₖ xₖ) -> τ { c } ◁ std::function<τ(τ₁, …, τₖ)>.

    Γ' = Γ marked read only, [x₁ ↦ τ₁, …, xₖ ↦ τₖ]    Γ' ⊢ c ⊣ Γ''    τ, τᵢ storable, well formed
    ───────────────────────────────────────────────────────────────────────────────────── (T-Lambda)
    Γ ⊢ [=](τ₁ x₁, …, τₖ xₖ) -> τ { c } ◁ std::function<τ(τ₁, …, τₖ)>

    The parameter and result types of the lambda are exactly those of the
    expected std::function type. The body is checked under Γ with every
    variable of the enclosing scope marked read only, the copies of `[=]`, and
    with the parameters of the lambda as ordinary variables.                    -/
partial def lambdaAt (p : Program) (Γ : TEnv) (ps : List Param) (r : Ty) (b : List Cmd) (τ : Ty) : T Unit := do
  let .fn r' pts := τ | throw (.lambdaMismatch τ)
  if pts.length != ps.length then throw (.arity "lambda" pts.length ps.length)
  if r != r' then throw (.mismatch "result of the lambda" r' r)
  if r != .void then storable "result of the lambda" r
  wellFormed p r
  for (q, t) in ps.zip pts do
    if q.ty != t then throw (.mismatch s!"parameter {q.name} of the lambda" t q.ty)
    storable s!"parameter {q.name} of the lambda" q.ty
    wellFormed p q.ty
  let Γ' := ps.reverse.foldl (fun Γ q => Γ.bind q.name q.ty) Γ.captured
  let _ ← cmds p r Γ' b

/-- The arguments of a call against the parameters, by value with ◁ and by
reference with ⊢ₗ, shared by T-Call, T-New and T-Method. -/
partial def checkArgs (p : Program) (Γ : TEnv) (f : String) (ps : List Param) (es : List Expr) : T Unit := do
  for (q, e) in ps.zip es do
    if q.byRef then
      let t ← match lval p Γ e with
        | .ok t => pure t
        | .error _ => throw (.refArgument f q.name e)
      if t != q.ty then throw (.mismatch s!"argument {q.name} of {f}" q.ty t)
    else
      accept p Γ s!"argument {q.name} of {f}" e q.ty

/-- The candidate of an overload set that a call selects, by its index. The
candidates that accept the arguments are collected, and the choice is the
exact one when several accept.

    A = the candidates of cand(f, k) that accept e₁, …, eₖ
    A has one element whose parameters are exactly the types of the arguments, or A is a singleton
    ─────────────────────────────────────────────────────────────────────────────── (T-Overload)
    the call of f selects that candidate

    With A empty the error is the one of the single candidate of that arity,
    when there is one, and `no overload` otherwise. With two or more in A and
    no exact one the call is ambiguous. Core C++ does not rank conversion
    sequences, so the rule fits in one line on the board.                        -/
partial def pickOverload (p : Program) (Γ : TEnv) (who : String)
    (cands : List (List Param)) (es : List Expr) : T Nat := do
  let idx := (List.range cands.length).filter fun i => (cands[i]!).length == es.length
  if idx.isEmpty then
    let some ps := cands.head? | throw (.undeclaredFunction who)
    throw (.arity who ps.length es.length)
  let fits := idx.filter fun i => (checkArgs p Γ who (cands[i]!) es).toOption.isSome
  match fits with
  | [i] => return i
  | [] =>
    match idx with
    | [i] => do checkArgs p Γ who (cands[i]!) es; return i
    | _ => throw (.noOverload who)
  | _ =>
    let exact := fits.filter fun i =>
      ((cands[i]!).zip es).all fun (q, e) => (expr p Γ e).toOption == some q.ty
    match exact with
    | [i] => return i
    | _ => throw (.ambiguousCall who)

/-- The function a call selects out of the overload set of its name. -/
partial def resolveFun (p : Program) (Γ : TEnv) (f : String) (es : List Expr) : T Fun := do
  let cands := p.funsNamed f
  if cands.isEmpty then throw (.undeclaredFunction f)
  let i ← pickOverload p Γ f (cands.map (·.params)) es
  return cands[i]!

/-- The method a call selects, with the class that declares it, the rules
T-Method and T-MethodArrow with the overload set of the name. -/
partial def resolveMethod (p : Program) (Γ : TEnv) (recv : Expr) (arrow : Bool) (m : String)
    (es : List Expr) : T (Method × String) := do
  let t ← expr p Γ recv
  let c ← if arrow then
      match t with
      | .ptr (.cls c) => pure c
      | _ => throw (.notPointer recv t)
    else
      match t with
      | .cls c => pure c
      | _ => throw (.notObject recv t)
  let cands := p.findMethods c m
  if cands.isEmpty then throw (.unknownMethod c m)
  let i ← pickOverload p Γ m (cands.map (·.1.params)) es
  let (md, k) := cands[i]!
  if md.vis == .priv && Γ.self != some k then throw (.privateMember k m)
  return (md, k)

/-- The rules T-Method and T-MethodArrow, see `expr`. -/
partial def methodCall (p : Program) (Γ : TEnv) (recv : Expr) (arrow : Bool) (m : String) (es : List Expr) : T Ty := do
  return (← resolveMethod p Γ recv arrow m es).1.ret

/-- The type of field f of class C as seen from Γ, or the error. A private
field is visible only when Γ(this) is the class that declares it.

    C has τ f declared in K    f public or Γ(this) = K*
    ──────────────────────────────────────────────────── (Visible)                -/
partial def fieldType (p : Program) (Γ : TEnv) (c f : String) : T Ty := do
  if (p.lookupClass c).isNone then throw (.unknownClass c)
  let some (fd, k) := p.findField c f | throw (.unknownField c f)
  if fd.vis == .priv && Γ.self != some k then throw (.privateMember k f)
  return fd.ty

/-- The expressions that denote a location, with their type. A variable, a
dereferenced pointer, a field of an object, a field through a pointer and an
element of a vector. A variable captured by copy inside a lambda denotes no
writable location.

    Γ(x) = τ, x not captured   Γ ⊢ e : τ*           Γ ⊢ e : C, C has τ f
    ──────────────────────── (T-LocVar)  ──────────── (T-LocDeref)  ─────────────────── (T-LocField)
    Γ ⊢ₗ x : τ                 Γ ⊢ₗ *e : τ          Γ ⊢ₗ e.f : τ

    Γ ⊢ e : C*, C has τ f                Γ ⊢ e : std::vector<τ>    Γ ⊢ i : int
    ────────────────────── (T-LocArrow)  ─────────────────────────────────── (T-LocIndex)
    Γ ⊢ₗ e->f : τ                        Γ ⊢ₗ e[i] : τ                                       -/
partial def lval (p : Program) (Γ : TEnv) : Expr → T Ty
  | .var x =>
    match Γ.lookup x with
    | some t => if Γ.isConst x then .error (.constCapture x) else .ok t
    | none   =>
      match Γ.self with
      | some c => if (p.findField c x).isSome then fieldType p Γ c x else .error (.undeclaredVariable x)
      | none => .error (.undeclaredVariable x)
  | e@(.deref _) | e@(.field ..) | e@(.arrow ..) => expr p Γ e
  /-  Γ ⊢ e : C    C has τ& operator[] visible from Γ
      ───────────────────────────────────────────────── (T-LocOpIndex)
      Γ ⊢ₗ e[i] : τ

      Γ ⊢ e : C    C has τ& m(…) visible from Γ
      ───────────────────────────────────────────── (T-LocMethod)
      Γ ⊢ₗ e.m(e₁, …, eₖ) : τ

      Indexing a vector denotes a location as before. Indexing an object, and
      calling a member, denote one exactly when the member returns τ&.        -/
  | e@(.index recv i) => do
    let t ← expr p Γ recv
    match t with
    | .vec _ => expr p Γ e
    | .cls _ =>
      let (md, _) ← resolveMethod p Γ recv false "operator[]" [i]
      if md.retRef then return md.ret else throw (.notLvalue e)
    | _ => throw (.notVector recv t)
  | e@(.methodCall recv arrow m es _ _) => do
    let (md, _) ← resolveMethod p Γ recv arrow m es
    if md.retRef then return md.ret else throw (.notLvalue e)
  | e => .error (.notLvalue e)

/-- Γ ⊢ c ⊣ Γ', under the return type τᵣ of the enclosing function. -/
partial def cmd (p : Program) (τᵣ : Ty) (Γ : TEnv) : Cmd → T TEnv
  /-  Γ ⊢ c₁ … cₙ ⊣ Γ'
      ──────────────────── (T-Block)      the block discards Γ'
      Γ ⊢ { c₁ … cₙ } ⊣ Γ                                                         -/
  | .block cs => do
    let _ ← cmds p τᵣ Γ cs
    return Γ
  /-  Γ ⊢ e : bool    Γ ⊢ {c₁} ⊣ Γ    Γ ⊢ {c₂} ⊣ Γ
      ──────────────────────────────────────────── (T-If)
      Γ ⊢ if (e) {c₁} else {c₂} ⊣ Γ                                               -/
  | .ite e t f => do
    let te ← expr p Γ e
    if te != .bool then throw (.mismatch "condition of if" .bool te)
    let _ ← cmd p τᵣ Γ (.block t)
    let _ ← cmd p τᵣ Γ (.block f)
    return Γ
  /-  Γ ⊢ e : bool    Γ ⊢ {c} ⊣ Γ
      ──────────────────────────── (T-While)
      Γ ⊢ while (e) {c} ⊣ Γ                                                       -/
  | .while e b => do
    let te ← expr p Γ e
    if te != .bool then throw (.mismatch "condition of while" .bool te)
    let _ ← cmd p τᵣ Γ (.block b)
    return Γ
  /-  Γ ⊢ c₀ ⊣ Γ₀    Γ₀ ⊢ e : bool    Γ₀ ⊢ cₛ ⊣ Γ₀    Γ₀ ⊢ {c} ⊣ Γ₀
      ─────────────────────────────────────────────────────────── (T-For)
      Γ ⊢ for (c₀; e; cₛ) {c} ⊣ Γ                                                 -/
  | .for c₀ e cₛ b => do
    let Γ₀ ← cmd p τᵣ Γ c₀
    let te ← expr p Γ₀ e
    if te != .bool then throw (.mismatch "condition of for" .bool te)
    let _ ← cmd p τᵣ Γ₀ cₛ
    let _ ← cmd p τᵣ Γ₀ (.block b)
    return Γ
  /-  τᵣ = void                      Γ ⊢ e ◁ τᵣ    τᵣ ≠ void
      ──────────────── (T-RetVoid)   ────────────────────────── (T-Ret)      a lambda may be returned
      Γ ⊢ return ⊣ Γ                 Γ ⊢ return e ⊣ Γ                        at a std::function type   -/
  | .ret none =>
    if τᵣ == .void then .ok Γ else .error (.mismatch "return without value" τᵣ .void)
  | .ret (some e) => do
    if τᵣ == .void then throw (.mismatch "return value" τᵣ (← expr p Γ e))
    accept p Γ "return value" e τᵣ
    return Γ
  /-  Γ ⊢ e ◁ τ    τ has values    τ well formed
      ───────────────────────────────────────── (T-Decl)      Γ[x ↦ τ] reaches the following commands,
      Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]                                  and a lambda initialises a std::function -/
  | .decl t x e => do
    storable s!"variable {x}" t
    wellFormed p t
    accept p Γ s!"initialiser of {x}" e t
    return Γ.bind x t
  /-  Γ ⊢ₗ e : τ    τ has values    τ well formed
      ───────────────────────────────────────────── (T-DeclRef)      the initialiser denotes a location
      Γ ⊢ τ& x = e ⊣ Γ[x ↦ τ]                                        and x has the type of its referent -/
  | .declRef t x e => do
    bindable s!"reference {x}" true t
    wellFormed p t
    let te ← value e (← lval p Γ e)
    if te != t then throw (.mismatch s!"referent of {x}" t te)
    return Γ.bind x t
  /-  Γ ⊢ e : τ    τ has values    τ ≠ nullptr_t
      ─────────────────────────────────────────── (T-Auto)      a lambda has no type for auto to copy
      Γ ⊢ auto x = e ⊣ Γ[x ↦ τ]                                                    -/
  | .declAuto x e => do
    let te ← value e (← expr p Γ e)
    storable s!"variable {x}" te
    return Γ.bind x te
  /-  Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ'    τ' ≈ τ    τ has values
      ───────────────────────────────────────────────── (T-Assign)
      Γ ⊢ e₁ = e₂ ⊣ Γ                                                              -/
  | .assign e₁ e₂ => do
    let t₁ ← lval p Γ e₁
    let _ ← value e₁ t₁
    let t₂ ← value e₂ (← expr p Γ e₂)
    if !compat p t₂ t₁ then throw (.mismatch s!"assignment to {e₁}" t₁ t₂)
    return Γ
  /-  Γ ⊢ e : τ
      ────────────── (T-ExprStmt)      any τ, void included
      Γ ⊢ e; ⊣ Γ                                                                   -/
  | .exprStmt e => do
    let _ ← expr p Γ e
    return Γ
  /-  Γ ⊢ e : C*                    Γ ⊢ e : std::vector<τ>*
      ──────────────── (T-Delete)   ──────────────────────── (T-DeleteVec)
      Γ ⊢ delete e ⊣ Γ              Γ ⊢ delete e ⊣ Γ                              -/
  | .delete e _ => do
    let t ← expr p Γ e
    match t with
    | .ptr (.cls _) | .ptr (.vec _) => return Γ
    | _ => throw (.notDeletable e t)

/-- Γ ⊢ c₁ … cₙ ⊣ Γₙ, threading the context through the sequence.

    ──────────── (T-Seq-Empty)      Γ ⊢ c ⊣ Γ₁    Γ₁ ⊢ cs ⊣ Γ₂
    Γ ⊢ ε ⊣ Γ                       ──────────────────────────── (T-Seq)
                                    Γ ⊢ c cs ⊣ Γ₂                                  -/
partial def cmds (p : Program) (τᵣ : Ty) (Γ : TEnv) : List Cmd → T TEnv
  | [] => .ok Γ
  | c :: cs => do
    let Γ₁ ← cmd p τᵣ Γ c
    cmds p τᵣ Γ₁ cs

end

/-- Every `return` of a member that returns a reference is a `return e` with
`e` denoting a location. The walk does not enter the body of a lambda, whose
`return` is the lambda's own.

    τ has values    every return of c is return e with Γ ⊢ₗ e : τ
    ─────────────────────────────────────────────────────────────── (T-RetRef)
    ⊢ τ& m(…) { c } in C                                                          -/
partial def refReturns (p : Program) (Γ : TEnv) (m : String) : List Cmd → T Unit
  | [] => .ok ()
  | c :: cs => do
    match c with
    | .ret (some e) => let _ ← (lval p Γ e).mapError fun _ => TypeError.refReturnNotLvalue m e
    | .ret none => pure ()
    | .block b | .while _ b => refReturns p Γ m b
    | .ite _ t f => do refReturns p Γ m t; refReturns p Γ m f
    | .for _ _ _ b => refReturns p Γ m b
    | _ => pure ()
    refReturns p Γ m cs

/-- A function is well typed when its parameter and return types have values
and are well formed, and its body is, under the context of its parameters and
its return type. A reference parameter has in Γ the type of its referent, as a
local reference does.

    τ, τᵢ storable and well formed    [x₁ ↦ τ₁, …, xₖ ↦ τₖ] ⊢ c ⊣ Γ'
    ──────────────────────────────────────────────────────────────── (T-Fun)
    ⊢ τ f (τ₁ x₁, …, τₖ xₖ) { c }                                                  -/
def fn (p : Program) (f : Fun) : T Unit := do
  if f.ret != .void then storable s!"result of {f.name}" f.ret
  wellFormed p f.ret
  for q in f.params do
    bindable s!"parameter {q.name} of {f.name}" q.byRef q.ty
    wellFormed p q.ty
  let Γ : TEnv := f.params.reverse.map fun q => (q.name, ⟨q.ty, false⟩)
  let _ ← cmds p f.ret Γ f.body

/-- The context of a member body, `this` bound to a pointer to the class and
the parameters as variables. -/
def memberEnv (c : String) (ps : List Param) : TEnv :=
  (ps.reverse.map fun q => (q.name, ⟨q.ty, false⟩)) ++ [("this", ⟨.ptr (.cls c), false⟩)]

/-- A class is well formed when its base exists and the chain has no cycle,
its fields have types with values, well formed, and repeat no field of a
base, its members have distinct names, each method redefines only a method
the base declares virtual and then carries override, with the same
signature, the constructor of the base, if any, takes no parameters, and
every member body is well typed under `this`.

    B exists, chain acyclic    fields storable, well formed, new in the chain
    for each method m of C. if some base has m then that m is virtual, m is override and the signatures agree
    for each override m of C. some base has a virtual m
    B has no constructor or one with no parameters
    [this ↦ C*, params] ⊢ body ⊣ Γ' for each method, the constructor and the destructor
    ───────────────────────────────────────────────────────────────────────────────────── (T-Class)
    ⊢ class C : public B { … }                                                     -/
def cls (p : Program) (c : ClassDecl) : T Unit := do
  if let some b := c.base then
    if (p.lookupClass b).isNone then throw (.unknownBase c.name b)
  let chain := p.chain c.name
  if chain.isEmpty || (chain.map (·.name)).eraseDups.length != chain.length
     || (chain.getLast?.bind (·.base)).isSome then throw (.cyclicInheritance c.name)
  let baseFields : List String := match c.base with
    | some b => (p.allFields b).map fun (f, _) => f.name
    | none => []
  -- A field name is unique, and two methods of one name are overloads when
  -- they differ in arity or in a parameter of a type other than std::function.
  let fieldNames := c.fields.map (·.name)
  for n in fieldNames do
    if (fieldNames.filter (· == n)).length > 1 then throw (.duplicateMember c.name n)
  for m in c.methods do
    if fieldNames.contains m.name then throw (.duplicateMember c.name m.name)
    for m' in c.methods do
      if m.name == m'.name && sigOf m.params != sigOf m'.params && !distinguishable m.params m'.params then
        throw (.indistinguishable s!"{c.name}::{m.name}")
    if (c.methods.filter fun m' => m'.name == m.name && sigOf m'.params == sigOf m.params).length > 1 then
      throw (.duplicateMember c.name m.name)
  for f in c.fields do
    if baseFields.contains f.name then throw (TypeError.fieldRedeclared c.name f.name)
    storable s!"field {f.name} of {c.name}" f.ty
    wellFormed p f.ty
  for m in c.methods do
    -- Every operator of the subset is binary, the receiver and one parameter.
    if m.name.startsWith "operator" && m.params.length != 1 then
      throw (.operatorArity c.name m.name)
    if m.retRef then
      if m.ret == .void then throw (.mismatch s!"result of {c.name}::{m.name}" m.ret .void)
      refReturns p (memberEnv c.name m.params) s!"{c.name}::{m.name}" m.body
    let inherited := c.base.bind fun b =>
      (p.findMethods b m.name).find? fun (bm, _) => sigOf bm.params == sigOf m.params
    match inherited with
    | some (bm, _) =>
      if !bm.isVirtual then throw (.redefinesNonVirtual c.name m.name)
      if !m.isOverride then throw (.overrideWithoutVirtual c.name m.name)
      if bm.ret != m.ret || bm.params.map (fun q => (q.ty, q.byRef)) != m.params.map (fun q => (q.ty, q.byRef)) then
        throw (.signatureMismatch c.name m.name)
    | none => if m.isOverride then throw (.overrideWithoutVirtual c.name m.name)
    if m.ret != .void then storable s!"result of {c.name}::{m.name}" m.ret
    wellFormed p m.ret
    for q in m.params do
      bindable s!"parameter {q.name} of {c.name}::{m.name}" q.byRef q.ty
      wellFormed p q.ty
    let _ ← cmds p m.ret (memberEnv c.name m.params) m.body
  if let some b := c.base then
    if let some bd := p.lookupClass b then
      if bd.ctor.any (!·.params.isEmpty) then throw (.baseConstructorParams c.name b)
  if let some k := c.ctor then
    for q in k.params do
      bindable s!"parameter {q.name} of the constructor of {c.name}" q.byRef q.ty
      wellFormed p q.ty
    let _ ← cmds p .void (memberEnv c.name k.params) k.body
  if let some d := c.dtor then
    let _ ← cmds p .void (memberEnv c.name []) d.body

end Typing

/-- The program with one class per template instantiation it mentions, the
expansion that precedes every other judgment. Idempotent. -/
def expand (p : Program) : Except TypeError Program :=
  (Templates.instantiate p).mapError TypeError.instantiation

/-- A program is well typed when class and function names are distinct up to
overloading, every class and function is well typed and `int main()` exists.
A template is not checked, only its instantiations are.

    names distinct up to overloading    ⊢ Cᵢ for each class    ⊢ fᵢ for each function
    main ↦ (int main() { c })
    ────────────────────────────────────────────────────────────────────────────── (T-Program)
    ⊢ p                                                                            -/
def check (p₀ : Program) : Except TypeError Unit := do
  let p ← expand p₀
  for f in p.funs do
    for g in p.funs do
      if f.name == g.name && sigOf f.params != sigOf g.params
         && !Typing.distinguishable f.params g.params then
        throw (.indistinguishable f.name)
    if (p.funsNamed f.name |>.filter fun g => sigOf g.params == sigOf f.params).length > 1 then
      throw (.duplicateFunction f.name)
  let cnames := p.classes.map (·.name) ++ p.templates.map (·.2.name)
  for c in cnames do
    if (cnames.filter (· == c)).length > 1 then throw (.duplicateClass c)
  for c in p.classes do Typing.cls p c
  for f in p.funs do Typing.fn p f
  match FunEnv.lookup p "main" with
  | some m => if m.ret == .int && m.params.isEmpty then pure () else throw .missingMain
  | none => throw .missingMain

namespace Typing

/-! ## Static classes and chosen overloads, for the evaluator

The evaluator dispatches a method call by the class tag of the receiver when
the method is virtual, and otherwise runs the method of the static class of
the receiver, and `delete` through a pointer needs the static class to check
that the destructor is virtual when the tag differs. A call also needs the
signature of the overload the type checker selected, since a name may denote
several functions or methods. Neither ρ nor σ carries types, so `annotate`
writes the static class and the signature into the tree after the program has
been checked, rewrites an operator on a class operand and the indexing of an
object into the call of the member, and rewrites the `return e` of a member
that returns a reference into `return &e`, the location as a value. -/

/-- The class a receiver expression has, `C` for `e.m` with `e : C` and for
`e->m` with `e : C*`, and for `delete e` with `e : C*`. -/
def staticClass (t : Ty) (arrow : Bool) : Option String :=
  match arrow, t with
  | true, .ptr (.cls c) => some c
  | false, .cls c => some c
  | _, _ => none

mutual

/-- The annotated call of the member m on the receiver recv, the form every
method call, operator and object indexing takes after annotation. -/
partial def annMethod (p : Program) (Γ : TEnv) (recv : Expr) (arrow : Bool) (m : String)
    (es : List Expr) : T Expr := do
  let t ← expr p Γ recv
  let (md, _) ← resolveMethod p Γ recv arrow m es
  return .methodCall recv arrow m es (staticClass t arrow) (some (sigOf md.params))

partial def annExpr (p : Program) (Γ : TEnv) : Expr → T Expr
  | .unop op e => return .unop op (← annExpr p Γ e)
  | .binop op a b => do
    let a' ← annExpr p Γ a
    let b' ← annExpr p Γ b
    if op != .and && op != .or then
      if let .cls _ ← expr p Γ a' then
        return ← annMethod p Γ a' false s!"operator{op.toString}" [b']
    return .binop op a' b'
  | .cond a b c => return .cond (← annExpr p Γ a) (← annExpr p Γ b) (← annExpr p Γ c)
  | .call f es _ => do
    let es' ← es.mapM (annExpr p Γ)
    if (Γ.lookup f).isNone && (p.funsNamed f).isEmpty then
      if let some c := Γ.self then
        if !(p.findMethods c f).isEmpty then return ← annMethod p Γ .this true f es'
    if (Γ.lookup f).isSome then return .call f es' none
    return .call f es' (some (sigOf (← resolveFun p Γ f es').params))
  | .callFn f es => return .callFn (← annExpr p Γ f) (← es.mapM (annExpr p Γ))
  | .newObj c es => return .newObj c (← es.mapM (annExpr p Γ))
  | .newVec t n => return .newVec t (← annExpr p Γ n)
  | .field e f => return .field (← annExpr p Γ e) f
  | .arrow e f => return .arrow (← annExpr p Γ e) f
  | .deref e => return .deref (← annExpr p Γ e)
  | .locOf e => return .locOf (← annExpr p Γ e)
  | .index e i => do
    let e' ← annExpr p Γ e
    let i' ← annExpr p Γ i
    if let .cls _ ← expr p Γ e' then
      return ← annMethod p Γ e' false "operator[]" [i']
    return .index e' i'
  | .lambda ps r b =>
    let Γ' := ps.reverse.foldl (fun Γ q => Γ.bind q.name q.ty) Γ.captured
    return .lambda ps r (← annCmds p r Γ' b)
  | .methodCall recv arrow m es _ _ => do
    annMethod p Γ (← annExpr p Γ recv) arrow m (← es.mapM (annExpr p Γ))
  | e => return e

partial def annCmd (p : Program) (τᵣ : Ty) (Γ : TEnv) : Cmd → T Cmd
  | .block cs => return .block (← annCmds p τᵣ Γ cs)
  | .ite e t f => return .ite (← annExpr p Γ e) (← annCmds p τᵣ Γ t) (← annCmds p τᵣ Γ f)
  | .while e b => return .while (← annExpr p Γ e) (← annCmds p τᵣ Γ b)
  | .for c₀ e cₛ b => do
    let c₀' ← annCmd p τᵣ Γ c₀
    let Γ₀ ← cmd p τᵣ Γ c₀'
    return .for c₀' (← annExpr p Γ₀ e) (← annCmd p τᵣ Γ₀ cₛ) (← annCmds p τᵣ Γ₀ b)
  | .ret none => return .ret none
  | .ret (some e) => return .ret (some (← annExpr p Γ e))
  | .decl t x e => return .decl t x (← annExpr p Γ e)
  | .declRef t x e => return .declRef t x (← annExpr p Γ e)
  | .declAuto x e => return .declAuto x (← annExpr p Γ e)
  | .assign l r => return .assign (← annExpr p Γ l) (← annExpr p Γ r)
  | .exprStmt e => return .exprStmt (← annExpr p Γ e)
  | .delete e _ => do
    let e' ← annExpr p Γ e
    return .delete e' (staticClass (← expr p Γ e') true)

partial def annCmds (p : Program) (τᵣ : Ty) (Γ : TEnv) : List Cmd → T (List Cmd)
  | [] => return []
  | c :: cs => do
    let c' ← annCmd p τᵣ Γ c
    let Γ' ← cmd p τᵣ Γ c'
    return c' :: (← annCmds p τᵣ Γ' cs)

end

/-- The `return e` of a member that returns a reference becomes `return &e`,
the location as a value, which the caller reads or uses as a location. The
walk does not enter the body of a lambda. -/
partial def refRets : List Cmd → List Cmd
  | [] => []
  | c :: cs =>
    let c' := match c with
      | .ret (some e) => Cmd.ret (some (.locOf e))
      | .block b => .block (refRets b)
      | .while e b => .while e (refRets b)
      | .ite e t f => .ite e (refRets t) (refRets f)
      | .for i e s b => .for i e s (refRets b)
      | c => c
    c' :: refRets cs

/-- The program with the static classes, the chosen overloads and the
reference returns filled in. Fails only on an ill typed program, which
`check` rejects first. -/
def annotate (p₀ : Program) : T Program := do
  let p ← expand p₀
  p.mapM fun
    | .fn f => do
      let Γ : TEnv := f.params.reverse.map fun q => (q.name, ⟨q.ty, false⟩)
      return .fn { f with body := ← annCmds p f.ret Γ f.body }
    | .tmpl t c => return .tmpl t c
    | .cls c => do
      let methods ← c.methods.mapM fun m => do
        let body ← annCmds p m.ret (memberEnv c.name m.params) m.body
        return { m with body := if m.retRef then refRets body else body }
      let ctor ← c.ctor.mapM fun k => do
        return { k with body := ← annCmds p .void (memberEnv c.name k.params) k.body }
      let dtor ← c.dtor.mapM fun d => do
        return { d with body := ← annCmds p .void (memberEnv c.name []) d.body }
      return .cls { c with methods, ctor, dtor }

end Typing

end CoreCpp
