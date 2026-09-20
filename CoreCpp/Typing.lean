import CoreCpp.Syntax
import CoreCpp.Pretty

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

instance : ToString TypeError := ⟨TypeError.toString⟩

abbrev T (α : Type) := Except TypeError α

namespace Typing

/-- Requires a type that has values, neither void nor an object type. -/
def value (e : Expr) (t : Ty) : T Ty :=
  if t == .void then .error (.voidValue e)
  else if t.isObject then .error (.objectValue e t)
  else .ok t

/-- τ₁ ≈ τ₂, equal types, or nullptr against a pointer type. The only implicit
conversion besides the lambda to `std::function`. -/
def compat : Ty → Ty → Bool
  | .nullT, .ptr _ => true
  | .ptr _, .nullT => true
  | t₁, t₂ => t₁ == t₂

/-- Requires that a variable, parameter or result type has values. -/
def storable (context : String) (t : Ty) : T Unit :=
  if t.isObject || t == .nullT then .error (.objectByValue context t) else .ok ()

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
  /-  Γ(x) = τ
      ─────────── (T-Var)                                                          -/
  | .var x =>
    match Γ.lookup x with
    | some t => .ok t
    | none   => .error (.undeclaredVariable x)
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
      if compat t₁ t₂ && t₁ != .void && !t₁.isObject && !t₁.isFn then .ok .bool
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
    else if compat t₂ t₃ then .ok (if t₂ == .nullT then t₃ else t₂)
    else .error (.mismatch "branches of ?:" t₂ t₃)
  /-  Γ(f) = std::function<τ(τ₁, …, τₖ)>    Γ ⊢ eᵢ ◁ τᵢ for each i
      ─────────────────────────────────────────────────────────── (T-CallFn)     a variable f bound to a
      Γ ⊢ f(e₁, …, eₖ) : τ                                                        function value hides the
                                                                                 function named f
      f ∉ Γ    f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c })
      Γ ⊢ eᵢ ◁ τᵢ for each parameter by value    Γ ⊢ₗ eⱼ : τⱼ for each parameter τⱼ& xⱼ
      ────────────────────────────────────────────────────────────────────────────── (T-Call)
      Γ ⊢ f(e₁, …, eₖ) : τ                                                         -/
  | .call f es => do
    match Γ.lookup f with
    | some t => callValue p Γ (.var f) t es
    | none =>
      let some fn := FunEnv.lookup p f | throw (.undeclaredFunction f)
      if fn.params.length != es.length then throw (.arity f fn.params.length es.length)
      for (q, e) in fn.params.zip es do
        if q.byRef then
          let t ← match lval p Γ e with
            | .ok t => pure t
            | .error _ => throw (.refArgument f q.name e)
          if t != q.ty then throw (.mismatch s!"argument {q.name} of {f}" q.ty t)
        else
          accept p Γ s!"argument {q.name} of {f}" e q.ty
      return fn.ret
  /-  Γ ⊢ e : std::function<τ(τ₁, …, τₖ)>    Γ ⊢ eᵢ ◁ τᵢ for each i
      ─────────────────────────────────────────────────────────── (T-CallFn)
      Γ ⊢ e(e₁, …, eₖ) : τ                                                         -/
  | .callFn fe es => do
    let t ← expr p Γ fe
    callValue p Γ fe t es
  /-  A lambda has no type of its own. Outside its three positions it is an
      error, see `lambdaAt` for Γ ⊢ [=](…) -> τ { c } ◁ std::function<…>.        -/
  | e@(.lambda ..) => .error (.lambdaPosition e)
  /-  C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
      ────────────────────────────────── (T-New)
      Γ ⊢ new C() : C*                                                             -/
  | .newObj c =>
    if (p.lookupClass c).isSome then .ok (.ptr (.cls c)) else .error (.unknownClass c)
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
    fieldType p c f
  /-  Γ ⊢ e : C*    C ↦ class C { … τ f; … }
      ────────────────────────────────────── (T-Arrow)      e->f abbreviates (*e).f
      Γ ⊢ e->f : τ                                                                 -/
  | .arrow e f => do
    let t ← expr p Γ e
    let .ptr (.cls c) := t | throw (.notPointer e t)
    fieldType p c f
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
  | .index e i => do
    let t ← expr p Γ e
    let .vec t' := t | throw (.notVector e t)
    let ti ← expr p Γ i
    if ti != .int then throw (.mismatch "index" .int ti)
    return t'

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
    if !compat t τ then throw (.mismatch context τ t)

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

/-- The type of field f of class C, or the error. -/
partial def fieldType (p : Program) (c f : String) : T Ty := do
  let some cd := p.lookupClass c | throw (.unknownClass c)
  let some t := cd.fieldType f | throw (.unknownField c f)
  return t

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
    | none   => .error (.undeclaredVariable x)
  | e@(.deref _) | e@(.field ..) | e@(.arrow ..) | e@(.index ..) => expr p Γ e
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
    storable s!"reference {x}" t
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
    if !compat t₂ t₁ then throw (.mismatch s!"assignment to {e₁}" t₁ t₂)
    return Γ
  /-  Γ ⊢ e : τ
      ────────────── (T-ExprStmt)      any τ, void included
      Γ ⊢ e; ⊣ Γ                                                                   -/
  | .exprStmt e => do
    let _ ← expr p Γ e
    return Γ

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
    storable s!"parameter {q.name} of {f.name}" q.ty
    wellFormed p q.ty
  let Γ : TEnv := f.params.reverse.map fun q => (q.name, ⟨q.ty, false⟩)
  let _ ← cmds p f.ret Γ f.body

/-- A class is well formed when each field has a type with values, well
formed in the program, and not a function type. Fields of class type are
pointers, never objects.

    τᵢ storable, well formed and not a function type for each i
    ──────────────────────────────────────────────────────────── (T-Class)
    ⊢ class C { τ₁ f₁; …; τₙ fₙ; }                                                 -/
def cls (p : Program) (c : ClassDecl) : T Unit := do
  for (t, f) in c.fields do
    storable s!"field {f} of {c.name}" t
    noFunction s!"field {f} of {c.name}" t
    wellFormed p t

end Typing

/-- A program is well typed when class and function names are distinct, every
class and function is well typed and `int main()` exists.

    names distinct    ⊢ Cᵢ for each class    ⊢ fᵢ for each function    main ↦ (int main() { c })
    ────────────────────────────────────────────────────────────────────────────────────── (T-Program)
    ⊢ p                                                                            -/
def check (p : Program) : Except TypeError Unit := do
  let fnames := p.funs.map (·.name)
  for f in p.funs do
    if (fnames.filter (· == f.name)).length > 1 then throw (.duplicateFunction f.name)
  let cnames := p.classes.map (·.name)
  for c in p.classes do
    if (cnames.filter (· == c.name)).length > 1 then throw (.duplicateClass c.name)
  for c in p.classes do Typing.cls p c
  for f in p.funs do Typing.fn p f
  match FunEnv.lookup p "main" with
  | some m => if m.ret == .int && m.params.isEmpty then pure () else throw .missingMain
  | none => throw .missingMain

end CoreCpp
