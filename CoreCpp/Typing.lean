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

Not checked here, and left to the evaluator as `missingReturn`, is that every
path of a non-void function ends in a return.
-/

namespace CoreCpp

/-- Typing context Γ, a finite map from identifiers to types. -/
abbrev TEnv := List (String × Ty)

def TEnv.lookup (Γ : TEnv) (x : String) : Option Ty :=
  (Γ.find? (·.1 == x)).map (·.2)

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
  | notPointer (e : Expr) (t : Ty)
  | notObject (e : Expr) (t : Ty)
  | notVector (e : Expr) (t : Ty)
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
  | .notPointer e t       => s!"{e} has type {t}, not a pointer"
  | .notObject e t        => s!"{e} has type {t}, not a class"
  | .notVector e t        => s!"{e} has type {t}, not a vector"
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
conversion of this subset. -/
def compat : Ty → Ty → Bool
  | .nullT, .ptr _ => true
  | .ptr _, .nullT => true
  | t₁, t₂ => t₁ == t₂

/-- Requires that a variable, parameter or result type has values. -/
def storable (context : String) (t : Ty) : T Unit :=
  if t.isObject || t == .nullT then .error (.objectByValue context t) else .ok ()

/-- A type mentioned in a declaration names only declared classes. -/
partial def wellFormed (p : Program) : Ty → T Unit
  | .cls c => if (p.lookupClass c).isSome then .ok () else .error (.unknownClass c)
  | .ptr t | .vec t => wellFormed p t
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
      if compat t₁ t₂ && t₁ != .void && !t₁.isObject then .ok .bool
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
  /-  f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c })    Γ ⊢ eᵢ : τᵢ' with τᵢ' ≈ τᵢ for each i
      ─────────────────────────────────────────────────────────────────────── (T-Call)
      Γ ⊢ f(e₁, …, eₖ) : τ                                                         -/
  | .call f es => do
    let some fn := FunEnv.lookup p f | throw (.undeclaredFunction f)
    if fn.params.length != es.length then throw (.arity f fn.params.length es.length)
    for (q, e) in fn.params.zip es do
      let t ← expr p Γ e
      if !compat t q.ty then throw (.mismatch s!"argument {q.name} of {f}" q.ty t)
    return fn.ret
  /-  C ↦ class C { τ₁ f₁; …; τₙ fₙ; }
      ────────────────────────────────── (T-New)
      Γ ⊢ new C() : C*                                                             -/
  | .newObj c =>
    if (p.lookupClass c).isSome then .ok (.ptr (.cls c)) else .error (.unknownClass c)
  /-  Γ ⊢ n : int    τ has values
      ──────────────────────────────────── (T-NewVec)
      Γ ⊢ new std::vector<τ>(n) : std::vector<τ>*                                  -/
  | .newVec t n => do
    let tn ← expr p Γ n
    if tn != .int then throw (.mismatch "size of std::vector" .int tn)
    storable "element of std::vector" t
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

/-- The type of field f of class C, or the error. -/
partial def fieldType (p : Program) (c f : String) : T Ty := do
  let some cd := p.lookupClass c | throw (.unknownClass c)
  let some t := cd.fieldType f | throw (.unknownField c f)
  return t

end

/-- The expressions that denote a location, with their type. A variable, a
dereferenced pointer, a field of an object, a field through a pointer and an
element of a vector.

    Γ(x) = τ            Γ ⊢ e : τ*           Γ ⊢ e : C, C has τ f
    ──────────── (T-LocVar)  ──────────── (T-LocDeref)  ─────────────────── (T-LocField)
    Γ ⊢ₗ x : τ          Γ ⊢ₗ *e : τ          Γ ⊢ₗ e.f : τ

    Γ ⊢ e : C*, C has τ f                Γ ⊢ e : std::vector<τ>    Γ ⊢ i : int
    ────────────────────── (T-LocArrow)  ─────────────────────────────────── (T-LocIndex)
    Γ ⊢ₗ e->f : τ                        Γ ⊢ₗ e[i] : τ                                       -/
def lval (p : Program) (Γ : TEnv) : Expr → T Ty
  | .var x =>
    match Γ.lookup x with
    | some t => .ok t
    | none   => .error (.undeclaredVariable x)
  | e@(.deref _) | e@(.field ..) | e@(.arrow ..) | e@(.index ..) => expr p Γ e
  | e => .error (.notLvalue e)

mutual

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
  /-  τᵣ = void                      Γ ⊢ e : τ    τ ≈ τᵣ    τᵣ ≠ void
      ──────────────── (T-RetVoid)   ────────────────────────────────── (T-Ret)
      Γ ⊢ return ⊣ Γ                 Γ ⊢ return e ⊣ Γ                              -/
  | .ret none =>
    if τᵣ == .void then .ok Γ else .error (.mismatch "return without value" τᵣ .void)
  | .ret (some e) => do
    let t ← expr p Γ e
    if compat t τᵣ && τᵣ != .void then .ok Γ else .error (.mismatch "return value" τᵣ t)
  /-  Γ ⊢ e : τ'    τ' ≈ τ    τ has values    τ well formed
      ────────────────────────────────────────────────── (T-Decl)      Γ[x ↦ τ] reaches the following commands
      Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]                                                       -/
  | .decl t x e => do
    storable s!"variable {x}" t
    wellFormed p t
    let te ← value e (← expr p Γ e)
    if !compat te t then throw (.mismatch s!"initialiser of {x}" t te)
    return (x, t) :: Γ
  /-  Γ ⊢ₗ e : τ    τ has values    τ well formed
      ───────────────────────────────────────────── (T-DeclRef)      the initialiser denotes a location
      Γ ⊢ τ& x = e ⊣ Γ[x ↦ τ]                                        and x has the type of its referent -/
  | .declRef t x e => do
    storable s!"reference {x}" t
    wellFormed p t
    let te ← value e (← lval p Γ e)
    if te != t then throw (.mismatch s!"referent of {x}" t te)
    return (x, t) :: Γ
  /-  Γ ⊢ e : τ    τ has values    τ ≠ nullptr_t
      ─────────────────────────────────────────── (T-Auto)
      Γ ⊢ auto x = e ⊣ Γ[x ↦ τ]                                                    -/
  | .declAuto x e => do
    let te ← value e (← expr p Γ e)
    storable s!"variable {x}" te
    return (x, te) :: Γ
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
its return type.

    τ, τᵢ storable and well formed    [x₁ ↦ τ₁, …, xₖ ↦ τₖ] ⊢ c ⊣ Γ'
    ──────────────────────────────────────────────────────────────── (T-Fun)
    ⊢ τ f (τ₁ x₁, …, τₖ xₖ) { c }                                                  -/
def fn (p : Program) (f : Fun) : T Unit := do
  if f.ret != .void then storable s!"result of {f.name}" f.ret
  wellFormed p f.ret
  for q in f.params do
    storable s!"parameter {q.name} of {f.name}" q.ty
    wellFormed p q.ty
  let Γ : TEnv := f.params.reverse.map fun q => (q.name, q.ty)
  let _ ← cmds p f.ret Γ f.body

/-- A class is well formed when each field has a type with values, well
formed in the program. Fields of class type are pointers, never objects.

    τᵢ storable and well formed for each i
    ─────────────────────────────────────── (T-Class)
    ⊢ class C { τ₁ f₁; …; τₙ fₙ; }                                                 -/
def cls (p : Program) (c : ClassDecl) : T Unit := do
  for (t, f) in c.fields do
    storable s!"field {f} of {c.name}" t
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
