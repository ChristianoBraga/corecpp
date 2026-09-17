import CoreCpp.Syntax
import CoreCpp.Pretty

/-!
# Static semantics of Core C++, subset

The judgment Γ ⊢ e : τ for expressions and Γ ⊢ c ⊣ Γ' for commands, where Γ'
is Γ extended by the declarations of c, so that a declaration reaches the
following commands of a sequence and a block discards the extension. Functions
are checked against their declared return type. Each rule is in the comment of
the case that implements it.

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
  | arity (f : String) (expected got : Nat)
  | mismatch (context : String) (expected got : Ty)
  | notLvalue (e : Expr)
  | voidValue (e : Expr)
  | badOperand (op : String) (t : Ty)
  | returnOutside
  | missingMain
  deriving Repr

def TypeError.toString : TypeError → String
  | .undeclaredVariable x => s!"undeclared variable {x}"
  | .undeclaredFunction f => s!"undeclared function {f}"
  | .duplicateFunction f  => s!"function {f} declared twice"
  | .arity f e g          => s!"call to {f} with {g} arguments, expected {e}"
  | .mismatch c e g       => s!"{c}: expected {e}, got {g}"
  | .notLvalue e          => s!"expression does not denote a location: {e}"
  | .voidValue e          => s!"void expression used as a value: {e}"
  | .badOperand op t      => s!"operator {op} applied to {t}"
  | .returnOutside        => "return outside a function"
  | .missingMain          => "no function int main()"

instance : ToString TypeError := ⟨TypeError.toString⟩

abbrev T (α : Type) := Except TypeError α

namespace Typing

/-- Requires a non-void type where a value is used. -/
def value (e : Expr) (t : Ty) : T Ty :=
  if t == .void then .error (.voidValue e) else .ok t

/-- Γ ⊢ e : τ -/
partial def expr (fs : FunEnv) (Γ : TEnv) : Expr → T Ty
  /-  ─────────────── (T-Lit)      ─────────────── (T-BoolLit)
      Γ ⊢ n : int                  Γ ⊢ b : bool                                     -/
  | .intLit _  => .ok .int
  | .boolLit _ => .ok .bool
  /-  Γ(x) = τ
      ─────────── (T-Var)                                                          -/
  | .var x =>
    match Γ.lookup x with
    | some t => .ok t
    | none   => .error (.undeclaredVariable x)
  /-  Γ ⊢ e : bool                 Γ ⊢ e : int
      ────────────── (T-Not)       ────────────── (T-Neg)                           -/
  | .unop .not e => do
    let t ← expr fs Γ e
    if t == .bool then .ok .bool else .error (.badOperand "!" t)
  | .unop .neg e => do
    let t ← expr fs Γ e
    if t == .int then .ok .int else .error (.badOperand "-" t)
  /-  Γ ⊢ e₁ : bool    Γ ⊢ e₂ : bool
      ──────────────────────────────── (T-Logic, ⊙ ∈ {&&, ||})
      Γ ⊢ e₁ ⊙ e₂ : bool                                                           -/
  | .binop op e₁ e₂ => do
    let t₁ ← expr fs Γ e₁
    let t₂ ← expr fs Γ e₂
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
    /-  Γ ⊢ e₁ : τ    Γ ⊢ e₂ : τ    τ ∈ {int, bool}
        ──────────────────────────────────────────── (T-Eq, ⋈ ∈ {==, !=})
        Γ ⊢ e₁ ⋈ e₂ : bool                                                         -/
    | .eq | .ne =>
      if t₁ == t₂ && t₁ != .void then .ok .bool
      else .error (.mismatch s!"operands of {op.toString}" t₁ t₂)
    /-  Γ ⊢ e₁ : int    Γ ⊢ e₂ : int
        ──────────────────────────── (T-Rel, ⋈ ∈ {<, <=, >, >=})
        Γ ⊢ e₁ ⋈ e₂ : bool                                                         -/
    | .lt | .le | .gt | .ge =>
      if t₁ == .int && t₂ == .int then .ok .bool
      else .error (.badOperand op.toString (if t₁ != .int then t₁ else t₂))
  /-  Γ ⊢ e₁ : bool    Γ ⊢ e₂ : τ    Γ ⊢ e₃ : τ    τ ≠ void
      ──────────────────────────────────────────────────── (T-Cond)
      Γ ⊢ e₁ ? e₂ : e₃ : τ                                                         -/
  | .cond e₁ e₂ e₃ => do
    let t₁ ← expr fs Γ e₁
    if t₁ != .bool then throw (.mismatch "condition" .bool t₁)
    let t₂ ← value e₂ (← expr fs Γ e₂)
    let t₃ ← value e₃ (← expr fs Γ e₃)
    if t₂ == t₃ then .ok t₂ else .error (.mismatch "branches of ?:" t₂ t₃)
  /-  f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c })    Γ ⊢ eᵢ : τᵢ for each i
      ──────────────────────────────────────────────────────── (T-Call)
      Γ ⊢ f(e₁, …, eₖ) : τ                                                         -/
  | .call f es => do
    let some fn := fs.lookup f | throw (.undeclaredFunction f)
    if fn.params.length != es.length then throw (.arity f fn.params.length es.length)
    for (p, e) in fn.params.zip es do
      let t ← expr fs Γ e
      if t != p.ty then throw (.mismatch s!"argument {p.name} of {f}" p.ty t)
    return fn.ret

/-- The expressions that denote a location. In this subset, only the variable.

    Γ(x) = τ
    ──────────── (T-LocVar)
    Γ ⊢ₗ x : τ                                                                     -/
def lval (Γ : TEnv) : Expr → T Ty
  | .var x =>
    match Γ.lookup x with
    | some t => .ok t
    | none   => .error (.undeclaredVariable x)
  | e => .error (.notLvalue e)

mutual

/-- Γ ⊢ c ⊣ Γ', under the return type τᵣ of the enclosing function. -/
partial def cmd (fs : FunEnv) (τᵣ : Ty) (Γ : TEnv) : Cmd → T TEnv
  /-  Γ ⊢ c₁ … cₙ ⊣ Γ'
      ──────────────────── (T-Block)      the block discards Γ'
      Γ ⊢ { c₁ … cₙ } ⊣ Γ                                                         -/
  | .block cs => do
    let _ ← cmds fs τᵣ Γ cs
    return Γ
  /-  Γ ⊢ e : bool    Γ ⊢ {c₁} ⊣ Γ    Γ ⊢ {c₂} ⊣ Γ
      ──────────────────────────────────────────── (T-If)
      Γ ⊢ if (e) {c₁} else {c₂} ⊣ Γ                                               -/
  | .ite e t f => do
    let te ← expr fs Γ e
    if te != .bool then throw (.mismatch "condition of if" .bool te)
    let _ ← cmd fs τᵣ Γ (.block t)
    let _ ← cmd fs τᵣ Γ (.block f)
    return Γ
  /-  Γ ⊢ e : bool    Γ ⊢ {c} ⊣ Γ
      ──────────────────────────── (T-While)
      Γ ⊢ while (e) {c} ⊣ Γ                                                       -/
  | .while e b => do
    let te ← expr fs Γ e
    if te != .bool then throw (.mismatch "condition of while" .bool te)
    let _ ← cmd fs τᵣ Γ (.block b)
    return Γ
  /-  Γ ⊢ c₀ ⊣ Γ₀    Γ₀ ⊢ e : bool    Γ₀ ⊢ cₛ ⊣ Γ₀    Γ₀ ⊢ {c} ⊣ Γ₀
      ─────────────────────────────────────────────────────────── (T-For)
      Γ ⊢ for (c₀; e; cₛ) {c} ⊣ Γ                                                 -/
  | .for c₀ e cₛ b => do
    let Γ₀ ← cmd fs τᵣ Γ c₀
    let te ← expr fs Γ₀ e
    if te != .bool then throw (.mismatch "condition of for" .bool te)
    let _ ← cmd fs τᵣ Γ₀ cₛ
    let _ ← cmd fs τᵣ Γ₀ (.block b)
    return Γ
  /-  τᵣ = void                      Γ ⊢ e : τᵣ    τᵣ ≠ void
      ──────────────── (T-RetVoid)   ────────────────────── (T-Ret)
      Γ ⊢ return ⊣ Γ                 Γ ⊢ return e ⊣ Γ                              -/
  | .ret none =>
    if τᵣ == .void then .ok Γ else .error (.mismatch "return without value" τᵣ .void)
  | .ret (some e) => do
    let t ← expr fs Γ e
    if t == τᵣ && t != .void then .ok Γ else .error (.mismatch "return value" τᵣ t)
  /-  Γ ⊢ e : τ    τ ≠ void
      ─────────────────────────── (T-Decl)      Γ[x ↦ τ] reaches the following commands
      Γ ⊢ τ x = e ⊣ Γ[x ↦ τ]                                                       -/
  | .decl t x e => do
    let te ← value e (← expr fs Γ e)
    if te != t then throw (.mismatch s!"initialiser of {x}" t te)
    return (x, t) :: Γ
  /-  Γ ⊢ e : τ    τ ≠ void
      ─────────────────────────── (T-Auto)
      Γ ⊢ auto x = e ⊣ Γ[x ↦ τ]                                                    -/
  | .declAuto x e => do
    let te ← value e (← expr fs Γ e)
    return (x, te) :: Γ
  /-  Γ ⊢ₗ e₁ : τ    Γ ⊢ e₂ : τ
      ──────────────────────────── (T-Assign)
      Γ ⊢ e₁ = e₂ ⊣ Γ                                                              -/
  | .assign e₁ e₂ => do
    let t₁ ← lval Γ e₁
    let t₂ ← expr fs Γ e₂
    if t₁ != t₂ then throw (.mismatch s!"assignment to {e₁}" t₁ t₂)
    return Γ
  /-  Γ ⊢ e : τ
      ────────────── (T-ExprStmt)      any τ, void included
      Γ ⊢ e; ⊣ Γ                                                                   -/
  | .exprStmt e => do
    let _ ← expr fs Γ e
    return Γ

/-- Γ ⊢ c₁ … cₙ ⊣ Γₙ, threading the context through the sequence.

    ──────────── (T-Seq-Empty)      Γ ⊢ c ⊣ Γ₁    Γ₁ ⊢ cs ⊣ Γ₂
    Γ ⊢ ε ⊣ Γ                       ──────────────────────────── (T-Seq)
                                    Γ ⊢ c cs ⊣ Γ₂                                  -/
partial def cmds (fs : FunEnv) (τᵣ : Ty) (Γ : TEnv) : List Cmd → T TEnv
  | [] => .ok Γ
  | c :: cs => do
    let Γ₁ ← cmd fs τᵣ Γ c
    cmds fs τᵣ Γ₁ cs

end

/-- A function is well typed when its body is, under the context of its
parameters and its return type.

    [x₁ ↦ τ₁, …, xₖ ↦ τₖ] ⊢ c ⊣ Γ'
    ──────────────────────────────── (T-Fun)
    ⊢ τ f (τ₁ x₁, …, τₖ xₖ) { c }                                                  -/
def fn (fs : FunEnv) (f : Fun) : T Unit := do
  let Γ : TEnv := f.params.reverse.map fun p => (p.name, p.ty)
  let _ ← cmds fs f.ret Γ f.body

end Typing

/-- A program is well typed when function names are distinct, every function is
well typed and `int main()` exists.

    names of p distinct    ⊢ fᵢ for each fᵢ    main ↦ (int main() { c })
    ───────────────────────────────────────────────────────────────── (T-Program)
    ⊢ p                                                                            -/
def check (p : Program) : Except TypeError Unit := do
  let names := p.map (·.name)
  for f in p do
    if (names.filter (· == f.name)).length > 1 then throw (.duplicateFunction f.name)
  for f in p do Typing.fn p f
  match FunEnv.lookup p "main" with
  | some m => if m.ret == .int && m.params.isEmpty then pure () else throw .missingMain
  | none => throw .missingMain

end CoreCpp
