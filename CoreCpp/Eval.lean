import CoreCpp.Syntax
import CoreCpp.Semantics
import CoreCpp.Pretty

/-!
# Core C++ evaluator in natural semantics

One function per judgment, with the corresponding rule in the comment of each
case. The judgments are

* ⟨e, ρ, σ⟩ ⇓ ⟨v, σ'⟩, expression evaluation,
* ⟨e, ρ, σ⟩ ⇓ₗ ⟨ℓ, σ'⟩, location denotation,
* ⟨c, ρ, σ⟩ ⇓ ⟨r, ρ', σ'⟩, command execution,

and all three admit `error` in place of the result, with propagation. The
evaluation order is left to right where C++17 leaves it unspecified, and the
C++17 order where it is fixed, right operand before left in assignment and
function before arguments in a call. The store enters expressions because a
call inside an expression may change it.

The evaluator runs in the monad `M`, which carries the derivation trace. When
tracing is enabled, every rule application records its conclusion, the full
judgment instance with the rule name, at the depth of the derivation tree.
Premises are recorded before their conclusion, so the trace read top to bottom
is the derivation tree in post-order, indented by depth.
-/

namespace CoreCpp

/-- One recorded judgment instance. -/
structure TraceEntry where
  depth : Nat
  text  : String
  deriving Repr

structure TState where
  enabled : Bool := false
  depth   : Nat := 0
  log     : Array TraceEntry := #[]

/-- The evaluation monad. The state survives an error, so the trace up to the
failing rule is kept. -/
abbrev M := ExceptT Error (StateM TState)

namespace Eval

/-- Runs `k` one level deeper and records the conclusion of the rule `rule`,
`conf arrow render a`, or the error, at the current depth. -/
def traced (rule conf : String) (render : α → String) (k : M α) (arrow : String := "⇓") : M α := do
  modify fun s => { s with depth := s.depth + 1 }
  let res : Except Error α ← tryCatch (do let a ← k; pure (.ok a)) (fun e => pure (.error e))
  modify fun s => { s with depth := s.depth - 1 }
  let s ← get
  if s.enabled then
    let concl := match res with
      | .ok a    => s!"{conf} {arrow} {render a}"
      | .error e => s!"{conf} {arrow} error ({e})"
    modify fun s => { s with log := s.log.push ⟨s.depth, s!"{concl}   ({rule})"⟩ }
  match res with
  | .ok a    => pure a
  | .error e => throw e

def confE (e : Expr) (ρ : Env) (σ : Store) : String := s!"⟨{e}, {ρ.toString}, {σ.toString}⟩"
def confC (c : Cmd) (ρ : Env) (σ : Store) : String := s!"⟨{c}, {ρ.toString}, {σ.toString}⟩"
def showV (r : Val × Store) : String := s!"⟨{r.1}, {r.2.toString}⟩"
def showL (r : Loc × Store) : String := s!"⟨{Loc.toString r.1}, {r.2.toString}⟩"
def showR (r : Ctrl × Env × Store) : String := s!"⟨{r.1}, {r.2.1.toString}, {r.2.2.toString}⟩"

/-- Range check for `int`.

    n ∈ [−2³¹, 2³¹ − 1]              n ∉ [−2³¹, 2³¹ − 1]
    ──────────────────              ──────────────────────
    int32 n ⇓ int n                 int32 n ⇓ error (overflow)              -/
def int32 (n : Int) : M Val :=
  if Int32.inRange n then pure (.int n) else throw .overflow

/-- Unary operators.

    ⟨e, ρ, σ⟩ ⇓ ⟨bool b, σ'⟩                 ⟨e, ρ, σ⟩ ⇓ ⟨int n, σ'⟩
    ─────────────────────────── (Not)        ─────────────────────────── (Neg)
    ⟨!e, ρ, σ⟩ ⇓ ⟨bool ¬b, σ'⟩               ⟨−e, ρ, σ⟩ ⇓ ⟨int32 (−n), σ'⟩       -/
def unop : UnOp → Val → M Val
  | .not, .bool b => pure (.bool !b)
  | .neg, .int n  => int32 (-n)
  | op, v => throw (.typeError s!"unary operator {op.toString} on {v}")

/-- Arithmetic and relational binary operators, on already evaluated values.

    ⟨e₁, ρ, σ⟩ ⇓ ⟨int n₁, σ₁⟩    ⟨e₂, ρ, σ₁⟩ ⇓ ⟨int n₂, σ₂⟩
    ────────────────────────────────────────────────────── (Arith, ⊕ ∈ {+, −, ×})
    ⟨e₁ ⊕ e₂, ρ, σ⟩ ⇓ ⟨int32 (n₁ ⊕ n₂), σ₂⟩

    ⟨e₁, ρ, σ⟩ ⇓ ⟨int n₁, σ₁⟩    ⟨e₂, ρ, σ₁⟩ ⇓ ⟨int n₂, σ₂⟩    n₂ ≠ 0
    ────────────────────────────────────────────────────────────── (Div, ⊘ ∈ {/, %})
    ⟨e₁ ⊘ e₂, ρ, σ⟩ ⇓ ⟨int32 (n₁ ⊘ n₂), σ₂⟩          division truncates toward zero, as in C++

    ⟨e₁, ρ, σ⟩ ⇓ ⟨int n₁, σ₁⟩    ⟨e₂, ρ, σ₁⟩ ⇓ ⟨int 0, σ₂⟩
    ────────────────────────────────────────────────────── (DivZero)
    ⟨e₁ ⊘ e₂, ρ, σ⟩ ⇓ error (division by zero)

    ⟨e₁, ρ, σ⟩ ⇓ ⟨v₁, σ₁⟩    ⟨e₂, ρ, σ₁⟩ ⇓ ⟨v₂, σ₂⟩
    ───────────────────────────────────────────────── (Rel, ⋈ ∈ {==, !=, <, <=, >, >=})
    ⟨e₁ ⋈ e₂, ρ, σ⟩ ⇓ ⟨bool (v₁ ⋈ v₂), σ₂⟩

    The left operand is evaluated before the right one, the Core C++ choice
    where C++17 does not specify the order.                                        -/
def binop : BinOp → Val → Val → M Val
  | .add, .int a, .int b => int32 (a + b)
  | .sub, .int a, .int b => int32 (a - b)
  | .mul, .int a, .int b => int32 (a * b)
  | .div, .int _, .int 0 => throw .divisionByZero
  | .mod, .int _, .int 0 => throw .divisionByZero
  | .div, .int a, .int b => int32 (a.tdiv b)
  | .mod, .int a, .int b => int32 (a.tmod b)
  | .eq,  .int a, .int b => pure (.bool (a == b))
  | .ne,  .int a, .int b => pure (.bool (a != b))
  | .lt,  .int a, .int b => pure (.bool (a < b))
  | .le,  .int a, .int b => pure (.bool (a ≤ b))
  | .gt,  .int a, .int b => pure (.bool (a > b))
  | .ge,  .int a, .int b => pure (.bool (a ≥ b))
  | .eq,  .bool a, .bool b => pure (.bool (a == b))
  | .ne,  .bool a, .bool b => pure (.bool (a != b))
  | op, v₁, v₂ => throw (.typeError s!"operator {op.toString} on {v₁} and {v₂}")

/-- Locations allocated by a block, ρ' ∖ ρ, for scope exit. -/
def fresh (ρ ρ' : Env) : List Loc :=
  (ρ'.take (ρ'.length - ρ.length)).map (·.2)

def expectBool (what : String) : Val → M Bool
  | .bool b => pure b
  | v => throw (.typeError s!"{what} is not boolean, got {v}")

mutual

/-- ⟨e, ρ, σ⟩ ⇓ ⟨v, σ'⟩ -/
partial def expr (fs : FunEnv) (ρ : Env) (σ : Store) (e : Expr) : M (Val × Store) :=
  match e with
  /-  ──────────────────────── (Lit)
      ⟨n, ρ, σ⟩ ⇓ ⟨int n, σ⟩                                                    -/
  | .intLit n => traced "Lit" (confE e ρ σ) showV do return (← int32 n, σ)
  /-  ──────────────────────── (BoolLit)
      ⟨b, ρ, σ⟩ ⇓ ⟨bool b, σ⟩                                                   -/
  | .boolLit b => traced "BoolLit" (confE e ρ σ) showV do return (.bool b, σ)
  /-  ρ(x) = ℓ    ℓ ∈ dom σ
      ──────────────────────── (Var)       reading x is reading σ(ρ(x))
      ⟨x, ρ, σ⟩ ⇓ ⟨σ(ℓ), σ⟩                                                    -/
  | .var x => traced "Var" (confE e ρ σ) showV do
    let (l, σ) ← lval fs ρ σ (.var x)
    match σ.read l with
    | some v => return (v, σ)
    | none   => throw (.danglingLocation l)
  /-  ⟨e, ρ, σ⟩ ⇓ ⟨v, σ'⟩    op v = v'
      ─────────────────────────────── (Unary)                                   -/
  | .unop op e₁ => traced "Unary" (confE e ρ σ) showV do
    let (v, σ) ← expr fs ρ σ e₁
    return (← unop op v, σ)
  /-  ⟨e₁, ρ, σ⟩ ⇓ ⟨bool false, σ₁⟩                   ⟨e₁, ρ, σ⟩ ⇓ ⟨bool true, σ₁⟩   ⟨e₂, ρ, σ₁⟩ ⇓ ⟨v, σ₂⟩
      ────────────────────────────────── (And-False)   ───────────────────────────────────────────────── (And-True)
      ⟨e₁ && e₂, ρ, σ⟩ ⇓ ⟨bool false, σ₁⟩               ⟨e₁ && e₂, ρ, σ⟩ ⇓ ⟨v, σ₂⟩
      short circuit, e₂ is evaluated only if e₁ is true                          -/
  | .binop .and e₁ e₂ => traced "And" (confE e ρ σ) showV do
    let (v₁, σ₁) ← expr fs ρ σ e₁
    if ← expectBool "left operand of &&" v₁ then expr fs ρ σ₁ e₂ else return (.bool false, σ₁)
  /-  ⟨e₁, ρ, σ⟩ ⇓ ⟨bool true, σ₁⟩                    ⟨e₁, ρ, σ⟩ ⇓ ⟨bool false, σ₁⟩   ⟨e₂, ρ, σ₁⟩ ⇓ ⟨v, σ₂⟩
      ────────────────────────────────── (Or-True)     ────────────────────────────────────────────────── (Or-False)
      ⟨e₁ || e₂, ρ, σ⟩ ⇓ ⟨bool true, σ₁⟩                ⟨e₁ || e₂, ρ, σ⟩ ⇓ ⟨v, σ₂⟩                          -/
  | .binop .or e₁ e₂ => traced "Or" (confE e ρ σ) showV do
    let (v₁, σ₁) ← expr fs ρ σ e₁
    if ← expectBool "left operand of ||" v₁ then return (.bool true, σ₁) else expr fs ρ σ₁ e₂
  /-  ⟨e₁, ρ, σ⟩ ⇓ ⟨v₁, σ₁⟩    ⟨e₂, ρ, σ₁⟩ ⇓ ⟨v₂, σ₂⟩    v₁ ⊕ v₂ = v
      ─────────────────────────────────────────────────────────── (Binary)
      ⟨e₁ ⊕ e₂, ρ, σ⟩ ⇓ ⟨v, σ₂⟩          left before right                     -/
  | .binop op e₁ e₂ => traced "Binary" (confE e ρ σ) showV do
    let (v₁, σ₁) ← expr fs ρ σ e₁
    let (v₂, σ₂) ← expr fs ρ σ₁ e₂
    return (← binop op v₁ v₂, σ₂)
  /-  ⟨e₁, ρ, σ⟩ ⇓ ⟨bool true, σ₁⟩   ⟨e₂, ρ, σ₁⟩ ⇓ ⟨v, σ₂⟩        ⟨e₁, ρ, σ⟩ ⇓ ⟨bool false, σ₁⟩   ⟨e₃, ρ, σ₁⟩ ⇓ ⟨v, σ₂⟩
      ──────────────────────────────────────────────── (Cond-T)   ──────────────────────────────────────────────── (Cond-F)
      ⟨e₁ ? e₂ : e₃, ρ, σ⟩ ⇓ ⟨v, σ₂⟩                               ⟨e₁ ? e₂ : e₃, ρ, σ⟩ ⇓ ⟨v, σ₂⟩                  -/
  | .cond e₁ e₂ e₃ => traced "Cond" (confE e ρ σ) showV do
    let (v₁, σ₁) ← expr fs ρ σ e₁
    if ← expectBool "condition" v₁ then expr fs ρ σ₁ e₂ else expr fs ρ σ₁ e₃
  /-  f ↦ (τ f (τ₁ x₁, …, τₖ xₖ) { c }) in the program
      ⟨e₁, ρ, σ⟩ ⇓ ⟨v₁, σ₁⟩  …  ⟨eₖ, ρ, σₖ₋₁⟩ ⇓ ⟨vₖ, σₖ⟩              arguments left to right
      (ℓᵢ, σ'ᵢ) = alloc σ'ᵢ₋₁ vᵢ,  σ'₀ = σₖ                          call by value, fresh location with a copy
      ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]                                    the function environment holds only the parameters
      ⟨c, ρ_f, σ'ₖ⟩ ⇓ ⟨ret v, ρ', σ''⟩
      ──────────────────────────────────────────────────────────── (Call)
      ⟨f(e₁, …, eₖ), ρ, σ⟩ ⇓ ⟨v, σ'' ∖ {ℓ₁, …, ℓₖ}⟩                   the return frees the parameters

      With ⟨c, ρ_f, σ'ₖ⟩ ⇓ ⟨normal, ρ', σ''⟩ the result is ⟨void, σ'' ∖ {ℓᵢ}⟩ if τ = void,
      and error (missing return) otherwise.                                                          -/
  | .call f es => traced "Call" (confE e ρ σ) showV do
    let some fn := fs.lookup f | throw (.undeclaredFunction f)
    if fn.params.length != es.length then throw (.arity f)
    let mut σ := σ
    let mut vs : List Val := []
    for a in es do
      let (v, σ') ← expr fs ρ σ a
      σ := σ'
      vs := vs ++ [v]
    let mut ρf : Env := []
    let mut ls : List Loc := []
    for (p, v) in fn.params.zip vs do
      let (l, σ') := σ.alloc v
      σ := σ'
      ρf := ρf.extend p.name l
      ls := l :: ls
    let (r, _, σ'') ← cmds fs ρf σ fn.body
    let σ''' := σ''.free ls
    match r, fn.ret with
    | .ret v, _      => return (v, σ''')
    | .normal, .void => return (.void, σ''')
    | .normal, _     => throw (.missingReturn f)

/-- ⟨e, ρ, σ⟩ ⇓ₗ ⟨ℓ, σ'⟩, the expressions that denote a location. In this subset,
only the variable.

    ρ(x) = ℓ
    ─────────────────────── (LocVar)
    ⟨x, ρ, σ⟩ ⇓ₗ ⟨ℓ, σ⟩                                                        -/
partial def lval (_fs : FunEnv) (ρ : Env) (σ : Store) (e : Expr) : M (Loc × Store) :=
  match e with
  | .var x => traced "LocVar" (confE e ρ σ) showL (arrow := "⇓ₗ") do
    match ρ.lookup x with
    | some l => return (l, σ)
    | none   => throw (.undeclaredVariable x)
  | _ => throw (.typeError s!"expression does not denote a location: {e}")

/-- ⟨c, ρ, σ⟩ ⇓ ⟨r, ρ', σ'⟩ -/
partial def cmd (fs : FunEnv) (ρ : Env) (σ : Store) (c : Cmd) : M (Ctrl × Env × Store) :=
  match c with
  /-  ⟨c₁ … cₙ, ρ, σ⟩ ⇓ ⟨r, ρ', σ'⟩
      ────────────────────────────────────────────── (Block)
      ⟨{ c₁ … cₙ }, ρ, σ⟩ ⇓ ⟨r, ρ, σ' ∖ (ρ' ∖ ρ)⟩
      the block discards the extension of ρ and removes from σ the locations it declared -/
  | .block cs => traced "Block" (confC c ρ σ) showR do
    let (r, ρ', σ') ← cmds fs ρ σ cs
    return (r, ρ, σ'.free (fresh ρ ρ'))
  /-  ⟨e, ρ, σ⟩ ⇓ ⟨bool true, σ₁⟩   ⟨{c₁}, ρ, σ₁⟩ ⇓ ⟨r, ρ, σ₂⟩        ⟨e, ρ, σ⟩ ⇓ ⟨bool false, σ₁⟩   ⟨{c₂}, ρ, σ₁⟩ ⇓ ⟨r, ρ, σ₂⟩
      ─────────────────────────────────────────────────── (If-T)     ─────────────────────────────────────────────────── (If-F)
      ⟨if (e) {c₁} else {c₂}, ρ, σ⟩ ⇓ ⟨r, ρ, σ₂⟩                       ⟨if (e) {c₁} else {c₂}, ρ, σ⟩ ⇓ ⟨r, ρ, σ₂⟩          -/
  | .ite e t f => traced "If" (confC c ρ σ) showR do
    let (v, σ₁) ← expr fs ρ σ e
    if ← expectBool "condition of if" v then cmd fs ρ σ₁ (.block t) else cmd fs ρ σ₁ (.block f)
  /-  ⟨e, ρ, σ⟩ ⇓ ⟨bool false, σ₁⟩
      ────────────────────────────────────── (While-F)
      ⟨while (e) {c}, ρ, σ⟩ ⇓ ⟨normal, ρ, σ₁⟩

      ⟨e, ρ, σ⟩ ⇓ ⟨bool true, σ₁⟩   ⟨{c}, ρ, σ₁⟩ ⇓ ⟨normal, ρ, σ₂⟩   ⟨while (e) {c}, ρ, σ₂⟩ ⇓ ⟨r, ρ, σ₃⟩
      ─────────────────────────────────────────────────────────────────────────────────────── (While-T)
      ⟨while (e) {c}, ρ, σ⟩ ⇓ ⟨r, ρ, σ₃⟩

      ⟨e, ρ, σ⟩ ⇓ ⟨bool true, σ₁⟩   ⟨{c}, ρ, σ₁⟩ ⇓ ⟨ret v, ρ, σ₂⟩
      ──────────────────────────────────────────────────────── (While-Ret)   the return interrupts the loop
      ⟨while (e) {c}, ρ, σ⟩ ⇓ ⟨ret v, ρ, σ₂⟩

      The divergence of while (true) {} has no derivation, a limitation of
      inductive big-step semantics.                                                                 -/
  | .while e b => traced "While" (confC c ρ σ) showR do
    let (v, σ₁) ← expr fs ρ σ e
    if ← expectBool "condition of while" v then
      let (r, _, σ₂) ← cmd fs ρ σ₁ (.block b)
      match r with
      | .normal => cmd fs ρ σ₂ (.while e b)
      | .ret _  => return (r, ρ, σ₂)
    else return (.normal, ρ, σ₁)
  /-  ⟨c₀, ρ, σ⟩ ⇓ ⟨normal, ρ₀, σ₀⟩   ⟨while (e) { {c} cₛ }, ρ₀, σ₀⟩ ⇓ ⟨r, ρ₀, σ₁⟩
      ─────────────────────────────────────────────────────────────────────── (For)
      ⟨for (c₀; e; cₛ) {c}, ρ, σ⟩ ⇓ ⟨r, ρ, σ₁ ∖ (ρ₀ ∖ ρ)⟩
      the variable of c₀ has the loop as its scope, the body is its own block, and
      the step cₛ runs after the body, outside the body's scope                                       -/
  | .for c₀ e cₛ b => traced "For" (confC c ρ σ) showR do
    let (r₀, ρ₀, σ₀) ← cmd fs ρ σ c₀
    match r₀ with
    | .ret _ => throw (.typeError "return in for initialiser")
    | .normal =>
      let (r, _, σ₁) ← cmd fs ρ₀ σ₀ (.while e [.block b, cₛ])
      return (r, ρ, σ₁.free (fresh ρ ρ₀))
  /-  ⟨e, ρ, σ⟩ ⇓ ⟨v, σ'⟩
      ────────────────────────────────── (Return)      ────────────────────────────────── (ReturnVoid)
      ⟨return e, ρ, σ⟩ ⇓ ⟨ret v, ρ, σ'⟩                ⟨return, ρ, σ⟩ ⇓ ⟨ret void, ρ, σ⟩              -/
  | .ret none => traced "ReturnVoid" (confC c ρ σ) showR do return (.ret .void, ρ, σ)
  | .ret (some e) => traced "Return" (confC c ρ σ) showR do
    let (v, σ') ← expr fs ρ σ e
    return (.ret v, ρ, σ')
  /-  ⟨e, ρ, σ⟩ ⇓ ⟨v, σ'⟩    (ℓ, σ'') = alloc σ' v    ℓ ∉ dom σ'
      ─────────────────────────────────────────────────────────── (Decl)
      ⟨τ x = e, ρ, σ⟩ ⇓ ⟨normal, ρ[x ↦ ℓ], σ''⟩
      the declaration allocates a fresh location and extends ρ for the following commands -/
  | .decl _ x e => traced "Decl" (confC c ρ σ) showR do
    let (v, σ') ← expr fs ρ σ e
    let (l, σ'') := σ'.alloc v
    return (.normal, ρ.extend x l, σ'')
  /-  The rule for auto is Decl, with τ the type of v.                            -/
  | .declAuto x e => traced "Decl" (confC c ρ σ) showR do
    let (v, σ') ← expr fs ρ σ e
    let (l, σ'') := σ'.alloc v
    return (.normal, ρ.extend x l, σ'')
  /-  ⟨e₂, ρ, σ⟩ ⇓ ⟨v, σ₁⟩    ⟨e₁, ρ, σ₁⟩ ⇓ₗ ⟨ℓ, σ₂⟩    ℓ ∈ dom σ₂
      ───────────────────────────────────────────────────────── (Assign)
      ⟨e₁ = e₂, ρ, σ⟩ ⇓ ⟨normal, ρ, σ₂[ℓ ↦ v]⟩
      right operand before left, the order C++17 fixes for assignment            -/
  | .assign e₁ e₂ => traced "Assign" (confC c ρ σ) showR do
    let (v, σ₁) ← expr fs ρ σ e₂
    let (l, σ₂) ← lval fs ρ σ₁ e₁
    if (σ₂.read l).isNone then throw (.danglingLocation l)
    return (.normal, ρ, σ₂.write l v)
  /-  ⟨e, ρ, σ⟩ ⇓ ⟨v, σ'⟩
      ──────────────────────────────── (ExprStmt)      the value is discarded
      ⟨e;, ρ, σ⟩ ⇓ ⟨normal, ρ, σ'⟩                                              -/
  | .exprStmt e => traced "ExprStmt" (confC c ρ σ) showR do
    let (_, σ') ← expr fs ρ σ e
    return (.normal, ρ, σ')

/-- Command sequences.

    ─────────────────────────────── (Seq-Empty)
    ⟨ε, ρ, σ⟩ ⇓ ⟨normal, ρ, σ⟩

    ⟨c, ρ, σ⟩ ⇓ ⟨normal, ρ₁, σ₁⟩    ⟨cs, ρ₁, σ₁⟩ ⇓ ⟨r, ρ₂, σ₂⟩
    ───────────────────────────────────────────────────────── (Seq)   ρ₁ carries the binding of c to the rest
    ⟨c cs, ρ, σ⟩ ⇓ ⟨r, ρ₂, σ₂⟩

    ⟨c, ρ, σ⟩ ⇓ ⟨ret v, ρ₁, σ₁⟩
    ─────────────────────────────────── (Seq-Ret)   the return interrupts the sequence
    ⟨c cs, ρ, σ⟩ ⇓ ⟨ret v, ρ₁, σ₁⟩                                                            -/
partial def cmds (fs : FunEnv) (ρ : Env) (σ : Store) : List Cmd → M (Ctrl × Env × Store)
  | [] => return (.normal, ρ, σ)
  | c :: cs => do
    let (r, ρ₁, σ₁) ← cmd fs ρ σ c
    match r with
    | .normal => cmds fs ρ₁ σ₁ cs
    | .ret _  => return (r, ρ₁, σ₁)

end

end Eval

/-- Program execution. The initial store is empty, because there are no global
variables, and the result is the value returned by `main()`.

    main ↦ (int main() { c })    ⟨main(), [], ∅⟩ ⇓ ⟨v, σ⟩
    ──────────────────────────────────────────────────── (Program)
    program ⇓ v                                                                   -/
def runWith (trace : Bool) (p : Program) : Except Error Val × Array TraceEntry :=
  let (r, s) := (Eval.expr p [] {} (.call "main" [])).run.run { enabled := trace }
  (r.map (·.1), s.log)

def run (p : Program) : Except Error Val := (runWith false p).1

/-- Renders the trace as the derivation tree in post-order, indented by depth. -/
def renderTrace (log : Array TraceEntry) : String :=
  "\n".intercalate (log.toList.map fun t => "".pushn ' ' (2 * t.depth) ++ t.text)

end CoreCpp
