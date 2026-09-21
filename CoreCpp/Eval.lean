import CoreCpp.Syntax
import CoreCpp.Semantics
import CoreCpp.Pretty
import CoreCpp.Typing

/-!
# Core C++ evaluator in natural semantics

One function per judgment, with the corresponding rule in the comment of each
case. The judgments are

* ρ, σ ⊢ e ⇒ v, σ', expression evaluation,
* ρ, σ ⊢ e ⇒ₗ ℓ, σ', location denotation,
* ρ, σ ⊢ c ⇒ r, ρ', σ', command execution,

in the sequent style of Kahn (1987), the hypotheses ρ and σ left of ⊢, the
subject right of it and the result after ⇒. All three admit `error` in place
of the result, with propagation. The evaluation order is left to right where
C++17 leaves it unspecified, and the C++17 order where it is fixed, right
operand before left in assignment and function before arguments in a call. The
store enters expressions because a call inside an expression may change it.
Objects live in the store as records of locations with a class tag, pointers
are locations, and the location judgment reaches fields and vector elements. A
reference parameter binds its name to the location of the argument, a lambda
evaluates to a closure with copies of the variables it uses, and a call through
a function value allocates the copies and the parameters afresh. An object of
a class with a constructor is created by `new C(args)`, which allocates the
fields of the whole chain of classes and runs the constructors from the root
base down, `this` is an alias binding to the location of the receiver inside a
member body, a method call runs the method of the static class of the
receiver, or of the class tag when the method is virtual, and `delete` runs
the destructors from the tag up and removes the locations of the object from
the store. The static classes come from `Typing.annotate`, applied by
`runWith` before the evaluation starts.

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
`conf arrow render a` in sequent notation, or the error, at the current depth. -/
def traced (rule conf : String) (render : α → String) (k : M α) (arrow : String := "⇒") : M α := do
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

def confE (e : Expr) (ρ : Env) (σ : Store) : String := s!"{ρ.toString}, {σ.toString} ⊢ {e}"
def confC (c : Cmd) (ρ : Env) (σ : Store) : String := s!"{ρ.toString}, {σ.toString} ⊢ {c}"
def showV (r : Val × Store) : String := s!"{r.1}, {r.2.toString}"
def showL (r : Loc × Store) : String := s!"{Loc.toString r.1}, {r.2.toString}"
def showR (r : Ctrl × Env × Store) : String := s!"{r.1}, {r.2.1.toString}, {r.2.2.toString}"

/-- Range check for `int`.

    n ∈ [−2³¹, 2³¹ − 1]              n ∉ [−2³¹, 2³¹ − 1]
    ──────────────────              ──────────────────────
    int32 n = int n                 int32 n = error (overflow)              -/
def int32 (n : Int) : M Val :=
  if Int32.inRange n then pure (.int n) else throw .overflow

/-- Unary operators.

    ρ, σ ⊢ e ⇒ bool b, σ'                    ρ, σ ⊢ e ⇒ int n, σ'
    ──────────────────────── (Not)           ────────────────────────── (Neg)
    ρ, σ ⊢ !e ⇒ bool ¬b, σ'                  ρ, σ ⊢ −e ⇒ int32 (−n), σ'          -/
def unop : UnOp → Val → M Val
  | .not, .bool b => pure (.bool !b)
  | .neg, .int n  => int32 (-n)
  | op, v => throw (.typeError s!"unary operator {op.toString} on {v}")

/-- Arithmetic and relational binary operators, on already evaluated values.

    ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int n₂, σ₂
    ──────────────────────────────────────────────── (Arith, ⊕ ∈ {+, −, ×})
    ρ, σ ⊢ e₁ ⊕ e₂ ⇒ int32 (n₁ ⊕ n₂), σ₂

    ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int n₂, σ₂    n₂ ≠ 0
    ──────────────────────────────────────────────────────── (Div, ⊘ ∈ {/, %})
    ρ, σ ⊢ e₁ ⊘ e₂ ⇒ int32 (n₁ ⊘ n₂), σ₂          division truncates toward zero, as in C++

    ρ, σ ⊢ e₁ ⇒ int n₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ int 0, σ₂
    ──────────────────────────────────────────────── (DivZero)
    ρ, σ ⊢ e₁ ⊘ e₂ ⇒ error (division by zero)

    ρ, σ ⊢ e₁ ⇒ v₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v₂, σ₂
    ─────────────────────────────────────────── (Rel, ⋈ ∈ {==, !=, <, <=, >, >=})
    ρ, σ ⊢ e₁ ⋈ e₂ ⇒ bool (v₁ ⋈ v₂), σ₂

    Two pointers are equal when they are the same location. nullptr equals
    only nullptr. There is no order on pointers.

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
  | .eq,  .loc a, .loc b => pure (.bool (a == b))
  | .ne,  .loc a, .loc b => pure (.bool (a != b))
  | .eq,  .null, .null => pure (.bool true)
  | .ne,  .null, .null => pure (.bool false)
  | .eq,  .loc _, .null | .eq, .null, .loc _ => pure (.bool false)
  | .ne,  .loc _, .null | .ne, .null, .loc _ => pure (.bool true)
  | op, v₁, v₂ => throw (.typeError s!"operator {op.toString} on {v₁} and {v₂}")

/-- Locations a block allocated, the owned bindings of ρ' ∖ ρ, for scope exit.
The bindings a reference declaration added alias locations that exist before
or outside the block, and those locations stay in σ. -/
def fresh (ρ ρ' : Env) : List Loc :=
  ((ρ'.take (ρ'.length - ρ.length)).filter (·.2.owned)).map (·.2.loc)

def expectBool (what : String) : Val → M Bool
  | .bool b => pure b
  | v => throw (.typeError s!"{what} is not boolean, got {v}")

/-- σ(ℓ), or error when ℓ ∉ dom σ. -/
def readLoc (σ : Store) (l : Loc) : M Val :=
  match σ.read l with
  | some v => pure v
  | none   => throw (.danglingLocation l)

/-- A pointer value as a live location. nullptr is error, the dereference
that C++ leaves undefined. -/
def pointee (v : Val) : M Loc :=
  match v with
  | .loc l => pure l
  | .null  => throw .nullDereference
  | v      => throw (.typeError s!"{v} is not a pointer")


/-- The free variables of a lambda body that the enclosing environment binds,
each with its current value, the captures of `[=]`. Reading a captured
variable whose location left the store is error. -/
def captures (ρ : Env) (σ : Store) (ps : List Param) (b : List Cmd) : M (List (String × Val)) := do
  let names := ((b.flatMap Cmd.vars).filter fun x => !(ps.any (·.name == x))).eraseDups
  let mut cap : List (String × Val) := []
  for x in names do
    if let some l := ρ.lookup x then
      cap := cap ++ [(x, ← readLoc σ l)]
  return cap

mutual

/-- ρ, σ ⊢ e ⇒ v, σ' -/
partial def expr (fs : FunEnv) (ρ : Env) (σ : Store) (e : Expr) : M (Val × Store) :=
  match e with
  /-  ───────────────────── (Lit)
      ρ, σ ⊢ n ⇒ int32 n, σ                                                     -/
  | .intLit n => traced "Lit" (confE e ρ σ) showV do return (← int32 n, σ)
  /-  ────────────────────── (BoolLit)
      ρ, σ ⊢ b ⇒ bool b, σ                                                      -/
  | .boolLit b => traced "BoolLit" (confE e ρ σ) showV do return (.bool b, σ)
  /-  ──────────────────────────── (Null)
      ρ, σ ⊢ nullptr ⇒ null, σ                                                  -/
  | .nullptr => traced "Null" (confE e ρ σ) showV do return (.null, σ)
  /-  ρ, σ ⊢ x ⇒ₗ ℓ, σ    ℓ ∈ dom σ
      ──────────────────────────────── (Var)       reading x is reading σ(ρ(x)), or the
      ρ, σ ⊢ x ⇒ σ(ℓ), σ                           field x of this inside a member body -/
  | .var x => traced "Var" (confE e ρ σ) showV do
    let (l, σ) ← lval fs ρ σ (.var x)
    return (← readLoc σ l, σ)
  /-  ρ(this) = ℓ
      ───────────────────────── (This)     this is the location of the receiver, bound
      ρ, σ ⊢ this ⇒ loc ℓ, σ               by the call of the member, never a variable -/
  | .this => traced "This" (confE e ρ σ) showV do
    match ρ.lookup "this" with
    | some l => return (.loc l, σ)
    | none => throw (.typeError "this outside a member body")
  /-  ρ, σ ⊢ e ⇒ₗ ℓ, σ'    ℓ ∈ dom σ'
      ────────────────────────────────── (Read)     e one of *e', e'.f, e'->f, e'[i]
      ρ, σ ⊢ e ⇒ σ'(ℓ), σ'                          reading a location is reading its content -/
  | .deref _ | .field .. | .arrow .. | .index .. => traced "Read" (confE e ρ σ) showV do
    let (l, σ') ← lval fs ρ σ e
    return (← readLoc σ' l, σ')
  /-  C ↦ class C : public B { … C(p₁ x₁, …, pₖ xₖ) { c } … }
      f₁ … fₙ = the fields of the chain of C, the root base first
      (ℓᵢ, σᵢ) = alloc σᵢ₋₁ (default τᵢ),  σ₀ = σ            one location per field, with its default value
      (ℓ, σ') = alloc σₙ (obj C [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ])       the record, tagged with the class
      the constructors of the chain run from the root base down, each with this ↦ ℓ,
      the one of C with the arguments as in Call, the others with none
      ────────────────────────────────────────────────────────────────────── (New)
      ρ, σ ⊢ new C(e₁, …, eₖ) ⇒ loc ℓ, σ''

      A class without a constructor is created by new C() and keeps the
      default values of its fields.                                                -/
  | .newObj c es => traced "New" (confE e ρ σ) showV do
    let chain := fs.chain c
    if chain.isEmpty then throw (.typeError s!"unknown class {c}")
    let flds := fs.allFields c
    let (ls, σ₁) := σ.allocMany (flds.map fun (f, _) => f.ty.default)
    let (l, σ₂) := σ₁.alloc (.obj c ((flds.map (·.1.name)).zip ls))
    let mut σ := σ₂
    for cd in chain.reverse do
      if let some k := cd.ctor then
        let args := if cd.name == c then es else []
        let (_, σ') ← runMember fs ρ σ l k.params k.body args .void s!"constructor of {cd.name}"
        σ := σ'
    return (.loc l, σ)
  /-  ρ, σ ⊢ e ⇒ₗ ℓ, σ₀ for e.m, or ρ, σ ⊢ e ⇒ loc ℓ, σ₀ for e->m    σ₀(ℓ) = obj T […]
      S = the static class of e, from the type checker
      m ↦ τ m(p₁ x₁, …, pₖ xₖ) { c } the method m nearest in the chain of S, or of T when that method is virtual
      arguments as in Call, this ↦ ℓ as an alias binding
      [this ↦ ℓ, x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ], σ'ₖ ⊢ c ⇒ ret v, ρ', σ''
      ────────────────────────────────────────────────────────────────────────── (MethodCall)
      ρ, σ ⊢ e.m(e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓᵢ | pᵢ by value} ∪ (ρ' ∖ ρ_m))

      Dispatch. A virtual method is chosen by the class tag T of the object,
      the one nearest T in the chain, so a call through a base pointer reaches
      the override of the derived class. A non virtual method is chosen by
      the static class S, and since Core C++ lets a derived class redefine a
      method only when the base declares it virtual, the two choices agree.
      With normal in place of ret v the result is void if τ = void and error
      (missing return) otherwise.                                                  -/
  | .methodCall recv arrow m es static sig => traced "MethodCall" (confE e ρ σ) showV do
    let (md, v, σ') ← callMethod fs ρ σ recv arrow m es static sig
    -- A member that returns a reference gives the location, read here
    -- because the call stands in a position that asks for a value.
    if md.retRef then return (← readLoc σ' (← pointee v), σ') else return (v, σ')
  /-  ρ, σ ⊢ n ⇒ int k, σ₁    k ≥ 0
      (ℓᵢ, σ'ᵢ) = alloc σ'ᵢ₋₁ (default τ) for 1 ≤ i ≤ k,  σ'₀ = σ₁    one location per element
      (ℓ, σ₂) = alloc σ'ₖ (vec [ℓ₁, …, ℓₖ])
      ─────────────────────────────────────────────────────────── (NewVec)
      ρ, σ ⊢ new std::vector<τ>(n) ⇒ loc ℓ, σ₂

      With k < 0 the result is error (negative size).                               -/
  | .newVec t n => traced "NewVec" (confE e ρ σ) showV do
    let (v, σ₁) ← expr fs ρ σ n
    let .int k := v | throw (.typeError s!"vector size {v} is not an int")
    if k < 0 then throw (.negativeSize k)
    let (ls, σ₂) := σ₁.allocMany (List.replicate k.toNat t.default)
    let (l, σ₃) := σ₂.alloc (.vec ls)
    return (.loc l, σ₃)
  /-  ρ, σ ⊢ e ⇒ v, σ'    op v = v'
      ─────────────────────────────── (Unary)
      ρ, σ ⊢ op e ⇒ v', σ'                                                      -/
  | .unop op e₁ => traced "Unary" (confE e ρ σ) showV do
    let (v, σ) ← expr fs ρ σ e₁
    return (← unop op v, σ)
  /-  ρ, σ ⊢ e₁ ⇒ bool false, σ₁                     ρ, σ ⊢ e₁ ⇒ bool true, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v, σ₂
      ─────────────────────────────── (And-False)    ────────────────────────────────────────────── (And-True)
      ρ, σ ⊢ e₁ && e₂ ⇒ bool false, σ₁               ρ, σ ⊢ e₁ && e₂ ⇒ v, σ₂
      short circuit, e₂ is evaluated only if e₁ is true                          -/
  | .binop .and e₁ e₂ => traced "And" (confE e ρ σ) showV do
    let (v₁, σ₁) ← expr fs ρ σ e₁
    if ← expectBool "left operand of &&" v₁ then expr fs ρ σ₁ e₂ else return (.bool false, σ₁)
  /-  ρ, σ ⊢ e₁ ⇒ bool true, σ₁                      ρ, σ ⊢ e₁ ⇒ bool false, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v, σ₂
      ─────────────────────────────── (Or-True)      ─────────────────────────────────────────────── (Or-False)
      ρ, σ ⊢ e₁ || e₂ ⇒ bool true, σ₁                ρ, σ ⊢ e₁ || e₂ ⇒ v, σ₂                             -/
  | .binop .or e₁ e₂ => traced "Or" (confE e ρ σ) showV do
    let (v₁, σ₁) ← expr fs ρ σ e₁
    if ← expectBool "left operand of ||" v₁ then return (.bool true, σ₁) else expr fs ρ σ₁ e₂
  /-  ρ, σ ⊢ e₁ ⇒ v₁, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v₂, σ₂    v₁ ⊕ v₂ = v
      ──────────────────────────────────────────────────────── (Binary)
      ρ, σ ⊢ e₁ ⊕ e₂ ⇒ v, σ₂          left before right                        -/
  | .binop op e₁ e₂ => traced "Binary" (confE e ρ σ) showV do
    let (v₁, σ₁) ← expr fs ρ σ e₁
    let (v₂, σ₂) ← expr fs ρ σ₁ e₂
    return (← binop op v₁ v₂, σ₂)
  /-  ρ, σ ⊢ e₁ ⇒ bool true, σ₁    ρ, σ₁ ⊢ e₂ ⇒ v, σ₂        ρ, σ ⊢ e₁ ⇒ bool false, σ₁    ρ, σ₁ ⊢ e₃ ⇒ v, σ₂
      ────────────────────────────────────────────── (Cond-T)   ─────────────────────────────────────────────── (Cond-F)
      ρ, σ ⊢ e₁ ? e₂ : e₃ ⇒ v, σ₂                                ρ, σ ⊢ e₁ ? e₂ : e₃ ⇒ v, σ₂                     -/
  | .cond e₁ e₂ e₃ => traced "Cond" (confE e ρ σ) showV do
    let (v₁, σ₁) ← expr fs ρ σ e₁
    if ← expectBool "condition" v₁ then expr fs ρ σ₁ e₂ else expr fs ρ σ₁ e₃
  /-  f ∉ ρ    f ↦ (τ f (p₁ x₁, …, pₖ xₖ) { c }) in the program
      for each i, left to right, with σ'₀ = σ,
        pᵢ = τᵢ      ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ    (ℓᵢ, σ'ᵢ) = alloc σᵢ vᵢ      call by value, a fresh location with a copy
        pᵢ = τᵢ&     ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ₗ ℓᵢ, σ'ᵢ                               call by reference, the location of the argument
      ρ_f = [x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]                                            only the parameters, the by value ones owned
      ρ_f, σ'ₖ ⊢ c ⇒ ret v, ρ', σ''
      ──────────────────────────────────────────────────────────────────── (Call)
      ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓᵢ | pᵢ by value} ∪ (ρ' ∖ ρ_f))         the return frees the copies and the locals
                                                                                of the body, never the referents

      With ρ_f, σ'ₖ ⊢ c ⇒ normal, ρ', σ'' the result is void, σ'' ∖ {ℓᵢ} if τ = void,
      and error (missing return) otherwise.

      ρ(f) = ℓ    σ(ℓ) = closure(…)    ρ, σ ⊢ ℓ(e₁, …, eₖ) as in CallFn
      ───────────────────────────────────────────────────────────── (CallFn)     a variable f bound to a
      ρ, σ ⊢ f(e₁, …, eₖ) ⇒ v, σ'                                                 function value hides the
                                                                                  function named f      -/
  | .call f es sig =>
    match ρ.lookup f with
    | some _ => traced "CallFn" (confE e ρ σ) showV do
      let (v, σ₁) ← expr fs ρ σ (.var f)
      applyClosure fs ρ σ₁ v es
    | none =>
      if (fs.lookup f).isNone && (ρ.lookup "this").isSome then
        -- an unqualified method name inside a member body is this->f(…),
        -- the form Typing.annotate produces; this case serves unannotated programs
        expr fs ρ σ (.methodCall .this true f es none none)
      else traced "Call" (confE e ρ σ) showV do
      let some fn := fs.lookupSig f sig | throw (.undeclaredFunction f)
      if fn.params.length != es.length then throw (.arity f)
      let mut σ := σ
      let mut ρf : Env := []
      let mut owned : List Loc := []
      for (p, a) in fn.params.zip es do
        if p.byRef then
          let (l, σ') ← lval fs ρ σ a
          σ := σ'
          ρf := ρf.alias p.name l
        else
          let (v, σ') ← expr fs ρ σ a
          let (l, σ'') := σ'.alloc v
          σ := σ''
          ρf := ρf.extend p.name l
          owned := l :: owned
      let (r, ρ', σ'') ← cmds fs ρf σ fn.body
      let σ''' := σ''.free (owned ++ fresh ρf ρ')
      match r, fn.ret with
      | .ret v, _      => return (v, σ''')
      | .normal, .void => return (.void, σ''')
      | .normal, _     => throw (.missingReturn f)
  /-  ρ, σ ⊢ e ⇒ closure(…), σ₀    the application as below
      ──────────────────────────────────────────────── (CallFn)
      ρ, σ ⊢ e(e₁, …, eₖ) ⇒ v, σ'                                                -/
  | .callFn fe es => traced "CallFn" (confE e ρ σ) showV do
    let (v, σ₁) ← expr fs ρ σ fe
    applyClosure fs ρ σ₁ v es
  /-  {y₁, …, yₘ} = the free variables of c bound in ρ, minus the xᵢ
      ρ(yⱼ) = ℓⱼ    ℓⱼ ∈ dom σ    wⱼ = σ(ℓⱼ)                             copies, taken at the lambda, read only
      ────────────────────────────────────────────────────────────────── (Lambda)
      ρ, σ ⊢ [=](τ₁ x₁, …, τₖ xₖ) -> τ { c } ⇒ closure(x⃗, τ, c, [y₁ ↦ w₁, …, yₘ ↦ wₘ]), σ

      The closure holds values, not locations. A captured pointer still reaches
      its object in σ, so an effect through it is visible outside, while a
      captured int or bool is a copy that the body cannot change.              -/
  | .lambda ps r b => traced "Lambda" (confE e ρ σ) showV do
    let cap ← captures ρ σ ps b
    return (.closure ps r b cap, σ)
  /-  ρ, σ ⊢ e ⇒ₗ ℓ, σ'
      ───────────────────────── (LocOf)      the location as a value, in the return
      ρ, σ ⊢ &e ⇒ loc ℓ, σ'                  of a member that returns a reference    -/
  | .locOf e₁ => traced "LocOf" (confE e ρ σ) showV do
    let (l, σ') ← lval fs ρ σ e₁
    return (.loc l, σ')

/-- The method m of class s with the signature the type checker chose, the
nearest in the chain of s, dispatched by the tag t when that method is
virtual. The signature picks one member of an overload set, and without it,
in an unannotated program, the first of the name serves. -/
partial def resolve (fs : FunEnv) (s t m : String) (sig : Option (List Ty)) : M (Method × String) := do
  let pick (c : String) : Option (Method × String) :=
    match sig with
    | some sg => (fs.findMethods c m).find? fun (md, _) => sigOf md.params == sg
    | none => fs.findMethod c m
  let some (md, k) := pick s | throw (.typeError s!"class {s} has no method {m}")
  if md.isVirtual then
    let some (md', k') := pick t | throw (.typeError s!"class {t} has no method {m}")
    return (md', k')
  else return (md, k)

/-- The receiver, the dispatch and the call of a method, shared by the value
position and the location position. The result of a member that returns a
reference is the location, `loc ℓ`, which the value position reads and the
location position takes as it is. -/
partial def callMethod (fs : FunEnv) (ρ : Env) (σ : Store) (recv : Expr) (arrow : Bool) (m : String)
    (es : List Expr) (static : Option String) (sig : Option (List Ty)) : M (Method × Val × Store) := do
  let (l, σ₀) ← if arrow then do
      let (v, σ') ← expr fs ρ σ recv
      pure (← pointee v, σ')
    else lval fs ρ σ recv
  let .obj tag _ ← readLoc σ₀ l | throw (.typeError s!"{recv} does not denote an object")
  let (md, k) ← resolve fs (static.getD tag) tag m sig
  let (v, σ') ← runMember fs ρ σ₀ l md.params md.body es md.ret s!"{k}::{m}"
  return (md, v, σ')

/-- The call of a member body, a method, a constructor or a destructor, with
this bound to the location ℓ of the receiver and the arguments bound as in
Call, by value with a fresh copy and by reference with an alias. The return
frees the copies and the locals of the body, never the receiver.

    for each i, left to right, with σ'₀ = σ,
      pᵢ = τᵢ      ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ vᵢ, σᵢ    (ℓᵢ, σ'ᵢ) = alloc σᵢ vᵢ
      pᵢ = τᵢ&     ρ, σ'ᵢ₋₁ ⊢ eᵢ ⇒ₗ ℓᵢ, σ'ᵢ
    ρ_m = [this ↦ ℓ, x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]    ρ_m, σ'ₖ ⊢ c ⇒ r, ρ', σ''
    ────────────────────────────────────────────────────────────── (Member)
    member ℓ (e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓᵢ | pᵢ by value} ∪ (ρ' ∖ ρ_m))          -/
partial def runMember (fs : FunEnv) (ρ : Env) (σ : Store) (l : Loc) (ps : List Param) (body : List Cmd)
    (es : List Expr) (ret : Ty) (who : String) : M (Val × Store) := do
  if ps.length != es.length then throw (.arity who)
  let mut σ := σ
  let mut ρm : Env := Env.alias [] "this" l
  let mut owned : List Loc := []
  for (q, a) in ps.zip es do
    if q.byRef then
      let (l', σ') ← lval fs ρ σ a
      σ := σ'
      ρm := ρm.alias q.name l'
    else
      let (v, σ') ← expr fs ρ σ a
      let (l', σ'') := σ'.alloc v
      σ := σ''
      ρm := ρm.extend q.name l'
      owned := l' :: owned
  let (r, ρ', σ'') ← cmds fs ρm σ body
  let σ''' := σ''.free (owned ++ fresh ρm ρ')
  match r, ret with
  | .ret v, _      => return (v, σ''')
  | .normal, .void => return (.void, σ''')
  | .normal, _     => throw (.missingReturn who)

/-- The application of a closure to arguments.

    v = closure(x₁ … xₖ, τ, c, [y₁ ↦ w₁, …, yₘ ↦ wₘ])
    ρ, σ ⊢ e₁ ⇒ v₁, σ₁  …  ρ, σₖ₋₁ ⊢ eₖ ⇒ vₖ, σₖ                    arguments left to right, by value
    (ℓ'ⱼ, ·) = alloc wⱼ    (ℓᵢ, ·) = alloc vᵢ                        fresh locations for the copies and the parameters
    ρ_c = [y₁ ↦ ℓ'₁, …, yₘ ↦ ℓ'ₘ, x₁ ↦ ℓ₁, …, xₖ ↦ ℓₖ]                the closure environment, nothing else is visible
    ρ_c, σ' ⊢ c ⇒ ret v, ρ'', σ''
    ─────────────────────────────────────────────────────────────── (Apply)
    apply v (e₁, …, eₖ) ⇒ v, σ'' ∖ ({ℓ'ⱼ, ℓᵢ} ∪ (ρ'' ∖ ρ_c))          the copies, the parameters and the locals leave

    With normal in place of ret v the result is void if τ = void and error
    (missing return) otherwise. A value that is not a closure is error.        -/
partial def applyClosure (fs : FunEnv) (ρ : Env) (σ : Store) (v : Val) (es : List Expr) : M (Val × Store) := do
  let .closure ps r b cap := v | throw (.notCallable v)
  if ps.length != es.length then throw (.arity "lambda")
  let mut σ := σ
  let mut vs : List Val := []
  for a in es do
    let (v, σ') ← expr fs ρ σ a
    σ := σ'
    vs := vs ++ [v]
  let mut ρc : Env := []
  let mut ls : List Loc := []
  for (y, w) in cap do
    let (l, σ') := σ.alloc w
    σ := σ'
    ρc := ρc.extend y l
    ls := l :: ls
  for (p, v) in ps.zip vs do
    let (l, σ') := σ.alloc v
    σ := σ'
    ρc := ρc.extend p.name l
    ls := l :: ls
  let (res, ρ'', σ'') ← cmds fs ρc σ b
  let σ''' := σ''.free (ls ++ fresh ρc ρ'')
  match res, r with
  | .ret v, _      => return (v, σ''')
  | .normal, .void => return (.void, σ''')
  | .normal, _     => throw (.missingReturn "lambda")

/-- ρ, σ ⊢ e ⇒ₗ ℓ, σ', the expressions that denote a location. A variable, a
dereferenced pointer, a field of an object, a field through a pointer and an
element of a vector.

    ρ(x) = ℓ                     ρ, σ ⊢ e ⇒ loc ℓ, σ'
    ──────────────────── (LocVar)  ────────────────────── (LocDeref)    nullptr is error
    ρ, σ ⊢ x ⇒ₗ ℓ, σ             ρ, σ ⊢ *e ⇒ₗ ℓ, σ'

    ρ, σ ⊢ e ⇒ₗ ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
    ─────────────────────────────────────────────── (LocField)
    ρ, σ ⊢ e.f ⇒ₗ ℓ_f, σ'

    ρ, σ ⊢ e ⇒ loc ℓ, σ'    σ'(ℓ) = obj C [… f ↦ ℓ_f …]
    ────────────────────────────────────────────────── (LocArrow)    e->f is (*e).f
    ρ, σ ⊢ e->f ⇒ₗ ℓ_f, σ'

    ρ, σ ⊢ e ⇒ₗ ℓ, σ₁    σ₁(ℓ) = vec [ℓ₀, …, ℓₙ₋₁]    ρ, σ₁ ⊢ i ⇒ int k, σ₂    0 ≤ k < n
    ──────────────────────────────────────────────────────────────────────────────── (LocIndex)
    ρ, σ ⊢ e[i] ⇒ₗ ℓₖ, σ₂

    With k outside [0, n) the result is error (out of bounds), where C++
    leaves it undefined.                                                            -/
partial def lval (fs : FunEnv) (ρ : Env) (σ : Store) (e : Expr) : M (Loc × Store) :=
  match e with
  /-  ρ(x) = ℓ                      x ∉ ρ    ρ(this) = ℓ    σ(ℓ) = obj C [… x ↦ ℓ_x …]
      ──────────────── (LocVar)     ─────────────────────────────────────────── (LocVarField)
      ρ, σ ⊢ x ⇒ₗ ℓ, σ              ρ, σ ⊢ x ⇒ₗ ℓ_x, σ        an unqualified field of this -/
  | .var x => traced "LocVar" (confE e ρ σ) showL (arrow := "⇒ₗ") do
    match ρ.lookup x with
    | some l => return (l, σ)
    | none   =>
      match ρ.lookup "this" with
      | some lt => fieldLoc σ lt x
      | none => throw (.undeclaredVariable x)
  | .deref e₁ => traced "LocDeref" (confE e ρ σ) showL (arrow := "⇒ₗ") do
    let (v, σ') ← expr fs ρ σ e₁
    return (← pointee v, σ')
  | .field e₁ f => traced "LocField" (confE e ρ σ) showL (arrow := "⇒ₗ") do
    let (l, σ') ← lval fs ρ σ e₁
    fieldLoc σ' l f
  | .arrow e₁ f => traced "LocArrow" (confE e ρ σ) showL (arrow := "⇒ₗ") do
    let (v, σ') ← expr fs ρ σ e₁
    fieldLoc σ' (← pointee v) f
  /-  the member m of C returns τ&    member ℓ (e₁, …, eₖ) ⇒ loc ℓ', σ'
      ──────────────────────────────────────────────────────────── (MethodLoc)
      ρ, σ ⊢ e.m(e₁, …, eₖ) ⇒ₗ ℓ', σ'                                            -/
  | .methodCall recv arrow m es static sig => traced "MethodLoc" (confE e ρ σ) showL (arrow := "⇒ₗ") do
    let (md, v, σ') ← callMethod fs ρ σ recv arrow m es static sig
    if !md.retRef then throw (.typeError s!"{m} does not return a reference")
    return (← pointee v, σ')
  | .index e₁ i => traced "LocIndex" (confE e ρ σ) showL (arrow := "⇒ₗ") do
    let (l, σ₁) ← lval fs ρ σ e₁
    let .vec ls ← readLoc σ₁ l | throw (.typeError s!"{e₁} is not a vector")
    let (v, σ₂) ← expr fs ρ σ₁ i
    let .int k := v | throw (.typeError s!"index {v} is not an int")
    if k < 0 || k ≥ ls.length then throw (.outOfBounds k ls.length)
    return (ls[k.toNat]!, σ₂)
  | _ => throw (.typeError s!"expression does not denote a location: {e}")

/-- The location of field f of the object stored at ℓ. -/
partial def fieldLoc (σ : Store) (l : Loc) (f : String) : M (Loc × Store) := do
  let .obj c fs ← readLoc σ l | throw (.typeError s!"{Loc.toString l} does not hold an object")
  match fs.lookup f with
  | some lf => return (lf, σ)
  | none    => throw (.typeError s!"class {c} has no field {f}")

/-- ρ, σ ⊢ c ⇒ r, ρ', σ' -/
partial def cmd (fs : FunEnv) (ρ : Env) (σ : Store) (c : Cmd) : M (Ctrl × Env × Store) :=
  match c with
  /-  ρ, σ ⊢ c₁ … cₙ ⇒ r, ρ', σ'
      ──────────────────────────────────────────── (Block)
      ρ, σ ⊢ { c₁ … cₙ } ⇒ r, ρ, σ' ∖ (ρ' ∖ ρ)
      the block discards the extension of ρ and removes from σ the locations it
      allocated, ρ' ∖ ρ read as the owned bindings, so an alias made by a
      reference declaration never frees the location it names -/
  | .block cs => traced "Block" (confC c ρ σ) showR do
    let (r, ρ', σ') ← cmds fs ρ σ cs
    return (r, ρ, σ'.free (fresh ρ ρ'))
  /-  ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c₁} ⇒ r, ρ, σ₂          ρ, σ ⊢ e ⇒ bool false, σ₁    ρ, σ₁ ⊢ {c₂} ⇒ r, ρ, σ₂
      ────────────────────────────────────────────────── (If-T)     ─────────────────────────────────────────────────── (If-F)
      ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂                        ρ, σ ⊢ if (e) {c₁} else {c₂} ⇒ r, ρ, σ₂             -/
  | .ite e t f => traced "If" (confC c ρ σ) showR do
    let (v, σ₁) ← expr fs ρ σ e
    if ← expectBool "condition of if" v then cmd fs ρ σ₁ (.block t) else cmd fs ρ σ₁ (.block f)
  /-  ρ, σ ⊢ e ⇒ bool false, σ₁
      ──────────────────────────────────────── (While-F)
      ρ, σ ⊢ while (e) {c} ⇒ normal, ρ, σ₁

      ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ normal, ρ, σ₂    ρ, σ₂ ⊢ while (e) {c} ⇒ r, ρ, σ₃
      ────────────────────────────────────────────────────────────────────────────────────── (While-T)
      ρ, σ ⊢ while (e) {c} ⇒ r, ρ, σ₃

      ρ, σ ⊢ e ⇒ bool true, σ₁    ρ, σ₁ ⊢ {c} ⇒ ret v, ρ, σ₂
      ────────────────────────────────────────────────────── (While-Ret)   the return interrupts the loop
      ρ, σ ⊢ while (e) {c} ⇒ ret v, ρ, σ₂

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
  /-  ρ, σ ⊢ c₀ ⇒ normal, ρ₀, σ₀    ρ₀, σ₀ ⊢ while (e) { {c} cₛ } ⇒ r, ρ₀, σ₁
      ────────────────────────────────────────────────────────────────────── (For)
      ρ, σ ⊢ for (c₀; e; cₛ) {c} ⇒ r, ρ, σ₁ ∖ (ρ₀ ∖ ρ)
      the variable of c₀ has the loop as its scope, the body is its own block, and
      the step cₛ runs after the body, outside the body's scope                                       -/
  | .for c₀ e cₛ b => traced "For" (confC c ρ σ) showR do
    let (r₀, ρ₀, σ₀) ← cmd fs ρ σ c₀
    match r₀ with
    | .ret _ => throw (.typeError "return in for initialiser")
    | .normal =>
      let (r, _, σ₁) ← cmd fs ρ₀ σ₀ (.while e [.block b, cₛ])
      return (r, ρ, σ₁.free (fresh ρ ρ₀))
  /-  ρ, σ ⊢ e ⇒ v, σ'
      ─────────────────────────────── (Return)         ────────────────────────────────── (ReturnVoid)
      ρ, σ ⊢ return e ⇒ ret v, ρ, σ'                   ρ, σ ⊢ return ⇒ ret void, ρ, σ                 -/
  | .ret none => traced "ReturnVoid" (confC c ρ σ) showR do return (.ret .void, ρ, σ)
  | .ret (some e) => traced "Return" (confC c ρ σ) showR do
    let (v, σ') ← expr fs ρ σ e
    return (.ret v, ρ, σ')
  /-  ρ, σ ⊢ e ⇒ v, σ'    (ℓ, σ'') = alloc σ' v    ℓ ∉ dom σ'
      ──────────────────────────────────────────────────────── (Decl)
      ρ, σ ⊢ τ x = e ⇒ normal, ρ[x ↦ ℓ], σ''
      the declaration allocates a fresh location and extends ρ for the following commands -/
  | .decl _ x e => traced "Decl" (confC c ρ σ) showR do
    let (v, σ') ← expr fs ρ σ e
    let (l, σ'') := σ'.alloc v
    return (.normal, ρ.extend x l, σ'')
  /-  ρ, σ ⊢ e ⇒ₗ ℓ, σ'
      ───────────────────────────────────────────── (DeclRef)
      ρ, σ ⊢ τ& x = e ⇒ normal, ρ[x ↦ ℓ], σ'
      a reference binds a second name to an existing location, nothing is
      allocated and the binding is not owned, so block exit leaves ℓ in σ      -/
  | .declRef _ x e => traced "DeclRef" (confC c ρ σ) showR do
    let (l, σ') ← lval fs ρ σ e
    return (.normal, ρ.alias x l, σ')
  /-  The rule for auto is Decl, with τ the type of v.                            -/
  | .declAuto x e => traced "Decl" (confC c ρ σ) showR do
    let (v, σ') ← expr fs ρ σ e
    let (l, σ'') := σ'.alloc v
    return (.normal, ρ.extend x l, σ'')
  /-  ρ, σ ⊢ e₂ ⇒ v, σ₁    ρ, σ₁ ⊢ e₁ ⇒ₗ ℓ, σ₂    ℓ ∈ dom σ₂
      ──────────────────────────────────────────────────────── (Assign)
      ρ, σ ⊢ e₁ = e₂ ⇒ normal, ρ, σ₂[ℓ ↦ v]
      right operand before left, the order C++17 fixes for assignment            -/
  | .assign e₁ e₂ => traced "Assign" (confC c ρ σ) showR do
    let (v, σ₁) ← expr fs ρ σ e₂
    let (l, σ₂) ← lval fs ρ σ₁ e₁
    if (σ₂.read l).isNone then throw (.danglingLocation l)
    return (.normal, ρ, σ₂.write l v)
  /-  ρ, σ ⊢ e ⇒ v, σ'
      ──────────────────────────── (ExprStmt)      the value is discarded
      ρ, σ ⊢ e; ⇒ normal, ρ, σ'                                                 -/
  | .exprStmt e => traced "ExprStmt" (confC c ρ σ) showR do
    let (_, σ') ← expr fs ρ σ e
    return (.normal, ρ, σ')
  /-  ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = obj T [f₁ ↦ ℓ₁, …, fₙ ↦ ℓₙ]    S = the static class of e
      S = T or the chain of S has a virtual destructor
      the destructors of the chain of T run from T up to the root, each with this ↦ ℓ, giving σ₁
      ───────────────────────────────────────────────────────────────────────────── (Delete)
      ρ, σ ⊢ delete e ⇒ normal, ρ, σ₁ ∖ {ℓ, ℓ₁, …, ℓₙ}

      ρ, σ ⊢ e ⇒ loc ℓ, σ₀    σ₀(ℓ) = vec [ℓ₁, …, ℓₙ]         ρ, σ ⊢ e ⇒ null, σ₀
      ─────────────────────────────────────────────── (DeleteVec)   ────────────────────────────── (DeleteNull)
      ρ, σ ⊢ delete e ⇒ normal, ρ, σ₀ ∖ {ℓ, ℓ₁, …, ℓₙ}              ρ, σ ⊢ delete e ⇒ normal, ρ, σ₀

      With ℓ ∉ dom σ₀ the result is error (double delete), and with S ≠ T and no
      virtual destructor in the chain of S it is error, the two cases C++17
      leaves undefined. delete nullptr does nothing, as in C++.                  -/
  | .delete e static => traced "Delete" (confC c ρ σ) showR do
    let (v, σ₀) ← expr fs ρ σ e
    match v with
    | .null => return (.normal, ρ, σ₀)
    | .loc l =>
      match σ₀.read l with
      | none => throw (.doubleDelete l)
      | some (.vec ls) => return (.normal, ρ, σ₀.free (l :: ls))
      | some (.obj tag flds) =>
        let s := static.getD tag
        if s != tag && !fs.hasVirtualDtor s then throw (.deleteWithoutVirtualDtor s tag)
        let mut σ := σ₀
        for cd in fs.chain tag do
          if let some d := cd.dtor then
            let (_, σ') ← runMember fs ρ σ l [] d.body [] .void s!"destructor of {cd.name}"
            σ := σ'
        return (.normal, ρ, σ.free (l :: flds.map (·.2)))
      | some w => throw (.typeError s!"delete of {w}, not an object")
    | w => throw (.typeError s!"delete of {w}, not a pointer")

/-- Command sequences.

    ────────────────────────── (Seq-Empty)
    ρ, σ ⊢ ε ⇒ normal, ρ, σ

    ρ, σ ⊢ c ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ cs ⇒ r, ρ₂, σ₂
    ──────────────────────────────────────────────────── (Seq)   ρ₁ carries the binding of c to the rest
    ρ, σ ⊢ c cs ⇒ r, ρ₂, σ₂

    ρ, σ ⊢ c ⇒ ret v, ρ₁, σ₁
    ───────────────────────────── (Seq-Ret)   the return interrupts the sequence
    ρ, σ ⊢ c cs ⇒ ret v, ρ₁, σ₁                                                                -/
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

    main ↦ (int main() { c })    [], ∅ ⊢ main() ⇒ v, σ
    ─────────────────────────────────────────────────── (Program)
    p ⇒ v

    The objects created with new stay in σ until delete or the end of the
    program. The locals of main leave σ with the return of the call, so the
    final store holds objects only. The program is annotated with the static
    classes of method calls and deletes before it runs, when it is well typed,
    and otherwise runs as parsed, with every dispatch by the class tag.        -/
def runWith (trace : Bool) (p : Program) : Except Error Val × Array TraceEntry :=
  let p := (Typing.annotate p).toOption.getD p
  let (r, s) := (Eval.expr p [] {} (.call "main" [] none)).run.run { enabled := trace }
  (r.map (·.1), s.log)

def run (p : Program) : Except Error Val := (runWith false p).1

/-- Renders the trace as the derivation tree in post-order, indented by depth. -/
def renderTrace (log : Array TraceEntry) : String :=
  "\n".intercalate (log.toList.map fun t => "".pushn ' ' (2 * t.depth) ++ t.text)

end CoreCpp
