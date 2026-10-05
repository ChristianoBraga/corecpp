import CoreCpp.Semantics.Library

/-!
# The dynamic semantics of Core C++, as relations

One inductive proposition per judgement, one constructor per rule, named as
in the blueprint.

| Judgement | Relation | Meaning |
| --- | --- | --- |
| ρ, σ ⊢ e ⇒ v, σ′ | `Eval p ρ σ e v σ′` | e has the value v |
| ρ, σ ⊢ e ⇒ₗ ℓ, σ′ | `LEval p ρ σ e ℓ σ′` | e denotes the location ℓ |
| ρ, σ ⊢ c ⇒ r, ρ′, σ′ | `Exec p ρ σ c r ρ′ σ′` | c ends with the control r |
| ρ, σ ⊢ c̄ ⇒ r, ρ′, σ′ | `Execs p ρ σ c̄ r ρ′ σ′` | the sequence c̄ ends with r |

The program p, the function table and the class table, is a parameter of
every relation. The auxiliaries `Args`, `Bind`, `Member`, `CallMethod`,
`Ctors`, `Dtors`, `Apply`, `ApplyArgs` and `Returns` name shared premises.

The relation is the specification and `CoreCpp.Eval` the implementation.
There is no `error`. Whatever C++17 leaves undefined has no derivation, and
the evaluator gives `error` for it. The subject is the program as
`Typing.annotate` leaves it. A subject of the library is judged by the module
its header declares, through the relations of `CoreCpp.Semantics.Library`,
the premises of NewLib, LocIndex, DeleteLib and CallLib.
-/

namespace CoreCpp.Semantics

/-! ## Notation

The judgements as the rules write them.

| Judgement | Notation | Expands to |
| --- | --- | --- |
| ρ, σ ⊢ e ⇒ v, σ′ | `⟨ρ, σ⟩ ⊢ e ⇒ v, σ'` | `Eval p ρ σ e v σ'` |
| ρ, σ ⊢ e ⇒ₗ ℓ, σ′ | `⟨ρ, σ⟩ ⊢ e ⇒ₗ ℓ, σ'` | `LEval p ρ σ e ℓ σ'` |
| ρ, σ ⊢ c ⇒ r, ρ′, σ′ | `⟨ρ, σ⟩ ⊢ c ⇒ r, ρ', σ'` | `Exec p ρ σ c r ρ' σ'` |
| ρ, σ ⊢ c̄ ⇒ r, ρ′, σ′ | `⟨ρ, σ⟩ ⊢ cs ⇒* r, ρ', σ'` | `Execs p ρ σ cs r ρ' σ'` |

The configuration ⟨ρ, σ⟩ is in angle brackets, since a comma after a bare
term would clash with the tuples of Lean, and the program is left out, which is the `p` in scope, the parameter of the
relations, so that the rules read as they do in the blueprint. A sequence of
commands takes `⇒*`, since the parser cannot tell a command from a list of
commands. The notation is declared before the relations it names, so that the
rules use it, and hygiene is off so that `p` and the names `Eval`, `LEval`,
`Exec` and `Execs` resolve at the use site, the latter to the relations under
definition inside the `mutual` block. -/

set_option hygiene false in
set_option quotPrecheck false in
scoped notation:40 "⟨" ρ:41 ", " σ:41 "⟩" " ⊢ " e:41 " ⇒ " v:41 ", " σ':41 => Eval p ρ σ e v σ'

set_option hygiene false in
set_option quotPrecheck false in
scoped notation:40 "⟨" ρ:41 ", " σ:41 "⟩" " ⊢ " e:41 " ⇒ₗ " ℓ:41 ", " σ':41 => LEval p ρ σ e ℓ σ'

set_option hygiene false in
set_option quotPrecheck false in
scoped notation:40 "⟨" ρ:41 ", " σ:41 "⟩" " ⊢ " c:41 " ⇒ " r:41 ", " ρ':41 ", " σ':41 => Exec p ρ σ c r ρ' σ'

set_option hygiene false in
set_option quotPrecheck false in
scoped notation:40 "⟨" ρ:41 ", " σ:41 "⟩" " ⊢ " cs:41 " ⇒* " r:41 ", " ρ':41 ", " σ':41 => Execs p ρ σ cs r ρ' σ'

end CoreCpp.Semantics

namespace CoreCpp

/-- The set fresh(ρ, ρ′), the locations a block allocated, the owned bindings of ρ′ ∖ ρ. The bindings
a reference declaration added alias locations that exist before the block, and
those stay in σ. -/
def Env.fresh (ρ ρ' : Env) : List Loc :=
  ((ρ'.take (ρ'.length - ρ.length)).filter (·.2.owned)).map (·.2.loc)

/-- ρ[x₁ ↦ ℓ₁]…[xₖ ↦ ℓₖ], owned bindings in order. -/
def Env.extendAll (ρ : Env) : List String → List Loc → Env
  | x :: xs, l :: ls => (ρ.extend x l).extendAll xs ls
  | _, _ => ρ

/-- The arithmetic operators, `+`, `−` and `×`. -/
def BinOp.isArith : BinOp → Bool
  | .add | .sub | .mul => true
  | _ => false

/-- n₁ ⊕ n₂ for an arithmetic operator. -/
def BinOp.arith : BinOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | _, _, _ => 0

/-- n₁ ⊘ n₂ for `/` and `%`, truncating toward zero as C++ does. The
remainder exists only when the quotient is in the range of `int`, since C++
leaves both undefined otherwise (N4659 §8.6 ¶4). -/
def BinOp.divide : BinOp → Int → Int → Option Int
  | .div, a, b => some (a.tdiv b)
  | .mod, a, b => if Int32.inRange (a.tdiv b) then some (a.tmod b) else none
  | _, _, _ => none

/-- v₁ ⋈ v₂ for a relational operator. Two pointers are equal when they are
the same location, `nullptr` equals only `nullptr`, and there is no order on
pointers. -/
def BinOp.compare : BinOp → Val → Val → Option Bool
  | .eq, .int a, .int b => some (a == b)
  | .ne, .int a, .int b => some (a != b)
  | .lt, .int a, .int b => some (a < b)
  | .le, .int a, .int b => some (a ≤ b)
  | .gt, .int a, .int b => some (a > b)
  | .ge, .int a, .int b => some (a ≥ b)
  | .eq, .bool a, .bool b => some (a == b)
  | .ne, .bool a, .bool b => some (a != b)
  | .eq, .loc a, .loc b => some (a == b)
  | .ne, .loc a, .loc b => some (a != b)
  | .eq, .null, .null => some true
  | .ne, .null, .null => some false
  | .eq, .loc _, .null | .eq, .null, .loc _ => some false
  | .ne, .loc _, .null | .ne, .null, .loc _ => some true
  | _, _, _ => none

/-- The expressions that denote a location and are read in a value position,
`*e`, `e.f`, `e->f` and `e[i]`. -/
def Expr.isPlace : Expr → Bool
  | .deref _ | .field .. | .arrow .. | .index .. => true
  | _ => false

/-- The captures of `[=]`, the free variables of the body that ρ binds, each
with its value in σ, or nothing when a captured location left σ. -/
def captures? (ρ : Env) (σ : Store) (ps : List Param) (b : List Cmd) : Option (List (String × Val)) :=
  let names := ((b.flatMap Cmd.vars).filter fun x => !(ps.any (·.name == x))).eraseDups
  names.foldlM (init := []) fun cap x =>
    match ρ.lookup x with
    | none => some cap
    | some l => (σ.read l).map fun v => cap ++ [(x, v)]

/-- The method m of the static class s with the signature the type checker
chose, the nearest in the chain of s, dispatched by the tag t of the object
when that method is virtual. -/
def Program.resolve (p : Program) (s t m : String) (sig : Option (List Ty)) : Option (Method × String) :=
  let pick (c : String) : Option (Method × String) :=
    match sig with
    | some sg => (p.findMethods c m).find? fun (md, _) => sigOf md.params == sg
    | none => p.findMethod c m
  match pick s with
  | none => none
  | some (md, k) => if md.isVirtual then pick t else some (md, k)

namespace Semantics

/-- The value a body with result type τ gives through its control. -/
inductive Returns : Ctrl → Ty → Val → Prop where
  /-- A `return e` gives the value of e. -/
  | ret : Returns (.ret v) τ v
  /-- A body of a `void` function that ends without `return` gives `void`. A
  body of another type that ends without `return` has no derivation. -/
  | void : Returns .normal .void .void

mutual

/-- ρ, σ ⊢ e ⇒ v, σ′ -/
inductive Eval (p : Program) : Env → Store → Expr → Val → Store → Prop where
  | lit
      (h : Int32.inRange n) :
    -- ────────────────────────────── (Lit)
      ⟨ρ, σ⟩ ⊢ .intLit n ⇒ .int n, σ

  | boolLit :
    -- ──────────────────────────────── (BoolLit)
      ⟨ρ, σ⟩ ⊢ .boolLit b ⇒ .bool b, σ

  | null :
    -- ──────────────────────────── (Null)
      ⟨ρ, σ⟩ ⊢ .nullptr ⇒ .null, σ

  /-- Reading x is reading σ(ρ(x)), or the field x of `this` inside a member. -/
  | var
      (hl : ⟨ρ, σ⟩ ⊢ .var x ⇒ₗ ℓ, σ)
      (hr : σ.read ℓ = some v) :
    -- ────────────────────────────── (Var)
      ⟨ρ, σ⟩ ⊢ .var x ⇒ v, σ

  | this
      (h : ρ.lookup "this" = some ℓ) :
    -- ────────────────────────────── (This)
      ⟨ρ, σ⟩ ⊢ .this ⇒ .loc ℓ, σ

  | read
      (hp : e.isPlace)
      (hl : ⟨ρ, σ⟩ ⊢ e ⇒ₗ ℓ, σ')
      (hr : σ'.read ℓ = some v) :
    -- ────────────────────────── (Read)
      ⟨ρ, σ⟩ ⊢ e ⇒ v, σ'

  /-- The constructor of C receives the arguments, the others none. -/
  | new
      (hc : p.chain c ≠ [])
      (ha : σ.allocMany ((p.allFields c).map fun (f, _) => f.ty.default) = (ls, σ₁))
      (ho : σ₁.alloc (.obj c (((p.allFields c).map (·.1.name)).zip ls)) = (ℓ, σ₂))
      (hk : Ctors p ρ σ₂ ℓ c (p.chain c).reverse es σ₃) :
    -- ────────────────────────────────────────────────────────────────────── (New)
      ⟨ρ, σ⟩ ⊢ .newObj c es ⇒ .loc ℓ, σ₃

  /-- See `CallMethod`. The method returns a value. -/
  | methodCall
      (h : CallMethod p ρ σ recv arrow m es static sig md v σ')
      (hr : md.retRef = false) :
    -- ───────────────────────────────────────────────────────── (MethodCall)
      ⟨ρ, σ⟩ ⊢ .methodCall recv arrow m es static sig ⇒ v, σ'

  /-- In a value position the location a member returns is read. -/
  | methodCallRef
      (h : CallMethod p ρ σ recv arrow m es static sig md (.loc ℓ) σ')
      (hr : md.retRef = true)
      (hv : σ'.read ℓ = some v) :
    -- ──────────────────────────────────────────────────────────────── (MethodCallRef)
      ⟨ρ, σ⟩ ⊢ .methodCall recv arrow m es static sig ⇒ v, σ'

  /-- The last premise is the relation `new` of the module of L. -/
  | newLib
      (ha : Args p ρ σ es vs σ₁)
      (hM : moduleOf L = some M)
      (hn : M.new ts vs σ₁ v σ₂) :
    -- ─────────────────────────────────────── (NewLib)
      ⟨ρ, σ⟩ ⊢ .newLib (.lib L ts) es ⇒ v, σ₂

  | not
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ .bool b, σ') :
    -- ──────────────────────────────────── (Not)
      ⟨ρ, σ⟩ ⊢ .unop .not e ⇒ .bool !b, σ'

  | neg
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ .int n, σ')
      (hr : Int32.inRange (-n)) :
    -- ───────────────────────────────────── (Neg)
      ⟨ρ, σ⟩ ⊢ .unop .neg e ⇒ .int (-n), σ'

  /-- Left before right, the Core C++ order where C++17 fixes none. An overflow has no derivation. -/
  | arith
      (hop : op.isArith)
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .int n₁, σ₁)
      (h₂ : ⟨ρ, σ₁⟩ ⊢ e₂ ⇒ .int n₂, σ₂)
      (hr : Int32.inRange (op.arith n₁ n₂)) :
    -- ──────────────────────────────────────────────────── (Arith)
      ⟨ρ, σ⟩ ⊢ .binop op e₁ e₂ ⇒ .int (op.arith n₁ n₂), σ₂

  /-- A zero divisor and a result outside the range of `int` have no derivation. -/
  | div
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .int n₁, σ₁)
      (h₂ : ⟨ρ, σ₁⟩ ⊢ e₂ ⇒ .int n₂, σ₂)
      (hz : n₂ ≠ 0)
      (hd : op.divide n₁ n₂ = some n)
      (hr : Int32.inRange n) :
    -- ───────────────────────────────────── (Div)
      ⟨ρ, σ⟩ ⊢ .binop op e₁ e₂ ⇒ .int n, σ₂

  | rel
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ v₁, σ₁)
      (h₂ : ⟨ρ, σ₁⟩ ⊢ e₂ ⇒ v₂, σ₂)
      (hc : op.compare v₁ v₂ = some b) :
    -- ────────────────────────────────────── (Rel)
      ⟨ρ, σ⟩ ⊢ .binop op e₁ e₂ ⇒ .bool b, σ₂

  | andF
      (h : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .bool false, σ₁) :
    -- ──────────────────────────────────────────── (And-False)
      ⟨ρ, σ⟩ ⊢ .binop .and e₁ e₂ ⇒ .bool false, σ₁

  | andT
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .bool true, σ₁)
      (h₂ : ⟨ρ, σ₁⟩ ⊢ e₂ ⇒ v, σ₂) :
    -- ─────────────────────────────────── (And-True)
      ⟨ρ, σ⟩ ⊢ .binop .and e₁ e₂ ⇒ v, σ₂

  | orT
      (h : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .bool true, σ₁) :
    -- ────────────────────────────────────────── (Or-True)
      ⟨ρ, σ⟩ ⊢ .binop .or e₁ e₂ ⇒ .bool true, σ₁

  | orF
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .bool false, σ₁)
      (h₂ : ⟨ρ, σ₁⟩ ⊢ e₂ ⇒ v, σ₂) :
    -- ──────────────────────────────────── (Or-False)
      ⟨ρ, σ⟩ ⊢ .binop .or e₁ e₂ ⇒ v, σ₂

  | condT
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .bool true, σ₁)
      (h₂ : ⟨ρ, σ₁⟩ ⊢ e₂ ⇒ v, σ₂) :
    -- ─────────────────────────────────── (Cond-T)
      ⟨ρ, σ⟩ ⊢ .cond e₁ e₂ e₃ ⇒ v, σ₂

  | condF
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .bool false, σ₁)
      (h₃ : ⟨ρ, σ₁⟩ ⊢ e₃ ⇒ v, σ₂) :
    -- ──────────────────────────────────── (Cond-F)
      ⟨ρ, σ⟩ ⊢ .cond e₁ e₂ e₃ ⇒ v, σ₂

  /-- See `Bind` and `Returns`. The return frees the copies and the locals of the body, never the referents. -/
  | call
      (hρ : ρ.lookup f = none)
      (hf : FunEnv.lookupSig p f sig = some fn)
      (hn : fn.params.length = es.length)
      (hb : Bind p ρ σ [] fn.params es ρf σ₁ owned)
      (hx : ⟨ρf, σ₁⟩ ⊢ fn.body ⇒* r, ρ', σ₂)
      (hr : Returns r fn.ret v) :
    -- ─────────────────────────────────────────────────────────────── (Call)
      ⟨ρ, σ⟩ ⊢ .call f es sig ⇒ v, σ₂.free (owned ++ Env.fresh ρf ρ')

  /-- A variable f bound to a `std::function` object, a reference parameter,
  hides the function named f. -/
  | callVar
      (hρ : ρ.lookup f = some ℓ)
      (hv : ⟨ρ, σ⟩ ⊢ .var f ⇒ .lib "std::function" [ℓₜ], σ₁)
      (ht : σ₁.read ℓₜ = some w)
      (ha : ApplyArgs p ρ σ₁ w es v σ') :
    -- ───────────────────────────────── (CallFn)
      ⟨ρ, σ⟩ ⊢ .call f es sig ⇒ v, σ'

  /-- An unqualified method name inside a member body. -/
  | callThis
      (hρ : ρ.lookup f = none)
      (hf : FunEnv.lookup p f = none)
      (hl : p.libDecls.lookup f = none)
      (ht : ρ.lookup "this" = some ℓ)
      (h : ⟨ρ, σ⟩ ⊢ .methodCall .this true f es none none ⇒ v, σ') :
    -- ──────────────────────────────────────────────────────────── (CallThis)
      ⟨ρ, σ⟩ ⊢ .call f es sig ⇒ v, σ'

  /-- The last premise is the relation `call` of the module of f. -/
  | callLib
      (hρ : ρ.lookup f = none)
      (hf : FunEnv.lookupSig p f sig = none)
      (hd : (f, es.length) ∈ p.libDecls)
      (hM : moduleOf f = some M)
      (ha : Args p ρ σ es vs σ₁)
      (hc : M.call vs σ₁ v σ₂) :
    -- ────────────────────────────────────── (CallLib)
      ⟨ρ, σ⟩ ⊢ .call f es sig ⇒ v, σ₂

  /-- The callee is a `std::function` object, `*f` for a pointer f, whose
  target w is a closure. A function with no target, `null` at ℓₜ, has no
  derivation. -/
  | callFn
      (he : ⟨ρ, σ⟩ ⊢ fe ⇒ .lib "std::function" [ℓₜ], σ₁)
      (ht : σ₁.read ℓₜ = some w)
      (ha : ApplyArgs p ρ σ₁ w es v σ') :
    -- ───────────────────────────────── (CallFn)
      ⟨ρ, σ⟩ ⊢ .callFn fe es ⇒ v, σ'

  /-- The closure holds values, copies taken at the lambda, read only. -/
  | lambda
      (hc : captures? ρ σ ps b = some cap) :
    -- ──────────────────────────────────────────────── (Lambda)
      ⟨ρ, σ⟩ ⊢ .lambda ps r b ⇒ .closure ps r b cap, σ

  /-- The location as a value, in the return of a member that returns a reference. -/
  | locOf
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ₗ ℓ, σ') :
    -- ────────────────────────────── (LocOf)
      ⟨ρ, σ⟩ ⊢ .locOf e ⇒ .loc ℓ, σ'

/-- ρ, σ ⊢ e ⇒ₗ ℓ, σ′ -/
inductive LEval (p : Program) : Env → Store → Expr → Loc → Store → Prop where
  | locVar
      (h : ρ.lookup x = some ℓ) :
    -- ───────────────────────── (LocVar)
      ⟨ρ, σ⟩ ⊢ .var x ⇒ₗ ℓ, σ

  /-- An unqualified field of `this`. -/
  | locVarField
      (h : ρ.lookup x = none)
      (ht : ρ.lookup "this" = some ℓₜ)
      (ho : σ.read ℓₜ = some (.obj c fs))
      (hf : fs.lookup x = some ℓ) :
    -- ─────────────────────────────────── (LocVarField)
      ⟨ρ, σ⟩ ⊢ .var x ⇒ₗ ℓ, σ

  /-- A `nullptr` has no derivation. -/
  | locDeref
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ .loc ℓ, σ') :
    -- ───────────────────────────── (LocDeref)
      ⟨ρ, σ⟩ ⊢ .deref e ⇒ₗ ℓ, σ'

  | locField
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ₗ ℓ, σ')
      (ho : σ'.read ℓ = some (.obj c fs))
      (hf : fs.lookup f = some ℓf) :
    -- ─────────────────────────────────── (LocField)
      ⟨ρ, σ⟩ ⊢ .field e f ⇒ₗ ℓf, σ'

  | locArrow
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ .loc ℓ, σ')
      (ho : σ'.read ℓ = some (.obj c fs))
      (hf : fs.lookup f = some ℓf) :
    -- ─────────────────────────────────── (LocArrow)
      ⟨ρ, σ⟩ ⊢ .arrow e f ⇒ₗ ℓf, σ'

  | methodLoc
      (h : CallMethod p ρ σ recv arrow m es static sig md (.loc ℓ) σ')
      (hr : md.retRef = true) :
    -- ──────────────────────────────────────────────────────────────── (MethodLoc)
      ⟨ρ, σ⟩ ⊢ .methodCall recv arrow m es static sig ⇒ₗ ℓ, σ'

  /-- The last premise is the relation `index` of the module of L. -/
  | locIndex
      (h₁ : ⟨ρ, σ⟩ ⊢ e ⇒ .lib L ls, σ₁)
      (h₂ : ⟨ρ, σ₁⟩ ⊢ i ⇒ v, σ₂)
      (hM : moduleOf L = some M)
      (hi : M.index (.lib L ls) v σ₂ ℓ σ₃) :
    -- ──────────────────────────────────── (LocIndex)
      ⟨ρ, σ⟩ ⊢ .index e i ⇒ₗ ℓ, σ₃

  | locCondT
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .bool true, σ₁)
      (h₂ : ⟨ρ, σ₁⟩ ⊢ e₂ ⇒ₗ ℓ, σ₂) :
    -- ──────────────────────────────── (LocCond-T)
      ⟨ρ, σ⟩ ⊢ .cond e₁ e₂ e₃ ⇒ₗ ℓ, σ₂

  | locCondF
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .bool false, σ₁)
      (h₃ : ⟨ρ, σ₁⟩ ⊢ e₃ ⇒ₗ ℓ, σ₂) :
    -- ──────────────────────────────── (LocCond-F)
      ⟨ρ, σ⟩ ⊢ .cond e₁ e₂ e₃ ⇒ₗ ℓ, σ₂

/-- ρ, σ ⊢ c ⇒ r, ρ′, σ′ -/
inductive Exec (p : Program) : Env → Store → Cmd → Ctrl → Env → Store → Prop where
  /-- The block discards the extension of ρ and frees the locations it allocated, fresh(ρ, ρ′), the owned bindings of ρ′ ∖ ρ. -/
  | block
      (h : ⟨ρ, σ⟩ ⊢ cs ⇒* r, ρ', σ') :
    -- ─────────────────────────────────────────────────── (Block)
      ⟨ρ, σ⟩ ⊢ .block cs ⇒ r, ρ, σ'.free (Env.fresh ρ ρ')

  | ifT
      (hc : ⟨ρ, σ⟩ ⊢ e ⇒ .bool true, σ₁)
      (h : ⟨ρ, σ₁⟩ ⊢ .block t ⇒ r, ρ, σ₂) :
    -- ─────────────────────────────────── (If-T)
      ⟨ρ, σ⟩ ⊢ .ite e t f ⇒ r, ρ, σ₂

  | ifF
      (hc : ⟨ρ, σ⟩ ⊢ e ⇒ .bool false, σ₁)
      (h : ⟨ρ, σ₁⟩ ⊢ .block f ⇒ r, ρ, σ₂) :
    -- ─────────────────────────────────── (If-F)
      ⟨ρ, σ⟩ ⊢ .ite e t f ⇒ r, ρ, σ₂

  | whileF
      (hc : ⟨ρ, σ⟩ ⊢ e ⇒ .bool false, σ₁) :
    -- ──────────────────────────────────── (While-F)
      ⟨ρ, σ⟩ ⊢ .while e b ⇒ .normal, ρ, σ₁

  /-- The divergence of `while (true) {}` has no derivation. -/
  | whileT
      (hc : ⟨ρ, σ⟩ ⊢ e ⇒ .bool true, σ₁)
      (hb : ⟨ρ, σ₁⟩ ⊢ .block b ⇒ .normal, ρ, σ₂)
      (hw : ⟨ρ, σ₂⟩ ⊢ .while e b ⇒ r, ρ, σ₃) :
    -- ────────────────────────────────────────── (While-T)
      ⟨ρ, σ⟩ ⊢ .while e b ⇒ r, ρ, σ₃

  /-- The return interrupts the loop. -/
  | whileRet
      (hc : ⟨ρ, σ⟩ ⊢ e ⇒ .bool true, σ₁)
      (hb : ⟨ρ, σ₁⟩ ⊢ .block b ⇒ .ret v, ρ, σ₂) :
    -- ───────────────────────────────────────── (While-Ret)
      ⟨ρ, σ⟩ ⊢ .while e b ⇒ .ret v, ρ, σ₂

  /-- The variable of c₀ has the loop as its scope, and the step runs after the body, outside the body's block. -/
  | forLoop
      (h₀ : ⟨ρ, σ⟩ ⊢ c₀ ⇒ .normal, ρ₀, σ₀)
      (hw : ⟨ρ₀, σ₀⟩ ⊢ .while e [.block b, cₛ] ⇒ r, ρ₀, σ₁) :
    -- ──────────────────────────────────────────────────────── (For)
      ⟨ρ, σ⟩ ⊢ .for c₀ e cₛ b ⇒ r, ρ, σ₁.free (Env.fresh ρ ρ₀)

  | retVoid :
    -- ───────────────────────────────────── (ReturnVoid)
      ⟨ρ, σ⟩ ⊢ .ret none ⇒ .ret .void, ρ, σ

  | ret
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ v, σ') :
    -- ────────────────────────────────────── (Return)
      ⟨ρ, σ⟩ ⊢ .ret (some e) ⇒ .ret v, ρ, σ'

  | decl
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ v, σ')
      (ha : σ'.alloc v = (ℓ, σ'')) :
    -- ───────────────────────────────────────────────── (Decl)
      ⟨ρ, σ⟩ ⊢ .decl τ x e ⇒ .normal, ρ.extend x ℓ, σ''

  /-- A second name for an existing location, the alias binding ρ[x ↦ₐ ℓ], not owned, so block exit leaves ℓ in σ. -/
  | declRef
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ₗ ℓ, σ') :
    -- ────────────────────────────────────────────────── (DeclRef)
      ⟨ρ, σ⟩ ⊢ .declRef τ x e ⇒ .normal, ρ.alias x ℓ, σ'

  /-- The rule Decl, with τ the type of v. -/
  | declAuto
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ v, σ')
      (ha : σ'.alloc v = (ℓ, σ'')) :
    -- ─────────────────────────────────────────────────── (Decl)
      ⟨ρ, σ⟩ ⊢ .declAuto x e ⇒ .normal, ρ.extend x ℓ, σ''

  /-- Right operand before left, the order C++17 fixes for assignment. -/
  | assign
      (hr : ⟨ρ, σ⟩ ⊢ e₂ ⇒ v, σ₁)
      (hl : ⟨ρ, σ₁⟩ ⊢ e₁ ⇒ₗ ℓ, σ₂)
      (hd : (σ₂.read ℓ).isSome) :
    -- ───────────────────────────────────────────────── (Assign)
      ⟨ρ, σ⟩ ⊢ .assign e₁ e₂ ⇒ .normal, ρ, σ₂.write ℓ v

  /-- The value is discarded. -/
  | exprStmt
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ v, σ') :
    -- ───────────────────────────────────── (ExprStmt)
      ⟨ρ, σ⟩ ⊢ .exprStmt e ⇒ .normal, ρ, σ'

  /-- As in C++, `delete nullptr` does nothing. -/
  | deleteNull
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ .null, σ') :
    -- ────────────────────────────────────────── (DeleteNull)
      ⟨ρ, σ⟩ ⊢ .delete e static ⇒ .normal, ρ, σ'

  /-- The last premise is the relation `delete` of the module of L. -/
  | deleteLib
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ .loc ℓ, σ₀)
      (ho : σ₀.read ℓ = some (.lib L ls))
      (hM : moduleOf L = some M)
      (hd : M.delete (.lib L ls) σ₀ σ₁) :
    -- ─────────────────────────────────────────────────── (DeleteLib)
      ⟨ρ, σ⟩ ⊢ .delete e static ⇒ .normal, ρ, σ₁.free [ℓ]

  /-- A second `delete` of ℓ, and a `delete` through a base pointer without a virtual destructor, have no derivation. -/
  | delete
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ .loc ℓ, σ₀)
      (ho : σ₀.read ℓ = some (.obj tag flds))
      (hv : static.getD tag = tag ∨ p.hasVirtualDtor (static.getD tag) = true)
      (hd : Dtors p ρ σ₀ ℓ (p.chain tag) σ₁) :
    -- ────────────────────────────────────────────────────────────────────── (Delete)
      ⟨ρ, σ⟩ ⊢ .delete e static ⇒ .normal, ρ, σ₁.free (ℓ :: flds.map (·.2))

/-- ρ, σ ⊢ c₁ … cₙ ⇒ r, ρ′, σ′, a sequence of commands. -/
inductive Execs (p : Program) : Env → Store → List Cmd → Ctrl → Env → Store → Prop where
  | nil :
    -- ──────────────────────────── (Seq-Empty)
      ⟨ρ, σ⟩ ⊢ [] ⇒* .normal, ρ, σ

  /-- The environment ρ₁ carries the binding of c to the rest. -/
  | cons
      (h : ⟨ρ, σ⟩ ⊢ c ⇒ .normal, ρ₁, σ₁)
      (hs : ⟨ρ₁, σ₁⟩ ⊢ cs ⇒* r, ρ₂, σ₂) :
    -- ────────────────────────────────── (Seq)
      ⟨ρ, σ⟩ ⊢ c :: cs ⇒* r, ρ₂, σ₂

  /-- The return interrupts the sequence. -/
  | consRet
      (h : ⟨ρ, σ⟩ ⊢ c ⇒ .ret v, ρ₁, σ₁) :
    -- ────────────────────────────────── (Seq-Ret)
      ⟨ρ, σ⟩ ⊢ c :: cs ⇒* .ret v, ρ₁, σ₁

/-- The values of arguments, left to right. -/
inductive Args (p : Program) : Env → Store → List Expr → List Val → Store → Prop where
  | nil :
    -- ────────────────────
      Args p ρ σ [] [] σ

  | cons
      (h : ⟨ρ, σ⟩ ⊢ e ⇒ v, σ₁)
      (hs : Args p ρ σ₁ es vs σ₂) :
    -- ─────────────────────────────────
      Args p ρ σ (e :: es) (v :: vs) σ₂

/-- The binding of parameters to arguments, left to right, from an initial
environment ρ₀. A by value parameter gets a fresh location with a copy of the
argument, owned, and a reference parameter is bound to the location of its
argument. The result lists the owned locations. -/
inductive Bind (p : Program) : Env → Store → Env → List Param → List Expr → Env → Store → List Loc → Prop where
  | nil :
    -- ───────────────────────────
      Bind p ρ σ ρ₀ [] [] ρ₀ σ []

  | byRef
      (hq : q.byRef = true)
      (hl : ⟨ρ, σ⟩ ⊢ a ⇒ₗ ℓ, σ₁)
      (hs : Bind p ρ σ₁ (ρ₀.alias q.name ℓ) qs es ρ' σ' owned) :
    -- ────────────────────────────────────────────────────────
      Bind p ρ σ ρ₀ (q :: qs) (a :: es) ρ' σ' owned

  | byVal
      (hq : q.byRef = false)
      (hv : ⟨ρ, σ⟩ ⊢ a ⇒ v, σ₁)
      (ha : σ₁.alloc v = (ℓ, σ₂))
      (hs : Bind p ρ σ₂ (ρ₀.extend q.name ℓ) qs es ρ' σ' owned) :
    -- ─────────────────────────────────────────────────────────
      Bind p ρ σ ρ₀ (q :: qs) (a :: es) ρ' σ' (ℓ :: owned)

/-- The call of a member body, a method, a constructor or a destructor, with
`this` bound to the location ℓ of the receiver. -/
inductive Member (p : Program) : Env → Store → Loc → List Param → List Cmd → List Expr → Ty → Val → Store → Prop where
  | member
      (hn : ps.length = es.length)
      (hb : Bind p ρ σ (Env.alias [] "this" ℓ) ps es ρm σ₁ owned)
      (hx : ⟨ρm, σ₁⟩ ⊢ body ⇒* r, ρ', σ₂)
      (hr : Returns r ret v) :
    -- ──────────────────────────────────────────────────────────────────── (Member)
      Member p ρ σ ℓ ps body es ret v (σ₂.free (owned ++ Env.fresh ρm ρ'))

/-- The receiver, the dispatch and the call of a method m. The receiver of
`e.m(ē)` is the location e denotes and the receiver of `e->m(ē)` the location
e points to. The method is the one nearest the static class S in the chain, or
nearest the tag T of the object when that method is virtual, so a call through
a base pointer reaches the override. -/
inductive CallMethod (p : Program) :
    Env → Store → Expr → Bool → String → List Expr → Option String → Option (List Ty) → Method → Val → Store → Prop where
  | dot
      (hl : ⟨ρ, σ⟩ ⊢ recv ⇒ₗ ℓ, σ₀)
      (ho : σ₀.read ℓ = some (.obj tag flds))
      (hm : p.resolve (static.getD tag) tag m sig = some (md, k))
      (hc : Member p ρ σ₀ ℓ md.params md.body es md.ret v σ') :
    -- ───────────────────────────────────────────────────────────
      CallMethod p ρ σ recv false m es static sig md v σ'

  | arrow
      (hv : ⟨ρ, σ⟩ ⊢ recv ⇒ .loc ℓ, σ₀)
      (ho : σ₀.read ℓ = some (.obj tag flds))
      (hm : p.resolve (static.getD tag) tag m sig = some (md, k))
      (hc : Member p ρ σ₀ ℓ md.params md.body es md.ret v σ') :
    -- ───────────────────────────────────────────────────────────
      CallMethod p ρ σ recv true m es static sig md v σ'

/-- The constructors of a chain of classes, run in the order of the list with
`this` bound to ℓ. The constructor of the class c being created receives the
arguments, the others none. -/
inductive Ctors (p : Program) : Env → Store → Loc → String → List ClassDecl → List Expr → Store → Prop where
  | nil :
    -- ───────────────────────
      Ctors p ρ σ ℓ c [] es σ

  | skip
      (hk : cd.ctor = none)
      (hs : Ctors p ρ σ ℓ c cds es σ') :
    -- ─────────────────────────────────
      Ctors p ρ σ ℓ c (cd :: cds) es σ'

  | run
      (hk : cd.ctor = some k)
      (hm : Member p ρ σ ℓ k.params k.body (if cd.name == c then es else []) .void v σ₁)
      (hs : Ctors p ρ σ₁ ℓ c cds es σ') :
    -- ──────────────────────────────────────────────────────────────────────
      Ctors p ρ σ ℓ c (cd :: cds) es σ'

/-- The destructors of a chain of classes, run in the order of the list with
`this` bound to ℓ. -/
inductive Dtors (p : Program) : Env → Store → Loc → List ClassDecl → Store → Prop where
  | nil :
    -- ────────────────────
      Dtors p ρ σ ℓ [] σ

  | skip
      (hd : cd.dtor = none)
      (hs : Dtors p ρ σ ℓ cds σ') :
    -- ────────────────────────────
      Dtors p ρ σ ℓ (cd :: cds) σ'

  | run
      (hd : cd.dtor = some d)
      (hm : Member p ρ σ ℓ [] d.body [] .void v σ₁)
      (hs : Dtors p ρ σ₁ ℓ cds σ') :
    -- ─────────────────────────────────────────────
      Dtors p ρ σ ℓ (cd :: cds) σ'

/-- The application of a closure to values. The environment ρ_c holds the captured
copies and the parameters, and nothing else is visible. On the way out the
copies, the parameters and the locals leave the store. -/
inductive Apply (p : Program) : Store → Val → List Val → Val → Store → Prop where
  | apply
      (hn : ps.length = vs.length)
      (ha : σ.allocMany (cap.map (·.2) ++ vs) = (ls, σ₁))
      (hρ : ρc = Env.extendAll [] (cap.map (·.1) ++ ps.map (·.name)) ls)
      (hx : ⟨ρc, σ₁⟩ ⊢ b ⇒* r, ρ'', σ₂)
      (hr : Returns r τ v) :
    -- ────────────────────────────────────────────────────────────────────── (Apply)
      Apply p σ (.closure ps τ b cap) vs v (σ₂.free (ls ++ Env.fresh ρc ρ''))

/-- The application of a closure to argument expressions, evaluated left to right,
by value. A value that is not a closure has no derivation. -/
inductive ApplyArgs (p : Program) : Env → Store → Val → List Expr → Val → Store → Prop where
  | applyArgs
      (hc : w = .closure ps τ b cap)
      (hn : ps.length = es.length)
      (ha : Args p ρ σ es vs σ₁)
      (hap : Apply p σ₁ w vs v σ') :
    -- ──────────────────────────────
      ApplyArgs p ρ σ w es v σ'

end

/-- p ⇒ v, the execution of a program. The initial store is empty, since there
are no global variables, and the result is the value `main()` returns.
```
[], ∅ ⊢ main() ⇒ v, σ
───────────────────── (Program)
p ⇒ v
``` -/
def Runs (p : Program) (v : Val) : Prop := ∃ σ, (⟨[], {}⟩ ⊢ .call "main" [] none ⇒ v, σ)

end Semantics

end CoreCpp
