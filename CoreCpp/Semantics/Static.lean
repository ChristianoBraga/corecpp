import CoreCpp.Typing
import CoreCpp.Semantics.Library

/-!
# The static semantics of Core C++, as relations

One inductive proposition per judgement, one constructor per rule, named as
in the blueprint.

| Judgement | Relation | Meaning |
| --- | --- | --- |
| Γ ⊢ e : τ | `HasType p Γ e τ` | e has the type τ |
| Γ ⊢ₗ e : τ | `LHasType p Γ e τ` | e denotes a location of type τ |
| Γ ⊢ e ◁ τ | `Accept p Γ e τ` | e is acceptable where τ is expected |
| Γ ⊢ c ⊣ Γ′ | `Check p τᵣ Γ c Γ′` | c is well typed under the result type τᵣ |
| Γ ⊢ c̄ ⊣ Γ′ | `Checks p τᵣ Γ c̄ Γ′` | the sequence c̄ is well typed |

The program p is a parameter of every relation. The auxiliaries `CheckArgs`,
`AcceptArgs` and `MethodSel` name shared premises, and `WF`, `FunOk`,
`ClassOk` and `ProgramOk` are the judgements on types and declarations.

The relation is the specification and `CoreCpp.Typing` the implementation.
An ill typed program has no derivation. The subject is the program as
`Typing.annotate` leaves it, with the signature of the overload a call
selects filled in. Choosing that overload, rule T-Overload, is the work of
the type checker, and the relation reads its result, so a call without a
signature has a derivation only when its name has one overload.
A `std::function<F>` is an object, created with `new std::function<F>(λ)`,
where the lambda is acceptable at its function type F, reached by pointer and
called as `(*f)(ē)`, rule T-CallFn. A subject of the library is judged by the
static relations of its module in `CoreCpp.Semantics.Library`, the premises
of T-NewLib, T-IndexLib, T-LocIndexLib, T-DeleteLib and T-CallLib.
-/

namespace CoreCpp.Semantics

/-! ## Notation

The judgements as the rules write them.

| Judgement | Notation | Expands to |
| --- | --- | --- |
| Γ ⊢ e : τ | `Γ ⊢ e : τ` | `HasType p Γ e τ` |
| Γ ⊢ₗ e : τ | `Γ ⊢ₗ e : τ` | `LHasType p Γ e τ` |
| Γ ⊢ e ◁ τ | `Γ ⊢ e ◁ τ` | `Accept p Γ e τ` |
| Γ ⊢ c ⊣ Γ′ under τᵣ | `⟨Γ, τᵣ⟩ ⊢ c ⊣ Γ'` | `Check p τᵣ Γ c Γ'` |
| Γ ⊢ c̄ ⊣ Γ′ under τᵣ | `⟨Γ, τᵣ⟩ ⊢ cs ⊣* Γ'` | `Checks p τᵣ Γ cs Γ'` |

The result type τᵣ of the enclosing body joins Γ in angle brackets, since a
notation that starts with a bare term and a comma would clash with the tuples
of Lean, and the program is left out, the `p` in scope, the parameter of the
relations. A sequence of commands takes `⊣*`. The notation is declared before
the relations and with `hygiene false`, so that `p` and the names of the
relations resolve at the use site, the latter to the relations under
definition inside the `mutual` block. -/

set_option hygiene false in
set_option quotPrecheck false in
scoped notation:40 Γ:41 " ⊢ " e:41 " : " τ:41 => HasType p Γ e τ

set_option hygiene false in
set_option quotPrecheck false in
scoped notation:40 Γ:41 " ⊢ₗ " e:41 " : " τ:41 => LHasType p Γ e τ

set_option hygiene false in
set_option quotPrecheck false in
scoped notation:40 Γ:41 " ⊢ " e:41 " ◁ " τ:41 => Accept p Γ e τ

set_option hygiene false in
set_option quotPrecheck false in
scoped notation:40 "⟨" Γ:41 ", " τᵣ:41 "⟩" " ⊢ " c:41 " ⊣ " Γ':41 => Check p τᵣ Γ c Γ'

set_option hygiene false in
set_option quotPrecheck false in
scoped notation:40 "⟨" Γ:41 ", " τᵣ:41 "⟩" " ⊢ " cs:41 " ⊣* " Γ':41 => Checks p τᵣ Γ cs Γ'

end CoreCpp.Semantics

namespace CoreCpp

/-- The type of `e₁ ? e₂ : e₃` from the types of its branches, the common one,
or the one the other converts to. -/
def Ty.join (p : Program) (t₂ t₃ : Ty) : Option Ty :=
  if t₂ == t₃ then some t₂
  else if Typing.compat p t₂ t₃ then some t₃
  else if Typing.compat p t₃ t₂ then some t₂
  else none

/-- The operands of `==` and `!=`, two related types among `int`, `bool`,
pointer types and `nullptr_t`. -/
def Ty.comparable (p : Program) (t₁ t₂ : Ty) : Bool :=
  Typing.related p t₁ t₂ && t₁ != .void && !(t₁ matches .cls _ | .lib .. | .fn ..)

def BinOp.isLogical : BinOp → Bool
  | .and | .or => true
  | _ => false

def BinOp.isArithmetic : BinOp → Bool
  | .add | .sub | .mul | .div | .mod => true
  | _ => false

def BinOp.isEquality : BinOp → Bool
  | .eq | .ne => true
  | _ => false

def BinOp.isRelational : BinOp → Bool
  | .lt | .le | .gt | .ge => true
  | _ => false

def Expr.isLambda : Expr → Bool
  | .lambda .. => true
  | _ => false

/-- Two declarations of one name are overloads when they differ in arity or in
a parameter of a type other than `std::function`, so that a lambda argument
never decides a call. -/
def Param.distinguishable (ps qs : List Param) : Bool :=
  ps.length != qs.length ||
    (ps.zip qs).any fun (a, b) => a.ty != b.ty && !a.ty.isFunction && !b.ty.isFunction

/-- The function a call of f selects, the one with the signature the type
checker filled in, or the only one of the name when none is filled in. -/
def Program.pickFun (p : Program) (f : String) (sig : Option (List Ty)) : Option Fun :=
  match sig with
  | some s => (p.funsNamed f).find? fun g => sigOf g.params == s
  | none => match p.funsNamed f with | [g] => some g | _ => none

/-- The method m of class c a call selects, with the class that declares it,
the one with the signature the type checker filled in, or the only one of the
name when none is filled in. -/
def Program.pickMethod (p : Program) (c m : String) (sig : Option (List Ty)) : Option (Method × String) :=
  match sig with
  | some s => (p.findMethods c m).find? fun (md, _) => sigOf md.params == s
  | none => match p.findMethods c m with | [x] => some x | _ => none

/-- The type of the field f of class c as seen from Γ. A private field is
visible only when Γ(this) is the class that declares it. -/
def Program.visibleField (p : Program) (Γ : TEnv) (c f : String) : Option Ty :=
  match p.findField c f with
  | some (fd, k) => if fd.vis == .pub || Γ.self == some k then some fd.ty else none
  | none => none

/-- The method m of class c that a method of a derived class with the
parameters ps redefines, if any. -/
def Program.inherited (p : Program) (c : ClassDecl) (m : String) (ps : List Param) : Option (Method × String) :=
  c.base.bind fun b => (p.findMethods b m).find? fun (bm, _) => sigOf bm.params == sigOf ps

/-- The chain of c has no cycle and ends at a class without a base. -/
def Program.chainAcyclic (p : Program) (c : String) : Bool :=
  let chain := p.chain c
  !chain.isEmpty && (chain.map (·.name)).eraseDups.length == chain.length
    && (chain.getLast?.bind (·.base)).isNone

/-- Γ[x₁ ↦ τ₁]…[xₖ ↦ τₖ], the parameters as variables. -/
def TEnv.bindParams (Γ : TEnv) (ps : List Param) : TEnv :=
  ps.reverse.foldl (fun Γ q => Γ.bind q.name q.ty) Γ

/-- The context of a function body, its parameters alone. -/
def TEnv.ofParams (ps : List Param) : TEnv := TEnv.bindParams [] ps

namespace Semantics

/-- An object type, a class or an entity of the library created with `new`.
Its values live in σ and are reached by pointer or by reference. -/
def IsObject : Ty → Prop
  | .cls _ => True
  | .lib L ts => ∃ S, staticOf L = some S ∧ ∃ ps r, S.new ts ps r
  | _ => False

/-- A type with values, neither `void` nor an object type. -/
def HasValues (τ : Ty) : Prop := τ ≠ .void ∧ ¬ IsObject τ

/-- A type a variable, a parameter or a result may have. -/
def Storable (τ : Ty) : Prop := ¬ IsObject τ ∧ τ ≠ .nullT ∧ ¬ τ.isFn

/-- A type a binding may have, an object type included when the binding is a
reference. -/
def Bindable (byRef : Bool) (τ : Ty) : Prop := (byRef = true ∧ IsObject τ) ∨ Storable τ

/-- Γ ⊢ τ ok, the type names declared classes and declared entities of the
library, an instance of the library is well formed by its module, and a
function type has a storable or `void` result and storable parameters. -/
inductive WF (p : Program) : Ty → Prop where
  | int :
    -- ──────── (WF-Int)
      WF p .int

  | bool :
    -- ───────── (WF-Bool)
      WF p .bool

  | void :
    -- ───────── (WF-Void)
      WF p .void

  | nullT :
    -- ────────── (WF-Null)
      WF p .nullT

  | cls
      (h : (p.lookupClass c).isSome) :
    -- ──────────── (WF-Class)
      WF p (.cls c)

  | ptr
      (h : WF p t) :
    -- ──────────── (WF-Ptr)
      WF p (.ptr t)

  | lib
      (hd : (L, ts.length) ∈ p.libDecls)
      (hS : staticOf L = some S)
      (hw : S.wf ts)
      (hts : ∀ t ∈ ts, WF p t) :
    -- ─────────────── (WF-Lib)
      WF p (.lib L ts)

  | fn
      (hr : r = .void ∨ Storable r)
      (hwr : WF p r)
      (hps : ∀ t ∈ ps, Storable t)
      (hwps : ∀ t ∈ ps, WF p t) :
    -- ─────────────── (WF-Fn)
      WF p (.fn r ps)

mutual

/-- Γ ⊢ e : τ -/
inductive HasType (p : Program) : TEnv → Expr → Ty → Prop where
  | lit :
    -- ──────────────────── (T-Lit)
      Γ ⊢ .intLit n : .int

  | boolLit :
    -- ────────────────────── (T-BoolLit)
      Γ ⊢ .boolLit b : .bool

  | null :
    -- ───────────────────── (T-Null)
      Γ ⊢ .nullptr : .nullT

  | var
      (h : Γ.lookup x = some τ) :
    -- ───────────────── (T-Var)
      Γ ⊢ .var x : τ

  /-- An unqualified field of `this`, inside a member body. -/
  | varField
      (h : Γ.lookup x = none)
      (hs : Γ.self = some c)
      (hf : p.visibleField Γ c x = some τ) :
    -- ───────────────── (T-VarField)
      Γ ⊢ .var x : τ

  /-- Only inside a method, a constructor or a destructor. -/
  | this
      (h : Γ.lookup "this" = some τ) :
    -- ──────────────── (T-This)
      Γ ⊢ .this : τ

  | not
      (h : Γ ⊢ e : .bool) :
    -- ───────────────────────── (T-Not)
      Γ ⊢ .unop .not e : .bool

  | neg
      (h : Γ ⊢ e : .int) :
    -- ──────────────────────── (T-Neg)
      Γ ⊢ .unop .neg e : .int

  | logic
      (hop : op.isLogical)
      (h₁ : Γ ⊢ e₁ : .bool)
      (h₂ : Γ ⊢ e₂ : .bool) :
    -- ───────────────────────────── (T-Logic)   ⊙ ∈ {&&, ||}
      Γ ⊢ .binop op e₁ e₂ : .bool

  /-- The left operand decides, so no operator on `int` or `bool` changes
  meaning, and `&&` and `||` are not overloaded. -/
  | opBin
      (hop : op.isLogical = false)
      (h₁ : Γ ⊢ e₁ : .cls c)
      (hm : Γ ⊢ .methodCall e₁ false ("operator" ++ op.toString) [e₂] none none : τ) :
    -- ───────────────────────────────────────────────────────────────────── (T-OpBin)
      Γ ⊢ .binop op e₁ e₂ : τ

  | arith
      (hop : op.isArithmetic)
      (h₁ : Γ ⊢ e₁ : .int)
      (h₂ : Γ ⊢ e₂ : .int) :
    -- ───────────────────────────── (T-Arith)   ⊕ ∈ {+, −, ×, /, %}
      Γ ⊢ .binop op e₁ e₂ : .int

  | eq
      (hop : op.isEquality)
      (h₁ : Γ ⊢ e₁ : τ₁)
      (h₂ : Γ ⊢ e₂ : τ₂)
      (hc : Ty.comparable p τ₁ τ₂) :
    -- ───────────────────────────── (T-Eq)   ⋈ ∈ {==, !=}
      Γ ⊢ .binop op e₁ e₂ : .bool

  | rel
      (hop : op.isRelational)
      (h₁ : Γ ⊢ e₁ : .int)
      (h₂ : Γ ⊢ e₂ : .int) :
    -- ───────────────────────────── (T-Rel)   ⋈ ∈ {<, <=, >, >=}
      Γ ⊢ .binop op e₁ e₂ : .bool

  | cond
      (h₁ : Γ ⊢ e₁ : .bool)
      (h₂ : Γ ⊢ e₂ : τ₂)
      (hv₂ : HasValues τ₂)
      (h₃ : Γ ⊢ e₃ : τ₃)
      (hv₃ : HasValues τ₃)
      (hj : Ty.join p τ₂ τ₃ = some τ) :
    -- ─────────────────────────── (T-Cond)
      Γ ⊢ .cond e₁ e₂ e₃ : τ

  /-- Two branches that denote objects of one type, as C++ makes the
  conditional an lvalue (N4659 §8.16 ¶4). -/
  | condObj
      (h : Γ ⊢ₗ .cond e₁ e₂ e₃ : τ)
      (ho : IsObject τ) :
    -- ─────────────────────────── (T-CondObj)
      Γ ⊢ .cond e₁ e₂ e₃ : τ

  /-- A variable f of a `std::function` type, a reference parameter, hides
  the function named f. -/
  | callVar
      (h : Γ.lookup f = some (Ty.function τ ps))
      (ha : AcceptArgs p Γ ps es) :
    -- ───────────────────────── (T-CallFn)
      Γ ⊢ .call f es sig : τ

  /-- See `Program.pickFun`. The uniqueness of the candidate, rule T-Overload,
  is the work of the type checker. -/
  | call
      (hρ : Γ.lookup f = none)
      (hf : p.pickFun f sig = some fn)
      (hn : fn.params.length = es.length)
      (ha : CheckArgs p Γ fn.params es) :
    -- ───────────────────────────── (T-Call)
      Γ ⊢ .call f es sig : fn.ret

  /-- The last premise but one is the relation `call` of the module of f. -/
  | callLib
      (hρ : Γ.lookup f = none)
      (hf : p.funsNamed f = [])
      (hd : (f, es.length) ∈ p.libDecls)
      (hS : staticOf f = some S)
      (hc : S.call ps τ)
      (ha : AcceptArgs p Γ ps es) :
    -- ───────────────────────── (T-CallLib)
      Γ ⊢ .call f es sig : τ

  /-- An unqualified method name inside a member body. -/
  | callThis
      (hρ : Γ.lookup f = none)
      (hf : p.funsNamed f = [])
      (hs : Γ.self = some c)
      (hm : p.findMethods c f ≠ [])
      (h : Γ ⊢ .methodCall .this true f es none none : τ) :
    -- ───────────────────────── (T-CallThis)
      Γ ⊢ .call f es sig : τ

  | callFn
      (h : Γ ⊢ fe : Ty.function τ ps)
      (ha : AcceptArgs p Γ ps es) :
    -- ─────────────────────── (T-CallFn)
      Γ ⊢ .callFn fe es : τ

  /-- The annotation of the `return` of a member that returns a reference. -/
  | locOf
      (h : Γ ⊢ₗ e : τ) :
    -- ───────────────── (T-LocOf)
      Γ ⊢ .locOf e : τ

  /-- A class without a constructor is created by `new C()` alone. -/
  | newNoCtor
      (hc : p.lookupClass c = some cd)
      (hk : cd.ctor = none) :
    -- ───────────────────────────── (T-New)
      Γ ⊢ .newObj c [] : .ptr (.cls c)

  | new
      (hc : p.lookupClass c = some cd)
      (hk : cd.ctor = some k)
      (hn : k.params.length = es.length)
      (ha : CheckArgs p Γ k.params es) :
    -- ───────────────────────────── (T-New)
      Γ ⊢ .newObj c es : .ptr (.cls c)

  /-- See `MethodSel`, the rules T-Method and T-MethodArrow. -/
  | method
      (h : MethodSel p Γ recv arrow m es sig md k) :
    -- ─────────────────────────────────────────────────── (T-Method)
      Γ ⊢ .methodCall recv arrow m es static sig : md.ret

  /-- The second premise is the relation `new` of the module of L. -/
  | newLib
      (hw : WF p (.lib L ts))
      (hS : staticOf L = some S)
      (hn : S.new ts ps τ)
      (ha : AcceptArgs p Γ ps es) :
    -- ───────────────────────────────── (T-NewLib)
      Γ ⊢ .newLib (.lib L ts) es : τ

  | field
      (h : Γ ⊢ e : .cls c)
      (hf : p.visibleField Γ c f = some τ) :
    -- ───────────────────── (T-Field)
      Γ ⊢ .field e f : τ

  | arrow
      (h : Γ ⊢ e : .ptr (.cls c))
      (hf : p.visibleField Γ c f = some τ) :
    -- ───────────────────── (T-Arrow)
      Γ ⊢ .arrow e f : τ

  | deref
      (h : Γ ⊢ e : .ptr τ) :
    -- ───────────────── (T-Deref)
      Γ ⊢ .deref e : τ

  /-- The second premise is the relation `index` of the module of L. -/
  | indexLib
      (h : Γ ⊢ e : .lib L ts)
      (hS : staticOf L = some S)
      (hi : S.index ts τ₁ τ)
      (ha : Γ ⊢ i ◁ τ₁) :
    -- ───────────────────── (T-IndexLib)
      Γ ⊢ .index e i : τ

  | opIndex
      (h : Γ ⊢ e : .cls c)
      (hm : Γ ⊢ .methodCall e false "operator[]" [i] none none : τ) :
    -- ───────────────────── (T-OpIndex)
      Γ ⊢ .index e i : τ

/-- Γ ⊢ₗ e : τ, the expressions that denote a location, with their type. A
variable captured by copy inside a lambda denotes no writable location. -/
inductive LHasType (p : Program) : TEnv → Expr → Ty → Prop where
  | locVar
      (h : Γ.lookup x = some τ)
      (hc : Γ.isConst x = false) :
    -- ────────────────── (T-LocVar)
      Γ ⊢ₗ .var x : τ

  | locVarField
      (h : Γ.lookup x = none)
      (hs : Γ.self = some c)
      (hf : p.visibleField Γ c x = some τ) :
    -- ────────────────── (T-LocVarField)
      Γ ⊢ₗ .var x : τ

  | locDeref
      (h : Γ ⊢ e : .ptr τ) :
    -- ────────────────── (T-LocDeref)
      Γ ⊢ₗ .deref e : τ

  | locField
      (h : Γ ⊢ e : .cls c)
      (hf : p.visibleField Γ c f = some τ) :
    -- ────────────────────── (T-LocField)
      Γ ⊢ₗ .field e f : τ

  | locArrow
      (h : Γ ⊢ e : .ptr (.cls c))
      (hf : p.visibleField Γ c f = some τ) :
    -- ────────────────────── (T-LocArrow)
      Γ ⊢ₗ .arrow e f : τ

  /-- The second premise is the relation `index` of the module of L, whose
  result is a location. -/
  | locIndexLib
      (h : Γ ⊢ e : .lib L ts)
      (hS : staticOf L = some S)
      (hi : S.index ts τ₁ τ)
      (ha : Γ ⊢ i ◁ τ₁) :
    -- ────────────────────── (T-LocIndexLib)
      Γ ⊢ₗ .index e i : τ

  /-- Indexing an object denotes a location exactly when `operator[]` returns
  a reference. -/
  | locOpIndex
      (h : Γ ⊢ e : .cls c)
      (hm : MethodSel p Γ e false "operator[]" [i] none md k)
      (hr : md.retRef = true) :
    -- ─────────────────────────── (T-LocOpIndex)
      Γ ⊢ₗ .index e i : md.ret

  /-- A member call denotes a location exactly when the member returns a
  reference. -/
  | locMethod
      (hm : MethodSel p Γ recv arrow m es sig md k)
      (hr : md.retRef = true) :
    -- ──────────────────────────────────────────────────── (T-LocMethod)
      Γ ⊢ₗ .methodCall recv arrow m es static sig : md.ret

  /-- Two branches that denote locations of one type, an lvalue in C++
  (N4659 §8.16 ¶4). -/
  | locCond
      (h₁ : Γ ⊢ e₁ : .bool)
      (h₂ : Γ ⊢ₗ e₂ : τ)
      (h₃ : Γ ⊢ₗ e₃ : τ) :
    -- ─────────────────────────── (T-LocCond)
      Γ ⊢ₗ .cond e₁ e₂ e₃ : τ

/-- Γ ⊢ e ◁ τ, e is acceptable where τ is expected. -/
inductive Accept (p : Program) : TEnv → Expr → Ty → Prop where
  /-- Any expression but a lambda, by its type. -/
  | accept
      (hl : e.isLambda = false)
      (h : Γ ⊢ e : τ')
      (hv : HasValues τ')
      (hc : Typing.compat p τ' τ) :
    -- ─────────── (Accept)
      Γ ⊢ e ◁ τ

  /-- A lambda is acceptable at its function type, the argument of
  `new std::function<F>(λ)`. The body is checked under Γ with every variable
  of the enclosing scope marked read only, the copies of `[=]`, and with the
  parameters of the lambda as ordinary variables. -/
  | lambda
      (hr : r = .void ∨ Storable r)
      (hwr : WF p r)
      (hps : ∀ q ∈ ps, Storable q.ty)
      (hwps : ∀ q ∈ ps, WF p q.ty)
      (hb : ⟨Γ.captured.bindParams ps, r⟩ ⊢ b ⊣* Γ') :
    -- ───────────────────────────────────────────────────── (T-Lambda)
      Γ ⊢ .lambda ps r b ◁ .fn r (ps.map (·.ty))

/-- The arguments of a call against its parameters, by value with ◁ and by
reference with ⊢ₗ, shared by T-Call, T-New and T-Method. -/
inductive CheckArgs (p : Program) : TEnv → List Param → List Expr → Prop where
  | nil :
    -- ───────────────────
      CheckArgs p Γ [] []

  | byRef
      (hq : q.byRef = true)
      (h : Γ ⊢ₗ e : q.ty)
      (hs : CheckArgs p Γ qs es) :
    -- ──────────────────────────────────
      CheckArgs p Γ (q :: qs) (e :: es)

  | byVal
      (hq : q.byRef = false)
      (h : Γ ⊢ e ◁ q.ty)
      (hs : CheckArgs p Γ qs es) :
    -- ──────────────────────────────────
      CheckArgs p Γ (q :: qs) (e :: es)

/-- The arguments of a use of the library against the parameter types of its
signature, each by ◁. -/
inductive AcceptArgs (p : Program) : TEnv → List Ty → List Expr → Prop where
  | nil :
    -- ────────────────────
      AcceptArgs p Γ [] []

  | cons
      (h : Γ ⊢ e ◁ τ)
      (hs : AcceptArgs p Γ τs es) :
    -- ───────────────────────────────────
      AcceptArgs p Γ (τ :: τs) (e :: es)

/-- The method m that `e.m(ē)` or `e->m(ē)` selects, with the class k that
declares it. The receiver has class type for `.` and pointer to class type
for `->`, the method is the one the signature names, see `Program.pickMethod`,
it accepts the arguments, and a private method is visible only when Γ(this) is
the class that declares it. -/
inductive MethodSel (p : Program) :
    TEnv → Expr → Bool → String → List Expr → Option (List Ty) → Method → String → Prop where
  | dot
      (h : Γ ⊢ recv : .cls c)
      (hm : p.pickMethod c m sig = some (md, k))
      (hn : md.params.length = es.length)
      (ha : CheckArgs p Γ md.params es)
      (hv : md.vis = .priv → Γ.self = some k) :
    -- ───────────────────────────────────────── (T-Method)
      MethodSel p Γ recv false m es sig md k

  | arrow
      (h : Γ ⊢ recv : .ptr (.cls c))
      (hm : p.pickMethod c m sig = some (md, k))
      (hn : md.params.length = es.length)
      (ha : CheckArgs p Γ md.params es)
      (hv : md.vis = .priv → Γ.self = some k) :
    -- ───────────────────────────────────────── (T-MethodArrow)
      MethodSel p Γ recv true m es sig md k

/-- Γ ⊢ c ⊣ Γ′, under the result type τᵣ of the enclosing body. -/
inductive Check (p : Program) : Ty → TEnv → Cmd → TEnv → Prop where
  /-- The block discards Γ′. -/
  | block
      (h : ⟨Γ, τᵣ⟩ ⊢ cs ⊣* Γ') :
    -- ──────────────────────────── (T-Block)
      ⟨Γ, τᵣ⟩ ⊢ .block cs ⊣ Γ

  | ite
      (he : Γ ⊢ e : .bool)
      (ht : ⟨Γ, τᵣ⟩ ⊢ .block t ⊣ Γ)
      (hf : ⟨Γ, τᵣ⟩ ⊢ .block f ⊣ Γ) :
    -- ──────────────────────────── (T-If)
      ⟨Γ, τᵣ⟩ ⊢ .ite e t f ⊣ Γ

  | while
      (he : Γ ⊢ e : .bool)
      (hb : ⟨Γ, τᵣ⟩ ⊢ .block b ⊣ Γ) :
    -- ──────────────────────────── (T-While)
      ⟨Γ, τᵣ⟩ ⊢ .while e b ⊣ Γ

  | forLoop
      (h₀ : ⟨Γ, τᵣ⟩ ⊢ c₀ ⊣ Γ₀)
      (he : Γ₀ ⊢ e : .bool)
      (hs : ⟨Γ₀, τᵣ⟩ ⊢ cₛ ⊣ Γₛ)
      (hb : ⟨Γ₀, τᵣ⟩ ⊢ .block b ⊣ Γ₀) :
    -- ──────────────────────────────── (T-For)
      ⟨Γ, τᵣ⟩ ⊢ .for c₀ e cₛ b ⊣ Γ

  | retVoid :
    -- ──────────────────────────── (T-RetVoid)
      ⟨Γ, .void⟩ ⊢ .ret none ⊣ Γ

  | ret
      (hv : τᵣ ≠ .void)
      (h : Γ ⊢ e ◁ τᵣ) :
    -- ──────────────────────────── (T-Ret)
      ⟨Γ, τᵣ⟩ ⊢ .ret (some e) ⊣ Γ

  /-- Γ[x ↦ τ] reaches the following commands. -/
  | decl
      (hs : Storable τ)
      (hw : WF p τ)
      (h : Γ ⊢ e ◁ τ) :
    -- ──────────────────────────────────── (T-Decl)
      ⟨Γ, τᵣ⟩ ⊢ .decl τ x e ⊣ Γ.bind x τ

  /-- The initialiser denotes a location, and x has the type of its
  referent. -/
  | declRef
      (hb : Bindable true τ)
      (hw : WF p τ)
      (h : Γ ⊢ₗ e : τ) :
    -- ─────────────────────────────────────── (T-DeclRef)
      ⟨Γ, τᵣ⟩ ⊢ .declRef τ x e ⊣ Γ.bind x τ

  /-- A lambda has no type for `auto` to copy. -/
  | declAuto
      (h : Γ ⊢ e : τ)
      (hv : HasValues τ)
      (hs : Storable τ) :
    -- ──────────────────────────────────── (T-Auto)
      ⟨Γ, τᵣ⟩ ⊢ .declAuto x e ⊣ Γ.bind x τ

  | assign
      (hl : Γ ⊢ₗ e₁ : τ)
      (hv : HasValues τ)
      (hr : Γ ⊢ e₂ : τ')
      (hv' : HasValues τ')
      (hc : Typing.compat p τ' τ) :
    -- ──────────────────────────── (T-Assign)
      ⟨Γ, τᵣ⟩ ⊢ .assign e₁ e₂ ⊣ Γ

  /-- Any τ, `void` included. -/
  | exprStmt
      (h : Γ ⊢ e : τ) :
    -- ──────────────────────────── (T-ExprStmt)
      ⟨Γ, τᵣ⟩ ⊢ .exprStmt e ⊣ Γ

  | delete
      (h : Γ ⊢ e : .ptr (.cls c)) :
    -- ────────────────────────────────── (T-Delete)
      ⟨Γ, τᵣ⟩ ⊢ .delete e static ⊣ Γ

  /-- The last premise is the relation `delete` of the module of L. -/
  | deleteLib
      (h : Γ ⊢ e : .ptr (.lib L ts))
      (ho : IsObject (.lib L ts))
      (hS : staticOf L = some S)
      (hd : S.delete ts) :
    -- ────────────────────────────────── (T-DeleteLib)
      ⟨Γ, τᵣ⟩ ⊢ .delete e static ⊣ Γ

/-- Γ ⊢ c₁ … cₙ ⊣ Γₙ, threading the context through the sequence. -/
inductive Checks (p : Program) : Ty → TEnv → List Cmd → TEnv → Prop where
  | nil :
    -- ──────────────────── (T-Seq-Empty)
      ⟨Γ, τᵣ⟩ ⊢ [] ⊣* Γ

  | cons
      (h : ⟨Γ, τᵣ⟩ ⊢ c ⊣ Γ₁)
      (hs : ⟨Γ₁, τᵣ⟩ ⊢ cs ⊣* Γ₂) :
    -- ──────────────────────────── (T-Seq)
      ⟨Γ, τᵣ⟩ ⊢ c :: cs ⊣* Γ₂

end

/-- Every `return` of a member that returns a reference is a `return e` with e
denoting a location. The walk does not enter the body of a lambda, whose
`return` is the lambda's own. -/
inductive RefReturns (p : Program) (Γ : TEnv) : List Cmd → Prop where
  | nil :
    -- ─────────────────── (T-RetRef)
      RefReturns p Γ []

  | ret
      (h : Γ ⊢ₗ e : τ)
      (hs : RefReturns p Γ cs) :
    -- ─────────────────────────────────
      RefReturns p Γ (.ret (some e) :: cs)

  | retNone
      (hs : RefReturns p Γ cs) :
    -- ───────────────────────────────
      RefReturns p Γ (.ret none :: cs)

  | block
      (hb : RefReturns p Γ b)
      (hs : RefReturns p Γ cs) :
    -- ───────────────────────────────
      RefReturns p Γ (.block b :: cs)

  | while
      (hb : RefReturns p Γ b)
      (hs : RefReturns p Γ cs) :
    -- ─────────────────────────────────
      RefReturns p Γ (.while e b :: cs)

  | ite
      (ht : RefReturns p Γ t)
      (hf : RefReturns p Γ f)
      (hs : RefReturns p Γ cs) :
    -- ─────────────────────────────────
      RefReturns p Γ (.ite e t f :: cs)

  | forLoop
      (hb : RefReturns p Γ b)
      (hs : RefReturns p Γ cs) :
    -- ──────────────────────────────────────
      RefReturns p Γ (.for c₀ e cₛ b :: cs)

  | other
      (ho : c matches .decl .. | .declRef .. | .declAuto .. | .assign .. | .exprStmt .. | .delete ..)
      (hs : RefReturns p Γ cs) :
    -- ───────────────────────────
      RefReturns p Γ (c :: cs)

/-- ⊢ τ f (τ₁ x₁, …, τₖ xₖ) { c }, rule T-Fun. The parameter and result types
have values and are well formed, and the body is well typed under the context
of the parameters and the result type. A reference parameter has in Γ the
type of its referent, as a local reference does. -/
structure FunOk (p : Program) (f : Fun) : Prop where
  /-- The result type is `void` or storable. -/
  ret : f.ret = .void ∨ Storable f.ret
  /-- The result type is well formed. -/
  retWF : WF p f.ret
  /-- Each parameter type is bindable, an object type when by reference. -/
  params : ∀ q ∈ f.params, Bindable q.byRef q.ty
  /-- Each parameter type is well formed. -/
  paramsWF : ∀ q ∈ f.params, WF p q.ty
  /-- The body is well typed under the parameters and the result type. -/
  body : ∃ Γ', ⟨TEnv.ofParams f.params, f.ret⟩ ⊢ f.body ⊣* Γ'

/-- ⊢ class C : public B { … }, rule T-Class. The base exists and the chain of
bases has no cycle. The fields have types that carry values, are well formed,
and repeat no field of a base. The members have distinct names, and each
method redefines only a method the base declares `virtual`, carrying
`override` and the same signature. The constructor of the base, if the base
has one, takes no parameters. Every member body is well typed under `this`. -/
structure ClassOk (p : Program) (c : ClassDecl) : Prop where
  /-- The base, when there is one, is a declared class. -/
  base : ∀ b, c.base = some b → (p.lookupClass b).isSome
  /-- The chain of bases has no cycle. -/
  chain : p.chainAcyclic c.name
  /-- The field names are distinct. -/
  fields : (c.fields.map (·.name)).eraseDups.length = c.fields.length
  /-- No method has the name of a field. -/
  names : ∀ m ∈ c.methods, ¬ (c.fields.map (·.name)).contains m.name
  /-- Two methods of one name with different signatures are distinguishable,
  by arity or by a parameter of a type other than `std::function`. -/
  overloads : ∀ m ∈ c.methods, ∀ m' ∈ c.methods,
    m.name = m'.name → sigOf m.params ≠ sigOf m'.params → Param.distinguishable m.params m'.params
  /-- No method is declared twice with the same signature. -/
  distinct : ∀ m ∈ c.methods,
    (c.methods.filter fun m' => m'.name == m.name && sigOf m'.params == sigOf m.params).length = 1
  /-- No field repeats a field of a base. -/
  fresh : ∀ f ∈ c.fields, ∀ b, c.base = some b → ¬ ((p.allFields b).map (·.1.name)).contains f.name
  /-- No field has type `void`, which has no values. -/
  fieldsNotVoid : ∀ f ∈ c.fields, f.ty ≠ .void
  /-- Each field type is storable. -/
  fieldTypes : ∀ f ∈ c.fields, Storable f.ty
  /-- Each field type is well formed. -/
  fieldsWF : ∀ f ∈ c.fields, WF p f.ty
  /-- Every operator of the subset is binary, the receiver and one parameter. -/
  operators : ∀ m ∈ c.methods, m.name.startsWith "operator" → m.params.length = 1
  /-- A method that returns a reference has a result and returns locations
  only, rule T-RetRef. -/
  refs : ∀ m ∈ c.methods, m.retRef = true →
    m.ret ≠ .void ∧ RefReturns p (Typing.memberEnv c.name m.params) m.body
  /-- A method that redefines a method of a base redefines a virtual one, is
  marked `override`, and keeps its signature. -/
  inherited : ∀ m ∈ c.methods, ∀ bm k, p.inherited c m.name m.params = some (bm, k) →
    bm.isVirtual = true ∧ m.isOverride = true ∧ bm.ret = m.ret ∧
      bm.params.map (fun q => (q.ty, q.byRef)) = m.params.map (fun q => (q.ty, q.byRef))
  /-- A method marked `override` redefines a method of a base. -/
  overrides : ∀ m ∈ c.methods, p.inherited c m.name m.params = none → m.isOverride = false
  /-- The result type of each method is `void` or storable, and well formed. -/
  results : ∀ m ∈ c.methods, (m.ret = .void ∨ Storable m.ret) ∧ WF p m.ret
  /-- The parameter types of each method are bindable and well formed. -/
  params : ∀ m ∈ c.methods, ∀ q ∈ m.params, Bindable q.byRef q.ty ∧ WF p q.ty
  /-- Each method body is well typed under `this` and its parameters. -/
  bodies : ∀ m ∈ c.methods, ∃ Γ', ⟨Typing.memberEnv c.name m.params, m.ret⟩ ⊢ m.body ⊣* Γ'
  /-- The constructor of the base, when there is one, has no parameters, since
  there is no initialiser list. -/
  baseCtor : ∀ b bd, c.base = some b → p.lookupClass b = some bd → ∀ k, bd.ctor = some k → k.params = []
  /-- The parameter types of the constructor are bindable and well formed. -/
  ctorParams : ∀ k, c.ctor = some k → ∀ q ∈ k.params, Bindable q.byRef q.ty ∧ WF p q.ty
  /-- The constructor body is well typed under `this`, with result `void`. -/
  ctorBody : ∀ k, c.ctor = some k → ∃ Γ', ⟨Typing.memberEnv c.name k.params, .void⟩ ⊢ k.body ⊣* Γ'
  /-- The destructor body is well typed under `this`, with result `void`. -/
  dtorBody : ∀ d, c.dtor = some d → ∃ Γ', ⟨Typing.memberEnv c.name [], .void⟩ ⊢ d.body ⊣* Γ'

/-- ⊢ p, rule T-Program. The program is the one with its class templates
instantiated, `Templates.instantiate`, since a template is never checked and
only its instantiations are. Class and function names are distinct up to
overloading, every declaration of a header has a module that agrees with it,
every class and function is well typed and `int main()` exists. -/
structure ProgramOk (p : Program) : Prop where
  /-- Two functions of one name with different signatures are
  distinguishable. -/
  overloads : ∀ f ∈ p.funs, ∀ g ∈ p.funs,
    f.name = g.name → sigOf f.params ≠ sigOf g.params → Param.distinguishable f.params g.params
  /-- No function is declared twice with the same signature. -/
  distinct : ∀ f ∈ p.funs, ((p.funsNamed f.name).filter fun g => sigOf g.params == sigOf f.params).length = 1
  /-- Every class template a header declares has a module. -/
  libTemplates : ∀ n ps, Decl.libTmpl n ps ∈ p → ∃ S, staticOf n = some S
  /-- Every function a header declares has a module whose signature agrees
  with the declaration. -/
  libFunctions : ∀ f r ps, Decl.libFn f r ps ∈ p → ∃ S, staticOf f = some S ∧ S.call (ps.map (·.ty)) r
  /-- Class and template names are distinct. -/
  classNames : (p.classes.map (·.name) ++ p.templates.map (·.2.name)).eraseDups.length
    = (p.classes.map (·.name) ++ p.templates.map (·.2.name)).length
  /-- Every class is well formed. -/
  classes : ∀ c ∈ p.classes, ClassOk p c
  /-- Every function is well typed. -/
  functions : ∀ f ∈ p.funs, FunOk p f
  /-- There is a function `int main()`. -/
  main : ∃ m, FunEnv.lookup p "main" = some m ∧ m.ret = .int ∧ m.params = []

end Semantics

end CoreCpp
