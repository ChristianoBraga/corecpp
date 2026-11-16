import CoreCpp.Semantics.InterpSound

/-!
# Completeness of the evaluator

The theorem `interp_complete` of the blueprint, after `Stmt.interp_complete`
of Radix. Every derivation of a relation of the dynamic semantics is reached by
the function of its judgement with enough fuel.

The predicate `Done c a` states that c gives the value a from every state of
the monad. The proof is one mutual structural recursion on the derivation. A
rule with premises reached with fuels nᵢ is reached with fuel 1 + Σ nᵢ and
with any larger fuel.
-/

namespace CoreCpp.Eval

open Semantics

variable {α β : Type}

/-- c gives the value a from every state. -/
def Done (c : M α) (a : α) : Prop := ∀ s, (res c s).1 = .ok a

/-- The function f reaches the value a with every fuel from some bound on. -/
def Reach (f : Nat → M α) (a : α) : Prop := ∃ n, ∀ m, n ≤ m → Done (f m) a

theorem done_pure : Done (pure a : M α) a := fun _ => rfl

theorem done_bind {c : M α} {f : α → M β} (hc : Done c a) (hf : Done (f a) b) : Done (c >>= f) b := by
  intro s
  rw [res_bind]
  rcases h : res c s with ⟨r, s₁⟩
  have := hc s
  rw [h] at this
  cases this
  exact hf s₁

theorem done_modify : Done (modify f : M Unit) () := fun _ => rfl

theorem done_get_bind {f : TState → M β} (hf : ∀ t, Done (f t) b) : Done (get >>= f) b := by
  intro s
  rw [res_bind, res_get]
  exact hf s s

theorem done_tryCatch (hc : Done c a) : Done (tryCatch c h) a := by
  intro s
  rw [res_tryCatch]
  rcases hr : res c s with ⟨r, s₁⟩
  have := hc s
  rw [hr] at this
  cases this
  rfl

theorem done_observe (hc : Done c a) : Done (observe c) (.ok a) := by
  intro s
  rw [res_observe]
  rcases hr : res c s with ⟨r, s₁⟩
  have := hc s
  rw [hr] at this
  cases this
  rfl

theorem done_observe' (hc : Done c a) :
    Done (tryCatch (do let a ← c; Pure.pure (Except.ok a)) (fun e => Pure.pure (Except.error e))) (Except.ok a) := by
  have h' := done_observe hc
  simp only [bind_pure_comp]
  exact h'

theorem done_traced (h : Done k a) : Done (traced rule ante render k arrow) a := by
  unfold Eval.traced
  refine done_bind done_modify (done_bind (done_observe' h) (done_bind done_modify (done_get_bind fun t => ?_)))
  dsimp only
  split
  · exact done_bind done_modify done_pure
  · exact done_pure

theorem done_tracedLib {k : M (String × α)} (h : Done k (r, a)) : Done (tracedLib fallback ante render k arrow) a := by
  unfold Eval.tracedLib
  refine done_bind done_modify (done_bind (done_observe' h) (done_bind done_modify (done_get_bind fun t => ?_)))
  dsimp only
  split
  · exact done_bind done_modify (done_bind done_modify done_pure)
  · exact done_bind done_modify done_pure

theorem done_tracedCases {k : M (String × Except Error α)} (h : Done k (r, .ok a)) :
    Done (tracedCases before ante render k arrow) a := by
  unfold Eval.tracedCases
  exact done_tracedLib (r := r) (done_bind h done_pure)

theorem done_int32 (h : Int32.inRange n) : Done (int32 n) (.int n) := by
  unfold int32; rw [if_pos h]; exact done_pure

theorem done_readLoc (h : σ.read l = some v) : Done (readLoc σ l) v := by
  unfold readLoc; rw [h]; exact done_pure

theorem done_pointee : Done (pointee (.loc l)) l := done_pure

theorem done_expectBool : Done (expectBool w (.bool b)) b := done_pure

theorem done_fnsOf (h : Std.fnsOf n = some F) : Done (fnsOf n) F := by
  unfold fnsOf; rw [h]; exact done_pure

theorem done_libStep (h : k = .ok (r, a)) : Done (libStep ρ σ subject render k) a := by
  unfold libStep; subst h; exact done_tracedLib done_pure

/-- The body of the loop of New, the constructors of the chain. -/
def ctorBody (n : Nat) (p : Program) (ρ : Env) (l : Loc) (c : String) (es : List Expr) (cd : ClassDecl) (s : Store) :
    M (ForInStep Store) :=
  match cd.ctor with
  | some k => do
    let x ← runMember n p ρ s l k.params k.body (if (cd.name == c) = true then es else []) Ty.void
      (toString "constructor of " ++ toString cd.name)
    pure (ForInStep.yield x.snd)
  | _ => pure (ForInStep.yield s)

/-- The body of the loop of Delete, the destructors of the chain. -/
def dtorBody (n : Nat) (p : Program) (ρ : Env) (l : Loc) (cd : ClassDecl) (s : Store) : M (ForInStep Store) :=
  match cd.dtor with
  | some d => do
    let x ← runMember n p ρ s l [] d.body [] Ty.void (toString "destructor of " ++ toString cd.name)
    pure (ForInStep.yield x.snd)
  | _ => pure (ForInStep.yield s)

/-- The body of the loop of Call and of `runMember`, the binding of one parameter. -/
def bindBody (n : Nat) (p : Program) (ρ : Env) (x : Param × Expr) (s : Store × Env × List Loc) :
    M (ForInStep (Store × Env × List Loc)) :=
  if x.fst.byRef = true then do
    let y ← lval n p ρ s.fst x.snd
    pure (ForInStep.yield (y.snd, s.snd.fst.alias x.fst.name y.fst, s.snd.snd))
  else do
    let y ← expr n p ρ s.fst x.snd
    pure (ForInStep.yield ((y.snd.alloc y.fst).snd, s.snd.fst.extend x.fst.name (y.snd.alloc y.fst).fst,
      (y.snd.alloc y.fst).fst :: s.snd.snd))

theorem done_forIn_cons {f : τ → β → M (ForInStep β)} (h : Done (f x b) (.yield b')) (hs : Done (forIn xs b' f) c) :
    Done (forIn (x :: xs) b f) c := by
  rw [List.forIn_cons]
  exact done_bind h hs

/-! ## The library and the operators -/

theorem lib_new_complete {Md : Module} (hM : moduleOf n = some Md) (h : Md.new ts vs σ v σ') :
    ∃ F r, Std.fnsOf n = some F ∧ F.new ts vs σ = .ok (r, v, σ') := by
  unfold moduleOf at hM
  split at hM <;> cases hM
  · cases h with
    | new hk ha ho =>
      refine ⟨_, "V-New", rfl, ?_⟩
      simp only [Std.Vector.fns]
      rw [if_neg (by omega)]
      simp [ha, ho]
      rfl
  · cases h with
    | target hw ht ho => subst hw; exact ⟨_, _, rfl, by simp [Std.Function.fns, ht, ho]; rfl⟩
    | empty ht ho => exact ⟨_, _, rfl, by simp [Std.Function.fns, ht, ho]; rfl⟩
  · cases h

theorem lib_index_complete {Md : Module} (hM : moduleOf n = some Md) (h : Md.index v w σ l σ') :
    ∃ F r, Std.fnsOf n = some F ∧ F.index v w σ = .ok (r, l, σ') := by
  unfold moduleOf at hM
  split at hM <;> cases hM
  · cases h with
    | index hi hl =>
      refine ⟨_, "V-Index", rfl, ?_⟩
      simp only [Std.Vector.fns, hl]
      rw [if_neg (by omega)]
      rfl
  · cases h
  · cases h

theorem lib_delete_complete {Md : Module} (hM : moduleOf n = some Md) (h : Md.delete v σ σ') :
    ∃ F r, Std.fnsOf n = some F ∧ F.delete v σ = .ok (r, σ') := by
  unfold moduleOf at hM
  split at hM <;> cases hM
  · cases h; exact ⟨_, _, rfl, rfl⟩
  · cases h; exact ⟨_, _, rfl, rfl⟩
  · cases h

theorem lib_call_complete {Md : Module} (hM : moduleOf n = some Md) (h : Md.call vs σ v σ') :
    ∃ F r, Std.fnsOf n = some F ∧ F.call vs σ = .ok (r, v, σ') := by
  unfold moduleOf at hM
  split at hM <;> cases hM
  · cases h
  · cases h
  · cases h; exact ⟨_, _, rfl, rfl⟩

theorem done_arith (hop : op.isArith = true) (hr : Int32.inRange (op.arith a b)) :
    Done (binop op (.int a) (.int b)) (.int (op.arith a b)) := by
  cases op <;> simp [BinOp.isArith] at hop <;> exact done_int32 hr

theorem done_divide (hz : b ≠ 0) (hd : op.divide a b = some k) (hr : Int32.inRange k) :
    Done (binop op (.int a) (.int b)) (.int k) := by
  cases op <;> simp [BinOp.divide] at hd
  · subst hd; simp only [binop]; exact done_int32 hr
  · obtain ⟨hq, rfl⟩ := hd
    simp only [binop]
    exact done_bind (done_int32 hq) (done_int32 hr)

theorem done_compare (hc : op.compare v w = some b) : Done (binop op v w) (.bool b) := by
  cases op <;> cases v <;> cases w <;> simp [BinOp.compare] at hc <;> subst hc <;> exact done_pure

theorem done_captures_loop (names : List String) (c₀ : List (String × Val))
    (h : names.foldlM (captureStep ρ σ) c₀ = some cap) :
    Done (forIn names c₀ fun x c =>
      match ρ.lookup x with
      | some l => do
        let v ← readLoc σ l
        pure (ForInStep.yield (c ++ [(x, v)]))
      | _ => pure (ForInStep.yield c)) cap := by
  induction names generalizing c₀ with
  | nil => cases h; exact done_pure
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases hs : captureStep ρ σ c₀ x with
    | none => rw [hs] at h; cases h
    | some c' =>
      rw [hs] at h
      refine done_forIn_cons (b' := c') ?_ (ih c' h)
      unfold captureStep at hs
      split at hs
      · rename_i hl
        cases hs
        rw [hl]; exact done_pure
      · rename_i l hl
        rw [hl]
        cases hv : σ.read l with
        | none => rw [hv] at hs; cases hs
        | some v => rw [hv] at hs; cases hs; exact done_bind (done_readLoc hv) done_pure

theorem done_captures (h : captures? ρ σ ps b = some cap) : Done (captures ρ σ ps b) cap := by
  unfold captures
  unfold captures? at h
  exact done_bind (done_captures_loop _ [] h) done_pure

theorem done_resolve (h : p.resolve s t m sig = some r) : Done (resolve (k + 1) p s t m sig) r := by
  unfold Eval.resolve
  cases sig <;>
  · dsimp only
    simp only [Program.resolve] at h
    split at h
    · cases h
    · rename_i md k' hs
      rw [hs]
      dsimp only
      split at h
      · rename_i hv
        rw [if_pos hv, h]; exact done_pure
      · rename_i hv
        rw [if_neg hv]; cases h; exact done_pure

theorem done_fieldLoc (ho : σ.read l = some (.obj c fs)) (hf : fs.lookup f = some lf) :
    Done (fieldLoc (k + 1) σ l f) (lf, σ) := by
  unfold Eval.fieldLoc
  refine done_bind (done_readLoc ho) ?_
  dsimp only
  rw [hf]; exact done_pure

theorem done_target (h : σ.read lt = some w) (hw : w = .closure ps r b cap) :
    Done (target σ (.lib "std::function" [lt])) w := by
  unfold target
  refine done_bind (done_readLoc h) ?_
  subst hw; exact done_pure

theorem done_forIn_pure {l : List τ} {g : τ → β → β} :
    Done (forIn l b fun x s => pure (ForInStep.yield (g x s)) : M β) (l.foldl (fun s x => g x s) b) := by
  induction l generalizing b with
  | nil => exact done_pure
  | cons x xs ih => exact done_forIn_cons done_pure ih

theorem done_forIn_alloc (xs : List τ) (nm : τ → String) (vl : τ → Val) (σ : Store) (ρ : Env) (acc : List Loc) :
    Done (forIn xs (σ, ρ, acc) fun x s =>
        pure (ForInStep.yield ((s.1.alloc (vl x)).2, s.2.1.extend (nm x) (s.1.alloc (vl x)).1, (s.1.alloc (vl x)).1 :: s.2.2)))
      ((σ.allocMany (xs.map vl)).2, ρ.extendAll (xs.map nm) (σ.allocMany (xs.map vl)).1,
        (σ.allocMany (xs.map vl)).1.reverse ++ acc) := by
  rw [← foldl_alloc]
  exact done_forIn_pure

theorem any_of_lookup_none {l : List (String × Nat)} (h : l.lookup f = none) : (l.any (·.1 == f)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    simp only [List.lookup] at h
    split at h
    · cases h
    · rename_i hne
      simp only [List.any_cons, Bool.or_eq_false_iff]
      refine ⟨?_, ih h⟩
      simp only [beq_eq_false_iff_ne, ne_eq] at hne ⊢
      exact fun h => hne h.symm

theorem lookup_none_of_funsNamed {p : Program} (h : p.funsNamed f = []) : FunEnv.lookup p f = none := by
  simp only [Program.funsNamed, List.filter_eq_nil_iff] at h
  simp only [FunEnv.lookup, List.find?_eq_none]
  exact h

theorem compare_and : BinOp.compare .and v w = none := by cases v <;> cases w <;> rfl

theorem compare_or : BinOp.compare .or v w = none := by cases v <;> cases w <;> rfl

/-! ## The derivations -/

mutual

theorem Eval.complete : Eval p ρ σ e v σ' → Reach (fun m => expr m p ρ σ e) (v, σ')
  | .lit h => ⟨1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr; exact done_traced (done_bind (done_int32 h) done_pure)⟩
  | .boolLit => ⟨1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr; exact done_traced done_pure⟩
  | .null => ⟨1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr; exact done_traced done_pure⟩
  | .var hl hr => by
      obtain ⟨n₁, e₁⟩ := LEval.complete hl
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_traced (done_bind (e₁ k (by omega)) (done_bind (done_readLoc hr) done_pure))
  | .this h => ⟨1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr; simp only [h]; exact done_traced done_pure⟩
  | .read (e := e) hp hl hr => by
      obtain ⟨n₁, e₁⟩ := LEval.complete hl
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      cases e <;> simp [Expr.isPlace] at hp <;>
        (unfold Eval.expr
         exact done_traced (done_bind (e₁ k (by omega)) (done_bind (done_readLoc hr) done_pure)))
  | .new (c := c) (ls := ls) (σ₁ := σ₁) hc ha ho hk => by
      obtain ⟨n₁, e₁⟩ := Ctors.complete hk
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      dsimp only
      rw [if_neg (by simpa using hc)]
      have ha' : σ.allocMany (List.map (fun x => x.fst.ty.default) (p.allFields c)) = (ls, σ₁) := ha
      rw [ha']
      dsimp only
      rw [ho]
      exact done_traced (done_bind (e₁ k (by omega)) done_pure)
  | .methodCall h hr => by
      obtain ⟨n₁, e₁⟩ := CallMethod.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      refine done_traced (done_bind (e₁ k (by omega)) ?_)
      dsimp only
      rw [if_neg (by simp [hr])]
      exact done_pure
  | .methodCallRef h hr hv => by
      obtain ⟨n₁, e₁⟩ := CallMethod.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      refine done_traced (done_bind (e₁ k (by omega)) ?_)
      dsimp only
      rw [if_pos hr]
      exact done_bind done_pointee (done_bind (done_readLoc hv) done_pure)
  | .newLib ha hM hn => by
      obtain ⟨n₁, e₁⟩ := Args.complete ha
      obtain ⟨F, r, hF, hk⟩ := lib_new_complete hM hn
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_traced (done_bind (e₁ k (by omega)) (done_bind (done_fnsOf hF) (done_libStep hk)))
  | .not h => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_tracedLib (done_bind (e₁ k (by omega)) (done_bind done_pure done_pure))
  | .neg h hr => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_tracedLib (done_bind (e₁ k (by omega)) (done_bind (done_int32 hr) done_pure))
  | .arith (op := op) hop h₁ h₂ hr => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := Eval.complete h₂
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      cases op <;> simp [BinOp.isArith] at hop <;>
        (unfold Eval.expr
         exact done_tracedLib (done_bind (e₁ k (by omega)) (done_bind (e₂ k (by omega))
           (done_bind (done_arith rfl hr) done_pure))))
  | .div (op := op) h₁ h₂ hz hd hr => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := Eval.complete h₂
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hw := done_divide hz hd hr
      cases op <;> simp [BinOp.divide] at hd <;>
        (unfold Eval.expr
         exact done_tracedLib (done_bind (e₁ k (by omega)) (done_bind (e₂ k (by omega)) (done_bind hw done_pure))))
  | .rel (op := op) h₁ h₂ hc => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := Eval.complete h₂
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hw := done_compare hc
      cases op
      all_goals first
        | (rw [compare_and] at hc; cases hc)
        | (rw [compare_or] at hc; cases hc)
        | (unfold Eval.expr
           exact done_tracedLib (done_bind (e₁ k (by omega)) (done_bind (e₂ k (by omega)) (done_bind hw done_pure))))
  | .andF h => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_tracedCases (r := "And-False") (done_bind (e₁ k (by omega)) (done_bind done_expectBool done_pure))
  | .andT h₁ h₂ => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := Eval.complete h₂
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_tracedCases (r := "And-True") (done_bind (e₁ k (by omega)) (done_bind done_expectBool
        (done_bind (done_observe (e₂ k (by omega))) done_pure)))
  | .orT h => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_tracedCases (r := "Or-True") (done_bind (e₁ k (by omega)) (done_bind done_expectBool done_pure))
  | .orF h₁ h₂ => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := Eval.complete h₂
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_tracedCases (r := "Or-False") (done_bind (e₁ k (by omega)) (done_bind done_expectBool
        (done_bind (done_observe (e₂ k (by omega))) done_pure)))
  | .condT h₁ h₂ => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := Eval.complete h₂
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_tracedCases (r := "Cond-T") (done_bind (e₁ k (by omega)) (done_bind done_expectBool
        (done_bind (done_observe (e₂ k (by omega))) done_pure)))
  | .condF h₁ h₃ => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := Eval.complete h₃
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_tracedCases (r := "Cond-F") (done_bind (e₁ k (by omega)) (done_bind done_expectBool
        (done_bind (done_observe (e₂ k (by omega))) done_pure)))
  | .call (f := f) (fn := fn) hρ hf hn hb hx hr => by
      obtain ⟨n₁, e₁⟩ := Bind.complete hb
      obtain ⟨n₂, e₂⟩ := Execs.complete hx
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hl : (FunEnv.lookup p f).isNone = false := by
        have := lookupSig_lookup hf; cases h : FunEnv.lookup p f <;> simp_all
      unfold Eval.expr
      simp only [hρ, hl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      refine done_traced ?_
      simp only [hf]
      rw [if_neg (by simpa using hn)]
      refine done_bind (e₁ k (by omega) []) (done_bind (e₂ k (by omega)) ?_)
      dsimp only
      rw [List.append_nil, free_reverse, fresh_eq]
      generalize fn.ret = τ at hr ⊢
      cases hr <;> exact done_pure
  | .callVar (w := w) hρ hv ht ha => by
      obtain ⟨n₁, e₁⟩ := Eval.complete hv
      obtain ⟨n₂, e₂⟩ := ApplyArgs.complete ha
      have hw : ∃ ps r b cap, w = Val.closure ps r b cap := by cases ha; exact ⟨_, _, _, _, ‹_›⟩
      obtain ⟨ps, r, b, cap, hw⟩ := hw
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      simp only [hρ]
      exact done_traced (done_bind (e₁ k (by omega)) (done_bind (done_target ht hw) (e₂ k (by omega))))
  | .callThis (f := f) hρ hf hl ht h => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      simp only [hρ, hf, ht, any_of_lookup_none hl, Option.isNone_none, Option.isSome_some, Bool.and_false,
        Bool.and_true, Bool.false_eq_true, ↓reduceIte]
      exact e₁ k (by omega)
  | .callLib (f := f) hρ hf hd hM ha hc => by
      obtain ⟨n₁, e₁⟩ := Args.complete ha
      obtain ⟨F, r, hF, hk⟩ := lib_call_complete hM hc
      have hany : (p.libDecls.any (·.1 == f)) = true := List.any_eq_true.mpr ⟨_, hd, by simp⟩
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      simp only [hρ, lookup_none_of_funsNamed hf, hany, Option.isNone_none, Bool.and_true, ↓reduceIte]
      refine done_traced ?_
      rw [if_pos (by simpa using hd)]
      exact done_bind (e₁ k (by omega)) (done_bind (done_fnsOf hF) (done_libStep hk))
  | .callFn (w := w) he ht ha => by
      obtain ⟨n₁, e₁⟩ := Eval.complete he
      obtain ⟨n₂, e₂⟩ := ApplyArgs.complete ha
      have hw : ∃ ps r b cap, w = Val.closure ps r b cap := by cases ha; exact ⟨_, _, _, _, ‹_›⟩
      obtain ⟨ps, r, b, cap, hw⟩ := hw
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_traced (done_bind (e₁ k (by omega)) (done_bind (done_target ht hw) (e₂ k (by omega))))
  | .lambda hc => ⟨1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr; exact done_traced (done_bind (done_captures hc) done_pure)⟩
  | .locOf h => by
      obtain ⟨n₁, e₁⟩ := LEval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.expr
      exact done_traced (done_bind (e₁ k (by omega)) done_pure)
termination_by structural h => h

theorem LEval.complete : LEval p ρ σ e l σ' → Reach (fun m => lval m p ρ σ e) (l, σ')
  | .locVar h => ⟨1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.lval; simp only [h]; exact done_traced done_pure⟩
  | .locVarField h ht ho hf => ⟨2, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      unfold Eval.lval; simp only [h, ht]; exact done_traced (done_fieldLoc ho hf)⟩
  | .locDeref h => by
      obtain ⟨n₁, h₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.lval
      exact done_traced (done_bind (h₁ k (by omega)) (done_bind done_pointee done_pure))
  | .locField h ho hf => by
      obtain ⟨n₁, h₁⟩ := LEval.complete h
      refine ⟨n₁ + 2, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      unfold Eval.lval
      exact done_traced (done_bind (h₁ (k + 1) (by omega)) (done_fieldLoc ho hf))
  | .locArrow h ho hf => by
      obtain ⟨n₁, h₁⟩ := Eval.complete h
      refine ⟨n₁ + 2, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      unfold Eval.lval
      exact done_traced (done_bind (h₁ (k + 1) (by omega)) (done_bind done_pointee (done_fieldLoc ho hf)))
  | .methodLoc h hr => by
      obtain ⟨n₁, h₁⟩ := CallMethod.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.lval
      refine done_traced (done_bind (h₁ k (by omega)) ?_)
      dsimp only
      rw [if_neg (by simp [hr])]
      exact done_bind done_pointee done_pure
  | .locIndex h₁ h₂ hM hi => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := Eval.complete h₂
      obtain ⟨F, r, hF, hk⟩ := lib_index_complete hM hi
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.lval
      refine done_traced (done_bind (e₁ k (by omega)) ?_)
      dsimp only
      exact done_bind (e₂ k (by omega)) (done_bind (done_fnsOf hF) (done_libStep hk))
  | .locCondT h₁ h₂ => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := LEval.complete h₂
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.lval
      refine done_tracedCases (r := "LocCond-T") (done_bind (e₁ k (by omega)) (done_bind done_expectBool ?_))
      simp only [↓reduceIte]
      exact done_bind (done_observe (e₂ k (by omega))) done_pure
  | .locCondF h₁ h₂ => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h₁
      obtain ⟨n₂, e₂⟩ := LEval.complete h₂
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.lval
      refine done_tracedCases (r := "LocCond-F") (done_bind (e₁ k (by omega)) (done_bind done_expectBool ?_))
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact done_bind (done_observe (e₂ k (by omega))) done_pure
termination_by structural h => h

theorem Exec.complete : Exec p ρ σ c r ρ' σ' → Reach (fun m => cmd m p ρ σ c) (r, ρ', σ')
  | .block h => by
      obtain ⟨n₁, h₁⟩ := Execs.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      exact done_traced (done_bind (h₁ k (by omega)) done_pure)
  | .ifT hc h => by
      obtain ⟨n₁, e₁⟩ := Eval.complete hc
      obtain ⟨n₂, e₂⟩ := Exec.complete h
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_tracedCases (r := "If-T") (done_bind (e₁ k (by omega)) (done_bind done_expectBool ?_))
      simp only [↓reduceIte]
      exact done_bind (done_observe (e₂ k (by omega))) done_pure
  | .ifF hc h => by
      obtain ⟨n₁, e₁⟩ := Eval.complete hc
      obtain ⟨n₂, e₂⟩ := Exec.complete h
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_tracedCases (r := "If-F") (done_bind (e₁ k (by omega)) (done_bind done_expectBool ?_))
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact done_bind (done_observe (e₂ k (by omega))) done_pure
  | .whileF hc => by
      obtain ⟨n₁, e₁⟩ := Eval.complete hc
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_tracedCases (r := "While-F") (done_bind (e₁ k (by omega)) (done_bind done_expectBool ?_))
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact done_pure
  | .whileT hc hb hw => by
      obtain ⟨n₁, e₁⟩ := Eval.complete hc
      obtain ⟨n₂, e₂⟩ := Exec.complete hb
      obtain ⟨n₃, e₃⟩ := Exec.complete hw
      refine ⟨n₁ + n₂ + n₃ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_tracedCases (r := "While-T") (done_bind (e₁ k (by omega)) (done_bind done_expectBool ?_))
      simp only [↓reduceIte]
      refine done_bind (done_observe (e₂ k (by omega))) ?_
      dsimp only
      exact done_bind (done_observe (e₃ k (by omega))) done_pure
  | .whileRet hc hb => by
      obtain ⟨n₁, e₁⟩ := Eval.complete hc
      obtain ⟨n₂, e₂⟩ := Exec.complete hb
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_tracedCases (r := "While-Ret") (done_bind (e₁ k (by omega)) (done_bind done_expectBool ?_))
      simp only [↓reduceIte]
      refine done_bind (done_observe (e₂ k (by omega))) ?_
      exact done_pure
  | .forLoop h₀ hw => by
      obtain ⟨n₁, e₁⟩ := Exec.complete h₀
      obtain ⟨n₂, e₂⟩ := Exec.complete hw
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_traced (done_bind (e₁ k (by omega)) ?_)
      dsimp only
      exact done_bind (e₂ k (by omega)) done_pure
  | .retVoid => ⟨1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd; exact done_traced done_pure⟩
  | .ret h => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      exact done_traced (done_bind (e₁ k (by omega)) done_pure)
  | .decl h ha => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_traced (done_bind (e₁ k (by omega)) ?_)
      dsimp only
      rw [ha]; exact done_pure
  | .declRef h => by
      obtain ⟨n₁, e₁⟩ := LEval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      exact done_traced (done_bind (e₁ k (by omega)) done_pure)
  | .declAuto h ha => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_traced (done_bind (e₁ k (by omega)) ?_)
      dsimp only
      rw [ha]; exact done_pure
  | .assign hr hl hd => by
      obtain ⟨n₁, e₁⟩ := Eval.complete hr
      obtain ⟨n₂, e₂⟩ := LEval.complete hl
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_traced (done_bind (e₁ k (by omega)) (done_bind (e₂ k (by omega)) ?_))
      dsimp only
      rw [if_neg (by revert hd; cases _ : Store.read _ _ <;> simp)]
      exact done_pure
  | .exprStmt h => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      exact done_traced (done_bind (e₁ k (by omega)) done_pure)
  | .deleteNull h => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_traced (done_bind (e₁ k (by omega)) ?_)
      exact done_pure
  | .deleteLib h ho hM hd => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      obtain ⟨F, r, hF, hk⟩ := lib_delete_complete hM hd
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_traced (done_bind (e₁ k (by omega)) ?_)
      dsimp only
      simp only [ho]
      exact done_bind (done_fnsOf hF) (done_bind (done_libStep hk) done_pure)
  | .delete h ho hv hd => by
      obtain ⟨n₁, e₁⟩ := Eval.complete h
      obtain ⟨n₂, e₂⟩ := Dtors.complete hd
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmd
      refine done_traced (done_bind (e₁ k (by omega)) ?_)
      dsimp only
      simp only [ho]
      rw [if_neg (by rcases hv with hv | hv <;> simp [hv])]
      exact done_bind (e₂ k (by omega)) done_pure
termination_by structural h => h

theorem Execs.complete : Execs p ρ σ cs r ρ' σ' → Reach (fun m => cmds m p ρ σ cs) (r, ρ', σ')
  | .nil => ⟨1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmds; exact done_pure⟩
  | .cons h hs => by
      obtain ⟨n₁, h₁⟩ := Exec.complete h
      obtain ⟨n₂, h₂⟩ := Execs.complete hs
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmds
      exact done_bind (h₁ k (by omega)) (h₂ k (by omega))
  | .consRet h => by
      obtain ⟨n₁, h₁⟩ := Exec.complete h
      refine ⟨n₁ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.cmds
      exact done_bind (h₁ k (by omega)) done_pure
termination_by structural h => h

theorem Args.complete : Args p ρ σ es vs σ' → Reach (fun m => args m p ρ σ es) (vs, σ')
  | .nil => ⟨1, fun m hm => by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.args; exact done_pure⟩
  | .cons h hs => by
      obtain ⟨n₁, h₁⟩ := Eval.complete h
      obtain ⟨n₂, h₂⟩ := Args.complete hs
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.args
      exact done_bind (h₁ k (by omega)) (done_bind (h₂ k (by omega)) done_pure)
termination_by structural h => h

theorem Bind.complete : Bind p ρ σ ρ₀ ps es ρ' σ' owned →
    ∃ n, ∀ m, n ≤ m → ∀ acc, Done (forIn (ps.zip es) (σ, ρ₀, acc) (bindBody m p ρ)) (σ', ρ', owned.reverse ++ acc)
  | .nil => ⟨0, fun _ _ acc => by simpa using done_pure⟩
  | .byRef hq hl hs => by
      obtain ⟨n₁, h₁⟩ := LEval.complete hl
      obtain ⟨n₂, h₂⟩ := Bind.complete hs
      refine ⟨n₁ + n₂, fun m hm acc => ?_⟩
      rw [List.zip_cons_cons]
      refine done_forIn_cons ?_ (h₂ m (by omega) acc)
      unfold bindBody
      rw [if_pos hq]
      exact done_bind (h₁ m (by omega)) done_pure
  | .byVal (q := q) (ρ₀ := ρ₀) (ℓ := ℓ) (σ₂ := σ₂) hq hv ha hs => by
      obtain ⟨n₁, h₁⟩ := Eval.complete hv
      obtain ⟨n₂, h₂⟩ := Bind.complete hs
      refine ⟨n₁ + n₂, fun m hm acc => ?_⟩
      rw [List.zip_cons_cons]
      refine done_forIn_cons (b' := (σ₂, ρ₀.extend q.name ℓ, ℓ :: acc)) ?_ ?_
      · unfold bindBody
        rw [if_neg (by simp [hq])]
        refine done_bind (h₁ m (by omega)) ?_
        dsimp only
        rw [ha]; exact done_pure
      · simpa using h₂ m (by omega) (ℓ :: acc)
termination_by structural h => h

theorem Member.complete : Member p ρ σ l ps body es ret v σ' →
    ∀ who, Reach (fun m => runMember m p ρ σ l ps body es ret who) (v, σ')
  | .member hn hb hx hr => fun who => by
      obtain ⟨n₁, h₁⟩ := Bind.complete hb
      obtain ⟨n₂, h₂⟩ := Execs.complete hx
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.runMember
      dsimp only
      rw [if_neg (by simpa using hn)]
      refine done_bind (h₁ k (by omega) []) (done_bind (h₂ k (by omega)) ?_)
      dsimp only
      rw [List.append_nil, free_reverse, fresh_eq]
      cases hr <;> exact done_pure
termination_by structural h => h

theorem CallMethod.complete : CallMethod p ρ σ recv arrow k es static sig md v σ' →
    Reach (fun m => callMethod m p ρ σ recv arrow k es static sig) (md, v, σ')
  | .dot (k := k') (m := m') hl ho hm hc => by
      obtain ⟨n₁, h₁⟩ := LEval.complete hl
      obtain ⟨n₂, h₂⟩ := Member.complete hc (toString k' ++ toString "::" ++ toString m')
      refine ⟨n₁ + n₂ + 2, fun m hm' => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      unfold Eval.callMethod
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine done_bind (h₁ (k + 1) (by omega)) (done_bind (done_readLoc ho) ?_)
      dsimp only
      exact done_bind (done_resolve hm) (done_bind (h₂ (k + 1) (by omega)) done_pure)
  | .arrow (k := k') (m := m') hv ho hm hc => by
      obtain ⟨n₁, h₁⟩ := Eval.complete hv
      obtain ⟨n₂, h₂⟩ := Member.complete hc (toString k' ++ toString "::" ++ toString m')
      refine ⟨n₁ + n₂ + 2, fun m hm' => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      unfold Eval.callMethod
      simp only [↓reduceIte, pure_bind]
      refine done_bind (h₁ (k + 1) (by omega)) (done_bind done_pointee (done_bind (done_readLoc ho) ?_))
      dsimp only
      exact done_bind (done_resolve hm) (done_bind (h₂ (k + 1) (by omega)) done_pure)
termination_by structural h => h

theorem Ctors.complete : Ctors p ρ σ l c cds es σ' →
    ∃ n, ∀ m, n ≤ m → Done (forIn cds σ (ctorBody m p ρ l c es)) σ'
  | .nil => ⟨0, fun _ _ => done_pure⟩
  | .skip hk hs => by
      obtain ⟨n, h⟩ := Ctors.complete hs
      exact ⟨n, fun m hm => done_forIn_cons (by unfold ctorBody; rw [hk]; exact done_pure) (h m hm)⟩
  | .run (cd := cd) hk hm hs => by
      obtain ⟨n₁, h₁⟩ := Member.complete hm (toString "constructor of " ++ toString cd.name)
      obtain ⟨n₂, h₂⟩ := Ctors.complete hs
      refine ⟨n₁ + n₂, fun m hm => done_forIn_cons ?_ (h₂ m (by omega))⟩
      unfold ctorBody; rw [hk]
      exact done_bind (h₁ m (by omega)) done_pure
termination_by structural h => h

theorem Dtors.complete : Dtors p ρ σ l cds σ' →
    ∃ n, ∀ m, n ≤ m → Done (forIn cds σ (dtorBody m p ρ l)) σ'
  | .nil => ⟨0, fun _ _ => done_pure⟩
  | .skip hd hs => by
      obtain ⟨n, h⟩ := Dtors.complete hs
      exact ⟨n, fun m hm => done_forIn_cons (by unfold dtorBody; rw [hd]; exact done_pure) (h m hm)⟩
  | .run (cd := cd) hd hm hs => by
      obtain ⟨n₁, h₁⟩ := Member.complete hm (toString "destructor of " ++ toString cd.name)
      obtain ⟨n₂, h₂⟩ := Dtors.complete hs
      refine ⟨n₁ + n₂, fun m hm => done_forIn_cons ?_ (h₂ m (by omega))⟩
      unfold dtorBody; rw [hd]
      exact done_bind (h₁ m (by omega)) done_pure
termination_by structural h => h

theorem Apply.complete : Apply p σ w vs v σ' → Reach (fun m => applyVals m p σ w vs) (v, σ')
  | .apply (ps := ps) (vs := vs) (cap := cap) (σ := σ) hn ha hρ hx hr => by
      obtain ⟨n₂, h₂⟩ := Execs.complete hx
      refine ⟨n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.applyVals
      dsimp only
      rw [if_neg (by simpa using hn)]
      refine done_bind (done_forIn_alloc cap (·.1) (·.2) σ [] []) ?_
      refine done_bind (done_forIn_alloc (ps.zip vs) (·.1.name) (·.2) _ _ _) ?_
      have hv : (ps.zip vs).map (·.2) = vs := List.map_snd_zip (by omega)
      have hp : (ps.zip vs).map (·.1.name) = ps.map (·.name) :=
        calc (ps.zip vs).map (·.1.name) = ((ps.zip vs).map (·.1)).map Param.name := by simp [List.map_map]
          _ = ps.map (·.name) := by rw [List.map_fst_zip (by omega)]
      dsimp only
      rw [hv, hp]
      rw [allocMany_append] at ha
      simp only [Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      subst hρ
      rw [extendAll_append _ _ _ _ _ (by rw [allocMany_length]; simp)] at h₂ ⊢
      refine done_bind (h₂ k (by omega)) ?_
      dsimp only
      have hfree (σ' : Store) (A B L : List Loc) : σ'.free (B.reverse ++ (A.reverse ++ []) ++ L) = σ'.free ((A ++ B) ++ L) := by
        rw [← free_reverse]; simp
      rw [hfree, fresh_eq]
      cases hr <;> dsimp only <;> exact done_pure
termination_by structural h => h

theorem ApplyArgs.complete : ApplyArgs p ρ σ w es v σ' → Reach (fun m => applyClosure m p ρ σ w es) (v, σ')
  | .applyArgs hc hn ha hap => by
      obtain ⟨n₁, h₁⟩ := Args.complete ha
      obtain ⟨n₂, h₂⟩ := Apply.complete hap
      subst hc
      refine ⟨n₁ + n₂ + 1, fun m hm => ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      unfold Eval.applyClosure
      dsimp only
      rw [if_neg (by simpa using hn)]
      exact done_bind (h₁ k (by omega)) (h₂ k (by omega))
termination_by structural h => h

end

end CoreCpp.Eval

namespace CoreCpp

/-- The theorem `interp_complete` of the blueprint, after `Stmt.interp_complete`
of Radix. A derivation of p ⇒ v is reached by the evaluator of `main()` with
every fuel from some bound on. -/
theorem interp_complete (h : Semantics.Runs p v) : ∃ n, ∀ m, n ≤ m → runMain p m = .ok v := by
  obtain ⟨σ, hd⟩ := h
  obtain ⟨n, hn⟩ := Eval.Eval.complete hd
  refine ⟨n, fun m hm => ?_⟩
  unfold runMain evalMain
  have := hn m hm { enabled := false }
  simp only [Eval.res] at this
  rcases hr : StateT.run (ExceptT.run (Eval.expr m p [] {} (.call "main" [] none))) { enabled := false } with ⟨r, s⟩
  rw [hr] at this
  simp only at this
  subst this
  rfl

/-- `interp_complete` for `run`, whose subject is the program `prepare` gives. -/
theorem run_complete (hp : prepare p = .ok q) (h : Semantics.Runs q v) :
    ∃ n, ∀ m, n ≤ m → run p m = .value v := by
  obtain ⟨n, hn⟩ := interp_complete h
  exact ⟨n, fun m hm => by rw [run_eq, hp]; exact Outcome.ofResult_eq_value.mpr (hn m hm)⟩

/-- The theorem `interp_error_sound` of the blueprint. An error of the
evaluator of `main()` other than the exhaustion of the fuel means that p ⇒ v
has no derivation for any v. -/
theorem interp_error_sound (h : runMain p n = .error e) (he : e ≠ .outOfFuel) : ¬ ∃ v, Semantics.Runs p v := by
  rintro ⟨v, hv⟩
  obtain ⟨m, hm⟩ := interp_complete hv
  have h₁ := hm (max n m) (Nat.le_max_right n m)
  rw [runMain_fuel_mono (Nat.le_max_left n m) (by rw [h]; intro h'; cases h'; exact he rfl), h] at h₁
  cases h₁

/-- `interp_error_sound` for `run`, whose subject is the program `prepare` gives. -/
theorem run_error_sound (hp : prepare p = .ok q) (h : run p n = .error e) (he : e ≠ .outOfFuel) :
    ¬ ∃ v, Semantics.Runs q v := by
  rw [run_eq, hp] at h
  exact interp_error_sound (Outcome.ofResult_eq_error.mp h) he

end CoreCpp
