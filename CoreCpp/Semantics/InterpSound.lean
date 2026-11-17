import CoreCpp.Semantics.Dynamic
import CoreCpp.Semantics.FuelMono
import CoreCpp.Semantics.Determinism

/-!
# Soundness of the evaluator

The theorem `interp_sound` of the blueprint, after `Stmt.interp_sound` of
Radix. A value of a function of the evaluator has a derivation in the relation
of its judgement.

The predicate `Ok c P` states that every value of c satisfies P, from every
state of the monad. Its lemmas follow the structure of the evaluator,
sequencing, the caught errors, `traced`, `tracedLib`, `tracedCases` and the
loops of `for`.
-/

namespace CoreCpp.Eval

variable {α β : Type} {P : α → Prop} {Q : β → Prop}

open Semantics

/-- Every value of c satisfies P, from every state. -/
def Ok (c : M α) (P : α → Prop) : Prop := ∀ s a s', res c s = (.ok a, s') → P a

theorem ok_pure (h : P a) : Ok (pure a : M α) P := by
  intro s b s' hr; rw [res_pure] at hr; cases hr; exact h

theorem ok_throw : Ok (throw e : M α) P := by
  intro s b s' hr; rw [res_throw] at hr; cases hr

theorem ok_bind {c : M α} {f : α → M β} (hc : Ok c P) (hf : ∀ a, P a → Ok (f a) Q) :
    Ok (c >>= f) Q := by
  intro s b s' hr
  rw [res_bind] at hr
  rcases h : res c s with ⟨r, s₁⟩
  rw [h] at hr
  cases r with
  | error e => cases hr
  | ok a => exact hf a (hc s a s₁ h) s₁ b s' hr

theorem ok_mono {Q : α → Prop} (h : Ok c P) (hPQ : ∀ a, P a → Q a) : Ok c Q :=
  fun s a s' hr => hPQ a (h s a s' hr)

theorem ok_modify : Ok (modify f : M Unit) (fun _ => True) := fun _ _ _ _ => trivial

theorem ok_get : Ok (get : M TState) (fun _ => True) := fun _ _ _ _ => trivial

theorem ok_tryCatch (hc : Ok c P) (hh : ∀ e, Ok (h e) P) : Ok (tryCatch c h) P := by
  intro s a s' hr
  rw [res_tryCatch] at hr
  rcases hx : res c s with ⟨r, s₁⟩
  rw [hx] at hr
  cases r with
  | ok b => cases hr; exact hc _ _ _ hx
  | error e => exact hh e s₁ a s' hr

/-- The run of c with its error caught as a value. -/
theorem ok_observe (h : Ok c P) : Ok (observe c) (fun x => ∀ a, x = .ok a → P a) := by
  intro s x s' hr
  rw [res_observe] at hr
  rcases hx : res c s with ⟨r, s₁⟩
  rw [hx] at hr
  cases r with
  | ok b => cases hr; intro a ha; cases ha; exact h _ _ _ hx
  | error e => cases hr; intro a ha; cases ha

theorem ok_observe' (h : Ok c P) :
    Ok (tryCatch (do let a ← c; Pure.pure (Except.ok a)) (fun e => Pure.pure (Except.error e)))
      (fun x => ∀ a, x = .ok a → P a) := by
  have h' := ok_observe h
  simp only [bind_pure_comp]
  exact h'

theorem ok_traced (h : Ok k P) : Ok (traced rule ante render k arrow) P := by
  unfold Eval.traced
  refine ok_bind ok_modify fun _ _ => ?_
  refine ok_bind (ok_observe' h) fun x hx => ?_
  refine ok_bind ok_modify fun _ _ => ?_
  refine ok_bind ok_get fun s _ => ?_
  dsimp only
  split
  · refine ok_bind ok_modify fun _ _ => ?_
    split
    · exact ok_pure (hx _ rfl)
    · exact ok_throw
  · split
    · exact ok_pure (hx _ rfl)
    · exact ok_throw

theorem ok_tracedLib {k : M (String × α)} (h : Ok k fun r => P r.2) :
    Ok (tracedLib fallback ante render k arrow) P := by
  unfold Eval.tracedLib
  refine ok_bind ok_modify fun _ _ => ?_
  refine ok_bind (ok_observe' h) fun x hx => ?_
  refine ok_bind ok_modify fun _ _ => ?_
  refine ok_bind ok_get fun s _ => ?_
  dsimp only
  split
  · refine ok_bind ok_modify fun _ _ => ?_
    refine ok_bind ok_modify fun _ _ => ?_
    split
    · exact ok_pure (hx _ rfl)
    · exact ok_throw
  · refine ok_bind ok_modify fun _ _ => ?_
    split
    · exact ok_pure (hx _ rfl)
    · exact ok_throw

theorem ok_tracedCases {k : M (String × Except Error α)} (h : Ok k fun r => ∀ a, r.2 = .ok a → P a) :
    Ok (tracedCases before ante render k arrow) P := by
  unfold Eval.tracedCases
  apply ok_tracedLib
  refine ok_bind h fun ⟨r, x⟩ hx => ?_
  dsimp only
  split
  · exact ok_pure (hx _ rfl)
  · exact ok_bind ok_modify fun _ _ => ok_throw

/-- A loop of `for`, with an invariant on the elements that remain. -/
theorem ok_forIn {f : τ → β → M (ForInStep β)} (I : List τ → β → Prop)
    (h : ∀ x xs b, I (x :: xs) b → Ok (f x b) fun r => match r with
      | .yield b' => I xs b'
      | .done b' => I [] b') :
    ∀ l b, I l b → Ok (forIn l b f) (I []) := by
  intro l
  induction l with
  | nil => intro b hb; exact ok_pure hb
  | cons x xs ih =>
    intro b hb
    simp only [List.forIn_cons]
    refine ok_bind (h x xs b hb) fun r hr => ?_
    cases r with
    | done b' => exact ok_pure hr
    | yield b' => exact ih b' hr

theorem ok_ite {p : Prop} [Decidable p] {a b : M α} (ha : p → Ok a P) (hb : ¬ p → Ok b P) :
    Ok (if p then a else b) P := by
  by_cases h : p
  · simp only [h, if_true]; exact ha h
  · simp only [h, if_false]; exact hb h

/-! ## The auxiliary functions -/

theorem ok_int32 : Ok (int32 n) fun v => Int32.inRange n ∧ v = .int n := by
  unfold int32; split
  · exact ok_pure ⟨‹_›, rfl⟩
  · exact ok_throw

theorem ok_readLoc : Ok (readLoc σ l) fun v => σ.read l = some v := by
  unfold readLoc; split
  · exact ok_pure ‹_›
  · exact ok_throw

theorem ok_pointee : Ok (pointee v) fun l => v = .loc l := by
  unfold pointee; split
  · exact ok_pure rfl
  · exact ok_throw
  · exact ok_throw

theorem ok_rd : Ok (rd σ r) fun v => r.rd σ = some v := by
  unfold rd; split
  · exact ok_pure rfl
  · exact ok_readLoc

theorem ok_lvalOf : Ok (lvalOf r) fun l => r = .lval l := by
  unfold lvalOf; split
  · exact ok_pure rfl
  · exact ok_throw

theorem ok_returns : Ok (returns who σ c ret ref) fun r => Semantics.Returns σ c ret ref r := by
  unfold returns; split
  · exact ok_bind ok_rd fun v hv => ok_pure (.val hv)
  · exact ok_bind ok_lvalOf fun l hl => ok_pure (by subst hl; exact .ref)
  · exact ok_pure .void
  · exact ok_throw

theorem ok_expectBool : Ok (expectBool w v) fun b => v = .bool b := by
  unfold expectBool; split
  · exact ok_pure rfl
  · exact ok_throw

theorem ok_unop : Ok (unop op v) fun w =>
    (op = .not ∧ ∃ b, v = .bool b ∧ w = .bool !b) ∨
    (op = .neg ∧ ∃ n, v = .int n ∧ Int32.inRange (-n) ∧ w = .int (-n)) := by
  unfold unop; split
  · exact ok_pure (.inl ⟨rfl, _, rfl, rfl⟩)
  · exact ok_mono ok_int32 fun _ ⟨h, hw⟩ => .inr ⟨rfl, _, rfl, h, hw⟩
  · exact ok_throw

/-- The premises of Arith, Div and Rel that follow the two operands. -/
def BinopOk (op : BinOp) (v₁ v₂ w : Val) : Prop :=
  (op.isArith ∧ ∃ n₁ n₂, v₁ = .int n₁ ∧ v₂ = .int n₂ ∧ Int32.inRange (op.arith n₁ n₂) ∧ w = .int (op.arith n₁ n₂)) ∨
  (∃ n₁ n₂ n, v₁ = .int n₁ ∧ v₂ = .int n₂ ∧ n₂ ≠ 0 ∧ op.divide n₁ n₂ = some n ∧ Int32.inRange n ∧ w = .int n) ∨
  (∃ b, op.compare v₁ v₂ = some b ∧ w = .bool b)

theorem ok_binop : Ok (binop op v₁ v₂) (BinopOk op v₁ v₂) := by
  unfold binop
  split <;> first
    | exact ok_throw
    | exact ok_pure (.inr (.inr ⟨_, rfl, rfl⟩))
    | exact ok_mono ok_int32 fun _ ⟨h, hw⟩ => .inl ⟨rfl, _, _, rfl, rfl, h, hw⟩
    | skip
  · rename_i a b hb
    exact ok_mono ok_int32 fun _ ⟨h, hw⟩ => .inr (.inl ⟨_, _, _, rfl, rfl, hb, rfl, h, hw⟩)
  · rename_i a b hb
    refine ok_bind ok_int32 fun _ ⟨hq, _⟩ => ok_mono ok_int32 fun _ ⟨h, hw⟩ =>
      .inr (.inl ⟨_, _, _, rfl, rfl, hb, ?_, h, hw⟩)
    simp [BinOp.divide, hq]

theorem ok_fnsOf : Ok (fnsOf n) fun F => Std.fnsOf n = some F := by
  unfold fnsOf; split
  · exact ok_pure ‹_›
  · exact ok_throw

theorem ok_libStep {k : Except Error (String × α)} :
    Ok (libStep ρ σ subject render k) fun a => ∃ r, k = .ok (r, a) := by
  unfold libStep
  apply ok_tracedLib
  cases k with
  | ok x => exact ok_pure ⟨x.1, rfl⟩
  | error e => exact ok_throw

theorem ok_target : Ok (target σ v) fun w => ∃ lt, v = .lib "std::function" [lt] ∧ σ.read lt = some w := by
  unfold target
  split
  · refine ok_bind ok_readLoc fun w hw => ?_
    split
    · exact ok_throw
    · exact ok_pure ⟨_, rfl, hw⟩
  · exact ok_throw

/-- The step of `captures?`, one free variable of the body. -/
def captureStep (ρ : Env) (σ : Store) (cap : List (String × Val)) (x : String) : Option (List (String × Val)) :=
  match ρ.lookup x with
  | none => some cap
  | some l => (σ.read l).map fun v => cap ++ [(x, v)]

theorem ok_captures : Ok (captures ρ σ ps b) fun cap => captures? ρ σ ps b = some cap := by
  unfold captures captures?
  dsimp only
  generalize ((List.flatMap Cmd.vars b).filter fun x => !ps.any fun y => y.name == x).eraseDups = names
  show Ok _ fun cap => names.foldlM (captureStep ρ σ) [] = some cap
  refine ok_bind (ok_forIn (fun rest c => names.foldlM (captureStep ρ σ) [] = rest.foldlM (captureStep ρ σ) c)
    ?_ names [] rfl) fun c hc => ok_pure (by rw [hc]; rfl)
  intro x xs c hI
  split
  · rename_i l hl
    refine ok_bind ok_readLoc fun v hv => ok_pure ?_
    rw [hI, List.foldlM_cons]
    simp [captureStep, hl, hv]
  · rename_i hl
    refine ok_pure ?_
    rw [hI, List.foldlM_cons]
    have : ρ.lookup x = none := by
      cases h : ρ.lookup x with
      | none => rfl
      | some l => exact absurd h (hl l)
    simp [captureStep, this]

/-! ## The library -/

theorem lib_new (hF : Std.fnsOf n = some F) (h : F.new ts vs σ = .ok (r, v, σ')) :
    ∃ M, moduleOf n = some M ∧ M.new ts vs σ v σ' := by
  unfold Std.fnsOf at hF
  split at hF <;> cases hF
  · refine ⟨_, rfl, ?_⟩
    simp only [Std.Vector.fns] at h
    split at h
    · rename_i t k
      by_cases hk : k < 0
      · simp [hk] at h; cases h
      · simp [hk] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact Vector.New.new (by omega) rfl rfl
    · cases h
  · refine ⟨_, rfl, ?_⟩
    simp only [Std.Function.fns] at h
    split at h
    · cases h; exact Function.New.target rfl rfl rfl
    · cases h; exact Function.New.empty rfl rfl
    · cases h
  · cases h

theorem lib_index (hF : Std.fnsOf n = some F) (h : F.index v w σ = .ok (r, l, σ')) :
    ∃ M, moduleOf n = some M ∧ M.index v w σ l σ' := by
  unfold Std.fnsOf at hF
  split at hF <;> cases hF
  · refine ⟨_, rfl, ?_⟩
    simp only [Std.Vector.fns] at h
    split at h
    · rename_i L ls i
      split at h
      · rename_i l' hl
        by_cases hi : i < 0
        · simp [hi] at h
        · simp [hi] at h
          obtain ⟨-, rfl, rfl⟩ := h
          exact Vector.Index.index (by omega) hl
      · cases h
    · cases h
  · cases h
  · cases h

theorem lib_delete (hF : Std.fnsOf n = some F) (h : F.delete v σ = .ok (r, σ')) :
    ∃ M, moduleOf n = some M ∧ M.delete v σ σ' := by
  unfold Std.fnsOf at hF
  split at hF <;> cases hF
  · refine ⟨_, rfl, ?_⟩
    simp only [Std.Vector.fns] at h
    split at h
    · cases h; exact Vector.Delete.delete
    · cases h
  · refine ⟨_, rfl, ?_⟩
    simp only [Std.Function.fns] at h
    split at h
    · cases h; exact Function.Delete.delete
    · cases h
  · cases h

theorem lib_call (hF : Std.fnsOf n = some F) (h : F.call vs σ = .ok (r, v, σ')) :
    ∃ M, moduleOf n = some M ∧ M.call vs σ v σ' := by
  unfold Std.fnsOf at hF
  split at hF <;> cases hF
  · cases h
  · cases h
  · refine ⟨_, rfl, ?_⟩
    simp only [Std.Assert.fns] at h
    split at h
    · cases h; exact Assert.Call.holds
    · cases h
    · cases h

/-! ## Facts about the relations and the store -/

theorem ok_throw_bind {f : α → M β} : Ok (throw e >>= f) Q :=
  ok_bind (P := fun _ => False) ok_throw fun _ h => h.elim

theorem free_reverse (σ : Store) (a b : List Loc) : σ.free (a.reverse ++ b) = σ.free (a ++ b) := by
  simp [Store.free]

theorem fresh_eq : fresh = Env.fresh := rfl

theorem Exec.block_env (h : Exec p ρ σ (.block cs) r ρ' σ') : ρ' = ρ := by cases h; rfl

theorem Exec.while_env (h : Exec p ρ σ (.while e b) r ρ' σ') : ρ' = ρ := by cases h <;> rfl

theorem funsNamed_nil {p : Program} (h : FunEnv.lookup p f = none) : p.funsNamed f = [] := by
  simp only [FunEnv.lookup, List.find?_eq_none] at h
  simp only [Program.funsNamed, List.filter_eq_nil_iff]
  exact h

theorem lookup_none_of_any {l : List (String × Nat)} (h : (l.any (·.1 == f)) = false) : l.lookup f = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp only [List.lookup]
    split
    · rename_i heq; simp_all
    · exact ih h.2

/-- The step of `Store.allocMany`. -/
def allocStep : List Loc × Store → Val → List Loc × Store :=
  fun (ls, σ) v => let (l, σ') := σ.alloc v; (ls ++ [l], σ')

theorem allocMany_eq (σ : Store) (vs : List Val) : σ.allocMany vs = vs.foldl allocStep ([], σ) := rfl

theorem allocMany_foldl (vs : List Val) (acc : List Loc) (σ : Store) :
    vs.foldl allocStep (acc, σ) = (acc ++ (vs.foldl allocStep ([], σ)).1, (vs.foldl allocStep ([], σ)).2) := by
  induction vs generalizing acc σ with
  | nil => simp
  | cons v vs ih =>
    have e₁ : allocStep (acc, σ) v = (acc ++ [(σ.alloc v).1], (σ.alloc v).2) := rfl
    have e₂ : allocStep ([], σ) v = ([(σ.alloc v).1], (σ.alloc v).2) := rfl
    rw [List.foldl_cons, List.foldl_cons, e₁, e₂, ih, ih [(σ.alloc v).1]]
    simp

theorem allocMany_cons (σ : Store) (v : Val) (vs : List Val) :
    σ.allocMany (v :: vs) = ((σ.alloc v).1 :: ((σ.alloc v).2.allocMany vs).1, ((σ.alloc v).2.allocMany vs).2) := by
  rw [allocMany_eq, List.foldl_cons, allocMany_foldl, allocMany_eq]
  rfl

theorem allocMany_append (σ : Store) (a b : List Val) :
    σ.allocMany (a ++ b) = ((σ.allocMany a).1 ++ ((σ.allocMany a).2.allocMany b).1, ((σ.allocMany a).2.allocMany b).2) := by
  induction a generalizing σ with
  | nil => simp [Store.allocMany]
  | cons v a ih => rw [List.cons_append, allocMany_cons, allocMany_cons, ih]; simp

theorem allocMany_length (σ : Store) (vs : List Val) : (σ.allocMany vs).1.length = vs.length := by
  induction vs generalizing σ with
  | nil => rfl
  | cons v vs ih => rw [allocMany_cons]; simp [ih]

theorem extendAll_append (ρ : Env) (a b : List String) (la lb : List Loc) (h : a.length = la.length) :
    ρ.extendAll (a ++ b) (la ++ lb) = (ρ.extendAll a la).extendAll b lb := by
  induction a generalizing ρ la with
  | nil => cases la <;> simp_all [Env.extendAll]
  | cons x a ih =>
    cases la with
    | nil => cases h
    | cons l la => simp only [List.cons_append, Env.extendAll]; exact ih _ _ (by simpa using h)

/-- The loops of `applyVals`, one allocation and one binding per element. -/
theorem foldl_alloc (xs : List τ) (nm : τ → String) (vl : τ → Val) (σ : Store) (ρ : Env) (acc : List Loc) :
    xs.foldl (fun s x => ((s.1.alloc (vl x)).2, s.2.1.extend (nm x) (s.1.alloc (vl x)).1, (s.1.alloc (vl x)).1 :: s.2.2))
        (σ, ρ, acc) =
      ((σ.allocMany (xs.map vl)).2, ρ.extendAll (xs.map nm) (σ.allocMany (xs.map vl)).1,
        (σ.allocMany (xs.map vl)).1.reverse ++ acc) := by
  induction xs generalizing σ ρ acc with
  | nil => simp [Store.allocMany, Env.extendAll]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, List.map_cons, List.map_cons, allocMany_cons]
    simp [Env.extendAll]

theorem ok_forIn_pure {l : List τ} {g : τ → β → β} :
    Ok (forIn l b fun x s => pure (ForInStep.yield (g x s)) : M β) fun r => r = l.foldl (fun s x => g x s) b := by
  refine ok_forIn (fun rest s => l.foldl (fun s x => g x s) b = rest.foldl (fun s x => g x s) s) ?_ l b rfl
    |> fun h => ok_mono h fun r hr => hr.symm
  intro x xs s hI
  exact ok_pure (by rw [hI]; rfl)

/-! ## The statement -/

/-- Soundness at fuel n, for every function of the evaluator. -/
def Sound (n : Nat) : Prop :=
  (∀ p ρ σ e, Ok (expr n p ρ σ e) fun r => Eval p ρ σ e r.1 r.2) ∧
  (∀ p s t m sig, Ok (resolve n p s t m sig) fun r => p.resolve s t m sig = some r) ∧
  (∀ p ρ σ recv arrow m es static sig, Ok (callMethod n p ρ σ recv arrow m es static sig)
    fun r => CallMethod p ρ σ recv arrow m es static sig r.1 r.2.1 r.2.2) ∧
  (∀ p ρ σ l ps body es ret ref who, Ok (runMember n p ρ σ l ps body es ret ref who)
    fun r => Member p ρ σ l ps body es ret ref r.1 r.2) ∧
  (∀ p ρ σ es, Ok (args n p ρ σ es) fun r => Args p ρ σ es r.1 r.2) ∧
  (∀ p σ v vs, Ok (applyVals n p σ v vs) fun r => Apply p σ v vs r.1 r.2) ∧
  (∀ p ρ σ v es, Ok (applyClosure n p ρ σ v es) fun r => ApplyArgs p ρ σ v es r.1 r.2) ∧
  (∀ σ l f, Ok (fieldLoc n σ l f) fun r => r.2 = σ ∧ ∃ c fs, σ.read l = some (.obj c fs) ∧ fs.lookup f = some r.1) ∧
  (∀ p ρ σ c, Ok (cmd n p ρ σ c) fun r => Exec p ρ σ c r.1 r.2.1 r.2.2) ∧
  (∀ p ρ σ cs, Ok (cmds n p ρ σ cs) fun r => Execs p ρ σ cs r.1 r.2.1 r.2.2)

/-- The binding of parameters, the loop of Call and of `runMember`. -/
theorem ok_bindLoop {p : Program}
    (hE : ∀ ρ σ e, Ok (expr n p ρ σ e) fun r => Eval p ρ σ e r.1 r.2)
    (hlen : ps.length = es.length) :
    Ok (forIn (ps.zip es) (σ, ρ₀, ([] : List Loc)) fun x s =>
        if x.fst.byRef = true then do
          let y ← expr n p ρ s.fst x.snd
          let l ← lvalOf y.fst
          pure (ForInStep.yield (y.snd, s.snd.fst.alias x.fst.name l, s.snd.snd))
        else do
          let y ← expr n p ρ s.fst x.snd
          let v ← rd y.snd y.fst
          pure (ForInStep.yield ((y.snd.alloc v).snd, s.snd.fst.extend x.fst.name (y.snd.alloc v).fst,
            (y.snd.alloc v).fst :: s.snd.snd)))
      fun s => Bind p ρ σ ρ₀ ps es s.2.1 s.1 s.2.2.reverse := by
  let I : List (Param × Expr) → Store × Env × List Loc → Prop := fun rest s =>
    ∀ ρ' σ' o, Bind p ρ s.1 s.2.1 (rest.map (·.1)) (rest.map (·.2)) ρ' σ' o →
      Bind p ρ σ ρ₀ ps es ρ' σ' (s.2.2.reverse ++ o)
  refine ok_mono (ok_forIn I ?_ _ _ ?_) fun s hs => by simpa using hs _ _ _ Bind.nil
  · rintro ⟨q, a⟩ xs ⟨σk, ρk, ok⟩ hI
    dsimp only
    split
    · rename_i hq
      refine ok_bind (hE _ _ _) fun ⟨r, σ₁⟩ hr => ok_bind ok_lvalOf fun l hl => ok_pure ?_
      dsimp only at hr hl ⊢
      subst hl
      intro ρ' σ' o hb
      exact hI _ _ _ (Bind.byRef hq hr hb)
    · rename_i hq
      refine ok_bind (hE _ _ _) fun ⟨r, σ₁⟩ hr => ok_bind ok_rd fun v hv => ok_pure ?_
      intro ρ' σ' o hb
      have := hI _ _ _ (Bind.byVal (by simpa using hq) hr hv rfl hb)
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append, Store.alloc] at this ⊢
      exact this
  · intro ρ' σ' o hb
    simpa [List.map_fst_zip, List.map_snd_zip, hlen] using hb

/-- A result of `returns` for a callee declared by value is a value. -/
theorem Returns.val_of_false (h : Returns σ c τ false r) : ∃ v, r = .val v := by
  cases h <;> exact ⟨_, rfl⟩

section
variable (ih : Sound n)
include ih

theorem Sound.args : ∀ p ρ σ es, Ok (args (n + 1) p ρ σ es) fun r => Args p ρ σ es r.1 r.2 := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hAC, hFl, hCm, hCs⟩ := ih
  intro p ρ σ es
  unfold Eval.args
  split
  · exact ok_pure .nil
  · exact ok_bind (hE _ _ _ _) fun ⟨r, σ₁⟩ h => ok_bind ok_rd fun v hv =>
      ok_bind (hA _ _ _ _) fun ⟨vs, σ₂⟩ hs => ok_pure (.cons h hv hs)

omit ih in
theorem Sound.fieldLoc : ∀ σ l f, Ok (fieldLoc (n + 1) σ l f)
    fun r => r.2 = σ ∧ ∃ c fs, σ.read l = some (.obj c fs) ∧ fs.lookup f = some r.1 := by
  intro σ l f
  unfold Eval.fieldLoc
  refine ok_bind ok_readLoc fun w hw => ?_
  split
  · split
    · exact ok_pure ⟨rfl, _, _, hw, ‹_›⟩
    · exact ok_throw
  · exact ok_throw

omit ih in
theorem Sound.resolve : ∀ p s t m sig, Ok (resolve (n + 1) p s t m sig) fun r => p.resolve s t m sig = some r := by
  intro p s t m sig
  unfold Eval.resolve
  cases sig <;>
  · dsimp only
    split
    · rename_i md k hs
      split
      · split
        · rename_i md' k' ht
          exact ok_pure (by simp only [Program.resolve, hs]; simp_all)
        · exact ok_throw
      · exact ok_pure (by simp only [Program.resolve, hs]; simp_all)
    · exact ok_throw

theorem Sound.cmds : ∀ p ρ σ cs, Ok (cmds (n + 1) p ρ σ cs) fun r => Execs p ρ σ cs r.1 r.2.1 r.2.2 := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hAC, hFl, hCm, hCs⟩ := ih
  intro p ρ σ cs
  unfold Eval.cmds
  split
  · exact ok_pure .nil
  · refine ok_bind (hCm _ _ _ _) fun ⟨r, ρ₁, σ₁⟩ h => ?_
    dsimp only at h ⊢
    cases r with
    | normal => exact ok_mono (hCs _ _ _ _) fun _ hs => .cons h hs
    | ret r => exact ok_pure (.consRet h)

theorem Sound.applyClosure : ∀ p ρ σ v es, Ok (applyClosure (n + 1) p ρ σ v es) fun r => ApplyArgs p ρ σ v es r.1 r.2 := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hAC, hFl, hCm, hCs⟩ := ih
  intro p ρ σ v es
  unfold Eval.applyClosure
  split
  · split
    · exact ok_throw_bind
    · rename_i hn
      exact ok_bind (hA _ _ _ _) fun ⟨vs, σ₁⟩ ha => ok_mono (hV _ _ _ _) fun _ hap =>
        .applyArgs rfl (by simpa using hn) ha hap
  · exact ok_throw

theorem Sound.applyVals : ∀ p σ v vs, Ok (applyVals (n + 1) p σ v vs) fun r => Apply p σ v vs r.1 r.2 := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hAC, hFl, hCm, hCs⟩ := ih
  intro p σ v vs
  unfold Eval.applyVals
  split
  · rename_i ps τ b cap
    split
    · exact ok_throw_bind
    · rename_i hn
      have hn : ps.length = vs.length := by simpa using hn
      refine ok_bind ok_forIn_pure fun s₁ hs₁ => ok_bind ok_forIn_pure fun s₂ hs₂ => ?_
      obtain rfl := hs₁.trans (foldl_alloc cap (·.1) (·.2) σ [] [])
      obtain rfl := hs₂.trans (foldl_alloc (ps.zip vs) (·.1.name) (·.2) _ _ _)
      have hv : (ps.zip vs).map (·.2) = vs := List.map_snd_zip (by omega)
      have hp : (ps.zip vs).map (·.1.name) = ps.map (·.name) :=
        calc (ps.zip vs).map (·.1.name) = ((ps.zip vs).map (·.1)).map Param.name := by simp [List.map_map]
          _ = ps.map (·.name) := by rw [List.map_fst_zip (by omega)]
      rw [hv, hp]
      generalize hA : σ.allocMany (cap.map (·.2)) = A
      generalize hB : A.2.allocMany vs = B
      refine ok_bind (hCs _ _ _ _) fun ⟨c, ρ'', σ₂⟩ hx => ok_bind ok_returns fun r hr => ok_bind ok_rd fun w hw => ?_
      have ha : σ.allocMany (cap.map (·.2) ++ vs) = (A.1 ++ B.1, B.2) := by
        rw [allocMany_append, hA, hB]
      have hρ : Env.extendAll (Env.extendAll [] (cap.map (·.1)) A.1) (ps.map (·.name)) B.1 =
          Env.extendAll [] (cap.map (·.1) ++ ps.map (·.name)) (A.1 ++ B.1) := by
        rw [extendAll_append]
        rw [← hA, allocMany_length]; simp
      have hfree (σ' : Store) (L : List Loc) : σ'.free (B.1.reverse ++ (A.1.reverse ++ []) ++ L) = σ'.free ((A.1 ++ B.1) ++ L) := by
        rw [← free_reverse]; simp
      dsimp only at hx hr hw ⊢
      obtain ⟨u, rfl⟩ := Returns.val_of_false hr
      simp only [Res.rd, Option.some.injEq] at hw
      subst hw
      rw [hρ] at hx ⊢
      exact ok_pure (by rw [hfree, ← fresh_eq.symm]; exact .apply hn ha rfl hx hr)
  · exact ok_throw

theorem Sound.runMember : ∀ p ρ σ l ps body es ret ref who,
    Ok (runMember (n + 1) p ρ σ l ps body es ret ref who) fun r => Member p ρ σ l ps body es ret ref r.1 r.2 := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hAC, hFl, hCm, hCs⟩ := ih
  intro p ρ σ l ps body es ret ref who
  unfold Eval.runMember
  dsimp only
  split
  · exact ok_throw_bind
  · rename_i hn
    have hn : ps.length = es.length := by simpa using hn
    refine ok_bind (ok_bindLoop (hE p) hn) fun ⟨σ₁, ρm, own⟩ hb => ?_
    refine ok_bind (hCs _ _ _ _) fun ⟨c, ρ', σ₂⟩ hx => ok_bind ok_returns fun r hr => ok_pure ?_
    dsimp only at hb hx hr ⊢
    rw [← free_reverse, ← fresh_eq.symm]; exact .member hn hb hx hr

theorem Sound.callMethod : ∀ p ρ σ recv arrow m es static sig,
    Ok (callMethod (n + 1) p ρ σ recv arrow m es static sig)
      fun r => CallMethod p ρ σ recv arrow m es static sig r.1 r.2.1 r.2.2 := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hAC, hFl, hCm, hCs⟩ := ih
  intro p ρ σ recv arrow m es static sig
  unfold Eval.callMethod
  dsimp only
  cases arrow
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ok_bind (hE _ _ _ _) fun ⟨r₀, σ₀⟩ h₀ => ok_bind ok_lvalOf fun l hl => ok_bind ok_readLoc fun w hw => ?_
    dsimp only at h₀ hl hw ⊢
    subst hl
    split
    · refine ok_bind (hR _ _ _ _ _) fun ⟨md, k⟩ hm => ?_
      refine ok_bind (hM _ _ _ _ _ _ _ _ _ _) fun ⟨r, σ'⟩ hc => ok_pure ?_
      exact .dot h₀ hw hm hc
    · exact ok_throw
  · simp only [↓reduceIte]
    refine ok_bind (hE _ _ _ _) fun ⟨r₀, σ₀⟩ h₀ => ok_bind ok_rd fun v hp =>
      ok_bind ok_pointee fun l hl => ok_bind ok_readLoc fun w hw => ?_
    dsimp only at h₀ hp hl hw ⊢
    subst hl
    split
    · refine ok_bind (hR _ _ _ _ _) fun ⟨md, k⟩ hm => ?_
      refine ok_bind (hM _ _ _ _ _ _ _ _ _ _) fun ⟨r, σ'⟩ hc => ok_pure ?_
      exact .arrow h₀ hp hw hm hc
    · exact ok_throw

theorem Sound.cmd : ∀ p ρ σ c, Ok (cmd (n + 1) p ρ σ c) fun r => Exec p ρ σ c r.1 r.2.1 r.2.2 := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hAC, hFl, hCm, hCs⟩ := ih
  intro p ρ σ c
  unfold Eval.cmd
  dsimp only
  split
  · exact ok_traced (ok_bind (hCs _ _ _ _) fun ⟨r, ρ', σ'⟩ h => ok_pure (.block h))
  · apply ok_tracedCases
    refine ok_bind (hE _ _ _ _) fun ⟨r, σ₁⟩ h₁ => ok_bind ok_rd fun v hv => ok_bind ok_expectBool fun b hb => ?_
    dsimp only at hb h₁ hv ⊢
    subst hb
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ok_bind (ok_observe (hCm _ _ _ _)) fun x hx => ok_pure fun ⟨r, ρ', σ'⟩ ha => by
        have h := hx _ ha; obtain rfl := Exec.block_env h; exact .ifF h₁ hv h
    · exact ok_bind (ok_observe (hCm _ _ _ _)) fun x hx => ok_pure fun ⟨r, ρ', σ'⟩ ha => by
        have h := hx _ ha; obtain rfl := Exec.block_env h; exact .ifT h₁ hv h
  · apply ok_tracedCases
    refine ok_bind (hE _ _ _ _) fun ⟨r, σ₁⟩ h₁ => ok_bind ok_rd fun v hv => ok_bind ok_expectBool fun b hb => ?_
    dsimp only at hb h₁ hv ⊢
    subst hb
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ok_pure fun a ha => by cases ha; exact .whileF h₁ hv
    · refine ok_bind (ok_observe (hCm _ _ _ _)) fun x hx => ?_
      split
      · exact ok_pure fun a ha => by cases ha
      · rename_i r' ρ₂ σ₂
        have hb := hx _ rfl
        obtain rfl := Exec.block_env hb
        exact ok_pure fun a ha => by cases ha; exact .whileRet h₁ hv hb
      · rename_i ρ₂ σ₂
        have hb := hx _ rfl
        obtain rfl := Exec.block_env hb
        exact ok_bind (ok_observe (hCm _ _ _ _)) fun y hy => ok_pure fun ⟨r, ρ', σ'⟩ ha => by
          have hw := hy _ ha; obtain rfl := Exec.while_env hw; exact .whileT h₁ hv hb hw
  · apply ok_traced
    refine ok_bind (hCm _ _ _ _) fun ⟨r₀, ρ₀, σ₀⟩ h₀ => ?_
    dsimp only at h₀ ⊢
    cases r₀ <;> dsimp only
    · exact ok_bind (hCm _ _ _ _) fun ⟨r, ρ₁, σ₁⟩ hw => ok_pure (by
        dsimp only at hw ⊢; obtain rfl := Exec.while_env hw; exact .forLoop h₀ hw)
    · exact ok_throw
  · exact ok_traced (ok_pure .retVoid)
  · exact ok_traced (ok_bind (hE _ _ _ _) fun ⟨r, σ'⟩ h => ok_pure (.ret h))
  · exact ok_traced (ok_bind (hE _ _ _ _) fun ⟨r, σ'⟩ h => ok_bind ok_rd fun v hv => ok_pure (.decl h hv rfl))
  · exact ok_traced (ok_bind (hE _ _ _ _) fun ⟨r, σ'⟩ h => ok_bind ok_lvalOf fun l hl => ok_pure (by
      dsimp only at h hl ⊢; subst hl; exact .declRef h))
  · exact ok_traced (ok_bind (hE _ _ _ _) fun ⟨r, σ'⟩ h => ok_bind ok_rd fun v hv => ok_pure (.declAuto h hv rfl))
  · apply ok_traced
    refine ok_bind (hE _ _ _ _) fun ⟨r₂, σ₁⟩ hr => ok_bind ok_rd fun v hv =>
      ok_bind (hE _ _ _ _) fun ⟨r, σ₂⟩ hl => ok_bind ok_lvalOf fun l hlv => ?_
    dsimp only at hr hv hl hlv ⊢
    subst hlv
    split
    · exact ok_throw_bind
    · rename_i hd
      exact ok_pure (.assign hr hv hl (by cases h : σ₂.read l <;> simp_all))
  · exact ok_traced (ok_bind (hE _ _ _ _) fun ⟨r, σ'⟩ h => ok_pure (.exprStmt h))
  · rename_i e st
    apply ok_traced
    refine ok_bind (hE _ _ _ _) fun ⟨r, σ₀⟩ h => ok_bind ok_rd fun v hv => ?_
    dsimp only at h hv ⊢
    split
    · exact ok_pure (.deleteNull h hv)
    · rename_i l
      split
      · exact ok_throw
      · rename_i L ls hread
        refine ok_bind ok_fnsOf fun F hF => ok_bind ok_libStep fun σ₁ ⟨r', hk⟩ => ok_pure ?_
        obtain ⟨M, hM, hd⟩ := lib_delete hF hk
        exact .deleteLib h hv hread hM hd
      · rename_i tag flds hread
        split
        · exact ok_throw_bind
        · rename_i hvd
          let I : List ClassDecl → Store → Prop := fun rest σk =>
            ∀ σ', Dtors p ρ σk l rest σ' → Dtors p ρ σ₀ l (p.chain tag) σ'
          refine ok_bind (ok_mono (ok_forIn I ?_ _ _ fun _ h => h) fun σk hk => hk _ .nil) fun σ₁ hd => ok_pure ?_
          · intro cd cds σk hI
            split
            · rename_i d hdt
              exact ok_bind (hM _ _ _ _ _ _ _ _ _ _) fun ⟨r', σ'⟩ hm => ok_pure fun σ'' hs => hI _ (.run hdt hm hs)
            · rename_i hdt
              exact ok_pure fun σ'' hs => hI _ (.skip (by revert hdt; cases cd.dtor <;> simp) hs)
          · refine .delete h hv hread ?_ hd
            by_cases hs : st.getD tag = tag
            · exact .inl hs
            · right; simp at hvd; exact hvd hs
      · exact ok_throw
    · exact ok_throw

theorem Sound.expr : ∀ p ρ σ e, Ok (expr (n + 1) p ρ σ e) fun r => Eval p ρ σ e r.1 r.2 := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hAC, hFl, hCm, hCs⟩ := ih
  intro p ρ σ e
  unfold Eval.expr
  dsimp only
  split
  · exact ok_traced (ok_bind ok_int32 fun _ ⟨h, hv⟩ => ok_pure (by subst hv; exact .lit h))
  · exact ok_traced (ok_pure .boolLit)
  · exact ok_traced (ok_pure .null)
  · -- Var, VarField
    split
    · exact ok_traced (ok_pure (.var ‹_›))
    · rename_i x hx
      apply ok_traced
      split
      · rename_i lt ht
        exact ok_bind (hFl _ _ _) fun ⟨lf, σ'⟩ ⟨hσ, c, fs, ho, hf⟩ => ok_pure (by
          dsimp only at hσ hf ⊢; subst hσ; exact .varField hx ht ho hf)
      · exact ok_throw
  · apply ok_traced
    split
    · exact ok_pure (.this ‹_›)
    · exact ok_throw
  · -- Deref
    apply ok_traced
    exact ok_bind (hE _ _ _ _) fun ⟨r, σ'⟩ h => ok_bind ok_rd fun v hv => ok_bind ok_pointee fun l hl =>
      ok_pure (by dsimp only at h hv hl ⊢; subst hl; exact .deref h hv)
  · -- Field
    apply ok_traced
    exact ok_bind (hE _ _ _ _) fun ⟨r, σ'⟩ h => ok_bind ok_lvalOf fun l hl =>
      ok_bind (hFl _ _ _) fun ⟨lf, σ''⟩ ⟨hσ, c, fs, ho, hf⟩ => ok_pure (by
        dsimp only at h hl hσ hf ⊢; subst hl hσ; exact .field h ho hf)
  · -- Arrow
    apply ok_traced
    exact ok_bind (hE _ _ _ _) fun ⟨r, σ'⟩ h => ok_bind ok_rd fun v hv => ok_bind ok_pointee fun l hl =>
      ok_bind (hFl _ _ _) fun ⟨lf, σ''⟩ ⟨hσ, c, fs, ho, hf⟩ => ok_pure (by
        dsimp only at h hv hl hσ hf ⊢; subst hl hσ; exact .arrow h hv ho hf)
  · -- Index
    apply ok_traced
    refine ok_bind (hE _ _ _ _) fun ⟨r₁, σ₁⟩ h₁ => ok_bind ok_rd fun v hv => ?_
    dsimp only at h₁ hv ⊢
    split
    · refine ok_bind (hE _ _ _ _) fun ⟨r₂, σ₂⟩ h₂ => ok_bind ok_rd fun w hw => ok_bind ok_fnsOf fun F hF =>
        ok_bind ok_libStep fun ⟨l, σ₃⟩ ⟨r, hk⟩ => ok_pure ?_
      obtain ⟨M, hM, hi⟩ := lib_index hF hk
      exact .index h₁ hv h₂ hw hM hi
    · exact ok_throw
  · -- New
    apply ok_traced
    split
    · exact ok_throw_bind
    · rename_i c es hc
      let I : List ClassDecl → Store → Prop := fun rest σk =>
        ∀ σ', Ctors p ρ σk ((σ.allocMany ((p.allFields c).map fun (f, _) => f.ty.default)).2.alloc
          (.obj c (((p.allFields c).map (·.1.name)).zip (σ.allocMany ((p.allFields c).map fun (f, _) => f.ty.default)).1))).1
          c rest es σ' →
        Ctors p ρ ((σ.allocMany ((p.allFields c).map fun (f, _) => f.ty.default)).2.alloc
          (.obj c (((p.allFields c).map (·.1.name)).zip (σ.allocMany ((p.allFields c).map fun (f, _) => f.ty.default)).1))).2
          ((σ.allocMany ((p.allFields c).map fun (f, _) => f.ty.default)).2.alloc
          (.obj c (((p.allFields c).map (·.1.name)).zip (σ.allocMany ((p.allFields c).map fun (f, _) => f.ty.default)).1))).1
          c (p.chain c).reverse es σ'
      refine ok_bind (ok_mono (ok_forIn I ?_ _ _ fun _ h => h) fun σk hk => hk _ .nil) fun σ₃ hk => ok_pure ?_
      · intro cd cds σk hI
        split
        · rename_i k hk
          exact ok_bind (hM _ _ _ _ _ _ _ _ _ _) fun ⟨r, σ'⟩ hm => ok_pure fun σ'' hs => hI _ (.run hk hm hs)
        · rename_i hk
          exact ok_pure fun σ'' hs => hI _ (.skip (by revert hk; cases cd.ctor <;> simp) hs)
      · exact .new (by simpa using hc) rfl rfl hk
  · -- MethodCall
    apply ok_traced
    exact ok_bind (hC _ _ _ _ _ _ _ _ _) fun ⟨md, r, σ'⟩ h => ok_pure (.methodCall h)
  · -- NewLib
    apply ok_traced
    split
    · refine ok_bind (hA _ _ _ _) fun ⟨vs, σ₁⟩ ha => ok_bind ok_fnsOf fun F hF =>
        ok_bind ok_libStep fun ⟨v, σ₂⟩ ⟨r, hk⟩ => ok_pure ?_
      obtain ⟨M, hM, hn⟩ := lib_new hF hk
      exact .newLib ha hM hn
    · exact ok_throw
  · -- Not, Neg
    apply ok_tracedLib
    refine ok_bind (hE _ _ _ _) fun ⟨r, σ₁⟩ h => ok_bind ok_rd fun v hv => ok_bind ok_unop fun w hw => ok_pure ?_
    dsimp only at h hv ⊢
    rcases hw with ⟨rfl, b, rfl, rfl⟩ | ⟨rfl, k, rfl, hr, rfl⟩
    · exact .not h hv
    · exact .neg h hv hr
  · -- And
    apply ok_tracedCases
    refine ok_bind (hE _ _ _ _) fun ⟨r₁, σ₁⟩ h₁ => ok_bind ok_rd fun v hv => ok_bind ok_expectBool fun b hb => ?_
    dsimp only at hb h₁ hv ⊢
    subst hb
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ok_pure fun a ha => by cases ha; exact .andF h₁ hv
    · refine ok_bind (ok_observe (P := fun a : Res × Store => ∃ r₂ w, Eval p ρ σ₁ _ r₂ a.2 ∧ r₂.rd a.2 = some w ∧ a.1 = .val w)
        (ok_bind (hE _ _ _ _) fun ⟨r₂, σ₂⟩ h₂ => ok_bind ok_rd fun w hw => ok_pure ⟨r₂, w, h₂, hw, rfl⟩)) fun x hx => ?_
      exact ok_pure fun ⟨a₁, a₂⟩ ha => by
        obtain ⟨r₂, w, h₂, hw, h⟩ := hx _ ha
        dsimp only at h h₂ hw ⊢; subst h; exact .andT h₁ hv h₂ hw
  · -- Or
    apply ok_tracedCases
    refine ok_bind (hE _ _ _ _) fun ⟨r₁, σ₁⟩ h₁ => ok_bind ok_rd fun v hv => ok_bind ok_expectBool fun b hb => ?_
    dsimp only at hb h₁ hv ⊢
    subst hb
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · refine ok_bind (ok_observe (P := fun a : Res × Store => ∃ r₂ w, Eval p ρ σ₁ _ r₂ a.2 ∧ r₂.rd a.2 = some w ∧ a.1 = .val w)
        (ok_bind (hE _ _ _ _) fun ⟨r₂, σ₂⟩ h₂ => ok_bind ok_rd fun w hw => ok_pure ⟨r₂, w, h₂, hw, rfl⟩)) fun x hx => ?_
      exact ok_pure fun ⟨a₁, a₂⟩ ha => by
        obtain ⟨r₂, w, h₂, hw, h⟩ := hx _ ha
        dsimp only at h h₂ hw ⊢; subst h; exact .orF h₁ hv h₂ hw
    · exact ok_pure fun a ha => by cases ha; exact .orT h₁ hv
  · -- Arith, Div, Rel
    apply ok_tracedLib
    refine ok_bind (hE _ _ _ _) fun ⟨r₁, σ₁⟩ h₁ => ok_bind ok_rd fun v₁ hv₁ =>
      ok_bind (hE _ _ _ _) fun ⟨r₂, σ₂⟩ h₂ => ok_bind ok_rd fun v₂ hv₂ => ok_bind ok_binop fun w hw => ok_pure ?_
    dsimp only at h₁ h₂ hv₁ hv₂ ⊢
    rcases hw with ⟨hop, n₁, n₂, rfl, rfl, hr, rfl⟩ | ⟨n₁, n₂, k, rfl, rfl, hz, hd, hr, rfl⟩ | ⟨b, hc, rfl⟩
    · exact .arith hop h₁ hv₁ h₂ hv₂ hr
    · exact .div h₁ hv₁ h₂ hv₂ hz hd hr
    · exact .rel h₁ hv₁ h₂ hv₂ hc
  · -- Cond
    apply ok_tracedCases
    refine ok_bind (hE _ _ _ _) fun ⟨r₁, σ₁⟩ h₁ => ok_bind ok_rd fun v hv => ok_bind ok_expectBool fun b hb => ?_
    dsimp only at hb h₁ hv ⊢
    subst hb
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ok_bind (ok_observe (hE _ _ _ _)) fun x hx => ok_pure fun a ha => .condF h₁ hv (hx a ha)
    · exact ok_bind (ok_observe (hE _ _ _ _)) fun x hx => ok_pure fun a ha => .condT h₁ hv (hx a ha)
  · -- CallFn on a variable, CallLib, CallThis and Call
    rename_i f es sig
    split
    · rename_i l hρ
      apply ok_traced
      refine ok_bind (hE _ _ _ _) fun ⟨r, σ₁⟩ h₁ => ok_bind ok_rd fun v hv => ok_bind ok_target fun w ⟨lt, hvt, hw⟩ =>
        ok_bind (hAC _ _ _ _ _) fun ⟨u, σ'⟩ ha => ok_pure ?_
      dsimp only at h₁ hv hvt ⊢
      subst hvt
      exact .callVar hρ h₁ hv hw ha
    · rename_i hρ
      split
      · rename_i hlib
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hlib
        apply ok_traced
        split
        · rename_i hd
          refine ok_bind (hA _ _ _ _) fun ⟨vs, σ₁⟩ ha => ok_bind ok_fnsOf fun F hF =>
            ok_bind ok_libStep fun ⟨v, σ₂⟩ ⟨r, hk⟩ => ok_pure ?_
          obtain ⟨M, hM, hc⟩ := lib_call hF hk
          exact .callLib hρ (funsNamed_nil hlib.1) (by simpa using hd) hM ha hc
        · exact ok_throw_bind
      · rename_i hlib
        split
        · rename_i hthis
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hthis
          obtain ⟨hf, lt, ht⟩ := hthis
          have hany : (p.libDecls.any (·.1 == f)) = false := by
            cases h : p.libDecls.any (·.1 == f) <;> simp_all
          have hl : p.libDecls.lookup f = none := lookup_none_of_any hany
          exact ok_mono (hE _ _ _ _) fun r h => .callThis hρ hf hl ht h
        · apply ok_traced
          split
          · rename_i fn hfn
            split
            · exact ok_throw_bind
            · rename_i hn
              have hn : fn.params.length = es.length := by simpa using hn
              refine ok_bind (ok_bindLoop (hE p) hn) fun ⟨σ₁, ρf, own⟩ hb => ?_
              refine ok_bind (hCs _ _ _ _) fun ⟨c, ρ', σ₂⟩ hx => ok_bind ok_returns fun r hr => ok_pure ?_
              dsimp only at hb hx hr ⊢
              rw [← free_reverse, ← fresh_eq.symm]; exact .call hρ hfn hn hb hx hr
          · exact ok_throw
  · -- CallFn
    apply ok_traced
    refine ok_bind (hE _ _ _ _) fun ⟨r, σ₁⟩ h₁ => ok_bind ok_rd fun v hv => ok_bind ok_target fun w ⟨lt, hvt, hw⟩ =>
      ok_bind (hAC _ _ _ _ _) fun ⟨u, σ'⟩ ha => ok_pure ?_
    dsimp only at h₁ hv hvt ⊢
    subst hvt
    exact .callFn h₁ hv hw ha
  · exact ok_traced (ok_bind ok_captures fun cap hc => ok_pure (.lambda hc))

end

theorem Sound.zero : Sound 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (unfold Eval.expr; exact ok_throw) | (unfold Eval.resolve; exact ok_throw)
    | (unfold Eval.callMethod; exact ok_throw) | (unfold Eval.runMember; exact ok_throw)
    | (unfold Eval.args; exact ok_throw) | (unfold Eval.applyVals; exact ok_throw)
    | (unfold Eval.applyClosure; exact ok_throw)
    | (unfold Eval.fieldLoc; exact ok_throw) | (unfold Eval.cmd; exact ok_throw)
    | (unfold Eval.cmds; exact ok_throw)

theorem Sound.succ (ih : Sound n) : Sound (n + 1) :=
  ⟨Sound.expr ih, Sound.resolve, Sound.callMethod ih, Sound.runMember ih, Sound.args ih,
   Sound.applyVals ih, Sound.applyClosure ih, Sound.fieldLoc, Sound.cmd ih, Sound.cmds ih⟩

/-- Soundness at every fuel. -/
theorem sound : ∀ n, Sound n
  | 0 => Sound.zero
  | n + 1 => Sound.succ (sound n)

/-- The result of an expression has a derivation of ρ, σ ⊢ e ⇒ r, σ′. -/
theorem expr_sound (h : res (expr n p ρ σ e) s = (.ok (r, σ'), s')) : Semantics.Eval p ρ σ e r σ' :=
  (sound n).1 p ρ σ e s _ s' h

/-- The result of a command has a derivation of ρ, σ ⊢ c ⇒ r, ρ′, σ′. -/
theorem cmd_sound (h : res (cmd n p ρ σ c) s = (.ok (r, ρ', σ'), s')) : Exec p ρ σ c r ρ' σ' :=
  (sound n).2.2.2.2.2.2.2.2.1 p ρ σ c s _ s' h

end CoreCpp.Eval

namespace CoreCpp

/-- The function `run` evaluates `main()` in the program `prepare` gives. -/
theorem run_eq : run p n = match prepare p with
    | .error r => .rejected r
    | .ok q => .ofResult (runMain q n) := by
  unfold run runWith runMain
  cases prepare p <;> rfl

/-- The theorem `interp_sound` of the blueprint, after `Stmt.interp_sound` of
Radix. A value of `main()` from the evaluator, with any fuel, is the result of
a derivation of p ⇒ v. -/
theorem interp_sound (h : runMain p n = .ok v) : Semantics.Runs p v := by
  unfold runMain evalMain at h
  rcases hr : (Eval.expr n p [] {} (.call "main" [] none)).run.run { enabled := false } with ⟨r, s'⟩
  rw [hr] at h
  cases r with
  | error e => cases h
  | ok a =>
    obtain ⟨w, σ'⟩ := a
    cases w with
    | val u =>
      simp only [Except.bind, Res.callValue, Except.ok.injEq] at h
      subst h
      exact ⟨σ', Eval.expr_sound hr⟩
    | lval l => simp [Except.bind, Res.callValue] at h

/-- `interp_sound` for `run`, whose subject is the program `prepare` gives. -/
theorem run_sound (hp : prepare p = .ok q) (h : run p n = .value v) : Semantics.Runs q v := by
  rw [run_eq, hp] at h
  exact interp_sound (Outcome.ofResult_eq_value.mp h)

end CoreCpp
