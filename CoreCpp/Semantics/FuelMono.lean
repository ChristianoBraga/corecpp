import CoreCpp.Eval

/-!
# Fuel monotonicity

The theorem `fuel_mono` of the blueprint. A result of the evaluator with fuel
n that is not `outOfFuel` is its result with any fuel m ≥ n, the trace and the
state of the monad included.

The proof compares the two runs by the relation `LeP bad c c'`, which states
that c' gives the result of c whenever that result is not `outOfFuel` and its
value is not `bad`. The predicate `bad` marks the values that hold a caught
`outOfFuel`, which the evaluator throws again later.
-/

namespace CoreCpp.Eval

/-- The result of a run of c from the state s. -/
abbrev res (c : M α) (s : TState) : Except Error α × TState := c.run.run s

/-- A result that carries no exhaustion of the fuel, neither as the error nor
as a value marked `bad`. -/
def Fine (bad : α → Prop) (r : Except Error α × TState) : Prop :=
  r.1 ≠ .error .outOfFuel ∧ ∀ a, r.1 = .ok a → ¬ bad a

/-- c' refines c, it gives the result of c whenever that result is fine. -/
def LeP (bad : α → Prop) (c c' : M α) : Prop :=
  ∀ s, Fine bad (res c s) → res c' s = res c s

/-- `LeP` with no value marked bad. -/
abbrev Le (c c' : M α) : Prop := LeP (fun _ => False) c c'

theorem res_bind (c : M α) (f : α → M β) (s : TState) :
    res (c >>= f) s = match res c s with
      | (.ok a, s₁) => res (f a) s₁
      | (.error e, s₁) => (.error e, s₁) := by
  simp only [res, ExceptT.run_bind, StateT.run_bind]
  rcases h : (c.run.run s) with ⟨r, s₁⟩
  cases r <;> rfl

theorem LeP.refl (c : M α) : LeP bad c c := fun _ _ => rfl

theorem LeP.mono {bad bad' : α → Prop} (h : LeP bad c c') (hb : ∀ a, bad a → bad' a) :
    LeP bad' c c' := fun s ⟨h₁, h₂⟩ => h s ⟨h₁, fun a ha hba => h₂ a ha (hb a hba)⟩

/-- Sequencing. The continuation of a bad value must end without a fine
result, as a throw of the caught error does. -/
theorem LeP.bind {bad₁ : α → Prop} {bad₂ : β → Prop} {c c' : M α} {f f' : α → M β}
    (hc : LeP bad₁ c c') (hf : ∀ a, ¬ bad₁ a → LeP bad₂ (f a) (f' a))
    (hbad : ∀ a, bad₁ a → ∀ s, ¬ Fine bad₂ (res (f a) s)) :
    LeP bad₂ (c >>= f) (c' >>= f') := by
  intro s hfine
  rw [res_bind] at hfine ⊢
  rw [res_bind]
  rcases hr : res c s with ⟨r, s₁⟩
  rw [hr] at hfine
  cases r with
  | error e =>
    have he : e ≠ .outOfFuel := by rintro rfl; exact hfine.1 rfl
    have : res c' s = res c s := hc s ⟨by simpa [hr] using he, by simp [hr]⟩
    rw [this, hr]
  | ok a =>
    by_cases hb : bad₁ a
    · exact absurd hfine (hbad a hb s₁)
    · have : res c' s = res c s := hc s ⟨by simp [hr], by simpa [hr] using hb⟩
      rw [this, hr]
      exact hf a hb s₁ hfine

/-- Sequencing with no bad value in the first computation. -/
theorem Le.bind {bad₂ : β → Prop} {c c' : M α} {f f' : α → M β}
    (hc : Le c c') (hf : ∀ a, LeP bad₂ (f a) (f' a)) :
    LeP bad₂ (c >>= f) (c' >>= f') :=
  LeP.bind hc (fun a _ => hf a) (fun _ h => h.elim)

theorem Le.toLeP (h : Le c c') : LeP bad c c' := fun s ⟨h₁, _⟩ => h s ⟨h₁, fun _ _ h => h⟩

theorem res_pure (a : α) (s : TState) : res (pure a : M α) s = (.ok a, s) := rfl

theorem res_modify (f : TState → TState) (s : TState) : res (modify f : M Unit) s = (.ok (), f s) := rfl

theorem res_get (s : TState) : res (get : M TState) s = (.ok s, s) := rfl

theorem res_throw (e : Error) (s : TState) : res (throw e : M α) s = (.error e, s) := rfl

theorem res_tryCatch (c : M α) (h : Error → M α) (s : TState) :
    res (tryCatch c h) s = match res c s with
      | (.ok a, s₁) => (.ok a, s₁)
      | (.error e, s₁) => res (h e) s₁ := by
  show StateT.run (ExceptT.tryCatch c h) s = _
  simp only [ExceptT.tryCatch, ExceptT.mk, StateT.run_bind, res, ExceptT.run]
  rcases (StateT.run c s) with ⟨r, s₁⟩
  cases r <;> rfl

/-- The run of c with its error caught as a value, the form of the premises
that `tracedCases` throws again. -/
abbrev observe (c : M α) : M (Except Error α) := tryCatch (Except.ok <$> c) (pure ∘ Except.error)

/-- The value that holds a caught exhaustion of the fuel. -/
abbrev Exhausted (x : Except Error α) : Prop := x = .error .outOfFuel

theorem res_observe (c : M α) (s : TState) :
    res (observe c) s = match res c s with
      | (.ok a, s₁) => (.ok (.ok a), s₁)
      | (.error e, s₁) => (.ok (.error e), s₁) := by
  rw [observe, res_tryCatch]
  have : res (Except.ok <$> c : M (Except Error α)) s = match res c s with
      | (.ok a, s₁) => ((.ok (.ok a) : Except Error (Except Error α)), s₁)
      | (.error e, s₁) => (.error e, s₁) := by
    rw [← bind_pure_comp, res_bind]
    rcases res c s with ⟨r, s₁⟩; cases r <;> rfl
  rw [this]
  rcases res c s with ⟨r, s₁⟩; cases r <;> rfl

theorem Le.observe (h : Le c c') : LeP Exhausted (observe c) (observe c') := by
  intro s ⟨_, h₂⟩
  rw [res_observe] at h₂ ⊢
  rw [res_observe]
  rcases hr : res c s with ⟨r, s₁⟩
  rw [hr] at h₂
  have : res c' s = res c s := by
    apply h s; rw [hr]
    cases r with
    | ok a => exact ⟨by simp, fun _ _ h => h⟩
    | error e =>
      refine ⟨?_, fun _ h _ => by cases h⟩
      intro he; cases he; exact h₂ _ rfl rfl
  rw [this, hr]

/-- The form of `traced` and `tracedLib`, which catch the error of the body. -/
theorem Le.observe' (h : Le c c') :
    LeP Exhausted (tryCatch (do let a ← c; pure (Except.ok a)) (fun e => pure (Except.error e)))
      (tryCatch (do let a ← c'; pure (Except.ok a)) (fun e => pure (Except.error e))) := by
  have h' := Le.observe h
  simp only [bind_pure_comp]
  exact h'

theorem Le.traced (h : Le k k') : Le (traced rule ante render k arrow) (traced rule ante render k' arrow) := by
  unfold Eval.traced
  apply Le.bind (LeP.refl _); intro
  apply LeP.bind (Le.observe' h) (fun _ _ => LeP.refl _)
  rintro _ rfl s ⟨hs, _⟩
  apply hs
  simp only [res_bind, res_modify, res_get]
  split <;> simp [res_bind, res_modify, res_throw]

theorem Le.tracedLib {k k' : M (String × α)} (h : Le k k') :
    Le (tracedLib fallback ante render k arrow) (tracedLib fallback ante render k' arrow) := by
  unfold Eval.tracedLib
  apply Le.bind (LeP.refl _); intro
  apply LeP.bind (Le.observe' h) (fun _ _ => LeP.refl _)
  rintro _ rfl s ⟨hs, _⟩
  apply hs
  simp only [res_bind, res_modify, res_get]
  split <;> simp [res_bind, res_modify, res_throw]

/-- The premises of `tracedCases` give the rule and the result, which may hold
a caught error. -/
abbrev CaseExhausted (p : String × Except Error α) : Prop := p.2 = .error .outOfFuel

theorem LeP.tracedCases {k k' : M (String × Except Error α)} (h : LeP CaseExhausted k k') :
    Le (tracedCases before ante render k arrow) (tracedCases before ante render k' arrow) := by
  unfold Eval.tracedCases
  apply Le.tracedLib
  apply LeP.bind h (fun _ _ => LeP.refl _)
  rintro ⟨r, x⟩ hx s ⟨hs, _⟩
  simp only [CaseExhausted] at hx
  subst hx
  apply hs
  simp [res_bind, res_modify, res_throw]

theorem Le.forIn {l : List τ} {f f' : τ → β → M (ForInStep β)} (h : ∀ x b, Le (f x b) (f' x b)) :
    ∀ b, Le (forIn l b f) (forIn l b f') := by
  induction l with
  | nil => intro b; exact LeP.refl _
  | cons x xs ih =>
    intro b
    simp only [List.forIn_cons]
    apply Le.bind (h x b)
    intro step
    cases step with
    | done => exact LeP.refl _
    | yield b' => exact ih b'

theorem Le.outOfFuel : Le (throw .outOfFuel : M α) c' := fun _ ⟨h, _⟩ => absurd rfl h

theorem LeP.ite {p : Prop} [Decidable p] {a a' b b' : M α}
    (ha : p → LeP bad a a') (hb : ¬ p → LeP bad b b') :
    LeP bad (if p then a else b) (if p then a' else b') := by
  by_cases h : p
  · simp only [h, if_true]; exact ha h
  · simp only [h, if_false]; exact hb h

/-- Sequencing after a caught error. The continuation of the caught
exhaustion of the fuel must end without a fine result. -/
theorem LeP.bind_observe {bad : β → Prop} {c c' : M α} {f f' : Except Error α → M β}
    (h : Le c c') (hf : ∀ x, ¬ Exhausted x → LeP bad (f x) (f' x))
    (hb : ∀ s, ¬ Fine bad (res (f (.error .outOfFuel)) s)) :
    LeP bad (observe c >>= f) (observe c' >>= f') :=
  LeP.bind (Le.observe h) hf (fun _ hx => by subst hx; exact hb)

/-- The statement for every function of the evaluator, fuel n against fuel m. -/
def Mono (n m : Nat) : Prop :=
  (∀ fs ρ σ e, Le (expr n fs ρ σ e) (expr m fs ρ σ e)) ∧
  (∀ fs s t k sig, Le (resolve n fs s t k sig) (resolve m fs s t k sig)) ∧
  (∀ fs ρ σ recv arrow k es static sig,
    Le (callMethod n fs ρ σ recv arrow k es static sig) (callMethod m fs ρ σ recv arrow k es static sig)) ∧
  (∀ fs ρ σ l ps body es ret who,
    Le (runMember n fs ρ σ l ps body es ret who) (runMember m fs ρ σ l ps body es ret who)) ∧
  (∀ fs ρ σ es, Le (args n fs ρ σ es) (args m fs ρ σ es)) ∧
  (∀ fs σ v vs, Le (applyVals n fs σ v vs) (applyVals m fs σ v vs)) ∧
  (∀ fs ρ σ v es, Le (applyClosure n fs ρ σ v es) (applyClosure m fs ρ σ v es)) ∧
  (∀ fs ρ σ e, Le (lval n fs ρ σ e) (lval m fs ρ σ e)) ∧
  (∀ σ l f, Le (fieldLoc n σ l f) (fieldLoc m σ l f)) ∧
  (∀ fs ρ σ c, Le (cmd n fs ρ σ c) (cmd m fs ρ σ c)) ∧
  (∀ fs ρ σ cs, Le (cmds n fs ρ σ cs) (cmds m fs ρ σ cs))

set_option hygiene false in
/-- One step of the comparison of two bodies that differ in the fuel of the
recursive calls only. -/
macro "mono_step" : tactic => `(tactic| first
  | with_reducible exact LeP.refl _
  | contradiction
  | (with_reducible apply Le.toLeP
     with_reducible first | apply hE | apply hR | apply hC | apply hM | apply hA | apply hV
                          | apply hF | apply hL | apply hFl | apply hCm | apply hCs)
  | with_reducible apply Le.traced
  | with_reducible apply Le.tracedLib
  | with_reducible apply LeP.tracedCases
  | (with_reducible apply Le.forIn; intro _ _)
  | (intro s hfine; simp [Fine, res_pure, res_bind, res_throw, res_modify] at hfine; done)
  | with_reducible apply LeP.bind_observe
  | with_reducible apply Le.bind
  | (with_reducible intro _)
  | (with_reducible apply LeP.ite <;> intro _)
  | split
  | dsimp only)

section
variable (ih : Mono n m)
include ih

theorem Mono.expr : ∀ fs ρ σ e, Le (expr (n + 1) fs ρ σ e) (expr (m + 1) fs ρ σ e) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs ρ σ e; unfold Eval.expr; repeat' mono_step

theorem Mono.resolve : ∀ fs s t k sig, Le (resolve (n + 1) fs s t k sig) (resolve (m + 1) fs s t k sig) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs s t k sig; unfold Eval.resolve; repeat' mono_step

theorem Mono.callMethod : ∀ fs ρ σ recv arrow k es static sig,
    Le (callMethod (n + 1) fs ρ σ recv arrow k es static sig) (callMethod (m + 1) fs ρ σ recv arrow k es static sig) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs ρ σ recv arrow k es static sig; unfold Eval.callMethod; repeat' mono_step

theorem Mono.runMember : ∀ fs ρ σ l ps body es ret who,
    Le (runMember (n + 1) fs ρ σ l ps body es ret who) (runMember (m + 1) fs ρ σ l ps body es ret who) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs ρ σ l ps body es ret who; unfold Eval.runMember; repeat' mono_step

theorem Mono.args : ∀ fs ρ σ es, Le (args (n + 1) fs ρ σ es) (args (m + 1) fs ρ σ es) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs ρ σ es; unfold Eval.args; repeat' mono_step

theorem Mono.applyVals : ∀ fs σ v vs, Le (applyVals (n + 1) fs σ v vs) (applyVals (m + 1) fs σ v vs) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs σ v vs; unfold Eval.applyVals; repeat' mono_step

theorem Mono.applyClosure : ∀ fs ρ σ v es, Le (applyClosure (n + 1) fs ρ σ v es) (applyClosure (m + 1) fs ρ σ v es) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs ρ σ v es; unfold Eval.applyClosure; repeat' mono_step

theorem Mono.lval : ∀ fs ρ σ e, Le (lval (n + 1) fs ρ σ e) (lval (m + 1) fs ρ σ e) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs ρ σ e; unfold Eval.lval; repeat' mono_step

theorem Mono.fieldLoc : ∀ σ l f, Le (fieldLoc (n + 1) σ l f) (fieldLoc (m + 1) σ l f) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro σ l f; unfold Eval.fieldLoc; repeat' mono_step

theorem Mono.cmd : ∀ fs ρ σ c, Le (cmd (n + 1) fs ρ σ c) (cmd (m + 1) fs ρ σ c) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs ρ σ c; unfold Eval.cmd; repeat' mono_step

theorem Mono.cmds : ∀ fs ρ σ cs, Le (cmds (n + 1) fs ρ σ cs) (cmds (m + 1) fs ρ σ cs) := by
  obtain ⟨hE, hR, hC, hM, hA, hV, hF, hL, hFl, hCm, hCs⟩ := ih
  intro fs ρ σ cs; unfold Eval.cmds; repeat' mono_step

end

theorem Mono.zero (m : Nat) : Mono 0 m := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    first
    | (unfold Eval.expr; exact Le.outOfFuel) | (unfold Eval.resolve; exact Le.outOfFuel)
    | (unfold Eval.callMethod; exact Le.outOfFuel) | (unfold Eval.runMember; exact Le.outOfFuel)
    | (unfold Eval.args; exact Le.outOfFuel) | (unfold Eval.applyVals; exact Le.outOfFuel)
    | (unfold Eval.applyClosure; exact Le.outOfFuel) | (unfold Eval.lval; exact Le.outOfFuel)
    | (unfold Eval.fieldLoc; exact Le.outOfFuel) | (unfold Eval.cmd; exact Le.outOfFuel)
    | (unfold Eval.cmds; exact Le.outOfFuel)

theorem Mono.succ (ih : Mono n m) : Mono (n + 1) (m + 1) :=
  ⟨Mono.expr ih, Mono.resolve ih, Mono.callMethod ih, Mono.runMember ih, Mono.args ih,
   Mono.applyVals ih, Mono.applyClosure ih, Mono.lval ih, Mono.fieldLoc ih, Mono.cmd ih, Mono.cmds ih⟩

/-- Every function of the evaluator with fuel n against fuel m ≥ n. -/
theorem mono : ∀ n m, n ≤ m → Mono n m
  | 0, m, _ => Mono.zero m
  | n + 1, m + 1, h => Mono.succ (mono n m (by omega))
  | _ + 1, 0, h => absurd h (by omega)

end CoreCpp.Eval

namespace CoreCpp

/-- The theorem `fuel_mono` of the blueprint. A run of a program that does not
exhaust the fuel n gives the same result with any fuel m ≥ n, the trace
included. -/
theorem runWith_fuel_mono {p : Program} {n m : Nat} (hnm : n ≤ m)
    (h : (runWith trace p n).1 ≠ .error .outOfFuel) : runWith trace p m = runWith trace p n := by
  unfold runWith at h ⊢
  have hle := (Eval.mono n m hnm).1 ((Typing.annotate p).toOption.getD p) [] {} (.call "main" [] none)
  have := hle { enabled := trace } ⟨by
    intro he; apply h
    show Except.map _ (Eval.res _ _).1 = _
    rw [he]; rfl, fun _ _ h => h⟩
  simp only [Eval.res] at this
  simp only [StateT.run, ExceptT.run] at this ⊢
  rw [this]

/-- `run` with fuel n that does not exhaust it gives its result with any fuel m ≥ n. -/
theorem run_fuel_mono {p : Program} {n m : Nat} (hnm : n ≤ m)
    (h : run p n ≠ .error .outOfFuel) : run p m = run p n := by
  unfold run at h ⊢
  rw [runWith_fuel_mono hnm h]

end CoreCpp
