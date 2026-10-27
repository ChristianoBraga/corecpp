import CoreCpp.Semantics.Dynamic

/-!
# Determinism of the dynamic semantics

The theorem `determinism` of the blueprint. Two derivations of one judgement,
from the same configuration and the same subject, give the same result. The
proof is one mutual structural recursion on the first derivation, with a case
analysis of the second. The rules of one subject have mutually exclusive
premises, and every allocation is the function `Store.alloc`, so each case
either matches the same rule or contradicts a premise.
-/

namespace CoreCpp.Semantics

/-- A body has at most one value for its control and its result type. -/
theorem Returns.det : Returns r τ v₁ → Returns r τ v₂ → v₁ = v₂
  | .ret, .ret => rfl
  | .void, .void => rfl

/-- The function named f with a chosen signature is also found by name. -/
theorem lookupSig_lookup {p : Program} (h : FunEnv.lookupSig p f sig = some fn) :
    (FunEnv.lookup p f).isSome := by
  unfold FunEnv.lookupSig at h
  split at h
  · have hm := List.mem_of_find?_eq_some h
    simp only [Program.funsNamed, List.mem_filter] at hm
    simp only [FunEnv.lookup, List.find?_isSome]
    exact ⟨fn, hm.1, hm.2⟩
  · simp [h]

/-- A name the headers declare has an entry in `libDecls`. -/
theorem libDecls_lookup {l : List (String × Nat)} (h : (f, k) ∈ l) : l.lookup f ≠ none := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    simp only [List.lookup]
    split
    · simp
    · rename_i hne
      cases h with
      | head => simp at hne
      | tail _ h => exact ih h

/-- The arithmetic, the division and the relational operators are disjoint. -/
theorem divide_of_isArith {op : BinOp} {a b : Int} (h : op.isArith = true) : op.divide a b = none := by
  cases op <;> simp_all [BinOp.isArith, BinOp.divide]

theorem compare_of_isArith {op : BinOp} {v w : Val} (h : op.isArith = true) : op.compare v w = none := by
  cases op <;> simp_all [BinOp.isArith, BinOp.compare]

theorem compare_of_divide {op : BinOp} {a b n : Int} {v w : Val} (h : op.divide a b = some n) : op.compare v w = none := by
  cases op <;> simp_all [BinOp.divide, BinOp.compare]

/-! ## The relations of the library -/

theorem Module.new_det (hM : moduleOf L = some M)
    (h₁ : M.new ts vs σ v₁ σ₁) (h₂ : M.new ts vs σ v₂ σ₂) : v₁ = v₂ ∧ σ₁ = σ₂ := by
  unfold moduleOf at hM
  split at hM <;> cases hM
  · cases h₁ with
    | new hk ha ho => cases h₂ with
      | new hk' ha' ho' =>
        rw [ha] at ha'; cases ha'; rw [ho] at ho'; cases ho'; exact ⟨rfl, rfl⟩
  · cases h₁ with
    | target hw ht ho => cases h₂ with
      | target hw' ht' ho' =>
        rw [ht] at ht'; cases ht'; rw [ho] at ho'; cases ho'; exact ⟨rfl, rfl⟩
    | empty ht ho => cases h₂ with
      | empty ht' ho' =>
        rw [ht] at ht'; cases ht'; rw [ho] at ho'; cases ho'; exact ⟨rfl, rfl⟩
  · cases h₁

theorem Module.index_det (hM : moduleOf L = some M)
    (h₁ : M.index v i σ ℓ₁ σ₁) (h₂ : M.index v i σ ℓ₂ σ₂) : ℓ₁ = ℓ₂ ∧ σ₁ = σ₂ := by
  unfold moduleOf at hM
  split at hM <;> cases hM
  · cases h₁ with
    | index hi hl => cases h₂ with
      | index hi' hl' => rw [hl] at hl'; cases hl'; exact ⟨rfl, rfl⟩
  · cases h₁
  · cases h₁

theorem Module.delete_det (hM : moduleOf L = some M)
    (h₁ : M.delete v σ σ₁) (h₂ : M.delete v σ σ₂) : σ₁ = σ₂ := by
  unfold moduleOf at hM
  split at hM <;> cases hM
  · cases h₁; cases h₂; rfl
  · cases h₁; cases h₂; rfl
  · cases h₁

theorem Module.call_det (hM : moduleOf f = some M)
    (h₁ : M.call vs σ v₁ σ₁) (h₂ : M.call vs σ v₂ σ₂) : v₁ = v₂ ∧ σ₁ = σ₂ := by
  unfold moduleOf at hM
  split at hM <;> cases hM
  · cases h₁
  · cases h₁
  · cases h₁; cases h₂; exact ⟨rfl, rfl⟩

/-! ## The judgements of the language -/

mutual

theorem Eval.det : Eval p ρ σ e v₁ σ₁ → Eval p ρ σ e v₂ σ₂ → v₁ = v₂ ∧ σ₁ = σ₂
  | .lit _, h₂ => by
    cases h₂ with
    | lit => exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
  | .boolLit, h₂ => by
    cases h₂ with
    | boolLit => exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
  | .null, h₂ => by
    cases h₂ with
    | null => exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
  | .var hl hr, h₂ => by
    cases h₂ with
    | var hl' hr' =>
      obtain ⟨rfl, -⟩ := LEval.det hl hl'
      rw [hr] at hr'; cases hr'; exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
  | .this h, h₂ => by
    cases h₂ with
    | this h' => rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
  | .read hp hl hr, h₂ => by
    cases h₂ with
    | read hp' hl' hr' =>
      obtain ⟨rfl, rfl⟩ := LEval.det hl hl'
      rw [hr] at hr'; cases hr'; exact ⟨rfl, rfl⟩
    | _ => simp [Expr.isPlace] at hp
  | .new hc ha ho hk, h₂ => by
    cases h₂ with
    | new hc' ha' ho' hk' =>
      rw [ha] at ha'; cases ha'; rw [ho] at ho'; cases ho'
      exact ⟨rfl, Ctors.det hk hk'⟩
    | read hp => simp [Expr.isPlace] at hp
  | .methodCall h hr, h₂ => by
    cases h₂ with
    | methodCall h' hr' =>
      obtain ⟨rfl, rfl, rfl⟩ := CallMethod.det h h'; exact ⟨rfl, rfl⟩
    | methodCallRef h' hr' hv' =>
      obtain ⟨rfl, rfl, rfl⟩ := CallMethod.det h h'; rw [hr] at hr'; cases hr'
    | read hp => simp [Expr.isPlace] at hp
  | .methodCallRef h hr hv, h₂ => by
    cases h₂ with
    | methodCall h' hr' =>
      obtain ⟨rfl, rfl, rfl⟩ := CallMethod.det h h'; rw [hr] at hr'; cases hr'
    | methodCallRef h' hr' hv' =>
      obtain ⟨rfl, h, rfl⟩ := CallMethod.det h h'; cases h
      rw [hv] at hv'; cases hv'; exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
  | .newLib ha hM hn, h₂ => by
    cases h₂ with
    | newLib ha' hM' hn' =>
      obtain ⟨rfl, rfl⟩ := Args.det ha ha'
      rw [hM] at hM'; cases hM'
      exact Module.new_det hM hn hn'
    | read hp => simp [Expr.isPlace] at hp
  | .not h, h₂ => by
    cases h₂ with
    | not h' => obtain ⟨h, rfl⟩ := Eval.det h h'; cases h; exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
  | .neg h hr, h₂ => by
    cases h₂ with
    | neg h' hr' => obtain ⟨h, rfl⟩ := Eval.det h h'; cases h; exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
  | .arith hop a₁ a₂ hr, h₂ => by
    cases h₂ with
    | arith hop' b₁ b₂ hr' =>
      obtain ⟨h, rfl⟩ := Eval.det a₁ b₁; cases h
      obtain ⟨h, rfl⟩ := Eval.det a₂ b₂; cases h
      exact ⟨rfl, rfl⟩
    | div b₁ b₂ hz hd => rw [divide_of_isArith hop] at hd; cases hd
    | rel b₁ b₂ hc => rw [compare_of_isArith hop] at hc; cases hc
    | andF => simp [BinOp.isArith] at hop
    | andT => simp [BinOp.isArith] at hop
    | orT => simp [BinOp.isArith] at hop
    | orF => simp [BinOp.isArith] at hop
    | read hp => simp [Expr.isPlace] at hp
  | .div a₁ a₂ hz hd hr, h₂ => by
    cases h₂ with
    | arith hop' b₁ b₂ hr' => rw [divide_of_isArith hop'] at hd; cases hd
    | div b₁ b₂ hz' hd' hr' =>
      obtain ⟨h, rfl⟩ := Eval.det a₁ b₁; cases h
      obtain ⟨h, rfl⟩ := Eval.det a₂ b₂; cases h
      rw [hd] at hd'; cases hd'; exact ⟨rfl, rfl⟩
    | rel b₁ b₂ hc => rw [compare_of_divide hd] at hc; cases hc
    | andF => simp [BinOp.divide] at hd
    | andT => simp [BinOp.divide] at hd
    | orT => simp [BinOp.divide] at hd
    | orF => simp [BinOp.divide] at hd
    | read hp => simp [Expr.isPlace] at hp
  | .rel a₁ a₂ hc, h₂ => by
    cases h₂ with
    | arith hop' b₁ b₂ hr' => rw [compare_of_isArith hop'] at hc; cases hc
    | div b₁ b₂ hz hd => rw [compare_of_divide hd] at hc; cases hc
    | rel b₁ b₂ hc' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a₁ b₁
      obtain ⟨rfl, rfl⟩ := Eval.det a₂ b₂
      rw [hc] at hc'; cases hc'; exact ⟨rfl, rfl⟩
    | andF => simp [BinOp.compare] at hc
    | andT => simp [BinOp.compare] at hc
    | orT => simp [BinOp.compare] at hc
    | orF => simp [BinOp.compare] at hc
    | read hp => simp [Expr.isPlace] at hp
  | .andF a, h₂ => by
    cases h₂ with
    | arith hop => simp [BinOp.isArith] at hop
    | div _ _ _ hd => simp [BinOp.divide] at hd
    | rel _ _ hc => simp [BinOp.compare] at hc
    | andF b => obtain ⟨-, rfl⟩ := Eval.det a b; exact ⟨rfl, rfl⟩
    | andT b => obtain ⟨h, -⟩ := Eval.det a b; cases h
    | read hp => simp [Expr.isPlace] at hp
  | .andT a₁ a₂, h₂ => by
    cases h₂ with
    | arith hop => simp [BinOp.isArith] at hop
    | div _ _ _ hd => simp [BinOp.divide] at hd
    | rel _ _ hc => simp [BinOp.compare] at hc
    | andF b => obtain ⟨h, -⟩ := Eval.det a₁ b; cases h
    | andT b₁ b₂ =>
      obtain ⟨-, rfl⟩ := Eval.det a₁ b₁
      exact Eval.det a₂ b₂
    | read hp => simp [Expr.isPlace] at hp
  | .orT a, h₂ => by
    cases h₂ with
    | arith hop => simp [BinOp.isArith] at hop
    | div _ _ _ hd => simp [BinOp.divide] at hd
    | rel _ _ hc => simp [BinOp.compare] at hc
    | orT b => obtain ⟨-, rfl⟩ := Eval.det a b; exact ⟨rfl, rfl⟩
    | orF b => obtain ⟨h, -⟩ := Eval.det a b; cases h
    | read hp => simp [Expr.isPlace] at hp
  | .orF a₁ a₂, h₂ => by
    cases h₂ with
    | arith hop => simp [BinOp.isArith] at hop
    | div _ _ _ hd => simp [BinOp.divide] at hd
    | rel _ _ hc => simp [BinOp.compare] at hc
    | orT b => obtain ⟨h, -⟩ := Eval.det a₁ b; cases h
    | orF b₁ b₂ =>
      obtain ⟨-, rfl⟩ := Eval.det a₁ b₁
      exact Eval.det a₂ b₂
    | read hp => simp [Expr.isPlace] at hp
  | .condT a₁ a₂, h₂ => by
    cases h₂ with
    | condT b₁ b₂ =>
      obtain ⟨-, rfl⟩ := Eval.det a₁ b₁
      exact Eval.det a₂ b₂
    | condF b => obtain ⟨h, -⟩ := Eval.det a₁ b; cases h
    | read hp => simp [Expr.isPlace] at hp
  | .condF a₁ a₃, h₂ => by
    cases h₂ with
    | condT b => obtain ⟨h, -⟩ := Eval.det a₁ b; cases h
    | condF b₁ b₃ =>
      obtain ⟨-, rfl⟩ := Eval.det a₁ b₁
      exact Eval.det a₃ b₃
    | read hp => simp [Expr.isPlace] at hp
  | .call hρ hf hn hb hx hr, h₂ => by
    cases h₂ with
    | call hρ' hf' hn' hb' hx' hr' =>
      rw [hf] at hf'; cases hf'
      obtain ⟨rfl, rfl, rfl⟩ := Bind.det hb hb'
      obtain ⟨rfl, rfl, rfl⟩ := Execs.det hx hx'
      rw [Returns.det hr hr']; exact ⟨rfl, rfl⟩
    | callVar hρ' => rw [hρ] at hρ'; cases hρ'
    | callThis _ hf' => have := lookupSig_lookup hf; rw [hf'] at this; cases this
    | callLib _ hf' => rw [hf] at hf'; cases hf'
    | read hp => simp [Expr.isPlace] at hp
  | .callVar hρ hv ht ha, h₂ => by
    cases h₂ with
    | call hρ' => rw [hρ] at hρ'; cases hρ'
    | callVar hρ' hv' ht' ha' =>
      obtain ⟨h, rfl⟩ := Eval.det hv hv'; cases h
      rw [ht] at ht'; cases ht'
      exact ApplyArgs.det ha ha'
    | callThis hρ' => rw [hρ] at hρ'; cases hρ'
    | callLib hρ' => rw [hρ] at hρ'; cases hρ'
    | read hp => simp [Expr.isPlace] at hp
  | .callThis hρ hf hl ht h, h₂ => by
    cases h₂ with
    | call _ hf' => have := lookupSig_lookup hf'; rw [hf] at this; cases this
    | callVar hρ' => rw [hρ] at hρ'; cases hρ'
    | callThis _ _ _ ht' h' => exact Eval.det h h'
    | callLib _ _ hd => exact absurd hl (libDecls_lookup hd)
    | read hp => simp [Expr.isPlace] at hp
  | .callLib hρ hf hd hM ha hc, h₂ => by
    cases h₂ with
    | call _ hf' => rw [hf] at hf'; cases hf'
    | callVar hρ' => rw [hρ] at hρ'; cases hρ'
    | callThis _ _ hl => exact absurd hl (libDecls_lookup hd)
    | callLib _ _ _ hM' ha' hc' =>
      rw [hM] at hM'; cases hM'
      obtain ⟨rfl, rfl⟩ := Args.det ha ha'
      exact Module.call_det hM hc hc'
    | read hp => simp [Expr.isPlace] at hp
  | .callFn he ht ha, h₂ => by
    cases h₂ with
    | callFn he' ht' ha' =>
      obtain ⟨h, rfl⟩ := Eval.det he he'; cases h
      rw [ht] at ht'; cases ht'
      exact ApplyArgs.det ha ha'
    | read hp => simp [Expr.isPlace] at hp
  | .lambda hc, h₂ => by
    cases h₂ with
    | lambda hc' => rw [hc] at hc'; cases hc'; exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
  | .locOf h, h₂ => by
    cases h₂ with
    | locOf h' => obtain ⟨rfl, rfl⟩ := LEval.det h h'; exact ⟨rfl, rfl⟩
    | read hp => simp [Expr.isPlace] at hp
termination_by structural h => h

theorem LEval.det : LEval p ρ σ e ℓ₁ σ₁ → LEval p ρ σ e ℓ₂ σ₂ → ℓ₁ = ℓ₂ ∧ σ₁ = σ₂
  | .locVar h, h₂ => by
    cases h₂ with
    | locVar h' => rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
    | locVarField h' => rw [h] at h'; cases h'
  | .locVarField h ht ho hf, h₂ => by
    cases h₂ with
    | locVar h' => rw [h] at h'; cases h'
    | locVarField _ ht' ho' hf' =>
      rw [ht] at ht'; cases ht'; rw [ho] at ho'; cases ho'; rw [hf] at hf'; cases hf'
      exact ⟨rfl, rfl⟩
  | .locDeref h, h₂ => by
    cases h₂ with
    | locDeref h' => obtain ⟨h, rfl⟩ := Eval.det h h'; cases h; exact ⟨rfl, rfl⟩
  | .locField h ho hf, h₂ => by
    cases h₂ with
    | locField h' ho' hf' =>
      obtain ⟨rfl, rfl⟩ := LEval.det h h'
      rw [ho] at ho'; cases ho'; rw [hf] at hf'; cases hf'; exact ⟨rfl, rfl⟩
  | .locArrow h ho hf, h₂ => by
    cases h₂ with
    | locArrow h' ho' hf' =>
      obtain ⟨h, rfl⟩ := Eval.det h h'; cases h
      rw [ho] at ho'; cases ho'; rw [hf] at hf'; cases hf'; exact ⟨rfl, rfl⟩
  | .methodLoc h hr, h₂ => by
    cases h₂ with
    | methodLoc h' hr' =>
      obtain ⟨rfl, h, rfl⟩ := CallMethod.det h h'; cases h; exact ⟨rfl, rfl⟩
  | .locIndex a₁ a₂ hM hi, h₂ => by
    cases h₂ with
    | locIndex b₁ b₂ hM' hi' =>
      obtain ⟨h, rfl⟩ := Eval.det a₁ b₁; cases h
      obtain ⟨rfl, rfl⟩ := Eval.det a₂ b₂
      rw [hM] at hM'; cases hM'
      exact Module.index_det hM hi hi'
  | .locCondT a₁ a₂, h₂ => by
    cases h₂ with
    | locCondT b₁ b₂ =>
      obtain ⟨-, rfl⟩ := Eval.det a₁ b₁
      exact LEval.det a₂ b₂
    | locCondF b => obtain ⟨h, -⟩ := Eval.det a₁ b; cases h
  | .locCondF a₁ a₃, h₂ => by
    cases h₂ with
    | locCondT b => obtain ⟨h, -⟩ := Eval.det a₁ b; cases h
    | locCondF b₁ b₃ =>
      obtain ⟨-, rfl⟩ := Eval.det a₁ b₁
      exact LEval.det a₃ b₃
termination_by structural h => h

theorem Exec.det : Exec p ρ σ c r₁ ρ₁ σ₁ → Exec p ρ σ c r₂ ρ₂ σ₂ → r₁ = r₂ ∧ ρ₁ = ρ₂ ∧ σ₁ = σ₂
  | .block h, h₂ => by
    cases h₂ with
    | block h' => obtain ⟨rfl, rfl, rfl⟩ := Execs.det h h'; exact ⟨rfl, rfl, rfl⟩
  | .ifT a b, h₂ => by
    cases h₂ with
    | ifT a' b' =>
      obtain ⟨-, rfl⟩ := Eval.det a a'
      obtain ⟨rfl, -, rfl⟩ := Exec.det b b'; exact ⟨rfl, rfl, rfl⟩
    | ifF a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
  | .ifF a b, h₂ => by
    cases h₂ with
    | ifT a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
    | ifF a' b' =>
      obtain ⟨-, rfl⟩ := Eval.det a a'
      obtain ⟨rfl, -, rfl⟩ := Exec.det b b'; exact ⟨rfl, rfl, rfl⟩
  | .whileF a, h₂ => by
    cases h₂ with
    | whileF a' => obtain ⟨-, rfl⟩ := Eval.det a a'; exact ⟨rfl, rfl, rfl⟩
    | whileT a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
    | whileRet a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
  | .whileT a b w, h₂ => by
    cases h₂ with
    | whileF a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
    | whileT a' b' w' =>
      obtain ⟨-, rfl⟩ := Eval.det a a'
      obtain ⟨-, -, rfl⟩ := Exec.det b b'
      obtain ⟨rfl, -, rfl⟩ := Exec.det w w'; exact ⟨rfl, rfl, rfl⟩
    | whileRet a' b' =>
      obtain ⟨-, rfl⟩ := Eval.det a a'
      obtain ⟨h, -, -⟩ := Exec.det b b'; cases h
  | .whileRet a b, h₂ => by
    cases h₂ with
    | whileF a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
    | whileT a' b' =>
      obtain ⟨-, rfl⟩ := Eval.det a a'
      obtain ⟨h, -, -⟩ := Exec.det b b'; cases h
    | whileRet a' b' =>
      obtain ⟨-, rfl⟩ := Eval.det a a'
      obtain ⟨h, -, rfl⟩ := Exec.det b b'; cases h; exact ⟨rfl, rfl, rfl⟩
  | .forLoop a w, h₂ => by
    cases h₂ with
    | forLoop a' w' =>
      obtain ⟨-, rfl, rfl⟩ := Exec.det a a'
      obtain ⟨rfl, -, rfl⟩ := Exec.det w w'; exact ⟨rfl, rfl, rfl⟩
  | .retVoid, h₂ => by
    cases h₂ with
    | retVoid => exact ⟨rfl, rfl, rfl⟩
  | .ret a, h₂ => by
    cases h₂ with
    | ret a' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; exact ⟨rfl, rfl, rfl⟩
  | .decl a ha, h₂ => by
    cases h₂ with
    | decl a' ha' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      rw [ha] at ha'; cases ha'; exact ⟨rfl, rfl, rfl⟩
  | .declRef a, h₂ => by
    cases h₂ with
    | declRef a' => obtain ⟨rfl, rfl⟩ := LEval.det a a'; exact ⟨rfl, rfl, rfl⟩
  | .declAuto a ha, h₂ => by
    cases h₂ with
    | declAuto a' ha' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      rw [ha] at ha'; cases ha'; exact ⟨rfl, rfl, rfl⟩
  | .assign a l hd, h₂ => by
    cases h₂ with
    | assign a' l' hd' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      obtain ⟨rfl, rfl⟩ := LEval.det l l'; exact ⟨rfl, rfl, rfl⟩
  | .exprStmt a, h₂ => by
    cases h₂ with
    | exprStmt a' => obtain ⟨-, rfl⟩ := Eval.det a a'; exact ⟨rfl, rfl, rfl⟩
  | .deleteNull a, h₂ => by
    cases h₂ with
    | deleteNull a' => obtain ⟨-, rfl⟩ := Eval.det a a'; exact ⟨rfl, rfl, rfl⟩
    | deleteLib a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
    | delete a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
  | .deleteLib a ho hM hd, h₂ => by
    cases h₂ with
    | deleteNull a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
    | deleteLib a' ho' hM' hd' =>
      obtain ⟨h, rfl⟩ := Eval.det a a'; cases h
      rw [ho] at ho'; cases ho'; rw [hM] at hM'; cases hM'
      rw [Module.delete_det hM hd hd']; exact ⟨rfl, rfl, rfl⟩
    | delete a' ho' =>
      obtain ⟨h, rfl⟩ := Eval.det a a'; cases h
      rw [ho] at ho'; cases ho'
  | .delete a ho hv hd, h₂ => by
    cases h₂ with
    | deleteNull a' => obtain ⟨h, -⟩ := Eval.det a a'; cases h
    | deleteLib a' ho' =>
      obtain ⟨h, rfl⟩ := Eval.det a a'; cases h
      rw [ho] at ho'; cases ho'
    | delete a' ho' hv' hd' =>
      obtain ⟨h, rfl⟩ := Eval.det a a'; cases h
      rw [ho] at ho'; cases ho'
      rw [Dtors.det hd hd']; exact ⟨rfl, rfl, rfl⟩
termination_by structural h => h

theorem Execs.det : Execs p ρ σ cs r₁ ρ₁ σ₁ → Execs p ρ σ cs r₂ ρ₂ σ₂ → r₁ = r₂ ∧ ρ₁ = ρ₂ ∧ σ₁ = σ₂
  | .nil, h₂ => by
    cases h₂ with
    | nil => exact ⟨rfl, rfl, rfl⟩
  | .cons a s, h₂ => by
    cases h₂ with
    | cons a' s' =>
      obtain ⟨-, rfl, rfl⟩ := Exec.det a a'
      exact Execs.det s s'
    | consRet a' => obtain ⟨h, -, -⟩ := Exec.det a a'; cases h
  | .consRet a, h₂ => by
    cases h₂ with
    | cons a' => obtain ⟨h, -, -⟩ := Exec.det a a'; cases h
    | consRet a' => exact Exec.det a a'
termination_by structural h => h

theorem Args.det : Args p ρ σ es vs₁ σ₁ → Args p ρ σ es vs₂ σ₂ → vs₁ = vs₂ ∧ σ₁ = σ₂
  | .nil, h₂ => by
    cases h₂ with
    | nil => exact ⟨rfl, rfl⟩
  | .cons a s, h₂ => by
    cases h₂ with
    | cons a' s' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      obtain ⟨rfl, rfl⟩ := Args.det s s'; exact ⟨rfl, rfl⟩
termination_by structural h => h

theorem Bind.det : Bind p ρ σ ρ₀ qs es ρ₁ σ₁ o₁ → Bind p ρ σ ρ₀ qs es ρ₂ σ₂ o₂ →
    ρ₁ = ρ₂ ∧ σ₁ = σ₂ ∧ o₁ = o₂
  | .nil, h₂ => by
    cases h₂ with
    | nil => exact ⟨rfl, rfl, rfl⟩
  | .byRef hq l s, h₂ => by
    cases h₂ with
    | byRef _ l' s' =>
      obtain ⟨rfl, rfl⟩ := LEval.det l l'
      exact Bind.det s s'
    | byVal hq' => rw [hq] at hq'; cases hq'
  | .byVal hq a ha s, h₂ => by
    cases h₂ with
    | byRef hq' => rw [hq] at hq'; cases hq'
    | byVal _ a' ha' s' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      rw [ha] at ha'; cases ha'
      obtain ⟨rfl, rfl, rfl⟩ := Bind.det s s'; exact ⟨rfl, rfl, rfl⟩
termination_by structural h => h

theorem Member.det : Member p ρ σ ℓ ps body es τ v₁ σ₁ → Member p ρ σ ℓ ps body es τ v₂ σ₂ →
    v₁ = v₂ ∧ σ₁ = σ₂
  | .member hn hb hx hr, h₂ => by
    cases h₂ with
    | member _ hb' hx' hr' =>
      obtain ⟨rfl, rfl, rfl⟩ := Bind.det hb hb'
      obtain ⟨rfl, rfl, rfl⟩ := Execs.det hx hx'
      rw [Returns.det hr hr']; exact ⟨rfl, rfl⟩
termination_by structural h => h

theorem CallMethod.det :
    CallMethod p ρ σ recv arrow m es static sig md₁ v₁ σ₁ →
    CallMethod p ρ σ recv arrow m es static sig md₂ v₂ σ₂ → md₁ = md₂ ∧ v₁ = v₂ ∧ σ₁ = σ₂
  | .dot hl ho hm hc, h₂ => by
    cases h₂ with
    | dot hl' ho' hm' hc' =>
      obtain ⟨rfl, rfl⟩ := LEval.det hl hl'
      rw [ho] at ho'; cases ho'; rw [hm] at hm'; cases hm'
      obtain ⟨rfl, rfl⟩ := Member.det hc hc'; exact ⟨rfl, rfl, rfl⟩
  | .arrow hv ho hm hc, h₂ => by
    cases h₂ with
    | arrow hv' ho' hm' hc' =>
      obtain ⟨h, rfl⟩ := Eval.det hv hv'; cases h
      rw [ho] at ho'; cases ho'; rw [hm] at hm'; cases hm'
      obtain ⟨rfl, rfl⟩ := Member.det hc hc'; exact ⟨rfl, rfl, rfl⟩
termination_by structural h => h

theorem Ctors.det : Ctors p ρ σ ℓ c cds es σ₁ → Ctors p ρ σ ℓ c cds es σ₂ → σ₁ = σ₂
  | .nil, h₂ => by
    cases h₂ with
    | nil => rfl
  | .skip hk s, h₂ => by
    cases h₂ with
    | skip _ s' => exact Ctors.det s s'
    | run hk' => rw [hk] at hk'; cases hk'
  | .run hk hm s, h₂ => by
    cases h₂ with
    | skip hk' => rw [hk] at hk'; cases hk'
    | run hk' hm' s' =>
      rw [hk] at hk'; cases hk'
      obtain ⟨-, rfl⟩ := Member.det hm hm'
      exact Ctors.det s s'
termination_by structural h => h

theorem Dtors.det : Dtors p ρ σ ℓ cds σ₁ → Dtors p ρ σ ℓ cds σ₂ → σ₁ = σ₂
  | .nil, h₂ => by
    cases h₂ with
    | nil => rfl
  | .skip hd s, h₂ => by
    cases h₂ with
    | skip _ s' => exact Dtors.det s s'
    | run hd' => rw [hd] at hd'; cases hd'
  | .run hd hm s, h₂ => by
    cases h₂ with
    | skip hd' => rw [hd] at hd'; cases hd'
    | run hd' hm' s' =>
      rw [hd] at hd'; cases hd'
      obtain ⟨-, rfl⟩ := Member.det hm hm'
      exact Dtors.det s s'
termination_by structural h => h

theorem Apply.det : Apply p σ w vs v₁ σ₁ → Apply p σ w vs v₂ σ₂ → v₁ = v₂ ∧ σ₁ = σ₂
  | .apply hn ha hρ hx hr, h₂ => by
    cases h₂ with
    | apply _ ha' hρ' hx' hr' =>
      rw [ha] at ha'; cases ha'
      rw [hρ', ← hρ] at hx'
      obtain ⟨rfl, rfl, rfl⟩ := Execs.det hx hx'
      rw [Returns.det hr hr', hρ, hρ']; exact ⟨rfl, rfl⟩
termination_by structural h => h

theorem ApplyArgs.det : ApplyArgs p ρ σ w es v₁ σ₁ → ApplyArgs p ρ σ w es v₂ σ₂ → v₁ = v₂ ∧ σ₁ = σ₂
  | .applyArgs hc hn ha hap, h₂ => by
    cases h₂ with
    | applyArgs hc' hn' ha' hap' =>
      obtain ⟨rfl, rfl⟩ := Args.det ha ha'
      exact Apply.det hap hap'
termination_by structural h => h

end

/-- The theorem `determinism` of the blueprint. A Core C++ program has at
most one result. -/
theorem Runs.det (h₁ : Runs p v₁) (h₂ : Runs p v₂) : v₁ = v₂ := by
  obtain ⟨_, h₁⟩ := h₁
  obtain ⟨_, h₂⟩ := h₂
  exact (Eval.det h₁ h₂).1

end CoreCpp.Semantics
