import CoreCpp.Semantics.Dynamic

/-!
# Determinism of the dynamic semantics

The theorem `det` of the blueprint. Two derivations of one judgement,
from the same configuration and the same subject, give the same result. The
proof is one mutual structural recursion on the first derivation, with a case
analysis of the second. The rules of one subject have mutually exclusive
premises, and every allocation is the function `Store.alloc`, so each case
either matches the same rule or contradicts a premise.
-/

namespace CoreCpp.Semantics

/-- A body has at most one result for its control and its declaration. -/
theorem Returns.det : Returns σ c τ b r₁ → Returns σ c τ b r₂ → r₁ = r₂
  | .val h, .val h' => by rw [h] at h'; cases h'; rfl
  | .ref, .ref => rfl
  | .void, .void => rfl

/-- The conversion rd of one result gives one value. -/
theorem rd_det (h₁ : Res.rd σ r = some v₁) (h₂ : Res.rd σ r = some v₂) : v₁ = v₂ := by
  rw [h₁] at h₂; cases h₂; rfl

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

/-- A function with a chosen signature is a function of the program by its name. -/
theorem lookupSig_funsNamed {p : Program} (h : FunEnv.lookupSig p f sig = some fn) : p.funsNamed f ≠ [] := by
  have := lookupSig_lookup h
  simp only [FunEnv.lookup, List.find?_isSome] at this
  obtain ⟨g, hg, hn⟩ := this
  simp only [Program.funsNamed, ne_eq, List.filter_eq_nil_iff]
  exact fun hall => hall g hg hn

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

theorem Eval.det : Eval p ρ σ e r₁ σ₁ → Eval p ρ σ e r₂ σ₂ → r₁ = r₂ ∧ σ₁ = σ₂
  | .lit _, h₂ => by
    cases h₂ with
    | lit => exact ⟨rfl, rfl⟩
  | .boolLit, h₂ => by
    cases h₂ with
    | boolLit => exact ⟨rfl, rfl⟩
  | .null, h₂ => by
    cases h₂ with
    | null => exact ⟨rfl, rfl⟩
  | .var h, h₂ => by
    cases h₂ with
    | var h' => rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
    | varField h' => rw [h] at h'; cases h'
  | .varField h ht ho hf, h₂ => by
    cases h₂ with
    | var h' => rw [h] at h'; cases h'
    | varField _ ht' ho' hf' =>
      rw [ht] at ht'; cases ht'; rw [ho] at ho'; cases ho'; rw [hf] at hf'; cases hf'
      exact ⟨rfl, rfl⟩
  | .this h, h₂ => by
    cases h₂ with
    | this h' => rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
  | .new hc ha ho hk, h₂ => by
    cases h₂ with
    | new hc' ha' ho' hk' =>
      rw [ha] at ha'; cases ha'; rw [ho] at ho'; cases ho'
      exact ⟨rfl, Ctors.det hk hk'⟩
  | .methodCall h, h₂ => by
    cases h₂ with
    | methodCall h' =>
      obtain ⟨rfl, rfl, rfl⟩ := CallMethod.det h h'; exact ⟨rfl, rfl⟩
  | .newLib ha hM hn, h₂ => by
    cases h₂ with
    | newLib ha' hM' hn' =>
      obtain ⟨rfl, rfl⟩ := Args.det ha ha'
      rw [hM] at hM'; cases hM'
      obtain ⟨rfl, rfl⟩ := Module.new_det hM hn hn'; exact ⟨rfl, rfl⟩
  | .not h hv, h₂ => by
    cases h₂ with
    | not h' hv' =>
      obtain ⟨rfl, rfl⟩ := Eval.det h h'; cases rd_det hv hv'; exact ⟨rfl, rfl⟩
  | .neg h hv hr, h₂ => by
    cases h₂ with
    | neg h' hv' hr' =>
      obtain ⟨rfl, rfl⟩ := Eval.det h h'; cases rd_det hv hv'; exact ⟨rfl, rfl⟩
  | .arith hop a₁ v₁ a₂ v₂ hr, h₂ => by
    cases h₂ with
    | arith hop' b₁ w₁ b₂ w₂ hr' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a₁ b₁; cases rd_det v₁ w₁
      obtain ⟨rfl, rfl⟩ := Eval.det a₂ b₂; cases rd_det v₂ w₂
      exact ⟨rfl, rfl⟩
    | div b₁ w₁ b₂ w₂ hz hd => rw [divide_of_isArith hop] at hd; cases hd
    | rel b₁ w₁ b₂ w₂ hc => rw [compare_of_isArith hop] at hc; cases hc
    | andF => simp [BinOp.isArith] at hop
    | andT => simp [BinOp.isArith] at hop
    | orT => simp [BinOp.isArith] at hop
    | orF => simp [BinOp.isArith] at hop
  | .div a₁ v₁ a₂ v₂ hz hd hr, h₂ => by
    cases h₂ with
    | arith hop' => rw [divide_of_isArith hop'] at hd; cases hd
    | div b₁ w₁ b₂ w₂ hz' hd' hr' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a₁ b₁; cases rd_det v₁ w₁
      obtain ⟨rfl, rfl⟩ := Eval.det a₂ b₂; cases rd_det v₂ w₂
      rw [hd] at hd'; cases hd'; exact ⟨rfl, rfl⟩
    | rel b₁ w₁ b₂ w₂ hc => rw [compare_of_divide hd] at hc; cases hc
    | andF => simp [BinOp.divide] at hd
    | andT => simp [BinOp.divide] at hd
    | orT => simp [BinOp.divide] at hd
    | orF => simp [BinOp.divide] at hd
  | .rel a₁ v₁ a₂ v₂ hc, h₂ => by
    cases h₂ with
    | arith hop' => rw [compare_of_isArith hop'] at hc; cases hc
    | div _ _ _ _ _ hd => rw [compare_of_divide hd] at hc; cases hc
    | rel b₁ w₁ b₂ w₂ hc' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a₁ b₁; cases rd_det v₁ w₁
      obtain ⟨rfl, rfl⟩ := Eval.det a₂ b₂; cases rd_det v₂ w₂
      rw [hc] at hc'; cases hc'; exact ⟨rfl, rfl⟩
    | andF => simp [BinOp.compare] at hc
    | andT => simp [BinOp.compare] at hc
    | orT => simp [BinOp.compare] at hc
    | orF => simp [BinOp.compare] at hc
  | .andF a v, h₂ => by
    cases h₂ with
    | arith hop => simp [BinOp.isArith] at hop
    | div _ _ _ _ _ hd => simp [BinOp.divide] at hd
    | rel _ _ _ _ hc => simp [BinOp.compare] at hc
    | andF b w => obtain ⟨rfl, rfl⟩ := Eval.det a b; exact ⟨rfl, rfl⟩
    | andT b w => obtain ⟨rfl, rfl⟩ := Eval.det a b; cases rd_det v w
  | .andT a₁ v₁ a₂ v₂, h₂ => by
    cases h₂ with
    | arith hop => simp [BinOp.isArith] at hop
    | div _ _ _ _ _ hd => simp [BinOp.divide] at hd
    | rel _ _ _ _ hc => simp [BinOp.compare] at hc
    | andF b w => obtain ⟨rfl, rfl⟩ := Eval.det a₁ b; cases rd_det v₁ w
    | andT b₁ w₁ b₂ w₂ =>
      obtain ⟨rfl, rfl⟩ := Eval.det a₁ b₁
      obtain ⟨rfl, rfl⟩ := Eval.det a₂ b₂; cases rd_det v₂ w₂; exact ⟨rfl, rfl⟩
  | .orT a v, h₂ => by
    cases h₂ with
    | arith hop => simp [BinOp.isArith] at hop
    | div _ _ _ _ _ hd => simp [BinOp.divide] at hd
    | rel _ _ _ _ hc => simp [BinOp.compare] at hc
    | orT b w => obtain ⟨rfl, rfl⟩ := Eval.det a b; exact ⟨rfl, rfl⟩
    | orF b w => obtain ⟨rfl, rfl⟩ := Eval.det a b; cases rd_det v w
  | .orF a₁ v₁ a₂ v₂, h₂ => by
    cases h₂ with
    | arith hop => simp [BinOp.isArith] at hop
    | div _ _ _ _ _ hd => simp [BinOp.divide] at hd
    | rel _ _ _ _ hc => simp [BinOp.compare] at hc
    | orT b w => obtain ⟨rfl, rfl⟩ := Eval.det a₁ b; cases rd_det v₁ w
    | orF b₁ w₁ b₂ w₂ =>
      obtain ⟨rfl, rfl⟩ := Eval.det a₁ b₁
      obtain ⟨rfl, rfl⟩ := Eval.det a₂ b₂; cases rd_det v₂ w₂; exact ⟨rfl, rfl⟩
  | .condT a₁ v a₂, h₂ => by
    cases h₂ with
    | condT b₁ w b₂ =>
      obtain ⟨rfl, rfl⟩ := Eval.det a₁ b₁
      exact Eval.det a₂ b₂
    | condF b w => obtain ⟨rfl, rfl⟩ := Eval.det a₁ b; cases rd_det v w
  | .condF a₁ v a₃, h₂ => by
    cases h₂ with
    | condT b w => obtain ⟨rfl, rfl⟩ := Eval.det a₁ b; cases rd_det v w
    | condF b₁ w b₃ =>
      obtain ⟨rfl, rfl⟩ := Eval.det a₁ b₁
      exact Eval.det a₃ b₃
  | .call hρ hf hn hb hx hr, h₂ => by
    cases h₂ with
    | call hρ' hf' hn' hb' hx' hr' =>
      rw [hf] at hf'; cases hf'
      obtain ⟨rfl, rfl, rfl⟩ := Bind.det hb hb'
      obtain ⟨rfl, rfl, rfl⟩ := Execs.det hx hx'
      cases Returns.det hr hr'; exact ⟨rfl, rfl⟩
    | callVar hρ' => rw [hρ] at hρ'; cases hρ'
    | callThis _ hf' => have := lookupSig_lookup hf; rw [hf'] at this; cases this
    | callLib _ hf' => exact absurd hf' (lookupSig_funsNamed hf)
  | .callVar hρ hv hr ht ha, h₂ => by
    cases h₂ with
    | call hρ' => rw [hρ] at hρ'; cases hρ'
    | callVar hρ' hv' hr' ht' ha' =>
      obtain ⟨rfl, rfl⟩ := Eval.det hv hv'; cases rd_det hr hr'
      rw [ht] at ht'; cases ht'
      obtain ⟨rfl, rfl⟩ := ApplyArgs.det ha ha'; exact ⟨rfl, rfl⟩
    | callThis hρ' => rw [hρ] at hρ'; cases hρ'
    | callLib hρ' => rw [hρ] at hρ'; cases hρ'
  | .callThis hρ hf hl ht h, h₂ => by
    cases h₂ with
    | call _ hf' => have := lookupSig_lookup hf'; rw [hf] at this; cases this
    | callVar hρ' => rw [hρ] at hρ'; cases hρ'
    | callThis _ _ _ ht' h' => exact Eval.det h h'
    | callLib _ _ hd => exact absurd hl (libDecls_lookup hd)
  | .callLib hρ hf hd hM ha hc, h₂ => by
    cases h₂ with
    | call _ hf' => exact absurd hf (lookupSig_funsNamed hf')
    | callVar hρ' => rw [hρ] at hρ'; cases hρ'
    | callThis _ _ hl => exact absurd hl (libDecls_lookup hd)
    | callLib _ _ _ hM' ha' hc' =>
      rw [hM] at hM'; cases hM'
      obtain ⟨rfl, rfl⟩ := Args.det ha ha'
      obtain ⟨rfl, rfl⟩ := Module.call_det hM hc hc'; exact ⟨rfl, rfl⟩
  | .callFn he hr ht ha, h₂ => by
    cases h₂ with
    | callFn he' hr' ht' ha' =>
      obtain ⟨rfl, rfl⟩ := Eval.det he he'; cases rd_det hr hr'
      rw [ht] at ht'; cases ht'
      obtain ⟨rfl, rfl⟩ := ApplyArgs.det ha ha'; exact ⟨rfl, rfl⟩
  | .lambda hc, h₂ => by
    cases h₂ with
    | lambda hc' => rw [hc] at hc'; cases hc'; exact ⟨rfl, rfl⟩
  | .deref h hv, h₂ => by
    cases h₂ with
    | deref h' hv' => obtain ⟨rfl, rfl⟩ := Eval.det h h'; cases rd_det hv hv'; exact ⟨rfl, rfl⟩
  | .field h ho hf, h₂ => by
    cases h₂ with
    | field h' ho' hf' =>
      obtain ⟨h, rfl⟩ := Eval.det h h'; cases h
      rw [ho] at ho'; cases ho'; rw [hf] at hf'; cases hf'; exact ⟨rfl, rfl⟩
  | .arrow h hv ho hf, h₂ => by
    cases h₂ with
    | arrow h' hv' ho' hf' =>
      obtain ⟨rfl, rfl⟩ := Eval.det h h'; cases rd_det hv hv'
      rw [ho] at ho'; cases ho'; rw [hf] at hf'; cases hf'; exact ⟨rfl, rfl⟩
  | .index a₁ v₁ a₂ v₂ hM hi, h₂ => by
    cases h₂ with
    | index b₁ w₁ b₂ w₂ hM' hi' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a₁ b₁; cases rd_det v₁ w₁
      obtain ⟨rfl, rfl⟩ := Eval.det a₂ b₂; cases rd_det v₂ w₂
      rw [hM] at hM'; cases hM'
      obtain ⟨rfl, rfl⟩ := Module.index_det hM hi hi'; exact ⟨rfl, rfl⟩
termination_by structural h => h

theorem Exec.det : Exec p ρ σ c r₁ ρ₁ σ₁ → Exec p ρ σ c r₂ ρ₂ σ₂ → r₁ = r₂ ∧ ρ₁ = ρ₂ ∧ σ₁ = σ₂
  | .block h, h₂ => by
    cases h₂ with
    | block h' => obtain ⟨rfl, rfl, rfl⟩ := Execs.det h h'; exact ⟨rfl, rfl, rfl⟩
  | .ifT a v b, h₂ => by
    cases h₂ with
    | ifT a' v' b' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      obtain ⟨rfl, -, rfl⟩ := Exec.det b b'; exact ⟨rfl, rfl, rfl⟩
    | ifF a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
  | .ifF a v b, h₂ => by
    cases h₂ with
    | ifT a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
    | ifF a' v' b' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      obtain ⟨rfl, -, rfl⟩ := Exec.det b b'; exact ⟨rfl, rfl, rfl⟩
  | .whileF a v, h₂ => by
    cases h₂ with
    | whileF a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; exact ⟨rfl, rfl, rfl⟩
    | whileT a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
    | whileRet a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
  | .whileT a v b w, h₂ => by
    cases h₂ with
    | whileF a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
    | whileT a' v' b' w' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      obtain ⟨-, -, rfl⟩ := Exec.det b b'
      obtain ⟨rfl, -, rfl⟩ := Exec.det w w'; exact ⟨rfl, rfl, rfl⟩
    | whileRet a' v' b' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      obtain ⟨h, -, -⟩ := Exec.det b b'; cases h
  | .whileRet a v b, h₂ => by
    cases h₂ with
    | whileF a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
    | whileT a' v' b' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
      obtain ⟨h, -, -⟩ := Exec.det b b'; cases h
    | whileRet a' v' b' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'
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
  | .decl a v ha, h₂ => by
    cases h₂ with
    | decl a' v' ha' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
      rw [ha] at ha'; cases ha'; exact ⟨rfl, rfl, rfl⟩
  | .declRef a, h₂ => by
    cases h₂ with
    | declRef a' => obtain ⟨h, rfl⟩ := Eval.det a a'; cases h; exact ⟨rfl, rfl, rfl⟩
  | .declAuto a v ha, h₂ => by
    cases h₂ with
    | declAuto a' v' ha' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
      rw [ha] at ha'; cases ha'; exact ⟨rfl, rfl, rfl⟩
  | .assign a v l hd, h₂ => by
    cases h₂ with
    | assign a' v' l' hd' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
      obtain ⟨h, rfl⟩ := Eval.det l l'; cases h; exact ⟨rfl, rfl, rfl⟩
  | .exprStmt a, h₂ => by
    cases h₂ with
    | exprStmt a' => obtain ⟨-, rfl⟩ := Eval.det a a'; exact ⟨rfl, rfl, rfl⟩
  | .deleteNull a v, h₂ => by
    cases h₂ with
    | deleteNull a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; exact ⟨rfl, rfl, rfl⟩
    | deleteLib a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
    | delete a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
  | .deleteLib a v ho hM hd, h₂ => by
    cases h₂ with
    | deleteNull a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
    | deleteLib a' v' ho' hM' hd' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
      rw [ho] at ho'; cases ho'; rw [hM] at hM'; cases hM'
      rw [Module.delete_det hM hd hd']; exact ⟨rfl, rfl, rfl⟩
    | delete a' v' ho' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
      rw [ho] at ho'; cases ho'
  | .delete a v ho hvd hd, h₂ => by
    cases h₂ with
    | deleteNull a' v' => obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
    | deleteLib a' v' ho' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
      rw [ho] at ho'; cases ho'
    | delete a' v' ho' hvd' hd' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
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
  | .cons a v s, h₂ => by
    cases h₂ with
    | cons a' v' s' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
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
      obtain ⟨h, rfl⟩ := Eval.det l l'; cases h
      exact Bind.det s s'
    | byVal hq' => rw [hq] at hq'; cases hq'
  | .byVal hq a v ha s, h₂ => by
    cases h₂ with
    | byRef hq' => rw [hq] at hq'; cases hq'
    | byVal _ a' v' ha' s' =>
      obtain ⟨rfl, rfl⟩ := Eval.det a a'; cases rd_det v v'
      rw [ha] at ha'; cases ha'
      obtain ⟨rfl, rfl, rfl⟩ := Bind.det s s'; exact ⟨rfl, rfl, rfl⟩
termination_by structural h => h

theorem Member.det : Member p ρ σ ℓ ps body es τ ref v₁ σ₁ → Member p ρ σ ℓ ps body es τ ref v₂ σ₂ →
    v₁ = v₂ ∧ σ₁ = σ₂
  | .member hn hb hx hr, h₂ => by
    cases h₂ with
    | member _ hb' hx' hr' =>
      obtain ⟨rfl, rfl, rfl⟩ := Bind.det hb hb'
      obtain ⟨rfl, rfl, rfl⟩ := Execs.det hx hx'
      cases Returns.det hr hr'; exact ⟨rfl, rfl⟩
termination_by structural h => h

theorem CallMethod.det :
    CallMethod p ρ σ recv arrow m es static sig md₁ v₁ σ₁ →
    CallMethod p ρ σ recv arrow m es static sig md₂ v₂ σ₂ → md₁ = md₂ ∧ v₁ = v₂ ∧ σ₁ = σ₂
  | .dot hl ho hm hc, h₂ => by
    cases h₂ with
    | dot hl' ho' hm' hc' =>
      obtain ⟨h, rfl⟩ := Eval.det hl hl'; cases h
      rw [ho] at ho'; cases ho'; rw [hm] at hm'; cases hm'
      obtain ⟨rfl, rfl⟩ := Member.det hc hc'; exact ⟨rfl, rfl, rfl⟩
  | .arrow hv hp ho hm hc, h₂ => by
    cases h₂ with
    | arrow hv' hp' ho' hm' hc' =>
      obtain ⟨rfl, rfl⟩ := Eval.det hv hv'; cases rd_det hp hp'
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
      cases Returns.det hr hr'; rw [hρ, hρ']; exact ⟨rfl, rfl⟩
termination_by structural h => h

theorem ApplyArgs.det : ApplyArgs p ρ σ w es v₁ σ₁ → ApplyArgs p ρ σ w es v₂ σ₂ → v₁ = v₂ ∧ σ₁ = σ₂
  | .applyArgs hc hn ha hap, h₂ => by
    cases h₂ with
    | applyArgs hc' hn' ha' hap' =>
      obtain ⟨rfl, rfl⟩ := Args.det ha ha'
      exact Apply.det hap hap'
termination_by structural h => h

end

/-- The theorem `det` of the blueprint. A Core C++ program has at
most one result. -/
theorem Runs.det (h₁ : Runs p v₁) (h₂ : Runs p v₂) : v₁ = v₂ := by
  obtain ⟨_, h₁⟩ := h₁
  obtain ⟨_, h₂⟩ := h₂
  obtain ⟨h, -⟩ := Eval.det h₁ h₂; cases h; rfl

end CoreCpp.Semantics
