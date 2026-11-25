import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7422 : ∀ (x1 : ℕ) [x2 : NeZero x1] (x3 : Fin (x1 + (1 : ℕ)) → Fin x1 × Fin x1 → Fin x1), (2 : ℕ) ≤ x1 → (∀ (x5 x6 : Fin (x1 + (1 : ℕ))), x5 ≠ x6 → Function.Bijective fun (x8 : Fin x1 × Fin x1) => (x3 x5 x8, x3 x6 x8)) → (∀ (x6 : Fin x1 × Fin x1), x3 (0 : Fin (x1 + (1 : ℕ))) x6 = x6.1 ∧ x3 (1 : Fin (x1 + (1 : ℕ))) x6 = x6.2) → (∀ (x7 : Fin (x1 + (1 : ℕ))), x7 ≠ (0 : Fin (x1 + (1 : ℕ))) → ∀ (x9 : Fin x1), x3 x7 ((0 : Fin x1), x9) = x9) → ∃ (x8 : Fin (x1 + (1 : ℕ)) ≃ Fin (x1 + (1 : ℕ))), x8 (0 : Fin (x1 + (1 : ℕ))) = (0 : Fin (x1 + (1 : ℕ))) ∧ x8 (1 : Fin (x1 + (1 : ℕ))) = (1 : Fin (x1 + (1 : ℕ))) ∧ ∀ (x9 : Fin x1), x3 (x8 x9.succ) ((1 : Fin x1), (0 : Fin x1)) = x9 := by
  intro x1 x2 x3 h2 hb h01 h0
  have hinj : Function.Injective (fun i : Fin x1 => x3 i.succ ((1 : Fin x1), (0 : Fin x1))) := by
    intro k k' hk
    by_contra hne
    have hs : k.succ ≠ k'.succ := fun h => hne (Fin.succ_injective _ h)
    have hi := (hb k.succ k'.succ hs).1
    have h := @hi ((0 : Fin x1), x3 k.succ ((1 : Fin x1), (0 : Fin x1))) ((1 : Fin x1), (0 : Fin x1)) (by
      simp only [Prod.mk.injEq]
      refine ⟨h0 _ (Fin.succ_ne_zero _) _, ?_⟩
      rw [h0 _ (Fin.succ_ne_zero _)]
      exact hk)
    have h1 : (0 : Fin x1) = 1 := congrArg Prod.fst h
    have h3 := congrArg Fin.val h1
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h3
    simp at h3
  let e := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have he : ∀ i, x3 (e.symm i).succ ((1 : Fin x1), (0 : Fin x1)) = i := fun i => e.apply_symm_apply i
  have he0 : e.symm 0 = 0 := by
    rw [Equiv.symm_apply_eq]
    have := (h01 ((1 : Fin x1), (0 : Fin x1))).2
    rw [← Fin.succ_zero_eq_one'] at this
    exact this.symm
  obtain ⟨f, hf⟩ : ∃ f : Fin x1 ≃ Fin x1, f = e.symm := ⟨_, rfl⟩
  rw [← hf] at he he0
  clear_value e
  refine ⟨(finSuccEquiv x1).trans ((Equiv.optionCongr f).trans (finSuccEquiv x1).symm), ?_, ?_, ?_⟩
  · simp
  · rw [← Fin.succ_zero_eq_one']
    simp only [Equiv.trans_apply, finSuccEquiv_succ, Equiv.optionCongr_apply, Option.map_some, finSuccEquiv_symm_some, he0]
  · intro i
    simp [he]
