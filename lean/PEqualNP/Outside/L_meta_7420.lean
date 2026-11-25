import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7420 : ∀ (x1 : ℕ) [x2 : NeZero x1] (x3 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1), (∀ (x4 x5 : Fin (x1 + (1 : ℕ))), x4 ≠ x5 → Function.Bijective fun (x7 : Fin (x1 * x1)) => (x3 x4 x7, x3 x5 x7)) → ∃ (x5 : Fin x1 × Fin x1 ≃ Fin (x1 * x1)) (x6 : Fin (x1 + (1 : ℕ)) → Fin x1 ≃ Fin x1), (∀ (x7 : Fin x1 × Fin x1), (x6 (0 : Fin (x1 + (1 : ℕ)))) (x3 (0 : Fin (x1 + (1 : ℕ))) (x5 x7)) = x7.1 ∧ (x6 (1 : Fin (x1 + (1 : ℕ)))) (x3 (1 : Fin (x1 + (1 : ℕ))) (x5 x7)) = x7.2) ∧ ∀ (x7 : Fin (x1 + (1 : ℕ))), x7 ≠ (0 : Fin (x1 + (1 : ℕ))) → ∀ (x9 : Fin x1), (x6 x7) (x3 x7 (x5 ((0 : Fin x1), x9))) = x9 := by
  intro n _ f hf
  have h01 : (0 : Fin (n + 1)) ≠ 1 := Fin.zero_ne_one'
  let e := Equiv.ofBijective _ (hf 0 1 h01)
  have he0 : ∀ p, f 0 (e.symm p) = p.1 := fun p => congrArg Prod.fst (e.apply_symm_apply p)
  have he1 : ∀ p, f 1 (e.symm p) = p.2 := fun p => congrArg Prod.snd (e.apply_symm_apply p)
  have hg : ∀ k, k ≠ 0 → Function.Bijective (fun y : Fin n => f k (e.symm (0, y))) := by
    intro k hk
    rw [← Finite.injective_iff_bijective]
    intro y y' h
    have key : (fun x7 => (f 0 x7, f k x7)) (e.symm (0, y)) = (fun x7 => (f 0 x7, f k x7)) (e.symm (0, y')) :=
      Prod.ext (by simp [he0]) h
    have h2 := e.symm.injective ((hf 0 k (Ne.symm hk)).1 key)
    exact (Prod.mk.inj h2).2
  refine ⟨e.symm, fun k => if hk : k = 0 then Equiv.refl _ else (Equiv.ofBijective _ (hg k hk)).symm, ?_, ?_⟩
  · intro p
    refine ⟨by simp [he0], ?_⟩
    beta_reduce
    rw [dif_neg (Ne.symm h01), Equiv.symm_apply_eq]
    simp [he1]
  · intro k hk y
    beta_reduce
    rw [dif_neg hk, Equiv.symm_apply_eq]
    rfl
