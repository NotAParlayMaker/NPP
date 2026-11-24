import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5077 : ∀ (x1 : Finset (Fin ((13 : ℕ) + (13 : ℕ)))), (∀ (x2 x3 : Fin (13 : ℕ)), x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ)) → Fin.castAdd (13 : ℕ) x2 ∈ x1 ∨ Fin.natAdd (13 : ℕ) x3 ∈ x1) → (13 : ℕ) ≤ x1.card := by
  intro x1 hcov
  let f : Fin 13 → Fin (13 + 13) := fun i =>
    if Fin.castAdd 13 i ∈ x1 then Fin.castAdd 13 i else Fin.natAdd 13 i
  have hf_mem : ∀ i : Fin 13, f i ∈ x1 := by
    intro i
    dsimp only [f]
    split_ifs with hi
    · exact hi
    · exact (hcov i i (Or.inl rfl)).resolve_left hi
  have hf_inj : Function.Injective f := by
    intro i j hij
    have hval := congrArg Fin.val hij
    dsimp only [f] at hval
    split_ifs at hval <;> (simp only [Fin.val_castAdd, Fin.val_natAdd] at hval; exact Fin.ext (by omega))
  have hsub : Finset.univ.image f ⊆ x1 := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact hf_mem i
  calc
    13 = (Finset.univ : Finset (Fin 13)).card := by rw [Finset.card_univ, Fintype.card_fin]
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective Finset.univ hf_inj).symm
    _ ≤ x1.card := Finset.card_le_card hsub
