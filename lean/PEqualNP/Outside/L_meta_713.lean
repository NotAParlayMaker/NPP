import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_713_aux
end PEqualNP.Outside.L_meta_713_aux

theorem PEqualNP.Outside.L_meta_713 : ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r := by
  intro n m r S B h
  have hsub : (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)) ⊆ B.biUnion (fun p => Finset.univ.filter (fun i : Fin m => p ∈ S i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨p, hp, hpi⟩ := hi
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p, hp, hpi⟩
  calc (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card
      ≤ (B.biUnion (fun p => Finset.univ.filter (fun i : Fin m => p ∈ S i))).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ B, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card := Finset.card_biUnion_le
    _ ≤ B.card * r := by
      have := Finset.sum_le_card_nsmul B (fun p => (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card) r (fun p _ => h p)
      simpa using this
