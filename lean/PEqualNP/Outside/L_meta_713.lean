import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_713 : ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r := by
  intro n m r S B h
  have hsub : (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)) ⊆
      B.biUnion (fun p => Finset.univ.filter (fun i : Fin m => p ∈ S i)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨-, p, hpB, hpS⟩ := hi
    rw [Finset.mem_biUnion]
    exact ⟨p, hpB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpS⟩⟩
  calc (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card
      ≤ (B.biUnion (fun p => Finset.univ.filter (fun i : Fin m => p ∈ S i))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ B, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ B, r := Finset.sum_le_sum (fun p _ => h p)
    _ = B.card * r := by rw [Finset.sum_const, smul_eq_mul]
