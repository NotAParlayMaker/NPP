import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_713 : ∀ (n m r : ℕ) (S : Fin m → Finset (Fin n)) (B : Finset (Fin n)), (∀ p : Fin n, (Finset.univ.filter (fun i : Fin m => p ∈ S i)).card ≤ r) → (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)).card ≤ B.card * r := by
  intro n m r S B hr
  classical
  let hits (p : Fin n) := Finset.univ.filter (fun i : Fin m => p ∈ S i)
  have eq : (Finset.univ.filter (fun i : Fin m => ∃ p ∈ B, p ∈ S i)) = B.biUnion hits := by
    ext i
    simp [hits]
  rw [eq]
  exact Finset.card_biUnion_le_card_mul B hits r (fun p _ => hr p)
