import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7645
open PEqualNP.CircuitLowerBounds



set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem key : ∀ u v : Fin 14, 14 * (u : ℕ) + (v : ℕ) ∈ ([(7 : ℕ), (8 : ℕ), (10 : ℕ), (21 : ℕ), (23 : ℕ), (27 : ℕ), (36 : ℕ), (40 : ℕ), (41 : ℕ), (49 : ℕ), (53 : ℕ), (54 : ℕ), (66 : ℕ), (67 : ℕ), (69 : ℕ), (79 : ℕ), (80 : ℕ), (82 : ℕ), (92 : ℕ), (93 : ℕ), (95 : ℕ)] : List ℕ) →
    ∃ m ∈ ([(129 : ℕ), (257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)] : List ℕ), ∀ i : Fin 14, m.testBit (i : ℕ) = decide (i = u ∨ i = v) := by
  decide +kernel

end PEqualNP.Outside.L_meta_7645

open PEqualNP.Outside.L_meta_7645 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7645 : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ)), (14 : ℕ) * ↑x2 + ↑x3 ∈ [(7 : ℕ), (8 : ℕ), (10 : ℕ), (21 : ℕ), (23 : ℕ), (27 : ℕ), (36 : ℕ), (40 : ℕ), (41 : ℕ), (49 : ℕ), (53 : ℕ), (54 : ℕ), (66 : ℕ), (67 : ℕ), (69 : ℕ), (79 : ℕ), (80 : ℕ), (82 : ℕ), (92 : ℕ), (93 : ℕ), (95 : ℕ)] ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∀ (x2 : Fin (14 : ℕ) → Bool), x1 x2 → (∀ x4 ≤ x2, x1 x4 → x4 = x2) → ∃ x5 ∈ [(129 : ℕ), (257 : ℕ), (1025 : ℕ), (130 : ℕ), (514 : ℕ), (8194 : ℕ), (260 : ℕ), (4100 : ℕ), (8196 : ℕ), (136 : ℕ), (2056 : ℕ), (4104 : ℕ), (1040 : ℕ), (2064 : ℕ), (8208 : ℕ), (544 : ℕ), (1056 : ℕ), (4128 : ℕ), (320 : ℕ), (576 : ℕ), (2112 : ℕ)], (fun (x6 : Fin (14 : ℕ)) => x5.testBit ↑x6) = x2 := by
  intro f x hx hmin
  obtain ⟨u, v, hmem, hu, hv⟩ := hx
  have he : (fun i : Fin 14 => decide (i = u ∨ i = v)) ≤ x := by
    intro i
    show decide (i = u ∨ i = v) ≤ x i
    rw [Bool.le_iff_imp]
    intro h
    rcases of_decide_eq_true h with h1 | h1
    · rw [h1]; exact hu
    · rw [h1]; exact hv
  have hfe : f (fun i : Fin 14 => decide (i = u ∨ i = v)) :=
    ⟨u, v, hmem, by simp, by simp⟩
  have hex := hmin _ he hfe
  obtain ⟨m, hm, hmi⟩ := key u v hmem
  refine ⟨m, hm, ?_⟩
  rw [← hex]
  exact funext hmi
