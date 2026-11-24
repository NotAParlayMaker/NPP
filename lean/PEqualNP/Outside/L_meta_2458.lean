import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2458_aux

open Configuration Configuration.ProjectivePlane Configuration.ofField

theorem plane (K : Type) [Field K] [Fintype K] (hK : Nat.card K = 211) :
    ∃ (x1 : ℕ) (x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3), (201 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧ (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) ∧ ∀ (x5 x6 : Fin x2), x5 ≠ x6 → ∃! x8 : Fin x2, x3 x5 x8 ∧ x3 x6 x8 := by
  classical
  haveI : Finite (Projectivization K (Fin 3 → K)) :=
    (Projectivization.finite_iff_of_finite K (Fin 3 → K)).2 inferInstance
  haveI := Fintype.ofFinite (Projectivization K (Fin 3 → K))
  have hc : Fintype.card (Projectivization K (Fin 3 → K))
      = order (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K)) ^ 2
        + order (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K)) + 1 :=
    card_points _ _
  have hc2 : Nat.card (Projectivization K (Fin 3 → K)) = 1 + 211 + 211 ^ 2 := by
    rw [Projectivization.card_of_finrank K (Fin 3 → K) (n := 3) (by simp), hK]
    simp [Finset.sum_range_succ]
  have hpc := fun l : Projectivization K (Fin 3 → K) =>
    pointCount_eq (Projectivization K (Fin 3 → K)) l
  have hex := fun a b : Projectivization K (Fin 3 → K) =>
    HasLines.existsUnique_line (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K)) a b
  generalize order (Projectivization K (Fin 3 → K)) (Projectivization K (Fin 3 → K)) = q at hc hpc
  have hq : q = 211 := by
    rw [Fintype.card_eq_nat_card, hc2] at hc
    rcases lt_trichotomy q 211 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  let e : Projectivization K (Fin 3 → K) ≃ Fin (q ^ 2 + q + 1) := Fintype.equivFinOfCardEq hc
  refine ⟨q, q ^ 2 + q + 1, fun a b => e.symm a ∈ e.symm b, Classical.decRel _, by omega, rfl, ?_, ?_⟩
  · intro l
    rw [Fintype.card_eq_nat_card, ← hpc (e.symm l)]
    exact Nat.card_congr (e.symm.subtypeEquiv (fun a => Iff.rfl))
  · intro a b hab
    obtain ⟨l, hl, hu⟩ := hex (e.symm a) (e.symm b) (by simpa using hab)
    refine ⟨e l, by simpa using hl, fun y hy => ?_⟩
    rw [← hu (e.symm y) hy]
    simp

end PEqualNP.Outside.L_meta_2458_aux

theorem PEqualNP.Outside.L_meta_2458 : ∃ (x1 : ℕ) (x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3), (201 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧ (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) ∧ ∀ (x5 x6 : Fin x2), x5 ≠ x6 → ∃! x8 : Fin x2, x3 x5 x8 ∧ x3 x6 x8 := by
  haveI : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  exact PEqualNP.Outside.L_meta_2458_aux.plane (ZMod 211) (by simp)
