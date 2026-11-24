import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2458 : ∃ (x1 : ℕ) (x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : DecidableRel x3), (201 : ℕ) ≤ x1 ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧ (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) ∧ ∀ (x5 x6 : Fin x2), x5 ≠ x6 → ∃! x8 : Fin x2, x3 x5 x8 ∧ x3 x6 x8 := by
  classical
  haveI : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  let K := ZMod 211
  let P := Projectivization K (Fin 3 → K)
  haveI : Fintype P := Fintype.ofFinite P
  let q := Configuration.ProjectivePlane.order P P
  have hcard : Fintype.card P = q ^ 2 + q + 1 := Configuration.ProjectivePlane.card_points P P
  have hcard2 : Nat.card P = ∑ i ∈ Finset.range 3, Nat.card K ^ i :=
    Projectivization.card_of_finrank K (Fin 3 → K) (by simp)
  have hK : Nat.card K = 211 := by simp [K]
  have hq : 201 ≤ q := by
    have h3 : q ^ 2 + q + 1 = 1 + 211 + 211 ^ 2 := by
      rw [← hcard, ← Nat.card_eq_fintype_card, hcard2, hK]
      simp [Finset.sum_range_succ]
    nlinarith
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  refine ⟨q, Fintype.card P, fun i j => e.symm i ∈ e.symm j, inferInstance, hq, hcard, ?_, ?_⟩
  · intro l
    have h := Configuration.ProjectivePlane.pointCount_eq P (e.symm l)
    rw [Configuration.pointCount, Nat.card_eq_fintype_card] at h
    rw [← h]
    exact Fintype.card_congr (e.symm.subtypeEquiv (fun _ => Iff.rfl))
  · intro i j hij
    have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    obtain ⟨l, hl, huniq⟩ :=
      Configuration.HasLines.existsUnique_line (P := P) (L := P) (e.symm i) (e.symm j) hne
    refine ⟨e l, ?_, ?_⟩
    · simpa using hl
    · intro m hm
      have hm' := huniq (e.symm m) hm
      rw [← hm']
      simp
