import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2074
import PEqualNP.Outside.R_meta_1882_1

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds in
/-- L-meta-1882 (junk>=2, nested junk pair, Ustar bound) splits on the small-cover status:
    * small neighborhood cover exists: R-meta-1882-1 (already on main) + L-meta-2074
      close the case with the constant 5;
    * no small cover, junk = 2      : H1 below (junk-two residual, already proved in the
      public repository as L-meta-5242);
    * no small cover, junk >= 3     : H2 below (junk-three-and-above residual).
    Both residuals are strictly smaller subgoals, and the small-cover half carries the hard
    counting argument, so this split earns its place. -/
theorem PEqualNP.Outside.R_meta_1882_2 :
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 →
        (PEqualNP.TopForm.junk x3 x7).card = (2 : ℕ) →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7,
          ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7,
            PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) →
        (¬ ∃ S : Finset (Fin x2), ∃ missed : Finset (Sym2 (Fin x2)),
          S.card ≤ 4 ∧ missed.card ≤ x7.size + 1 ∧
          ∀ e ∈ PEqualNP.TopForm.Ustar x3 x7, e ∈ missed ∨
            ∃ p q : Fin x2, e = s(p, q) ∧
              ((∃ z ∈ S, x3.Adj p z) ∨ ∃ z ∈ S, x3.Adj q z)) →
        (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) →
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7,
          ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7,
            PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) →
        (¬ ∃ S : Finset (Fin x2), ∃ missed : Finset (Sym2 (Fin x2)),
          S.card ≤ 4 ∧ missed.card ≤ x7.size + 1 ∧
          ∀ e ∈ PEqualNP.TopForm.Ustar x3 x7, e ∈ missed ∨
            ∃ p q : Fin x2, e = s(p, q) ∧
              ((∃ z ∈ S, x3.Adj p z) ∨ ∃ z ∈ S, x3.Adj q z)) →
        (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) →
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7,
          ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7,
            PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) →
        (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) := by
  intro hJunkEq2 hJunkGe3
  obtain ⟨c2, hc2⟩ := hJunkEq2
  obtain ⟨c3, hc3⟩ := hJunkGe3
  refine PEqualNP.Outside.R_meta_1882_1 PEqualNP.Outside.L_meta_2074
    ⟨max c2 c3, ?_⟩
  intro n G _ hg hne C hl ht hTwo hNested hSmall
  by_cases hj2 : (junk G C).card = 2
  · exact (hc2 n G hg hne C hl ht hj2 hNested hSmall).trans
      (Nat.mul_le_mul_right _ (Nat.le_max_left c2 c3))
  · have hj3 : 3 ≤ (junk G C).card := by
      have hjne2 : (junk G C).card ≠ 2 := hj2
      have hjcard2 : 2 ≤ (junk G C).card := hTwo
      omega
    exact (hc3 n G hg hne C hl ht hj3 hNested hSmall).trans
      (Nat.mul_le_mul_right _ (Nat.le_max_right c2 c3))
