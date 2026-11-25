import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2579_1
    (core :
      ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
        G.edgeFinset.Nonempty →
        ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (H : SimpleGraph (Fin n)),
          PEqualNP.TopForm.IsLeastAO G C →
          PEqualNP.TopForm.TopForm G C →
          H ≤ G.deleteEdges (PEqualNP.TopForm.starEdges G C : Set (Sym2 (Fin n))) →
          (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
          H.edgeSet.ncard ≤ k * (C.size + 1))
    (residual_core :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
        G.edgeFinset.Nonempty →
        ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO G C →
          PEqualNP.TopForm.TopForm G C →
          ∃ H : SimpleGraph (Fin n),
            H ≤ G.deleteEdges (PEqualNP.TopForm.starEdges G C : Set (Sym2 (Fin n))) ∧
            (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) ∧
            H.edgeSet = ↑((PEqualNP.TopForm.Ustar G C).filter (fun e =>
                ¬ ∃ u v : Fin n, e = s(u, v) ∧
                  ∃ h < C.gates.length, ∃ b : Fin 2,
                    2 ≤ (PEqualNP.TopForm.orIn n C (n + h)).card ∧
                    (∀ w ∈ PEqualNP.TopForm.orIn n C (n + h), G.Adj u w) ∧
                    PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C h b) = {v}))
    ) :
      ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
        (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → 5 ≤ x6.length) →
        x3.edgeFinset.Nonempty →
        ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x3 x7 →
          PEqualNP.TopForm.TopForm x3 x7 →
          {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 |
            ¬ ∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧
              ∃ x13 < x7.gates.length, ∃ (x14 : Fin 2),
                2 ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧
                (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧
                PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card
            ≤ x1 * (x7.size + 1) := by
  obtain ⟨k, hcore⟩ := core
  refine ⟨k, ?_⟩
  intro n G _ hGirth hne C hLeast hTop
  obtain ⟨H, hsub, hdeg, hEq⟩ := residual_core n G hGirth hne C hLeast hTop
  have hbound := hcore n G hGirth hne C H hLeast hTop hsub hdeg
  have hcount : H.edgeSet.ncard =
      ((PEqualNP.TopForm.Ustar G C).filter (fun e =>
        ¬ ∃ u v : Fin n, e = s(u, v) ∧
          ∃ h < C.gates.length, ∃ b : Fin 2,
            2 ≤ (PEqualNP.TopForm.orIn n C (n + h)).card ∧
            (∀ w ∈ PEqualNP.TopForm.orIn n C (n + h), G.Adj u w) ∧
            PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C h b) = {v})).card := by
    rw [hEq, Set.ncard_coe_finset]
  rw [← hcount]
  exact hbound
