import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1770_402
    (bottomBottom : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∃ EBB : Finset (Sym2 (Fin n)), EBB.card ≤ 204 * C.size ∧
        ∀ e ∈ Ustar G C,
          (∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C,
            ∃ g ∈ junk G C, ∃ h ∈ junk G C,
            g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
            gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
            (∀ j ∈ junk G C, ¬InCone n C j g) ∧ (∀ j ∈ junk G C, ¬InCone n C j h)) →
          e ∈ EBB)
    (bottomDeep : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∃ E : Finset (Sym2 (Fin n)), E.card ≤ k * (C.size + 1) ∧
        ∀ e ∈ Ustar G C,
          (¬∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ (b : Fin 2), ∃ g ∈ junk G C,
            u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧ gateVal n C g (pairInput u v) = true) →
          (∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ (b : Fin 2),
            ∃ g ∈ junk G C, ∃ h ∈ junk G C,
            g ≠ h ∧ OrReaches n C (opnd C a b) g ∧ OrReaches n C (opnd C a (1 - b)) h ∧
            gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
            (∀ j ∈ junk G C, ¬InCone n C j g) ∧ (∃ j ∈ junk G C, InCone n C j h)) →
          e ∈ E)
    (deepDeep : ∃ (k : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∃ E : Finset (Sym2 (Fin n)), E.card ≤ k * (C.size + 1) ∧
        ∀ e ∈ Ustar G C,
          (¬∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C, ∃ (b : Fin 2), ∃ g ∈ junk G C,
            u ∈ side C a b ∧ OrReaches n C (opnd C a (1 - b)) g ∧ gateVal n C g (pairInput u v) = true) →
          (∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧ ∃ a ∈ tops G C,
            ∃ g ∈ junk G C, ∃ h ∈ junk G C,
            g ≠ h ∧ OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
            gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true ∧
            (∃ j ∈ junk G C, InCone n C j g) ∧ (∃ j ∈ junk G C, InCone n C j h)) →
          e ∈ E) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | (¬∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ (x13 : Fin (2 : ℕ)), ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.side x5 x12 x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 ((1 : Fin (2 : ℕ)) - x13)) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true) ∧ ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  obtain ⟨k1, hk1⟩ := bottomDeep
  obtain ⟨k2, hk2⟩ := deepDeep
  refine ⟨204 + k1 + k2, ?_⟩
  intro n G _ C hG5 hL hT
  obtain ⟨EBB, hBB, mBB⟩ := bottomBottom n G C hG5 hL hT
  obtain ⟨EBD, hBD, mBD⟩ := hk1 n G C hG5 hL hT
  obtain ⟨EDD, hDD, mDD⟩ := hk2 n G C hG5 hL hT
  have hU1 := Finset.card_union_le (EBB ∪ EBD) EDD
  have hU2 := Finset.card_union_le EBB EBD
  have hBB' : EBB.card ≤ 204 * (C.size + 1) := hBB.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  calc _ ≤ (EBB ∪ EBD ∪ EDD).card := Finset.card_le_card (by
          intro e he
          rw [Finset.mem_filter] at he
          obtain ⟨heU, hns, u, v, rfl, a, ha, g1, hg1, g2, hg2, hne, hr1, hr2, hv1, hv2⟩ := he
          by_cases hd1 : ∃ j ∈ junk G C, InCone n C j g1
          · by_cases hd2 : ∃ j ∈ junk G C, InCone n C j g2
            · exact Finset.mem_union_right _
                (mDD s(u, v) heU hns ⟨u, v, rfl, a, ha, g1, hg1, g2, hg2, hne, hr1, hr2, hv1, hv2, hd1, hd2⟩)
            · refine Finset.mem_union_left _ (Finset.mem_union_right _
                (mBD s(u, v) heU hns ⟨u, v, rfl, a, ha, 1, g2, hg2, g1, hg1, hne.symm, hr2, ?_, hv2, hv1,
                  fun j hj hc => hd2 ⟨j, hj, hc⟩, hd1⟩))
              simpa [show (1 : Fin 2) - 1 = 0 by decide] using hr1
          · by_cases hd2 : ∃ j ∈ junk G C, InCone n C j g2
            · refine Finset.mem_union_left _ (Finset.mem_union_right _
                (mBD s(u, v) heU hns ⟨u, v, rfl, a, ha, 0, g1, hg1, g2, hg2, hne, hr1, ?_, hv1, hv2,
                  fun j hj hc => hd1 ⟨j, hj, hc⟩, hd2⟩))
              simpa [show (1 : Fin 2) - 0 = 1 by decide] using hr2
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (mBB s(u, v) heU ⟨u, v, rfl, a, ha, g1, hg1, g2, hg2, hne, hr1, hr2, hv1, hv2,
                  fun j hj hc => hd1 ⟨j, hj, hc⟩, fun j hj hc => hd2 ⟨j, hj, hc⟩⟩)))
    _ ≤ EBB.card + EBD.card + EDD.card := by omega
    _ ≤ 204 * (C.size + 1) + k1 * (C.size + 1) + k2 * (C.size + 1) := by omega
    _ = (204 + k1 + k2) * (C.size + 1) := by ring
