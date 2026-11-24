import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1597_1 :
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
       (∀ u v : Fin 11, G.Adj u v ↔ Nat.testBit 110600787412925398093569809860560384 (11 * u.val + v.val) = true) →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let J : Finset ℕ := PEqualNP.TopForm.junk G D
       (∀ a ∈ T,
         let S0 : Finset (Fin 11) := PEqualNP.TopForm.side (n := 11) D a 0
         let S1 : Finset (Fin 11) := PEqualNP.TopForm.side (n := 11) D a 1
         Disjoint S0 S1 ∧ (∀ u ∈ S0, ∀ v ∈ S1, G.Adj u v) ∧ (S0.card ≤ 1 ∨ S1.card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ PEqualNP.TopForm.Ustar G D → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       16 + (T \ C0).card + 2 * C0.card + J.card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ D.size + (PEqualNP.TopForm.Ustar G D).card + 1 →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G D)) K → K.card ≤ (T \ C0).card) →
       3 ≤ J.card → 22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : ℕ),
       (∀ u v : Fin 11, G.Adj u v ↔ Nat.testBit 110600787412925398093569809860560384 (11 * u.val + v.val) = true) →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let J : Finset ℕ := PEqualNP.TopForm.junk G D
       (∀ a ∈ T,
         let S0 : Finset (Fin 11) := PEqualNP.TopForm.side (n := 11) D a 0
         let S1 : Finset (Fin 11) := PEqualNP.TopForm.side (n := 11) D a 1
         Disjoint S0 S1 ∧ (∀ u ∈ S0, ∀ v ∈ S1, G.Adj u v) ∧ (S0.card ≤ 1 ∨ S1.card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ PEqualNP.TopForm.Ustar G D → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       16 + (T \ C0).card + 2 * C0.card + J.card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ D.size + (PEqualNP.TopForm.Ustar G D).card + 1 →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G D)) K → K.card ≤ (T \ C0).card) →
       J = {g1, g2} → PEqualNP.EdgeOwnership.InCone 11 D g1 g2 → 22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : ℕ),
       (∀ u v : Fin 11, G.Adj u v ↔ Nat.testBit 110600787412925398093569809860560384 (11 * u.val + v.val) = true) →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let J : Finset ℕ := PEqualNP.TopForm.junk G D
       (∀ a ∈ T,
         let S0 : Finset (Fin 11) := PEqualNP.TopForm.side (n := 11) D a 0
         let S1 : Finset (Fin 11) := PEqualNP.TopForm.side (n := 11) D a 1
         Disjoint S0 S1 ∧ (∀ u ∈ S0, ∀ v ∈ S1, G.Adj u v) ∧ (S0.card ≤ 1 ∨ S1.card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ PEqualNP.TopForm.Ustar G D → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       16 + (T \ C0).card + 2 * C0.card + J.card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ D.size + (PEqualNP.TopForm.Ustar G D).card + 1 →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G D)) K → K.card ≤ (T \ C0).card) →
       g1 ≠ g2 → J = {g1, g2} → ¬ PEqualNP.EdgeOwnership.InCone 11 D g1 g2 → ¬ PEqualNP.EdgeOwnership.InCone 11 D g2 g1 →
       (∃ a ∈ T, PEqualNP.EdgeOwnership.InCone 11 D g1 a ∧ PEqualNP.EdgeOwnership.InCone 11 D g2 a) → 22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : ℕ),
       (∀ u v : Fin 11, G.Adj u v ↔ Nat.testBit 110600787412925398093569809860560384 (11 * u.val + v.val) = true) →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let J : Finset ℕ := PEqualNP.TopForm.junk G D
       (∀ a ∈ T,
         let S0 : Finset (Fin 11) := PEqualNP.TopForm.side (n := 11) D a 0
         let S1 : Finset (Fin 11) := PEqualNP.TopForm.side (n := 11) D a 1
         Disjoint S0 S1 ∧ (∀ u ∈ S0, ∀ v ∈ S1, G.Adj u v) ∧ (S0.card ≤ 1 ∨ S1.card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ PEqualNP.TopForm.Ustar G D → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       16 + (T \ C0).card + 2 * C0.card + J.card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ D.size + (PEqualNP.TopForm.Ustar G D).card + 1 →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G D)) K → K.card ≤ (T \ C0).card) →
       g1 ≠ g2 → J = {g1, g2} → ¬ PEqualNP.EdgeOwnership.InCone 11 D g1 g2 → ¬ PEqualNP.EdgeOwnership.InCone 11 D g2 g1 →
       (∀ a ∈ T, PEqualNP.EdgeOwnership.InCone 11 D g1 a → ¬ PEqualNP.EdgeOwnership.InCone 11 D g2 a) → 22 ≤ D.size) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → (∀ a ∈ PEqualNP.TopForm.tops G C, Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧ (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧ ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C → ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧ PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card + 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧ ∀ K : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K → K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → PEqualNP.TopForm.TopForm (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → 2 ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D).card → 22 ≤ D.size := by
  intro c1 c2 c3 c4 h1 h2 D hL hT hj2
  set G0 := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  change 2 ≤ (PEqualNP.TopForm.junk G0 D).card at hj2
  have hnf : PEqualNP.TopForm.NoFourCycle G0 := by decide
  have hne : G0.edgeFinset.Nonempty := by decide
  have hecard : G0.edgeFinset.card = 16 := by decide
  obtain ⟨hstar, hoff⟩ := h1 11 G0 D hnf hne hL hT
  obtain ⟨hcnt, hcov⟩ := h2 11 G0 D hnf hne hL hT
  rw [hecard] at hcnt
  have hG0 : ∀ u v : Fin 11, G0.Adj u v ↔ Nat.testBit 110600787412925398093569809860560384 (11 * u.val + v.val) = true := by decide
  by_cases hj3 : 3 ≤ (PEqualNP.TopForm.junk G0 D).card
  · exact c1 G0 D hG0 hL hT hstar hoff hcnt hcov hj3
  · have hj_eq2 : (PEqualNP.TopForm.junk G0 D).card = 2 := by omega
    obtain ⟨g1, g2, hne12, hjset⟩ := Finset.card_eq_two.mp hj_eq2
    by_cases hc12 : PEqualNP.EdgeOwnership.InCone 11 D g1 g2
    · exact c2 G0 D g1 g2 hG0 hL hT hstar hoff hcnt hcov hjset hc12
    · by_cases hc21 : PEqualNP.EdgeOwnership.InCone 11 D g2 g1
      · rw [Finset.pair_comm] at hjset
        exact c2 G0 D g2 g1 hG0 hL hT hstar hoff hcnt hcov hjset hc21
      · by_cases hsh : ∃ a ∈ PEqualNP.TopForm.tops G0 D, PEqualNP.EdgeOwnership.InCone 11 D g1 a ∧ PEqualNP.EdgeOwnership.InCone 11 D g2 a
        · exact c3 G0 D g1 g2 hG0 hL hT hstar hoff hcnt hcov hne12 hjset hc12 hc21 hsh
        · refine c4 G0 D g1 g2 hG0 hL hT hstar hoff hcnt hcov hne12 hjset hc12 hc21 ?_
          intro a ha hg1
          exact fun hg2 => hsh ⟨a, ha, hg1, hg2⟩
