import PEqualNP.Defs

-- Select one operand of each top whose reachable junk gates all have a small OR support.
-- The counting hypothesis charges only edge witnesses with such a junk gate.

theorem PEqualNP.Outside.R_meta_3807_428
    (thin : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C →
      ∀ t ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
        ∀ g ∈ PEqualNP.TopForm.junk G C,
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C t b) g →
            ∃ k : Fin 2, (have S : Finset (Fin n) := PEqualNP.TopForm.side C g k; S.card ≤ 14))
    (charge : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∀ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x13 ∈ PEqualNP.TopForm.junk x3 x7, ¬PEqualNP.EdgeOwnership.InCone x2 x7 x11 x13) → ∀ (picked : Finset (Sym2 (Fin x2))),
  (∀ e ∈ picked, e ∈ PEqualNP.TopForm.Ustar x3 x7 ∧
    ∃ t ∈ PEqualNP.TopForm.tops x3 x7, ∃ b : Fin 2,
    ∃ g ∈ PEqualNP.TopForm.junk x3 x7, ∃ h ∈ PEqualNP.TopForm.junk x3 x7,
      g ≠ h ∧
      PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 t b) g ∧
      PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 t (1 - b)) h ∧
      (∃ k : Fin 2, (have S : Finset (Fin x2) := PEqualNP.TopForm.side x7 g k; S.card ≤ 14)) ∧
      e ∈ PEqualNP.TopForm.gammaE x3 x7 g ∧ e ∈ PEqualNP.TopForm.gammaE x3 x7 h) → picked.card ≤
        x1 * (x7.size + 1)) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∀ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x13 ∈ PEqualNP.TopForm.junk x3 x7, ¬PEqualNP.EdgeOwnership.InCone x2 x7 x11 x13) → {x12 ∈ PEqualNP.TopForm.Ustar x3 x7 | ∃ (x13 : Fin x2) (x14 : Fin x2), x12 = s(x13, x14) ∧ ∃ x15 ∈ PEqualNP.TopForm.tops x3 x7, ∃ x16 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x17 ∈ PEqualNP.TopForm.junk x3 x7, x16 ≠ x17 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 (0 : Fin (2 : ℕ))) x16 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 (1 : Fin (2 : ℕ))) x17 ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x16 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x17 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨K, hK⟩ := charge
  refine ⟨K, ?_⟩
  intro n G d hG hE C hleast htop hnum hsep
  refine hK n G hG hE C hleast htop hnum hsep _ ?_
  intro e he
  obtain ⟨hu, a, b, hab, t, ht, g, hg, h, hh, hne, hrg, hrh, hvg, hvh⟩ :=
    Finset.mem_filter.mp he
  have hedge : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp hu).1
  have hge : e ∈ PEqualNP.TopForm.gammaE G C g := Finset.mem_filter.mpr
    ⟨hedge, a, b, hab, hvg⟩
  have hhe : e ∈ PEqualNP.TopForm.gammaE G C h := Finset.mem_filter.mpr
    ⟨hedge, a, b, hab, hvh⟩
  obtain ⟨side, hside⟩ := thin n G hG C hleast.1 t ht
  have h01 : (1 : Fin 2) - 0 = 1 := by decide
  have h10 : (1 : Fin 2) - 1 = 0 := by decide
  fin_cases side
  · exact
      ⟨hu, t, ht, 0, g, hg, h, hh, hne, hrg, h01.symm ▸ hrh, hside g hg hrg, hge, hhe⟩
  · exact
      ⟨hu, t, ht, 1, h, hh, g, hg, hne.symm, hrh, h10.symm ▸ hrg, hside h hh hrh, hhe, hge⟩
