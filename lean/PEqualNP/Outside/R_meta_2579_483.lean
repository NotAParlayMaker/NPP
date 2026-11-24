import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- A pin has two classes of edge input, according to whether the source has
-- an earlier active junk ancestor. Remove any occupied class of at most d
-- surviving edges, then reconsider the other classes. Once removed, a class
-- stays empty. The circuit has four classes per gate, including both pins.
-- In the residual problem every occupied junk handoff is shared by more than
-- d edges at that same reader pin and in that same nesting class.
theorem PEqualNP.Outside.R_meta_2579_483
    (zero : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → x2.edgeFinset.Nonempty → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x6 → PEqualNP.TopForm.TopForm x2 x6 → PEqualNP.TopForm.junk x2 x6 = ∅ → PEqualNP.TopForm.Ustar x2 x6 = ∅)
    (one : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : ℕ), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → PEqualNP.TopForm.junk x3 x7 = {x8} → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)))
    (core : ∃ d k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C → 2 ≤ (junk G C).card →
      ∀ H : Finset (Sym2 (Fin n)), H ⊆ Ustar G C →
      (∀ u v, s(u,v) ∈ H → ∀ j < C.gates.length, ∀ b : Fin 2,
        2 ≤ (orIn n C (n+j)).card → (∀ w ∈ orIn n C (n+j), G.Adj u w) →
        orIn n C (opnd C j b) ≠ {v}) →
      (∀ j < C.size, ∀ b : Fin 2, ∀ g ∈ junk G C, opnd C j b = n+g →
        ∀ t : Bool, let F := (gammaE G C j ∩ gammaE G C g).filter fun e =>
          (t = true ↔ ∃ a ∈ junk G C, InCone n C a g ∧ e ∈ gammaE G C a)
        (H ∩ F).Nonempty → d < (H ∩ F).card) →
      H.card ≤ k*(C.size+1)) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨d, k, hcore⟩ := core
  obtain ⟨c, hsingle⟩ := one
  refine ⟨c + (k + 4*d), ?_⟩
  intro n G inst hg he C hC ht
  let E := (Ustar G C).filter fun e => ¬∃ u v : Fin n, e = s(u,v) ∧
    ∃ j < C.gates.length, ∃ b : Fin 2, 2 ≤ (orIn n C (n+j)).card ∧
      (∀ w ∈ orIn n C (n+j), G.Adj u w) ∧ orIn n C (opnd C j b) = {v}
  change E.card ≤ (c + (k + 4*d)) * (C.size+1)
  by_cases large : 2 ≤ (junk G C).card
  · let I := Fin C.size × Fin 2 × Bool
    let P (i : I) : Finset (Sym2 (Fin n)) :=
      let g := opnd C i.1 i.2.1 - n
      (gammaE G C i.1 ∩ gammaE G C g).filter fun e =>
        (i.2.2 = true ↔ ∃ a ∈ junk G C, InCone n C a g ∧ e ∈ gammaE G C a)
    have peel (J : Finset I) : ∀ X : Finset (Sym2 (Fin n)), ∃ Y ⊆ X,
        X.card ≤ Y.card + d*J.card ∧
        ∀ i ∈ J, (Y ∩ P i).Nonempty → d < (Y ∩ P i).card := by
      induction J using Finset.strongInduction with
      | H J ih =>
        intro X
        by_cases good : ∀ i ∈ J, (X ∩ P i).Nonempty → d < (X ∩ P i).card
        · exact ⟨X, Finset.Subset.rfl, by omega, good⟩
        · push Not at good
          obtain ⟨i, hi, alive, few⟩ := good
          obtain ⟨Y, hY, cost, dense⟩ := ih (J.erase i) (Finset.erase_ssubset hi) (X \ P i)
          have split := Finset.card_sdiff_add_card_inter X (P i)
          have sizeJ : J.card = (J.erase i).card + 1 := by
            have hpos := Finset.card_pos.mpr ⟨i,hi⟩
            rw [Finset.card_erase_of_mem hi]
            omega
          refine ⟨Y, hY.trans Finset.sdiff_subset, ?_, ?_⟩
          · rw [sizeJ, Nat.mul_add, Nat.mul_one]
            omega
          · intro a ha occupied
            rcases eq_or_ne a i with rfl | h
            · obtain ⟨e, he⟩ := occupied
              exact False.elim ((Finset.mem_sdiff.mp (hY (Finset.mem_inter.mp he).1)).2
                (Finset.mem_inter.mp he).2)
            · exact dense a (Finset.mem_erase.mpr ⟨h,ha⟩) occupied
    obtain ⟨Y, sub, cost, dense⟩ := peel Finset.univ E
    have price := hcore n G hg he C hC ht large Y
      (sub.trans (Finset.filter_subset _ _)) (by
        intro u v huv j hj b hb hall heq
        exact (Finset.mem_filter.mp (sub huv)).2 ⟨u,v,rfl,j,hj,b,hb,hall,heq⟩) (by
        intro j hj b g _ hwire t
        have h := dense (⟨j,hj⟩,b,t) (Finset.mem_univ _)
        have same : opnd C j b - n = g := by omega
        cases same
        exact h)
    have hnum : (Finset.univ : Finset I).card = C.size * 4 := by simp [I, Nat.mul_assoc]
    rw [hnum] at cost
    calc
      E.card ≤ k*(C.size+1) + d*(C.size*4) := by omega
      _ ≤ k*(C.size+1) + d*((C.size+1)*4) := by gcongr <;> omega
      _ = (k+4*d)*(C.size+1) := by ring
      _ ≤ (c+(k+4*d))*(C.size+1) := Nat.mul_le_mul_right _ (by omega)
  · have hu : E ⊆ Ustar G C := Finset.filter_subset _ _
    by_cases empty : junk G C = ∅
    · have hz := zero n G hg he C hC ht empty
      rw [hz] at hu
      have eh := Finset.subset_empty.mp hu
      simp [eh]
    · have hj : (junk G C).card = 1 := by
        have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
        omega
      obtain ⟨g,hg'⟩ := Finset.card_eq_one.mp hj
      have bound := hsingle n G hg he C g hC ht hg'
      exact (Finset.card_le_card hu).trans (bound.trans (Nat.mul_le_mul_right _ (by omega)))
