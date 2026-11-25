import PEqualNP.Defs
import Mathlib.Tactic.FinCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.LowMerge
open PEqualNP.CleanedNonEdge PEqualNP.GenericRejection PEqualNP.ReadTwo

-- Recover the actual output OR frontier; the leased family need not be that frontier.
-- The counting child retains strict separation on every quadrangle and allows shared OR nodes.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5278_897
    (frontier : ∀ (n : ℕ) (R : Finset (List Bool)) (C : Circuit),
      IsAO2 n C →
      (∀ x ∈ R, x.length = n) →
      (∀ i < n, ∃ x ∈ R, x.getD i false = true) →
      (∀ x ∈ R, C.eval x = false) →
      let K := gatesWhere C (OrToOutput n C)
      let J := K.filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval [false, true] = false)
      orIn n C C.output = ∅ ∧
      (∀ j ∈ K, ∀ x ∈ R, wireVal C x (n+j) = false) ∧
      J.card ≤ (K \ J).card + 1 ∧
      ∀ x : List Bool, x.length = n →
        (C.eval x = true ↔ ∃ j ∈ J, wireVal C x (n+j) = true))
    (count :
      let S := singerLines3
      let N (Q : Finset (Fin 13)) := incidenceInput Q (missLines S Q)
      let Qs := quadrangles S
      ∀ C : Circuit,
      let G := PEqualNP.MetaComplexity.NestedCover.gateAt C
      let W := wireVal C
      let K := gatesWhere C (OrToOutput 26 C)
      let J := K.filter (fun j => (G j).op.eval [false, true] = false)
      IsAO2 26 C → 38 ≤ C.size →
      (8 ≤ nAnd C ∧ 18 ≤ nOr C) →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      2 ≤ andPairs 26 C →
      (∀ j, isAnd C j → ∀ i ∈ (G j).inputs,
        ∃ Q ∈ Qs, W (N Q) (26+j) ≠ W (N Q) i) →
      orIn 26 C C.output = ∅ →
      (∀ j ∈ K, ∀ Q ∈ Qs, W (N Q) (26+j) = false) →
      J.card ≤ (K \ J).card + 1 →
      (∀ p l : Fin 13, p ∈ S l →
        ∃ j ∈ J, W (pointLineInput 13 13 p l) (26+j) = true) →
      64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : Finset (Finset (Fin (13 : ℕ))) := PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;   have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;   PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (38 : ℕ) ≤ x3.size → x3.size < (64 : ℕ) → (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3 → (∀ x11 ∈ x3.gates, x11.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x11.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ x13 < x3.size, (x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x16 ∈ (x5 x13).inputs, ∃ x18 ∈ x2, x6 (x1 x18) ((26 : ℕ) + x13) ≠ x6 (x1 x18) x16) → (∀ x14 ∈ x4, x14 < x3.size ∧ (x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x16 ∈ x2, x6 (x1 x16) ((26 : ℕ) + x14) = Bool.false) → (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) → (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x3.eval x16 = Bool.true ↔ ∃ x18 ∈ x4, x6 x16 ((26 : ℕ) + x18) = Bool.true)) → (∀ (x17 x18 : Fin (13 : ℕ)), x17 ∈ PEqualNP.HeptadCover.singerLines3 x18 → ∃ x20 ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x17 x18) ((26 : ℕ) + x20) = Bool.true) → False := by
  intro N Qs C A G W ao low small counts distinct nested strict safe oldBudget cover posA
  let R : Finset (List Bool) := Qs.image N
  have rowLength (Q : Finset (Fin 13)) : (N Q).length = 26 := by
    change (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))).length = 26
    simp
  have lengths : ∀ x ∈ R, x.length = 26 := by
    intro x hx
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hx
    exact rowLength Q
  have inputsCovered : ∀ i : Fin 26,
      ∃ Q ∈ Qs, (N Q).getD i.val false = true := by
    intro i
    fin_cases i
    · refine ⟨({0, 1, 2, 5} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 5} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 5} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 2, 3, 4} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 4, 6} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 5} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 6} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 7} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 4, 8} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 2, 4, 9} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 5, 10} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 11} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 4, 12} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({2, 4, 5, 6} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 3, 5, 6} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 4, 6} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 5} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({1, 2, 3, 6} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 2, 3, 4} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 4, 8} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 5} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 5} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 1, 2, 6} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({1, 2, 3, 7} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({0, 2, 3, 4} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
    · refine ⟨({1, 3, 4, 5} : Finset (Fin 13)), ?_, ?_⟩
      · simp only [Qs, quadrangles, Finset.mem_filter, Finset.mem_powersetCard,
          Finset.subset_univ, true_and]
        decide
      · decide
  have rawCovered : ∀ i < 26, ∃ x ∈ R, x.getD i false = true := by
    intro i hi
    obtain ⟨Q, hQ, hv⟩ := inputsCovered ⟨i, hi⟩
    exact ⟨N Q, Finset.mem_image_of_mem N hQ, hv⟩
  have negative : ∀ x ∈ R, C.eval x = false := by
    intro x hx
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hx
    cases he : C.eval (N Q) with
    | false => rfl
    | true =>
      obtain ⟨j, hj, ht⟩ := (cover (N Q) (rowLength Q)).mp he
      have hz := (safe j hj).2.2 Q hQ
      have bad : (false : Bool) = true := hz.symm.trans ht
      cases bad
  have pairLength (p l : Fin 13) : (pointLineInput 13 13 p l).length = 26 := by
    simp [pointLineInput, restrictInput]
  have positive (p l : Fin 13) (h : p ∈ singerLines3 l) :
      C.eval (pointLineInput 13 13 p l) = true :=
    (cover (pointLineInput 13 13 p l) (pairLength p l)).mpr (posA p l h)
  obtain ⟨noRaw, zeroK, budgetJ, coverJ⟩ :=
    frontier 26 R C ao lengths rawCovered negative
  have nodup : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (ao.2.2 g hg)
    simpa [hab] using distinct g hg
  have lower : 64 ≤ C.size := by
    apply count C ao low counts nodup nested
    · intro j hj i hi
      exact strict j hj.1 hj.2 i hi
    · exact noRaw
    · intro j hj Q hQ
      exact zeroK j hj (N Q) (Finset.mem_image_of_mem N hQ)
    · exact budgetJ
    · intro p l hp
      exact (coverJ (pointLineInput 13 13 p l) (pairLength p l)).mp (positive p l hp)
  exact (Nat.not_le_of_gt small lower).elim
