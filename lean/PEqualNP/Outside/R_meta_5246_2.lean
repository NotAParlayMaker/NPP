import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5246_2
    (hThree :
      ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
        (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
        x3.edgeFinset.Nonempty →
        ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x3 x7 →
          PEqualNP.TopForm.TopForm x3 x7 →
          (PEqualNP.TopForm.junk x3 x7).card = (3 : ℕ) →
          (¬∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7,
            x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) →
          (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))),
            x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧
            ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨
              ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧
                ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
          ((PEqualNP.TopForm.Ustar x3 x7).filter (fun e =>
            ∃ (u : Fin x2) (v : Fin x2), e = s(u, v) ∧
              (4 : ℕ) < x3.degree u ∧ (4 : ℕ) < x3.degree v)).card ≤ x1 * (x7.size + (1 : ℕ)))
    (hFour :
      ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
        (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
        x3.edgeFinset.Nonempty →
        ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x3 x7 →
          PEqualNP.TopForm.TopForm x3 x7 →
          (4 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
          (¬∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7,
            x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) →
          (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))),
            x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧
            ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨
              ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧
                ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
          ((PEqualNP.TopForm.Ustar x3 x7).filter (fun e =>
            ∃ (u : Fin x2) (v : Fin x2), e = s(u, v) ∧
              (4 : ℕ) < x3.degree u ∧ (4 : ℕ) < x3.degree v)).card ≤ x1 * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (¬∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  -- step one: wires agree away from an input wire that no gate reads
  have key : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w w' : List Bool) (u : ℕ),
      (∀ g ∈ gs, u ∉ g.inputs) → w.length = w'.length →
      (∀ i, i ≠ u → w.getD i false = w'.getD i false) →
      ∀ i, i ≠ u →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
            i false =
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD
            i false := by
    intro gs
    induction gs with
    | nil => intro w w' u _ _ h i hi; exact h i hi
    | cons g gs ih =>
      intro w w' u hg hl h
      simp only [List.foldl_cons]
      apply ih _ _ u (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      · simp [hl]
      · have hb : g.op.eval (g.inputs.map fun i => w.getD i false) =
            g.op.eval (g.inputs.map fun i => w'.getD i false) := by
          congr 1
          apply List.map_congr_left
          intro i hi
          exact h i (fun e => hg g (List.mem_cons_self) (e ▸ hi))
        rw [hb]
        intro i hi
        by_cases hlt : i < w.length
        · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hl ▸ hlt)]
          exact h i hi
        · push Not at hlt
          rw [List.getD_append_right _ _ _ _ hlt, List.getD_append_right _ _ _ _ (hl ▸ hlt), hl]
  -- step two: every endpoint of an edge is read by a gate or is the output wire
  have readEnd : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∀ u v : Fin n, G.Adj u v →
        ((u : ℕ) = C.output ∨ ∃ g ∈ C.gates, (u : ℕ) ∈ g.inputs) := by
    intro n G _ C hf u v huv
    by_contra hno
    push Not at hno
    obtain ⟨hout, hrd⟩ := hno
    have h1 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
        (PEqualNP.EdgeOwnership.pairInput u v) = true := by
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,
        PEqualNP.EdgeOwnership.pairInput, Finset.notMem_empty, false_and, exists_false,
        decide_false, Bool.false_or, decide_eq_true_eq]
      exact ⟨u, v, huv, by simp, by simp⟩
    have h2 : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
        (PEqualNP.EdgeOwnership.pairInput v v) = false := by
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,
        PEqualNP.EdgeOwnership.pairInput, Finset.notMem_empty, false_and, exists_false,
        decide_false, Bool.false_or, or_self, decide_eq_false_iff_not, not_exists, not_and]
      intro a b hab ha hb
      simp only [decide_eq_true_eq] at ha hb
      subst ha; subst hb
      exact G.irrefl hab
    have e1 := congrFun hf (PEqualNP.EdgeOwnership.pairInput u v)
    have e2 := congrFun hf (PEqualNP.EdgeOwnership.pairInput v v)
    rw [h1] at e1
    rw [h2] at e2
    have hagree := key C.gates (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))
      (List.ofFn (PEqualNP.EdgeOwnership.pairInput v v)) u hrd (by simp) (by
        intro i hi
        by_cases hin : i < n
        · rw [List.getD_eq_getElem _ _ (by simpa using hin),
            List.getD_eq_getElem _ _ (by simpa using hin)]
          simp only [List.getElem_ofFn, PEqualNP.EdgeOwnership.pairInput]
          have : (⟨i, hin⟩ : Fin n) ≠ u := fun e => hi (by rw [← e])
          simp [this]
        · push Not at hin
          rw [List.getD_eq_default _ _ (by simpa using hin),
            List.getD_eq_default _ _ (by simpa using hin)]) C.output (Ne.symm hout)
    have : PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) =
        PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.EdgeOwnership.pairInput v v) := hagree
    rw [e1, e2] at this
    exact Bool.noConfusion this
  -- step three: the wires read by some gate, with the output, number at most 2 size + 1
  have readCard : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ C.gates, g.inputs.length = 2) →
      (Finset.univ.filter (fun u : Fin n =>
        (u : ℕ) = C.output ∨ ∃ g ∈ C.gates, (u : ℕ) ∈ g.inputs)).card ≤ 2 * C.size + 1 := by
    intro n C h2
    let L : List ℕ := C.output :: C.gates.flatMap (fun g => g.inputs)
    have hlen : L.length = 2 * C.size + 1 := by
      have : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate, (∀ g ∈ gs, g.inputs.length = 2) →
          (gs.flatMap (fun g => g.inputs)).length = 2 * gs.length := by
        intro gs
        induction gs with
        | nil => intro _; simp
        | cons g gs ih =>
          intro h
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          rw [h g List.mem_cons_self, ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))]
          ring
      simp only [L, List.length_cons, this C.gates h2, PEqualNP.CircuitLowerBounds.Circuit.size]
    have hsub : (Finset.univ.filter (fun u : Fin n =>
        (u : ℕ) = C.output ∨ ∃ g ∈ C.gates, (u : ℕ) ∈ g.inputs)).map Fin.valEmbedding ⊆
          L.toFinset := by
      intro x hx
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      simp only [L, List.mem_toFinset, List.mem_cons, List.mem_flatMap]
      rcases hu with h | ⟨g, hg, hi⟩
      · exact Or.inl h
      · exact Or.inr ⟨g, hg, hi⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_map] at this
    have := List.toFinset_card_le L
    omega
  obtain ⟨c1, h1⟩ := hThree
  obtain ⟨c2, h2⟩ := hFour
  refine ⟨max c1 c2 + 8, ?_⟩
  intro n G _ hg he C hL hT hj hnd hno
  -- the high part
  have hHigh : ((PEqualNP.TopForm.Ustar G C).filter (fun e =>
      ∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧
        (4 : ℕ) < G.degree u ∧ (4 : ℕ) < G.degree v)).card ≤ max c1 c2 * (C.size + 1) := by
    by_cases h3 : (PEqualNP.TopForm.junk G C).card = 3
    · exact le_trans (h1 n G hg he C hL hT h3 hnd hno)
        (Nat.mul_le_mul_right _ (le_max_left _ _))
    · have h4 : 4 ≤ (PEqualNP.TopForm.junk G C).card := by omega
      exact le_trans (h2 n G hg he C hL hT h4 hnd hno)
        (Nat.mul_le_mul_right _ (le_max_right _ _))
  -- the low part: edges with an endpoint of degree at most four
  let R : Finset (Fin n) := Finset.univ.filter (fun u : Fin n =>
    (u : ℕ) = C.output ∨ ∃ g ∈ C.gates, (u : ℕ) ∈ g.inputs)
  have hR : R.card ≤ 2 * C.size + 1 := readCard n C hL.1.2.2
  let Rl : Finset (Fin n) := R.filter (fun u => G.degree u ≤ 4)
  have hLow : ((PEqualNP.TopForm.Ustar G C).filter (fun e =>
      ¬ ∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧
        (4 : ℕ) < G.degree u ∧ (4 : ℕ) < G.degree v)).card ≤ 8 * (C.size + 1) := by
    have hsub : (PEqualNP.TopForm.Ustar G C).filter (fun e =>
        ¬ ∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧
          (4 : ℕ) < G.degree u ∧ (4 : ℕ) < G.degree v) ⊆
          Rl.biUnion (fun u => G.incidenceFinset u) := by
      intro e he'
      rw [Finset.mem_filter] at he'
      obtain ⟨heU, hnot⟩ := he'
      have heE : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp heU).1
      induction e using Sym2.ind with
      | h u v =>
        have huv : G.Adj u v := by simpa using heE
        push Not at hnot
        have hcase : G.degree u ≤ 4 ∨ G.degree v ≤ 4 := by
          by_contra hc
          push Not at hc
          exact absurd (hnot u v rfl hc.1) (not_le.mpr hc.2)
        rw [Finset.mem_biUnion]
        rcases hcase with hu | hv
        · refine ⟨u, ?_, ?_⟩
          · simp only [Rl, R, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨readEnd n G C hL.2.1 u v huv, hu⟩
          · rw [SimpleGraph.mem_incidenceFinset]
            exact G.mk'_mem_incidenceSet_left_iff.mpr huv
        · refine ⟨v, ?_, ?_⟩
          · simp only [Rl, R, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨readEnd n G C hL.2.1 v u huv.symm, hv⟩
          · rw [SimpleGraph.mem_incidenceFinset]
            exact G.mk'_mem_incidenceSet_right_iff.mpr huv
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_biUnion_le (s := Rl) (t := fun u => G.incidenceFinset u)
    have hc3 : ∑ u ∈ Rl, (G.incidenceFinset u).card ≤ ∑ _u ∈ Rl, 4 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [SimpleGraph.card_incidenceFinset_eq_degree]
      exact (Finset.mem_filter.mp hu).2
    have hc4 : Rl.card ≤ R.card := Finset.card_filter_le _ _
    rw [Finset.sum_const, smul_eq_mul] at hc3
    nlinarith
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := PEqualNP.TopForm.Ustar G C) (fun e =>
      ∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧
        (4 : ℕ) < G.degree u ∧ (4 : ℕ) < G.degree v)
  have hm : (max c1 c2 + 8) * (C.size + 1) = max c1 c2 * (C.size + 1) + 8 * (C.size + 1) := by
    ring
  omega
