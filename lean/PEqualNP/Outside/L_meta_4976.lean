import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

theorem PEqualNP.Outside.L_meta_4976 : ∀ (x1 : Finset (Fin (9 : ℕ))) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x1.card ≤ (2 : ℕ) → PEqualNP.NotBracket.notCount x2 = (0 : ℕ) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ PEqualNP.NotBracket.notCount x6 = (0 : ℕ) ∧ x6.size = x2.size + (2 : ℕ) ∧ ∀ (x7 : Fin (9 : ℕ) → Bool), x6.eval (List.ofFn x7) = x2.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x8 ∈ x1, x7 x8 = Bool.true)]) := by
  intro x1 x2 hFan hCard hNot
  refine ⟨⟨⟨GateOp.or, [0, 4]⟩ ::
    ⟨GateOp.or, x1.toList.map (fun i : Fin 9 => (i : ℕ))⟩ :: x2.gates,
    x2.output⟩, ?_, ?_, ?_, ?_⟩
  · -- FanInTwo
    intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · exact ⟨by simp, by simp⟩
    · refine ⟨by simp, ?_⟩
      rw [List.length_map, Finset.length_toList]
      exact hCard
    · exact hFan g hg
  · -- notCount
    have hnc : notCount ⟨⟨GateOp.or, [0, 4]⟩ ::
        ⟨GateOp.or, x1.toList.map (fun i : Fin 9 => (i : ℕ))⟩ :: x2.gates,
        x2.output⟩ = notCount x2 := by
      simp [notCount]
    rw [hnc, hNot]
  · -- size
    rfl
  · -- eval
    intro x7
    have hA : GateOp.or.eval (([0, 4] : List ℕ).map
        fun i => (List.ofFn x7).getD i false) = (x7 0 || x7 4) := by
      have e0 : (List.ofFn x7).getD 0 false = x7 0 := by simp
      have e4 : (List.ofFn x7).getD 4 false = x7 4 := by simp
      have hmap : ([0, 4] : List ℕ).map (fun i => (List.ofFn x7).getD i false)
          = [x7 0, x7 4] := by
        simp only [List.map_cons, List.map_nil, e0, e4]
      rw [hmap]
      cases h0 : x7 0 <;> cases h4 : x7 4 <;> rfl
    have hB : GateOp.or.eval ((x1.toList.map (fun i : Fin 9 => (i : ℕ))).map
        fun i => (List.ofFn x7 ++ [x7 0 || x7 4]).getD i false)
        = Decidable.decide (∃ x8 ∈ x1, x7 x8 = Bool.true) := by
      have h2 : ∀ a : Fin 9, (List.ofFn x7 ++ [x7 0 || x7 4]).getD (a : ℕ) false
          = x7 a := by
        intro a
        rw [List.getD_append]
        · rw [List.getD_eq_getElem _ _ (by simp)]
          exact List.getElem_ofFn (by simp)
        · simp
      simp only [GateOp.eval, List.any_map]
      by_cases h : ∃ x8 ∈ x1, x7 x8 = true
      · rw [decide_eq_true h, List.any_eq_true]
        obtain ⟨a, ha, hxa⟩ := h
        exact ⟨a, Finset.mem_toList.mpr ha, by
          simp only [Function.comp_apply]; rw [h2 a]; exact hxa⟩
      · rw [decide_eq_false h, List.any_eq_false]
        intro a ha
        rw [Finset.mem_toList] at ha
        simp only [Function.comp_apply]
        rw [h2 a]
        intro hxa
        exact h ⟨a, ha, hxa⟩
    have hW : Circuit.wires ⟨⟨GateOp.or, [0, 4]⟩ ::
          ⟨GateOp.or, x1.toList.map (fun i : Fin 9 => (i : ℕ))⟩ :: x2.gates,
          x2.output⟩ (List.ofFn x7)
        = Circuit.wires x2 (List.ofFn x7 ++ [x7 0 || x7 4,
            Decidable.decide (∃ x8 ∈ x1, x7 x8 = Bool.true)]) := by
      show List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x7)
          (⟨GateOp.or, [0, 4]⟩ ::
            ⟨GateOp.or, x1.toList.map (fun i : Fin 9 => (i : ℕ))⟩ :: x2.gates)
        = List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x7 ++ [x7 0 || x7 4,
            Decidable.decide (∃ x8 ∈ x1, x7 x8 = Bool.true)]) x2.gates
      rw [List.foldl_cons, List.foldl_cons]
      dsimp only
      rw [hA, hB, List.append_assoc, List.singleton_append]
    show (Circuit.wires ⟨⟨GateOp.or, [0, 4]⟩ ::
          ⟨GateOp.or, x1.toList.map (fun i : Fin 9 => (i : ℕ))⟩ :: x2.gates,
          x2.output⟩ (List.ofFn x7)).getD x2.output false
        = (Circuit.wires x2 (List.ofFn x7 ++ [x7 0 || x7 4,
            Decidable.decide (∃ x8 ∈ x1, x7 x8 = Bool.true)])).getD x2.output false
    rw [hW]
