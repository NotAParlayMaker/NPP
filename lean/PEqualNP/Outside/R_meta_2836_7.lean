import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2836_7
    (h1 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 0 false) ++
          [x 0 || x 4, x 0 || x 3]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      False)
    (h2 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn (Function.update x 4 false) ++
          [x 0 || x 4, x 4 || x 1]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      False)
    (h3 : ∀ v ∈ ([1, 2, 3, 6] : List (Fin 9)), ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [false, x 0 || x 4 || x v]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : (Fin (9 : ℕ) → Bool) → Bool := fun (x2 : Fin (9 : ℕ) → Bool) => x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (4 : Fin (9 : ℕ)) || x2 (4 : Fin (9 : ℕ)) && x2 (0 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ));   PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ((∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ))]) = x2 x5) ∨ ∃ (x5 : Fin (9 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) ∧ x5 ≠ (4 : Fin (9 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [Bool.false, x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x5]) = x2 x6) → False := by
  intro C F hfan hs hcase
  -- the symmetry (1 5)(2 8)(6 7) of the graph, which fixes the vertices 0, 3 and 4
  have hF0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
      (b0 && b5 || b5 && b8 || b8 && b3 || b3 && b4 || b4 && b0 || b0 && b1 ||
        b5 && b7 || b8 && b6 || b3 && b2 || b1 && b6 || b7 && b2 || b2 && b1) =
      (b0 && b1 || b1 && b2 || b2 && b3 || b3 && b4 || b4 && b0 || b0 && b5 ||
        b1 && b6 || b2 && b7 || b3 && b8 || b5 && b7 || b6 && b8 || b8 && b5) := by
    decide
  have hlt : ∀ j : ℕ, j < 9 → List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j < 9 := by
    intro j hj
    interval_cases j <;> decide
  have hge : ∀ j : ℕ, 9 ≤ j → List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j = j := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl
  have hpre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length → 9 ≤ W.length →
      (∀ j : ℕ, W'.getD (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j) false = W.getD j false) →
      ∀ j : ℕ,
        ((gs.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
            PEqualNP.CircuitLowerBounds.Gate.mk g.op
              (g.inputs.map fun i => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD
            (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD
          j false := by
    intro gs
    induction gs with
    | nil =>
      intro W W' _ _ hW j
      exact hW j
    | cons g gs ih =>
      intro W W' hl h9 hW
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp [hl]
      · simp
        omega
      · have hv : g.op.eval ((g.inputs.map fun i => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i).map
            fun i => W'.getD i false) = g.op.eval (g.inputs.map fun i => W.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hW i
        intro j
        rw [hv]
        by_cases hj : j < W.length
        · have hj' : List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j < W'.length := by
            by_cases h : j < 9
            · have := hlt j h
              omega
            · rw [hge j (by omega)]
              omega
          have hWj := hW j
          generalize List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j = r at hj' hWj ⊢
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hj', List.getElem?_append_left hj]
          simpa only [List.getD_eq_getElem?_getD] using hWj
        · rw [hge j (by omega)]
          by_cases hj2 : j = W.length
          · subst hj2
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hl,
              List.getElem?_append_right (le_refl _), ← hl,
              List.getElem?_append_right (le_refl _)]
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hD' : PEqualNP.MetaComplexity.FanInTwo (PEqualNP.CircuitLowerBounds.Circuit.mk
      (C.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
        PEqualNP.CircuitLowerBounds.Gate.mk g.op
          (g.inputs.map fun i => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i))
      (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] C.output C.output)) := by
    intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    refine ⟨(hfan g0 hg0).1, ?_⟩
    simpa using (hfan g0 hg0).2
  have hDs' : (PEqualNP.CircuitLowerBounds.Circuit.mk
      (C.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
        PEqualNP.CircuitLowerBounds.Gate.mk g.op
          (g.inputs.map fun i => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i))
      (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] C.output C.output)).size ≤ 13 := by
    show (List.map _ C.gates).length ≤ 13
    rw [List.length_map]
    exact hs
  have hrel : ∀ Lx Ly : List Bool, Lx.length = 11 → Ly.length = 11 →
      (∀ j : ℕ, Ly.getD (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j) false = Lx.getD j false) →
      (PEqualNP.CircuitLowerBounds.Circuit.mk
        (C.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
          PEqualNP.CircuitLowerBounds.Gate.mk g.op
            (g.inputs.map fun i => List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] i i))
        (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] C.output C.output)).eval Ly = C.eval Lx := by
    intro Lx Ly hx hy hj
    exact hpre C.gates Lx Ly (by rw [hx, hy]) (by rw [hx]; omega) hj C.output
  have htail : ∀ (Lx Ly : List Bool), Lx.length = 11 → Ly.length = 11 → ∀ j : ℕ, 11 ≤ j →
      Ly.getD (List.getD [0, 5, 8, 3, 4, 1, 7, 6, 2] j j) false = Lx.getD j false := by
    intro Lx Ly hx hy j hj
    rw [hge j (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  rcases hcase with c1 | c2 | c3 | ⟨v, hv0, hv4, c4⟩
  · exact h1 C hfan hs c1
  · exact h2 C hfan hs c2
  · apply h2 _ hD' hDs'
    intro y
    rw [hrel (List.ofFn (Function.update (fun i => y (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)) 4 false) ++
        [y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 0) || y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 4),
          y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 4) || y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 5)])
      _ (by simp) (by simp) ?_]
    · rw [c3]
      exact hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8)
    · intro j
      by_cases hj : j < 11
      · interval_cases j <;> rfl
      · exact htail _ _ (by simp) (by simp) j (by omega)
  · fin_cases v
    · exact absurd rfl hv0
    · exact h3 1 (by decide) C hfan hs c4
    · exact h3 2 (by decide) C hfan hs c4
    · exact h3 3 (by decide) C hfan hs c4
    · exact absurd rfl hv4
    · apply h3 1 (by decide) _ hD' hDs'
      intro y
      rw [hrel (List.ofFn (fun i => y (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)) ++
          [false, y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 0) || y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 4) ||
            y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 5)])
        _ (by simp) (by simp) ?_]
      · exact (c4 _).trans (hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))
      · intro j
        by_cases hj : j < 11
        · interval_cases j <;> rfl
        · exact htail _ _ (by simp) (by simp) j (by omega)
    · exact h3 6 (by decide) C hfan hs c4
    · apply h3 6 (by decide) _ hD' hDs'
      intro y
      rw [hrel (List.ofFn (fun i => y (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)) ++
          [false, y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 0) || y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 4) ||
            y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 7)])
        _ (by simp) (by simp) ?_]
      · exact (c4 _).trans (hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))
      · intro j
        by_cases hj : j < 11
        · interval_cases j <;> rfl
        · exact htail _ _ (by simp) (by simp) j (by omega)
    · apply h3 2 (by decide) _ hD' hDs'
      intro y
      rw [hrel (List.ofFn (fun i => y (![0, 5, 8, 3, 4, 1, 7, 6, 2] i)) ++
          [false, y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 0) || y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 4) ||
            y (![0, 5, 8, 3, 4, 1, 7, 6, 2] 8)])
        _ (by simp) (by simp) ?_]
      · exact (c4 _).trans (hF0 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7) (y 8))
      · intro j
        by_cases hj : j < 11
        · interval_cases j <;> rfl
        · exact htail _ _ (by simp) (by simp) j (by omega)
