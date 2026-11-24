import Mathlib
import PEqualNP.Defs

-- Cut by the graph automorphism fixing 0, 3, 4 and swapping 1 with 5, 2 with 8, 6 with 7.
-- It carries the third case onto the second, and the seventh-wire cases 5, 8, 7 of the
-- fourth onto 1, 2, 6. The three hypotheses are the first case, the second case, and the
-- fourth case restricted to the wires 1, 2, 3, 6.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2836_7
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ 13 → (∀ (x5 : Fin 9 → Bool), x1.eval (List.ofFn (Function.update x5 0 false) ++ [x5 0 || x5 4, x5 0 || x5 3]) = (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5)) → False)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ 13 → (∀ (x5 : Fin 9 → Bool), x1.eval (List.ofFn (Function.update x5 4 false) ++ [x5 0 || x5 4, x5 4 || x5 1]) = (x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 || x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 5 && x5 7 || x5 6 && x5 8 || x5 8 && x5 5)) → False)
    (h4 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ 13 → ∀ (x5 : Fin 9), x5 ∈ ([1, 2, 3, 6] : List (Fin 9)) → (∀ (x6 : Fin 9 → Bool), x1.eval (List.ofFn x6 ++ [false, x6 0 || x6 4 || x6 x5]) = (x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 || x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 5 && x6 7 || x6 6 && x6 8 || x6 8 && x6 5)) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : (Fin (9 : ℕ) → Bool) → Bool := fun (x2 : Fin (9 : ℕ) → Bool) => x2 (0 : Fin (9 : ℕ)) && x2 (1 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (2 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (3 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (4 : Fin (9 : ℕ)) || x2 (4 : Fin (9 : ℕ)) && x2 (0 : Fin (9 : ℕ)) || x2 (0 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ)) || x2 (1 : Fin (9 : ℕ)) && x2 (6 : Fin (9 : ℕ)) || x2 (2 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (5 : Fin (9 : ℕ)) && x2 (7 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ)) && x2 (8 : Fin (9 : ℕ)) || x2 (8 : Fin (9 : ℕ)) && x2 (5 : Fin (9 : ℕ));   PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ((∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x2 x5) ∨ (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ))]) = x2 x5) ∨ ∃ (x5 : Fin (9 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) ∧ x5 ≠ (4 : Fin (9 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x6 ++ [Bool.false, x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) || x6 x5]) = x2 x6) → False := by
  intro C x2 fan hsize hc
  let σ : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  let wm : ℕ → ℕ := fun w => if h : w < 9 then (σ ⟨w, h⟩ : ℕ) else w
  let rg : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun g => ⟨g.op, g.inputs.map wm⟩
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map rg, wm C.output⟩
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wm_ge : ∀ i, 9 ≤ i → wm i = i := by
    intro i hi
    simp [wm, Nat.not_lt.mpr hi]
  have wm_lt : ∀ i, i < 9 → wm i < 9 := by
    intro i hi
    simp only [wm, dite_eq_left hi]
    exact (σ ⟨i, hi⟩).isLt
  have rel : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u v : List Bool), 9 ≤ u.length →
      u.length = v.length → (∀ i, u.getD (wm i) false = v.getD i false) →
      ∀ i, ((gs.map rg).foldl step u).getD (wm i) false = (gs.foldl step v).getD i false := by
    intro gs
    induction gs with
    | nil => intro u v _ _ h i; exact h i
    | cons g gs ih =>
      intro u v h9 hl h
      have vals : (g.inputs.map wm).map (fun i => u.getD i false)
          = g.inputs.map (fun i => v.getD i false) := by
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => h i)
      have newEq : step u (rg g) = u ++ [g.op.eval (g.inputs.map fun i => v.getD i false)] := by
        change u ++ [g.op.eval ((g.inputs.map wm).map fun i => u.getD i false)] = _
        rw [vals]
      have h' : ∀ i, (u ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]).getD (wm i) false
          = (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]).getD i false := by
        intro i
        rcases Nat.lt_trichotomy i u.length with hi | hi | hi
        · have hwm : wm i < u.length := by
            by_cases h9' : i < 9
            · exact lt_of_lt_of_le (wm_lt i h9') h9
            · rw [wm_ge i (by omega)]
              exact hi
          rw [List.getD_append _ _ _ _ hwm, List.getD_append _ _ _ _ (hl ▸ hi)]
          exact h i
        · rw [wm_ge i (by omega), hi]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right le_rfl, List.getElem?_append_right (le_of_eq hl.symm)]
          simp [hl]
        · rw [wm_ge i (by omega), List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
      intro i
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, newEq]
      exact ih _ _ (by simp; omega) (by simp; omega) h' i
  have evalC' : ∀ (u v : List Bool), 9 ≤ u.length → u.length = v.length →
      (∀ i, u.getD (wm i) false = v.getD i false) → C'.eval u = C.eval v := by
    intro u v h9 hl h
    exact rel C.gates u v h9 hl h C.output
  have fan' : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    refine ⟨(fan g0 hg0).1, ?_⟩
    change (g0.inputs.map wm).length ≤ 2
    rw [List.length_map]
    exact (fan g0 hg0).2
  have size' : C'.size ≤ 13 := by
    change (C.gates.map rg).length ≤ 13
    rw [List.length_map]
    exact hsize
  have perm_list : ∀ (g : Fin 9 → Bool) (a b : Bool) (i : ℕ),
      (List.ofFn g ++ [a, b]).getD (wm i) false = (List.ofFn (g ∘ σ) ++ [a, b]).getD i false := by
    intro g a b i
    by_cases hi : i < 11
    · interval_cases i <;> rfl
    · rw [wm_ge i (by omega), List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  have transfer : ∀ (g : Fin 9 → Bool) (a b : Bool),
      C'.eval (List.ofFn g ++ [a, b]) = C.eval (List.ofFn (g ∘ σ) ++ [a, b]) := by
    intro g a b
    exact evalC' _ _ (by simp) (by simp) (perm_list g a b)
  have upd : ∀ g : Fin 9 → Bool,
      (Function.update g 4 false) ∘ σ = Function.update (g ∘ σ) 4 false := by
    intro g
    funext i
    have hσ : ∀ i : Fin 9, σ i = 4 ↔ i = 4 := by decide
    by_cases h : i = 4
    · subst h
      simp [σ]
    · have : σ i ≠ 4 := fun e => h ((hσ i).1 e)
      simp [h, this]
  have fσ : ∀ y : Fin 9 → Bool, ((y ∘ σ) 0 && (y ∘ σ) 1 || (y ∘ σ) 1 && (y ∘ σ) 2 || (y ∘ σ) 2 && (y ∘ σ) 3 || (y ∘ σ) 3 && (y ∘ σ) 4 || (y ∘ σ) 4 && (y ∘ σ) 0 || (y ∘ σ) 0 && (y ∘ σ) 5 || (y ∘ σ) 1 && (y ∘ σ) 6 || (y ∘ σ) 2 && (y ∘ σ) 7 || (y ∘ σ) 3 && (y ∘ σ) 8 || (y ∘ σ) 5 && (y ∘ σ) 7 || (y ∘ σ) 6 && (y ∘ σ) 8 || (y ∘ σ) 8 && (y ∘ σ) 5) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5) := by
    decide +kernel
  rcases hc with hc1 | hc2 | hc3 | hc4
  · exact h1 C fan hsize hc1
  · exact h2 C fan hsize hc2
  · apply h2 C' fan' size'
    intro y
    rw [transfer, upd y]
    exact (hc3 (y ∘ σ)).trans (fσ y)
  · obtain ⟨k, hk0, hk4, hk⟩ := hc4
    have direct : k ∈ ([1, 2, 3, 6] : List (Fin 9)) → False := fun hm => h4 C fan hsize k hm hk
    have viaσ : σ k ∈ ([1, 2, 3, 6] : List (Fin 9)) → False := by
      intro hm
      apply h4 C' fan' size' (σ k) hm
      intro y
      rw [transfer]
      exact (hk (y ∘ σ)).trans (fσ y)
    fin_cases k
    · exact absurd rfl hk0
    · exact direct (by decide)
    · exact direct (by decide)
    · exact direct (by decide)
    · exact absurd rfl hk4
    · exact viaσ (by decide)
    · exact direct (by decide)
    · exact viaσ (by decide)
    · exact viaσ (by decide)
