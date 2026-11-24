import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4135_2
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 →
      (∀ g ∈ x1.gates, (10 : ℕ) ∉ g.inputs) → x1.output ≠ 10 →
      ∀ (x5 : Fin (10 : ℕ) → Bool) (x6 : Bool),
        x1.eval (List.ofFn x5 ++ [x6]) = x1.eval (List.ofFn x5 ++ [Bool.false]))
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (18 : ℕ) → (∃ g ∈ x1.gates, (10 : ℕ) ∈ g.inputs) →
      (∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool),
        x1.eval (List.ofFn x4 ++ [Bool.false]) ≠ x1.eval (List.ofFn x5 ++ [Bool.false])) →
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧
        x5.size ≤ (17 : ℕ) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool),
          x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6 ++ [Bool.false])) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x4 : Fin (10 : ℕ) → Bool) (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [Bool.false]) ≠ x1.eval (List.ofFn x5 ++ [Bool.false])) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size ≤ (17 : ℕ) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool), x5.eval (List.ofFn x6) = x1.eval (List.ofFn x6 ++ [Bool.false])) ∨ ∀ (x5 : Fin (10 : ℕ) → Bool) (x6 : Bool), x1.eval (List.ofFn x5 ++ [x6]) = x1.eval (List.ofFn x5 ++ [Bool.false]) := by
  intro x1 hf hs hnonconst
  -- Appending gates never changes wire 10 of the input list.
  have getD10 : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), 10 < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD 10 false
        = w.getD 10 false := by
    intro gs
    induction gs with
    | nil => intro w _; rfl
    | cons g gs ih =>
      intro w hw
      rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]
  by_cases hread : ∃ g ∈ x1.gates, (10 : ℕ) ∈ g.inputs
  · exact Or.inl (h2 x1 hf hs hread hnonconst)
  · have hout : x1.output ≠ 10 := by
      intro h
      obtain ⟨x4, x5, hne⟩ := hnonconst
      have e4 : x1.eval (List.ofFn x4 ++ [Bool.false]) = false := by
        show (x1.wires (List.ofFn x4 ++ [Bool.false])).getD x1.output false = false
        rw [h]
        show (x1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x4 ++ [Bool.false])).getD 10 false = false
        rw [getD10 x1.gates _ (by simp)]
        simp
      have e5 : x1.eval (List.ofFn x5 ++ [Bool.false]) = false := by
        show (x1.wires (List.ofFn x5 ++ [Bool.false])).getD x1.output false = false
        rw [h]
        show (x1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x5 ++ [Bool.false])).getD 10 false = false
        rw [getD10 x1.gates _ (by simp)]
        simp
      exact hne (by rw [e4, e5])
    exact Or.inr (h1 x1 hf (fun g hg hmem => hread ⟨g, hg, hmem⟩) hout)
