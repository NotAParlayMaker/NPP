import Mathlib
import PEqualNP.Defs

abbrev E3089 : (Fin 9 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

abbrev Hyps3089 (x2 : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
  PEqualNP.MetaComplexity.FanInTwo x2 ∧
  x2.size = 14 ∧
  (x2.output ≤ 10 + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ 10 + x2.size) ∧
  (∀ x6 < 10 + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) ∧
  (9 + (List.filter (fun x7 : PEqualNP.CircuitLowerBounds.Gate => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length +
    ∑ x7 ∈ Finset.range (10 + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - 1) ≤ x2.size) ∧
  List.count 9 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) = 1 ∧
  (∀ x9 : Fin 9, ∃ x10 : Fin 9 → Bool, x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ E3089 x10)

abbrev Goal3089 (x2 : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
  ∃ x10 : Fin 9 → Bool, x2.eval (List.ofFn x10 ++ [x10 0 || x10 3]) ≠ E3089 x10

abbrev SmallOr (x2 : PEqualNP.CircuitLowerBounds.Circuit) (g : PEqualNP.CircuitLowerBounds.Gate) : Prop :=
  ∀ a ∈ g.inputs, a ≠ 9 → (∃ l : Fin 9, a = l ∨ ∃ g2 ∈ x2.gates, ∀ b ∈ g2.inputs, ∃ l : Fin 9, b = l)

theorem PEqualNP.Outside.R_meta_3089_1 :
  (∀ x2, Hyps3089 x2 → (∃ g ∈ x2.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 9 ∈ g.inputs) → Goal3089 x2) →
  (∀ x2, Hyps3089 x2 → (∃ g ∈ x2.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 9 ∈ g.inputs ∧ SmallOr x2 g) → Goal3089 x2) →
  (∀ x2, Hyps3089 x2 → (∃ g ∈ x2.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 9 ∈ g.inputs ∧ ¬ SmallOr x2 g) → Goal3089 x2) →
  (∀ x2, Hyps3089 x2 → (∃ g ∈ x2.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ 9 ∈ g.inputs) → Goal3089 x2) →
  ∀ x2, Hyps3089 x2 → Goal3089 x2 := by
  intro andCase orSmallCase orBigCase notCase x2 h
  obtain ⟨hFan, hSize, hBound, hUsed, hCount, hRead1, hDist⟩ := h
  have h : Hyps3089 x2 := ⟨hFan, hSize, hBound, hUsed, hCount, hRead1, hDist⟩
  -- Step 1: foldl does not change wires below the initial length.
  have readLemma : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : Nat),
      i < w.length → (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i hi; simp
    | cons g gs ih =>
      intro w i hi
      simp only [List.foldl_cons]
      rw [ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hi
  -- Step 2: wire 9 is the output or is read by some gate.
  have readerExists : x2.output = 9 ∨ ∃ g ∈ x2.gates, 9 ∈ g.inputs := by
    have hpos : 0 < List.count 9 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) := by omega
    have h9 : 9 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates := by
      by_contra hnin
      have hzero : List.count 9 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) = 0 :=
        List.count_eq_zero.2 hnin
      omega
    rcases List.mem_cons.1 h9 with h | h
    · left; exact h.symm
    · right
      obtain ⟨g, hg, hg9⟩ := List.mem_flatMap.1 h
      exact ⟨g, hg, hg9⟩
  cases readerExists with
  | inl hOut =>
    -- Output is wire 9 itself: evaluate on the edge-pair (1, 2).
    let x10 : Fin 9 → Bool := fun i => decide (i = 1 ∨ i = 2)
    refine ⟨x10, ?_⟩
    have hlen : (List.ofFn x10 ++ [x10 0 || x10 3]).length = 10 := by simp
    have hEval : x2.eval (List.ofFn x10 ++ [x10 0 || x10 3]) = false := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
      rw [hOut, readLemma x2.gates _ 9 (by omega)]
      rw [List.getD_append_right _ _ _ _ (by simp : (List.ofFn x10).length ≤ 9)]
      decide
    have hEdge : E3089 x10 = true := by decide
    rw [hEval, hEdge]
    exact Bool.false_ne_true
  | inr hGate =>
    obtain ⟨g, hg, hg9⟩ := hGate
    obtain ⟨hop, -⟩ := hFan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop1 | hop2 | hop3
    · exact andCase x2 h ⟨g, hg, hop1, hg9⟩
    · by_cases hSmall : SmallOr x2 g
      · exact orSmallCase x2 h ⟨g, hg, hop2, hg9, hSmall⟩
      · exact orBigCase x2 h ⟨g, hg, hop2, hg9, hSmall⟩
    · exact notCase x2 h ⟨g, hg, hop3, hg9⟩
