import Mathlib
import PEqualNP.Defs

-- Size cut for L-meta-3927. Put the gates OR(x_0, x_2) and OR(wire 9, x_k) in front of a circuit of
-- the statement: the wire indices do not move, so this is a circuit for the edge function on the
-- nine inputs with two more gates. With at most 12 gates that is a circuit of at most 14 gates,
-- which the checked bound of L-meta-2012 excludes. What is left is the case of exactly 13 gates.
theorem PEqualNP.Outside.R_meta_3927_1
    (hcore : ∀ (x1 : Fin (9 : ℕ)), ↑x1 ∈ [(1 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (8 : ℕ)] → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (13 : ℕ) ≤ x3.size → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))))
    (hsmall : ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x6 : Fin (9 : ℕ) → Bool) => (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)))) (14 : ℕ)) :
    ∀ (x1 : Fin (9 : ℕ)), ↑x1 ∈ [(1 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (8 : ℕ)] → ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x6 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)), x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) || x6 x1]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro x1 hx1 x3 hf hs
  by_cases h : 13 ≤ x3.size
  · exact hcore x1 hx1 x3 hf hs h
  · by_contra hc
    push Not at hc
    apply hsmall
    refine ⟨⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ ::
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, x1.val]⟩ :: x3.gates, x3.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp, by simp⟩
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨by simp, by simp⟩
        · exact hf g hg
    · show x3.gates.length + 1 + 1 ≤ 14
      have h' : ¬ 13 ≤ x3.gates.length := h
      omega
    · intro x
      have hv0 : PEqualNP.CircuitLowerBounds.GateOp.or.eval ([0, 2].map fun i => (List.ofFn x).getD i false) =
          (x 0 || x 2) := by
        show ([0, 2].map fun i => (List.ofFn x).getD i false).any id = (x 0 || x 2)
        simp [List.getD_eq_getElem?_getD]
      have hv1 : PEqualNP.CircuitLowerBounds.GateOp.or.eval ([9, x1.val].map fun i =>
          (List.ofFn x ++ [x 0 || x 2]).getD i false) = (x 0 || x 2 || x x1) := by
        show ([9, x1.val].map fun i => (List.ofFn x ++ [x 0 || x 2]).getD i false).any id = (x 0 || x 2 || x x1)
        have h9 : (List.ofFn x ++ [x 0 || x 2]).getD 9 false = (x 0 || x 2) := by
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
        have hk : (List.ofFn x ++ [x 0 || x 2]).getD x1.val false = x x1 := by
          rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp [x1.isLt]
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, h9, hk, Bool.or_false,
          Bool.or_assoc]
      have key : PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ ::
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, x1.val]⟩ :: x3.gates, x3.output⟩ (List.ofFn x) =
          x3.eval ((List.ofFn x ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([0, 2].map fun i => (List.ofFn x).getD i false)]) ++
            [PEqualNP.CircuitLowerBounds.GateOp.or.eval ([9, x1.val].map fun i =>
              (List.ofFn x ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
                ([0, 2].map fun i => (List.ofFn x).getD i false)]).getD i false)]) := rfl
      rw [key, hv0, hv1, List.append_assoc]
      exact hc x
