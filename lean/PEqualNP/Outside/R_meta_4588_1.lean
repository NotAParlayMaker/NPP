import Mathlib
import PEqualNP.Defs

-- Size cut for L-meta-4588. Put the gates OR(x_0, x_4) and OR(x_2, x_3) in front of a circuit of
-- the statement: the wire indices do not move, so this is a circuit for the edge function on the
-- nine inputs with two more gates. With at most 12 gates that is a circuit of at most 14 gates,
-- which the checked bound of L-meta-2012 (no circuit of at most 14 gates) excludes. What is left
-- is the case of exactly 13 gates.
theorem PEqualNP.Outside.R_meta_4588_1
    (hcore : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → (13 : ℕ) ≤ x1.size → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), x4 (2 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ))]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → False)
    (hsmall : ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) (14 : ℕ)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)), x4 (2 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ))]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → False := by
  intro x1 hf hs he
  by_cases h : 13 ≤ x1.size
  · exact hcore x1 hf hs h he
  · apply hsmall
    refine ⟨⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ::
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩ :: x1.gates, x1.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp, by simp⟩
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨by simp, by simp⟩
        · exact hf g hg
    · show x1.gates.length + 1 + 1 ≤ 14
      have h' : ¬ 13 ≤ x1.gates.length := h
      omega
    · intro x
      have hv0 : PEqualNP.CircuitLowerBounds.GateOp.or.eval ([0, 4].map fun i => (List.ofFn x).getD i false) =
          (x 0 || x 4) := by
        show ([0, 4].map fun i => (List.ofFn x).getD i false).any id = (x 0 || x 4)
        simp [List.getD_eq_getElem?_getD]
      have hv1 : PEqualNP.CircuitLowerBounds.GateOp.or.eval ([2, 3].map fun i =>
          (List.ofFn x ++ [x 0 || x 4]).getD i false) = (x 2 || x 3) := by
        show ([2, 3].map fun i => (List.ofFn x ++ [x 0 || x 4]).getD i false).any id = (x 2 || x 3)
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left]
      have key : PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ::
            ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩ :: x1.gates, x1.output⟩ (List.ofFn x) =
          x1.eval ((List.ofFn x ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([0, 4].map fun i => (List.ofFn x).getD i false)]) ++
            [PEqualNP.CircuitLowerBounds.GateOp.or.eval ([2, 3].map fun i =>
              (List.ofFn x ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
                ([0, 4].map fun i => (List.ofFn x).getD i false)]).getD i false)]) := rfl
      rw [key, hv0, hv1, List.append_assoc]
      exact he x
