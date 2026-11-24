import Mathlib
import PEqualNP.Defs

-- Size cut for L-meta-3584. Put the gate OR(x_0, x_2) in front of a circuit of the statement:
-- the wire indices do not move, so this is a circuit for the edge function on the nine inputs
-- with one more gate. With at most 13 gates that is a circuit of at most 14 gates, which the
-- checked bound of L-meta-2012 (no circuit of at most 14 gates) excludes. What is left is the
-- case of 14 gates and more.
theorem PEqualNP.Outside.R_meta_3584_1
    (hcore : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     (∀ (x4 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = x1 x4) →       (have x5 : List ℕ := List.flatMap (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x5.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x5.inputs) x2.gates;         (∀ x6 < (10 : ℕ) + x2.size, x6 ≠ x2.output → x6 ∈ x5) ∧ (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x2.gates).length + (x5.length - x5.toFinset.card) ≤ (5 : ℕ)) →         (∀ (x6 : Fin (9 : ℕ)) (x7 : Fin (10 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) → x6 ≠ (2 : Fin (9 : ℕ)) → x6.castSucc ≠ x7 → ∀ x11 ∈ x2.gates, x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or → x11.inputs = [↑x6, ↑x7] ∨ x11.inputs = [↑x7, ↑x6] → (2 : ℕ) ≤ (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x6) x2.gates).length) → (14 : ℕ) ≤ x2.size → (15 : ℕ) ≤ x2.size)
    (hsmall : ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) (14 : ℕ)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     (∀ (x4 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = x1 x4) →       (have x5 : List ℕ := List.flatMap (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x5.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x5.inputs) x2.gates;         (∀ x6 < (10 : ℕ) + x2.size, x6 ≠ x2.output → x6 ∈ x5) ∧ (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x2.gates).length + (x5.length - x5.toFinset.card) ≤ (5 : ℕ)) →         (∀ (x6 : Fin (9 : ℕ)) (x7 : Fin (10 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) → x6 ≠ (2 : Fin (9 : ℕ)) → x6.castSucc ≠ x7 → ∀ x11 ∈ x2.gates, x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or → x11.inputs = [↑x6, ↑x7] ∨ x11.inputs = [↑x7, ↑x6] → (2 : ℕ) ≤ (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x6) x2.gates).length) → (15 : ℕ) ≤ x2.size := by
  dsimp only at hcore ⊢
  intro x2 hf he hA hB
  by_cases h : 14 ≤ x2.size
  · exact hcore x2 hf he hA hB h
  · exfalso
    apply hsmall
    refine ⟨⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ :: x2.gates, x2.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact hf g hg
    · show x2.gates.length + 1 ≤ 14
      have h' : ¬ 14 ≤ x2.gates.length := h
      omega
    · intro x
      have hv : PEqualNP.CircuitLowerBounds.GateOp.or.eval ([0, 2].map fun i => (List.ofFn x).getD i false) =
          (x 0 || x 2) := by
        show ([0, 2].map fun i => (List.ofFn x).getD i false).any id = (x 0 || x 2)
        simp [List.getD_eq_getElem?_getD]
      have key : PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ :: x2.gates, x2.output⟩ (List.ofFn x) =
          x2.eval (List.ofFn x ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            ([0, 2].map fun i => (List.ofFn x).getD i false)]) := rfl
      rw [key, hv]
      exact he x
