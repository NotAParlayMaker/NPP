import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.L_meta_1742 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 28] }], output := 32 } : PEqualNP.CircuitLowerBounds.Circuit) →
  let B2 : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 4), (3, 5), (3, 6),
    (4, 3), (4, 5), (4, 6), (5, 3), (5, 4), (5, 6), (6, 3), (6, 4), (6, 5)];
  (∀ m : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun p : Fin 7 => ((p : ℕ), (m : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p p' : Fin 7, p ≠ p' → ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2 ∧ ((p' : ℕ), (l : ℕ)) ∈ B2)).card ≠ 1) ∧
  C.gates.length = 19 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (7 + 7) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (x y : Fin 7 → Bool), C.eval (List.ofFn x ++ List.ofFn y)
     = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ B2 ∧ x p = true ∧ y l = true) := by
  intro C h
  subst C
  dsimp only
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, rfl, by decide +kernel, by simp, ?_⟩
  intro x y
  simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ, Fin.exists_fin_succ]
  simp only [Bool.and_or_distrib_left, Bool.and_or_distrib_right]
  ac_rfl
