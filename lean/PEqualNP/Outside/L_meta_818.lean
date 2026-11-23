import PEqualNP.Defs
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_818_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def certifiedCircuit : Circuit :=
  ⟨[⟨.or, [1, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [10, 7]⟩,
    ⟨.and, [2, 11]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [3, 13]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [9, 12]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩

private def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 5), (1, 2), (2, 3), (2, 7), (3, 4), (3, 6), (4, 5)]

private def input (a b c d e f g h : Bool) (i : Fin 8) : Bool :=
  [a, b, c, d, e, f, g, h].get ⟨i.val, i.isLt⟩

set_option maxHeartbeats 0 in
private theorem evaluate_inputs (a b c d e f g h : Bool) :
    certifiedCircuit.eval (List.ofFn (input a b c d e f g h)) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ edges ∧
        input a b c d e f g h u = true ∧ input a b c d e f g h v = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    cases g <;> cases h <;> decide

theorem certify : FanInTwo certifiedCircuit ∧ certifiedCircuit.size = 11 ∧
    ∀ x : Fin 8 → Bool, certifiedCircuit.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  refine ⟨?_, by decide, ?_⟩
  · intro g hg
    simp only [certifiedCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : input (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) = x := by
      funext i
      fin_cases i <;> rfl
    simpa only [hx] using evaluate_inputs (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

end PEqualNP.Outside.L_meta_818_aux

theorem PEqualNP.Outside.L_meta_818 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 15]⟩], output := 18 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 11 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (2, 3), (2, 7), (3, 4), (3, 6), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst C
  exact PEqualNP.Outside.L_meta_818_aux.certify
