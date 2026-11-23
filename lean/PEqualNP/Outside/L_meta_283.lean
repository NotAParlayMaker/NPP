import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in

theorem PEqualNP.Outside.L_meta_283 :
∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) → (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 2 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 5), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  refine ⟨⟨by simp [PEqualNP.MetaComplexity.Monotone2],?_⟩,by decide +kernel⟩
  refine ⟨{3,8},by decide,?_⟩
  intro j g hg hop
  by_cases hj : j < 9
  · interval_cases j <;> simp_all <;> subst g <;> simp_all
  · have hh : ([⟨GateOp.or,[0,1]⟩,⟨GateOp.or,[6,2]⟩,⟨GateOp.or,[3,5]⟩,
      ⟨GateOp.and,[7,8]⟩,⟨GateOp.or,[6,3]⟩,⟨GateOp.or,[10,9]⟩,
      ⟨GateOp.or,[2,4]⟩,⟨GateOp.or,[12,9]⟩,⟨GateOp.and,[11,13]⟩] : List Gate)[j]? = none :=
      List.getElem?_eq_none (by simp;omega)
    simp only [hh] at hg
    contradiction
