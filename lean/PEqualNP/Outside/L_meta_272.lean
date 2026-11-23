import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in

theorem PEqualNP.Outside.L_meta_272 :
∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 7 ∧ (∃ A : Finset ℕ, A.card = 5 ∧ (∀ j ∈ A, j < C.size) ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ↔ j ∈ A)) ∧ (∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ 3 ≤ (List.ofFn x).count true)) := by
  rintro C rfl
  refine ⟨by simp [PEqualNP.MetaComplexity.Monotone2],rfl,?_,by decide +kernel⟩
  refine ⟨{0,1,3,4,6},by decide,by decide,?_⟩
  intro j g hg
  by_cases hj : j < 7
  · interval_cases j <;> simp_all <;> subst g <;> simp_all
  · have hn : j ≥ 7 := by omega
    have hh : ([⟨GateOp.and,[0,2]⟩,⟨GateOp.and,[1,3]⟩,⟨GateOp.or,[4,5]⟩,
      ⟨GateOp.and,[0,1]⟩,⟨GateOp.and,[2,3]⟩,⟨GateOp.or,[7,8]⟩,
      ⟨GateOp.and,[6,9]⟩] : List Gate)[j]? = none := List.getElem?_eq_none (by simp;omega)
    simp only [hh] at hg
    contradiction
