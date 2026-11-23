import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_meta_776 :
    ∀ C : Circuit,
      C = ({ gates := [⟨GateOp.and, [0,1]⟩, ⟨GateOp.or, [2,5]⟩,
                       ⟨GateOp.or, [0,3]⟩, ⟨GateOp.and, [4,7]⟩,
                       ⟨GateOp.or, [1,3]⟩, ⟨GateOp.and, [6,9]⟩,
                       ⟨GateOp.or, [8,10]⟩], output := 11 } : Circuit) →
      FanInTwo C ∧ C.size = 7 ∧
      (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 5, (u.val,v.val) ∈
          ([(0,1),(0,4),(1,2),(2,3),(3,4)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · simp [FanInTwo]
  · decide
