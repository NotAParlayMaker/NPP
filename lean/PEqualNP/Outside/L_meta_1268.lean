import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1268

-- The six input bits spelled out; a finite check over 64 cases.
theorem aux : ∀ a b c d e f : Bool, ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit).eval ([a, b, c] ++ [d, e, f]) = decide (∃ (p : Fin 3) (w : Fin 3), (fun (p : Fin 3) (w : Fin 3) => decide ((p.val, w.val) ∈ ([(0, 0), (1, 0), (1, 1), (2, 1), (2, 2), (0, 2)] : List (ℕ × ℕ)))) p w = true ∧ ![a, b, c] p = true ∧ ![d, e, f] w = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1268

theorem PEqualNP.Outside.L_meta_1268 : ∀ (x : Fin 3 → Bool) (y : Fin 3 → Bool), ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x ++ List.ofFn y) = decide (∃ (p : Fin 3) (w : Fin 3), (fun (p : Fin 3) (w : Fin 3) => decide ((p.val, w.val) ∈ ([(0, 0), (1, 0), (1, 1), (2, 1), (2, 2), (0, 2)] : List (ℕ × ℕ)))) p w = true ∧ x p = true ∧ y w = true) := by
  intro x y
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, x = ![a, b, c] :=
    ⟨x 0, x 1, x 2, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨d, e, f, rfl⟩ : ∃ d e f, y = ![d, e, f] :=
    ⟨y 0, y 1, y 2, by funext i; fin_cases i <;> rfl⟩
  exact PEqualNP.Outside.L_meta_1268.aux a b c d e f
