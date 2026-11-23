import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1193

lemma ev (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin 8 → Bool) → Bool)
    (g : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool)
    (hf : ∀ x : Fin 8 → Bool, f x = g (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7))
    (h : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
      C.eval [a0, a1, a2, a3, a4, a5, a6, a7] = g a0 a1 a2 a3 a4 a5 a6 a7) :
    ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    first
      | rfl
      | simp [List.ofFn_succ]
  rw [hx, hf]
  exact h _ _ _ _ _ _ _ _

end PEqualNP.Outside.L_meta_1193

theorem PEqualNP.Outside.L_meta_1193 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 7)) x := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · refine PEqualNP.Outside.L_meta_1193.ev _ _ (fun a0 a1 a2 a3 a4 a5 a6 a7 => (a0 && a1) || (a0 && a2) || (a0 && a3) || (a1 && a4) || (a1 && a5) || (a2 && a6) || (a4 && a7)) (fun _ => rfl) ?_
    decide +kernel
