import Mathlib.Tactic.Tauto
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1186 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩,
      ⟨.or, [8, 3]⟩,
      ⟨.and, [0, 9]⟩,
      ⟨.and, [1, 2]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.and, [3, 12]⟩,
      ⟨.and, [6, 7]⟩,
      ⟨.or, [10, 11]⟩,
      ⟨.or, [15, 13]⟩,
      ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · intro x
    simp [C, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.ofFn_succ]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true_iff, Bool.or_eq_true_iff]
    tauto
