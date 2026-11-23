import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_241 :
    ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => false) s := by
  intro n s
  refine ⟨⟨[], n⟩, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.BinaryCircuit.size]
  · intro x
    simp only [PEqualNP.MetaComplexity.BinaryCircuit.eval,
      PEqualNP.MetaComplexity.BinaryCircuit.wires, List.foldl_nil]
    exact List.getD_eq_default _ _ (le_of_eq (List.length_ofFn (f := x)))
