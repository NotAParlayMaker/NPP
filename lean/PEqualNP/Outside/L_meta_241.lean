import Mathlib
import PEqualNP.Defs

-- The empty circuit with output wire n. It has no gates, so its wires are just the input,
-- of length n, and reading wire n falls outside that list and yields false.
theorem PEqualNP.Outside.L_meta_241 :
    ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n
      (fun _ : Fin n → Bool => false) s := by
  intro n s
  refine ⟨⟨[], n⟩, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.BinaryCircuit.size]
  · intro x
    simp [PEqualNP.MetaComplexity.BinaryCircuit.eval,
      PEqualNP.MetaComplexity.BinaryCircuit.wires]
