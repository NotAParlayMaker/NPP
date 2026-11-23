import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_241 : ∀ n s : ℕ,
    PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => false) s := by
  intro n s
  refine ⟨⟨[], n⟩, Nat.zero_le s, ?_⟩
  intro x
  have hx : (List.ofFn x).length = n := List.length_ofFn
  simp only [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires,
    List.foldl_nil]
  rw [List.getD_eq_default]
  omega
