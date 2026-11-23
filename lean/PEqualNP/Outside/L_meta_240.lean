import Mathlib
import PEqualNP.Defs

-- One gate suffices: a gate ignoring both its wires and returning true, read as the output.
-- Conversely a circuit of size zero has no gates, so its wires are just the inputs; on the
-- all-false input every wire is false, so it cannot return true.
theorem PEqualNP.Outside.L_meta_240 :
    ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n
      (fun _ : Fin n → Bool => true) s ↔ 1 ≤ s := by
  intro n s
  constructor
  · rintro ⟨C, hsize, heval⟩
    by_contra hcon
    have hs : s = 0 := by omega
    subst hs
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero
      (Nat.le_zero.mp (by simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hsize))
    have h := heval (fun _ => false)
    rw [PEqualNP.MetaComplexity.BinaryCircuit.eval,
      PEqualNP.MetaComplexity.BinaryCircuit.wires, hg] at h
    simp [List.ofFn_const, List.getD] at h
  · intro hs
    refine ⟨⟨[⟨fun _ _ => true, 0, 0⟩], n⟩, ?_, ?_⟩
    · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hs
    · intro x
      simp [PEqualNP.MetaComplexity.BinaryCircuit.eval,
        PEqualNP.MetaComplexity.BinaryCircuit.wires]
