import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_240 : ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => true) s ↔ 1 ≤ s := by
  intro n s
  constructor
  · rintro ⟨C, hs, h⟩
    by_contra hlt
    have h0 : C.gates = [] := by
      have : C.gates.length = 0 := by
        have := hs
        simp only [PEqualNP.MetaComplexity.BinaryCircuit.size] at this
        omega
      exact List.length_eq_zero_iff.mp this
    have := h (fun _ => false)
    simp only [PEqualNP.MetaComplexity.BinaryCircuit.eval,
      PEqualNP.MetaComplexity.BinaryCircuit.wires, h0, List.foldl_nil,
      List.getD_eq_getElem?_getD] at this
    by_cases hi : C.output < n
    · simp [hi] at this
    · simp [hi] at this
  · intro hs
    refine ⟨⟨[⟨fun _ _ => true, 0, 0⟩], n⟩, by simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hs, fun x => ?_⟩
    simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires,
      List.getD_eq_getElem?_getD]
