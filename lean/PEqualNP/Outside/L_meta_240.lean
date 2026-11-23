import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_240 :
    ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => true) s ↔ 1 ≤ s := by
  intro n s
  constructor
  · rintro ⟨C, hle, hfun⟩
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · have hsz : C.size = 0 := Nat.le_zero.mp hle
      have hnil : C.gates = [] := by
        simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hsz
      have hfalse : C.eval (List.ofFn (fun _ : Fin n => false)) = false := by
        simp [PEqualNP.MetaComplexity.BinaryCircuit.eval,
          PEqualNP.MetaComplexity.BinaryCircuit.wires, hnil]
      have htrue := hfun (fun _ : Fin n => false)
      rw [hfalse] at htrue
      simp at htrue
    · exact hs
  · intro hs
    refine ⟨⟨[⟨fun _ _ => true, 0, 0⟩], n⟩, ?_, ?_⟩
    · simp [PEqualNP.MetaComplexity.BinaryCircuit.size]
      omega
    · intro x
      simp [PEqualNP.MetaComplexity.BinaryCircuit.eval,
        PEqualNP.MetaComplexity.BinaryCircuit.wires]
