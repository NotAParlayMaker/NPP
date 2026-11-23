import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_238 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize 2 (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔ 1 ≤ s := by
  intro s
  constructor
  · rintro ⟨C, hsize, heval⟩
    by_contra hs
    have hzero : C.size = 0 := by omega
    have hgs : C.gates = [] := by
      cases hg : C.gates with
      | nil => rfl
      | cons g gs => simp [PEqualNP.MetaComplexity.BinaryCircuit.size, hg] at hzero
    cases hout : C.output with
    | zero =>
        have e := heval (fun i : Fin 2 => i = 1)
        simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, hgs, hout] at e
    | succ i =>
        cases i with
        | zero =>
            have e := heval (fun i : Fin 2 => i = 0)
            simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, hgs, hout] at e
        | succ i =>
            have e := heval (fun i : Fin 2 => i = 0)
            simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires, hgs, hout] at e
  · intro hs
    refine ⟨⟨[⟨xor, 0, 1⟩], 2⟩, ?_, ?_⟩
    · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hs
    · intro x
      simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires]
