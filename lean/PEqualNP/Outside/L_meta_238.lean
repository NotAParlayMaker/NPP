import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_238 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize 2 (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔
      1 ≤ s := by
  intro s
  constructor
  · rintro ⟨C, hle, heval⟩
    by_contra hs
    have hs0 : s = 0 := by omega
    have hlen : C.gates.length = 0 := by
      simp [PEqualNP.MetaComplexity.BinaryCircuit.size] at hle
      omega
    have hgates : C.gates = [] := List.eq_nil_of_length_eq_zero hlen
    have hev : ∀ x : Fin 2 → Bool, [x 0, x 1].getD C.output false = xor (x 0) (x 1) := by
      intro x
      have h := heval x
      simpa [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires,
        hgates, List.ofFn_succ] using h
    match ho : C.output with
    | 0 =>
      have h := hev (fun i => if i = 0 then false else true)
      simp [ho] at h
    | 1 =>
      have h := hev (fun i => if i = 0 then true else false)
      simp [ho] at h
    | k + 2 =>
      have h := hev (fun i => if i = 0 then true else false)
      simp [ho] at h
  · intro hs
    refine ⟨⟨[⟨xor, 0, 1⟩], 2⟩, ?_, ?_⟩
    · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hs
    · intro x
      simp [PEqualNP.MetaComplexity.BinaryCircuit.eval, PEqualNP.MetaComplexity.BinaryCircuit.wires,
        List.ofFn_succ]
