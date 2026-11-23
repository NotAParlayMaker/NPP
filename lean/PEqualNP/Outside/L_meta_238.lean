import Mathlib
import PEqualNP.Defs

-- One xor gate reading the two inputs suffices. Conversely a circuit of size zero has no
-- gates, so its value is one of the two inputs or false; each of those disagrees with xor
-- on one of the inputs (true, false) and (false, true), which xor sends to true.
theorem PEqualNP.Outside.L_meta_238 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize 2
      (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔ 1 ≤ s := by
  intro s
  constructor
  · rintro ⟨⟨gates, out⟩, hsize, heval⟩
    by_contra hcon
    have hs : s = 0 := by omega
    subst hs
    have hg : gates = [] := List.eq_nil_of_length_eq_zero
      (Nat.le_zero.mp (by simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hsize))
    subst hg
    have h0 := heval (fun i => decide (i = 0))
    have h1 := heval (fun i => decide (i = 1))
    simp [PEqualNP.MetaComplexity.BinaryCircuit.eval,
      PEqualNP.MetaComplexity.BinaryCircuit.wires, List.ofFn_succ] at h0 h1
    match out, h0, h1 with
    | 0, _, h1 => simp at h1
    | 1, h0, _ => simp at h0
    | (_ + 2), h0, _ => simp at h0
  · intro hs
    refine ⟨⟨[⟨xor, 0, 1⟩], 2⟩, ?_, ?_⟩
    · simpa [PEqualNP.MetaComplexity.BinaryCircuit.size] using hs
    · intro x
      simp [PEqualNP.MetaComplexity.BinaryCircuit.eval,
        PEqualNP.MetaComplexity.BinaryCircuit.wires, List.ofFn_succ]
