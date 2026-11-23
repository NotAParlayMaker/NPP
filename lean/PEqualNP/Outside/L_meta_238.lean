import PEqualNP.Defs

open PEqualNP.MetaComplexity

/-- With no gate the output is an input bit or alse, and neither is the exclusive or; one
gate computing the exclusive or of the two inputs suffices. -/
theorem PEqualNP.Outside.L_meta_238 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize 2 (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔ 1 ≤ s := by
  intro s
  constructor
  · rintro ⟨⟨gates, o⟩, hsize, heval⟩
    by_contra hs
    have hg : gates = [] := by
      simp only [BinaryCircuit.size] at hsize
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hg
    have h1 := heval ![true, true]
    have h2 := heval ![true, false]
    have h3 := heval ![false, true]
    simp [BinaryCircuit.eval, BinaryCircuit.wires] at h1 h2 h3
    rcases o with _ | _ | o
    · simp at h1
    · simp at h1
    · simp at h2
  · intro hs
    refine ⟨⟨[⟨xor, 0, 1⟩], 2⟩, hs, ?_⟩
    intro x
    revert x
    decide
