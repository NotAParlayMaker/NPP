import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_312 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool), (C.wires x).length = x.length + C.gates.length := by
  rintro ⟨gates, output⟩ x
  change (gates.foldl _ x).length = x.length + gates.length
  induction gates generalizing x with
  | nil => simp
  | cons g gates ih =>
    rw [List.foldl_cons, ih, List.length_append, List.length_cons]
    simp only [List.length_cons, List.length_nil]
    omega
