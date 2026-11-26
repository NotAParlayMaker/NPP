import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_17958_aux

private def extended (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.and, [a,b]⟩], n + C.size⟩

private theorem foldLength (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem extend_ok {n : ℕ} {C : Circuit} {a b : ℕ}
    (hC : IsAO2 n C) (huniq : ∀ g ∈ C.gates, g.inputs.Nodup) (hab : a ≠ b)
    (ha : a < n + C.size) (hb : b < n + C.size) :
    IsAO2 n (extended n C a b) ∧ (∀ g ∈ (extended n C a b).gates, g.inputs.Nodup) ∧
    ∀ x : Fin n → Bool, ∀ i < n + C.size,
      wireValue (extended n C a b) n x i = wireValue C n x i := by
  have parts (g : Gate) (hg : g ∈ (extended n C a b).gates) :
      g ∈ C.gates ∨ g = ⟨.and, [a,b]⟩ := by simpa [extended] using hg
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    rcases parts g hg with h | rfl
    · exact hC.1 g h
    · exact Or.inl rfl
  · intro j hj i hi
    by_cases hj' : j < C.gates.length
    · apply hC.2.1 j hj' i
      simpa [gateAt, extended, List.getD_eq_getElem?_getD, List.getElem?_append_left hj'] using hi
    · have he : j = C.gates.length := by
        simp [extended] at hj
        omega
      subst j
      simp [gateAt, extended, List.getD_eq_getElem?_getD] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    rcases parts g hg with h | rfl
    · exact hC.2.2 g h
    · rfl
  · intro g hg
    rcases parts g hg with h | rfl
    · exact huniq g h
    · simpa using hab
  · intro x i hi
    have len : (C.wires (List.ofFn x)).length = n + C.size := by
      unfold Circuit.wires Circuit.size
      rw [foldLength, List.length_ofFn]
    unfold PEqualNP.BlindGate.wireValue
    simp only [extended, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    apply List.getD_append
    change i < (C.wires (List.ofFn x)).length
    rwa [len]

end PEqualNP.Outside.L_meta_17958_aux

theorem PEqualNP.Outside.L_meta_17958 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) → x2 ≠ x3 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x9.size ≤ x1.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x9 ∧ (∀ x11 ∈ x9.gates, x11.inputs.Nodup) ∧ x9.output = (26 : ℕ) + x10 ∧ x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), ∀ x12 < (26 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x11 x12 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 x12 := by
  intro C a b hC hu hab ha hb
  let C' := PEqualNP.Outside.L_meta_17958_aux.extended 26 C a b
  obtain ⟨hA, hU, hW⟩ := PEqualNP.Outside.L_meta_17958_aux.extend_ok hC hu hab ha hb
  refine ⟨C', C.size, ?_, hA, hU, rfl, ?_, hW⟩
  · simp [C', PEqualNP.Outside.L_meta_17958_aux.extended, Circuit.size]
  · simp [C', PEqualNP.Outside.L_meta_17958_aux.extended, Circuit.size, List.getElem?_append_right]
