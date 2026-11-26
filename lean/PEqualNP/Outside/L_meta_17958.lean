import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17958

open PEqualNP.CircuitLowerBounds

theorem wires_length (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

theorem main :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →
      (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →
      x2 ≠ x3 →
      x2 < (26 : ℕ) + x1.size →
      x3 < (26 : ℕ) + x1.size →
      ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ),
        x9.size ≤ x1.size + (1 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x9 ∧
        (∀ x11 ∈ x9.gates, x11.inputs.Nodup) ∧
        x9.output = (26 : ℕ) + x10 ∧
        x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧
        ∀ (x11 : Fin (26 : ℕ) → Bool), ∀ x12 < (26 : ℕ) + x1.size,
          PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x11 x12 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 x12 := by
  intro x1 x2 x3 hAO hNodup hne hx2 hx3
  obtain ⟨hOp, hBack, hLen⟩ := hAO
  let gNew : Gate := { op := GateOp.and, inputs := [x2, x3] }
  let cNew : Circuit := { gates := x1.gates ++ [gNew], output := 26 + x1.size }
  refine ⟨cNew, x1.size, ?_, ⟨?_, ?_, ?_⟩, ?_, rfl, ?_, ?_⟩
  · simp [cNew, Circuit.size]
  · intro g hg
    simp only [cNew, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hOp g hg
    · left; rfl
  · intro j hj i hi
    simp only [cNew, List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
    · have hget : PEqualNP.MetaComplexity.NestedCover.gateAt cNew j =
          PEqualNP.MetaComplexity.NestedCover.gateAt x1 j := by
        simp [cNew, PEqualNP.MetaComplexity.NestedCover.gateAt, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hBack j hlt i hi
    · have hget : PEqualNP.MetaComplexity.NestedCover.gateAt cNew x1.gates.length = gNew := by
        simp [cNew, PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [hget] at hi
      simp only [gNew, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [Circuit.size] using hx2
      · simpa [Circuit.size] using hx3
  · intro g hg
    simp only [cNew, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hLen g hg
    · rfl
  · intro g hg
    simp only [cNew, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hNodup g hg
    · simp [gNew, hne]
  · simp [cNew, gNew, Circuit.size]
  · intro x11 x12 hx12
    simp only [cNew, PEqualNP.BlindGate.wireValue, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (x1.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x11)).length =
        26 + x1.size := by
      rw [wires_length, List.length_ofFn, Circuit.size]
    exact List.getD_append _ _ _ _ (by omega)

end PEqualNP.Outside.L_meta_17958

theorem PEqualNP.Outside.L_meta_17958 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ x5 ∈ x1.gates, x5.inputs.Nodup) → x2 ≠ x3 → x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x9.size ≤ x1.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x9 ∧ (∀ x11 ∈ x9.gates, x11.inputs.Nodup) ∧ x9.output = (26 : ℕ) + x10 ∧ x9.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), ∀ x12 < (26 : ℕ) + x1.size, PEqualNP.BlindGate.wireValue x9 (26 : ℕ) x11 x12 = PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x11 x12) := by
  exact PEqualNP.Outside.L_meta_17958.main
