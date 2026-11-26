import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17962

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
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
      PEqualNP.TopForm.IsAO2 x1 x2 →
      (∀ x6 ∈ x2.gates, x6.inputs.Nodup) →
      x3 ≠ x4 →
      x3 < x1 + x2.size →
      x4 < x1 + x2.size →
      have x10 : PEqualNP.CircuitLowerBounds.Circuit :=
        { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate }],
          output := x1 + x2.size : PEqualNP.CircuitLowerBounds.Circuit };
      PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧
        ∀ (x11 : Fin x1 → Bool), ∀ x12 < x1 + x2.size,
          PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12 := by
  intro x1 x2 x3 x4 hAO hNodup hne hx3 hx4
  obtain ⟨hOp, hBack, hLen⟩ := hAO
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hOp g hg
    · left; rfl
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
    · have hget : PEqualNP.MetaComplexity.NestedCover.gateAt
          { gates := x2.gates ++ [{ op := GateOp.and, inputs := [x3, x4] }], output := x1 + x2.size } j =
          PEqualNP.MetaComplexity.NestedCover.gateAt x2 j := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hBack j hlt i hi
    · have hget : PEqualNP.MetaComplexity.NestedCover.gateAt
          { gates := x2.gates ++ [{ op := GateOp.and, inputs := [x3, x4] }], output := x1 + x2.size } x2.gates.length =
          { op := GateOp.and, inputs := [x3, x4] } := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [hget] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · simpa [Circuit.size] using hx3
      · simpa [Circuit.size] using hx4
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hLen g hg
    · rfl
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hNodup g hg
    · simp [hne]
  · intro x11 x12 hx12
    simp only [PEqualNP.BlindGate.wireValue, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (x2.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x11)).length =
        x1 + x2.size := by
      rw [wires_length, List.length_ofFn, Circuit.size]
    exact List.getD_append _ _ _ _ (by omega)

end PEqualNP.Outside.L_meta_17962

theorem PEqualNP.Outside.L_meta_17962 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x2.gates, x6.inputs.Nodup) →       x3 ≠ x4 →         x3 < x1 + x2.size →           x4 < x1 + x2.size →             have x10 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate }], output := x1 + x2.size : PEqualNP.CircuitLowerBounds.Circuit };             PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), ∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12) := by
  exact PEqualNP.Outside.L_meta_17962.main
