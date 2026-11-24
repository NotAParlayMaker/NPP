import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3168_1
    (h_input : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      have x2 : ℕ → List PEqualNP.CircuitLowerBounds.Gate := fun (x2 : ℕ) => List.filter (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x2 ∈ x3.inputs)) x1.gates;
      PEqualNP.MetaComplexity.FanInTwo x1 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 →
      (∀ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length = (1 : ℕ)) ∧ (x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length = (2 : ℕ) ∧ x5.inputs.Nodup)) →
      x1.size = (14 : ℕ) →
      (∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x2 (9 : ℕ) = [x7] ∧ (∀ i ∈ x7.inputs, i ≠ 9 → i < 9)) →
      (∀ x8 ∈ [(0 : ℕ), (2 : ℕ)], (x2 x8).length = (1 : ℕ)) →
      (∀ x9 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], (x2 x9).length ≤ (2 : ℕ)) →
      (∀ (x10 : Fin (9 : ℕ)), (x2 ↑x10).length ≤ (3 : ℕ)) →
      (∀ x11 ∈ x1.gates, ¬((0 : ℕ) ∈ x11.inputs ∧ (2 : ℕ) ∈ x11.inputs) ∧ ((9 : ℕ) ∈ x11.inputs → (0 : ℕ) ∉ x11.inputs ∧ (2 : ℕ) ∉ x11.inputs)) →
      ¬∀ (x12 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) =
        (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ))))
    (h_gate : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      have x2 : ℕ → List PEqualNP.CircuitLowerBounds.Gate := fun (x2 : ℕ) => List.filter (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x2 ∈ x3.inputs)) x1.gates;
      PEqualNP.MetaComplexity.FanInTwo x1 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 →
      (∀ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length = (1 : ℕ)) ∧ (x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length = (2 : ℕ) ∧ x5.inputs.Nodup)) →
      x1.size = (14 : ℕ) →
      (∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x2 (9 : ℕ) = [x7] ∧ (∃ i ∈ x7.inputs, 10 ≤ i)) →
      (∀ x8 ∈ [(0 : ℕ), (2 : ℕ)], (x2 x8).length = (1 : ℕ)) →
      (∀ x9 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], (x2 x9).length ≤ (2 : ℕ)) →
      (∀ (x10 : Fin (9 : ℕ)), (x2 ↑x10).length ≤ (3 : ℕ)) →
      (∀ x11 ∈ x1.gates, ¬((0 : ℕ) ∈ x11.inputs ∧ (2 : ℕ) ∈ x11.inputs) ∧ ((9 : ℕ) ∈ x11.inputs → (0 : ℕ) ∉ x11.inputs ∧ (2 : ℕ) ∉ x11.inputs)) →
      ¬∀ (x12 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) =
        (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      have x2 : ℕ → List PEqualNP.CircuitLowerBounds.Gate := fun (x2 : ℕ) => List.filter (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (x2 ∈ x3.inputs)) x1.gates;
      PEqualNP.MetaComplexity.FanInTwo x1 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 →
      (∀ x5 ∈ x1.gates, (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length = (1 : ℕ)) ∧ (x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length = (2 : ℕ) ∧ x5.inputs.Nodup)) →
      x1.size = (14 : ℕ) →
      (∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x2 (9 : ℕ) = [x7]) →
      (∀ x8 ∈ [(0 : ℕ), (2 : ℕ)], (x2 x8).length = (1 : ℕ)) →
      (∀ x9 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], (x2 x9).length ≤ (2 : ℕ)) →
      (∀ (x10 : Fin (9 : ℕ)), (x2 ↑x10).length ≤ (3 : ℕ)) →
      (∀ x11 ∈ x1.gates, ¬((0 : ℕ) ∈ x11.inputs ∧ (2 : ℕ) ∈ x11.inputs) ∧ ((9 : ℕ) ∈ x11.inputs → (0 : ℕ) ∉ x11.inputs ∧ (2 : ℕ) ∉ x11.inputs)) →
      ¬∀ (x12 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) =
        (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ))) := by
  intro x1 x2 hfan hreads hgates hsize hg9 h02 h467 hall9 hg02
  obtain ⟨x7, hop, hreaders⟩ := hg9
  by_cases hcase : ∀ i ∈ x7.inputs, i ≠ 9 → i < 9
  · exact h_input x1 hfan hreads hgates hsize ⟨x7, hop, hreaders, hcase⟩ h02 h467 hall9 hg02
  · have hgate_case : ∃ i ∈ x7.inputs, 10 ≤ i := by
      by_contra hc
      apply hcase
      intro i hi hi9
      by_contra hlt
      have hge : 10 ≤ i := by
        have : 9 ≤ i := by omega
        omega
      exact hc ⟨i, hi, hge⟩
    exact h_gate x1 hfan hreads hgates hsize ⟨x7, hop, hreaders, hgate_case⟩ h02 h467 hall9 hg02
