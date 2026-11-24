import Mathlib
import PEqualNP.Defs

-- Trim gates after the output and constrain the marked readers using the test inputs.
theorem PEqualNP.Outside.R_meta_3953_617
    (trim : let inputs := fun r : ℕ => List.ofFn (fun i : Fin 9 => r.testBit i.val) ++
        [r.testBit 4 || r.testBit 6]
      let positives : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
      let negatives : List ℕ := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
      let fits := fun D : PEqualNP.CircuitLowerBounds.Circuit => ∀ r ∈ positives ++ negatives,
        D.eval (inputs r) = decide (r ∈ positives)
      let unique := fun D : PEqualNP.CircuitLowerBounds.Circuit => ∀ v ∈ ([4, 6] : List ℕ),
        ∃! j : Fin D.gates.length, v ∈ (D.gates.get j).inputs
      let separates := fun D : PEqualNP.CircuitLowerBounds.Circuit =>
        ∀ a ∈ ([(4,17,69), (4,17,201), (4,24,104), (4,24,201),
          (6,66,50), (6,66,402), (6,320,276), (6,320,402)] : List (ℕ × ℕ × ℕ)),
        ∀ j : Fin D.gates.length, a.1 ∈ (D.gates.get j).inputs →
          (D.wires (inputs a.2.1)).getD (10 + j.val) false = true ∧
          (D.wires (inputs a.2.2)).getD (10 + j.val) false = false
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → unique C → fits C →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ C.size ∧ fits D ∧
          D.output + 1 = 10 + D.size ∧ unique D ∧
          (∀ j : Fin D.gates.length, 4 ∈ (D.gates.get j).inputs → 6 ∉ (D.gates.get j).inputs) ∧ separates D)
    (bound : let inputs := fun r : ℕ => List.ofFn (fun i : Fin 9 => r.testBit i.val) ++
        [r.testBit 4 || r.testBit 6]
      let positives : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]
      let negatives : List ℕ := [42, 50, 69, 104, 116, 138, 201, 208, 261, 276, 385, 402]
      let fits := fun D : PEqualNP.CircuitLowerBounds.Circuit => ∀ r ∈ positives ++ negatives,
        D.eval (inputs r) = decide (r ∈ positives)
      let unique := fun D : PEqualNP.CircuitLowerBounds.Circuit => ∀ v ∈ ([4, 6] : List ℕ),
        ∃! j : Fin D.gates.length, v ∈ (D.gates.get j).inputs
      let separates := fun D : PEqualNP.CircuitLowerBounds.Circuit =>
        ∀ a ∈ ([(4,17,69), (4,17,201), (4,24,104), (4,24,201),
          (6,66,50), (6,66,402), (6,320,276), (6,320,402)] : List (ℕ × ℕ × ℕ)),
        ∀ j : Fin D.gates.length, a.1 ∈ (D.gates.get j).inputs →
          (D.wires (inputs a.2.1)).getD (10 + j.val) false = true ∧
          (D.wires (inputs a.2.2)).getD (10 + j.val) false = false
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → D.size ≤ 14 →
        D.output + 1 = 10 + D.size → unique D → (∀ j : Fin D.gates.length, 4 ∈ (D.gates.get j).inputs → 6 ∉ (D.gates.get j).inputs) →
        separates D → fits D → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (14 : ℕ) →       (∀ x4 ∈ [(4 : ℕ), (6 : ℕ)], ∃! x6 : Fin x1.gates.length, x4 ∈ (x1.gates.get x6).inputs) →         (∀ x5 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)] ++ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)],             have x7 : Fin (9 : ℕ) → Bool := fun (x7 : Fin (9 : ℕ)) => x5.testBit ↑x7;             x1.eval (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]) = Decidable.decide (x5 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →           False := by
  intro C hmono hsize hreader hfit
  obtain ⟨D, hmonoD, hsizeD, hfitD, hout, hreaderD, hdistinct, hseparates⟩ :=
    trim C hmono hreader hfit
  exact bound D hmonoD (hsizeD.trans hsize) hout hreaderD hdistinct hseparates hfitD
