import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2718_41
    (normalize : ∀ C : Circuit, Monotone2 C →
      (∃ x y : Fin 26 → Bool, circuitFun 26 C x ≠ circuitFun 26 C y) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ circuitFun 26 D = circuitFun 26 C ∧
        D.output < 26 + D.size ∧
        ∀ j (g : Gate), D.gates[j]? = some g →
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < 26 + j)
    (backwardCase :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → x3.output < 26 + x3.size → (∀ j (g : Gate), x3.gates[j]? = some g → ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < 26 + j) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 ∧ (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x5 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x5 (1 : ℕ))) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), (∃ x5 ∈ x1, x3 = x4 + x5) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∉ x3, ∃ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) ∧ ∃ x7 ∈ x1, x4 = x6 + x7) → ((∃ (x5 : Fin (13 : ℕ)), ∀ x6 ∈ x3, ∃ x8 ∈ x1, x6 = x5 + x8) ∨ ∃ (x5 : Fin (13 : ℕ)), ∀ (x6 : Fin (13 : ℕ)), (∀ x7 ∈ x3, ¬∃ x9 ∈ x1, x7 = x6 + x9) → ∃ x8 ∈ x1, x5 = x6 + x8) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x2 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x3, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x3, ¬∃ x10 ∈ x1, x8 = x7 + x10)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 ∧ (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x5 (1 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x5 (1 : ℕ)) := by
  intro diff good C hc
  have zeroMem : (0 : Fin 13) ∈ diff := by decide +kernel
  have on := hc.2.2.1 (0 : Fin 13) (0 : Fin 13) ⟨0, zeroMem, by simp⟩
  have off := hc.2.2.2 ∅
    (by
      intro p _
      refine ⟨p, ?_, 0, zeroMem, ?_⟩
      · simp
      · simp)
    (by
      left
      exact ⟨0, by simp⟩)
  have nonconstant : ∃ x y : Fin 26 → Bool, circuitFun 26 C x ≠ circuitFun 26 C y := by
    exact ⟨_, _, fun e => Bool.false_ne_true (off.symm.trans (e.symm.trans on))⟩
  obtain ⟨D, monotone, size, same, output, sorted⟩ := normalize C hc.1 nonconstant
  have hd : good D := by
    refine ⟨monotone, size.trans hc.2.1, ?_, ?_⟩
    · intro p l h
      rw [same]
      exact hc.2.2.1 p l h
    · intro S maximal degenerate
      rw [same]
      exact hc.2.2.2 S maximal degenerate
  exact backwardCase D hd output sorted
