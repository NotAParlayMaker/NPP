import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2473 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x5]? = Option.some x6 → x1 x2 x3 x6 → x5 ∈ x4) → ∃ x6 ⊆ x4, x6 ⊆ Finset.range x3.size ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x7]? = Option.some x8 → (x7 ∈ x6 ↔ x1 x2 x3 x8) := by
  classical
  intro P n C T h
  refine ⟨(Finset.range C.size).filter (fun i => ∃ g, C.gates[i]? = some g ∧ P n C g), ?_, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨g, hg, hP⟩ := hi.2
    exact h i g hg hP
  · exact Finset.filter_subset _ _
  · intro i g hg
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, g', hg', hP⟩
      rw [hg] at hg'
      cases hg'
      exact hP
    · intro hP
      refine ⟨?_, g, hg, hP⟩
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hg
      exact hlt
