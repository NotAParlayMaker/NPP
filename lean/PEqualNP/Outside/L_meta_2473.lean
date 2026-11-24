import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2473 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x5]? = Option.some x6 → x1 x2 x3 x6 → x5 ∈ x4) → ∃ x6 ⊆ x4, x6 ⊆ Finset.range x3.size ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x7]? = Option.some x8 → (x7 ∈ x6 ↔ x1 x2 x3 x8) := by
  intro x1 x2 x3 x4 hsub
  classical
  refine ⟨(Finset.range x3.size).filter (fun i => ∃ g, x3.gates[i]? = some g ∧ x1 x2 x3 g), ?_, Finset.filter_subset _ _, ?_⟩
  · intro i hi
    obtain ⟨_, g, hg, hx1⟩ := Finset.mem_filter.mp hi
    exact hsub i g hg hx1
  · intro x7 x8 hx7
    rw [Finset.mem_filter, Finset.mem_range]
    have hlt : x7 < x3.size := by
      unfold PEqualNP.CircuitLowerBounds.Circuit.size
      exact (List.getElem?_eq_some_iff.mp hx7).1
    constructor
    · rintro ⟨_, g, hg, hx1⟩
      rw [hx7] at hg
      cases hg
      exact hx1
    · intro hx1
      exact ⟨hlt, x8, hx7, hx1⟩
