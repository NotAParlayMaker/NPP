import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_785 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 8 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 5), (1, 2), (2, 3), (3, 4), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have h : ∀ (x0 x1 x2 x3 x4 x5 : Bool),
        (({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit).eval [x0, x1, x2, x3, x4, x5] = true ↔
          (x0 = true ∧ x1 = true) ∨ (x0 = true ∧ x5 = true) ∨ (x1 = true ∧ x2 = true) ∨
          (x2 = true ∧ x3 = true) ∨ (x3 = true ∧ x4 = true) ∨ (x4 = true ∧ x5 = true)) := by
      decide
    have hof : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by simp [List.ofFn_succ]
    rw [hof, h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)]
    constructor
    · rintro (⟨h0, h1⟩ | ⟨h0, h5⟩ | ⟨h1, h2⟩ | ⟨h2, h3⟩ | ⟨h3, h4⟩ | ⟨h4, h5⟩)
      · exact ⟨0, 1, by simp, h0, h1⟩
      · exact ⟨0, 5, by simp, h0, h5⟩
      · exact ⟨1, 2, by simp, h1, h2⟩
      · exact ⟨2, 3, by simp, h2, h3⟩
      · exact ⟨3, 4, by simp, h3, h4⟩
      · exact ⟨4, 5, by simp, h4, h5⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      fin_cases u <;> fin_cases v <;> simp_all
