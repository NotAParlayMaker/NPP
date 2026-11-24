import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2901_aux

open PEqualNP.CircuitLowerBounds

def circ : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 }

theorem lhs : ∀ a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool, circ.eval ([a0, a1, a2, a3, a4, a5, a6] ++ [b0, b1, b2, b3, b4, b5, b6]) = ((((((((((((a3 || b2) && (a5 || b1)) && (a3 || a5)) || a0) || a4) && b1) || ((((((a3 || b2) && (a5 || b1)) && (a3 || a5)) || a0) || a6) && b2)) || (((a0 || a1) || a2) && b0)) || (((a1 || a3) || a5) && b3)) || (((a1 || a4) || a6) && b4)) || (((a2 || a3) || a6) && b5)) || (((a2 || a4) || a5) && b6)) := by
  intro a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6
  simp only [circ, Circuit.eval, Circuit.wires, List.foldl, List.map, GateOp.eval, List.getD_cons_succ, List.getD_cons_zero, List.cons_append, List.nil_append, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]

theorem fg : ∀ a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool, ((((((((((((a3 || b2) && (a5 || b1)) && (a3 || a5)) || a0) || a4) && b1) || ((((((a3 || b2) && (a5 || b1)) && (a3 || a5)) || a0) || a6) && b2)) || (((a0 || a1) || a2) && b0)) || (((a1 || a3) || a5) && b3)) || (((a1 || a4) || a6) && b4)) || (((a2 || a3) || a6) && b5)) || (((a2 || a4) || a5) && b6)) = ((a0 && b0) || ((a0 && b1) || ((a0 && b2) || ((a1 && b0) || ((a1 && b3) || ((a1 && b4) || ((a2 && b0) || ((a2 && b5) || ((a2 && b6) || ((a3 && b1) || ((a3 && b3) || ((a3 && b5) || ((a4 && b1) || ((a4 && b4) || ((a4 && b6) || ((a5 && b2) || ((a5 && b3) || ((a5 && b6) || ((a6 && b2) || ((a6 && b4) || ((a6 && b5)))))))))))))))))))))) := by
  decide +kernel

theorem rhs (x y : Fin 7 → Bool) : decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) = ((x 0 && y 0) || ((x 0 && y 1) || ((x 0 && y 2) || ((x 1 && y 0) || ((x 1 && y 3) || ((x 1 && y 4) || ((x 2 && y 0) || ((x 2 && y 5) || ((x 2 && y 6) || ((x 3 && y 1) || ((x 3 && y 3) || ((x 3 && y 5) || ((x 4 && y 1) || ((x 4 && y 4) || ((x 4 && y 6) || ((x 5 && y 2) || ((x 5 && y 3) || ((x 5 && y 6) || ((x 6 && y 2) || ((x 6 && y 4) || ((x 6 && y 5)))))))))))))))))))))) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨p, l, h, hx, hy⟩
    fin_cases p <;> fin_cases l
    · simp at hx hy
      simp [hx, hy]
    · simp at hx hy
      simp [hx, hy]
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [hx, hy]
    · simp at hx hy
      simp [hx, hy]
    · exact absurd h (by decide)
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨0, 0, by decide, hx, hy⟩
    · exact ⟨0, 1, by decide, hx, hy⟩
    · exact ⟨0, 2, by decide, hx, hy⟩
    · exact ⟨1, 0, by decide, hx, hy⟩
    · exact ⟨1, 3, by decide, hx, hy⟩
    · exact ⟨1, 4, by decide, hx, hy⟩
    · exact ⟨2, 0, by decide, hx, hy⟩
    · exact ⟨2, 5, by decide, hx, hy⟩
    · exact ⟨2, 6, by decide, hx, hy⟩
    · exact ⟨3, 1, by decide, hx, hy⟩
    · exact ⟨3, 3, by decide, hx, hy⟩
    · exact ⟨3, 5, by decide, hx, hy⟩
    · exact ⟨4, 1, by decide, hx, hy⟩
    · exact ⟨4, 4, by decide, hx, hy⟩
    · exact ⟨4, 6, by decide, hx, hy⟩
    · exact ⟨5, 2, by decide, hx, hy⟩
    · exact ⟨5, 3, by decide, hx, hy⟩
    · exact ⟨5, 6, by decide, hx, hy⟩
    · exact ⟨6, 2, by decide, hx, hy⟩
    · exact ⟨6, 4, by decide, hx, hy⟩
    · exact ⟨6, 5, by decide, hx, hy⟩

end PEqualNP.Outside.L_meta_2901_aux

open PEqualNP.Outside.L_meta_2901_aux in
theorem PEqualNP.Outside.L_meta_2901 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 31 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ x y : Fin 7 → Bool, C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true)) ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a : Fin 7 => decide (a ∈ ({3} : Finset (Fin 7)))) ++ List.ofFn (fun b : Fin 7 => decide (b ∈ ({1} : Finset (Fin 7))))) = false ∧
  PEqualNP.CircuitLowerBounds.Circuit.eval ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 38] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) (List.ofFn (fun a2 : Fin 7 => decide (a2 ∈ ({5} : Finset (Fin 7)))) ++ List.ofFn (fun b2 : Fin 7 => decide (b2 ∈ ({2} : Finset (Fin 7))))) = false := by
  intro C hC
  subst hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · rfl
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
    decide +kernel
  · intro x y
    rw [rhs, ← fg (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)]
    exact lhs (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)
  · decide +kernel
  · decide +kernel
