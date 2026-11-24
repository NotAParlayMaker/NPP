import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3053_aux

open PEqualNP.CircuitLowerBounds

def circ : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 28] }], output := 44 }

def F (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool := ((((((((a1 || a2) && b0) && ((((a1 || a2) || a0) || a3) && b0)) || ((((a1 || a2) && b0) || ((((a1 || a2) || a0) || a3) && b0)) && (a0 && (b0 || b4)))) || (((((a1 || a2) && b0) || ((((a1 || a2) || a0) || a3) && b0)) || (a0 && (b0 || b4))) && ((a1 || a4) && b3))) || ((((((a1 || a2) && b0) || ((((a1 || a2) || a0) || a3) && b0)) || (a0 && (b0 || b4))) || ((a1 || a4) && b3)) && (a1 && (b3 || b2)))) || (((((((a1 || a2) && b0) || ((((a1 || a2) || a0) || a3) && b0)) || (a0 && (b0 || b4))) || ((a1 || a4) && b3)) || (a1 && (b3 || b2))) && ((a2 || a5) && b5))) || ((((((((a1 || a2) && b0) || ((((a1 || a2) || a0) || a3) && b0)) || (a0 && (b0 || b4))) || ((a1 || a4) && b3)) || (a1 && (b3 || b2))) || ((a2 || a5) && b5)) && (a2 && (b5 || b1))))

def G (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool) : Bool := ((a0 && b0) || ((a0 && b1) || ((a0 && b2) || ((a1 && b0) || ((a1 && b3) || ((a1 && b4) || ((a2 && b0) || ((a2 && b5) || ((a2 && b6) || ((a3 && b1) || ((a3 && b3) || ((a3 && b5) || ((a4 && b1) || ((a4 && b4) || ((a4 && b6) || ((a5 && b2) || ((a5 && b3) || ((a5 && b6) || ((a6 && b2) || ((a6 && b4) || ((a6 && b5))))))))))))))))))))))

theorem lhs : ∀ a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool, circ.eval ([a0, a1, a2, a3, a4, a5, a6] ++ [b0, b1, b2, b3, b4, b5, b6]) = F a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 := by
  intro a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6
  simp only [circ, F, Circuit.eval, Circuit.wires, List.foldl, List.map, GateOp.eval, List.getD_cons_succ, List.getD_cons_zero, List.cons_append, List.nil_append, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem core : ∀ a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Bool, G a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 = false → (F a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 = true ↔ ((a0 = false ∧ a1 = true ∧ a2 = true ∧ a3 = false ∧ a4 = false ∧ a5 = false ∧ a6 = false) ∧ (b0 = false ∧ b1 = true ∧ b2 = true ∧ b3 = false ∧ b4 = false ∧ b5 = false ∧ b6 = false)) ∨ ((a0 = true ∧ a1 = false ∧ a2 = false ∧ a3 = false ∧ a4 = false ∧ a5 = true ∧ a6 = false) ∧ (b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false ∧ b4 = true ∧ b5 = true ∧ b6 = false))) := by
  unfold F G
  intro a0 a1 a2 a3 a4 a5 a6
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;> decide +kernel

theorem pat (x : Fin 7 → Bool) (S : Finset (Fin 7)) : (∀ i : Fin 7, x i = decide (i ∈ S)) ↔ (x 0 = decide (0 ∈ S) ∧ x 1 = decide (1 ∈ S) ∧ x 2 = decide (2 ∈ S) ∧ x 3 = decide (3 ∈ S) ∧ x 4 = decide (4 ∈ S) ∧ x 5 = decide (5 ∈ S) ∧ x 6 = decide (6 ∈ S)) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6

theorem rhs (x y : Fin 7 → Bool) : decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) = G (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨p, l, h, hx, hy⟩
    fin_cases p <;> fin_cases l
    · simp at hx hy
      simp [G, hx, hy]
    · simp at hx hy
      simp [G, hx, hy]
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
    · simp at hx hy
      simp [G, hx, hy]
    · simp at hx hy
      simp [G, hx, hy]
    · exact absurd h (by decide)
  · intro h
    simp only [G, Bool.or_eq_true, Bool.and_eq_true] at h
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


end PEqualNP.Outside.L_meta_3053_aux

open PEqualNP.Outside.L_meta_3053_aux in
theorem PEqualNP.Outside.L_meta_3053 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 28] }], output := 44 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 32 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C ∧
  (∀ (p l : Fin 7), ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) → PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn (fun a : Fin 7 => decide (a = p)) ++ List.ofFn (fun b : Fin 7 => decide (b = l))) = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (1, 3), (2, 5)] : List (ℕ × ℕ)))) ∧
  (∀ x y : Fin 7 → Bool, (¬ ∃ p l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 0), (2, 0), (0, 1), (3, 1), (4, 1), (0, 2), (5, 2), (6, 2), (1, 3), (3, 3), (5, 3), (1, 4), (4, 4), (6, 4), (2, 5), (3, 5), (6, 5), (2, 6), (4, 6), (5, 6)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn x ++ List.ofFn y) = true ↔ ((∀ i : Fin 7, x i = decide (i ∈ ({1, 2} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({1, 2} : Finset (Fin 7)))) ∨ ((∀ i : Fin 7, x i = decide (i ∈ ({0, 5} : Finset (Fin 7)))) ∧ ∀ j : Fin 7, y j = decide (j ∈ ({4, 5} : Finset (Fin 7)))))) := by
  intro C hC
  subst hC
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · rfl
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
    decide +kernel
  · decide +kernel
  · intro x y h
    have hg : G (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) = false := by
      rw [← rhs x y]
      exact decide_eq_false h
    have e : circ.eval (List.ofFn x ++ List.ofFn y) = F (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) := lhs (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)
    change circ.eval (List.ofFn x ++ List.ofFn y) = true ↔ _
    rw [e, pat x, pat y, pat x, pat y]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.isValue, Fin.reduceEq, or_self, or_false, false_or, or_true, true_or, decide_true, decide_false]
    exact core (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) hg
