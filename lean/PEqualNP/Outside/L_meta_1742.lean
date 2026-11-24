import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1742_aux

theorem k2 : ∀ a b c d e f g h i j k l m n : Bool, (((a || b || c) && (h || i || j)) || ((e || f || g) && k) || ((d || f || g) && l) || ((d || e || g) && m) || ((d || e || f) && n))
      = decide (∃ p : Fin 7, ∃ q : Fin 7, ((p : ℕ), (q : ℕ)) ∈ ([(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 4), (3, 5), (3, 6),
    (4, 3), (4, 5), (4, 6), (5, 3), (5, 4), (5, 6), (6, 3), (6, 4), (6, 5)] : List (ℕ × ℕ)) ∧ ![a, b, c, d, e, f, g] p = true ∧ ![h, i, j, k, l, m, n] q = true) := by
  intro a b c d e f g h i j k l m n
  rw [Bool.eq_iff_iff]
  simp [Fin.exists_fin_succ]
  simp only [or_and_right, and_or_left, or_assoc]
  simp only [or_comm, or_left_comm]

theorem k1 : ∀ a b c d e f g h i j k l m n : Bool, ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 28] }], output := 32 } : PEqualNP.CircuitLowerBounds.Circuit).eval [a, b, c, d, e, f, g, h, i, j, k, l, m, n] = (((a || b || c) && (h || i || j)) || ((e || f || g) && k) || ((d || f || g) && l) || ((d || e || g) && m) || ((d || e || f) && n)) := by
  intro a b c d e f g h i j k l m n
  simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.or_assoc]

end PEqualNP.Outside.L_meta_1742_aux

theorem PEqualNP.Outside.L_meta_1742 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 28] }], output := 32 } : PEqualNP.CircuitLowerBounds.Circuit) →
  let B2 : List (ℕ × ℕ) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2), (3, 4), (3, 5), (3, 6),
    (4, 3), (4, 5), (4, 6), (5, 3), (5, 4), (5, 6), (6, 3), (6, 4), (6, 5)];
  (∀ m : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun p : Fin 7 => ((p : ℕ), (m : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p : Fin 7, ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2)).card = 3) ∧
  (∀ p p' : Fin 7, p ≠ p' → ((Finset.univ : Finset (Fin 7)).filter (fun l : Fin 7 => ((p : ℕ), (l : ℕ)) ∈ B2 ∧ ((p' : ℕ), (l : ℕ)) ∈ B2)).card ≠ 1) ∧
  C.gates.length = 19 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (7 + 7) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (x y : Fin 7 → Bool), C.eval (List.ofFn x ++ List.ofFn y)
     = decide (∃ p : Fin 7, ∃ l : Fin 7, ((p : ℕ), (l : ℕ)) ∈ B2 ∧ x p = true ∧ y l = true) := by
  intro C hC
  subst hC
  dsimp only
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, rfl, ?_, by simp, ?_⟩
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
    decide +kernel
  · intro x y
    have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      funext i
      fin_cases i <;> rfl
    have hy : y = ![y 0, y 1, y 2, y 3, y 4, y 5, y 6] := by
      funext i
      fin_cases i <;> rfl
    rw [hx, hy]
    exact (PEqualNP.Outside.L_meta_1742_aux.k1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)).trans (PEqualNP.Outside.L_meta_1742_aux.k2 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6))
