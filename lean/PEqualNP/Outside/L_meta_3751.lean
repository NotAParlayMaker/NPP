import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L3751

open PEqualNP.CircuitLowerBounds

def K : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [54, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 55] }], output := 56 }

theorem formula_edges : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool,
    (((((((((((b0 || b1) || b3) && ((b7 || b8) || b10)) || (b5 && (b7 || b10))) && ((b0 || b10) && (((b1 || b3) || b5) || b7))) || (((((b0 || b1) || b3) && ((b7 || b8) || b10)) || (b4 && (b7 || b8))) && ((b1 || b8) && (((b0 || b3) || b4) || b7)))) || (b2 && (b7 || b12))) || (((b0 || b5) || b6) && b9)) || (((b1 || b4) || b6) && b11)) || (((b2 || b3) || b6) && b12)) || (((b2 || b4) || b5) && b13)) =
    ((b0 && b7) || (b0 && b8) || (b0 && b9) || (b1 && b7) || (b1 && b10) || (b1 && b11) || (b2 && b7) || (b2 && b12) || (b2 && b13) || (b3 && b8) || (b3 && b10) || (b3 && b12) || (b4 && b8) || (b4 && b11) || (b4 && b13) || (b5 && b9) || (b5 && b10) || (b5 && b13) || (b6 && b9) || (b6 && b11) || (b6 && b12)) := by
  decide +kernel

theorem and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_formula (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) : K.eval [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13] = (((((((((((b0 || b1) || b3) && ((b7 || b8) || b10)) || (b5 && (b7 || b10))) && ((b0 || b10) && (((b1 || b3) || b5) || b7))) || (((((b0 || b1) || b3) && ((b7 || b8) || b10)) || (b4 && (b7 || b8))) && ((b1 || b8) && (((b0 || b3) || b4) || b7)))) || (b2 && (b7 || b12))) || (((b0 || b5) || b6) && b9)) || (((b1 || b4) || b6) && b11)) || (((b2 || b3) || b6) && b12)) || (((b2 || b4) || b5) && b13)) := by
  simp only [K, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
    and2, or2]

theorem list_any (x : Fin 14 → Bool) :
    (([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)).any fun e => x e.1 && x e.2) =
    ((x 0 && x 7) || (x 0 && x 8) || (x 0 && x 9) || (x 1 && x 7) || (x 1 && x 10) || (x 1 && x 11) || (x 2 && x 7) || (x 2 && x 12) || (x 2 && x 13) || (x 3 && x 8) || (x 3 && x 10) || (x 3 && x 12) || (x 4 && x 8) || (x 4 && x 11) || (x 4 && x 13) || (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 13) || (x 6 && x 9) || (x 6 && x 11) || (x 6 && x 12)) := by
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

theorem computes (x : Fin 14 → Bool) : PEqualNP.MetaComplexity.circuitFun 14 K x =
    decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true) := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := rfl
  have hl : PEqualNP.MetaComplexity.circuitFun 14 K x = K.eval [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := by
    rw [← hx]; rfl
  rw [hl, eval_formula, formula_edges, ← list_any, Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [List.any_eq_true, Bool.and_eq_true]

theorem shape : PEqualNP.TopForm.IsAO2 14 K ∧ K.size = 43 := by
  decide +kernel

theorem rereads : ∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)),
    PEqualNP.Core.ReadTwiceAt 14 K (K.output - 14) e.1 e.2 ↔
      e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14)) := by
  decide +kernel

end PEqualNP.Outside.L3751

theorem PEqualNP.Outside.L_meta_3751 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [42, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [54, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 55] }], output := 56 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 43 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  intro C hC
  subst hC
  exact ⟨PEqualNP.Outside.L3751.shape.1, PEqualNP.Outside.L3751.shape.2,
    PEqualNP.Outside.L3751.computes, PEqualNP.Outside.L3751.rereads⟩
