import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_983_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Assign each edge to a vertex of a cover, compute each resulting star,
-- and take the disjunction of the stars.

private lemma graph01 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 6 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 5)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩,
        ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩,
        ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph02 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩,
        ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph03 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 3 && x 5) ||
          (x 4 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.and, [1, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [10, 11]⟩,
        ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph04 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩,
        ⟨.and, [1, 10]⟩, ⟨.and, [3, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [9, 11]⟩,
        ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph05 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩,
        ⟨.or, [4, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [9, 10]⟩,
        ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph06 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 4 && x 5) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩,
        ⟨.and, [3, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [9, 10]⟩,
        ⟨.or, [14, 11]⟩, ⟨.or, [15, 13]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph07 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 4 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩,
        ⟨.or, [5, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩,
        ⟨.or, [14, 12]⟩, ⟨.or, [15, 13]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph08 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 4) ||
          (x 2 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 5)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩,
        ⟨.and, [3, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [9, 10]⟩,
        ⟨.or, [14, 11]⟩, ⟨.or, [15, 13]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph09 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 1 && x 3) ||
          (x 2 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 6]⟩,
        ⟨.and, [4, 10]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [8, 9]⟩,
        ⟨.or, [14, 11]⟩, ⟨.or, [15, 13]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph10 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 0 && x 5) ||
          (x 0 && x 6) ||
          (x 1 && x 2) ||
          (x 3 && x 4)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩,
        ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩,
        ⟨.or, [12, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph11 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 0 && x 5) ||
          (x 1 && x 2) ||
          (x 1 && x 6) ||
          (x 3 && x 4)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩,
        ⟨.and, [0, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [3, 4]⟩,
        ⟨.or, [11, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph12 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 0 && x 5) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩,
        ⟨.and, [0, 10]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩,
        ⟨.or, [11, 12]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph13 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 1 && x 6) ||
          (x 3 && x 4)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.or, [2, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [3, 4]⟩,
        ⟨.or, [10, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph14 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 2 && x 6) ||
          (x 3 && x 4)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 4]⟩,
        ⟨.or, [10, 12]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph15 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 3 && x 4) ||
          (x 3 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [3, 13]⟩,
        ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph16 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩,
        ⟨.or, [10, 12]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph17 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 3 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [6, 13]⟩,
        ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph18 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 3 && x 5) ||
          (x 3 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.and, [5, 6]⟩,
        ⟨.or, [10, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph19 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 3 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.and, [1, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 13]⟩,
        ⟨.or, [10, 11]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph20 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 2 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩,
        ⟨.and, [1, 10]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 13]⟩,
        ⟨.or, [9, 11]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph21 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 5)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩,
        ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.and, [4, 5]⟩,
        ⟨.or, [9, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph22 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 3 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩,
        ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.and, [5, 6]⟩,
        ⟨.or, [9, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph23 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 5) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩,
        ⟨.and, [1, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [5, 13]⟩,
        ⟨.or, [9, 11]⟩, ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph24 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩,
        ⟨.and, [1, 10]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 13]⟩,
        ⟨.or, [9, 11]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph25 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 4 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩,
        ⟨.or, [3, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.and, [5, 6]⟩,
        ⟨.or, [9, 10]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph26 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 4) ||
          (x 2 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 5) ||
          (x 4 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩,
        ⟨.or, [2, 4]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 13]⟩,
        ⟨.or, [9, 10]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph27 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 0 && x 5) ||
          (x 0 && x 6) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩,
        ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩,
        ⟨.and, [5, 6]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph28 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 1 && x 6) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.or, [2, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [3, 4]⟩,
        ⟨.and, [5, 6]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph29 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 3 && x 4) ||
          (x 3 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩,
        ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [3, 13]⟩,
        ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [17, 15]⟩], 18⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph30 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 2 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩,
        ⟨.and, [1, 10]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [13, 5]⟩,
        ⟨.and, [6, 14]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [16, 12]⟩, ⟨.or, [17, 15]⟩], 18⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

private lemma graph31 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 5) ||
          (x 5 && x 6)) x := by
  let circuit : Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩,
        ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [4, 6]⟩,
        ⟨.and, [5, 14]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [17, 15]⟩], 18⟩
  refine ⟨circuit, ?_, by decide, ?_⟩
  · simp [Monotone2, circuit]
  · intro x
    have inputs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
      simp only [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [inputs]
    simp [circuit, Circuit.eval, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
      Bool.and_or_distrib_left] <;> ac_rfl

end PEqualNP.Outside.L_meta_983_aux

open PEqualNP.Outside.L_meta_983_aux in
theorem PEqualNP.Outside.L_meta_983 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 6 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 5)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 3 && x 5) ||
          (x 4 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 4 && x 5) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 4 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 4) ||
          (x 2 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 5)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 1 && x 3) ||
          (x 2 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 0 && x 5) ||
          (x 0 && x 6) ||
          (x 1 && x 2) ||
          (x 3 && x 4)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 0 && x 5) ||
          (x 1 && x 2) ||
          (x 1 && x 6) ||
          (x 3 && x 4)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 0 && x 5) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 1 && x 6) ||
          (x 3 && x 4)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 2 && x 6) ||
          (x 3 && x 4)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 3 && x 4) ||
          (x 3 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 3 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 3 && x 5) ||
          (x 3 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 3 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 2 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 5)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 3 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 5) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 4 && x 5) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 4) ||
          (x 2 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 5) ||
          (x 4 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 0 && x 5) ||
          (x 0 && x 6) ||
          (x 1 && x 2) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 1 && x 6) ||
          (x 3 && x 4) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 0 && x 4) ||
          (x 1 && x 2) ||
          (x 1 && x 5) ||
          (x 3 && x 4) ||
          (x 3 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 2 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 6) ||
          (x 5 && x 6)) x) ∧
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 7 → Bool => (x 0 && x 1) ||
          (x 0 && x 2) ||
          (x 0 && x 3) ||
          (x 1 && x 2) ||
          (x 1 && x 4) ||
          (x 3 && x 5) ||
          (x 3 && x 6) ||
          (x 4 && x 5) ||
          (x 5 && x 6)) x) := by
  exact ⟨graph01, graph02, graph03, graph04, graph05, graph06, graph07, graph08,
    graph09, graph10, graph11, graph12, graph13, graph14, graph15, graph16,
    graph17, graph18, graph19, graph20, graph21, graph22, graph23, graph24,
    graph25, graph26, graph27, graph28, graph29, graph30, graph31⟩
