import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2498_1
    (hAnd : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      (circuitFun 9 C = fun x : Fin 9 → Bool =>
        [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
         ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
         ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
         ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
          fun e => x e.1 && x e.2) →
      (∀ v ∈ ([0, 1, 2, 3, 5, 8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
           ∃ k < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD k false)) → S.card ≤ 3) →
      C.gates[1]?.map Gate.op = some GateOp.and → 16 ≤ C.size)
    (hOr : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      (circuitFun 9 C = fun x : Fin 9 → Bool =>
        [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
         ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
         ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
         ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
          fun e => x e.1 && x e.2) →
      (∀ v ∈ ([0, 1, 2, 3, 5, 8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
           ∃ k < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD k false)) → S.card ≤ 3) →
      C.gates[1]?.map Gate.op = some GateOp.or → 16 ≤ C.size)
    (hNot : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      (circuitFun 9 C = fun x : Fin 9 → Bool =>
        [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
         ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
         ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
         ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
          fun e => x e.1 && x e.2) →
      (∀ v ∈ ([0, 1, 2, 3, 5, 8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
           ∃ k < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD k false)) → S.card ≤ 3) →
      C.gates[1]?.map Gate.op = some GateOp.not → 16 ≤ C.size)
    (hNone : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      (circuitFun 9 C = fun x : Fin 9 → Bool =>
        [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
         ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
         ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
         ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
          fun e => x e.1 && x e.2) →
      (∀ v ∈ ([0, 1, 2, 3, 5, 8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
           ∃ k < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD k false)) → S.card ≤ 3) →
      C.gates[1]? = none → 16 ≤ C.size) :
    ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      (circuitFun 9 C = fun x : Fin 9 → Bool =>
        [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
         ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
         ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)),
         ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
          fun e => x e.1 && x e.2) →
      (∀ v ∈ ([0, 1, 2, 3, 5, 8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
           ∃ k < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD k false)) → S.card ≤ 3) →
      16 ≤ C.size := by
  intro C hFan hFirst hFun hStruct
  cases h : C.gates[1]? with
  | none =>
    exact hNone C hFan hFirst hFun hStruct h
  | some g =>
    have hlen : 1 < C.gates.length := by
      obtain ⟨hlt, _⟩ := (List.getElem?_eq_some_iff).1 h
      exact hlt
    have hg : C.gates[1] = g := by
      obtain ⟨_, heq⟩ := (List.getElem?_eq_some_iff).1 h
      exact heq
    have mem : g ∈ C.gates := by
      rw [← hg]
      exact List.getElem_mem hlen
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      have hin := (hFan g mem).1
      rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hin
      exact hin
    have hmap : C.gates[1]?.map Gate.op = some g.op := by
      rw [h]; rfl
    rcases hop with han | hor | hn
    · exact hAnd C hFan hFirst hFun hStruct (hmap.trans (congrArg some han))
    · exact hOr C hFan hFirst hFun hStruct (hmap.trans (congrArg some hor))
    · exact hNot C hFan hFirst hFun hStruct (hmap.trans (congrArg some hn))
