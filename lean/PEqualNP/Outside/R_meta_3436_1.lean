import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3436_1 :
  let graph : (BitVec 9) → Bool := fun x7 =>
    [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)),
      ((2 : Fin 9), (3 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)),
      ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
      ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)),
      ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)),
      ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any
      (fun e => x7.getLsbD e.1.val && x7.getLsbD e.2.val)
  let inputFn : (BitVec 9) → Fin 9 → Bool := fun w i => w.getLsbD i.val
  let inputs : (BitVec 9) → List Bool := fun w => List.ofFn (inputFn w) ++ [!inputFn w 0]
  let small : (BitVec 9) → Prop := fun w =>
    (Finset.univ.filter (fun i : Fin 9 => inputFn w i = true)).card ≤ 2
  let edges : List (Fin 9 × Fin 9) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
      (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
  let edgeRows : (BitVec 9) → Bool := fun w =>
    edges.any (fun e => inputFn w e.1 && inputFn w e.2)
  let allowed : Fin 11 → Fin 11 → Prop := fun i j =>
    11 * ↑i + ↑j ∈ [1, 2, 3, 4, 6, 9, 13, 14, 15, 16, 17, 18, 19, 20,
      25, 26, 28, 29, 30, 31, 37, 39, 42, 50, 53, 73, 75]
  ∀ (_hRows : ∀ w : BitVec 9, small w → graph w = edgeRows w),
    ∀ (_hSparseMono : ∀ (x1 x2 : Fin 11), allowed x1 x2 → x1.val ≠ 9 → x2.val ≠ 9 →
        ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
            ∃ w : BitVec 9, small w ∧
              C.eval (inputs w ++ [(inputs w).getD x1.val false ||
                (inputs w).getD x2.val false]) ≠ edgeRows w),
      ∀ (_hSparseNot : ∀ (x1 x2 : Fin 11), allowed x1 x2 → (x1.val = 9 ∨ x2.val = 9) →
          ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
              ∃ w : BitVec 9, small w ∧
                C.eval (inputs w ++ [(inputs w).getD x1.val false ||
                  (inputs w).getD x2.val false]) ≠ edgeRows w),
        ∀ (x1 x2 : Fin 11) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
          allowed x1 x2 → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ 13 →
            ∃ (x7 : BitVec 9),
              have x8 : Fin 9 → Bool := fun i => x7.getLsbD i.val
              have x9 : List Bool := List.ofFn x8 ++ [!x8 0]
              x3.eval (x9 ++ [x9.getD x1.val false || x9.getD x2.val false]) ≠ graph x7 := by
  intro graph inputFn inputs small edges edgeRows allowed hRows hSparseMono hSparseNot x1 x2 x3 hallowed hFan hSize
  by_cases hNot : x1.val = 9 ∨ x2.val = 9
  · obtain ⟨w, hs, hdiff⟩ := hSparseNot x1 x2 hallowed hNot x3 hFan hSize
    refine ⟨w, ?_⟩
    change x3.eval (inputs w ++ [(inputs w).getD x1.val false ||
      (inputs w).getD x2.val false]) ≠ graph w
    intro heq
    exact hdiff (by rw [heq, hRows w hs])
  · have hNot1 : x1.val ≠ 9 := fun h => hNot (.inl h)
    have hNot2 : x2.val ≠ 9 := fun h => hNot (.inr h)
    obtain ⟨w, hs, hdiff⟩ := hSparseMono x1 x2 hallowed hNot1 hNot2 x3 hFan hSize
    refine ⟨w, ?_⟩
    change x3.eval (inputs w ++ [(inputs w).getD x1.val false ||
      (inputs w).getD x2.val false]) ≠ graph w
    intro heq
    exact hdiff (by rw [heq, hRows w hs])
