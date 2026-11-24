import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3170_2
    (base :
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [!x 0, false]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (pair :
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [!x 0, x 1 || x 5]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (bypass :
      ∀ C : Circuit, FanInTwo C → ∀ j : Fin 11,
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (w : List Bool) (b : Bool), w.length = 10 →
            D.eval (w ++ [b]) = C.eval (w ++ [w.getD j.val false])) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  let edge (x : Fin 9 → Bool) := (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let inputs (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  intro pins hlen _ allowed C hC hsize
  let bad (i j : Fin 9) :=
    ∃ x : Fin 9 → Bool, C.eval (inputs x ++ [x i || x j]) ≠ edge x
  have get (i : Fin 9) (x : Fin 9 → Bool) : (inputs x).getD i.val false = x i := by
    change (List.ofFn x ++ [!x 0]).getD i.val false = x i
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  have duplicate (i : Fin 9) : bad i i := by
    obtain ⟨D, hD, hs, heval⟩ := bypass C hC (Fin.castAdd 2 i)
    obtain ⟨x, hx⟩ := base D hD (hs.trans_le hsize)
    have he := heval (inputs x) false (by simp [inputs])
    change D.eval (inputs x ++ [false]) = C.eval (inputs x ++ [(inputs x).getD i.val false]) at he
    rw [get] at he
    refine ⟨x, ?_⟩
    change C.eval (inputs x ++ [x i || x i]) ≠ edge x
    rw [Bool.or_self, ← he]
    exact hx
  have b15 : bad 1 5 := by
    obtain ⟨x, hx⟩ := pair C hC hsize
    refine ⟨x, ?_⟩
    change C.eval ((List.ofFn x ++ [!x 0]) ++ [x 1 || x 5]) ≠ edge x
    rw [List.append_assoc]
    exact hx
  have b51 : bad 5 1 := by
    obtain ⟨x, hx⟩ := b15
    refine ⟨x, ?_⟩
    change C.eval (inputs x ++ [x 5 || x 1]) ≠ edge x
    rw [Bool.or_comm (x 5) (x 1)]
    exact hx
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, pins = [a, b] := by
    cases pins with
    | nil => simp at hlen
    | cons a rest =>
      cases rest with
      | nil => simp at hlen
      | cons b tail =>
        have ht : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hlen
          omega
        exact ⟨a, b, by rw [ht]⟩
  have ha := allowed a (by simp)
  have hb := allowed b (by simp)
  let i : Fin 9 := ⟨a, by omega⟩
  let j : Fin 9 := ⟨b, by omega⟩
  have hbad : bad i j := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact duplicate 1
    · exact b15
    · exact b51
    · exact duplicate 5
  obtain ⟨x, hx⟩ := hbad
  refine ⟨x, ?_⟩
  change C.eval (inputs x ++ [((inputs x).getD i.val false ||
    ((inputs x).getD j.val false || false))]) ≠ edge x
  rw [get, get, Bool.or_false]
  exact hx
