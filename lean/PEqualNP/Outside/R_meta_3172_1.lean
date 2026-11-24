import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3172_1
    (duplicates :
      ∀ i ∈ ([2, 3] : List (Fin 9)), ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x i]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (distinct :
      ∀ i ∈ ([3, 8] : List (Fin 9)), ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 2 || x i]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (permute :
      ∀ (C : Circuit), FanInTwo C → ∀ p : Equiv.Perm (Fin 9),
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (x : Fin 9 → Bool) (u v : Bool),
            D.eval (List.ofFn x ++ [u, v]) = C.eval (List.ofFn (fun i => x (p i)) ++ [u, v])) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  let edge (x : Fin 9 → Bool) := (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let sigma : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
  have inv : Function.Involutive sigma := by
    change ∀ i, sigma (sigma i) = i
    decide
  let p : Equiv.Perm (Fin 9) := ⟨sigma, sigma, inv, inv⟩
  have zeroFixed : p 0 = 0 := rfl
  have edgeInvariant (x : Fin 9 → Bool) : edge (fun i => x (p i)) = edge x := by
    change (x 0 && x 5 || x 5 && x 8 || x 8 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 1 || x 5 && x 7 || x 8 && x 6 || x 3 && x 2 || x 1 && x 6 ||
      x 7 && x 2 || x 2 && x 1) = edge x
    dsimp only [edge]
    ac_rfl
  intro pins hlen _ hpins C hC hsize
  let bad (i j : Fin 9) : Prop :=
    ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x i || x j]) ≠ edge x
  have swap (i j : Fin 9) (h : bad j i) : bad i j := by
    obtain ⟨x, hx⟩ := h
    refine ⟨x, ?_⟩
    change C.eval (List.ofFn x ++ [!x 0, x i || x j]) ≠ edge x
    rw [Bool.or_comm (x i) (x j)]
    exact hx
  have fromPerm (i j : Fin 9)
      (h : ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
        ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0, x (p i) || x (p j)]) ≠ edge x) :
      bad i j := by
    obtain ⟨D, hD, hs, hrel⟩ := permute C hC p
    obtain ⟨x, hx⟩ := h D hD (hs.trans_le hsize)
    rw [hrel] at hx
    refine ⟨fun k => x (p k), ?_⟩
    change C.eval ((List.ofFn fun k => x (p k)) ++ [!x (p 0), x (p i) || x (p j)]) ≠
      edge (fun k => x (p k))
    rw [zeroFixed, edgeInvariant]
    exact hx
  have b22 : bad 2 2 := by
    obtain ⟨x, hx⟩ := duplicates 2 (by decide) C hC hsize
    refine ⟨x, ?_⟩
    change C.eval (List.ofFn x ++ [!x 0, x 2 || x 2]) ≠ edge x
    rw [Bool.or_self]
    exact hx
  have b33 : bad 3 3 := by
    obtain ⟨x, hx⟩ := duplicates 3 (by decide) C hC hsize
    refine ⟨x, ?_⟩
    change C.eval (List.ofFn x ++ [!x 0, x 3 || x 3]) ≠ edge x
    rw [Bool.or_self]
    exact hx
  have b88 : bad 8 8 := by
    apply fromPerm
    intro D hD hs
    obtain ⟨x, hx⟩ := duplicates 2 (by decide) D hD hs
    refine ⟨x, ?_⟩
    change D.eval (List.ofFn x ++ [!x 0, x 2 || x 2]) ≠ edge x
    rw [Bool.or_self]
    exact hx
  have b23 : bad 2 3 := distinct 3 (by decide) C hC hsize
  have b28 : bad 2 8 := distinct 8 (by decide) C hC hsize
  have b83 : bad 8 3 := by
    apply fromPerm
    intro D hD hs
    exact distinct 3 (by decide) D hD hs
  obtain ⟨i, j, rfl⟩ : ∃ i j : ℕ, pins = [i, j] := by
    cases pins with
    | nil => simp at hlen
    | cons i rest =>
      cases rest with
      | nil => simp at hlen
      | cons j tail =>
        have ht : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hlen
          omega
        exact ⟨i, j, by rw [ht]⟩
  have hi := hpins i (by simp)
  have hj := hpins j (by simp)
  have hi9 : i < 9 := by omega
  have hj9 : j < 9 := by omega
  have selected : bad ⟨i, hi9⟩ ⟨j, hj9⟩ := by
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
    · exact b22
    · exact b23
    · exact b28
    · exact swap 3 2 b23
    · exact b33
    · exact swap 3 8 b83
    · exact swap 8 2 b28
    · exact b83
    · exact b88
  obtain ⟨x, hx⟩ := selected
  refine ⟨x, ?_⟩
  let w := List.ofFn x ++ [!x 0]
  change C.eval (w ++ [GateOp.or.eval [w.getD i false, w.getD j false]]) ≠ edge x
  have a : w.getD i false = x ⟨i, hi9⟩ := by
    change (List.ofFn x ++ [!x 0]).getD i false = _
    rw [List.getD_append _ _ _ _ (by simpa using hi9)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi9, dite_true, Option.getD_some]
  have b : w.getD j false = x ⟨j, hj9⟩ := by
    change (List.ofFn x ++ [!x 0]).getD j false = _
    rw [List.getD_append _ _ _ _ (by simpa using hj9)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj9, dite_true, Option.getD_some]
  rw [a, b]
  change C.eval ((List.ofFn x ++ [!x 0]) ++ [(x ⟨i, hi9⟩ || (x ⟨j, hj9⟩ || false))]) ≠ edge x
  rw [Bool.or_false, List.append_assoc]
  exact hx
