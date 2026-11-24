import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3024_1
    (raw :
      ∀ i ∈ ([0, 1, 3, 4, 6, 8] : List (Fin 9)), ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [x 0 || x 2, !x i]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (other :
      ∀ (b : Bool) (C : Circuit), FanInTwo C → C.size ≤ 13 →
        ∃ x : Fin 9 → Bool,
          C.eval (List.ofFn x ++ [x 0 || x 2, !(b && (x 0 || x 2))]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (permute :
      ∀ (C : Circuit), FanInTwo C → ∀ p : Equiv.Perm (Fin 9),
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (x : Fin 9 → Bool) (u v : Bool),
            D.eval (List.ofFn x ++ [u, v]) = C.eval (List.ofFn (fun i => x (p i)) ++ [u, v])) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  let edge (x : Fin 9 → Bool) := (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let first (x : Fin 9 → Bool) := x 0 || x 2
  let sigma : Fin 9 → Fin 9 := ![2, 1, 0, 5, 7, 3, 6, 4, 8]
  have inv : Function.Involutive sigma := by
    change ∀ i, sigma (sigma i) = i
    decide
  let p : Equiv.Perm (Fin 9) := ⟨sigma, sigma, inv, inv⟩
  have firstInvariant (x : Fin 9 → Bool) : first (fun i => x (p i)) = first x := by
    change (x 2 || x 0) = (x 0 || x 2)
    exact Bool.or_comm _ _
  have edgeInvariant (x : Fin 9 → Bool) : edge (fun i => x (p i)) = edge x := by
    change (x 2 && x 1 || x 1 && x 0 || x 0 && x 5 || x 5 && x 7 || x 7 && x 2 ||
      x 2 && x 3 || x 1 && x 6 || x 0 && x 4 || x 5 && x 8 || x 3 && x 4 ||
      x 6 && x 8 || x 8 && x 3) = edge x
    dsimp only [edge]
    ac_rfl
  have reps : ∀ i : Fin 9, i ∈ ([0, 1, 3, 4, 6, 8] : List (Fin 9)) ∨
      p i ∈ ([0, 1, 3, 4, 6, 8] : List (Fin 9)) := by
    change ∀ i : Fin 9, i ∈ ([0, 1, 3, 4, 6, 8] : List (Fin 9)) ∨
      sigma i ∈ ([0, 1, 3, 4, 6, 8] : List (Fin 9))
    decide
  intro pins _ C hC hsize
  have allRaw (i : Fin 9) :
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [first x, !x i]) ≠ edge x := by
    rcases reps i with hi | hi
    · exact raw i hi C hC hsize
    · obtain ⟨D, hD, hsz, hrel⟩ := permute C hC p
      obtain ⟨x, hx⟩ := raw (p i) hi D hD (hsz.trans_le hsize)
      have he : D.eval (List.ofFn x ++ [first x, !x (p i)]) ≠ edge x := hx
      rw [hrel] at he
      refine ⟨fun j => x (p j), ?_⟩
      rw [firstInvariant, edgeInvariant]
      exact he
  cases pins with
  | nil =>
    obtain ⟨x, hx⟩ := other false C hC hsize
    refine ⟨x, ?_⟩
    change C.eval ((List.ofFn x ++ [first x]) ++ [true]) ≠ edge x
    rw [List.append_assoc]
    exact hx
  | cons j js =>
    have evalAt (x : Fin 9 → Bool) :
        GateOp.not.eval ((j :: js).map (fun k : Fin 11 => (List.ofFn x ++ [first x]).getD k.val false)) =
          !((List.ofFn x ++ [first x]).getD j.val false) := rfl
    by_cases hj : j.val < 9
    · let i : Fin 9 := ⟨j.val, hj⟩
      obtain ⟨x, hx⟩ := allRaw i
      refine ⟨x, ?_⟩
      change C.eval ((List.ofFn x ++ [first x]) ++ [_]) ≠ edge x
      rw [evalAt, List.getD_append _ _ _ _ (by simpa using hj)]
      have hget : (List.ofFn x).getD j.val false = x i := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some, i]
      rw [hget, List.append_assoc]
      exact hx
    · by_cases heq : j.val = 9
      · obtain ⟨x, hx⟩ := other true C hC hsize
        refine ⟨x, ?_⟩
        change C.eval ((List.ofFn x ++ [first x]) ++ [_]) ≠ edge x
        rw [evalAt, heq]
        have hget : (List.ofFn x ++ [first x]).getD 9 false = first x := by
          simp [List.getD_eq_getElem?_getD]
        rw [hget, List.append_assoc]
        exact hx
      · have out : j.val = 10 := by
          have hlt := j.isLt
          omega
        obtain ⟨x, hx⟩ := other false C hC hsize
        refine ⟨x, ?_⟩
        change C.eval ((List.ofFn x ++ [first x]) ++ [_]) ≠ edge x
        rw [evalAt, out, List.getD_eq_default _ _ (by simp), List.append_assoc]
        exact hx
