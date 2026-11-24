import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- Set input 6 to false. The extra OR wire now duplicates input 0. Two test
   assignments show that the unfixed circuit depends on wire 6 and is not
   that input projection. A gate that reads it can therefore be removed
   under the restriction, with false and true available as input ports.
   On the eight remaining vertices, the complemented vertex has two
   possible types under automorphisms of the ten-edge graph. -/
set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_3248_1
    (degreeTwo : ∀ D : Circuit, FanInTwo D → D.size ≤ 12 →
      ∃ x : Fin 8 → Bool, D.eval (List.ofFn (fun i => if i = (0 : Fin 8) then !x i else x i) ++ [false, true]) ≠
        ([(0, 1), (1, 2), (2, 3), (0, 4), (1, 5), (2, 6), (3, 7), (4, 6), (5, 7), (7, 4)] : List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2))
    (degreeThree : ∀ D : Circuit, FanInTwo D → D.size ≤ 12 →
      ∃ x : Fin 8 → Bool, D.eval (List.ofFn (fun i => if i = (1 : Fin 8) then !x i else x i) ++ [false, true]) ≠
        ([(0, 1), (1, 2), (2, 3), (0, 4), (1, 5), (2, 6), (3, 7), (4, 6), (5, 7), (7, 4)] : List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2))
    (remove : ∀ (n m : ℕ) (z : Fin n) (one : Fin m) (f : Fin n → Fin m) (C : Circuit),
      FanInTwo C →
      (∃ u v : Fin n → Bool, (∀ j, j ≠ z → u j = v j) ∧ circuitFun n C u ≠ circuitFun n C v) →
      (∃ u : Fin n → Bool, circuitFun n C u ≠ u z) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧ ∀ y : Fin m → Bool,
        y (f z) = false → y one = true → circuitFun m D y = circuitFun n C (y ∘ f)) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → ∃ (x8 : Fin (9 : ℕ) → Bool), x3.eval ((List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ))]).set ↑x2 !x8 x2) ≠ x1 x8 := by
  intro targetFn i C h0 h6 fan small
  classical
  by_contra! all
  let edge9 (x : Fin 9 → Bool) := ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let edge8 (x : Fin 8 → Bool) := ([(0, 1), (1, 2), (2, 3), (0, 4), (1, 5), (2, 6), (3, 7), (4, 6), (5, 7), (7, 4)] : List (Fin 8 × Fin 8)).any (fun e => x e.1 && x e.2)
  let pack (i : Fin 9) (x : Fin 9 → Bool) : Fin 10 → Bool :=
    ![(if i = 0 then !x 0 else x 0), (if i = 1 then !x 1 else x 1), (if i = 2 then !x 2 else x 2), (if i = 3 then !x 3 else x 3), (if i = 4 then !x 4 else x 4), (if i = 5 then !x 5 else x 5), (if i = 6 then !x 6 else x 6), (if i = 7 then !x 7 else x 7), (if i = 8 then !x 8 else x 8), x 0 || x 6]
  have packEq (x : Fin 9 → Bool) : List.ofFn (pack i x) =
      (List.ofFn x ++ [x 0 || x 6]).set i.val (!x i) := by fin_cases i <;> rfl
  have good (x : Fin 9 → Bool) : circuitFun 10 C (pack i x) = edge9 x := by
    change C.eval (List.ofFn (pack i x)) = _
    rw [packEq]
    exact all x
  let row (b : Bool) : Fin 9 → Bool := ![true,false,false,false,false,false,b,false,true]
  let hit : Fin 9 → Bool := ![true,true,false,false,false,false,false,false,false]
  have pair : ∀ (j : Fin 9), j ≠ 6 → ∀ k : Fin 10, k ≠ 6 →
      pack j (row false) k = pack j (row true) k := by decide +kernel
  have sense : ∃ u v : Fin 10 → Bool, (∀ j, j ≠ 6 → u j = v j) ∧
      circuitFun 10 C u ≠ circuitFun 10 C v := by
    refine ⟨pack i (row false), pack i (row true), pair i h6, ?_⟩
    rw [good, good]
    decide +kernel
  have nonproj : ∃ u : Fin 10 → Bool, circuitFun 10 C u ≠ u 6 := by
    refine ⟨pack i hit, ?_⟩
    rw [good]
    have chk : ∀ j : Fin 9, j ≠ 6 → edge9 hit ≠ pack j hit 6 := by decide +kernel
    exact chk i h6
  let f : Fin 9 → Fin 10 → Fin 10 := ![![1, 0, 4, 7, 5, 2, 8, 6, 3, 1], ![1, 0, 4, 7, 5, 2, 8, 6, 3, 1], ![4, 0, 1, 2, 6, 7, 8, 5, 3, 4], ![7, 3, 2, 1, 5, 4, 8, 6, 0, 7], ![1, 5, 7, 4, 0, 2, 8, 3, 6, 1], ![2, 3, 7, 4, 6, 1, 8, 5, 0, 2], ![1, 0, 4, 7, 5, 2, 8, 6, 3, 1], ![7, 5, 1, 2, 3, 4, 8, 0, 6, 7], ![2, 3, 7, 4, 6, 1, 8, 5, 0, 2]]
  let typ : Fin 9 → Fin 8 := ![0, 0, 1, 1, 0, 1, 0, 0, 0]
  let lift (i : Fin 9) (x : Fin 8 → Bool) (v : Fin 9) : Bool :=
    (List.ofFn x ++ [false,true]).getD (f i v.castSucc).val false
  let env (j : Fin 8) (x : Fin 8 → Bool) : Fin 10 → Bool :=
    ![(if j = 0 then !x 0 else x 0), (if j = 1 then !x 1 else x 1), (if j = 2 then !x 2 else x 2), (if j = 3 then !x 3 else x 3), (if j = 4 then !x 4 else x 4), (if j = 5 then !x 5 else x 5), (if j = 6 then !x 6 else x 6), (if j = 7 then !x 7 else x 7), false, true]
  have envEq (j : Fin 8) (x : Fin 8 → Bool) : List.ofFn (env j x) =
      List.ofFn (fun k => if k = j then !x k else x k) ++ [false,true] := by fin_cases j <;> rfl
  have projection : ∀ i : Fin 9, i ≠ 0 → i ≠ 6 → ∀ x : Fin 8 → Bool,
      (env (typ i) x ∘ f i) = pack i (lift i x) ∧ edge9 (lift i x) = edge8 x := by decide +kernel
  have zero : ∀ (i : Fin 9) (x : Fin 8 → Bool), env (typ i) x (f i 6) = false := by
    intro j x
    fin_cases j <;> rfl
  obtain ⟨D, hd, hs, eq⟩ := remove 10 10 6 9 (f i) C fan sense nonproj
  have short : D.size ≤ 12 := by omega
  have hk : typ i = 0 ∨ typ i = 1 := by fin_cases i <;> decide
  have counter : ∃ x : Fin 8 → Bool, D.eval (List.ofFn (env (typ i) x)) ≠ edge8 x := by
    simp only [envEq]
    rcases hk with h | h
    · rw [h]
      exact degreeTwo D hd short
    · rw [h]
      exact degreeThree D hd short
  obtain ⟨x,bad⟩ := counter
  obtain ⟨ports,edges⟩ := projection i h0 h6 x
  apply bad
  exact (eq (env (typ i) x) (zero i x) rfl).trans
    ((congrArg (circuitFun 10 C) ports).trans ((good (lift i x)).trans edges))
