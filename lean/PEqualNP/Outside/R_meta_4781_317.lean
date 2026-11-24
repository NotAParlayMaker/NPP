import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_4781_317
    (compileMasks : (∀ (m : ℕ) (A : List ℕ) (C : Circuit), Monotone2 C →
      ∃ (B : List ℕ) (v : ℕ), B.length = C.size ∧ v ∈ [0, 2^m-1] ++ A ++ B ∧
      (∀ i : Fin B.length,
        ∃ a ∈ [0, 2^m-1] ++ A ++ B.take i.val, ∃ b ∈ [0, 2^m-1] ++ A ++ B.take i.val,
          B.get i = a &&& b ∨ B.get i = a ||| b) ∧
      ∀ j : Fin m, v.testBit j.val = C.eval (A.map fun x => x.testBit j.val)))
    (excludeTable : (let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      ∀ (B : List ℕ), B.length ≤ 24 →
        (∀ i : Fin B.length,
        ∃ a ∈ [0, 288230376151711743] ++ A ++ B.take i.val, ∃ b ∈ [0, 288230376151711743] ++ A ++ B.take i.val,
          B.get i = a &&& b ∨ B.get i = a ||| b) →
        ∀ v ∈ [0, 288230376151711743] ++ A ++ B,
          ¬ (∀ j : Fin 58, v.testBit j.val = (2097150 : ℕ).testBit j.val))) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Fin (14 : ℕ) → Bool), (∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)), (↑x5, ↑x6) ∈ x1 ∧ (x5 ≠ (0 : Fin (14 : ℕ)) ∨ x6 ≠ (7 : Fin (14 : ℕ))) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → x2.eval (List.ofFn x4) = Bool.true) → (∀ (x5 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true → ∃ (x7 : Fin (14 : ℕ)) (x8 : Fin (14 : ℕ)), (↑x7, ↑x8) ∈ x1 ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true) → x2.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = (0 : Fin (14 : ℕ)) ∨ x6 = (7 : Fin (14 : ℕ)))) = Bool.false → (25 : ℕ) ≤ x2.size := by
  intro E C hmono hcomplete hsound hreject
  let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let X (j : Fin 58) (i : Fin 14) := (A.getD i.val 0).testBit j.val
  have represented : ∀ j : Fin 58, A.map (fun b => b.testBit j.val) = List.ofFn (X j) := by
    dsimp only [A, X]
    decide +kernel
  have rzero : X 0 = fun i => decide (i = (0 : Fin 14) ∨ i = (7 : Fin 14)) := by
    funext i
    revert i
    dsimp only [A, X]
    decide +kernel
  have rows : ∀ j : Fin 58,
      (0 < j.val ∧ j.val < 21 →
        ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ (u ≠ 0 ∨ v ≠ 7) ∧ X j u = true ∧ X j v = true) ∧
      (21 ≤ j.val → ¬ ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ X j u = true ∧ X j v = true) := by
    dsimp only [A, E, X]
    decide +kernel
  have targetBits : ∀ j : Fin 58, (2097150 : ℕ).testBit j.val = decide (0 < j.val ∧ j.val < 21) := by
    decide +kernel
  obtain ⟨B, v, hlen, hmem, hlegal, hval⟩ := compileMasks 58 A C hmono
  by_contra hsize
  have small : B.length ≤ 24 := by omega
  apply excludeTable B small hlegal v hmem
  intro j
  rw [hval, represented, targetBits]
  by_cases hz : j = 0
  · subst j
    rw [rzero, hreject]
    rfl
  by_cases hj : j.val < 21
  · have h : 0 < j.val ∧ j.val < 21 := ⟨by have := Fin.val_ne_of_ne hz; omega, hj⟩
    rw [hcomplete _ ((rows j).1 h), decide_eq_true h]
  · have no := (rows j).2 (Nat.le_of_not_gt hj)
    cases h : C.eval (List.ofFn (X j)) with
    | false => simp [hj]
    | true => exact False.elim (no (hsound _ h))
