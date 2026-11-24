import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_3535_421
    (lift :
      let step := fun (A : List ℕ) (x : ℕ) =>
      ∃ a ∈ A, ∃ b ∈ A, x = a &&& b ∨ x = a ||| b
    let valid := fun (A S : List ℕ) =>
      ∀ i : Fin S.length, step (A ++ S.take i.val) (S.get i)
    ∀ (R : ℕ → ℕ → Prop) (A B S : List ℕ),
      (∀ u ∈ B, ∃ a ∈ A, R a u) →
      (∀ {a b u v : ℕ}, R a u → R b v → R (a &&& b) (u &&& v)) →
      (∀ {a b u v : ℕ}, R a u → R b v → R (a ||| b) (u ||| v)) →
      valid B S →
      ∃ T : List ℕ, T.length = S.length ∧ valid A T ∧
        ∀ u ∈ B ++ S, ∃ a ∈ A ++ T, R a u)
    (compressed :
      let B : List ℕ := [917681471495, 14877982776, 31886295695808, 257731333632, 42884715540480, 82789891276800, 248671168364609, 198670308900872, 158476001153026, 238332533547520, 176488259388544, 212188564308240, 280375465084964, 271282175770697, 280357743665737, 0]
      let step := fun (W : List ℕ) (z : ℕ) =>
        ∃ a ∈ W, ∃ b ∈ W, z = a &&& b ∨ z = a ||| b
      ∃ S : List ℕ, S.length ≤ 22 ∧ 262143 ∈ B ++ S ∧
        ∀ i : Fin S.length, step (B ++ S.take i.val) (S.get i)) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)] ++ [(191866593364673099 : ℕ), (193001360500003407 : ℕ), (7 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (22 : ℕ) ∧ (∃ x3 ∈ x1 ++ x2, x3 ||| (7 : ℕ) = (2097151 : ℕ)) ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5 := by
  let A : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)] ++ [(191866593364673099 : ℕ), (193001360500003407 : ℕ), (7 : ℕ)]
  let B : List ℕ := [917681471495, 14877982776, 31886295695808, 257731333632, 42884715540480, 82789891276800, 248671168364609, 198670308900872, 158476001153026, 238332533547520, 176488259388544, 212188564308240, 280375465084964, 271282175770697, 280357743665737, 0]
  let keep (i : Fin 48) : Nat :=
    ([3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37, 38, 39, 40, 42, 43, 45, 46, 47, 48, 50, 51, 53, 55, 57] : List Nat).getD i.val 0
  let omitted (i : Fin 7) : Nat :=
    ([35, 41, 44, 49, 52, 54, 56] : List Nat).getD i.val 0
  let dominant (i : Fin 7) : Nat :=
    ([37, 42, 45, 51, 53, 55, 57] : List Nat).getD i.val 0
  let rep (i : Fin 58) : Fin 48 :=
    Fin.ofNat 48 (([0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 32, 33, 34, 35, 36, 37, 37, 38, 39, 39, 40, 41, 42, 44, 43, 44, 45, 45, 46, 46, 47, 47] : List Nat).getD i.val 0)
  let drop (i : Fin 58) : Fin 7 :=
    Fin.ofNat 7 (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 3, 0, 0, 4, 0, 5, 0, 6, 0] : List Nat).getD i.val 0)
  let rel (a u : Nat) : Prop :=
    (∀ i : Fin 48, a.testBit (keep i) = u.testBit i.val) ∧
    (∀ i : Fin 7, a.testBit (omitted i) = true → a.testBit (dominant i) = true) ∧
    a < 2 ^ 58
  have seeds : ∀ i : Fin 16, A.getD (i.val + 1) 0 ∈ A ∧
      rel (A.getD (i.val + 1) 0) (B.getD i.val 0) := by
    dsimp only [A, B, rel, keep, omitted, dominant]
    decide +kernel
  have liftSeeds : ∀ u ∈ B, ∃ a ∈ A, rel a u := by
    intro u hu
    obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hu
    have hn' : n < 16 := by simpa [B] using hn
    let i : Fin 16 := ⟨n, hn'⟩
    have hs := seeds i
    have hu' : B.getD i.val 0 = u :=
      (List.getD_eq_getElem _ _ hn).trans hget
    exact ⟨A.getD (i.val + 1) 0, hs.1, hu' ▸ hs.2⟩
  have andRel : ∀ {a b u v}, rel a u → rel b v → rel (a &&& b) (u &&& v) := by
    intro a b u v ha hb
    refine ⟨?_, ?_, Nat.and_lt_two_pow _ hb.2.2⟩
    · intro i
      simp only [Nat.testBit_and, ha.1 i, hb.1 i]
    · intro i h
      simp only [Nat.testBit_and, Bool.and_eq_true] at h ⊢
      exact ⟨ha.2.1 i h.1, hb.2.1 i h.2⟩
  have orRel : ∀ {a b u v}, rel a u → rel b v → rel (a ||| b) (u ||| v) := by
    intro a b u v ha hb
    refine ⟨?_, ?_, Nat.or_lt_two_pow ha.2.2 hb.2.2⟩
    · intro i
      simp only [Nat.testBit_or, ha.1 i, hb.1 i]
    · intro i h
      simp only [Nat.testBit_or, Bool.or_eq_true] at h ⊢
      exact h.elim (fun h => Or.inl (ha.2.1 i h)) (fun h => Or.inr (hb.2.1 i h))
  have coverage : ∀ i : Fin 58,
      ((7 : Nat).testBit i.val = true ∧ (2097151 : Nat).testBit i.val = true) ∨
      (keep (rep i) = i.val ∧
        ((7 : Nat).testBit i.val || (262143 : Nat).testBit (rep i).val) =
          (2097151 : Nat).testBit i.val) ∨
      (omitted (drop i) = i.val ∧ dominant (drop i) = keep (rep i) ∧
        (262143 : Nat).testBit (rep i).val = false ∧
        (7 : Nat).testBit i.val = (2097151 : Nat).testBit i.val) := by
    dsimp only [keep, rep, drop, omitted, dominant]
    decide +kernel
  have finish : ∀ a, rel a 262143 → a ||| 7 = 2097151 := by
    intro a ha
    apply Nat.eq_of_testBit_eq
    intro n
    by_cases hn : n < 58
    · let i : Fin 58 := ⟨n, hn⟩
      change (a ||| 7).testBit i.val = (2097151 : Nat).testBit i.val
      rcases coverage i with supplied | retained | dominated
      · simp only [Nat.testBit_or, supplied.1, Bool.or_true, supplied.2]
      · have hr := ha.1 (rep i)
        rw [retained.1] at hr
        rw [Nat.testBit_or, hr, Bool.or_comm]
        exact retained.2
      · have hd := ha.2.1 (drop i)
        rw [dominated.1, dominated.2.1] at hd
        have hf : a.testBit i.val = false := by
          cases hb : a.testBit i.val
          · rfl
          · have hr := hd hb
            rw [ha.1 (rep i), dominated.2.2.1] at hr
            contradiction
        simpa only [Nat.testBit_or, hf, Bool.false_or] using dominated.2.2.2
    · have hp : 2 ^ 58 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have a0 : a.testBit n = false := Nat.testBit_eq_false_of_lt (ha.2.2.trans_le hp)
      have b0 : (7 : Nat).testBit n = false :=
        Nat.testBit_eq_false_of_lt ((by decide : 7 < 2 ^ 58).trans_le hp)
      have t0 : (2097151 : Nat).testBit n = false :=
        Nat.testBit_eq_false_of_lt ((by decide : 2097151 < 2 ^ 58).trans_le hp)
      simp only [Nat.testBit_or, a0, b0, t0, Bool.false_or]
  obtain ⟨S, hSmall, hTarget, hSteps⟩ := compressed
  obtain ⟨T, hLength, valid, seen⟩ := lift rel A B S liftSeeds andRel orRel hSteps
  obtain ⟨a, hA, hR⟩ := seen 262143 hTarget
  exact ⟨T, hLength.trans_le hSmall, ⟨a, hA, finish a hR⟩, valid⟩

