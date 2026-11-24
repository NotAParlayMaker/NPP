import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4614_1
    (hfinite :
      ∀ (K : List ℕ) (q : ℕ),
        (∀ a ∈ K, ∀ b : ℕ, 58 ≤ b → a.testBit b = false) →
        (∃ j : Fin 58, 21 ≤ j.val ∧ q.testBit j.val = true) →
        (∀ i : Fin 58, ∃ j : Fin 58,
          q.testBit j.val = true ∧ (2097151 : ℕ).testBit j.val = (2097151 : ℕ).testBit i.val ∧
          ∀ a ∈ K, if (2097151 : ℕ).testBit i.val = true then a.testBit j.val = true → a.testBit i.val = true
                   else a.testBit i.val = true → a.testBit j.val = true) →
        ∀ i : ℕ, ∃ j : ℕ,
          q.testBit j = true ∧ (2097151 : ℕ).testBit j = (2097151 : ℕ).testBit i ∧
          ∀ a ∈ K, if (2097151 : ℕ).testBit i = true then a.testBit j = true → a.testBit i = true
                   else a.testBit i = true → a.testBit j = true)
    (hsearch :
      let legal : List ℕ → List ℕ → Prop := fun s l =>
        ∀ i : Fin l.length, ∃ a ∈ s ++ l.take i.val, ∃ b ∈ s ++ l.take i.val,
          l.get i = a &&& b ∨ l.get i = a ||| b
      let A : List ℕ :=
        [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
         8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
         155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
         270286071508633728, 288160007407550752]
      ∃ (F K : List ℕ) (q : ℕ) (U : List ℕ),
        F.length ≤ 14 ∧ K.length ≤ 13 ∧ U.length ≤ 12 ∧
        legal A F ∧ (∀ k ∈ K, k ∈ A ++ F) ∧
        (∃ j : Fin 58, 21 ≤ j.val ∧ q.testBit j.val = true) ∧
        (∀ i : Fin 58, ∃ j : Fin 58,
          q.testBit j.val = true ∧ (2097151 : ℕ).testBit j.val = (2097151 : ℕ).testBit i.val ∧
          ∀ a ∈ K, if (2097151 : ℕ).testBit i.val = true then a.testBit j.val = true → a.testBit i.val = true
                   else a.testBit i.val = true → a.testBit j.val = true) ∧
        legal (K.map fun a => a &&& q) U ∧
        (2097151 : ℕ) &&& q ∈ (K.map fun a => a &&& q) ++ U) :
    have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; have x2 : List ℕ → ℕ → ℕ → Prop := fun (x2 : List ℕ) (x3 x4 : ℕ) => ∀ (x5 : ℕ), ∃ (x6 : ℕ), x3.testBit x6 = Bool.true ∧ x4.testBit x6 = x4.testBit x5 ∧ ∀ x7 ∈ x2, if x4.testBit x5 = Bool.true then x7.testBit x6 = Bool.true → x7.testBit x5 = Bool.true else x7.testBit x5 = Bool.true → x7.testBit x6 = Bool.true; have x3 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x4 : List ℕ) (x5 : List ℕ) (x6 : ℕ) (x7 : List ℕ), x4.length ≤ (14 : ℕ) ∧ x5.length ≤ (13 : ℕ) ∧ x7.length ≤ (12 : ℕ) ∧ x1 x3 x4 ∧ (∀ x8 ∈ x5, x8 ∈ x3 ++ x4) ∧ x2 x5 x6 (2097151 : ℕ) ∧ x1 (List.map (fun (x8 : ℕ) => x8 &&& x6) x5) x7 ∧ (2097151 : ℕ) &&& x6 ∈ List.map (fun (x8 : ℕ) => x8 &&& x6) x5 ++ x7 := by
  dsimp only at hsearch ⊢
  obtain ⟨F, K, q, U, hF, hK, hU, hlegF, hsub, hhi, hcov58, hlegU, hmem⟩ := hsearch
  let A : List ℕ :=
    [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
     8521481482240, 14003410187812864, 55389823207997440, 189297016294081033,
     155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984,
     270286071508633728, 288160007407550752]
  have hltA : ∀ w ∈ A, w < 2 ^ 58 := by decide
  have hbitA (w : ℕ) (hw : w ∈ A) (b : ℕ) (hb : 58 ≤ b) : w.testBit b = false :=
    Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (hltA w hw) (Nat.pow_le_pow_right (by decide) hb))
  have hbitF (b : ℕ) (hb : 58 ≤ b) : ∀ (i : ℕ) (hi : i < F.length), (F[i]'hi).testBit b = false := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro hi
      obtain ⟨a, ha, c, hc, hop⟩ := hlegF ⟨i, hi⟩
      have getZero (w : ℕ) (hw : w ∈ A ++ F.take i) : w.testBit b = false := by
        rcases List.mem_append.mp hw with hA | hT
        · exact hbitA w hA b hb
        · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hT
          have hjlen : j < i := by
            have : (F.take i).length ≤ i := List.length_take_le i F
            omega
          rw [List.getElem_take]
          exact ih j hjlen (by omega)
      have ha0 := getZero a ha
      have hc0 := getZero c hc
      have hget : F.get ⟨i, hi⟩ = F[i]'hi := rfl
      rw [hget] at hop
      rcases hop with h | h
      · rw [h, Nat.testBit_and, ha0, hc0]; rfl
      · rw [h, Nat.testBit_or, ha0, hc0]; rfl
  have hbitK (a : ℕ) (ha : a ∈ K) (b : ℕ) (hb : 58 ≤ b) : a.testBit b = false := by
    rcases List.mem_append.mp (hsub a ha) with hA | hFm
    · exact hbitA a hA b hb
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hFm
      exact hbitF b hb i hi
  exact ⟨F, K, q, U, hF, hK, hU, hlegF, hsub, hfinite K q hbitK hhi hcov58, hlegU, hmem⟩
