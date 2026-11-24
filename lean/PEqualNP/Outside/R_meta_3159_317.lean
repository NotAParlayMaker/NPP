import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3159_317
    (input_literal :
      ∀ (n : ℕ) (ops : Fin n → Bool) (a b : Fin n → ℕ × Bool)
        (r : Fin 9) (V : (Fin 9 → Bool) → ℕ → Bool),
        0 < n → n ≤ 14 → (r ≠ 0 → n ≤ 13) →
        (∀ i, (a i).1 < 10 + i.val ∧ (b i).1 < 10 + i.val) →
        (∀ j : Fin 9, ∃ i, (a i).1 = j.val ∨ (b i).1 = j.val) →
        (∀ i w, w = a i ∨ w = b i →
          w.2 = true → w.1 = 0 ∨ w.1 = 9 ∨ w.1 = r.val) →
        (∀ (x : Fin 9 → Bool) (j : Fin 9), V x j.val = x j) →
        (∀ x, V x 9 = false) →
        (∀ x i, let read := fun w : ℕ × Bool => V x w.1 ^^ w.2
          V x (10 + i.val) =
            if ops i then read (a i) && read (b i) else read (a i) || read (b i)) →
        ∃ x, V x (9 + n) ≠
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
            (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (gate_literal :
      ∀ (n : ℕ) (ops : Fin n → Bool) (a b : Fin n → ℕ × Bool)
        (p : Fin n) (V : (Fin 9 → Bool) → ℕ → Bool),
        0 < n → n ≤ 13 →
        (∀ i, (a i).1 < 10 + i.val ∧ (b i).1 < 10 + i.val) →
        (∀ j : Fin 9, ∃ i, (a i).1 = j.val ∨ (b i).1 = j.val) →
        (∀ i w, w = a i ∨ w = b i →
          w.2 = true → w.1 = 0 ∨ w.1 = 9 ∨ w.1 = 10 + p.val) →
        (∀ (x : Fin 9 → Bool) (j : Fin 9), V x j.val = x j) →
        (∀ x, V x 9 = false) →
        (∀ x i, let read := fun w : ℕ × Bool => V x w.1 ^^ w.2
          V x (10 + i.val) =
            if ops i then read (a i) && read (b i) else read (a i) || read (b i)) →
        ∃ x, V x (9 + n) ≠
          ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
            (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (0 : ℕ) < x1 →     x6.card ≤ (3 : ℕ) →       x1 + x6.card ≤ (14 : ℕ) →         x6.card ≤ (1 : ℕ) →           (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) →             (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) →               (∀ (x14 : ℕ), x14 ∈ x6 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (x5 = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x7 x15 ↑x16 = x15 x16) →                   (∀ (x16 : Fin (9 : ℕ) → Bool), x7 x16 (9 : ℕ) = Bool.false) →                     (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1),                         have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x7 x17 x19.1 ^^ x19.2;                         x7 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) →                       ∃ (x18 : Fin (9 : ℕ) → Bool), (x7 x18 ((9 : ℕ) + x1) ^^ x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ))) := by
  intro n ops a b inverted S V hn _ hbudget hcard hback hread hS hV hzero hstep
  have neg_mem (i : Fin n) (w : ℕ × Bool) (hw : w = a i ∨ w = b i)
      (hs : w.2 = true) (h0 : w.1 ≠ 0) (h9 : w.1 ≠ 9) : w.1 ∈ S := by
    apply (hS w.1).mpr
    refine ⟨h0, h9, Or.inr ⟨i, ?_⟩⟩
    have hw' : w = (w.1, true) := Prod.ext rfl hs
    rcases hw with h | h
    · exact Or.inl (h.symm.trans hw')
    · exact Or.inr (h.symm.trans hw')
  have allowed_empty (hempty : S = ∅) (i : Fin n) (w : ℕ × Bool)
      (hw : w = a i ∨ w = b i) (hs : w.2 = true) : w.1 = 0 ∨ w.1 = 9 := by
    by_contra! h
    simpa [hempty] using neg_mem i w hw hs h.1 h.2
  have allowed_single (k : ℕ) (hk : k ∈ S) (i : Fin n) (w : ℕ × Bool)
      (hw : w = a i ∨ w = b i) (hs : w.2 = true) : w.1 = 0 ∨ w.1 = 9 ∨ w.1 = k := by
    by_cases h0 : w.1 = 0
    · exact Or.inl h0
    by_cases h9 : w.1 = 9
    · exact Or.inr (Or.inl h9)
    exact Or.inr (Or.inr ((Finset.card_le_one.mp hcard) _ (neg_mem i w hw hs h0 h9) _ hk))
  cases inverted with
  | false =>
    have h14 : n ≤ 14 := by omega
    by_cases hempty : S = ∅
    · obtain ⟨x, hx⟩ := input_literal n ops a b 0 V hn h14
        (by simp) hback hread
        (fun i w hw hs => (allowed_empty hempty i w hw hs).imp_right Or.inl)
        hV hzero hstep
      exact ⟨x, by simpa using hx⟩
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨k, hk⟩
    have h13 : n ≤ 13 := by omega
    have hsource := (hS k).mp hk
    by_cases hsmall : k < 9
    · let r : Fin 9 := ⟨k, hsmall⟩
      obtain ⟨x, hx⟩ := input_literal n ops a b r V hn h14 (fun _ => h13) hback hread
        (allowed_single k hk) hV hzero hstep
      exact ⟨x, by simpa using hx⟩
    have hlarge : 10 ≤ k := by have := hsource.2.1; omega
    have hused : ∃ i, a i = (k, true) ∨ b i = (k, true) := by
      simpa using hsource.2.2
    obtain ⟨i, hi⟩ := hused
    have hlt : k < 10 + n := by
      have hb := hback i
      have hi' := i.isLt
      rcases hi with h | h
      · rw [h] at hb
        exact lt_trans hb.1 (by omega)
      · rw [h] at hb
        exact lt_trans hb.2 (by omega)
    let p : Fin n := ⟨k - 10, by omega⟩
    have hp : 10 + p.val = k := by dsimp [p]; omega
    obtain ⟨x, hx⟩ := gate_literal n ops a b p V hn h13 hback hread
      (by rw [hp]; exact allowed_single k hk) hV hzero hstep
    exact ⟨x, by simpa using hx⟩
  | true =>
    let lo : Fin 9 → Bool := fun _ => false
    let hi : Fin 9 → Bool := fun i => decide (i = 1 ∨ i = 2)
    have hlast : 9 + n ∈ S := (hS (9 + n)).mpr
      ⟨by omega, by omega, Or.inl ⟨rfl, rfl⟩⟩
    have hfree (i : Fin n) (w : ℕ × Bool) (hw : w = a i ∨ w = b i)
        (hs : w.2 = true) : w.1 = 0 ∨ w.1 = 9 := by
      have hlt : w.1 < 9 + n := by
        have hb := hback i
        have hi' := i.isLt
        rcases hw with h | h
        · rw [h]; omega
        · rw [h]; omega
      rcases allowed_single _ hlast i w hw hs with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · omega
    have hfixed (w : ℕ) (hw : w = 0 ∨ w = 9) : V lo w = V hi w := by
      rcases hw with rfl | rfl
      · change V lo (0 : Fin 9).val = V hi (0 : Fin 9).val
        rw [hV lo 0, hV hi 0]
        decide
      · rw [hzero lo, hzero hi]
    have hmono : ∀ j ≤ 9 + n, V lo j = true → V hi j = true := by
      intro j
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        intro hj
        by_cases hinput : j < 9
        · let v : Fin 9 := ⟨j, hinput⟩
          change V lo v.val = true → V hi v.val = true
          rw [hV lo v, hV hi v]
          simp [lo]
        by_cases hconstant : j = 9
        · subst j
          simp [hzero]
        have hgate : 10 ≤ j := by omega
        let i : Fin n := ⟨j - 10, by omega⟩
        have hiIndex : 10 + i.val = j := by dsimp [i]; omega
        have hoperand (w : ℕ × Bool) (hw : w = a i ∨ w = b i)
            (hlt : w.1 < j) :
            (V lo w.1 ^^ w.2) = true → (V hi w.1 ^^ w.2) = true := by
          cases hs : w.2
          · simpa [hs] using ih w.1 hlt (by omega)
          · rw [hfixed _ (hfree i w hw hs)]
            exact id
        have hb := hback i
        rw [hiIndex] at hb
        have ha' := hoperand (a i) (Or.inl rfl) hb.1
        have hb' := hoperand (b i) (Or.inr rfl) hb.2
        rw [← hiIndex, hstep lo i, hstep hi i]
        by_cases hop : ops i = true
        · simp only [hop]
          intro h
          obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
          exact Bool.and_eq_true_iff.mpr ⟨ha' ha, hb' hb⟩
        · simp only [hop]
          intro h
          rcases Bool.or_eq_true_iff.mp h with ha | hb
          · exact Bool.or_eq_true_iff.mpr (Or.inl (ha' ha))
          · exact Bool.or_eq_true_iff.mpr (Or.inr (hb' hb))
    by_cases h : V lo (9 + n) = true
    · refine ⟨hi, ?_⟩
      rw [hmono _ (le_refl _) h]
      decide
    · refine ⟨lo, ?_⟩
      have hl : V lo (9 + n) = false := Bool.eq_false_of_not_eq_true h
      rw [hl]
      decide
