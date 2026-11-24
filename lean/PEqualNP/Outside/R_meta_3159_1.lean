import Mathlib
import PEqualNP.Defs

-- Cut of L-meta-3159. The complemented-output case is proved here: with the output negated the
-- set x6 is forced to be the singleton of the output wire, so no gate reads a complemented wire
-- outside the two free wires 0 and 9, so every wire is monotone in x_1 .. x_8 once x_0 is fixed,
-- while the negated edge function is not. h1 is the shape with no gate output read complemented,
-- h2 the shape with exactly one.
theorem PEqualNP.Outside.R_meta_3159_1
    (h1 : ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool), (0 : ℕ) < x1 → x6.card ≤ (3 : ℕ) → x1 + x6.card ≤ (14 : ℕ) → x6.card ≤ (1 : ℕ) → (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) → (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) → (∀ (x14 : ℕ), x14 ∈ x6 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (x5 = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) → (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x7 x15 ↑x16 = x15 x16) → (∀ (x16 : Fin (9 : ℕ) → Bool), x7 x16 (9 : ℕ) = Bool.false) → (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1), have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x7 x17 x19.1 ^^ x19.2; x7 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) → x5 = Bool.false ∧ x6.card = (0 : ℕ) → ∃ (x18 : Fin (9 : ℕ) → Bool), (x7 x18 ((9 : ℕ) + x1) ^^ x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ))))
    (h2 : ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool), (0 : ℕ) < x1 → x6.card ≤ (3 : ℕ) → x1 + x6.card ≤ (14 : ℕ) → x6.card ≤ (1 : ℕ) → (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) → (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) → (∀ (x14 : ℕ), x14 ∈ x6 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (x5 = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) → (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x7 x15 ↑x16 = x15 x16) → (∀ (x16 : Fin (9 : ℕ) → Bool), x7 x16 (9 : ℕ) = Bool.false) → (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1), have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x7 x17 x19.1 ^^ x19.2; x7 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) → x5 = Bool.false ∧ x6.card = (1 : ℕ) → ∃ (x18 : Fin (9 : ℕ) → Bool), (x7 x18 ((9 : ℕ) + x1) ^^ x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ)))) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool), (0 : ℕ) < x1 → x6.card ≤ (3 : ℕ) → x1 + x6.card ≤ (14 : ℕ) → x6.card ≤ (1 : ℕ) → (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) → (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) → (∀ (x14 : ℕ), x14 ∈ x6 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (x5 = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) → (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x7 x15 ↑x16 = x15 x16) → (∀ (x16 : Fin (9 : ℕ) → Bool), x7 x16 (9 : ℕ) = Bool.false) → (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1), have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x7 x17 x19.1 ^^ x19.2; x7 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) → ∃ (x18 : Fin (9 : ℕ) → Bool), (x7 x18 ((9 : ℕ) + x1) ^^ x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ))) := by
  intro n op a b pol S val hn hcard3 hsum hcard1 hff hcov hmem hinp hconst hgate
  by_cases hp : pol = Bool.true
  · -- The output literal is complemented. Then the output wire itself lies in x6, so x6 is exactly
    -- that singleton, so no gate reads a complemented wire outside the two free wires 0 and 9, so
    -- every wire is monotone in x_1 .. x_8 once x_0 is fixed, while the negated edge function is
    -- not.
    subst hp
    have hout : (9 : ℕ) + n ∈ S := by
      rw [hmem]
      exact ⟨by omega, by omega, Or.inl ⟨rfl, rfl⟩⟩
    have huniq : ∀ y ∈ S, y = (9 : ℕ) + n :=
      fun y hy => ((Finset.card_le_one.mp hcard1) ((9 : ℕ) + n) hout y hy).symm
    have hneg : ∀ (i : Fin n) (w : ℕ), (a i = (w, Bool.true) ∨ b i = (w, Bool.true)) →
        w = (0 : ℕ) ∨ w = (9 : ℕ) := by
      intro i w hw
      by_contra! hne
      have hw' : w ∈ S := (hmem w).mpr ⟨hne.1, hne.2, Or.inr ⟨i, hw⟩⟩
      have hlt : w < (10 : ℕ) + (i : ℕ) := by
        rcases hw with ha | hb
        · have hfw : (a i).1 = w := by rw [ha]
          rw [← hfw]
          exact (hff i).1
        · have hfw : (b i).1 = w := by rw [hb]
          rw [← hfw]
          exact (hff i).2
      have hge : w = (9 : ℕ) + n := huniq w hw'
      omega
    have heq09 : ∀ (w : ℕ), (w = (0 : ℕ) ∨ w = (9 : ℕ)) → ∀ (x y : Fin (9 : ℕ) → Bool),
        x (0 : Fin (9 : ℕ)) = y (0 : Fin (9 : ℕ)) → val x w = val y w := by
      intro w hw x y hx0
      rcases hw with rfl | rfl
      · have ex : val x ↑(0 : Fin (9 : ℕ)) = x (0 : Fin (9 : ℕ)) := hinp x (0 : Fin (9 : ℕ))
        have ey : val y ↑(0 : Fin (9 : ℕ)) = y (0 : Fin (9 : ℕ)) := hinp y (0 : Fin (9 : ℕ))
        show val x ↑(0 : Fin (9 : ℕ)) = val y ↑(0 : Fin (9 : ℕ))
        rw [ex, ey]
        exact hx0
      · rw [hconst x, hconst y]
    have mono : ∀ (t : ℕ), t < (10 : ℕ) + n → ∀ (x y : Fin (9 : ℕ) → Bool),
        x (0 : Fin (9 : ℕ)) = y (0 : Fin (9 : ℕ)) →
        (∀ (i : Fin (9 : ℕ)), i ≠ (0 : Fin (9 : ℕ)) → x i = Bool.true → y i = Bool.true) →
        val x t = Bool.true → val y t = Bool.true := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        intro ht x y hx0 hlink hval
        rcases Nat.lt_or_ge t (9 : ℕ) with h9 | h9
        · have key : x ⟨t, h9⟩ = Bool.true := by
            have hv : val x ↑(⟨t, h9⟩ : Fin (9 : ℕ)) = Bool.true := hval
            rw [hinp x ⟨t, h9⟩] at hv
            exact hv
          have tgt : y ⟨t, h9⟩ = Bool.true := by
            rcases Nat.eq_zero_or_pos t with rfl | ht0
            · have he : (⟨0, h9⟩ : Fin (9 : ℕ)) = (0 : Fin (9 : ℕ)) := by
                apply Fin.ext
                rfl
              rw [he, ← hx0, ← he]
              exact key
            · refine hlink ⟨t, h9⟩ (fun hh => Nat.ne_of_gt ht0 (congrArg Fin.val hh)) key
          show val y ↑(⟨t, h9⟩ : Fin (9 : ℕ)) = Bool.true
          rw [hinp y ⟨t, h9⟩]
          exact tgt
        · by_cases h9e : t = (9 : ℕ)
          · subst h9e
            rw [hconst x] at hval
            exact absurd hval (by decide)
          · obtain ⟨i, rfl⟩ : ∃ (i : Fin n), t = (10 : ℕ) + (i : ℕ) := by
              exact ⟨⟨t - (10 : ℕ), by omega⟩, by show t = (10 : ℕ) + (t - (10 : ℕ)); omega⟩
            have hlt1 : (a i).1 < (10 : ℕ) + n := by
              have ha0 : (a i).1 < (10 : ℕ) + (i : ℕ) := (hff i).1
              have hi : (i : ℕ) < n := i.isLt
              omega
            have hlt2 : (b i).1 < (10 : ℕ) + n := by
              have hb0 : (b i).1 < (10 : ℕ) + (i : ℕ) := (hff i).2
              have hi : (i : ℕ) < n := i.isLt
              omega
            have hax : val x (a i).1 = Bool.true → val y (a i).1 = Bool.true :=
              fun hxv => ih ((a i).1) ((hff i).1) hlt1 x y hx0 hlink hxv
            have hbx : val x (b i).1 = Bool.true → val y (b i).1 = Bool.true :=
              fun hxv => ih ((b i).1) ((hff i).2) hlt2 x y hx0 hlink hxv
            have pa : (val x (a i).1 ^^ (a i).2) = Bool.true →
                (val y (a i).1 ^^ (a i).2) = Bool.true := by
              intro h
              cases hc : (a i).2 with
              | true =>
                have hzw : (a i).1 = (0 : ℕ) ∨ (a i).1 = (9 : ℕ) :=
                  hneg i ((a i).1) (Or.inl (Prod.ext rfl hc))
                rw [← heq09 ((a i).1) hzw x y hx0]
                rw [hc] at h
                exact h
              | false =>
                rw [hc] at h
                rw [Bool.xor_false] at h
                rw [hax h]
                decide
            have pb : (val x (b i).1 ^^ (b i).2) = Bool.true →
                (val y (b i).1 ^^ (b i).2) = Bool.true := by
              intro h
              cases hc : (b i).2 with
              | true =>
                have hzw : (b i).1 = (0 : ℕ) ∨ (b i).1 = (9 : ℕ) :=
                  hneg i ((b i).1) (Or.inr (Prod.ext rfl hc))
                rw [← heq09 ((b i).1) hzw x y hx0]
                rw [hc] at h
                exact h
              | false =>
                rw [hc] at h
                rw [Bool.xor_false] at h
                rw [hbx h]
                decide
            rw [hgate x i] at hval
            rw [hgate y i]
            cases hq : op i with
            | false =>
              rw [hq] at hval
              have hv2 :
                  ((val x (a i).1 ^^ (a i).2) || (val x (b i).1 ^^ (b i).2)) = Bool.true := hval
              show ((val y (a i).1 ^^ (a i).2) || (val y (b i).1 ^^ (b i).2)) = Bool.true
              rw [Bool.or_eq_true] at hv2
              rcases hv2 with h | h
              · rw [Bool.or_eq_true]
                exact Or.inl (pa h)
              · rw [Bool.or_eq_true]
                exact Or.inr (pb h)
            | true =>
              rw [hq] at hval
              have hv2 :
                  ((val x (a i).1 ^^ (a i).2) && (val x (b i).1 ^^ (b i).2)) = Bool.true := hval
              show ((val y (a i).1 ^^ (a i).2) && (val y (b i).1 ^^ (b i).2)) = Bool.true
              rw [Bool.and_eq_true] at hv2
              rcases hv2 with ⟨h1', h2'⟩
              rw [Bool.and_eq_true]
              exact ⟨pa h1', pb h2'⟩
    set u : Fin (9 : ℕ) → Bool := fun _ => Bool.false
    set v : Fin (9 : ℕ) → Bool :=
      fun i => if i = (1 : Fin (9 : ℕ)) ∨ i = (2 : Fin (9 : ℕ)) then Bool.true else Bool.false
    have h0 : u (0 : Fin (9 : ℕ)) = v (0 : Fin (9 : ℕ)) := rfl
    have hlinkuv : ∀ (i : Fin (9 : ℕ)), i ≠ (0 : Fin (9 : ℕ)) →
        u i = Bool.true → v i = Bool.true := by
      intro i _ hi
      have hu : u i = Bool.false := rfl
      rw [hu] at hi
      exact absurd hi (by decide)
    have hfu : (fun (x18 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ)))) u = Bool.false := by decide
    have hfv : (fun (x18 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ)))) v = Bool.true := by decide
    by_contra! hcomp
    have hcu : (val u ((9 : ℕ) + n) ^^ Bool.true) =
        (fun (x18 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ)))) u := hcomp u
    rw [hfu] at hcu
    rw [Bool.xor_true] at hcu
    have hu1 : val u ((9 : ℕ) + n) = Bool.true := by simpa using hcu
    have hv : val v ((9 : ℕ) + n) = Bool.true :=
      mono ((9 : ℕ) + n) (by omega) u v h0 hlinkuv hu1
    have hcv : (val v ((9 : ℕ) + n) ^^ Bool.true) =
        (fun (x18 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ)))) v := hcomp v
    rw [hfv, hv] at hcv
    exact absurd hcv (by decide)
  · -- The output literal is not complemented: the two remaining shapes are h1 and h2.
    have hp' : pol = Bool.false := by
      cases pol with
      | false => rfl
      | true => exact absurd rfl hp
    have hcard : S.card = (0 : ℕ) ∨ S.card = (1 : ℕ) := by
      have hle : S.card ≤ (1 : ℕ) := hcard1
      omega
    rcases hcard with hz | ho
    · exact h1 n op a b pol S val hn hcard3 hsum hcard1 hff hcov hmem hinp hconst hgate ⟨hp', hz⟩
    · exact h2 n op a b pol S val hn hcard3 hsum hcard1 hff hcov hmem hinp hconst hgate ⟨hp', ho⟩

