import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3364_720
    (stars : ∀ (q N s : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      N ≤ s → N * (q + 1) ≤ 100 * s →
      ∃ (P L : Fin s → Finset (Fin N)),
        (∀ i p, p ∈ P i → ∀ l, l ∈ L i → I p l) ∧
        (∀ p l, I p l → ∃ i, p ∈ P i ∧ l ∈ L i) ∧
        ∑ i, ((P i).card + (L i).card) ≤ 100 * s + N)
    (density : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      let U := Fin N → Bool
      let e := fun p r : Fin N => decide (r = p)
      199 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (M : Finset ℕ) (W : ℕ → Set (U × U)),
        o < N + N + s →
        (∀ p : Fin N, W p.val = {x | x.1 p = true} ∧ W (N + p.val) = {x | x.2 p = true}) →
        (∀ i < s, ∃ a < N + N + i, ∃ b < N + N + i,
          let z := W (N + N + i)
          z ∈ [W a ∪ W b, W a, ∅] ∨
            z = W a ∩ W b ∧ (i ∈ M ∨ ∃ P L : Set U, W a = P ×ˢ Set.univ ∧ W b = Set.univ ×ˢ L)) →
        (∀ p l, I p l → (e p, e l) ∈ W o) →
        (∀ y : U, Fintype.card {l : Fin N // y l = true} ≤ q →
          (fun p => decide (¬ ∃ l, I p l ∧ y l = true), y) ∉ W o) →
        100 * M.card < N * q → N * (q + 1) ≤ 100 * s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → ∃ (x19 : Fin x9 → Finset (Fin x2)) (x20 : Fin x9 → Finset (Fin x2)), (∀ (x21 : Fin x9), ∀ x22 ∈ x19 x21, ∀ x24 ∈ x20 x21, x3 x22 x24) ∧ (∀ (x21 x22 : Fin x2), x3 x21 x22 → ∃ (x24 : Fin x9), x21 ∈ x19 x24 ∧ x22 ∈ x20 x24) ∧ ∑ x21 : Fin x9, ((x19 x21).card + (x20 x21).card) ≤ (100 : ℕ) * x9 + x2 := by
  classical
  intro q N I _ hq hN hDegree hUnique s o M W hOut hBase hGate hPlus hMinus hMarked
  have hChoice (i : Fin s) : ∃ a b : ℕ,
      a < N + N + i.val ∧ b < N + N + i.val ∧
      (W (N + N + i.val) = W a ∪ W b ∨ W (N + N + i.val) = W a ∨
        W (N + N + i.val) = ∅ ∨ W (N + N + i.val) = W a ∩ W b) := by
    obtain ⟨a, ha, b, hb, h⟩ := hGate i.val i.isLt
    refine ⟨a, b, ha, hb, ?_⟩
    rcases h with h | h | h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  choose a b hChoice using hChoice
  have frontier (k : ℕ) (hk : k ≤ s) (T : Finset ℕ) (hT : ∀ w ∈ T, w < N + N + k) :
      ∃ S : Finset ℕ, S.card ≤ T.card + k ∧ (∀ w ∈ S, w < N + N) ∧
        ∀ x y : (Fin N → Bool) × (Fin N → Bool),
          (∀ w ∈ S, x ∈ W w → y ∈ W w) →
          ∀ t ∈ T, x ∈ W t → y ∈ W t := by
    induction k generalizing T with
    | zero =>
      refine ⟨T, by simp, ?_, ?_⟩
      · intro w hw
        simpa using hT w hw
      · intro x y h t ht
        exact h t ht
    | succ k ih =>
      let w := N + N + k
      by_cases hw : w ∈ T
      · let i : Fin s := ⟨k, by omega⟩
        obtain ⟨ha, hb, hop⟩ := hChoice i
        change a i < w at ha
        change b i < w at hb
        change W w = W (a i) ∪ W (b i) ∨ W w = W (a i) ∨ W w = ∅ ∨
          W w = W (a i) ∩ W (b i) at hop
        let U := insert (a i) (insert (b i) (T.erase w))
        have hU : ∀ u ∈ U, u < N + N + k := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact ha
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact hb
          obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hu
          have hbound := hT u hin
          dsimp [w] at hne
          omega
        obtain ⟨S, hSize, hIn, hMove⟩ := ih (by omega) U hU
        have hCard : U.card ≤ T.card + 1 := by
          have h1 := Finset.card_insert_le (a i) (insert (b i) (T.erase w))
          have h2 := Finset.card_insert_le (b i) (T.erase w)
          rw [Finset.card_erase_of_mem hw] at h2
          have hpos := Finset.card_pos.mpr ⟨w, hw⟩
          dsimp [U]
          omega
        refine ⟨S, by omega, hIn, ?_⟩
        intro x y hs t ht hin
        by_cases he : t = w
        · subst t
          have A := hMove x y hs (a i) (by simp [U])
          have B := hMove x y hs (b i) (by simp [U])
          rcases hop with h | h | h | h
          · rw [h] at hin ⊢
            exact hin.imp A B
          · rw [h] at hin ⊢
            exact A hin
          · rw [h] at hin
            exact False.elim (Set.notMem_empty _ hin)
          · rw [h] at hin ⊢
            exact ⟨A hin.1, B hin.2⟩
        · exact hMove x y hs t (by simp [U, he, ht]) hin
      · have hU : ∀ u ∈ T, u < N + N + k := by
          intro u hu
          have hn : u ≠ w := fun e => hw (e ▸ hu)
          have hb := hT u hu
          dsimp [w] at hn
          omega
        obtain ⟨S, hSize, hIn, hMove⟩ := ih (by omega) T hU
        exact ⟨S, by omega, hIn, hMove⟩
  obtain ⟨S, hs, hS, hFlow⟩ := frontier s le_rfl {o} (by simpa using hOut)
  have preserve (bad : ℕ) (x y : (Fin N → Bool) × (Fin N → Bool))
      (hp : ∀ p : Fin N, p.val ≠ bad → x.1 p = true → y.1 p = true)
      (hl : ∀ l : Fin N, N + l.val ≠ bad → x.2 l = true → y.2 l = true)
      (hNo : bad ∉ S) :
      x ∈ W o → y ∈ W o := by
    apply hFlow x y ?_ o (by simp)
    intro w hw hx
    have hn : w ≠ bad := fun he => hNo (he ▸ hw)
    have hb := hS w hw
    by_cases hpw : w < N
    · let p : Fin N := ⟨w, hpw⟩
      rw [(hBase p).1] at hx ⊢
      exact hp p hn hx
    · let l : Fin N := ⟨w - N, by omega⟩
      have hL : N + l.val = w := by dsimp [l]; omega
      rw [← hL, (hBase l).2] at hx ⊢
      exact hl l (hL ▸ hn) hx
  have hPoint (p : Fin N) : ∃ l, I p l := by
    by_cases hp : p.val = 0
    · let r : Fin N := ⟨1, by omega⟩
      have hpr : p ≠ r := by intro he; have hv := congrArg Fin.val he; change p.val = 1 at hv; omega
      obtain ⟨l, h, _⟩ := hUnique p r hpr
      exact ⟨l, h.1⟩
    · let r : Fin N := ⟨0, by omega⟩
      have hpr : p ≠ r := by intro he; have hv := congrArg Fin.val he; change p.val = 0 at hv; omega
      obtain ⟨l, h, _⟩ := hUnique p r hpr
      exact ⟨l, h.1⟩
  have hLine (l : Fin N) : ∃ p, I p l := by
    have hn : Nonempty {p : Fin N // I p l} := Fintype.card_pos_iff.mp (by rw [hDegree l]; omega)
    obtain ⟨⟨p, hp⟩⟩ := hn
    exact ⟨p, hp⟩
  have hCover : Finset.range (N + N) ⊆ S := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    by_contra hn
    by_cases hpk : k < N
    · let p : Fin N := ⟨k, hpk⟩
      obtain ⟨l, hpl⟩ := hPoint p
      let z : Fin N → Bool := fun l' => decide (l' = l)
      let x : (Fin N → Bool) × (Fin N → Bool) := (fun p' => decide (p' = p), z)
      let y : (Fin N → Bool) × (Fin N → Bool) := (fun p' => decide (¬ ∃ l', I p' l' ∧ z l' = true), z)
      have cardZ : Fintype.card {l' : Fin N // z l' = true} ≤ q := by
        simpa [z] using (show 1 ≤ q by omega)
      apply hMinus z cardZ
      apply preserve k x y ?_ (fun _ _ h => h) hn (hPlus p l hpl)
      intro p' hNot' hYes
      change decide (p' = p) = true at hYes
      exact (hNot' (congrArg Fin.val (of_decide_eq_true hYes))).elim
    · let l : Fin N := ⟨k - N, by omega⟩
      obtain ⟨p, hpl⟩ := hLine l
      let z : Fin N → Bool := fun _ => false
      let x : (Fin N → Bool) × (Fin N → Bool) := (fun p' => decide (p' = p), fun l' => decide (l' = l))
      let y : (Fin N → Bool) × (Fin N → Bool) := (fun p' => decide (¬ ∃ l', I p' l' ∧ z l' = true), z)
      have cardZ : Fintype.card {l' : Fin N // z l' = true} ≤ q := by simp [z]
      apply hMinus z cardZ
      apply preserve k x y (by intro p' _ _; simp [y, z]) ?_ hn (hPlus p l hpl)
      intro l' hNot' hYes
      change decide (l' = l) = true at hYes
      have he : l' = l := of_decide_eq_true hYes
      apply (hNot' _).elim
      subst l'
      dsimp [l]
      omega
  have hRaw := Finset.card_le_card hCover
  rw [Finset.card_range] at hRaw
  simp only [Finset.card_singleton] at hs
  have hAll : N + N ≤ s + 1 := by omega
  have hSlots : N ≤ s := by omega
  apply stars q N s I hDegree hSlots
  by_cases hsmall : q < 199
  · have hmq : N * (q + 1) ≤ N * 199 := Nat.mul_le_mul_left N (by omega)
    have hbigN : 100 ≤ N := by omega
    omega
  apply density q N I (by omega) hN hDegree hUnique s o M W hOut hBase ?_ hPlus hMinus hMarked
  intro i hi
  obtain ⟨a, ha, b, hb, h⟩ := hGate i hi
  exact ⟨a, ha, b, hb, by simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using h⟩
