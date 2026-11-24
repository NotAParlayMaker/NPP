import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3501_638
    (small : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I], 2 ≤ q →
      n = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (F : ℕ → Finset (Finset (Fin (n + n)))), o < n + n + s →
      (∀ i : Fin (n + n), F i = {{i}}) →
      (∀ j < s, ∃ a b, a < b ∧ b < n + n + j ∧
        (F (n + n + j) = F a ∪ F b ∨
         F (n + n + j) = (F a).biUnion (fun t => (F b).image (t ∪ ·)))) →
      (∀ x : Fin (n + n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        ((∀ t ∈ F o, ∃ i ∈ t, x i = true) ↔
          ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      3 * n ≤ s + 1)
    (large : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I], 300 ≤ q →
      n = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (F : ℕ → Finset (Finset (Fin (n + n)))), o < n + n + s →
      (∀ i : Fin (n + n), F i = {{i}}) →
      (∀ j < s, ∃ a b, a < b ∧ b < n + n + j ∧
        (F (n + n + j) = F a ∪ F b ∨
         F (n + n + j) = (F a).biUnion (fun t => (F b).image (t ∪ ·)))) →
      (∀ x : Fin (n + n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        ((∀ t ∈ F o, ∃ i ∈ t, x i = true) ↔
          ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true)) →
      (∃ j < s, ∃ a b, a < b ∧ b < n + n + j ∧ F (n + n + j) = F a ∪ F b ∧
        ∃ d : Bool, ∀ w ∈ [a,b], ∃ t ∈ F w, ∃ i : Fin n,
          (if d then Fin.natAdd n i else Fin.castAdd n i) ∈ t) → n * q ≤ 100 * s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Finset (Finset (Fin (x2 + x2)))),             x10 < x2 + x2 + x9 →               (∀ (x13 : Fin (x2 + x2)), x11 ↑x13 = {{x13}}) →                 (∀ x14 < x9, ∃ (x16 : ℕ) (x17 : ℕ), x16 < x17 ∧ x17 < x2 + x2 + x14 ∧ (x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17 ∨ x11 (x2 + x2 + x14) = (x11 x16).biUnion fun (x18 : Finset (Fin (x2 + x2))) => Finset.image (fun (x19 : Finset (Fin (x2 + x2))) => x18 ∪ x19) (x11 x17))) →                   (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → Fin.castAdd x2 x17 ∈ x15 ∨ Fin.natAdd x2 x18 ∈ x15) →                     (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, (∀ (x19 : Fin x2), Fin.castAdd x2 x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ ∀ (x19 : Fin x2), Fin.natAdd x2 x19 ∈ x18 ↔ x19 ∉ x16) →                       (∃ x17 < x9,                           ∃ (x18 : ℕ) (x19 : ℕ),                             x18 < x19 ∧                               x19 < x2 + x2 + x17 ∧                                 x11 (x2 + x2 + x17) = x11 x18 ∪ x11 x19 ∧                                   ∃ (x20 : Bool),                                     ∀ x21 ∈ [x18, x19],                                       ∃ (x23 : Fin x2 → Bool),                                         have x24 : Bool → List Bool := fun (x24 : Bool) => if x20 = Bool.true then List.ofFn x23 ++ List.replicate x2 x24 else List.replicate x2 x24 ++ List.ofFn x23;                                         have x25 : Bool → Prop := fun (x25 : Bool) => ∀ x26 ∈ x11 x21, ∃ x28 ∈ x26, (x24 x25).getD (↑x28) Bool.false = Bool.true;                                         ¬(x25 Bool.false ↔ x25 Bool.true)) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q n I inst hq hn hdeg hjoin s o F ho hin hw hcover hclauses hmarked
  classical
  have hSound (x : Fin (n + n) → Bool)
      (hx : Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q) :
      (∀ t ∈ F o, ∃ i ∈ t, x i = true) ↔
        ∃ p l, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true := by
    constructor
    · intro hAll
      by_contra hNo
      let T := Finset.univ.filter (fun l : Fin n => x (Fin.natAdd n l) = true)
      have hT (l : Fin n) : l ∈ T ↔ x (Fin.natAdd n l) = true := by simp [T]
      have hTc : T.card ≤ q := by rw [← Fintype.card_subtype]; exact hx
      obtain ⟨t, ht, hP, hL⟩ := hclauses T hTc
      obtain ⟨i, hi, hxi⟩ := hAll t ht
      induction i using Fin.addCases with
      | left p =>
        obtain ⟨l, hl, hI⟩ := (hP p).mp hi
        exact hNo ⟨p, l, hI, hxi, (hT l).mp hl⟩
      | right l =>
        exact (hL l).mp hi ((hT l).mpr hxi)
    · rintro ⟨p, l, hI, hp, hl⟩ t ht
      rcases hcover t ht p l hI with h | h
      · exact ⟨Fin.castAdd n p, h, hp⟩
      · exact ⟨Fin.natAdd n l, h, hl⟩
  clear hcover hclauses
  have hArithmetic : ∀ (m k z : ℕ), 100 ≤ m → k ≤ 299 → 3 * m ≤ z + 1 → m * k ≤ 100 * z := by
    intro m k z hm hk hz
    have hnum := Nat.mul_le_mul_left 100 hz
    rw [Nat.mul_add] at hnum
    exact (Nat.mul_le_mul_left m hk).trans (by omega)
  by_cases hlow : q ≤ 299
  · have h2 : 2 ≤ q := (by decide : 2 ≤ 250).trans hq
    have hn' : 100 ≤ n := by omega
    exact hArithmetic n q s hn' hlow (small q n I h2 hn hdeg hjoin s o F ho hin hw hSound)
  · have h300 : 300 ≤ q := by omega
    refine large q n I h300 hn hdeg hjoin s o F ho hin hw hSound ?_
    obtain ⟨j, hj, a, b, hab, hb, eq, d, hd⟩ := hmarked
    refine ⟨j, hj, a, b, hab, hb, eq, d, ?_⟩
    intro w hw'
    obtain ⟨z, hz⟩ := hd w hw'
    by_contra! hAbsent
    let row := fun c : Bool => Fin.append (if d then z else fun _ => c) (if d then fun _ => c else z)
    have hrow (c : Bool) : List.ofFn (row c) =
        if d = true then List.ofFn z ++ List.replicate n c else List.replicate n c ++ List.ofFn z := by
      cases d <;> simp [row, List.ofFn_fin_append, List.ofFn_const]
    have hread (c : Bool) (i : Fin (n + n)) : (List.ofFn (row c)).getD i.val false = row c i := by
      rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
    have hFixed (t : Finset (Fin (n + n))) (ht : t ∈ F w) (i : Fin (n + n)) (hi : i ∈ t) :
        row false i = row true i := by
      induction i using Fin.addCases with
      | left p =>
        cases d with
        | false => exact (hAbsent t ht p (by simpa using hi)).elim
        | true => simp [row]
      | right l =>
        cases d with
        | false => simp only [row, Bool.false_eq_true, ite_false, Fin.append_right]
        | true => exact (hAbsent t ht l (by simpa using hi)).elim
    dsimp only at hz
    simp_rw [← hrow, hread] at hz
    apply hz
    constructor <;> intro h t ht <;> obtain ⟨i, hi, he⟩ := h t ht
    · exact ⟨i, hi, (hFixed t ht i hi).symm.trans he⟩
    · exact ⟨i, hi, (hFixed t ht i hi).trans he⟩
