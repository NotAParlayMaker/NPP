import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2276_1
    (packed : ∀ (x1 : ℕ) (x2 : List (BitVec x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : List (BitVec x1)), x5.length ≤ x3.size ∧ (∀ (x6 : Fin x5.length), ∃ x7 ∈ (0 : BitVec x1) :: BitVec.allOnes x1 :: (x2 ++ List.take (↑x6) x5), ∃ x8 ∈ (0 : BitVec x1) :: BitVec.allOnes x1 :: (x2 ++ List.take (↑x6) x5), x5.get x6 = x7 &&& x8 ∨ x5.get x6 = x7 ||| x8) ∧ ∃ x6 ∈ (0 : BitVec x1) :: BitVec.allOnes x1 :: (x2 ++ x5), ∀ (x7 : Fin x1), x6.getLsbD ↑x7 = x3.eval (List.map (fun (x8 : BitVec x1) => x8.getLsbD ↑x7) x2))
    (fewAnd :
      let base : List (BitVec 58) := [(95229015649943559 : BitVec 58), (63038587666488 : BitVec 58), (256462815680 : BitVec 58), (4292497062759936 : BitVec 58), (8521481482240 : BitVec 58), (14003410187812864 : BitVec 58), (55389823207997440 : BitVec 58), (189297016294081033 : BitVec 58), (155696362464477250 : BitVec 58), (218994303132270608 : BitVec 58), (183565875465490436 : BitVec 58), (229736628138025984 : BitVec 58), (270286071508633728 : BitVec 58), (288160007407550752 : BitVec 58)]
      ∀ T : List (Bool × BitVec 58), T.length ≤ 24 → T.countP Prod.fst ≤ 6 →
        (∀ j : Fin T.length,
          let pool := base ++ (T.take j.val).map Prod.snd
          (T.get j).2 ∉ pool ∧ ∃ a ∈ pool, ∃ b ∈ pool, a ≠ b ∧
            (T.get j).2 = if (T.get j).1 then a &&& b else a ||| b) →
        (2097150 : BitVec 58) ∉ T.map Prod.snd)
    (fewOr :
      let base : List (BitVec 58) := [(95229015649943559 : BitVec 58), (63038587666488 : BitVec 58), (256462815680 : BitVec 58), (4292497062759936 : BitVec 58), (8521481482240 : BitVec 58), (14003410187812864 : BitVec 58), (55389823207997440 : BitVec 58), (189297016294081033 : BitVec 58), (155696362464477250 : BitVec 58), (218994303132270608 : BitVec 58), (183565875465490436 : BitVec 58), (229736628138025984 : BitVec 58), (270286071508633728 : BitVec 58), (288160007407550752 : BitVec 58)]
      ∀ T : List (Bool × BitVec 58), T.length ≤ 24 → T.countP (fun p => !p.1) ≤ 17 →
        (∀ j : Fin T.length,
          let pool := base ++ (T.take j.val).map Prod.snd
          (T.get j).2 ∉ pool ∧ ∃ a ∈ pool, ∃ b ∈ pool, a ≠ b ∧
            (T.get j).2 = if (T.get j).1 then a &&& b else a ||| b) →
        (2097150 : BitVec 58) ∉ T.map Prod.snd) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → x6 (0 : Fin (14 : ℕ)) = Bool.false ∨ x6 (7 : Fin (14 : ℕ)) = Bool.false → (x4.eval (List.ofFn x6) = Bool.true ↔ x2 x6)) → x4.eval (List.ofFn fun (x7 : Fin (14 : ℕ)) => Decidable.decide (x7 = (0 : Fin (14 : ℕ)) ∨ x7 = (7 : Fin (14 : ℕ)))) = Bool.false → (25 : ℕ) ≤ x4.size := by
  let cols : List (BitVec 58) := [(95229015649943559 : BitVec 58), (63038587666488 : BitVec 58), (256462815680 : BitVec 58), (4292497062759936 : BitVec 58), (8521481482240 : BitVec 58), (14003410187812864 : BitVec 58), (55389823207997440 : BitVec 58), (189297016294081033 : BitVec 58), (155696362464477250 : BitVec 58), (218994303132270608 : BitVec 58), (183565875465490436 : BitVec 58), (229736628138025984 : BitVec 58), (270286071508633728 : BitVec 58), (288160007407550752 : BitVec 58)]
  let edges : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let hit := fun x : Fin 14 → Bool =>
    ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
  let ext := fun x : Fin 14 → Bool =>
    (hit x ∧ ∀ i : Fin 14, x i = true → ¬ hit (Function.update x i false)) ∨
    (¬ hit x ∧ ∀ i : Fin 14, x i = false → hit (Function.update x i true))
  let row := fun (k : Fin 58) (i : Fin 14) => (cols.getD i 0).getLsbD k
  let test := fun x : Fin 14 → Bool => edges.any fun e =>
    x (Fin.ofNat 14 e.1) && x (Fin.ofNat 14 e.2)
  have bounds : ∀ e ∈ edges, e.1 < 14 ∧ e.2 < 14 := by decide
  have reflect (x : Fin 14 → Bool) : hit x ↔ test x = true := by
    simp only [hit, test, List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨(a.val, b.val), hab, by simpa using ha, by simpa using hb⟩
    · rintro ⟨⟨a, b⟩, hab, ha, hb⟩
      obtain ⟨hal, hbl⟩ := bounds (a, b) hab
      exact ⟨⟨a, hal⟩, ⟨b, hbl⟩, hab, by simpa [Fin.ofNat, Nat.mod_eq_of_lt hal] using ha,
        by simpa [Fin.ofNat, Nat.mod_eq_of_lt hbl] using hb⟩
  let target : BitVec 58 := 2097150
  let verify := fun (k : Fin 58) =>
    if k.val = 0 then
      (List.finRange 14).all fun i => row k i == decide (i = 0 ∨ i = 7)
    else
      let x := row k
      let p := target.getLsbD k
      (!x 0 || !x 7) && (test x == p) && (List.finRange 14).all fun i =>
        if x i = p then test (Function.update x i (!p)) == !p else true
  have allRows : (List.finRange 58).all verify = true := by
    dsimp only [verify, test, target, row, cols, edges]
    decide +kernel
  have row0 : row 0 = fun i : Fin 14 => decide (i = 0 ∨ i = 7) := by
    funext i
    have hk := List.all_eq_true.mp allRows 0 (by simp)
    change ((List.finRange 14).all fun j => row 0 j == decide (j = 0 ∨ j = 7)) = true at hk
    exact beq_iff_eq.mp (List.all_eq_true.mp hk i (by simp))
  have cert : ∀ k : Fin 58, k.val ≠ 0 →
      ext (row k) ∧ (row k 0 = false ∨ row k 7 = false) ∧ (hit (row k) ↔ target.getLsbD k = true) := by
    intro k hk0
    have hk := List.all_eq_true.mp allRows k (by simp)
    simp only [verify, hk0, ↓reduceIte] at hk
    obtain ⟨h12, hflip⟩ := Bool.and_eq_true_iff.mp hk
    obtain ⟨h07, hp⟩ := Bool.and_eq_true_iff.mp h12
    have h07' : row k 0 = false ∨ row k 7 = false := by
      rcases Bool.or_eq_true_iff.mp h07 with h | h
      · exact Or.inl (Bool.not_eq_true' _ |>.mp h)
      · exact Or.inr (Bool.not_eq_true' _ |>.mp h)
    have heq : test (row k) = target.getLsbD k := beq_iff_eq.mp hp
    refine ⟨?_, h07', by rw [reflect, heq]⟩
    have flips (i : Fin 14) (hi : row k i = target.getLsbD k) :
        test (Function.update (row k) i (!(target.getLsbD k))) = !(target.getLsbD k) := by
      have h := List.all_eq_true.mp hflip i (by simp)
      change (if row k i = target.getLsbD k then _ else true) = true at h
      simpa [hi] using h
    cases hpv : target.getLsbD k with
    | false =>
      right
      refine ⟨by rw [reflect, heq, hpv]; decide, ?_⟩
      intro i hi
      have hf := flips i (hi.trans hpv.symm)
      rw [hpv] at hf
      exact (reflect _).2 hf
    | true =>
      left
      refine ⟨(reflect _).2 (heq.trans hpv), ?_⟩
      intro i hi
      have hf := flips i (hi.trans hpv.symm)
      rw [hpv] at hf
      change test (Function.update (row k) i false) = false at hf
      rw [reflect, hf]
      decide
  have inputRows (k : Fin 58) : cols.map (fun v => v.getLsbD k) = List.ofFn (row k) := by
    apply List.ext_getElem
    · simp [cols]
    · intro i hi hi'
      have hic : i < cols.length := by simpa using hi
      simp only [List.getElem_map, List.getElem_ofFn, row, List.getD_eq_getElem _ _ hic]
  intro _ _ _ C hmono hbd h07
  by_contra hlt25
  have hle24 : C.size ≤ 24 := by omega
  obtain ⟨S, hSlen, hSsteps, t, htmem, htbits⟩ := packed 58 cols C hmono
  have ht_eq : t = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let r : Fin 58 := ⟨k, hk⟩
    change t.getLsbD r.val = target.getLsbD r.val
    rw [htbits r, inputRows r]
    by_cases hk0 : r.val = 0
    · have hr0 : r = 0 := Fin.ext hk0
      rw [hr0, row0, h07]
      decide
    · obtain ⟨hext, hnot, hhit⟩ := cert r hk0
      exact Bool.eq_iff_iff.mpr ((hbd (row r) hext hnot).trans hhit)
  have htgt : target ∈ (0 : BitVec 58) :: BitVec.allOnes 58 :: (cols ++ S) := ht_eq ▸ htmem
  let x1 : List (BitVec 58) := (0 : BitVec 58) :: BitVec.allOnes 58 :: cols
  have htgt' : target ∈ x1 ++ S := by simpa [x1] using htgt
  let Good : List (Bool × BitVec 58) → Prop := fun T =>
    ∀ j : Fin T.length,
      let pool := cols ++ (T.take j.val).map Prod.snd
      (T.get j).2 ∉ pool ∧ ∃ a ∈ pool, ∃ b ∈ pool, a ≠ b ∧
        (T.get j).2 = if (T.get j).1 then a &&& b else a ||| b
  have hbuild : ∀ k ≤ S.length, ∃ T : List (Bool × BitVec 58),
      T.length ≤ k ∧ Good T ∧
      ∀ v ∈ x1 ++ S.take k, v = 0 ∨ v = BitVec.allOnes 58 ∨ v ∈ cols ++ T.map Prod.snd := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], Nat.le_refl 0, fun j => Fin.elim0 j, ?_⟩
      intro v hv
      simp only [List.take_zero, List.append_nil, List.map_nil, x1, List.mem_cons] at hv ⊢
      exact hv
    | succ k ih =>
      intro hk
      obtain ⟨T, hTlen, hTgood, hTcov⟩ := ih (Nat.le_of_succ_le hk)
      have hklt : k < S.length := Nat.lt_of_succ_le hk
      let v : BitVec 58 := S.get ⟨k, hklt⟩
      have htake : S.take (k + 1) = S.take k ++ [v] :=
        List.take_succ_eq_append_getElem hklt
      have hcov_prev : ∀ u ∈ x1 ++ S.take (k + 1),
          u = v ∨ u = 0 ∨ u = BitVec.allOnes 58 ∨ u ∈ cols ++ T.map Prod.snd := by
        intro u hu
        rw [htake, ← List.append_assoc, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact Or.inr (hTcov u hu)
        · exact Or.inl rfl
      by_cases htriv : v = 0 ∨ v = BitVec.allOnes 58 ∨ v ∈ cols ++ T.map Prod.snd
      · refine ⟨T, Nat.le_succ_of_le hTlen, hTgood, ?_⟩
        intro u hu
        rcases hcov_prev u hu with rfl | hrest
        · exact htriv
        · exact hrest
      · push Not at htriv
        obtain ⟨hv0, hv1, hvnot⟩ := htriv
        obtain ⟨a, ha, b, hb, hstep⟩ := hSsteps ⟨k, hklt⟩
        have ha' : a ∈ x1 ++ S.take k := by simpa [x1] using ha
        have hb' : b ∈ x1 ++ S.take k := by simpa [x1] using hb
        change v = a &&& b ∨ v = a ||| b at hstep
        have ha_mem : a ∈ cols ++ T.map Prod.snd := by
          rcases hTcov a ha' with rfl | rfl | ham
          · rcases hstep with h | h
            · simp at h
              exact absurd h hv0
            · simp at h
              have hbv := hTcov b hb'
              rw [← h] at hbv
              rcases hbv with h0 | h1 | hm
              · exact absurd h0 hv0
              · exact absurd h1 hv1
              · exact absurd hm hvnot
          · rcases hstep with h | h
            · rw [BitVec.allOnes_and] at h
              have hbv := hTcov b hb'
              rw [← h] at hbv
              rcases hbv with h0 | h1 | hm
              · exact absurd h0 hv0
              · exact absurd h1 hv1
              · exact absurd hm hvnot
            · rw [BitVec.allOnes_or] at h
              exact absurd h hv1
          · exact ham
        have hb_mem : b ∈ cols ++ T.map Prod.snd := by
          rcases hTcov b hb' with rfl | rfl | hbm
          · rcases hstep with h | h
            · simp at h
              exact absurd h hv0
            · simp at h
              rw [h] at hvnot
              exact absurd ha_mem hvnot
          · rcases hstep with h | h
            · rw [BitVec.and_allOnes] at h
              rw [h] at hvnot
              exact absurd ha_mem hvnot
            · rw [BitVec.or_allOnes] at h
              exact absurd h hv1
          · exact hbm
        have hab : a ≠ b := by
          rintro rfl
          rcases hstep with h | h
          · simp at h
            rw [h] at hvnot
            exact hvnot ha_mem
          · simp at h
            rw [h] at hvnot
            exact hvnot ha_mem
        have htag : ∃ tag : Bool, v = if tag then a &&& b else a ||| b := by
          rcases hstep with h | h
          · exact ⟨true, h⟩
          · exact ⟨false, h⟩
        obtain ⟨tag, htag⟩ := htag
        refine ⟨T ++ [(tag, v)], by simp; omega, ?_, ?_⟩
        · intro j
          by_cases hj : j.val < T.length
          · have hget : (T ++ [(tag, v)]).get j = T.get ⟨j.val, hj⟩ := by
              simp [List.get_eq_getElem, List.getElem_append_left hj]
            have htk : (T ++ [(tag, v)]).take j.val = T.take j.val :=
              List.take_append_of_le_length (Nat.le_of_lt hj)
            simpa only [hget, htk] using hTgood ⟨j.val, hj⟩
          · have hjeq : j.val = T.length := by
              have := j.isLt
              simp at this
              omega
            have hget : (T ++ [(tag, v)]).get j = (tag, v) := by
              simp [List.get_eq_getElem, hjeq]
            have htk : (T ++ [(tag, v)]).take j.val = T := by
              rw [hjeq, List.take_left]
            simpa only [hget, htk] using ⟨hvnot, a, ha_mem, b, hb_mem, hab, htag⟩
        · intro u hu
          rcases hcov_prev u hu with rfl | h0 | h1 | hm
          · exact Or.inr (Or.inr (by simp))
          · exact Or.inl h0
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (by simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append] at hm ⊢; rcases hm with h | h; exact Or.inl h; exact Or.inr (Or.inl h)))
  obtain ⟨T, hTlen, hTgood, hTcov⟩ := hbuild S.length (Nat.le_refl _)
  have htarget_in : target ∈ T.map Prod.snd := by
    have h1 := hTcov target (by simpa using htgt')
    have hne0 : target ≠ 0 := by decide
    have hne1 : target ≠ BitVec.allOnes 58 := by decide
    have hnotb : target ∉ cols := by decide
    rcases h1 with h0 | h1 | hm
    · exact absurd h0 hne0
    · exact absurd h1 hne1
    · rw [List.mem_append] at hm
      exact hm.resolve_left hnotb
  have hpart : ∀ L : List (Bool × BitVec 58),
      L.countP Prod.fst + L.countP (fun p => !p.1) = L.length := by
    intro L
    induction L with
    | nil => rfl
    | cons p L ih =>
      rcases p with ⟨b, w⟩
      cases b <;> simp <;> omega
  have hsum := hpart T
  have hTle24 : T.length ≤ 24 := Nat.le_trans hTlen (Nat.le_trans hSlen hle24)
  by_cases hand : T.countP Prod.fst ≤ 6
  · exact fewAnd T hTle24 hand hTgood htarget_in
  · exact fewOr T hTle24 (by omega) hTgood htarget_in
