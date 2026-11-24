import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3159_583
    (rawSign : ∀ (b s : ℕ) (op : Fin b → Bool) (l r : Fin b → ℕ × Bool)
      (w : (Fin 9 → Bool) → ℕ → Bool),
      5 ≤ b → s < 9 → b + (if s = 0 then 0 else 1) ≤ 14 →
      (∀ i : Fin 9, ∃ j, l j = (i.val,false) ∨ r j = (i.val,false)) →
      (∀ j, (l j).1 < 10 + j.val ∧ (r j).1 < 10 + j.val) →
      (∀ j, ∀ p ∈ [l j, r j], p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 = s) →
      (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
      (∀ x j, let v := fun p : ℕ × Bool => w x p.1 ^^ p.2
        w x (10 + j.val) = if op j then v (l j) && v (r j) else v (l j) || v (r j)) →
      ∃ x : Fin 9 → Bool, w x (9 + b) ≠
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (gateSign : ∀ (b s : ℕ) (op : Fin b → Bool) (l r : Fin b → ℕ × Bool)
      (w : (Fin 9 → Bool) → ℕ → Bool),
      5 ≤ b → 10 ≤ s → s < 9 + b → b ≤ 13 →
      (∀ i : Fin 9, ∃ j, (l j).1 = i.val ∨ (r j).1 = i.val) →
      (∀ j, (l j).1 < 10 + j.val ∧ (r j).1 < 10 + j.val) →
      (∀ j, ∀ p ∈ [l j, r j], p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 = s) →
      (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
      (∀ x j, let v := fun p : ℕ × Bool => w x p.1 ^^ p.2
        w x (10 + j.val) = if op j then v (l j) && v (r j) else v (l j) || v (r j)) →
      ∃ x : Fin 9 → Bool, w x (9 + b) ≠
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (0 : ℕ) < x1 →     x6.card ≤ (3 : ℕ) →       x1 + x6.card ≤ (14 : ℕ) →         x6.card ≤ (1 : ℕ) →           (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) →             (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) →               (∀ (x14 : ℕ), x14 ∈ x6 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (x5 = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x7 x15 ↑x16 = x15 x16) →                   (∀ (x16 : Fin (9 : ℕ) → Bool), x7 x16 (9 : ℕ) = Bool.false) →                     (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1),                         have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x7 x17 x19.1 ^^ x19.2;                         x7 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) →                       ∃ (x18 : Fin (9 : ℕ) → Bool), (x7 x18 ((9 : ℕ) + x1) ^^ x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ))) := by
  intro b op l r phase paid w positive _ budget small earlier seen charge raw zero step
  classical
  let f := fun x : Fin 9 → Bool =>
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let v (x : Fin 9 → Bool) (p : ℕ × Bool) := w x p.1 ^^ p.2
  have count : 5 ≤ b := by
    let left := Finset.univ.image (fun j : Fin b => (l j).1)
    let right := Finset.univ.image (fun j : Fin b => (r j).1)
    have sub : Finset.range 9 ⊆ left ∪ right := by
      intro k hk
      let i : Fin 9 := ⟨k, Finset.mem_range.mp hk⟩
      obtain ⟨j, hj | hj⟩ := seen i
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)
    have lsize : left.card ≤ b := Finset.card_image_le.trans (by simp)
    have rsize : right.card ≤ b := Finset.card_image_le.trans (by simp)
    have limit := (Finset.card_le_card sub).trans (Finset.card_union_le left right)
    rw [Finset.card_range] at limit
    omega
  have only (s : ℕ) (paidOnly : ∀ k ∈ paid, k = s) :
      ∀ j, ∀ p ∈ [l j, r j], p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 = s := by
    intro j p hp sign
    by_cases e0 : p.1 = 0
    · exact Or.inl e0
    by_cases e9 : p.1 = 9
    · exact Or.inr (Or.inl e9)
    have occ : ∃ k, l k = (p.1, true) ∨ r k = (p.1, true) := by
      have eta : p = (p.1, true) := Prod.ext rfl sign
      refine ⟨j, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with h | h
      · exact Or.inl (h.symm.trans eta)
      · exact Or.inr (h.symm.trans eta)
    exact Or.inr (Or.inr (paidOnly _ ((charge _).mpr ⟨e0, e9, Or.inr occ⟩)))
  have unique (s : ℕ) (hs : s ∈ paid) : ∀ k ∈ paid, k = s := by
    have seq : {s} = paid := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.singleton_subset_iff.mpr hs
      · simpa using small
    intro k hk
    simpa [← seq] using hk
  have combine : ∀ (t a c d e : Bool), (a = true → d = true) →
      (c = true → e = true) → (if t then a && c else a || c) = true →
      (if t then d && e else d || e) = true := by decide
  have compare (x y : Fin 9 → Bool)
      (low : ∀ j, ∀ p ∈ [l j, r j], p.1 < 10 → v x p = true → v y p = true)
      (high : ∀ j, ∀ p ∈ [l j, r j], 10 ≤ p.1 → p.2 = false) :
      w x (9+b) = true → w y (9+b) = true := by
    have aux : ∀ k, 10 ≤ k → k < 10 + b → w x k = true → w y k = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk kmax wx
        let j : Fin b := ⟨k - 10, by omega⟩
        have index : k = 10 + j.val := by dsimp [j]; omega
        have slot (p : ℕ × Bool) (hp : p ∈ [l j, r j]) :
            v x p = true → v y p = true := by
          by_cases plow : p.1 < 10
          · exact low j p hp plow
          · have pprior : p.1 < k := by
              rw [index]
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with h | h
              · rw [h]; exact (earlier j).1
              · rw [h]; exact (earlier j).2
            have s := high j p hp (by omega)
            simpa only [v, s, Bool.xor_false] using ih p.1 pprior (by omega) (by omega)
        rw [index, step x j] at wx
        rw [index, step y j]
        exact combine _ _ _ _ _ (slot _ (by simp)) (slot _ (by simp)) wx
    exact aux _ (by omega) (by omega)
  let neighbor : Fin 9 → Fin 9 := ![1, 0, 1, 2, 0, 0, 1, 2, 3]
  let one (i : Fin 9) : Fin 9 → Bool := fun k => decide (k = neighbor i)
  let two (i : Fin 9) : Fin 9 → Bool := fun k => decide (k = i ∨ k = neighbor i)
  have test : ∀ i : Fin 9, f (one i) = false ∧ f (two i) = true := by
    dsimp only [f, one, two, neighbor]
    decide
  by_contra no
  have computes (x : Fin 9 → Bool) : (w x (9+b) ^^ phase) = f x :=
    Classical.byContradiction (fun h => no ⟨x, h⟩)
  by_cases signedOut : phase = true
  · have outPaid : 9 + b ∈ paid := (charge _).mpr ⟨by omega, by omega, Or.inl ⟨signedOut, rfl⟩⟩
    have signs := only (9+b) (unique _ outPaid)
    have stable : ∀ j, ∀ p ∈ [l j, r j], 10 ≤ p.1 → p.2 = false := by
      intro j p hp hi
      cases hp2 : p.2 with
      | false => rfl
      | true =>
        have pbound : p.1 < 9+b := by
          have jlt := j.isLt
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with h | h
          · rw [h]; have hlt := (earlier j).1; omega
          · rw [h]; have hlt := (earlier j).2; omega
        rcases signs j p hp hp2 with h | h | h <;> omega
    let x := one (1 : Fin 9)
    let y := two (1 : Fin 9)
    have low (j : Fin b) (p : ℕ × Bool) (hp : p ∈ [l j, r j]) (bound : p.1 < 10) :
        v x p = true → v y p = true := by
      by_cases ix : p.1 < 9
      · let i : Fin 9 := ⟨p.1, ix⟩
        have a : w x p.1 = x i := raw _ i
        have d : w y p.1 = y i := raw _ i
        by_cases eq : i = 1
        · have hzero : p.1 = 1 := congrArg Fin.val eq
          have pos : p.2 = false := by
            cases h : p.2 with
            | false => rfl
            | true => rcases signs j p hp h with h | h | h <;> omega
          rw [show v x p = (x i ^^ p.2) by unfold v; rw [a],
            show v y p = (y i ^^ p.2) by unfold v; rw [d], pos, eq]
          decide
        · have same : x i = y i := by simp [x, y, one, two, eq]
          simpa only [v, a, d, same] using (fun h : (y i ^^ p.2) = true => h)
      · have eq : p.1 = 9 := by omega
        simp only [v, eq, zero, imp_self]
    have hx := computes x
    have hy := computes y
    rw [signedOut, show f x = false from (test 1).1] at hx
    rw [signedOut, show f y = true from (test 1).2] at hy
    have wx : w x (9+b) = true := by
      cases h : w x (9+b) with
      | false => simp [h] at hx
      | true => rfl
    have wy := compare x y low stable wx
    rw [wy] at hy
    exact Bool.noConfusion hy
  have phaseFalse : phase = false := Bool.eq_false_of_not_eq_true signedOut
  have good (x : Fin 9 → Bool) : w x (9+b) = f x := by
    simpa only [phaseFalse, Bool.xor_false] using computes x
  by_cases gate : ∃ s ∈ paid, 10 ≤ s
  · obtain ⟨s, hs, hgate⟩ := gate
    have used := (charge s).mp hs
    have below : s < 9+b := by
      rcases used.2.2 with flip | ⟨j, h | h⟩
      · rw [phaseFalse] at flip
        exact Bool.noConfusion flip.1
      · have hlt := (earlier j).1
        rw [h] at hlt
        have jlt := j.isLt
        omega
      · have hlt := (earlier j).2
        rw [h] at hlt
        have jlt := j.isLt
        omega
    have onePaid := Finset.card_pos.mpr ⟨s, hs⟩
    obtain ⟨x, bad⟩ := gateSign b s op l r w count hgate below (by omega)
      seen earlier (only s (unique s hs)) raw zero step
    exact bad (good x)
  have noGate : ∀ k ∈ paid, k < 9 := by
    intro k hk
    have ne := ((charge k).mp hk).2.1
    by_contra! high
    exact gate ⟨k, hk, by omega⟩
  have posSeen : ∀ i : Fin 9, ∃ j, l j = (i.val,false) ∨ r j = (i.val,false) := by
    intro i
    by_contra missed
    let x := two i
    let y := one i
    have high (j : Fin b) (p : ℕ × Bool) (hp : p ∈ [l j, r j]) (big : 10 ≤ p.1) : p.2 = false := by
      cases hp2 : p.2 with
      | false => rfl
      | true =>
        have eta : p = (p.1, true) := Prod.ext rfl hp2
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        have used : ∃ j, l j = (p.1, true) ∨ r j = (p.1, true) := by
          rcases hp with eq | eq
          · exact ⟨j, Or.inl (eq.symm.trans eta)⟩
          · exact ⟨j, Or.inr (eq.symm.trans eta)⟩
        have mem := (charge p.1).mpr ⟨by omega, by omega, Or.inr used⟩
        have := noGate _ mem
        omega
    have low (j : Fin b) (p : ℕ × Bool) (hp : p ∈ [l j, r j]) (bound : p.1 < 10) :
        v x p = true → v y p = true := by
      by_cases ix : p.1 < 9
      · let k : Fin 9 := ⟨p.1, ix⟩
        have a : w x p.1 = x k := raw _ k
        have d : w y p.1 = y k := raw _ k
        by_cases eq : k = i
        · have same : p.1 = i.val := congrArg Fin.val eq
          have neg : p.2 = true := by
            cases h : p.2 with
            | true => rfl
            | false =>
              have eta : p = (i.val, false) := Prod.ext same h
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              exact False.elim (missed ⟨j, hp.imp (fun e => e.symm.trans eta) (fun e => e.symm.trans eta)⟩)
          rw [show v x p = (x k ^^ p.2) by unfold v; rw [a],
            show v y p = (y k ^^ p.2) by unfold v; rw [d], neg, eq]
          simp [x, two]
        · have same : x k = y k := by simp [x, y, one, two, eq]
          simpa only [v, a, d, same] using (fun h : (y k ^^ p.2) = true => h)
      · have eq : p.1 = 9 := by omega
        simp only [v, eq, zero, imp_self]
    have wx : w x (9+b) = true := (good x).trans (test i).2
    exact Bool.noConfusion (compare x y low high wx |>.symm.trans ((good y).trans (test i).1))
  by_cases empty : paid = ∅
  · have paidOnly : ∀ k ∈ paid, k = 0 := by simp [empty]
    obtain ⟨x, bad⟩ := rawSign b 0 op l r w count (by decide) (by simpa [empty] using budget)
      posSeen earlier (only 0 paidOnly) raw zero step
    exact bad (good x)
  · obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have e0 := ((charge s).mp hs).1
    have plus := Finset.card_pos.mpr ⟨s, hs⟩
    obtain ⟨x, bad⟩ := rawSign b s op l r w count (noGate s hs) (by simp [e0]; omega)
      posSeen earlier (only s (unique s hs)) raw zero step
    exact bad (good x)
