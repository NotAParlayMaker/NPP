import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4811_1
    (hchar :
      let D : List ℕ := [0, 5, 7, 17, 20]
      let P : (Fin 42 → Bool) → Prop := fun x =>
        ∃ u v : Fin 42, (u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ D) ∧ x u = true ∧ x v = true
      let E : Fin 21 → Fin 21 → Prop := fun p l => (l.val + 21 - p.val) % 21 ∈ D
      let Z : (Fin 21 → Bool) → Fin 21 → Bool := fun y l =>
        !(y l || y (l + 1) || y (l + 4) || y (l + 14) || y (l + 16))
      ∀ x : Fin 42 → Bool,
        ((P x ∧ ∀ z : Fin 42 → Bool, (∀ i, z i = true → x i = true) → P z → z = x) →
          ∃ p l : Fin 21, E p l ∧ x = fun i => i.val == p.val || i.val == 21 + l.val) ∧
        ((¬P x ∧ ∀ z : Fin 42 → Bool, (∀ i, x i = true → z i = true) → ¬P z → z = x) →
          ∃ y : Fin 21 → Bool,
            (∀ p : Fin 21, y p = false → ∃ l : Fin 21, E p l ∧ Z y l = true) ∧
            x = fun i => if i.val < 21 then y (Fin.ofNat 21 i.val) else Z y (Fin.ofNat 21 (i.val - 21))))
    (hbuild :
      let E : Fin 21 → Fin 21 → Prop := fun p l => (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let Z : (Fin 21 → Bool) → Fin 21 → Bool := fun y l =>
        !(y l || y (l + 1) || y (l + 4) || y (l + 14) || y (l + 16))
      let ev (x2 : Fin 42) (x3 x4 : Fin 43) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin 42 → Bool) : Bool :=
        let x8 : Fin 43 → Bool := fun i => Fin.lastCases (x6 0 || x6 x2) x6 i
        x5.eval (List.ofFn fun j : Fin 44 => Fin.lastCases (x8 x3 || x8 x4) x8 j)
      ∃ (x2 : Fin 42) (x3 x4 : Fin 43) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (x2 = 1 ∨ x2 = 21 ∨ x2 = 22) ∧ x3 < x4 ∧
        (x3, x4) ≠ (0, x2.castSucc) ∧
        (x4 = Fin.last 42 → x3 ≠ 0 ∧ x3 ≠ x2.castSucc) ∧
        (∀ x6 : Fin 42, List.count x6.val [0, x2.val, x3.val, x4.val] = 1 → ∃ g ∈ x5.gates, x6.val ∈ g.inputs) ∧
        PEqualNP.MetaComplexity.Monotone2 x5 ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 44 x5 ∧
        x5.size ≤ 122 ∧
        (∀ p l : Fin 21, E p l → ev x2 x3 x4 x5 (fun i => i.val == p.val || i.val == 21 + l.val) = true) ∧
        (∀ y : Fin 21 → Bool,
          (∀ p : Fin 21, y p = false → ∃ l : Fin 21, E p l ∧ Z y l = true) →
          ev x2 x3 x4 x5 (fun i => if i.val < 21 then y (Fin.ofNat 21 i.val) else Z y (Fin.ofNat 21 (i.val - 21))) = false)) :
    have x1 : (Fin (42 : ℕ) → Bool) → Prop := fun (x1 : Fin (42 : ℕ) → Bool) => ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (42 : ℕ)), (↑x2 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x3 ∧ (↑x3 + (21 : ℕ) - ↑x2) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x1 x2 = Bool.true ∧ x1 x3 = Bool.true; ∃ (x2 : Fin (42 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : Fin (43 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (x2 = (1 : Fin (42 : ℕ)) ∨ x2 = (21 : Fin (42 : ℕ)) ∨ x2 = (22 : Fin (42 : ℕ))) ∧     x3 < x4 ∧       (x3, x4) ≠ ((0 : Fin (43 : ℕ)), x2.castSucc) ∧         (x4 = Fin.last (42 : ℕ) → x3 ≠ (0 : Fin (43 : ℕ)) ∧ x3 ≠ x2.castSucc) ∧           (∀ (x6 : Fin (42 : ℕ)), List.count ↑x6 [(0 : ℕ), ↑x2, ↑x3, ↑x4] = (1 : ℕ) → ∃ x8 ∈ x5.gates, ↑x6 ∈ x8.inputs) ∧             PEqualNP.MetaComplexity.Monotone2 x5 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x5 ∧                 x5.size ≤ (122 : ℕ) ∧                   ∀ (x6 : Fin (42 : ℕ) → Bool),                     ((x1 x6 ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x7 x8 = Bool.true → x6 x8 = Bool.true) → x1 x7 → x7 = x6) ∨ ¬x1 x6 ∧ ∀ (x7 : Fin (42 : ℕ) → Bool), (∀ (x8 : Fin (42 : ℕ)), x6 x8 = Bool.true → x7 x8 = Bool.true) → ¬x1 x7 → x7 = x6) →                       have x8 : Fin (43 : ℕ) → Bool := fun (x8 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 (0 : Fin (42 : ℕ)) || x6 x2) x6 x8;                       x5.eval (List.ofFn fun (x9 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 x3 || x8 x4) x8 x9) = Bool.true ↔ x1 x6 := by
  obtain ⟨x2, x3, x4, x5, h2, h34, hne, hlast, hcnt, hmon, hrb, hsz, hpos, hneg⟩ := hbuild
  refine ⟨x2, x3, x4, x5, h2, h34, hne, hlast, hcnt, hmon, hrb, hsz, ?_⟩
  intro x6 hbd
  rcases hbd with hmin | hmax
  · obtain ⟨p, l, he, rfl⟩ := (hchar x6).1 hmin
    exact ⟨fun _ => hmin.1, fun _ => hpos p l he⟩
  · obtain ⟨y, hy, rfl⟩ := (hchar x6).2 hmax
    have hfalse := hneg y hy
    constructor
    · intro ht
      have hbad : false = true := hfalse.symm.trans ht
      cases hbad
    · intro hp
      exact False.elim (hmax.1 hp)
