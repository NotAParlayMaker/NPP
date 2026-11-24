import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_3841_421
    (relabel :
      let rename := fun (p : Fin 9 → Fin 9) (i : Fin 26) =>
      if h : i.val < 9 then Fin.ofNat 26 (p ⟨i.val, h⟩).val else i
    let read := fun (s : List Bool) (i : Fin 26) =>
      if i.val = 25 then true else s.getD i.val false
    let push := fun (s : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
      s ++ [if g.1.val = 0 then read s g.2.1 && read s g.2.2 else
        if g.1.val = 1 then read s g.2.1 || read s g.2.2 else !read s g.2.1]
    let run := fun (x : Fin 9 → Bool) (z : Fin 26) (gs : List (Fin 3 × Fin 26 × Fin 26)) =>
      (gs.foldl push (List.ofFn x ++ [x 0 || x 4])).getD z.val false
    ∀ (p : Fin 9 → Fin 9), p 0 = 0 → p 4 = 4 →
      ∀ (x : Fin 9 → Bool) (z : Fin 26) (gs : List (Fin 3 × Fin 26 × Fin 26)),
        run (x ∘ p) z gs = run x (rename p z)
          (gs.map fun g => (g.1, rename p g.2.1, rename p g.2.2)))
    (remaining :
      have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 (Fin.insertNth (4 : Fin ((8 : ℕ) + (1 : ℕ))) Bool.false x2); have x3 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) → Prop := fun (x3 x4 x5 : Fin (26 : ℕ)) (x6 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))) =>   ∀ x7 < (512 : ℕ),     have x9 : Fin (9 : ℕ) → Bool := fun (x9 : Fin (9 : ℕ)) => x7.testBit ↑x9;     have x10 : List Bool → Fin (26 : ℕ) → Bool := fun (x10 : List Bool) (x11 : Fin (26 : ℕ)) => if ↑x11 = (25 : ℕ) then Bool.true else x10.getD (↑x11) Bool.false;     have x11 : List Bool := List.foldl (fun (x11 : List Bool) (x12 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x11 ++ [if ↑x12.1 = (0 : ℕ) then x10 x11 x12.2.1 && x10 x11 x12.2.2 else if ↑x12.1 = (1 : ℕ) then x10 x11 x12.2.1 || x10 x11 x12.2.2 else !x10 x11 x12.2.1]) (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x3, x4) :: x6);     x11.getD (↑x5) Bool.false = x1 x9;
      let exceptional := fun (a b : Fin 26) =>
      9 ≤ a.val ∨ 9 ≤ b.val ∨ a = b ∨
      a.val = 4 ∧ b.val ∈ ([0, 2, 3, 6, 7, 8] : List Nat) ∨
      b.val = 4 ∧ a.val ∈ ([0, 2, 3, 6, 7, 8] : List Nat)
      ∀ (a b z : Fin 26) (gs : List (Fin 3 × Fin 26 × Fin 26)),
        gs.length ≤ 13 → a.val ≠ 9 → b.val ≠ 9 → a.val ≠ 25 → b.val ≠ 25 →
        exceptional a b → x3 a b z gs →
        PEqualNP.MetaComplexity.HasCircuitSize 9 x1 14 ∨
        PEqualNP.MetaComplexity.HasCircuitSize 8 x2 12) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 (Fin.insertNth (4 : Fin ((8 : ℕ) + (1 : ℕ))) Bool.false x2); have x3 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) → Prop := fun (x3 x4 x5 : Fin (26 : ℕ)) (x6 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))) =>   ∀ x7 < (512 : ℕ),     have x9 : Fin (9 : ℕ) → Bool := fun (x9 : Fin (9 : ℕ)) => x7.testBit ↑x9;     have x10 : List Bool → Fin (26 : ℕ) → Bool := fun (x10 : List Bool) (x11 : Fin (26 : ℕ)) => if ↑x11 = (25 : ℕ) then Bool.true else x10.getD (↑x11) Bool.false;     have x11 : List Bool := List.foldl (fun (x11 : List Bool) (x12 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x11 ++ [if ↑x12.1 = (0 : ℕ) then x10 x11 x12.2.1 && x10 x11 x12.2.2 else if ↑x12.1 = (1 : ℕ) then x10 x11 x12.2.1 || x10 x11 x12.2.2 else !x10 x11 x12.2.1]) (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x3, x4) :: x6);     x11.getD (↑x5) Bool.false = x1 x9; have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (9 : ℕ) ∧ ↑x5 < (9 : ℕ) ∧ Nat.testBit (2305843017923426382 : ℕ) ((9 : ℕ) * ↑x4 + ↑x5) = Bool.true; ∀ (x5 x6 x7 : Fin (26 : ℕ)) (x8 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))), x8.length ≤ (13 : ℕ) → ↑x5 ≠ (9 : ℕ) → ↑x6 ≠ (9 : ℕ) → ↑x5 ≠ (25 : ℕ) → ↑x6 ≠ (25 : ℕ) → x3 x5 x6 x7 x8 → PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ) ∨ PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x2 (12 : ℕ) ∨ ∃ (x15 : Fin (26 : ℕ)) (x16 : Fin (26 : ℕ)) (x17 : Fin (26 : ℕ)) (x18 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))), x18.length ≤ (13 : ℕ) ∧ x4 x15 x16 ∧ x3 x15 x16 x17 x18 := by
  let x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))
  let x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 (Fin.insertNth (4 : Fin ((8 : ℕ) + (1 : ℕ))) Bool.false x2)
  let x3 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) → Prop := fun (x3 x4 x5 : Fin (26 : ℕ)) (x6 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))) =>   ∀ x7 < (512 : ℕ),     have x9 : Fin (9 : ℕ) → Bool := fun (x9 : Fin (9 : ℕ)) => x7.testBit ↑x9;     have x10 : List Bool → Fin (26 : ℕ) → Bool := fun (x10 : List Bool) (x11 : Fin (26 : ℕ)) => if ↑x11 = (25 : ℕ) then Bool.true else x10.getD (↑x11) Bool.false;     have x11 : List Bool := List.foldl (fun (x11 : List Bool) (x12 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x11 ++ [if ↑x12.1 = (0 : ℕ) then x10 x11 x12.2.1 && x10 x11 x12.2.2 else if ↑x12.1 = (1 : ℕ) then x10 x11 x12.2.1 || x10 x11 x12.2.2 else !x10 x11 x12.2.1]) (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x3, x4) :: x6);     x11.getD (↑x5) Bool.false = x1 x9
  let x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (9 : ℕ) ∧ ↑x5 < (9 : ℕ) ∧ Nat.testBit (2305843017923426382 : ℕ) ((9 : ℕ) * ↑x4 + ↑x5) = Bool.true
  let exceptional := fun (a b : Fin 26) =>
      9 ≤ a.val ∨ 9 ≤ b.val ∨ a = b ∨
      a.val = 4 ∧ b.val ∈ ([0, 2, 3, 6, 7, 8] : List Nat) ∨
      b.val = 4 ∧ a.val ∈ ([0, 2, 3, 6, 7, 8] : List Nat)
  let rename := fun (p : Fin 9 → Fin 9) (i : Fin 26) =>
      if h : i.val < 9 then Fin.ofNat 26 (p ⟨i.val, h⟩).val else i
  let read := fun (s : List Bool) (i : Fin 26) =>
      if i.val = 25 then true else s.getD i.val false
  let push := fun (s : List Bool) (g : Fin 3 × Fin 26 × Fin 26) =>
      s ++ [if g.1.val = 0 then read s g.2.1 && read s g.2.2 else
        if g.1.val = 1 then read s g.2.1 || read s g.2.2 else !read s g.2.1]
  let run := fun (x : Fin 9 → Bool) (z : Fin 26) (gs : List (Fin 3 × Fin 26 × Fin 26)) =>
      (gs.foldl push (List.ofFn x ++ [x 0 || x 4])).getD z.val false
  let symmetry (v : Fin 9) : Fin 9 :=
    ([0, 5, 8, 3, 4, 1, 7, 6, 2] : List (Fin 9)).getD v.val 0
  let choose (useSymmetry : Bool) (v : Fin 9) : Fin 9 :=
    bif useSymmetry then symmetry v else v
  have fixed0 (useSymmetry : Bool) : choose useSymmetry 0 = 0 := by
    cases useSymmetry <;> decide
  have fixed4 (useSymmetry : Bool) : choose useSymmetry 4 = 4 := by
    cases useSymmetry <;> decide
  have graphInvariant : ∀ n : Fin 512,
      x1 (fun v => n.val.testBit (symmetry v).val) = x1 (fun v => n.val.testBit v.val) := by
    dsimp only [x1, symmetry]
    decide +kernel
  have classified : ∀ a b : Fin 26, exceptional a b ∨
      ∃ useSymmetry flip : Bool,
        x4 (rename (choose useSymmetry) (bif flip then b else a))
          (rename (choose useSymmetry) (bif flip then a else b)) := by
    dsimp only [x4, exceptional, rename, choose, symmetry]
    decide +kernel
  change ∀ (x5 x6 x7 : Fin (26 : ℕ)) (x8 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))), x8.length ≤ (13 : ℕ) → ↑x5 ≠ (9 : ℕ) → ↑x6 ≠ (9 : ℕ) → ↑x5 ≠ (25 : ℕ) → ↑x6 ≠ (25 : ℕ) → x3 x5 x6 x7 x8 → PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ) ∨ PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x2 (12 : ℕ) ∨ ∃ (x15 : Fin (26 : ℕ)) (x16 : Fin (26 : ℕ)) (x17 : Fin (26 : ℕ)) (x18 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))), x18.length ≤ (13 : ℕ) ∧ x4 x15 x16 ∧ x3 x15 x16 x17 x18
  intro a b z gs size ha9 hb9 ha25 hb25 correct
  rcases classified a b with bad | ⟨useSymmetry, flip, valid⟩
  · exact (remaining a b z gs size ha9 hb9 ha25 hb25 bad correct).elim
      Or.inl (fun h => Or.inr (Or.inl h))
  · let p := choose useSymmetry
    let l := bif flip then b else a
    let r := bif flip then a else b
    let mapped := gs.map fun g => (g.1, rename p g.2.1, rename p g.2.2)
    have swapped (x : Fin 9 → Bool) :
        run x z ((1, l, r) :: gs) = run x z ((1, a, b) :: gs) := by
      cases flip <;> simp [run, push, l, r, Bool.or_comm]
    refine Or.inr (Or.inr ⟨rename p l, rename p r, rename p z, mapped, ?_, valid, ?_⟩)
    · simpa [mapped] using size
    · intro row hrow
      let x : Fin 9 → Bool := fun i => row.testBit i.val
      change run x (rename p z) ((1, rename p l, rename p r) :: mapped) = x1 x
      have hRelabel := relabel p (fixed0 useSymmetry) (fixed4 useSymmetry) x z ((1, l, r) :: gs)
      change run (x ∘ p) z ((1, l, r) :: gs) =
        run x (rename p z) ((1, rename p l, rename p r) :: mapped) at hRelabel
      rw [← hRelabel, swapped]
      let packed := BitVec.ofBoolListLE (List.ofFn (x ∘ p))
      have packedInRange : packed.toNat < 512 := by
        simpa only [List.length_ofFn] using packed.isLt
      have packedReads : (fun i : Fin 9 => packed.toNat.testBit i.val) = x ∘ p := by
        funext i
        change (BitVec.ofBoolListLE (List.ofFn (x ∘ p))).toNat.testBit i.val = (x ∘ p) i
        rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
          List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      have eval := correct packed.toNat packedInRange
      change run (fun i : Fin 9 => packed.toNat.testBit i.val) z ((1, a, b) :: gs) =
        x1 (fun i : Fin 9 => packed.toNat.testBit i.val) at eval
      rw [packedReads] at eval
      rw [eval]
      cases useSymmetry with
      | false => rfl
      | true => exact graphInvariant ⟨row, hrow⟩

