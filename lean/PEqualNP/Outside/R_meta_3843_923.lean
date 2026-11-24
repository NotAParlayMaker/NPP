import PEqualNP.Defs

-- The gate translation can use fold_tg and bits from Glue in L_meta_3855.
-- The second hypothesis is the checked graph bound L_meta_1676.
theorem PEqualNP.Outside.R_meta_3843_923
    (translate :
      ∀ (f : (Fin 9 → Bool) → Bool) (a b out : Fin 26)
        (tail : List (Fin 3 × Fin 26 × Fin 26)), tail.length ≤ 13 →
        (∀ m < 512,
          let x : Fin 9 → Bool := fun i => m.testBit i.val
          let read (w : List Bool) (i : Fin 26) :=
            if i.val = 25 then true else w.getD i.val false
          let wires := ((1, a, b) :: tail).foldl (fun w g =>
            w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
              else if g.1.val = 1 then read w g.2.1 || read w g.2.2
              else !read w g.2.1]) (List.ofFn x ++ [x 0 || x 4])
          wires.getD out.val false = f x) →
        ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo C ∧
          (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) ∧
          PEqualNP.MetaComplexity.circuitFun 9 C = f ∧ C.size ≤ 15)
    (firstWireBound :
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
        (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4)) →
        PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
        16 ≤ C.size) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) → Prop := fun (x2 x3 x4 : Fin (26 : ℕ)) (x5 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))) =>   ∀ x6 < (512 : ℕ),     have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x6.testBit ↑x8;     have x9 : List Bool → Fin (26 : ℕ) → Bool := fun (x9 : List Bool) (x10 : Fin (26 : ℕ)) => if ↑x10 = (25 : ℕ) then Bool.true else x9.getD (↑x10) Bool.false;     have x10 : List Bool := List.foldl (fun (x10 : List Bool) (x11 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x10 ++ [if ↑x11.1 = (0 : ℕ) then x9 x10 x11.2.1 && x9 x10 x11.2.2 else if ↑x11.1 = (1 : ℕ) then x9 x10 x11.2.1 || x9 x10 x11.2.2 else !x9 x10 x11.2.1]) (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x2, x3) :: x5);     x10.getD (↑x4) Bool.false = x1 x8; have x3 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x3 x4 : Fin (26 : ℕ)) => ↑x3 < (9 : ℕ) ∧ ↑x4 < (9 : ℕ) ∧ Nat.testBit (2305843017923426382 : ℕ) ((9 : ℕ) * ↑x3 + ↑x4) = Bool.true; ∀ (x4 x5 x6 : Fin (26 : ℕ)) (x7 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))), x7.length ≤ (13 : ℕ) → x3 x4 x5 → ¬x2 x4 x5 x6 x7 := by
  dsimp only
  intro a b out tail small _ agrees
  let f := fun x : Fin 9 → Bool =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  obtain ⟨C, legal, first, computes, budget⟩ := translate f a b out tail small agrees
  have same : f = (fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] <;> rfl
  exact (by decide : ¬ 16 ≤ 15) ((firstWireBound C legal first (computes.trans same)).trans budget)
