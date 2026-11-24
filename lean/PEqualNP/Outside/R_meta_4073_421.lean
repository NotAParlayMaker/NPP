import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4073_421
    (boundary :
      let edge := fun x : Fin 10 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
          fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
      let w := fun (C : Circuit) (a : ℕ) (x : Fin 10 → Bool) =>
        (C.wires (List.ofFn x ++ [!x 0])).getD a false
      let row := fun (m : ℕ) (i : Fin 10) => m.testBit i.val
      ∀ (C : Circuit) (a b : ℕ), Monotone2 C →
        (∀ x, (w C a x && w C b x) = edge x) →
        (∃ x, w C a x = true ∧ w C b x = false) →
        ∃ m ∈ ([50, 69, 104, 116, 138, 200, 201, 208, 276, 385, 402, 521, 548,
          554, 770, 772, 773] : List ℕ), w C a (row m) = true ∧ w C b (row m) = false)
    (monotoneCase :
      let w := fun (C : Circuit) (a m : ℕ) =>
        let x := fun i : Fin 10 => m.testBit i.val
        (C.wires (List.ofFn x ++ [!x 0])).getD a false
      let pos : List ℕ := [3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265,
        288, 320, 321, 528, 576, 577, 640, 641]
      let neg : List ℕ := [50, 69, 104, 116, 138, 200, 201, 208, 276, 385, 402, 521,
        548, 554, 770, 772, 773]
      ∀ (C : Circuit) (a b : ℕ), Monotone2 C → C.size ≤ 17 →
        (∀ m ∈ pos, (w C a m && w C b m) = true) →
        (∀ m ∈ neg, (w C a m && w C b m) = false) →
        (∃ m ∈ neg, w C a m = true ∧ w C b m = false) →
        (∃ m ∈ neg, w C b m = true ∧ w C a m = false) → False)
    (signedCase :
      let edge := fun x : Fin 10 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
          fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
      let w := fun (C : Circuit) (a : ℕ) (x : Fin 10 → Bool) =>
        (C.wires (List.ofFn x ++ [!x 0])).getD a false
      ∀ (C : Circuit) (a b : ℕ), FanInTwo C → C.size ≤ 17 →
        (∃ g ∈ C.gates, g.op = .not) →
        (∃ x, w C a x = true ∧ w C b x = false) →
        (∃ x, w C b x = true ∧ w C a x = false) →
        (∀ x, (w C a x && w C b x) = edge x) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       have x6 : (Fin (10 : ℕ) → Bool) → Bool := fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ));       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x1.wires (List.ofFn x7 ++ [!x7 (0 : Fin (10 : ℕ))])).getD x8 Bool.false;       (∃ (x8 : Fin (10 : ℕ) → Bool), x7 x8 x2 = Bool.true ∧ x7 x8 x3 = Bool.false) → (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x2 = Bool.false ∧ x7 x9 x3 = Bool.true) → (∀ (x10 : Fin (10 : ℕ) → Bool), x6 x10 = Bool.true → x7 x10 x2 = Bool.true ∧ x7 x10 x3 = Bool.true) → ∃ (x11 : Fin (10 : ℕ) → Bool), x6 x11 = Bool.false ∧ x7 x11 x2 = Bool.true ∧ x7 x11 x3 = Bool.true := by
  intro C a b hFan hs
  dsimp only
  intro hx hy hAccept
  let edge := fun x : Fin 10 → Bool =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any
      fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
  let w := fun (C : Circuit) (a : ℕ) (x : Fin 10 → Bool) =>
    (C.wires (List.ofFn x ++ [!x 0])).getD a false
  let row := fun (m : ℕ) (i : Fin 10) => m.testBit i.val
  have edgeEq (x : Fin 10 → Bool) : edge x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    simp only [edge, List.any_cons, List.any_nil, Bool.or_assoc, Bool.or_false]; rfl
  by_contra hBad
  have hExact : ∀ x, (w C a x && w C b x) = edge x := by
    intro x
    cases he : edge x with
    | false =>
      cases ht : w C a x && w C b x with
      | false => rfl
      | true =>
        obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp ht
        exact False.elim (hBad ⟨x, (edgeEq x).symm.trans he, ha, hb⟩)
    | true => exact Bool.and_eq_true_iff.mpr (hAccept x ((edgeEq x).symm.trans he))
  by_cases hMono : Monotone2 C
  · have w1 := boundary C a b hMono hExact hx
    have w2 := boundary C b a hMono (fun x => (Bool.and_comm _ _).trans (hExact x))
      (by obtain ⟨x, ha, hb⟩ := hy; exact ⟨x, hb, ha⟩)
    have posCheck : ([3, 6, 12, 13, 17, 24, 33, 66, 132, 133, 160, 264, 265, 288,
      320, 321, 528, 576, 577, 640, 641] : List ℕ).all (fun m => edge (row m)) = true := by
      decide
    have negCheck : ([50, 69, 104, 116, 138, 200, 201, 208, 276, 385, 402, 521, 548,
      554, 770, 772, 773] : List ℕ).all (fun m => !(edge (row m))) = true := by
      decide
    apply monotoneCase C a b hMono hs _ _ w1 w2
    · intro m hm
      exact (hExact (row m)).trans (List.all_eq_true.mp posCheck m hm)
    · intro m hm
      have h := List.all_eq_true.mp negCheck m hm
      exact (hExact (row m)).trans (by simpa using h)
  · have hNot : ∃ g ∈ C.gates, g.op = .not := by
      by_contra h
      apply hMono
      intro g hg
      have hOps : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hFan g hg).1
      obtain ha | ho | hn := hOps
      · exact ⟨by simp [ha], (hFan g hg).2⟩
      · exact ⟨by simp [ho], (hFan g hg).2⟩
      · exact False.elim (h ⟨g, hg, hn⟩)
    exact signedCase C a b hFan hs hNot hx
      (by obtain ⟨x, ha, hb⟩ := hy; exact ⟨x, hb, ha⟩) hExact
