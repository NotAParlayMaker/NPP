import PEqualNP.Defs

-- L-meta-1667 through L-meta-1669 cover the three pairs of degree-three vertices.
-- L-meta-1670 through L-meta-1672 cover the other three pairs.
theorem PEqualNP.Outside.R_meta_4734_1
    (bothDegreeThree : ∀ b : Fin 9, b = 1 ∨ b = 2 ∨ b = 3 →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y b)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (mixedAdjacent : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (mixedNonAdjacent : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (bothDegreeTwo : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size) :
    ∀ (x1 x2 : Fin (9 : ℕ)), (↑x1, ↑x2) ∈ [((0 : ℕ), (1 : ℕ)), ((0 : ℕ), (2 : ℕ)), ((0 : ℕ), (3 : ℕ)), ((0 : ℕ), (4 : ℕ)), ((0 : ℕ), (6 : ℕ)), ((4 : ℕ), (6 : ℕ))] → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x6 : Fin (9 : ℕ) → Bool), (x4.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = (x6 x1 && x6 x2)) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x4 = fun (x7 : Fin (9 : ℕ) → Bool) => x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x4.size := by
  intro u v pair C fan first computes
  have fixed (a b : Fin 9) (ha : u.val = a.val) (hb : v.val = b.val) :
      ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y a && y b) := by
    simpa only [Fin.ext ha, Fin.ext hb] using first
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at pair
  rcases pair with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact bothDegreeThree 1 (Or.inl rfl) C fan (fixed 0 1 ha hb) computes
  · exact bothDegreeThree 2 (Or.inr (Or.inl rfl)) C fan (fixed 0 2 ha hb) computes
  · exact bothDegreeThree 3 (Or.inr (Or.inr rfl)) C fan (fixed 0 3 ha hb) computes
  · exact mixedAdjacent C fan (fixed 0 4 ha hb) computes
  · exact mixedNonAdjacent C fan (fixed 0 6 ha hb) computes
  · exact bothDegreeTwo C fan (fixed 4 6 ha hb) computes
