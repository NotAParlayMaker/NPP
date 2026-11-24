import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3186_1
    (search :
      ∀ (x1 : Fin 9 → BitVec 24) (x2 x3 : BitVec 24) (C : Circuit) (w : ℕ → BitVec 24),
        (∀ i : Fin 9, w i.val = x1 i) → w 9 = x2 →
        (∀ j < C.size,
          (∃ a < 9 + j, ∃ b < 9 + j,
            w (9 + j) = w a &&& w b ∨ w (9 + j) = w a ||| w b) ∨
          w (9 + j) = 0 ∨ w (9 + j) = -1) →
        w C.output = x3 → x3 ≠ 0 → x3 ≠ -1 →
        ∃ L : List (BitVec 24),
          L.length ≤ C.size - 1 ∧ x3 ∈ List.ofFn x1 ++ [x2] ++ L ∧
          ∀ i : Fin L.length,
            let P := List.ofFn x1 ++ [x2] ++ List.take i.val L
            L.get i ∉ P ∧ L.get i ≠ 0 ∧ L.get i ≠ -1 ∧
            ∃ a ∈ P, ∃ b ∈ P, L.get i = a &&& b ∨ L.get i = a ||| b)
    (bridge :
      ∀ (x1 : Fin 9 → BitVec 24) (x2 x3 : BitVec 24) (C : Circuit),
        let w : ℕ → BitVec 24 := fun r =>
          (BitVec.ofBoolListLE (List.ofFn fun k : Fin 24 =>
            (C.wires (List.ofFn fun i : Fin 9 => (x1 i).getLsbD k.val)).getD r false)).cast (by simp)
        (∀ i : Fin 9, w i.val = x1 i) ∧ w 9 = x2 ∧
        (∀ j < C.size,
          (∃ a < 9 + j, ∃ b < 9 + j,
            w (9 + j) = w a &&& w b ∨ w (9 + j) = w a ||| w b) ∨
          w (9 + j) = 0 ∨ w (9 + j) = -1) ∧
        w C.output = x3) :
    ∀ (x1 : Fin (9 : ℕ) → BitVec (24 : ℕ)) (x2 x3 : BitVec (24 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     x3 ≠ (0 : BitVec (24 : ℕ)) →       x3 ≠ (-1 : BitVec (24 : ℕ)) →         (∀ (x8 : Fin (24 : ℕ)),             have x9 : Fin (9 : ℕ) → Bool := fun (x9 : Fin (9 : ℕ)) => (x1 x9).getLsbD ↑x8;             (x4.wires (List.ofFn x9)).getD (9 : ℕ) Bool.false = x2.getLsbD ↑x8 ∧ x4.eval (List.ofFn x9) = x3.getLsbD ↑x8) →           have x9 : List (BitVec (24 : ℕ)) := List.ofFn x1 ++ [x2];           ∃ (x10 : List (BitVec (24 : ℕ))),             x10.length ≤ x4.size - (1 : ℕ) ∧               x3 ∈ x9 ++ x10 ∧                 ∀ (x11 : Fin x10.length),                   have x12 : List (BitVec (24 : ℕ)) := x9 ++ List.take (↑x11) x10;                   x10.get x11 ∉ x12 ∧ x10.get x11 ≠ (0 : BitVec (24 : ℕ)) ∧ x10.get x11 ≠ (-1 : BitVec (24 : ℕ)) ∧ ∃ x13 ∈ x12, ∃ x14 ∈ x12, x10.get x11 = x13 &&& x14 ∨ x10.get x11 = x13 ||| x14 := by
  intro x1 x2 x3 C _ hx0 hxall _
  let w : ℕ → BitVec 24 := fun r =>
    (BitVec.ofBoolListLE (List.ofFn fun k : Fin 24 =>
      (C.wires (List.ofFn fun i : Fin 9 => (x1 i).getLsbD k.val)).getD r false)).cast (by simp)
  have b := bridge x1 x2 x3 C
  dsimp only at b
  exact search x1 x2 x3 C w b.1 b.2.1 b.2.2.1 b.2.2.2 hx0 hxall
