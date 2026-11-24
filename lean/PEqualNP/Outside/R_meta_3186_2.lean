import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3186_2
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
      ∀ (x1 : Fin 9 → BitVec 24) (C : Circuit), Monotone2 C →
        let w : ℕ → BitVec 24 := fun r =>
          BitVec.ofBoolListLE (List.ofFn fun k : Fin 24 =>
            (C.wires (List.ofFn fun i : Fin 9 => (x1 i).getLsbD k.val)).getD r false)
        (∀ i : Fin 9, w i.val = x1 i) ∧
        ∀ j < C.size,
          (∃ a < 9 + j, ∃ b < 9 + j,
            w (9 + j) = w a &&& w b ∨ w (9 + j) = w a ||| w b) ∨
          w (9 + j) = 0 ∨ w (9 + j) = -1) :
    ∀ (x1 : Fin (9 : ℕ) → BitVec (24 : ℕ)) (x2 x3 : BitVec (24 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     x3 ≠ (0 : BitVec (24 : ℕ)) →       x3 ≠ (-1 : BitVec (24 : ℕ)) →         (∀ (x8 : Fin (24 : ℕ)),             have x9 : Fin (9 : ℕ) → Bool := fun (x9 : Fin (9 : ℕ)) => (x1 x9).getLsbD ↑x8;             (x4.wires (List.ofFn x9)).getD (9 : ℕ) Bool.false = x2.getLsbD ↑x8 ∧ x4.eval (List.ofFn x9) = x3.getLsbD ↑x8) →           have x9 : List (BitVec (24 : ℕ)) := List.ofFn x1 ++ [x2];           ∃ (x10 : List (BitVec (24 : ℕ))),             x10.length ≤ x4.size - (1 : ℕ) ∧               x3 ∈ x9 ++ x10 ∧                 ∀ (x11 : Fin x10.length),                   have x12 : List (BitVec (24 : ℕ)) := x9 ++ List.take (↑x11) x10;                   x10.get x11 ∉ x12 ∧ x10.get x11 ≠ (0 : BitVec (24 : ℕ)) ∧ x10.get x11 ≠ (-1 : BitVec (24 : ℕ)) ∧ ∃ x13 ∈ x12, ∃ x14 ∈ x12, x10.get x11 = x13 &&& x14 ∨ x10.get x11 = x13 ||| x14 := by
  intro x1 x2 x3 C hmono hx0 hxall hbits
  let w : ℕ → BitVec 24 := fun r =>
    (BitVec.ofBoolListLE (List.ofFn fun k : Fin 24 =>
      (C.wires (List.ofFn fun i : Fin 9 => (x1 i).getLsbD k.val)).getD r false)).cast (by simp)
  have hb := bridge x1 C hmono
  dsimp only at hb
  have hwin : ∀ i : Fin 9, w i.val = x1 i := hb.1
  have hwgate : ∀ j < C.size,
      (∃ a < 9 + j, ∃ b < 9 + j,
        w (9 + j) = w a &&& w b ∨ w (9 + j) = w a ||| w b) ∨
      w (9 + j) = 0 ∨ w (9 + j) = -1 := hb.2
  have hw9 : w 9 = x2 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    dsimp [w]
    rw [BitVec.getLsbD_cast]
    rw [BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    rw [List.getElem_ofFn]
    convert (hbits ⟨k, hk⟩).1 using 1
  have hwout : w C.output = x3 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    dsimp [w]
    rw [BitVec.getLsbD_cast]
    rw [BitVec.getLsbD_ofBoolListLE]
    rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    rw [List.getElem_ofFn]
    change C.eval (List.ofFn fun i : Fin 9 => (x1 i).getLsbD k) = x3.getLsbD k
    convert (hbits ⟨k, hk⟩).2 using 1
  exact search x1 x2 x3 C w hwin hw9 hwgate hwout hx0 hxall
