import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A normalized gate has a three-valued opcode and two five-bit-range addresses.
-- Address 24 always reads false on ten inputs and at most fourteen gates.
-- AND and OR have ordered operands. NOT uses only its first operand.
-- Row r stores the nine independent inputs in its low bits, with the control at bit four.
-- The target word records the required output on all 512 rows, least significant row first.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2040_8
    (normalize :
      let decode := fun (p : Fin 3 × Fin 25 × Fin 25) =>
        if p.1 = 0 then Gate.mk .and [p.2.1.val, p.2.2.val]
        else if p.1 = 1 then Gate.mk .or [p.2.1.val, p.2.2.val]
        else Gate.mk .not [p.2.1.val]
      ∀ C : Circuit, FanInTwo C → C.size ≤ 14 →
      C.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
        (fun i => i == 4 || i == 9)) ≤ 1 →
      ∃ (k : Fin 15) (p : Fin k.val → Fin 3 × Fin 25 × Fin 25) (o : Fin 25),
        (∀ j, if (p j).1 = 2 then (p j).2.2 = 24 else (p j).2.1 ≤ (p j).2.2) ∧
        (List.ofFn p).countP (fun a => (decode a).inputs.any (fun i => i == 4 || i == 9)) ≤ 1 ∧
        ∀ y : Fin 10 → Bool, (⟨(List.ofFn p).map decode, o.val⟩ : Circuit).eval (List.ofFn y) = C.eval (List.ofFn y))
    (search :
      let bit : ℕ → ℕ → Bool := Nat.testBit
      let decode := fun (p : Fin 3 × Fin 25 × Fin 25) =>
        if p.1 = 0 then Gate.mk .and [p.2.1.val, p.2.2.val]
        else if p.1 = 1 then Gate.mk .or [p.2.1.val, p.2.2.val]
        else Gate.mk .not [p.2.1.val]
      ∀ (k : Fin 15) (p : Fin k.val → Fin 3 × Fin 25 × Fin 25),
        (∀ j, if (p j).1 = 2 then (p j).2.2 = 24 else (p j).2.1 ≤ (p j).2.2) →
        (List.ofFn p).countP (fun a => (decode a).inputs.any (fun i => i == 4 || i == 9)) ≤ 1 →
        ∀ o : Fin 25, ∃ r : Fin 512,
          (⟨(List.ofFn p).map decode, o.val⟩ : Circuit).eval
            ((List.ofFn fun i : Fin 9 => bit r.val i.val) ++ [!(bit r.val 4)]) ≠
          bit 13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 r.val) :
    have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (0 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x2, x3 (4 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (6 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), !x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) => x3 (0 : Fin (8 : ℕ)) && x3 (1 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (2 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (3 : Fin (8 : ℕ)) || x3 (0 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)) || x3 (1 : Fin (8 : ℕ)) && x3 (5 : Fin (8 : ℕ)) || x3 (2 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (3 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (4 : Fin (8 : ℕ)) && x3 (6 : Fin (8 : ℕ)) || x3 (5 : Fin (8 : ℕ)) && x3 (7 : Fin (8 : ℕ)) || x3 (7 : Fin (8 : ℕ)) && x3 (4 : Fin (8 : ℕ)); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → List.countP x1 x4.gates ≤ (1 : ℕ) → (∀ (x8 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.false x8) = x3 x8) → ∃ (x9 : Fin (8 : ℕ) → Bool), x4.eval (x2 Bool.true x9) ≠ (x3 x9 || x9 (0 : Fin (8 : ℕ)) || x9 (3 : Fin (8 : ℕ))) := by
  dsimp only
  intro C fan size reads low
  by_contra! high
  obtain ⟨k,p,o,ordered,one,sim⟩ := normalize C fan size reads
  obtain ⟨r,bad⟩ := search k p ordered one o
  let x (r : Fin 512) (i : Fin 8) := r.val.testBit (if i.val < 4 then i.val else i.val + 1)
  let lo (x : Fin 8 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)
  let row (b : Bool) (x : Fin 8 → Bool) :=
    [x 0, x 1, x 2, x 3, b, x 4, x 5, x 6, x 7, !b]
  change ∀ z, C.eval (row false z) = lo z at low
  change ∀ z, C.eval (row true z) = (lo z || z 0 || z 3) at high
  have target : ∀ s : Fin 512,
      (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit s.val =
        (if s.val.testBit 4 then lo (x s) || x s 0 || x s 3 else lo (x s)) := by
    decide +kernel
  let y (i : Fin 10) := if i.val < 9 then r.val.testBit i.val else !r.val.testBit 4
  have align : (List.ofFn fun i : Fin 9 => r.val.testBit i.val) ++ [!r.val.testBit 4] =
      List.ofFn y := rfl
  have splitRow : List.ofFn y = row (r.val.testBit 4) (x r) := rfl
  apply bad
  rw [align, sim y, splitRow, target r]
  cases b : r.val.testBit 4
  · exact low (x r)
  · exact high (x r)
