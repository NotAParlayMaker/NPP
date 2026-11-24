import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4844_613
    (forceRead : let read := fun (g : Gate) (w : ℕ) =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i=w))
      ∀ (p s : List Gate) (g : Gate) (o : ℕ) (a b : List Bool),
      let C : Circuit := ⟨p++g::s,o⟩
      FanInTwo C → (∀ k ∈ p++s, read k 6 = false) → a.length=b.length →
      (∀ i ≠ 6, a.getD i false = b.getD i false) → o ≠ 6 → o ≠ a.length+p.length →
      C.eval a ≠ C.eval b → a.length+p.length < o ∧ o < a.length+p.length+s.length+1 ∧
      ∃ k ∈ s, read k (a.length+p.length) = true)
    (rawOr : ∀ (p s : List Gate) (g : Gate) (o : ℕ) (a : List Bool),
      6 < a.length → a.getD 6 false = true → g.op = .or → 6 ∈ g.inputs →
      (o=6 ∨ o=a.length+p.length) → (Circuit.mk (p++g::s) o).eval a = true)
    (exclude : let read := fun (g : Gate) (w : ℕ) =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i=w))
      let low := fun i : ℕ => ([18369897887404062920,18446740762289764600,18446744073709551560,
        18446744073709551608].getD (i/64) (0 : ℕ)).testBit (i%64)
      let row := fun i : ℕ => fun j : Fin 8 => i.testBit j.val
      let x := fun (b : Bool) (i : ℕ) =>
        [i.testBit 1,i.testBit 0,i.testBit 4,i.testBit 7,i.testBit 5,i.testBit 2,b,
          i.testBit 6,i.testBit 3,i.testBit 1 || b]
      ∀ (p s : List Gate) (g : Gate) (o : ℕ),
      let C : Circuit := ⟨p++g::s,o⟩
      FanInTwo C → p.length+s.length ≤ 13 → (∀ k ∈ p++s, read k 6 = false) →
      read g 6 = true → g.op = .or →
      (10+p.length < o ∧ o < 10+p.length+s.length+1 ∧ ∃ k ∈ s, read k (10+p.length) = true) →
      (∀ i < 256, (List.ofFn (row i)).count true ≤ 2 ∨ low i = false ∨ i=255 →
        C.eval (x false i) = low i ∧ C.eval (x true i) = (low i || i.testBit 0 || i.testBit 3)) →
      (∀ i ∈ [10,26,74], g.op.eval (g.inputs.map fun j => ((Circuit.mk p 0).wires (x false i)).getD j false) = false) → False) :
have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : ℕ → Bool := fun (x3 : ℕ) => ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x3 / (64 : ℕ)) (0 : ℕ)).testBit (x3 % (64 : ℕ)); have x4 : ℕ → Fin (8 : ℕ) → Bool := fun (x4 : ℕ) (x5 : Fin (8 : ℕ)) => x4.testBit ↑x5; ∀ (x5 x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : ℕ),   have x9 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x5 ++ x7 :: x6, output := x8 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x9 → x5.length + x6.length ≤ (13 : ℕ) → (∀ x12 ∈ x5 ++ x6, x1 x12 = Bool.false) → x1 x7 = Bool.true → x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∀ x15 < (256 : ℕ), List.count Bool.true (List.ofFn (x4 x15)) ≤ (2 : ℕ) ∨ x3 x15 = Bool.false ∨ x15 = (255 : ℕ) → x9.eval (x2 Bool.false (x4 x15)) = x3 x15 ∧ x9.eval (x2 Bool.true (x4 x15)) = (x3 x15 || x4 x15 (0 : Fin (8 : ℕ)) || x4 x15 (3 : Fin (8 : ℕ)))) → (∀ x16 ∈ [(10 : ℕ), (26 : ℕ), (74 : ℕ)], x7.op.eval (List.map (fun (x18 : ℕ) => ({ gates := x5, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x2 Bool.false (x4 x16))).getD x18 Bool.false) x7.inputs) = Bool.false) → False := by
  dsimp only
  intro p s g o fit budget misses reads op tests quiet
  let row := fun (b : Bool) (i : ℕ) =>
    [i.testBit 1,i.testBit 0,i.testBit 4,i.testBit 7,i.testBit 5,i.testBit 2,b,
      i.testBit 6,i.testBit 3,i.testBit 1 || b]
  let C : Circuit := ⟨p++g::s,o⟩
  have oneBit (i : ℕ) (hne : i ≠ 6) : (row false 10).getD i false = (row true 10).getD i false := by
    by_cases inrange : i < 10
    · interval_cases i <;> first | contradiction | rfl
    · rw [List.getD_eq_default _ _ (by simpa [row] using Nat.le_of_not_gt inrange),
        List.getD_eq_default _ _ (by simpa [row] using Nat.le_of_not_gt inrange)]
  have pivot : C.eval (row false 10) ≠ C.eval (row true 10) := by
    have at10 := tests 10 (by decide) (Or.inl (by decide))
    have low : C.eval (row false 10) = false := at10.1.trans (by decide)
    have high : C.eval (row true 10) = true := at10.2.trans (by decide)
    rw [low,high]
    decide
  have zero : C.eval (row true 0) = false := by
    have at0 := tests 0 (by decide) (Or.inl (by decide))
    exact at0.2.trans (by decide)
  have appears : 6 ∈ g.inputs := by
    have gate0 : g.op.eval [false,false] = false := by
      rw [op] <;> rfl
    have hit : g.inputs.any (fun i => decide (i=6)) = true := by
      simpa only [gate0,Bool.false_eq_true,if_false] using reads
    obtain ⟨i,hi,e⟩ := List.any_eq_true.mp hit
    exact (of_decide_eq_true e) ▸ hi
  have output (h : o=6 ∨ o=10+p.length) : False := by
    have yes := rawOr p s g o (row true 0) (by decide) (by decide) op appears h
    exact Bool.noConfusion (zero.symm.trans yes)
  have live := forceRead p s g o (row false 10) (row true 10) fit misses rfl oneBit
    (fun h => output (Or.inl h)) (fun h => output (Or.inr h)) pivot
  exact exclude p s g o fit budget misses reads op live tests quiet
