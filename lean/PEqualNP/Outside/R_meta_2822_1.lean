import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2822_1
    (hreader : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) C →
    (let f : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (b : Bool) (y : Fin (8 : ℕ) → Bool) => C.eval ((List.ofFn y).insertIdx (↑x3 : ℕ) b);
      ∃ (y1 : Fin (8 : ℕ) → Bool) (y2 : Fin (8 : ℕ) → Bool), f Bool.false y1 ≠ f Bool.false y2) →
    (let f : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (b : Bool) (y : Fin (8 : ℕ) → Bool) => C.eval ((List.ofFn y).insertIdx (↑x3 : ℕ) b);
      ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (f Bool.false) s → C.size ≤ s + (1 : ℕ)) →
    ∃ j : Fin C.size,
      (let r : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (i : Fin (9 : ℕ)) (g : PEqualNP.CircuitLowerBounds.Gate) => (if g.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) g.inputs else g.inputs).contains (↑i : ℕ); r x3 (C.gates.get j) = Bool.true) ∧
      ∀ j' : Fin C.size,
        (let r : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (i : Fin (9 : ℕ)) (g : PEqualNP.CircuitLowerBounds.Gate) => (if g.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) g.inputs else g.inputs).contains (↑i : ℕ); r x3 (C.gates.get j') = Bool.true) → j' = j)
    (hgate : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) C →
    (let f : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (b : Bool) (y : Fin (8 : ℕ) → Bool) => C.eval ((List.ofFn y).insertIdx (↑x3 : ℕ) b);
      ∃ (y1 : Fin (8 : ℕ) → Bool) (y2 : Fin (8 : ℕ) → Bool), f Bool.false y1 ≠ f Bool.false y2) →
    (let f : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (b : Bool) (y : Fin (8 : ℕ) → Bool) => C.eval ((List.ofFn y).insertIdx (↑x3 : ℕ) b);
      ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (f Bool.false) s → C.size ≤ s + (1 : ℕ)) →
    ∀ j : Fin C.size,
      (let r : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (i : Fin (9 : ℕ)) (g : PEqualNP.CircuitLowerBounds.Gate) => (if g.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) g.inputs else g.inputs).contains (↑i : ℕ); r x3 (C.gates.get j) = Bool.true) →
      ∃ w : ℕ, (9 : ℕ) ≤ w ∧ w < (9 : ℕ) + (j.val : ℕ) ∧
        (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ((C.gates.get j).inputs = [(↑x3 : ℕ), w] ∨ (C.gates.get j).inputs = [w, (↑x3 : ℕ)])) : have x1 : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) => (if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs).contains ↑x1; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x2 →     have x5 : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (x5 : Bool) (x6 : Fin (8 : ℕ) → Bool) => x2.eval ((List.ofFn x6).insertIdx (↑x3) x5);     (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x5 Bool.false x6 ≠ x5 Bool.false x7) → (∀ (x7 : Fin (9 : ℕ)), x7 ≠ x3 → ∃ (x9 : Fin (8 : ℕ) → Bool), x5 Bool.false x9 ≠ x5 Bool.true x9 ∧ ((List.ofFn x9).insertIdx (↑x3) Bool.false).getD (↑x7) Bool.false = Bool.true) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (2 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x8 = x5 Bool.false) ∨ ∃ (x8 : Fin x2.size) (x9 : ℕ), (9 : ℕ) ≤ x9 ∧ x9 < (9 : ℕ) + ↑x8 ∧ (x2.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x2.gates.get x8).inputs = [↑x3, x9] ∨ (x2.gates.get x8).inputs = [x9, ↑x3]) ∧ ∀ (x10 : Fin x2.size), x1 x3 (x2.gates.get x10) = Bool.true → x10 = x8 := by
  intro x1 C x3 hmin x5 hvar hsen
  let f : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun b y => C.eval ((List.ofFn y).insertIdx (↑x3 : ℕ) b)
  by_cases hsmall : ∃ (C8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C8 ∧ C8.size + (2 : ℕ) ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) C8 = f Bool.false
  · exact Or.inl (by simpa [f, x5] using hsmall)
  · right
    have hlb : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (f Bool.false) s → C.size ≤ s + (1 : ℕ) := by
      intro s hs
      obtain ⟨D, hD, hDs, hfun⟩ := hs
      have hnot : ¬ D.size + (2 : ℕ) ≤ C.size := by
        intro hle
        exact hsmall ⟨D, hD, hle, by funext y; simpa [f, x5, PEqualNP.MetaComplexity.circuitFun] using hfun y⟩
      omega
    obtain ⟨j, hj, huniq⟩ := hreader C x3 hmin (by simpa [f, x5] using hvar) (by simpa [f, x5] using hlb)
    obtain ⟨w, hw9, hwlt, hop, hin⟩ := hgate C x3 hmin (by simpa [f, x5] using hvar) (by simpa [f, x5] using hlb) j hj
    refine ⟨j, w, hw9, hwlt, hop, hin, ?_⟩
    intro j' hj'
    exact huniq j' (by simpa [x1] using hj')
