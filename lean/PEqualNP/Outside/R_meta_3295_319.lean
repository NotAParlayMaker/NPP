import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3295_319
    (h1 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ));
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.FanInTwo x3 →
        x2.size + x3.size ≤ (13 : ℕ) → (8 : ℕ) ≤ x4 → x4 < (8 : ℕ) + x2.size →
        Option.map PEqualNP.CircuitLowerBounds.Gate.op x2.gates[x4 - (8 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and →
        have x10 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x10 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x10);
        have x11 : (Fin (8 : ℕ) → Bool) → Bool := fun (x11 : Fin (8 : ℕ) → Bool) => (x10 x11).getD x4 Bool.false;
        (∀ (x12 : Fin (8 : ℕ) → Bool), x1 x12 = Bool.false → (x12 (0 : Fin (8 : ℕ)) || x12 (3 : Fin (8 : ℕ))) = Bool.true → x11 x12 = Bool.true) →
        (∀ (x13 : Fin (8 : ℕ) → Bool), x3.eval (x10 x13 ++ [x11 x13]) = x1 x13) →
        ∃ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x10 x14 ++ [Bool.false]) ≠ (x1 x14 || x14 (0 : Fin (8 : ℕ)) || x14 (3 : Fin (8 : ℕ))))
    (h2 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ));
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.FanInTwo x3 →
        x2.size + x3.size ≤ (13 : ℕ) → (8 : ℕ) ≤ x4 → x4 < (8 : ℕ) + x2.size →
        Option.map PEqualNP.CircuitLowerBounds.Gate.op x2.gates[x4 - (8 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or →
        have x10 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x10 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x10);
        have x11 : (Fin (8 : ℕ) → Bool) → Bool := fun (x11 : Fin (8 : ℕ) → Bool) => (x10 x11).getD x4 Bool.false;
        (∀ (x12 : Fin (8 : ℕ) → Bool), x1 x12 = Bool.false → (x12 (0 : Fin (8 : ℕ)) || x12 (3 : Fin (8 : ℕ))) = Bool.true → x11 x12 = Bool.true) →
        (∀ (x13 : Fin (8 : ℕ) → Bool), x3.eval (x10 x13 ++ [x11 x13]) = x1 x13) →
        ∃ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x10 x14 ++ [Bool.false]) ≠ (x1 x14 || x14 (0 : Fin (8 : ℕ)) || x14 (3 : Fin (8 : ℕ))))
    (h3 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ));
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.FanInTwo x3 →
        x2.size + x3.size ≤ (13 : ℕ) → (8 : ℕ) ≤ x4 → x4 < (8 : ℕ) + x2.size →
        Option.map PEqualNP.CircuitLowerBounds.Gate.op x2.gates[x4 - (8 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not →
        have x10 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x10 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x10);
        have x11 : (Fin (8 : ℕ) → Bool) → Bool := fun (x11 : Fin (8 : ℕ) → Bool) => (x10 x11).getD x4 Bool.false;
        (∀ (x12 : Fin (8 : ℕ) → Bool), x1 x12 = Bool.false → (x12 (0 : Fin (8 : ℕ)) || x12 (3 : Fin (8 : ℕ))) = Bool.true → x11 x12 = Bool.true) →
        (∀ (x13 : Fin (8 : ℕ) → Bool), x3.eval (x10 x13 ++ [x11 x13]) = x1 x13) →
        ∃ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x10 x14 ++ [Bool.false]) ≠ (x1 x14 || x14 (0 : Fin (8 : ℕ)) || x14 (3 : Fin (8 : ℕ)))) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         (8 : ℕ) ≤ x4 →           x4 < (8 : ℕ) + x2.size →             have x10 : (Fin (8 : ℕ) → Bool) → List Bool := fun (x10 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x10);             have x11 : (Fin (8 : ℕ) → Bool) → Bool := fun (x11 : Fin (8 : ℕ) → Bool) => (x10 x11).getD x4 Bool.false;             (∀ (x12 : Fin (8 : ℕ) → Bool), x1 x12 = Bool.false → (x12 (0 : Fin (8 : ℕ)) || x12 (3 : Fin (8 : ℕ))) = Bool.true → x11 x12 = Bool.true) → (∀ (x13 : Fin (8 : ℕ) → Bool), x3.eval (x10 x13 ++ [x11 x13]) = x1 x13) → ∃ (x14 : Fin (8 : ℕ) → Bool), x3.eval (x10 x14 ++ [Bool.false]) ≠ (x1 x14 || x14 (0 : Fin (8 : ℕ)) || x14 (3 : Fin (8 : ℕ))) := by
  intro _x1 x2 x3 x4 hf2 hf3 hsum hge8 hlt _x10 _x11 hcond heval
  have hidx : x4 - 8 < x2.gates.length := by
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hlt
    omega
  have hget : x2.gates[x4 - 8]? = some (x2.gates[x4 - 8]) := List.getElem?_eq_getElem hidx
  have hmem : x2.gates[x4 - 8] ∈ x2.gates := List.getElem_mem hidx
  rcases (hf2 _ hmem).1 with hop | hop | hop
  · exact h1 x2 x3 x4 hf2 hf3 hsum hge8 hlt (by rw [hget]; simp [hop]) hcond heval
  · exact h2 x2 x3 x4 hf2 hf3 hsum hge8 hlt (by rw [hget]; simp [hop]) hcond heval
  · exact h3 x2 x3 x4 hf2 hf3 hsum hge8 hlt (by rw [hget]; simp [Set.mem_singleton_iff.mp hop]) hcond heval
