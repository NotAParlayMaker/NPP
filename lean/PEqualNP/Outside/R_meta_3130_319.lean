import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3130_319
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) →
      x1.gates.countP (fun g => g.op.eval [Bool.false]) = (0 : ℕ) →
      have x4 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) => x4.inputs[(0 : ℕ)]? = Option.some x5 ∨ x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x4.inputs;
      (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)], ∃! x7 : Fin x1.gates.length, x4 (x1.gates.get x7) x5) →
      ∀ (x6 : Finset (Fin x1.gates.length)), x6.card + (11 : ℕ) ≤ x1.size →
      (∀ x8 ∉ x6, ∀ x10 ∈ [(4 : ℕ), (6 : ℕ), (9 : ℕ)], ¬x4 (x1.gates.get x8) x10) →
      (∀ x9 ∉ x6, ∀ x11 ∈ (x1.gates.get x9).inputs, x4 (x1.gates.get x9) x11 →
        have x14 : (Fin (7 : ℕ) → Bool) → Bool := fun (x14 : Fin (7 : ℕ) → Bool) => ({ gates := List.take (↑x9) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires [x14 (4 : Fin (7 : ℕ)), x14 (3 : Fin (7 : ℕ)), x14 (0 : Fin (7 : ℕ)), x14 (5 : Fin (7 : ℕ)), Bool.false, x14 (1 : Fin (7 : ℕ)), Bool.false, x14 (2 : Fin (7 : ℕ)), x14 (6 : Fin (7 : ℕ)), Bool.false]).getD x11 Bool.false;
        ∃ (x15 : Fin (7 : ℕ) → Bool) (x16 : Fin (7 : ℕ) → Bool), x14 x15 ≠ x14 x16) →
      ∃ (x10 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x10 ++ [x10 (4 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ))]) ≠ (fun (x11 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ)))) x10)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) →
      x1.gates.countP (fun g => g.op.eval [Bool.false]) = (1 : ℕ) →
      have x4 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) => x4.inputs[(0 : ℕ)]? = Option.some x5 ∨ x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x4.inputs;
      (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)], ∃! x7 : Fin x1.gates.length, x4 (x1.gates.get x7) x5) →
      ∀ (x6 : Finset (Fin x1.gates.length)), x6.card + (11 : ℕ) ≤ x1.size →
      (∀ x8 ∉ x6, ∀ x10 ∈ [(4 : ℕ), (6 : ℕ), (9 : ℕ)], ¬x4 (x1.gates.get x8) x10) →
      (∀ x9 ∉ x6, ∀ x11 ∈ (x1.gates.get x9).inputs, x4 (x1.gates.get x9) x11 →
        have x14 : (Fin (7 : ℕ) → Bool) → Bool := fun (x14 : Fin (7 : ℕ) → Bool) => ({ gates := List.take (↑x9) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires [x14 (4 : Fin (7 : ℕ)), x14 (3 : Fin (7 : ℕ)), x14 (0 : Fin (7 : ℕ)), x14 (5 : Fin (7 : ℕ)), Bool.false, x14 (1 : Fin (7 : ℕ)), Bool.false, x14 (2 : Fin (7 : ℕ)), x14 (6 : Fin (7 : ℕ)), Bool.false]).getD x11 Bool.false;
        ∃ (x15 : Fin (7 : ℕ) → Bool) (x16 : Fin (7 : ℕ) → Bool), x14 x15 ≠ x14 x16) →
      ∃ (x10 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x10 ++ [x10 (4 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ))]) ≠ (fun (x11 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ)))) x10)
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) →
      (2 : ℕ) ≤ x1.gates.countP (fun g => g.op.eval [Bool.false]) →
      have x4 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) => x4.inputs[(0 : ℕ)]? = Option.some x5 ∨ x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x4.inputs;
      (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)], ∃! x7 : Fin x1.gates.length, x4 (x1.gates.get x7) x5) →
      ∀ (x6 : Finset (Fin x1.gates.length)), x6.card + (11 : ℕ) ≤ x1.size →
      (∀ x8 ∉ x6, ∀ x10 ∈ [(4 : ℕ), (6 : ℕ), (9 : ℕ)], ¬x4 (x1.gates.get x8) x10) →
      (∀ x9 ∉ x6, ∀ x11 ∈ (x1.gates.get x9).inputs, x4 (x1.gates.get x9) x11 →
        have x14 : (Fin (7 : ℕ) → Bool) → Bool := fun (x14 : Fin (7 : ℕ) → Bool) => ({ gates := List.take (↑x9) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires [x14 (4 : Fin (7 : ℕ)), x14 (3 : Fin (7 : ℕ)), x14 (0 : Fin (7 : ℕ)), x14 (5 : Fin (7 : ℕ)), Bool.false, x14 (1 : Fin (7 : ℕ)), Bool.false, x14 (2 : Fin (7 : ℕ)), x14 (6 : Fin (7 : ℕ)), Bool.false]).getD x11 Bool.false;
        ∃ (x15 : Fin (7 : ℕ) → Bool) (x16 : Fin (7 : ℕ) → Bool), x14 x15 ≠ x14 x16) →
      ∃ (x10 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x10 ++ [x10 (4 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ))]) ≠ (fun (x11 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ)))) x10) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (14 : ℕ) →       have x4 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ) => x4.inputs[(0 : ℕ)]? = Option.some x5 ∨ x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5 ∈ x4.inputs;       (∀ x5 ∈ [(4 : ℕ), (6 : ℕ)], ∃! x7 : Fin x1.gates.length, x4 (x1.gates.get x7) x5) →         ∀ (x6 : Finset (Fin x1.gates.length)),           x6.card + (11 : ℕ) ≤ x1.size →             (∀ x8 ∉ x6, ∀ x10 ∈ [(4 : ℕ), (6 : ℕ), (9 : ℕ)], ¬x4 (x1.gates.get x8) x10) →               (∀ x9 ∉ x6,                   ∀ x11 ∈ (x1.gates.get x9).inputs,                     x4 (x1.gates.get x9) x11 →                       have x14 : (Fin (7 : ℕ) → Bool) → Bool := fun (x14 : Fin (7 : ℕ) → Bool) => ({ gates := List.take (↑x9) x1.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires [x14 (4 : Fin (7 : ℕ)), x14 (3 : Fin (7 : ℕ)), x14 (0 : Fin (7 : ℕ)), x14 (5 : Fin (7 : ℕ)), Bool.false, x14 (1 : Fin (7 : ℕ)), Bool.false, x14 (2 : Fin (7 : ℕ)), x14 (6 : Fin (7 : ℕ)), Bool.false]).getD x11 Bool.false;                       ∃ (x15 : Fin (7 : ℕ) → Bool) (x16 : Fin (7 : ℕ) → Bool), x14 x15 ≠ x14 x16) →                 ∃ (x10 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x10 ++ [x10 (4 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ))]) ≠ (fun (x11 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ)))) x10 := by
  intro x1 hfit hsize _x4 huniq x6 hcard hno hnc
  by_cases h0 : x1.gates.countP (fun g => g.op.eval [Bool.false]) = (0 : ℕ)
  · exact h1 x1 hfit hsize h0 huniq x6 hcard hno hnc
  · by_cases h1c : x1.gates.countP (fun g => g.op.eval [Bool.false]) = (1 : ℕ)
    · exact h2 x1 hfit hsize h1c huniq x6 hcard hno hnc
    · exact h3 x1 hfit hsize (by omega) huniq x6 hcard hno hnc
