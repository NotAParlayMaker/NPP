import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3074_319
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.gates.countP (fun g => g.op.eval [Bool.false]) = (0 : ℕ) →
      (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) →
      (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) →
      (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) →
      (15 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.gates.countP (fun g => g.op.eval [Bool.false]) = (1 : ℕ) →
      (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) →
      (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) →
      (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) →
      (15 : ℕ) ≤ x1.size)
    (h3 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      (2 : ℕ) ≤ x1.gates.countP (fun g => g.op.eval [Bool.false]) →
      (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) →
      (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) →
      (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) →
      (15 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ))])) → (∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ))]) ≠ x1.eval (List.ofFn x4 ++ [Bool.false])) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (∀ x6 ∈ [(0 : ℕ), (3 : ℕ)], (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => [x6, (9 : ℕ)].any fun (x9 : ℕ) => (if x8.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x8.inputs else x8.inputs).contains x9) x1.gates).length ≤ (2 : ℕ)) → (15 : ℕ) ≤ x1.size := by
  intro x1 hfit hd1 hd2 heval hread
  by_cases h0 : x1.gates.countP (fun g => g.op.eval [Bool.false]) = (0 : ℕ)
  · exact h1 x1 hfit h0 hd1 hd2 heval hread
  · by_cases h1c : x1.gates.countP (fun g => g.op.eval [Bool.false]) = (1 : ℕ)
    · exact h2 x1 hfit h1c hd1 hd2 heval hread
    · exact h3 x1 hfit (by omega) hd1 hd2 heval hread
