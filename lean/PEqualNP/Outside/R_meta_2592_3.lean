import Mathlib
import PEqualNP.Defs

-- The extra input occupies the wire vacated by the first gate.
-- If simplification drops a gate, the shortened circuit can ignore a free negated input.
theorem PEqualNP.Outside.R_meta_2592_3
    (h1 : ∀ f : (Fin 10 → Bool) → Bool, f (fun _ => false) = false →
      (∀ i j : Fin 10, i ≠ j → ∃ σ : Equiv.Perm (Fin 10),
        σ i = 0 ∧ (σ j = 1 ∨ σ j = 2) ∧ ∀ x, f (x ∘ σ) = f x) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
        (∃ g ∈ C.gates, g.op = .not) → (∀ x, C.eval (List.ofFn x) = f x) →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (op : PEqualNP.CircuitLowerBounds.GateOp)
          (j : Fin 10), PEqualNP.MetaComplexity.FanInTwo D ∧ D.size < C.size ∧
          (j = 1 ∨ j = 2) ∧ (op = .not ∨ op = .and ∨ op = .or) ∧
          (op ≠ .not → ∃ g ∈ D.gates, g.op = .not) ∧
          ∀ x, D.eval (List.ofFn x ++ [op.eval [x 0, x j]]) = f x)
    (h2 :
      let f := fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ i j : Fin 10, i ≠ j → ∃ σ : Equiv.Perm (Fin 10),
        σ i = 0 ∧ (σ j = 1 ∨ σ j = 2) ∧ ∀ x, f (x ∘ σ) = f x)
    (h3 :
      let f := fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        D.size ≤ 18 → ∃ x, D.eval (List.ofFn x ++ [!x 0]) ≠ f x)
    (h4 :
      let f := fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (op : PEqualNP.CircuitLowerBounds.GateOp)
        (j : Fin 10), PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 18 →
        (∃ g ∈ D.gates, g.op = .not) → (op = .and ∨ op = .or) → (j = 1 ∨ j = 2) →
        ∃ x, D.eval (List.ofFn x ++ [op.eval [x 0, x j]]) ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (19 : ℕ) → (∃ x4 ∈ x1.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬∀ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C fan budget hasNot correct
  let f := fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  obtain ⟨D, op, j, fanD, smaller, pair, basis, keepsNot, computes⟩ :=
    h1 f rfl h2 C fan hasNot correct
  have budgetD : D.size ≤ 18 := by omega
  rcases basis with rfl | binary
  · obtain ⟨x, mismatch⟩ := h3 D fanD budgetD
    exact mismatch (computes x)
  · have neNot : op ≠ .not := by
      intro eqNot
      rcases binary with rfl | rfl <;> cases eqNot
    obtain ⟨x, mismatch⟩ := h4 D op j fanD budgetD (keepsNot neNot) binary pair
    exact mismatch (computes x)
