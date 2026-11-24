import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_582_8
    (search :
      let E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let target := fun x : Fin 14 → Bool => decide
        (∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true)
      ∃ (u v : Fin 14) (op : GateOp) (D : Circuit),
        (u.val, v.val) ∈ ([(0, 7), (0, 1), (0, 9)] : List (ℕ × ℕ)) ∧
        (op = GateOp.and ∨ op = GateOp.or) ∧
        Monotone2 D ∧ D.size ≤ 25 ∧
        ∀ x : Fin 14 → Bool,
          D.eval (List.ofFn x ++ [op.eval [x u, x v]]) = target x)
    (prepend : ∀ (n k : ℕ) (u v : Fin n) (op : GateOp),
      (op = GateOp.and ∨ op = GateOp.or) →
      ∀ D : Circuit, Monotone2 D → D.size ≤ k →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ k + 1 ∧ ∀ x : Fin n → Bool,
        C.eval (List.ofFn x) = D.eval (List.ofFn x ++ [op.eval [x u, x v]])) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 26 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨u, v, op, D, _, kind, mono, size, computes⟩ := search
  obtain ⟨C, model, budget, eval⟩ := prepend 14 25 u v op kind D mono size
  refine ⟨C, model, budget, ?_⟩
  intro x
  rw [eval x, computes x]
  simp only [decide_eq_true_eq]
