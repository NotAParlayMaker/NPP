import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_582_901
    (search :
      let E : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let target := fun x : Fin 14 → Bool => decide
        (∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true)
      ∃ (op : GateOp) (a b : ℕ) (D : Circuit),
        (op = GateOp.and ∨ op = GateOp.or) ∧
        a ≤ 13 + D.size ∧ b ≤ 13 + D.size ∧
        Monotone2 D ∧ D.size ≤ 25 ∧
        ∀ x : Fin 14 → Bool,
          op.eval [(D.wires (List.ofFn x)).getD a false,
            (D.wires (List.ofFn x)).getD b false] = target x)
    (append : ∀ (op : GateOp) (a b : ℕ) (D : Circuit),
        (op = GateOp.and ∨ op = GateOp.or) → Monotone2 D → D.size ≤ 25 →
        a ≤ 13 + D.size → b ≤ 13 + D.size →
        ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 26 ∧
          ∀ x : Fin 14 → Bool,
            C.eval (List.ofFn x) =
              op.eval [(D.wires (List.ofFn x)).getD a false,
                (D.wires (List.ofFn x)).getD b false]) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 26 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  dsimp at search
  obtain ⟨op, a, b, D, kind, ha, hb, mono, size, computes⟩ := search
  obtain ⟨C, monoC, sizeC, evalC⟩ := append op a b D kind mono size ha hb
  refine ⟨C, monoC, sizeC, ?_⟩
  intro x
  rw [evalC x, computes x]
  simp only [decide_eq_true_eq]
