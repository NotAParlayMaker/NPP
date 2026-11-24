import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 32768 in
theorem PEqualNP.Outside.R_meta_650_773
    (search :
      let near := fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧
        (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let target := fun x : Fin 26 → Bool => decide
        (∃ u v : Fin 26, near u v ∧ x u = true ∧ x v = true)
      let rank := fun (a b c d : ℕ) =>
        (27 * min a b + max a b) * 729 + (27 * min c d + max c d)
      let rename := fun (σ : Equiv.Perm (Fin 26)) (i : Fin 27) =>
        if i.val < 26 then (σ (Fin.ofNat 26 i.val)).val else 26
      ∃ (a b : Fin 26) (c d : Fin 27) (op₁ op₂ : GateOp) (D : Circuit),
        a < b ∧ c < d ∧
        (op₁ = GateOp.and ∨ op₁ = GateOp.or) ∧ (op₂ = GateOp.and ∨ op₂ = GateOp.or) ∧
        (∀ σ : Equiv.Perm (Fin 26), (∀ x, target (x ∘ σ) = target x) →
          rank a.val b.val c.val d.val ≤ rank (σ a).val (σ b).val (rename σ c) (rename σ d)) ∧
        Monotone2 D ∧ D.size ≤ 61 ∧
        ∀ x : Fin 26 → Bool,
          let w := List.ofFn x ++ [op₁.eval [x a,x b]]
          D.eval (w ++ [op₂.eval [w.getD c.val false,w.getD d.val false]]) = target x)
    (prepend : ∀ (n k : ℕ) (a b : Fin n) (c d : Fin (n + 1)) (op₁ op₂ : GateOp),
      (op₁ = GateOp.and ∨ op₁ = GateOp.or) → (op₂ = GateOp.and ∨ op₂ = GateOp.or) →
      ∀ D : Circuit, Monotone2 D → D.size ≤ k →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ k + 2 ∧ ∀ x : Fin n → Bool,
        let w := List.ofFn x ++ [op₁.eval [x a,x b]]
        C.eval (List.ofFn x) = D.eval (w ++ [op₂.eval [w.getD c.val false,w.getD d.val false]])) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨a, b, c, d, op₁, op₂, D, _, _, kind₁, kind₂, _, mono, size, computes⟩ := search
  obtain ⟨C, model, budget, eval⟩ := prepend 26 61 a b c d op₁ op₂ kind₁ kind₂ D mono size
  refine ⟨C, model, budget, ?_⟩
  intro x
  rw [eval x, computes x]
  simp only [decide_eq_true_eq]
  have matching : ∀ u v : Fin 26,
      (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0,1,3,9] : List ℕ)) ↔
      (u.val,v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) := by decide
  simp only [matching]
