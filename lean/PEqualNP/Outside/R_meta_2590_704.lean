import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each signal is represented by the rows on which it is true.
-- Union and intersection add a signal only when its column is new.
-- Rows zero through fourteen are the edges in the target expression.
-- The remaining rows are the maximal independent sets in increasing mask order.
theorem PEqualNP.Outside.R_meta_2590_704
    (normalize : ∀ (m n : ℕ) (cols : Fin n → Finset (Fin m)) (C : Circuit), Monotone2 C →
      let S := insert (∅ : Finset (Fin m)) (insert Finset.univ (Finset.univ.image cols))
      ∃ T, Relation.ReflTransGen (fun S T : Finset (Finset (Fin m)) =>
        T ≠ S ∧ ∃ a ∈ S, ∃ b ∈ S, T = insert (a ∪ b) S ∨ T = insert (a ∩ b) S) S T ∧
        T.card ≤ S.card + C.size ∧
        ∃ out ∈ T, ∀ r : Fin m, r ∈ out ↔ C.eval (List.ofFn (fun i => decide (r ∈ cols i))) = true)
    (search : let cols : Fin 10 → Finset (Fin 30) := fun i => Finset.univ.filter (fun r : Fin 30 =>
        (([579928113, 419987523, 608501894, 169476364, 23364120, 201770016, 3616832, 28839040, 834691328, 1040194048] : List Nat).getD i.val 0).testBit r.val = true)
      let S := insert (∅ : Finset (Fin 30)) (insert Finset.univ (Finset.univ.image cols))
      ∀ T, Relation.ReflTransGen (fun S T : Finset (Finset (Fin 30)) =>
        T ≠ S ∧ ∃ a ∈ S, ∃ b ∈ S, T = insert (a ∪ b) S ∨ T = insert (a ∩ b) S) S T →
        T.card ≤ S.card + 19 → ∀ out ∈ T, ¬(∀ r : Fin 30, r ∈ out ↔ r.val < 15)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ¬∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C legal bound computed
  let cols : Fin 10 → Finset (Fin 30) := fun i => Finset.univ.filter (fun r : Fin 30 =>
        (([579928113, 419987523, 608501894, 169476364, 23364120, 201770016, 3616832, 28839040, 834691328, 1040194048] : List Nat).getD i.val 0).testBit r.val = true)
  let graph (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  have rows : ∀ r : Fin 30, graph (fun i => decide (r ∈ cols i)) = decide (r.val < 15) := by
    simp only [cols,Finset.mem_filter,Finset.mem_univ,true_and,Bool.decide_eq_true]
    decide +kernel
  obtain ⟨T,reach,size,out,present,meaning⟩ := normalize 30 10 cols C legal
  apply search T reach (size.trans (Nat.add_le_add_left bound _)) out present
  intro r
  rw [meaning,computed]
  change (graph (fun i => decide (r∈cols i)) = true) ↔ r.val < 15
  rw [rows,decide_eq_true_eq]
