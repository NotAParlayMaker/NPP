import Mathlib
import PEqualNP.Defs

-- Count OR gates and AND gates separately: a circuit of AND and OR gates for the edge function
-- of the Heawood graph has at least 20 OR gates (21 edges less one) and at least 7 AND gates
-- (the cover number), so at least 27 gates. Point i lies on the lines -i, 1 - i, 3 - i (mod 7);
-- the table in the statement lists exactly those pairs.
theorem PEqualNP.Outside.R_meta_971_7 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ((List.range 7).flatMap (fun i : ℕ => [(i, 7 + (7 - i) % 7), (i, 7 + (8 - i) % 7), (i, 7 + (10 - i) % 7)])) ∧ x u = true ∧ x v = true)) → 20 ≤ {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ((List.range 7).flatMap (fun i : ℕ => [(i, 7 + (7 - i) % 7), (i, 7 + (8 - i) % 7), (i, 7 + (10 - i) % 7)])) ∧ x u = true ∧ x v = true)) → 7 ≤ {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 27 ≤ C.size := by
  intro hor hand C hmono hcomp
  have key : List.Perm ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ))
      ((List.range 7).flatMap (fun i : ℕ => [(i, 7 + (7 - i) % 7), (i, 7 + (8 - i) % 7), (i, 7 + (10 - i) % 7)])) := by
    decide
  simp only [key.mem_iff] at hcomp
  have e1 := hor C hmono hcomp
  have e2 := hand C hmono hcomp
  have hdisj : Disjoint {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}
      {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
    rw [Set.disjoint_left]
    intro i ha hb
    rw [Set.mem_ofPred_eq] at ha hb
    rw [ha] at hb
    exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion hb
  have hsum := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : ({i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or} ∪
      {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}).ncard ≤
      C.gates.length := by
    calc _ ≤ (Set.univ : Set (Fin C.gates.length)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = C.gates.length := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hs : C.size = C.gates.length := rfl
  omega
