import Mathlib.Data.Set.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Count edges whose owner can be made sound on pairs by deleting at most
-- three other vertices. The remaining edges have no such owner.
theorem PEqualNP.Outside.R_meta_1735_37
    (blocked : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C →
      {e ∈ (Ustar G C : Set (Sym2 (Fin n))) | ∃ (u v : Fin n) (j : Fin C.gates.length) (K : Finset (Fin n)),
          e = s(u, v) ∧ K.card ≤ 3 ∧ u ∉ K ∧ v ∉ K ∧ Owns n C j.val u v ∧
          gateVal n C j.val (fun _ => false) = false ∧
          ∀ p q : Fin n, ¬ G.Adj p q →
            gateVal n C j.val (pairInput p q) = true → p ∈ K ∨ q ∈ K}.ncard ≤ 32 * C.size)
    (remaining : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      {e ∈ (Ustar G C : Set (Sym2 (Fin n))) | ¬ (∃ (u v : Fin n) (j : Fin C.gates.length) (K : Finset (Fin n)),
          e = s(u, v) ∧ K.card ≤ 3 ∧ u ∉ K ∧ v ∉ K ∧ Owns n C j.val u v ∧
          gateVal n C j.val (fun _ => false) = false ∧
          ∀ p q : Fin n, ¬ G.Adj p q →
            gateVal n C j.val (pairInput p q) = true → p ∈ K ∨ q ∈ K)}.ncard ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨c, countRemaining⟩ := remaining
  refine ⟨32 + c, ?_⟩
  intro n G x4 girth nonempty C least form
  let hasBlocker (e : Sym2 (Fin n)) : Prop := ∃ (u v : Fin n) (j : Fin C.gates.length) (K : Finset (Fin n)),
          e = s(u, v) ∧ K.card ≤ 3 ∧ u ∉ K ∧ v ∉ K ∧ Owns n C j.val u v ∧
          gateVal n C j.val (fun _ => false) = false ∧
          ∀ p q : Fin n, ¬ G.Adj p q →
            gateVal n C j.val (pairInput p q) = true → p ∈ K ∨ q ∈ K
  have hBlocked : ((Ustar G C).filter hasBlocker).card ≤ 32 * C.size := by
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    exact @blocked n G x4 C girth least
  have hRemaining : ((Ustar G C).filter (fun e => ¬ hasBlocker e)).card ≤ c * (C.size + 1) := by
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    exact @countRemaining n G x4 C girth nonempty least form
  have split := Finset.card_filter_add_card_filter_not (s := Ustar G C) hasBlocker
  rw [← split, Nat.add_mul]
  exact Nat.add_le_add (hBlocked.trans (Nat.mul_le_mul_left 32 (Nat.le_succ _))) hRemaining
