import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection
open PEqualNP.HeptadCover

-- Pinning an input false makes each direct AND reader false and each direct OR reader a copy or false.
-- The first child is the incidence form of pinCircuit in L_meta_1708. The all-false assignment supplies its witness.
-- Measure a vertex by distinct reader gates. Count a gate reading it twice only once.
-- If deleting a vertex loses at most k edges per reader, the saved gates pay for those edges.
-- Re-minimize after each deletion. At the stopping case, the sparse reader condition holds for every minimum circuit.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_1999_23
    (pin : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit),
      Monotone2 C → ComputesIncidence S C → ∀ v : ℕ, v < n + m →
      ∃ D : Circuit, Monotone2 D ∧
        ComputesIncidence (fun l => (S l).filter fun p => p.val ≠ v ∧ n + l.val ≠ v) D ∧
        D.size + C.gates.countP (fun g => decide (v ∈ g.inputs)) ≤ C.size)
    (core : ∃ k b : ℕ, 4 ≤ k ∧ ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)),
      PEqualNP.ReadTwo.Lin (fun p l => p ∈ S l) →
      (∀ C : Circuit, Monotone2 C → ComputesIncidence S C →
        (∀ B : Circuit, Monotone2 B → ComputesIncidence S B → C.size ≤ B.size) →
        ∀ v : ℕ, v < n + m →
        let deg := ((incidences S).filter fun e => e.1.val = v ∨ n + e.2.val = v).card
        0 < deg → k * C.gates.countP (fun g => decide (v ∈ g.inputs)) < deg) →
      ∀ C : Circuit, Monotone2 C → ComputesIncidence S C → (incidences S).card ≤ b * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ x1 * (x9.size + (1 : ℕ)) := by
  classical
  obtain ⟨k, b, _, hard⟩ := core
  let A := max k b
  refine ⟨A, ?_⟩
  intro n m R dec _ _ square C mono computes
  let S₀ := fun l : Fin m => Finset.univ.filter fun p : Fin n => R p l
  have initial : ComputesIncidence S₀ C := by
    intro X Y
    change C.eval (List.ofFn (fun p => decide (p ∈ X)) ++ List.ofFn (fun l => decide (l ∈ Y))) =
      decide (∃ p ∈ X, ∃ l ∈ Y, p ∈ S₀ l)
    rw [computes]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, S₀, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, l, edge, hx, hy⟩; exact ⟨p, hx, l, hy, edge⟩
    · rintro ⟨p, hx, l, hy, edge⟩; exact ⟨p, l, edge, hx, hy⟩
  have linear : PEqualNP.ReadTwo.Lin (fun p l => p ∈ S₀ l) := by
    intro p q u v pq uv contra
    have rel {i j} (h : i ∈ S₀ j) : R i j := (Finset.mem_filter.mp h).2
    exact (square p q u v (rel contra.1) (rel contra.2.1) (rel contra.2.2.1) (rel contra.2.2.2)).elim pq uv
  have solve (e : ℕ) (S : Fin m → Finset (Fin n)) (edgeCount : (incidences S).card = e)
      (lin : PEqualNP.ReadTwo.Lin (fun p l => p ∈ S l)) (D : Circuit)
      (ok : Monotone2 D) (correct : ComputesIncidence S D) : e ≤ A * (D.size + 1) := by
    induction e using Nat.strong_induction_on generalizing S D with
    | ind e smaller =>
      let degree := fun (v : ℕ) =>
        ((incidences S).filter fun edge => edge.1.val = v ∨ n + edge.2.val = v).card
      let readers := fun (B : Circuit) (v : ℕ) =>
        B.gates.countP (fun g => decide (v ∈ g.inputs))
      by_cases last : ∀ B : Circuit, Monotone2 B → ComputesIncidence S B →
          (∀ H : Circuit, Monotone2 H → ComputesIncidence S H → B.size ≤ H.size) →
          ∀ v : ℕ, v < n + m → 0 < degree v → k * readers B v < degree v
      · rw [← edgeCount]
        exact (hard n m S lin last D ok correct).trans (Nat.mul_le_mul_right _ (Nat.le_max_right k b))
      · push Not at last
        obtain ⟨B, okB, correctB, least, v, vlt, active, cheap⟩ := last
        let T := fun l : Fin m => (S l).filter fun p => p.val ≠ v ∧ n + l.val ≠ v
        have linT : PEqualNP.ReadTwo.Lin (fun p l => p ∈ T l) := by
          intro p q u w pq uw h
          exact lin p q u w pq uw ⟨(Finset.mem_filter.mp h.1).1, (Finset.mem_filter.mp h.2.1).1,
            (Finset.mem_filter.mp h.2.2.1).1, (Finset.mem_filter.mp h.2.2.2).1⟩
        obtain ⟨H, okH, correctH, saved⟩ := pin n m S B okB correctB v vlt
        change H.size + readers B v ≤ B.size at saved
        change ComputesIncidence T H at correctH
        have after : incidences T = (incidences S).filter
            (fun edge => ¬ (edge.1.val = v ∨ n + edge.2.val = v)) := by
          ext edge
          change edge ∈ Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ T e.2) ↔
            edge ∈ (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ S e.2)).filter _
          simp [T, not_or]
        have counts : degree v + (incidences T).card = e := by
          rw [after, ← edgeCount]
          exact Finset.card_filter_add_card_filter_not _
        have low := smaller (incidences T).card (by omega) T rfl linT H okH correctH
        have paid : degree v ≤ A * readers B v :=
          cheap.trans (Nat.mul_le_mul_right _ (Nat.le_max_left k b))
        calc
          e = (incidences T).card + degree v := by omega
          _ ≤ A * (H.size + 1) + A * readers B v := Nat.add_le_add low paid
          _ = A * (H.size + readers B v + 1) := by rw [← Nat.mul_add]; congr 1; omega
          _ ≤ A * (D.size + 1) := Nat.mul_le_mul_left _ (by have := least D ok correct; omega)
  have result := solve _ S₀ rfl linear C mono initial
  have tally : (incidences S₀).card = ∑ p : Fin n, (Finset.univ.filter (R p)).card := by
    change (Finset.univ.filter (fun e : Fin n × Fin m => e.1 ∈ S₀ e.2)).card = _
    rw [← Finset.univ_product_univ, Finset.card_filter, Finset.sum_product]
    simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_filter]
  rwa [tally] at result
