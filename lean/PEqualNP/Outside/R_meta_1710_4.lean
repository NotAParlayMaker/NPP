import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Deleting an input pays for its incident edges when enough gates read it.
-- The remaining case only needs graphs whose nonisolated vertices have degree at least nine.
theorem PEqualNP.Outside.R_meta_1710_4
    (peel : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n),
      0 < G.degree v → ∀ C : Circuit, Monotone2 C →
      circuitFun n C = (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) →
      let reads := (C.gates.countP fun g => decide (v.val ∈ g.inputs))
      0 < reads ∧ ∃ D : Circuit, Monotone2 D ∧ D.size + reads ≤ C.size ∧
        circuitFun n D = (fun x => decide
          (∃ i j, (G.deleteIncidenceSet v).Adj i j ∧ x i = true ∧ x j = true)))
    (core : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C →
      circuitFun n C = (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) →
      (∀ v, G.degree v = 0 ∨
        (0 < (C.gates.countP fun g => decide (v.val ∈ g.inputs)) ∧
          8 * (C.gates.countP fun g => decide (v.val ∈ g.inputs)) < G.degree v)) →
      G.edgeFinset.card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) →
      (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 →
      (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) =>
        Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2),
          x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) →
      x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c, bound⟩ := core
  refine ⟨max c 8, ?_⟩
  have aux (s : ℕ) : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, C.size = s → Monotone2 C →
      circuitFun n C = (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeFinset.card ≤ max c 8 * (C.size + 1) := by
    induction s using Nat.strong_induction_on with
    | ind s smaller =>
      intro n G inst hG C hsize hmono hfun
      by_cases cheap : ∃ v : Fin n, 0 < G.degree v ∧
          G.degree v ≤ 8 * (C.gates.countP fun g => decide (v.val ∈ g.inputs))
      · obtain ⟨v, hv, hcost⟩ := cheap
        obtain ⟨hreads, D, hmonoD, hsave, hfunD⟩ := peel n G v hv C hmono hfun
        have inherit (u : Fin n) (p : (G.deleteIncidenceSet v).Walk u u)
            (hp : p.IsCycle) : 5 ≤ p.length := by
          have hle := G.deleteIncidenceSet_le v
          simpa only [SimpleGraph.Walk.length_mapLe] using hG u (p.mapLe hle) (hp.mapLe hle)
        have hlt : D.size < s := by omega
        have hrest := smaller D.size hlt n (G.deleteIncidenceSet v) inherit D rfl hmonoD hfunD
        have hcard : G.edgeFinset.card = (G.deleteIncidenceSet v).edgeFinset.card + G.degree v := by
          have hsub := G.card_edgeFinset_deleteIncidenceSet v
          have hdegree : G.degree v ≤ G.edgeFinset.card := by
            rw [← G.card_incidenceFinset_eq_degree v]
            exact Finset.card_le_card (G.incidenceFinset_subset v)
          omega
        have hcharge := hcost.trans (Nat.mul_le_mul_right _ (le_max_right c 8))
        have hsaving : (D.size + 1) + (C.gates.countP fun g => decide (v.val ∈ g.inputs))
            ≤ C.size + 1 := by omega
        have hsum := Nat.mul_le_mul_left (max c 8) hsaving
        rw [Nat.mul_add] at hsum
        omega
      · have expensive (v : Fin n) : G.degree v = 0 ∨
            (0 < (C.gates.countP fun g => decide (v.val ∈ g.inputs)) ∧
              8 * (C.gates.countP fun g => decide (v.val ∈ g.inputs)) < G.degree v) := by
          by_cases zero : G.degree v = 0
          · exact Or.inl zero
          · have hv := Nat.pos_of_ne_zero zero
            exact Or.inr ⟨(peel n G v hv C hmono hfun).1,
              Nat.lt_of_not_ge (fun h => cheap ⟨v, hv, h⟩)⟩
        exact (bound n G hG C hmono hfun expensive).trans
          (Nat.mul_le_mul_right _ (le_max_left c 8))
  intro n G inst _ hG C hmono hfun
  exact aux C.size n G hG C rfl hmono hfun
