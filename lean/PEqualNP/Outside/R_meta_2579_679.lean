import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2579_679
    (compileRect : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit), IsAO2 n C → circuitFun n C = graphFun G ∅ → G.edgeFinset.Nonempty →
    ∃ R : Finset (Set (Fin n × Fin n) × Set (Set (Fin n))), R.card ≤ C.size ∧
    ∀ D : Set (Set (Fin n × Fin n) × Set (Set (Fin n))),
      (∀ v : Fin n, ({p | v = p.1 ∨ v = p.2}, {s | v ∉ s}) ∈ D) →
      (∀ r ∈ R, ∀ a ∈ D, ∀ b ∈ D,
        (∀ p ∈ r.1, ∀ s ∈ r.2, (p ∈ a.1 ∧ s ∈ a.2) ∨ (p ∈ b.1 ∧ s ∈ b.2)) → r ∈ D) →
      ∃ r ∈ D, (∀ u v, G.Adj u v → (u,v) ∈ r.1) ∧
        ∀ s : Set (Fin n), (∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v) → s ∈ r.2)
    (rectBound : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
    ∀ R : Finset (Set (Fin n × Fin n) × Set (Set (Fin n))), (∀ D : Set (Set (Fin n × Fin n) × Set (Set (Fin n))),
      (∀ v : Fin n, ({p | v = p.1 ∨ v = p.2}, {s | v ∉ s}) ∈ D) →
      (∀ r ∈ R, ∀ a ∈ D, ∀ b ∈ D,
        (∀ p ∈ r.1, ∀ s ∈ r.2, (p ∈ a.1 ∧ s ∈ a.2) ∨ (p ∈ b.1 ∧ s ∈ b.2)) → r ∈ D) →
      ∃ r ∈ D, (∀ u v, G.Adj u v → (u,v) ∈ r.1) ∧
        ∀ s : Set (Fin n), (∀ u ∈ s, ∀ v ∈ s, ¬ G.Adj u v) → s ∈ r.2) →
    G.edgeFinset.card ≤ k * (R.card + 1)) :
∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [_x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k,hk⟩ := rectBound
  refine ⟨k,?_⟩
  intro n G _ hg he C hl _
  obtain ⟨R,hR,hgen⟩ := compileRect n G C hl.1 hl.2.1 he
  have hsub : Ustar G C ⊆ G.edgeFinset := Finset.sdiff_subset
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    ((Finset.card_le_card hsub).trans ((hk n G hg R hgen).trans
      (Nat.mul_le_mul_left k (by omega))))
