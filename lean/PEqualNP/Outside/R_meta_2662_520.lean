import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2662_520
    (packing : ∀ (n : ℕ) (u v : Fin n) (P : Finset (Fin n × Fin n)) (T : Finset (Fin n)),
      let support : Fin n × Fin n → Finset (Fin n) := fun p => {p.1,p.2} \ {u,v}
      (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (support p) (support q)) →
      (∀ p ∈ P, (support p).Nonempty → ¬ Disjoint T (support p)) →
      P.card ≤ T.card + 4)
    (bound : ∃ k K : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C →
      circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∀ E ⊆ G.edgeFinset,
      (∀ e ∈ E, ∀ u v : Fin n, e = s(u,v) →
        ∀ j : Fin C.gates.length, Owns n C j.val u v →
        let val := fun p q : Fin n => gateVal n C j.val (pairInput p q) = true
        let S := fun p q : Fin n => ({p,q} : Finset (Fin n)) \ {u,v}
        val u u ∨ val v v ∨
          ∀ T : Finset (Fin n),
            (∀ p q : Fin n, val p q → ¬ G.Adj p q → (S p q).Nonempty → ¬ Disjoint T (S p q)) →
            k ≤ T.card) →
      E.card ≤ K * (C.size + 1)) :∃ (x1 : ℕ) (x2 : ℕ),   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj],     (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →       (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 →             PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ →               ∀ x11 ⊆ x4.edgeFinset,                 (∀ x13 ∈ x11,                     ∀ (x15 x16 : Fin x3),                       x13 = s(x15, x16) →                         ∀ (x18 : Fin x8.gates.length),                           PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 →                             have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true;                             have x21 : Fin x3 × Fin x3 → Finset (Fin x3) := fun (x21 : Fin x3 × Fin x3) => {x21.1, x21.2} \ {x15, x16};                             x20 x15 x15 ∨ x20 x16 x16 ∨ ∃ (x22 : Finset (Fin x3 × Fin x3)), x22.card = x1 + (3 : ℕ) ∧ (∀ x23 ∈ x22, x20 x23.1 x23.2 ∧ ¬x4.Adj x23.1 x23.2) ∧ ∀ x23 ∈ x22, ∀ x25 ∈ x22, x23 ≠ x25 → Disjoint (x21 x23) (x21 x25)) →                   x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  obtain ⟨k,K,count⟩ := bound
  refine ⟨k+1,K,?_⟩
  intro n G _ degree girth C least computes E sub selected
  apply count n G degree girth C least computes E sub
  intro e he u v eq j owner
  rcases selected e he u v eq j owner with hx | hy | ⟨P,card,valid,separate⟩
  · exact Or.inl hx
  · exact Or.inr (Or.inl hy)
  · apply Or.inr
    apply Or.inr
    intro T hit
    have c := packing n u v P T separate (fun p hp hn =>
      hit p.1 p.2 (valid p hp).1 (valid p hp).2 hn)
    omega