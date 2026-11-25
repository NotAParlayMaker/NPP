import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1764_701
    (hOwned : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.EdgeOwnership.EveryEdgeOwned n G C)
    (hOneHot : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (w : Fin n) (walk : G.Walk w w), walk.IsCycle → 5 ≤ walk.length) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        {e ∈ G.edgeFinset | ∃ (u v : Fin n), e = s(u, v) ∧ ∃ (j : Fin C.gates.length),
          PEqualNP.EdgeOwnership.Owns n C j.val u v ∧
          ∃ (a : Fin n), PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a a) = true}.card
        ≤ c * (C.size + 1))
    (hNonEdge : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v : Fin n, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ (w : Fin n) (walk : G.Walk w w), walk.IsCycle → 5 ≤ walk.length) →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        {e ∈ G.edgeFinset | ∃ (u v : Fin n), e = s(u, v) ∧ ∃ (j : Fin C.gates.length),
          PEqualNP.EdgeOwnership.Owns n C j.val u v ∧
          (∀ (a : Fin n), PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a a) = false) ∧
          ∃ (a b : Fin n), a ≠ b ∧ ¬ G.Adj a b ∧
            PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a b) = true}.card
        ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x2 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ → {x10 ∈ x3.edgeFinset | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ (x13 : Fin x7.gates.length), PEqualNP.EdgeOwnership.Owns x2 x7 (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin x2), PEqualNP.EdgeOwnership.gateVal x2 x7 (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → x3.Adj x14 x15}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨c1, hc1⟩ := hOneHot
  obtain ⟨c2, hc2⟩ := hNonEdge
  refine ⟨c1 + c2, ?_⟩
  intro n G _ hdeg hgirth C hmono hfun
  have h1 := hc1 n G hdeg hgirth C hmono hfun
  have h2 := hc2 n G hdeg hgirth C hmono hfun
  have hev := hOwned n G C hmono hfun
  let S := {x10 ∈ G.edgeFinset | ¬∃ (x11 : Fin n) (x12 : Fin n), x10 = s(x11, x12) ∧ ∃ (x13 : Fin C.gates.length), PEqualNP.EdgeOwnership.Owns n C (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin n), PEqualNP.EdgeOwnership.gateVal n C (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → G.Adj x14 x15}
  let S1 := {e ∈ G.edgeFinset | ∃ (u v : Fin n), e = s(u, v) ∧ ∃ (j : Fin C.gates.length),
    PEqualNP.EdgeOwnership.Owns n C j.val u v ∧
    ∃ (a : Fin n), PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a a) = true}
  let S2 := {e ∈ G.edgeFinset | ∃ (u v : Fin n), e = s(u, v) ∧ ∃ (j : Fin C.gates.length),
    PEqualNP.EdgeOwnership.Owns n C j.val u v ∧
    (∀ (a : Fin n), PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a a) = false) ∧
    ∃ (a b : Fin n), a ≠ b ∧ ¬ G.Adj a b ∧
      PEqualNP.EdgeOwnership.gateVal n C j.val (PEqualNP.EdgeOwnership.pairInput a b) = true}
  have hsub : S ⊆ S1 ∪ S2 := by
    intro e he
    simp only [S, Finset.mem_filter] at he
    rcases he with ⟨hedge, hnotclean⟩
    rcases e with ⟨u, v⟩
    have hadj : G.Adj u v := G.mem_edgeFinset.mp hedge
    obtain ⟨j, hjlt, howns⟩ := hev u v hadj
    by_cases hoh : ∃ a : Fin n, PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput a a) = true
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hedge, u, v, rfl, ⟨j, hjlt⟩, howns, hoh⟩)
    · apply Finset.mem_union_right
      refine Finset.mem_filter.mpr ⟨hedge, u, v, rfl, ⟨j, hjlt⟩, howns, ?_, ?_⟩
      · intro a
        cases hv : PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput a a)
        · rfl
        · exact absurd ⟨a, hv⟩ hoh
      · by_contra hclean
        apply hnotclean
        refine ⟨u, v, rfl, ⟨j, hjlt⟩, howns, ?_⟩
        intro a b hab
        by_contra hna
        by_cases heq : a = b
        · subst heq
          exact hoh ⟨a, hab⟩
        · exact hclean ⟨a, b, heq, hna, hab⟩
  have hc : S.card ≤ S1.card + S2.card := (Finset.card_le_card hsub).trans (Finset.card_union_le S1 S2)
  have hmul : (c1 + c2) * (C.size + 1) = c1 * (C.size + 1) + c2 * (C.size + 1) := Nat.add_mul c1 c2 (C.size + 1)
  have hS1 : S1.card ≤ c1 * (C.size + 1) := by convert h1
  have hS2 : S2.card ≤ c2 * (C.size + 1) := by convert h2
  have hS : S.card = {x10 ∈ G.edgeFinset | ¬∃ (x11 : Fin n) (x12 : Fin n), x10 = s(x11, x12) ∧ ∃ (x13 : Fin C.gates.length), PEqualNP.EdgeOwnership.Owns n C (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin n), PEqualNP.EdgeOwnership.gateVal n C (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → G.Adj x14 x15}.card := by
    congr 1
  omega
