import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A walk may revisit vertices. Each new cubic vertex after the first meets an already counted edge.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5020_315
    (save : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let reads := fun v : Fin n => C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ i j, G.Adj i j → i ∉ A) → FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (reads v).length) →
      (∃ v ∉ A, (reads v).length = 2 ∧ ∃ g ∈ reads v, g.op ≠ GateOp.or) →
      ∃ u v, ∃ p : G.Walk u v, ∃ t : ℕ, Disjoint A p.support.toFinset ∧
        t + 3 * p.support.toFinset.card + 1 ≤ C.size ∧
        HasCircuitSize n (fun x => f (fun i => if i ∈ p.support then false else x i)) t)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n) (p : G.Walk u v)
        (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (t k : ℕ),
      (∀ a ∉ A, (G.neighborSet a).ncard = 3) →
      (∀ a (c : G.Walk a a), c.IsCycle → 7 ≤ c.length) →
      (∀ i j, G.Adj i j → i ∉ A) → Disjoint A p.support.toFinset →
      (∀ i j, H.Adj i j ↔ G.Adj i j ∧ i ∉ p.support ∧ j ∉ p.support) →
      (∀ T : Finset (Fin n), H.IsVertexCover (T : Set (Fin n)) → k ≤ T.card) →
      HasCircuitSize n (graphFun H A) t → A.card + H.edgeSet.ncard + k ≤ t+1) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) →     (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →       (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) →         (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) →           (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) →             (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →               PEqualNP.MetaComplexity.FanInTwo x6 →                 PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 →                   (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) →                     (∀ x16 ∉ x4, (2 : ℕ) ≤ (List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x16) x6.gates).length) →                       (∃ x17 ∉ x4,                           have x18 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x17) x6.gates;                           x18.length = (2 : ℕ) ∧ ∃ x19 ∈ x18, x19.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →                         x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  classical
  intro n k G A f C deg girth sep edge cover hf fits comp minimal reads two
  have eqF : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    delta graphFun
    simpa only [ Bool.or_eq_true, decide_eq_true_eq] using hf x
  rw [eqF] at comp minimal
  obtain ⟨u,v,p,t,disj,paid,small⟩ := save n G A C deg girth sep fits comp minimal reads two
  let S := p.support.toFinset
  let B (U : Finset (Fin n)) := U.biUnion (fun i => G.incidenceFinset i)
  let H := G.deleteEdges (B S : Set (Sym2 (Fin n)))
  have outside {i : Fin n} (hi : i ∈ S) : i ∉ A :=
    fun ha => (Finset.disjoint_left.mp disj ha hi)
  have hdeg {i : Fin n} (h : i ∉ A) : (G.incidenceFinset i).card = 3 := by
    rw [SimpleGraph.card_incidenceFinset_eq_degree, ← SimpleGraph.ncard_neighborSet]
    exact deg i h
  have count : ∀ {a b : Fin n} (q : G.Walk a b), (∀ i ∈ q.support, i ∉ A) →
      (B q.support.toFinset).card ≤ 2 * q.support.toFinset.card + 1 := by
    intro a b q
    induction q with
    | @nil a =>
      intro ok
      have three := hdeg (ok a (by simp))
      simpa [B] using three.le
    | @cons a b c h q ih =>
      intro ok
      let T := q.support.toFinset
      have sub : ∀ i ∈ q.support, i ∉ A := fun i hi => ok i (by simp [hi])
      have prior := ih sub
      change (B T).card ≤ 2 * T.card + 1 at prior
      change (B (List.toFinset (a :: q.support))).card ≤ 2 * (List.toFinset (a :: q.support)).card + 1
      rw [List.toFinset_cons]
      change (B (insert a T)).card ≤ 2 * (insert a T).card + 1
      by_cases old : a ∈ T
      · simpa [Finset.insert_eq_of_mem old] using prior
      · have shared : (G.incidenceFinset a ∩ B T).Nonempty := by
          refine ⟨Sym2.mk a b, Finset.mem_inter.mpr ⟨SimpleGraph.mem_incidenceFinset.mpr
            (G.mk'_mem_incidenceSet_left_iff.mpr h), ?_⟩⟩
          exact Finset.mem_biUnion.mpr ⟨b, List.mem_toFinset.mpr q.start_mem_support,
            SimpleGraph.mem_incidenceFinset.mpr (G.mk'_mem_incidenceSet_right_iff.mpr h)⟩
        have tally := Finset.card_union_add_card_inter (G.incidenceFinset a) (B T)
        have positive := shared.card_pos
        have three := hdeg (ok a (by simp))
        rw [show B (insert a T) = G.incidenceFinset a ∪ B T by simp [B], Finset.card_insert_of_notMem old]
        omega
  have cost := count p (fun _ h => outside (List.mem_toFinset.mpr h))
  have subset : (B S : Set (Sym2 (Fin n))) ⊆ G.edgeSet := by
    intro e he
    obtain ⟨i, _, h⟩ := Finset.mem_biUnion.mp (show e ∈ B S from he)
    exact (SimpleGraph.incidenceSet_subset G i) (SimpleGraph.mem_incidenceFinset.mp h)
  have ledger : H.edgeSet.ncard + (B S).card = G.edgeSet.ncard := by
    simpa only [H, SimpleGraph.edgeSet_deleteEdges, Set.ncard_coe_finset] using
      Set.ncard_sdiff_add_ncard_of_subset subset (Set.toFinite _)
  have adj (i j : Fin n) : H.Adj i j ↔ G.Adj i j ∧ i ∉ p.support ∧ j ∉ p.support := by
    change (G.deleteEdges _).Adj i j ↔ _
    simp only [SimpleGraph.deleteEdges_adj, Finset.mem_coe, B, Finset.mem_biUnion,
      SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff, S, List.mem_toFinset]
    constructor
    · rintro ⟨e, no⟩
      exact ⟨e, fun hi => no ⟨i, hi, e, Or.inl rfl⟩, fun hj => no ⟨j, hj, e, Or.inr rfl⟩⟩
    · rintro ⟨e, hi, hj⟩
      refine ⟨e, ?_⟩
      rintro ⟨w, hw, _, rfl | rfl⟩
      · exact hi hw
      · exact hj hw
  have agree : (fun x : Fin n → Bool => graphFun G A (fun i => if i ∈ p.support then false else x i)) = graphFun H A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    delta graphFun
    simp only [ Bool.or_eq_true, decide_eq_true_eq]
    have atA (i : Fin n) (h : i ∈ A) : i ∉ p.support :=
      fun h' => outside (List.mem_toFinset.mpr h') h
    have val (i : Fin n) : (if i ∈ p.support then false else x i) = true ↔ i ∉ p.support ∧ x i = true := by
      by_cases h : i ∈ p.support <;> simp [h]
    simp only [val]
    constructor
    · rintro (⟨i, hi, _, vi⟩ | ⟨i, j, e, ⟨hi, vi⟩, hj, vj⟩)
      · exact Or.inl ⟨i, hi, vi⟩
      · exact Or.inr ⟨i, j, (adj i j).2 ⟨e, hi, hj⟩, vi, vj⟩
    · rintro (⟨i, hi, vi⟩ | ⟨i, j, e, vi, vj⟩)
      · exact Or.inl ⟨i, hi, atA i hi, vi⟩
      · obtain ⟨e, hi, hj⟩ := (adj i j).1 e
        exact Or.inr ⟨i, j, e, ⟨hi, vi⟩, hj, vj⟩
  have charge (T : Finset (Fin n)) (hc : H.IsVertexCover (T : Set (Fin n))) : k - S.card ≤ T.card := by
    have hc' : ∀ i j, G.Adj i j → i ∈ S ∪ T ∨ j ∈ S ∪ T := by
      intro i j e
      by_cases hi : i ∈ S
      · exact Or.inl (Finset.mem_union_left _ hi)
      by_cases hj : j ∈ S
      · exact Or.inr (Finset.mem_union_left _ hj)
      have hh := hc ((adj i j).mpr ⟨e,fun h => hi (List.mem_toFinset.mpr h),fun h => hj (List.mem_toFinset.mpr h)⟩)
      rcases hh with h | h
      · exact Or.inl (Finset.mem_union_right _ h)
      · exact Or.inr (Finset.mem_union_right _ h)
    have := cover (S ∪ T) hc'
    have := Finset.card_union_le S T
    omega
  rw [agree] at small
  have lower := residual n G A u v p H t (k-S.card) deg girth sep disj adj charge small
  change (B S).card ≤ 2 * S.card + 1 at cost
  change t + 3 * S.card + 1 ≤ C.size at paid
  omega
