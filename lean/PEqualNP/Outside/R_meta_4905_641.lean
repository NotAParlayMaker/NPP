import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The cubic cofactor argument only requires the edge-plus-cover lower bound of the small-support AND-sound case.
-- The first child weakens L-meta-1407's all-assignments soundness assumption to supports of cardinality at most two.
-- L-meta-4009 supplies the star-cover upper bound for the cofactor.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4905_641
  (pairLower : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (List.ofFn x).count true ≤ 2 → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1)
  (starUpper : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 x5 : Finset (Fin x1)) (x6 : ℕ), (x4.Nonempty ∨ ∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∈ x5 ∨ x9 ∈ x5) → x6 + (1 : ℕ) = x4.card + x2.edgeFinset.card + x5.card → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x10 : Fin x1 → Bool) => Decidable.decide ((∃ x11 ∈ x4, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true)) x6)
  (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    have r : Fin n → List Gate := fun v => C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G ∅ →
    (∀ v ∉ A, (r v).length ≤ 3 ∧ ((r v).length = 3 → ∀ g ∈ r v, g.op = .or)) →
    (∃ v ∉ A, (r v).length ≤ 1) →
    (∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → C.size+1 < G.edgeFinset.card+T.card) →
    ((∃ g ∈ C.gates, g.op = .not) ∨
      ∃ (i : Fin C.gates.length) (x : Fin n → Bool), (C.gates.get i).op = .and ∧
        (List.ofFn x).count true ≤ 2 ∧
        (C.wires (List.ofFn x)).getD (n+i.val) false = true ∧ circuitFun n C x = false) →
    ∃ v ∉ A, ∃ t, t+4 ≤ C.size ∧ HasCircuitSize n (fun x => NestedCover.graphFun G ∅ (Function.update x v false)) t) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) =>     have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x6.gates;     (∀ x8 ∉ x4, (x7 x8).length ≤ (3 : ℕ) ∧ ((x7 x8).length = (3 : ℕ) → ∀ x11 ∈ x7 x8, x11.op = PEqualNP.CircuitLowerBounds.GateOp.or)) ∧ ∃ x8 ∉ x4, (x7 x8).length ≤ (1 : ℕ);   (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x5 → ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update x16 x14 Bool.false)) x15 := by
  intro n G inst A C sparseDef deg girth iso edge minC compute sparse
  classical
  have spec (x : Fin n → Bool) : circuitFun n C x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [compute]
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) || decide _) = true ↔ _
    simp
  have no4 (a b c d : Fin n) (hac : a ≠ c) (hbd : b ≠ d) :
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro ⟨ab,bc,cd,da⟩
    let w : G.Walk a a := .cons ab (.cons bc (.cons cd (.cons da .nil)))
    have hc : w.IsCycle := by
      apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      refine ⟨?_,by change 3 ≤ 4; decide⟩
      change (SimpleGraph.Walk.cons bc (.cons cd (.cons da .nil))).IsPath
      simp [SimpleGraph.Walk.isPath_def,ab.ne.symm,bc.ne,cd.ne,da.ne,hac.symm,hbd]
    have hw := girth a w hc
    change 7 ≤ 4 at hw
    omega
  by_cases cov : ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ C.size+1
  swap
  · have strict (T : Finset (Fin n)) (hT : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) : C.size+1 < G.edgeFinset.card + T.card := by
      by_contra! h
      exact cov ⟨T,hT,h⟩
    have bad : (∃ g ∈ C.gates, g.op = .not) ∨
      ∃ (i : Fin C.gates.length) (x : Fin n → Bool), (C.gates.get i).op = .and ∧
        (List.ofFn x).count true ≤ 2 ∧
        (C.wires (List.ofFn x)).getD (n+i.val) false = true ∧ circuitFun n C x = false := by
      by_contra bad
      have pos (g : Gate) (hg : g ∈ C.gates) : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
        have H := minC.1 g hg
        have noN : g.op ≠ .not := fun h => bad (Or.inl ⟨g,hg,h⟩)
        have e : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using H.1
        exact ⟨e.elim Or.inl (fun h => Or.inr (h.resolve_right noN)),H.2⟩
      have eq (x : Fin n → Bool) : C.eval (List.ofFn x) = decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
        apply Bool.eq_iff_iff.mpr
        exact (spec x).trans decide_eq_true_iff.symm
      have sound (i : Fin C.gates.length) (x : Fin n → Bool) (hi : (C.gates.get i).op = .and)
          (hx : (List.ofFn x).count true ≤ 2)
          (hv : ((Circuit.mk C.gates 0).wires (List.ofFn x)).getD (n+i.val) false = true) :
          ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        apply (spec x).mp
        by_contra! h
        exact bad (Or.inr ⟨i,x,hi,hx,hv,Bool.eq_false_iff.mpr h⟩)
      obtain ⟨T,hT,hsize⟩ := pairLower n G no4 C.gates C.output pos
        (fun x => eq x) sound
      exact cov ⟨T,hT,hsize⟩
    exact residual n G A C deg girth iso edge minC compute sparse.1 sparse.2 strict bad
  obtain ⟨T,hT,hsize⟩ := cov
  obtain ⟨a,b,ab⟩ := edge
  obtain ⟨z,hz,hzA⟩ : ∃ z ∈ T, z ∉ A := by
    rcases hT a b ab with ha|hb
    · exact ⟨a,ha,iso a b ab⟩
    · exact ⟨b,hb,iso b a ab.symm⟩
  have hzdeg : G.degree z = 3 := by rw [← G.ncard_neighborSet]; exact deg z hzA
  have hn : ∃ u v, (G.deleteEdges (G.incidenceSet z)).Adj u v := by
    obtain ⟨u,zu⟩ := (G.degree_pos_iff_exists_adj z).mp (by omega)
    have huA := iso u z zu.symm
    have hu : G.degree u = 3 := by rw [← G.ncard_neighborSet]; exact deg u huA
    have hzmem : z ∈ G.neighborFinset u := (G.mem_neighborFinset u z).mpr zu.symm
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < ((G.neighborFinset u).erase z).card by rw [Finset.card_erase_of_mem hzmem,show (G.neighborFinset u).card = G.degree u from rfl,hu]; decide)
    obtain ⟨hvz,hm⟩ := Finset.mem_erase.mp hv
    exact ⟨u,v,SimpleGraph.deleteIncidenceSet_adj.mpr
      ⟨(G.mem_neighborFinset u v).mp hm,zu.ne.symm,hvz⟩⟩
  let H := G.deleteEdges (G.incidenceSet z)
  have heq : H.edgeFinset = G.edgeFinset \ G.incidenceFinset z := by
    ext e
    rw [SimpleGraph.mem_edgeFinset,Finset.mem_sdiff,SimpleGraph.mem_edgeFinset,← Finset.mem_coe,
      G.coe_incidenceFinset,show H.edgeSet = G.edgeSet \ G.incidenceSet z from SimpleGraph.edgeSet_deleteEdges _]
    exact Set.mem_sdiff e
  have hcount : H.edgeFinset.card + 3 = G.edgeFinset.card := by
    rw [← hzdeg,heq,← G.card_incidenceFinset_eq_degree]
    exact Finset.card_sdiff_add_card_eq_card (G.incidenceFinset_subset z)
  have hcov : ∀ u v, H.Adj u v → u ∈ T.erase z ∨ v ∈ T.erase z := by
    intro u v huv
    obtain ⟨adj,hu,hv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp huv
    rcases hT u v adj with h|h
    · exact Or.inl (Finset.mem_erase.mpr ⟨hu,h⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hv,h⟩)
  have hcard : H.edgeFinset.card + (T.erase z).card + 4 ≤ C.size+1 := by
    rw [Finset.card_erase_of_mem hz]
    have htpos : 0 < T.card := Finset.card_pos.mpr ⟨z,hz⟩
    change G.edgeFinset.card + T.card ≤ C.size + 1 at hsize
    omega
  have hEc : 0 < H.edgeFinset.card := by
    obtain ⟨u,v,hv⟩ := hn
    exact Finset.card_pos.mpr ⟨s(u,v),by rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]; exact hv⟩
  let t := H.edgeFinset.card + (T.erase z).card - 1
  have ht : t+1 = (∅ : Finset (Fin n)).card + H.edgeFinset.card + (T.erase z).card := by
    simp [t]; omega
  obtain B := starUpper n H ∅ (T.erase z) t (Or.inr hn) hcov ht
  refine ⟨z,hzA,t,by omega,?_⟩
  obtain ⟨D,hD,hDt,hDfun⟩ := B
  refine ⟨D,hD,hDt,fun x => ?_⟩
  rw [hDfun]
  apply Bool.eq_iff_iff.mpr
  change _ ↔ (decide (∃ a ∈ (∅ : Finset (Fin n)), (Function.update x z false) a = true) || decide _) = true
  simp only [decide_eq_true_eq,Finset.notMem_empty,false_and,exists_false,false_or,decide_false,Bool.false_or]
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    obtain ⟨huv,huz,hvz⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
    exact ⟨u,v,huv,by simpa [Function.update_of_ne huz] using hu,by simpa [Function.update_of_ne hvz] using hv⟩
  · rintro ⟨u,v,h,hu,hv⟩
    have huz : u ≠ z := by intro e; subst u; simp at hu
    have hvz : v ≠ z := by intro e; subst v; simp at hv
    exact ⟨u,v,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨h,huz,hvz⟩,by simpa [Function.update_of_ne huz] using hu,by simpa [Function.update_of_ne hvz] using hv⟩
