import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Two unmarked input partners that mask an input through OR gates must form an edge.
theorem PEqualNP.Outside.R_meta_2633_561
    (partner : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
  (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
  (∀ u w, G.Adj u w → u ∉ A) → FanInTwo C →
  circuitFun n C = graphFun G A →
  ∀ v a b : Fin n, v ∉ A → a ∉ A → b ∉ A →
    (G.neighborSet v).ncard = 3 → a ≠ v → b ≠ v →
    (∀ g ∈ C.gates, (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val →
      g.op = .or ∧ (a.val ∈ g.inputs ∨ b.val ∈ g.inputs)) →
    G.Adj a b)
    (restrict : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let readers (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u w, G.Adj u w → u ∉ A) → (∃ u w, G.Adj u w) →
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
        ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∀ v ∉ A, ∀ g ∈ readers v, g.op = .or) →
      (∀ v ∉ A, (readers v).length = 2 → ∀ a b : Fin n,
        a ∉ A → b ∉ A → a ≠ v → b ≠ v →
        (∀ g ∈ readers v, a.val ∈ g.inputs ∨ b.val ∈ g.inputs) → G.Adj a b) →
      (∃ v ∉ A, (readers v).length = 2) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ∉ x4, ∀ x18 ∈ x7 x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x17 ∉ x4, (x7 x17).length = (2 : ℕ)) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19 := by
  intro n G dec A C f readers degree girth unmarked edge fan computes minimal limits allOr two
  refine restrict n G A C degree girth unmarked edge fan computes minimal limits allOr ?_ two
  intro v hv _ a b ha hb hav hbv masked
  refine partner n G A C girth unmarked fan computes v a b hv ha hb (degree v hv) hav hbv ?_
  intro g hg reads
  have member : g ∈ readers v := List.mem_filter.mpr ⟨hg, reads⟩
  exact ⟨allOr v hv g member, masked g member⟩
