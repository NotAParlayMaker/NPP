import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Each operand contributes the raw inputs that reach it through OR gates.
-- Keep an AND gate when every pair in this product is an edge of the graph.
theorem PEqualNP.Outside.R_meta_1710_118 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C → ∀ jobs : Finset (Fin C.gates.length),
        (∀ j ∈ jobs, ((side (n := n) C j 0 ×ˢ side (n := n) C j 1).image fun p => s(p.1,p.2)) ⊆ G.edgeFinset) →
        (jobs.biUnion (fun j => ((side (n := n) C j 0 ×ˢ side (n := n) C j 1).image fun p => s(p.1,p.2)))).card ≤ 2*C.size) →
    (∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) → (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∀ jobs : Finset (Fin C.gates.length),
        (∀ j : Fin C.gates.length, j ∈ jobs ↔ (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2 ∧
           (∀ w ∈ (gateAt C j).inputs, w < n+j) ∧ ((side (n := n) C j 0 ×ˢ side (n := n) C j 1).image fun p => s(p.1,p.2)) ⊆ G.edgeFinset) →
        (G.edgeFinset \ jobs.biUnion (fun j => ((side (n := n) C j 0 ×ˢ side (n := n) C j 1).image fun p => s(p.1,p.2)))).card ≤ c*(C.size+1)) →
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) => Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  intro priced residual
  obtain ⟨b,hb⟩ := residual
  refine ⟨2+b,?_⟩
  intro n G inst degrees girth C mono computes
  have edge : circuitFun n C = graphFun G ∅ := by
    funext x
    change circuitFun n C x =
      (decide (∃ v ∈ (∅ : Finset (Fin n)), x v = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or]
    exact congrFun computes x
  let rect (j : Fin C.gates.length) : Finset (Sym2 (Fin n)) :=
    (side (n := n) C j 0 ×ˢ side (n := n) C j 1).image fun p => s(p.1,p.2)
  classical
  let jobs := (Finset.univ : Finset (Fin C.gates.length)).filter fun j : Fin C.gates.length =>
    (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2 ∧
    (∀ w ∈ (gateAt C j).inputs, w < n+j) ∧ rect j ⊆ G.edgeFinset
  let covered := jobs.biUnion rect
  have spec (j : Fin C.gates.length) : j ∈ jobs ↔
      (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2 ∧
      (∀ w ∈ (gateAt C j).inputs, w < n+j) ∧ rect j ⊆ G.edgeFinset := by
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _))
  have price : covered.card ≤ 2*C.size :=
    priced n G girth C mono jobs fun j hj => ((spec j).mp hj).2.2.2
  have remn : (G.edgeFinset \ covered).card ≤ b*(C.size+1) := hb n G degrees girth C mono edge jobs spec
  have included : covered ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨j,hj,hh⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hj).2.2.2.2 hh
  have partition := Finset.card_sdiff_add_card_eq_card included
  rw [Nat.add_mul]
  omega
