import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The counting child locates a cubic vertex whose closed neighborhood is read twice.
-- The other child asks for gate elimination under this local hypothesis.

theorem PEqualNP.Outside.R_meta_4151_643
    (locate : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U S : Finset (Fin n)),
      U.Nonempty → (∀ v ∈ U, (G.neighborFinset v).card = 3) →
      (∀ a b, G.Adj a b → b ∈ U) → (∀ a b c, G.Adj a b → G.Adj a c → ¬ G.Adj b c) →
      S ⊆ U → (∀ I : Finset (Fin n), I ⊆ U → (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) →
        U.card + 2 * I.card ≤ 2 * S.card) →
      ∃ v ∈ S, ∀ w, G.Adj v w → w ∈ S)
    (localElimination : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let reads (v : Fin n) := (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → IsMinimalCircuit n C → circuitFun n C = f →
      (∀ v ∉ A, 2 ≤ reads v ∧ reads v ≤ 3 ∧ (reads v = 3 →
        ∀ g ∈ C.gates, (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val →
          g.op = GateOp.or)) →
      (∃ v ∉ A, reads v = 2 ∧ ∀ w, G.Adj v w → reads w = 2) →
      ∃ v ∉ A, ∃ size, size + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) size) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ⊆ x4ᶜ, (∀ x18 ∈ x16, ∀ x20 ∈ x16, ¬x2.Adj x18 x20) → x4ᶜ.card + (2 : ℕ) * x16.card ≤ (2 : ℕ) * {x19 ∉ x4 | (x7 x19).length = (2 : ℕ)}.card) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  intro n G dec A C f readers cubic girth isolated nonempty fan computes min readBounds density
  let S := Aᶜ.filter fun v => (readers v).length = 2
  have hasOrdinary : Aᶜ.Nonempty := by
    obtain ⟨u, v, huv⟩ := nonempty
    exact ⟨u, Finset.mem_compl.mpr (isolated u v huv)⟩
  have degree (v : Fin n) (hv : v ∈ Aᶜ) : (G.neighborFinset v).card = 3 := by
    rw [G.neighborFinset_def, ← Set.ncard_eq_toFinset_card']
    exact cubic v (Finset.mem_compl.mp hv)
  have inside (u v : Fin n) (edge : G.Adj u v) : v ∈ Aᶜ :=
    Finset.mem_compl.mpr (isolated v u edge.symm)
  have triangle : ∀ a b c, G.Adj a b → G.Adj a c → ¬ G.Adj b c := by
    intro a b c ab ac bc
    let w : G.Walk a a := .cons ab (.cons bc (.cons ac.symm .nil))
    have cyc : w.IsCycle := by
      apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      constructor
      · simp [w, SimpleGraph.Walk.isPath_def, ab.ne.symm, ac.ne.symm, bc.ne]
      · simp [w]
    have h := girth a w cyc
    simp [w] at h
  obtain ⟨v, hv, around⟩ := locate n G Aᶜ S hasOrdinary degree inside triangle
    (Finset.filter_subset _ _) density
  have minimum : IsMinimalCircuit n C := by
    refine ⟨fan, ?_⟩
    intro D dFan dComputes
    exact min D.size ⟨D, dFan, le_rfl, fun x => congrFun (dComputes.trans computes) x⟩
  apply localElimination n G A C cubic girth isolated minimum computes
  · intro u hu
    obtain ⟨lo, hi, three⟩ := readBounds u hu
    refine ⟨lo, hi, fun h g hg hRead => three h g ?_⟩
    exact List.mem_filter.mpr ⟨hg, hRead⟩
  · have here := Finset.mem_filter.mp hv
    refine ⟨v, Finset.mem_compl.mp here.1, here.2, ?_⟩
    exact fun w edge => (Finset.mem_filter.mp (around w edge)).2
