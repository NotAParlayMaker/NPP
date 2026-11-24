import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

-- Count effective input positions, with at most one for each NOT gate.
-- When that count pays for a vertex cover circuit, delete a cover vertex.
-- Its three incident edges and the cover vertex account for four gates.
theorem PEqualNP.Outside.R_meta_1973_2
    (slotBound : ∀ (n : ℕ) (A : Finset (Fin n)) (C : Circuit),
      let readers (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      let twos := (Aᶜ.filter fun v => (readers v).length = 2).card
      FanInTwo C → (∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s) →
      (∀ a ∈ A, ∃ x y : Fin n → Bool, (∀ i ≠ a, x i = y i) ∧
        circuitFun n C x ≠ circuitFun n C y) →
      (∀ v ∉ A, 2 ≤ (readers v).length) →
      A.card + 3 * Aᶜ.card + PEqualNP.NotBracket.notCount C ≤ C.size + 1 + twos)
    (cofactorUpper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A T : Finset (Fin n)) (v : Fin n),
      PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → v ∈ T → v ∉ A → G.degree v = 3 →
      (∃ u w, G.Adj u w ∧ u ≠ v ∧ w ≠ v) →
      ∃ s, s + 5 ≤ A.card + G.edgeFinset.card + T.card ∧
        HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) s)
    (dense : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let readers (v : Fin n) := C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      let twos := (Aᶜ.filter fun v => (readers v).length = 2).card
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
        ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∀ T : Finset (Fin n), T ⊆ Aᶜ → PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T →
        G.edgeFinset.card + PEqualNP.NotBracket.notCount C < T.card + twos) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 →
      Bool) →
      Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
          (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       (2 : ℕ) ≤ x16.length ∧ x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length = (2 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  classical
  intro n G A f C degree girth noMarked edge fSpec fan computes minimal readBounds _
  let target := graphFun G A
  let readers (v : Fin n) := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  let twos := (Aᶜ.filter fun v => (readers v).length = 2).card
  have targetEq : target = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ f x = true
    rw [fSpec]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have computesTarget : circuitFun n C = target := computes.trans targetEq.symm
  have minTarget (s : ℕ) (h : HasCircuitSize n target s) : C.size ≤ s :=
    minimal s (targetEq ▸ h)
  suffices ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => target (Function.update x v false)) s by
    rwa [targetEq] at this
  by_cases covers : ∃ T : Finset (Fin n), T ⊆ Aᶜ ∧ PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T ∧
      T.card + twos ≤ G.edgeFinset.card + PEqualNP.NotBracket.notCount C
  · obtain ⟨T, subT, coverT, countT⟩ := covers
    obtain ⟨u, w, uw⟩ := edge
    obtain ⟨v, hv⟩ : T.Nonempty := by
      rcases coverT u w uw with h | h
      · exact ⟨u, h⟩
      · exact ⟨w, h⟩
    have notMarked : v ∉ A := Finset.mem_compl.mp (subT hv)
    have degMarked (i : Fin n) (hi : i ∈ A) : G.degree i = 0 :=
      (G.degree_eq_zero i).mpr (fun j ij => noMarked i j ij hi)
    have degOrdinary (i : Fin n) (hi : i ∉ A) : G.degree i = 3 := by
      rw [← G.ncard_neighborSet]
      exact degree i hi
    have degreeSum := G.sum_degrees_eq_twice_card_edges
    rw [← A.sum_add_sum_compl, Finset.sum_congr rfl degMarked,
      Finset.sum_congr rfl (fun i hi => degOrdinary i (Finset.mem_compl.mp hi))] at degreeSum
    simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at degreeSum
    have retained : ∃ i j, G.Adj i j ∧ i ≠ v ∧ j ≠ v := by
      have neighbor : ∃ i, G.Adj v i := by
        by_contra! h
        have z := (G.degree_eq_zero v).mpr h
        have d := degOrdinary v notMarked
        omega
      obtain ⟨i, vi⟩ := neighbor
      have iv : i ≠ v := vi.ne.symm
      have di := degOrdinary i (noMarked i v vi.symm)
      by_contra! noEdge
      have oneNeighbor : G.neighborFinset i ⊆ {v} := by
        intro j hj
        apply Finset.mem_singleton.mpr
        exact noEdge i j ((G.mem_neighborFinset i j).mp hj) iv
      have bound := Finset.card_le_card oneNeighbor
      simp [di] at bound
    have essential (a : Fin n) (ha : a ∈ A) :
        ∃ x y : Fin n → Bool, (∀ i ≠ a, x i = y i) ∧
          circuitFun n C x ≠ circuitFun n C y := by
      let x : Fin n → Bool := fun _ => false
      let y : Fin n → Bool := fun i => decide (i = a)
      refine ⟨x, y, fun i hi => by simp [x, y, hi], ?_⟩
      rw [computes]
      have hx : f x ≠ true := by simp [x, fSpec]
      have hy : f y = true := (fSpec y).mpr (Or.inl ⟨a, ha, by simp [y]⟩)
      exact fun e => hx (e.trans hy)
    have slots : A.card + 3 * Aᶜ.card + PEqualNP.NotBracket.notCount C ≤ C.size + 1 + twos :=
      slotBound n A C fan (by simpa only [computes] using minimal) essential
        (fun v hv => (readBounds v hv).1)
    obtain ⟨s, upper, circuit⟩ := cofactorUpper n G A T v coverT hv notMarked
      (degOrdinary v notMarked) retained
    exact ⟨v, notMarked, s, by omega, circuit⟩
  · apply dense n G A C degree girth noMarked edge fan computesTarget minTarget readBounds
    intro T subT coverT
    exact Nat.lt_of_not_ge (fun h => covers ⟨T, subT, coverT, h⟩)
