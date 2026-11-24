import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A vertex in a cover removes three edges and one cover member when set false.
theorem PEqualNP.Outside.R_meta_1973_624
    (coverDrop : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n)) (v : Fin n),
  (∀ w ∉ A, (G.neighborSet w).ncard = 3) →
  (∀ u w, G.Adj u w → u ∉ A) → v ∉ A → v ∈ T →
  (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
  ∃ s, s + 5 ≤ A.card + G.edgeFinset.card + T.card ∧
    HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) s)
    (smaller : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
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
      (∃ v ∉ A, (readers v).length = 2) →
      (∀ T : Finset (Fin n), (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) →
        C.size + 1 < A.card + G.edgeFinset.card + T.card) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       (2 : ℕ) ≤ x16.length ∧ x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length = (2 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  intro n G A f C degree girth unmarked edge spec fan computes minimal limits two
  classical
  let target := graphFun G A
  have same : target = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ f x = true
    rw [spec x]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have result : ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => target (Function.update x v false)) s := by
    by_cases h : ∃ T : Finset (Fin n), (∀ u w, G.Adj u w → u ∈ T ∨ w ∈ T) ∧
        A.card + G.edgeFinset.card + T.card - 1 ≤ C.size
    · obtain ⟨T, covers, budget⟩ := h
      obtain ⟨a,b,hab⟩ := edge
      have pick : ∃ v ∉ A, v ∈ T := by
        rcases covers a b hab with ha | hb
        · exact ⟨a, unmarked _ _ hab, ha⟩
        · exact ⟨b, unmarked _ _ hab.symm, hb⟩
      obtain ⟨v,hv,hT⟩ := pick
      obtain ⟨s,hs,proof⟩ := coverDrop n G A T v degree unmarked hv hT covers
      exact ⟨v,hv,s,by omega,proof⟩
    · have targetComputes : circuitFun n C = target := computes.trans same.symm
      have targetMinimal (s : ℕ) (hs : HasCircuitSize n target s) : C.size ≤ s :=
        minimal s (same ▸ hs)
      refine smaller n G A C degree girth unmarked edge fan targetComputes targetMinimal limits two ?_
      intro T cov
      have bound : ¬ (A.card + G.edgeFinset.card + T.card - 1 ≤ C.size) := fun hT => h ⟨T,cov,hT⟩
      omega
  rwa [same] at result
