import Mathlib
import PEqualNP.Defs

-- Triangle-free cover pricing settles the high-size range. The remaining
-- circuits exceed the two-read baseline but lie strictly below its one-sixth
-- surplus. Each has either a nonstandard gate or a reused internal wire.
theorem PEqualNP.Outside.R_meta_5020_1
    (price : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (k : ℕ), (∀ i∉A, (G.neighborSet i).ncard=3) → (∀ i (w : G.Walk i i), w.IsCycle → 7≤w.length) → (∀ i j, G.Adj i j → i∉A) → (∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i∈T ∨ j∈T) → k≤T.card) → 2*G.edgeSet.ncard=3*Aᶜ.card ∧ 3*k≤2*Aᶜ.card)
    (structureCase : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), let f := PEqualNP.MetaComplexity.NestedCover.graphFun G A; let R := fun w : ℕ => C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains w); (∀ i∉A, (G.neighborSet i).ncard=3) → (∀ i (w : G.Walk i i), w.IsCycle → 7≤w.length) → (∀ i j, G.Adj i j → i∉A) → (∃ u v, G.Adj u v) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C=f → (∀ s, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) → (∀ v∉A, 2≤(R v).length) → 6*(C.size+1)<6*A.card+13*Aᶜ.card → A.card+2*Aᶜ.card<C.size+1 ∧ ((∃ g∈C.gates, ¬ ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs=[a,b] ∧ a≠b)) ∨ ∃ j : Fin C.size, 1 < (R (n+j.val)).length + (if C.output=n+j.val then 1 else 0)))
    (extractSet : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), let f := PEqualNP.MetaComplexity.NestedCover.graphFun G A; let R := fun w : ℕ => C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains w); (∀ i∉A, (G.neighborSet i).ncard=3) → (∀ i (w : G.Walk i i), w.IsCycle → 7≤w.length) → (∀ i j, G.Adj i j → i∉A) → (∃ u v, G.Adj u v) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C=f → (∀ s, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) → (∀ v∉A, 2≤(R v).length) → (∃ v∉A, (R v).length=2 ∧ ∃ g∈R v, g.op≠.or) → 6*(C.size+1)<6*A.card+13*Aᶜ.card → A.card+2*Aᶜ.card<C.size+1 → ((∃ g∈C.gates, ¬ ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs=[a,b] ∧ a≠b)) ∨ ∃ j : Fin C.size, 1 < (R (n+j.val)).length + (if C.output=n+j.val then 1 else 0)) → ∃ I : Finset (Fin n), I⊆Aᶜ ∧ (∀ u∈I, ∀ v∈I, ¬G.Adj u v) ∧ 5*Aᶜ.card+2*A.card≤2*(C.size+1+I.card)) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) →     (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →       (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) →         (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) →           (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) →             (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →               PEqualNP.MetaComplexity.FanInTwo x6 →                 PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 →                   (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) →                     (∀ x16 ∉ x4, (2 : ℕ) ≤ (List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x16) x6.gates).length) →                       (∃ x17 ∉ x4,                           have x18 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x17) x6.gates;                           x18.length = (2 : ℕ) ∧ ∃ x19 ∈ x18, x19.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →                         x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  classical
  intro n k G A f C deg girth iso edge demand spec fan ev least twice mixed
  have eq : f = PEqualNP.MetaComplexity.NestedCover.graphFun G A := by
    funext x; apply Bool.eq_iff_iff.mpr
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simpa only [Bool.or_eq_true,decide_eq_true_eq] using spec x
  rw [eq] at ev least
  obtain ⟨edges,cover⟩ := price n G A k deg girth iso demand
  by_cases narrow : 6*(C.size+1)<6*A.card+13*Aᶜ.card
  · obtain ⟨low,shape⟩ := structureCase n G A C deg girth iso edge fan ev least twice narrow
    obtain ⟨I,sub,ind,sz⟩ := extractSet n G A C deg girth iso edge fan ev least twice mixed narrow low shape
    have hk := demand (Aᶜ \ I) (by
      intro u v h; by_cases hu : u ∈ I
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (iso _ _ h.symm),fun hv => ind _ hu _ hv h⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (iso _ _ h),hu⟩))
    rw [Finset.card_sdiff_of_subset sub] at hk
    have := Finset.card_le_card sub; omega
  · omega
