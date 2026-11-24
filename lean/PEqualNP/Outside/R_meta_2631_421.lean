import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2631_421
    (collapse : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (p q h j : ℕ),
      PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = f →
      (∃ x y : Fin n → Bool, f (Function.update x v false) ≠ f (Function.update y v false)) →
      q ∉ [p,h,j] → q < C.size → j < C.size → p < h → h < j →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C p).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or →
      (v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C p).inputs.take (bif (PEqualNP.MetaComplexity.NestedCover.gateAt C p).op.eval [false] then 1 else 2)) →
      (v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C q).inputs.take (bif (PEqualNP.MetaComplexity.NestedCover.gateAt C q).op.eval [false] then 1 else 2)) →
      (n + p ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C h).inputs.take (bif (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op.eval [false] then 1 else 2)) →
      (n + h ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.take (bif (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval [false] then 1 else 2)) →
      ∃ s, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x v false)) s)
    (remaining : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have pins : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun g => g.inputs.take (bif g.op.eval [false] then 1 else 2); have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun v => List.filter (fun g => (pins g).contains ↑v) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4)  → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (have gx : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5; ¬ ∃ (v : Fin x1) (p q h j : ℕ), v ∉ x4 ∧ q ∉ [p,h,j] ∧ p < h ∧ h < j ∧ (gx p).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (gx h).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ v.val ∈ pins (gx p) ∧ v.val ∈ pins (gx q) ∧ x1+p ∈ pins (gx h) ∧ x1+h ∈ pins (gx j)) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  intro n G inst A C f readers hdeg hgirth hisol hEdge hF hf hmin hread hanchor
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let readsOf (g : PEqualNP.CircuitLowerBounds.Gate) : List ℕ :=
    g.inputs.take (bif g.op.eval [false] then 1 else 2)
  classical
  have valid (k i : ℕ) (hu : i ∈ readsOf (gate k)) : k < C.size := by
    by_contra h
    have hd : gate k = ⟨PEqualNP.CircuitLowerBounds.GateOp.or,[]⟩ := by
      change C.gates.getD k ⟨.or,[]⟩ = _
      exact List.getD_eq_default _ _ (Nat.le_of_not_gt h)
    rw [hd] at hu
    change i ∈ [].take _ at hu
    simp only [List.take_nil,List.not_mem_nil] at hu
  by_cases chain : ∃ (v : Fin n) (p q h j : ℕ), v ∉ A ∧
      q ∉ [p,h,j] ∧ p < h ∧ h < j ∧
      (gate p).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (gate h).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧
      v.val ∈ readsOf (gate p) ∧ v.val ∈ readsOf (gate q) ∧
        n+p ∈ readsOf (gate h) ∧ n+h ∈ readsOf (gate j)
  · obtain ⟨v,p,q,h,j,hv,hsep,hph,hhj,hpAND,hhNotOR,hpv,hqv,hhp,hjh⟩ := chain
    have huExists : ∃ u : Fin n, u ≠ v ∧ u ∉ A := by
      obtain ⟨a,b,hab⟩ := hEdge
      by_cases he : a = v
      · refine ⟨b,?_,hisol b a hab.symm⟩
        intro hb
        exact (G.ne_of_adj hab) (he.trans hb.symm)
      · exact ⟨a,he,hisol a b hab⟩
    obtain ⟨u,huv,huA⟩ := huExists
    have hwExists : ∃ w : Fin n, w ≠ v ∧ G.Adj u w := by
      by_contra h
      have hsub : G.neighborSet u ⊆ ({v} : Set (Fin n)) := by
        intro w hw
        apply Set.mem_singleton_iff.mpr
        by_contra hne
        exact h ⟨w,hne,hw⟩
      have hcap := Set.ncard_le_ncard hsub (Set.finite_singleton v)
      rw [hdeg u huA,Set.ncard_singleton] at hcap
      omega
    obtain ⟨w,hwv,huw⟩ := hwExists
    have hnc : ∃ x y : Fin n → Bool,
        f (Function.update x v false) ≠ f (Function.update y v false) := by
      let z : Fin n → Bool := Function.update (fun _ => false) v false
      let o : Fin n → Bool := Function.update (fun _ => true) v false
      have hz (i : Fin n) : z i = false := by
        by_cases hi : i = v <;> simp [z,hi]
      have hfz : f z = false := by
        change (decide (∃ a ∈ A, z a = true) ||
          decide (∃ a b : Fin n, G.Adj a b ∧ z a = true ∧ z b = true)) = false
        simp [hz]
      have hfo : f o = true := by
        change (decide (∃ a ∈ A, o a = true) ||
          decide (∃ a b : Fin n, G.Adj a b ∧ o a = true ∧ o b = true)) = true
        exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true
          ⟨u,w,huw,by simp [o,huv],
            by simp [o,hwv]⟩))
      refine ⟨fun _ => false,fun _ => true,?_⟩
      change f z ≠ f o
      rw [hfz,hfo]
      decide
    exact ⟨v,hv,collapse n f C v p q h j hF hf hnc hsep (valid q _ hqv) (valid j _ hjh)
      hph hhj hpAND hhNotOR hpv hqv hhp hjh⟩
  · exact remaining n G A C hdeg hgirth hisol hF hf hmin hread hanchor chain
