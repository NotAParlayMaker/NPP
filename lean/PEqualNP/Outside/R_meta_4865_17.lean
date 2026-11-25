import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4865_17
    (h_not_not :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
        have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;
        (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) →
        (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) →
        (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) →
        PEqualNP.MetaComplexity.FanInTwo x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 →
        (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) →
        (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∀ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        (∀ x17 ⊆ x4ᶜ, (∀ (x19 x20 : Fin x1), x2.Adj x19 x20 → x19 ∈ x17 ∨ x20 ∈ x17) → ∑ x20 ∈ x4ᶜ, (x7 x20).length + (List.filter (fun (x20 : PEqualNP.CircuitLowerBounds.Gate) => x20.op.eval [Bool.false]) x5.gates).length < x2.edgeFinset.card + x17.card) →
        ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19)
    (h_not_and :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
        have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;
        (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) →
        (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) →
        (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) →
        PEqualNP.MetaComplexity.FanInTwo x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 →
        (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) →
        (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ (∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (∀ x17 ⊆ x4ᶜ, (∀ (x19 x20 : Fin x1), x2.Adj x19 x20 → x19 ∈ x17 ∨ x20 ∈ x17) → ∑ x20 ∈ x4ᶜ, (x7 x20).length + (List.filter (fun (x20 : PEqualNP.CircuitLowerBounds.Gate) => x20.op.eval [Bool.false]) x5.gates).length < x2.edgeFinset.card + x17.card) →
        ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19)
    (h_not_or :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
        have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;
        (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) →
        (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) →
        (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) →
        PEqualNP.MetaComplexity.FanInTwo x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 →
        (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) →
        (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ (∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (∀ x17 ⊆ x4ᶜ, (∀ (x19 x20 : Fin x1), x2.Adj x19 x20 → x19 ∈ x17 ∨ x20 ∈ x17) → ∑ x20 ∈ x4ᶜ, (x7 x20).length + (List.filter (fun (x20 : PEqualNP.CircuitLowerBounds.Gate) => x20.op.eval [Bool.false]) x5.gates).length < x2.edgeFinset.card + x17.card) →
        ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ x17 ⊆ x4ᶜ, (∀ (x19 x20 : Fin x1), x2.Adj x19 x20 → x19 ∈ x17 ∨ x20 ∈ x17) → ∑ x20 ∈ x4ᶜ, (x7 x20).length + (List.filter (fun (x20 : PEqualNP.CircuitLowerBounds.Gate) => x20.op.eval [Bool.false]) x5.gates).length < x2.edgeFinset.card + x17.card) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19 := by
  intro x1 x2 x3 x4 x5 x6 x7 hcub hgirth hadj hex hfan hfun hmin hdeg hnot2 hvc
  obtain ⟨v, hv, hlen2, gnot, hgnot_mem, hgnot_op⟩ := hnot2
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen2
  have ha_mem : a ∈ x7 v := by rw [hab]; simp
  have hb_mem : b ∈ x7 v := by rw [hab]; simp
  have ha_gates : a ∈ x5.gates := (List.mem_filter.mp ha_mem).1
  have hb_gates : b ∈ x5.gates := (List.mem_filter.mp hb_mem).1
  have ha_op : a.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) :=
    (hfan a ha_gates).1
  have hb_op : b.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) :=
    (hfan b hb_gates).1
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at ha_op hb_op
  rcases ha_op with ha_and | ha_or | ha_not
  · exact h_not_and x1 x2 x4 x5 hcub hgirth hadj hex hfan hfun hmin hdeg ⟨v, hv, hlen2, ⟨gnot, hgnot_mem, hgnot_op⟩, a, ha_mem, ha_and⟩ hvc
  · exact h_not_or x1 x2 x4 x5 hcub hgirth hadj hex hfan hfun hmin hdeg ⟨v, hv, hlen2, ⟨gnot, hgnot_mem, hgnot_op⟩, a, ha_mem, ha_or⟩ hvc
  · rcases hb_op with hb_and | hb_or | hb_not
    · exact h_not_and x1 x2 x4 x5 hcub hgirth hadj hex hfan hfun hmin hdeg ⟨v, hv, hlen2, ⟨gnot, hgnot_mem, hgnot_op⟩, b, hb_mem, hb_and⟩ hvc
    · exact h_not_or x1 x2 x4 x5 hcub hgirth hadj hex hfan hfun hmin hdeg ⟨v, hv, hlen2, ⟨gnot, hgnot_mem, hgnot_op⟩, b, hb_mem, hb_or⟩ hvc
    · refine h_not_not x1 x2 x4 x5 hcub hgirth hadj hex hfan hfun hmin hdeg ⟨v, hv, hlen2, ?_⟩ hvc
      intro g hg
      change g ∈ x7 v at hg
      rw [hab] at hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact ha_not
      · exact hb_not
