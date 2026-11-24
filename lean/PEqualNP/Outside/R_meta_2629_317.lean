import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_2629_317
    (compile : ∀ (x1 : ℕ) (x2 : Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x3 →     ∀ (x5 : Finset ((Fin x1 → Bool) → Bool)),       (∀ (x6 : Fin x3.size),           have x7 : (Fin x1 → Bool) → Bool := fun (x7 : Fin x1 → Bool) => (x3.wires (List.ofFn (Function.update x7 x2 Bool.false))).getD (x1 + ↑x6) Bool.false;           (∃ (x8 : Bool), x7 = fun (x9 : Fin x1 → Bool) => x8) ∨ (∃ (x8 : Fin x1), x7 = fun (x9 : Fin x1 → Bool) => x9 x8) ∨ x7 ∈ x5) →         PEqualNP.MetaComplexity.circuitFun x1 x3 (Function.update (fun (x7 : Fin x1) => Bool.false) x2 Bool.false) = Bool.false → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x8 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x3 (Function.update x8 x2 Bool.false)) x5.card)
    (coverage : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (j : Fin C.size), FanInTwo C → (C.gates.get j).op = .not → v.val ∈ (C.gates.get j).inputs.take 1 → let eff (k : Fin C.size) := let r := C.gates.get k; r.inputs.take (bif r.op.eval [false] then 1 else 2)
      let readers := (Finset.univ.filter (fun k => v.val ∈ eff k ∨ (j < k ∧ n+j.val ∈ eff k)))
      4 ≤ readers.card → ∃ S : Finset ((Fin n → Bool) → Bool), S.card+4 ≤ C.size ∧ ∀ i : Fin C.size, let f := fun x : Fin n → Bool => (C.wires (List.ofFn (Function.update x v false))).getD (n+i.val) false; (∃ c : Bool, f = fun _ => c) ∨ (∃ u : Fin n, f = fun x => x u) ∨ f ∈ S)
    (narrow : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ u ∉ x4, (x7 u).length = 2 ∨ (x7 u).length = 3 ∧ ∀ g ∈ x7 u, g.op = GateOp.or) → (∃ v ∉ x4, ∃ j : Fin x5.size, let g := x5.gates.get j; g.op = GateOp.not ∧ v.val ∈ g.inputs.take 1 ∧ let eff (k : Fin x5.size) := let r := x5.gates.get k; r.inputs.take (bif r.op.eval [false] then 1 else 2)
      let readers := (Finset.univ.filter (fun k => v.val ∈ eff k ∨ (j < k ∧ x1+j.val ∈ eff k)))
      readers.card ≤ 3) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  intro n G dec A C
  dsimp only
  intro cubic girth isolated edge fan computed minimal reads hnot
  obtain ⟨v, hv, two, g, hg, hop⟩ := hnot
  obtain ⟨mem, readsV⟩ := List.mem_filter.mp hg
  obtain ⟨k, hk, ek⟩ := List.getElem_of_mem mem
  let j : Fin C.size := ⟨k, hk⟩
  have index : C.gates.get j = g := ek
  have isNot : (C.gates.get j).op = GateOp.not := by rw [index]; exact hop
  have hits : v.val ∈ (C.gates.get j).inputs.take 1 := by
    rw [index]
    rw [hop] at readsV
    change (g.inputs.take 1).contains v.val = true at readsV
    exact List.contains_iff_mem.mp readsV
  let eff (k : Fin C.size) :=
    let r := C.gates.get k
    r.inputs.take (bif r.op.eval [false] then 1 else 2)
  let D := Finset.univ.filter (fun k => v.val ∈ eff k ∨ (j < k ∧ n+j.val ∈ eff k))
  by_cases bound : D.card ≤ 3
  · apply narrow n G A C cubic girth isolated fan computed minimal
    · intro u hu
      obtain ⟨low,high,hor⟩ := reads u hu
      have split (a : ℕ) (l : 2 ≤ a) (h : a ≤ 3) : a = 2 ∨ a = 3 := by omega
      rcases split _ low high with he | he
      · exact Or.inl he
      · exact Or.inr ⟨he,hor he⟩
    · exact ⟨v,hv,j,isNot,hits,bound⟩
  obtain ⟨S, size, covers⟩ := coverage n C v j fan isNot hits (show 4 ≤ D.card by omega)
  have hz : circuitFun n C (Function.update (fun _ => false) v false) = false := by
    rw [computed]
    have pinned : Function.update (fun _ : Fin n => false) v false = (fun _ => false) := by
      funext u
      by_cases h : u = v <;> simp [h]
    rw [pinned]
    change (decide (∃ a ∈ A, false = true) || decide (∃ a b, G.Adj a b ∧ false = true ∧ false = true)) = false
    simp
  have result := compile n v C fan S covers hz
  rw [computed] at result
  exact ⟨v, hv, S.card, size, result⟩
