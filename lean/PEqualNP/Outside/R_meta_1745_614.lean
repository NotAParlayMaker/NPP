import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1745_614
    (single : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ v : Fin x1, v ∉ x3 ∧ (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif g.op.eval [false] then 1 else 2) g.inputs).contains v.val) x5.gates).length ≤ 1) → ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16)
    (adjacent : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
  (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let readers (v : Fin n) := C.gates.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
  (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
  (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
  (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
  (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = f →
  (∀ s, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
  (∀ v ∉ A, (readers v).length ≤ 3 ∧
    ((readers v).length = 3 → ∀ g ∈ readers v, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
  (∀ v ∉ A, 2 ≤ (readers v).length) → ∃ u v : Fin n, G.Adj u v ∧ (readers u).length = 2 ∧ (readers v).length = 2)
    (contract : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
  (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let readers (v : Fin n) := C.gates.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
  (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
  (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
  (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
  (∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = f →
  (∀ s, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
  (∀ v ∉ A, (readers v).length ≤ 3 ∧
    ((readers v).length = 3 → ∀ g ∈ readers v, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
  (∀ v ∉ A, 2 ≤ (readers v).length) → (∃ u v : Fin n, G.Adj u v ∧ (readers u).length = 2 ∧ (readers v).length = 2) → ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x v false)) s) : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  classical
  intro n G A f C degree girth isolated edge spec fan computes least readBounds
  let readers (v : Fin n) := (C.gates.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length
  by_cases low : ∃ v : Fin n, v ∉ A ∧ readers v ≤ 1
  · exact single n G A f C degree girth isolated edge spec fan computes least readBounds low
  · have ge2 (v : Fin n) (hv : v ∉ A) : 2 ≤ readers v := by
      by_contra h
      exact low ⟨v,hv,by omega⟩
    have link := adjacent n G A f C degree girth isolated edge spec fan computes least readBounds ge2
    exact contract n G A f C degree girth isolated edge spec fan computes least readBounds ge2 link
