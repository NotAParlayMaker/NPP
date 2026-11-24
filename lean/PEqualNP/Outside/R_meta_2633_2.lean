import Mathlib
import PEqualNP.Defs

-- Split by the least vertex cover against the ordinary vertices read three times.
-- With a cover T of at most half the ordinary vertices plus the three-read ones, the slot count
-- and the cover circuit on the graph without one cover vertex give the four gates.
theorem PEqualNP.Outside.R_meta_2633_2
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      have F : (Fin n → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun G A;
      have R : Fin n → List PEqualNP.CircuitLowerBounds.Gate := fun v => C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains (v : ℕ);
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ u v, G.Adj u v → u ∉ A) →
      (∃ u v, G.Adj u v) →
      PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.circuitFun n C = F →
      (∀ s, PEqualNP.MetaComplexity.HasCircuitSize n F s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (R v).length) →
      (∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        2 * T.card ≤ Aᶜ.card + 2 * (Aᶜ.filter fun v => 3 ≤ (R v).length).card) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧
        PEqualNP.MetaComplexity.HasCircuitSize n (fun x => F (Function.update x v false)) s)
    (h2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ∉ x4, ∀ x18 ∈ x7 x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x17 ∉ x4, (x7 x17).length = (2 : ℕ)) → (∀ (T : Finset (Fin x1)), (∀ (u v : Fin x1), x2.Adj u v → u ∈ T ∨ v ∈ T) → x4ᶜ.card + (2 : ℕ) * (Finset.filter (fun (v : Fin x1) => (3 : ℕ) ≤ (x7 v).length) x4ᶜ).card < (2 : ℕ) * T.card) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ∉ x4, ∀ x18 ∈ x7 x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x17 ∉ x4, (x7 x17).length = (2 : ℕ)) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19 := by
  intro x1 x2 x3 x4 x5
  dsimp only
  intro hdeg hgirth hadj hedge hfan hfun hmin hread hor htwo
  by_cases hT : ∃ T : Finset (Fin x1), (∀ u v : Fin x1, x2.Adj u v → u ∈ T ∨ v ∈ T) ∧
      2 * T.card ≤ x4ᶜ.card + 2 * (x4ᶜ.filter fun v : Fin x1 => 3 ≤ (x5.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains (v : ℕ)).length).card
  · exact h1 x1 x2 x4 x5 hdeg hadj hedge hfan hfun hmin (fun v hv => (hread v hv).1) hT
  · refine h2 x1 x2 x4 x5 hdeg hgirth hadj hedge hfan hfun hmin hread hor htwo ?_
    intro T hTc
    exact Nat.lt_of_not_le (fun hle => hT ⟨T, hTc, hle⟩)
