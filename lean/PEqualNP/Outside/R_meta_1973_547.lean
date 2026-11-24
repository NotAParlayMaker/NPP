import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Set a vertex false. Every gate that reads it goes away, and so does every gate that reads an
-- AND or NOT gate reading it, since such a gate has become constant. killTwo says this for any
-- circuit, counting those gates. If some unmarked vertex has four of them the step holds at
-- once. What remains is fewKilled: every unmarked vertex has at most three.
theorem PEqualNP.Outside.R_meta_1973_547
    (killTwo : ∀ (n : ℕ) (C : Circuit) (v : Fin n), FanInTwo C →
      (∀ x : Fin n → Bool, circuitFun n C (Function.update x v false) = true) ∨
      ∃ E : Circuit, FanInTwo E ∧
        E.size + List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == ↑v || (Nat.ble n k && (C.gates[k - n]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains ↑v && !h.op.eval [Bool.true, Bool.false])))) C.gates ≤ C.size ∧
        ∀ x : Fin n → Bool, circuitFun n E x = circuitFun n C (Function.update x v false))
    (fewKilled : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       (2 : ℕ) ≤ x16.length ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length = (2 : ℕ)) → (∀ v ∉ x3, List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == ↑v || (Nat.ble x1 k && (x5.gates[k - x1]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains ↑v && !h.op.eval [Bool.true, Bool.false])))) x5.gates ≤ 3) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       (2 : ℕ) ≤ x16.length ∧ x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length = (2 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  intro n G A f C degree girth noMarked edge fSpec fan computes minimal readBounds twoReaders
  by_cases hk : ∃ v, v ∉ A ∧ 4 ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == ↑v || (Nat.ble n k && (C.gates[k - n]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains ↑v && !h.op.eval [Bool.true, Bool.false])))) C.gates
  · obtain ⟨v, hv, h4⟩ := hk
    rcases killTwo n C v fan with hT | ⟨E, hE, hEs, hEf⟩
    · exfalso
      have h1 := hT (fun _ => false)
      have h2 : Function.update (fun _ : Fin n => false) v false = fun _ => false := by
        funext i
        by_cases h : i = v
        · rw [h, Function.update_self]
        · rw [Function.update_of_ne h]
      rw [h2, computes] at h1
      rcases (fSpec _).mp h1 with ⟨a, _, ha⟩ | ⟨u, w, _, hu, _⟩
      · exact Bool.false_ne_true ha
      · exact Bool.false_ne_true hu
    · refine ⟨v, hv, E.size, by omega, E, hE, le_rfl, fun x => ?_⟩
      have h3 := hEf x
      rw [computes] at h3
      exact h3
  · exact fewKilled n G A f C degree girth noMarked edge fSpec fan computes minimal
      (fun v hv => ⟨(readBounds v hv).1, (readBounds v hv).2.2⟩)
      twoReaders (by
        intro v hv
        by_contra h
        exact hk ⟨v, hv, by omega⟩)
