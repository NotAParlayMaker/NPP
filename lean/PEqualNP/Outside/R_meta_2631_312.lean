import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_2631_312
    (compileRestriction : ∀ (n : ℕ) (C : Circuit),
      let effective := fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2);
    let fixedReaders := fun v : Fin n =>
      {j : ℕ | j < C.size ∧ ∃ w ∈ effective (gateAt C j), w < n+j ∧
        ∃ b, ∀ x : Fin n → Bool, wval C (Function.update x v false) w = b}.ncard;
      FanInTwo C → ∀ v : Fin n, 4 ≤ fixedReaders v →
      (circuitFun n C (fun _ => false) = false) →
      ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) s)
    (fewConstantReads : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let effective := fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2);
    let fixedReaders := fun v : Fin n =>
      {j : ℕ | j < C.size ∧ ∃ w ∈ effective (gateAt C j), w < n+j ∧
        ∃ b, ∀ x : Fin n → Bool, wval C (Function.update x v false) w = b}.ncard;
      let f := graphFun G A;
      let readers := fun v : Fin n => C.gates.filter (fun g => (effective g).contains v.val);
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) →
      FanInTwo C → circuitFun n C = f →
      (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
        ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, (readers v).length = 2 ∧ ∃ g ∈ readers v, g.op = .and) →
      (∀ v ∉ A, fixedReaders v ≤ 3) →
      ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  intro n G _ A C f readers degree girth noMarked edge fan computes least reads hasAnd
  let effective := fun g : Gate => g.inputs.take (bif g.op.eval [false] then 1 else 2)
  let fixedReaders := fun v : Fin n =>
    {j : ℕ | j < C.size ∧ ∃ w ∈ effective (gateAt C j), w < n+j ∧
      ∃ b, ∀ x : Fin n → Bool, wval C (Function.update x v false) w = b}.ncard
  by_cases large : ∃ v ∉ A, 4 ≤ fixedReaders v
  · obtain ⟨v, hv, ht⟩ := large
    have allFalse : circuitFun n C (fun _ => false) = false := by
      rw [computes]
      change (decide (∃ a ∈ A, false = true) ||
        decide (∃ u w, G.Adj u w ∧ false = true ∧ false = true)) = false
      simp (config := {congrConsts := false})
    obtain ⟨s, hs, hcir⟩ := compileRestriction n C fan v ht allFalse
    rw [computes] at hcir
    exact ⟨v, hv, s, hs, hcir⟩
  · have small (v : Fin n) (hv : v ∉ A) : fixedReaders v ≤ 3 := by
      have h : ¬ 4 ≤ fixedReaders v := fun hv4 => large ⟨v, hv, hv4⟩
      omega
    exact fewConstantReads n G A C degree girth noMarked fan computes least reads hasAnd small
