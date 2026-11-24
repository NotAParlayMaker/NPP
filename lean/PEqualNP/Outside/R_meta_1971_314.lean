import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A sole binary reader has a single assignment that detects bypassing the reader.
-- On a negative assignment each neighbor gives two specified changes at its other operand.
-- The graph and minimality conversions follow the width reduction in PR #10297.
theorem PEqualNP.Outside.R_meta_1971_314
    (obstruction : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    let f := graphFun G A
    let reads (v : Fin n) := C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    let witness (v : Fin n) := ∀ (B D : Circuit) (g : Gate),
      C = ⟨B.gates ++ g :: D.gates,D.output⟩ → g.op.eval [false] = false →
      g.inputs.Perm [v.val,B.output] → B.output ≠ v.val → D.output ≠ v.val →
      ∃ x : Fin n → Bool, let h := circuitFun n B
        let b := g.op.eval []
        x v = b ∧ h x = !b ∧ D.eval (B.wires (List.ofFn x) ++ [x v]) ≠ f x ∧
        (f x = false → ∀ u, G.Adj v u → ∀ z : Bool, h (fun i => (z && decide (i=v)) ||
          (decide (i=u) || (x i && !decide (G.Adj u i)))) = b)
    (∀ i j, G.Adj i j → i ∉ A) → IsMinimalCircuit n C → circuitFun n C = f → ∀ v, (reads v).length ≤ 1 → witness v)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    let f := graphFun G A
    let reads (v : Fin n) := C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    let witness (v : Fin n) := ∀ (B D : Circuit) (g : Gate),
      C = ⟨B.gates ++ g :: D.gates,D.output⟩ → g.op.eval [false] = false →
      g.inputs.Perm [v.val,B.output] → B.output ≠ v.val → D.output ≠ v.val →
      ∃ x : Fin n → Bool, let h := circuitFun n B
        let b := g.op.eval []
        x v = b ∧ h x = !b ∧ D.eval (B.wires (List.ofFn x) ++ [x v]) ≠ f x ∧
        (f x = false → ∀ u, G.Adj v u → ∀ z : Bool, h (fun i => (z && decide (i=v)) ||
          (decide (i=u) || (x i && !decide (G.Adj u i)))) = b)
    (∀ i j, G.Adj i j → i ∉ A) → IsMinimalCircuit n C → circuitFun n C = f →
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) → 7 ≤ G.egirth →
    (∀ v ∉ A, (reads v).length ≤ 3 ∧ ((reads v).length = 3 → ∀ g ∈ reads v, g.op = .or)) →
    (∃ v ∉ A, (reads v).length ≤ 1 ∧ witness v) →
    ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length ≤ (1 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  classical
  intro n G A f C degree girth unmarked _edge description fan computes least bounds few
  have exactGraph : graphFun G A = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) ||
      decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = true ↔ f x = true
    rw [description x]
    simp only [Bool.or_eq_true,decide_eq_true_eq]
  have minimal : IsMinimalCircuit n C :=
    ⟨fan,fun D h eq => least D.size ⟨D,h,le_rfl,congrFun (eq.trans computes)⟩⟩
  have wide : 7 ≤ G.egirth := by
    apply SimpleGraph.le_egirth.mpr
    exact fun v p hc => by exact_mod_cast girth v p hc
  obtain ⟨v,hv,one⟩ := few
  have result := residual n G A C unmarked minimal (computes.trans exactGraph.symm) degree wide bounds
    ⟨v,hv,one,obstruction n G A C unmarked minimal (computes.trans exactGraph.symm) v one⟩
  rwa [exactGraph] at result
