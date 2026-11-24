import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.CircuitMoves PEqualNP.CleanedNonEdge

-- Lift only OR gates outside the OR closure of the output. Fewer gates
-- then lie outside that closure, so a minimum for this measure is normal.
theorem PEqualNP.Outside.R_meta_2978_3
    (lift : ∀ (n : ℕ) (C : Circuit), IsAO2 n C → C.output < n + C.gates.length →
      (∃ j < C.gates.length, (gateAt C j).op = .or ∧
        ¬ OrReaches n C C.output j ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ WireBelowOutput n C w) →
      ∃ E : Circuit, Lift n C E ∧ IsAO2 n E ∧ E.output < n + E.gates.length ∧
        circuitFun n E = circuitFun n C ∧ E.size ≤ C.size ∧
        (gatesWhere E (fun j => ¬ OrReaches n E E.output j)).card <
          (gatesWhere C (fun j => ¬ OrReaches n C C.output j)).card)
    (normalize : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [_x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true))
      → (¬ ∃ j < x5.gates.length, (gateAt x5 j).op = .or ∧
        ¬ OrReaches (x1 + x2) x5 x5.output j ∧
        ∃ w ∈ (gateAt x5 j).inputs, x1 + x2 ≤ w ∧ WireBelowOutput (x1 + x2) x5 w)
      → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [_x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10 := by
  intro n m I inst C square ao correct
  classical
  by_cases valid : C.output < n + m + C.gates.length
  · let cost (D : Circuit) :=
      (gatesWhere D (fun j => ¬ OrReaches (n + m) D D.output j)).card
    let candidates (k : ℕ) :=
      ∃ D : Circuit, IsAO2 (n + m) D ∧ D.output < n + m + D.gates.length ∧
        circuitFun (n + m) D = circuitFun (n + m) C ∧ D.size ≤ C.size ∧ cost D = k
    have existsCandidate : ∃ k, candidates k := ⟨cost C, C, ao, valid, rfl, le_rfl, rfl⟩
    obtain ⟨k, ⟨D, hD, out, functionEq, bound, rank⟩, minimal⟩ := Nat.findX existsCandidate
    have normal : ¬ ∃ j < D.gates.length, (gateAt D j).op = .or ∧
        ¬ OrReaches (n + m) D D.output j ∧
        ∃ w ∈ (gateAt D j).inputs, n + m ≤ w ∧ WireBelowOutput (n + m) D w := by
      intro h
      obtain ⟨E, _, hE, outE, eqE, boundE, smaller⟩ := lift (n + m) D hD out h
      have less : cost E < k := by
        change cost E < cost D at smaller
        exact rank ▸ smaller
      exact minimal (cost E) less
        ⟨E,hE,outE,eqE.trans functionEq,boundE.trans bound,rfl⟩
    obtain ⟨E,P,L,hE,sem,small,points,lines,ands⟩ :=
      normalize n m I D square hD
        (fun x => (congrFun functionEq x).trans (correct x)) normal
    exact ⟨E,P,L,hE,sem,small.trans bound,points,lines,ands⟩
  · let D : Circuit := ⟨[], n + m⟩
    refine ⟨D, ∅, ∅, ?_, ?_, ?_, by simp, by simp, by simp [D]⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg
        exact (List.not_mem_nil hg).elim
      · intro j hj
        exact (Nat.not_lt_zero j hj).elim
      · intro g hg
        exact (List.not_mem_nil hg).elim
    · intro x
      have lenStep (gs : List Gate) (v : List Bool) :
          (gs.foldl (fun w (g : Gate) =>
            w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).length =
              v.length + gs.length := by
        induction gs generalizing v with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons, ih]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
      have len : (C.wires (List.ofFn x)).length = n + m + C.gates.length := by
        unfold Circuit.wires
        rw [lenStep, List.length_ofFn]
      have originalFalse : circuitFun (n + m) C x = false := by
        change (C.wires (List.ofFn x)).getD C.output false = false
        exact List.getD_eq_default _ _ (by omega)
      have emptyFalse : circuitFun (n + m) D x = false := by
        change (List.ofFn x).getD (n + m) false = false
        exact List.getD_eq_default _ _ (by rw [List.length_ofFn])
      rw [emptyFalse, ← correct x, originalFalse]
    · change 0 ≤ C.size
      omega
