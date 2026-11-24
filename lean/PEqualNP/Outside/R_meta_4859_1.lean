import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4859_1
    (h1 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.IsMinimalCircuit n C →
      PEqualNP.MetaComplexity.circuitFun n C = f →
      (∃ x y : Fin n → Bool, f x ≠ f y) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size ≤ C.size ∧
        PEqualNP.MetaComplexity.circuitFun n D = f ∧
        D.output < n + D.gates.length ∧
        ∀ i : Fin D.gates.length,
          let g := D.gates.get i
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
          ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
            g.inputs.length = 2 ∧ g.inputs.headD 0 ≠ g.inputs.tail.headD 0) ∧
          (∀ w ∈ g.inputs, w < n + (i : ℕ)))
    (h2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj]
      (x4 : Finset (Fin x1)) (D : PEqualNP.CircuitLowerBounds.Circuit)
      (x6 : ℕ) (x7 x8 : Fin x6 ↪ Fin x1),
      Odd x6 →
      (∀ x10 : Fin x6, x2.Adj (x7 x10) (x8 x10) ∧ x8 x10 ∉ Set.range ⇑x7) →
      (∀ x11 x12 : Fin x6, x2.Adj (x7 x11) (x7 x12) ↔
        (↑x11 + (1 : ℕ)) % x6 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x6 = ↑x11) →
      (∀ x12 : Fin x1, (x2.neighborSet x12).ncard = if x12 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →
      (7 : ℕ∞) ≤ x2.egirth →
      PEqualNP.MetaComplexity.FanInTwo D →
      PEqualNP.MetaComplexity.circuitFun x1 D = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →
      D.output < x1 + D.gates.length →
      (∀ i : Fin D.gates.length,
        let g := D.gates.get i
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) ∧
        ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
          g.inputs.length = 2 ∧ g.inputs.headD 0 ≠ g.inputs.tail.headD 0) ∧
        (∀ w ∈ g.inputs, w < x1 + (i : ℕ))) →
      ∃ (x16 : Fin x6) (x17 : Fin x6),
        x2.Adj (x7 x16) (x7 x17) ∧
        ∃ (x18 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo (x18 (0 : ℕ)) ∧
          (x18 (0 : ℕ)).size ≤ D.size ∧
          PEqualNP.MetaComplexity.circuitFun x1 (x18 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 D ∧
          ∀ x19 < (7 : ℕ),
            ∃ (x21 : ℕ) (x22 : ℕ),
              x21 < (x18 x19).size ∧
              (x22 < x1 + x21 ∨ x1 + (x18 x19).size ≤ x22) ∧
              x18 (x19 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x18 x19) x21 x22 ∧
              ((∀ (x23 : Fin x1 → Bool),
                  have x24 : List Bool := (x18 x19).wires (List.ofFn (Function.update (Function.update x23 (x7 x16) Bool.false) (x7 x17) Bool.false));
                  x24.getD (x1 + x21) Bool.false = x24.getD x22 Bool.false) ∨
                (x18 x19).output ≠ x1 + x21 ∧ ∀ x23 ∈ List.drop (x21 + (1 : ℕ)) (x18 x19).gates, x1 + x21 ∉ x23.inputs)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 x8 : Fin x6 ↪ Fin x1),   Odd x6 →     (∀ (x10 : Fin x6), x2.Adj (x7 x10) (x8 x10) ∧ x8 x10 ∉ Set.range ⇑x7) →       (∀ (x11 x12 : Fin x6), x2.Adj (x7 x11) (x7 x12) ↔ (↑x11 + (1 : ℕ)) % x6 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x6 = ↑x11) →         (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard = if x12 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →           (7 : ℕ∞) ≤ x2.egirth →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →                 ∃ (x16 : Fin x6) (x17 : Fin x6),                   x2.Adj (x7 x16) (x7 x17) ∧                     ∃ (x18 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo (x18 (0 : ℕ)) ∧                         (x18 (0 : ℕ)).size ≤ x5.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 (x18 (0 : ℕ)) = PEqualNP.MetaComplexity.circuitFun x1 x5 ∧                             ∀ x19 < (7 : ℕ),                               ∃ (x21 : ℕ) (x22 : ℕ),                                 x21 < (x18 x19).size ∧                                   (x22 < x1 + x21 ∨ x1 + (x18 x19).size ≤ x22) ∧                                     x18 (x19 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate x1 (x18 x19) x21 x22 ∧                                       ((∀ (x23 : Fin x1 → Bool),                                           have x24 : List Bool := (x18 x19).wires (List.ofFn (Function.update (Function.update x23 (x7 x16) Bool.false) (x7 x17) Bool.false));                                           x24.getD (x1 + x21) Bool.false = x24.getD x22 Bool.false) ∨                                         (x18 x19).output ≠ x1 + x21 ∧ ∀ x23 ∈ List.drop (x21 + (1 : ℕ)) (x18 x19).gates, x1 + x21 ∉ x23.inputs) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 hodd hadj8 hadj7 hdeg hgirth hmin hfun
  have hx6_pos : 0 < x6 := by
    rcases hodd with ⟨k, rfl⟩
    omega
  have hnonconst : ∃ x y : Fin x1 → Bool,
      PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 x ≠
      PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 y := by
    refine ⟨fun _ => Bool.false, fun _ => Bool.true, ?_⟩
    have hedge : x2.Adj (x7 ⟨0, hx6_pos⟩) (x8 ⟨0, hx6_pos⟩) := (hadj8 ⟨0, hx6_pos⟩).1
    have h0 : PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (fun _ => Bool.false) = Bool.false := by
      simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
    have h1v : PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (fun _ => Bool.true) = Bool.true := by
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, decide_eq_true_eq]
      exact Or.inr ⟨x7 ⟨0, hx6_pos⟩, x8 ⟨0, hx6_pos⟩, hedge, rfl, rfl⟩
    rw [h0, h1v]
    decide
  obtain ⟨D, hDfan, hDsize, hDfun, hDout, hDclean⟩ :=
    h1 x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x5 hmin hfun hnonconst
  obtain ⟨x16, x17, hadj16, x18, h18fan, h18size, h18fun, hsteps⟩ :=
    h2 x1 x2 x4 D x6 x7 x8 hodd hadj8 hadj7 hdeg hgirth hDfan hDfun hDout hDclean
  refine ⟨x16, x17, hadj16, x18, h18fan, Nat.le_trans h18size hDsize, ?_, hsteps⟩
  rw [h18fun, hDfun, hfun]
