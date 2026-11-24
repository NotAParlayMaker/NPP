import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- Cut along the desk sketch, refining the cover charge of R_meta_2978_2.
-- A wire forces F when it is true only where F is true.
-- normalize (the known part, no graph involved): an OR gate with exactly one forcing input
-- can hand that input to a new top OR gate (the old gate slot is reused, so the size stays);
-- the function stays F, and the number of gates outside the top OR tree drops, so repeating
-- ends in a circuit no larger where every OR gate has both inputs forcing or neither.
-- blockCharge (the open part): only for such normal circuits, edges plus a vertex cover
-- are paid by the gates; this is the old charge with the normal form as an extra premise.
-- synthesize: the star circuit of a vertex cover, verbatim from R_meta_2978_2.
theorem PEqualNP.Outside.R_meta_2978_401
    (normalize : ∀ (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool), IsAO2 n C →
      (∀ z, circuitFun n C z = F z) →
      ∃ D : Circuit, IsAO2 n D ∧ (∀ z, circuitFun n D z = F z) ∧ D.size ≤ C.size ∧
        ∀ j < D.gates.length, (gateAt D j).op = GateOp.or → ∀ a b : ℕ, (gateAt D j).inputs = [a, b] →
          ((∀ z : Fin n → Bool, (D.wires (List.ofFn z)).getD a false = true → F z = true) ↔
            (∀ z : Fin n → Bool, (D.wires (List.ofFn z)).getD b false = true → F z = true)))
    (blockCharge : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [DecidableRel x3] (D : Circuit),
      (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) →
      IsAO2 (x1 + x2) D →
      (∀ z : Fin (x1 + x2) → Bool, circuitFun (x1 + x2) D z = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ z (Fin.castAdd x2 x9) = Bool.true ∧ z (Fin.natAdd x1 x10) = Bool.true)) →
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.or → ∀ a b : ℕ, (gateAt D j).inputs = [a, b] →
          ((∀ z : Fin (x1 + x2) → Bool, (D.wires (List.ofFn z)).getD a false = true → Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ z (Fin.castAdd x2 x9) = Bool.true ∧ z (Fin.natAdd x1 x10) = Bool.true) = true) ↔
            (∀ z : Fin (x1 + x2) → Bool, (D.wires (List.ofFn z)).getD b false = true → Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ z (Fin.castAdd x2 x9) = Bool.true ∧ z (Fin.natAdd x1 x10) = Bool.true) = true))) →
      ∃ T : Finset (Fin (x1 + x2)), (∀ p l, x3 p l → Fin.castAdd x2 p ∈ T ∨ Fin.natAdd x1 l ∈ T) ∧
        (PEqualNP.ReadTwo.incid x3).card + T.card ≤ D.size + 1)
    (synthesize : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [DecidableRel x3] (T : Finset (Fin (x1+x2))), (∀ p l, x3 p l → Fin.castAdd x2 p ∈ T ∨ Fin.natAdd x1 l ∈ T) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ (PEqualNP.ReadTwo.incid x3).card + T.card - 1 ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10 := by
  intro x1 x2 x3 x4 x5 hfree hao hfun
  obtain ⟨D, hD, hDfun, hDsize, hnf⟩ := normalize (x1 + x2) x5 _ hao hfun
  obtain ⟨T, covers, budget⟩ := blockCharge x1 x2 x3 D hfree hD hDfun hnf
  obtain ⟨E, P, L, valid, correct, size, rest⟩ := synthesize x1 x2 x3 T covers
  exact ⟨E, P, L, valid, correct, by omega, rest⟩
