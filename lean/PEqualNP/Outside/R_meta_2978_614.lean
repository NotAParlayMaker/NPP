import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first child extends itay-raveh’s branch and cover count (L-meta-614, #728)
-- to bipartite incidence with isolated vertices. It charges one distinct live
-- branch for each vertex in a cover of the edges having two non-leaf endpoints.
-- The third child is BastianMIllan’s checked star synthesis (L-meta-3493, #6920).
theorem PEqualNP.Outside.R_meta_2978_614
    (branch : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (C : Circuit),
      let E := PEqualNP.ReadTwo.incid I
      let V := E.image (fun e => Fin.castAdd m e.1) ∪ E.image (fun e => Fin.natAdd n e.2)
      let inner := fun K : Finset (Fin (n+m)) => ∀ p l, I p l →
        (∃ k, I p k ∧ k ≠ l) → (∃ q, I q l ∧ q ≠ p) →
        Fin.castAdd m p ∈ K ∨ Fin.natAdd n l ∈ K
      (∀ p q l k, p ≠ q → l ≠ k → ¬ (I p l ∧ I p k ∧ I q l ∧ I q k)) →
      PEqualNP.TopForm.IsAO2 (n+m) C →
      (∀ z : Fin (n+m) → Bool, circuitFun (n+m) C z = decide (∃ p l, I p l ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      ∃ K, inner K ∧ V.card + K.card ≤ C.size + 1)
    (remaining : ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (C : Circuit),
      let E := PEqualNP.ReadTwo.incid I
      let V := E.image (fun e => Fin.castAdd m e.1) ∪ E.image (fun e => Fin.natAdd n e.2)
      let covers := fun K : Finset (Fin (n+m)) => ∀ p l, I p l →
        Fin.castAdd m p ∈ K ∨ Fin.natAdd n l ∈ K
      let inner := fun K : Finset (Fin (n+m)) => ∀ p l, I p l →
        (∃ k, I p k ∧ k ≠ l) → (∃ q, I q l ∧ q ≠ p) →
        Fin.castAdd m p ∈ K ∨ Fin.natAdd n l ∈ K
      (∀ p q l k, p ≠ q → l ≠ k → ¬ (I p l ∧ I p k ∧ I q l ∧ I q k)) →
      PEqualNP.TopForm.IsAO2 (n+m) C →
      (∀ z : Fin (n+m) → Bool, circuitFun (n+m) C z = decide (∃ p l, I p l ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      ∀ K, inner K → V.card + K.card ≤ C.size + 1 →
      (∀ T, covers T → V.card + K.card < E.card + T.card) →
      ∃ T, covers T ∧ E.card + T.card ≤ C.size + 1)
    (synthesize : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [DecidableRel x3] (T : Finset (Fin (x1+x2))), (∀ p l, x3 p l → Fin.castAdd x2 p ∈ T ∨ Fin.natAdd x1 l ∈ T) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ (PEqualNP.ReadTwo.incid x3).card + T.card - 1 ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [_x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10 := by
  intro n m I inst C h4 ao correct
  let E := PEqualNP.ReadTwo.incid I
  let V := E.image (fun e => Fin.castAdd m e.1) ∪ E.image (fun e => Fin.natAdd n e.2)
  let full := fun K : Finset (Fin (n+m)) => ∀ p l, I p l → Fin.castAdd m p ∈ K ∨ Fin.natAdd n l ∈ K
  obtain ⟨K,inner,sz⟩ := branch n m I C h4 ao correct
  have budget : V.card + K.card ≤ C.size + 1 := sz
  have found : ∃ T, full T ∧ E.card + T.card ≤ C.size + 1 := by
    by_cases cheap : ∃ T, full T ∧ E.card + T.card ≤ V.card + K.card
    · obtain ⟨T,f,h⟩ := cheap
      exact ⟨T,f,h.trans budget⟩
    · exact remaining n m I C h4 ao correct K inner budget (fun T f =>
        Nat.lt_of_not_ge (fun h => cheap ⟨T,f,h⟩))
  obtain ⟨T,hit,price⟩ := found
  obtain ⟨D,P,L,valid,evalD,size,rest⟩ := synthesize n m I T hit
  change D.size ≤ E.card + T.card - 1 at size
  exact ⟨D,P,L,valid,evalD,by omega,rest⟩
