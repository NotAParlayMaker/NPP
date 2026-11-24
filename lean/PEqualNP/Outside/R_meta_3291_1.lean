import PEqualNP.Defs

set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.R_meta_3291_1
    (hSmallInput : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → (44 : ℕ) * x5.size < x2 * (x1 + (1 : ℕ)) → x5.output < x2 + x2 → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (44 : ℕ) * x5.size)
    (hSmallGate : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → (44 : ℕ) * x5.size < x2 * (x1 + (1 : ℕ)) → x2 + x2 ≤ x5.output → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (44 : ℕ) * x5.size)
    : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  classical
  intro q n r dec C hq hN hline huniq hAO hsound
  let P : Fin n × Fin n → Prop := fun e =>
    PEqualNP.MetaComplexity.circuitFun (n + n) C
      (fun i : Fin (n + n) =>
        Decidable.decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd n e.2)) = Bool.true
  have hFilter :
      Fintype.card {e : Fin n × Fin n // r e.1 e.2 ∧ P e} ≤
      Fintype.card {e : Fin n × Fin n // r e.1 e.2} :=
    by
      let f : {e : Fin n × Fin n // r e.1 e.2 ∧ P e} ↪
          {e : Fin n × Fin n // r e.1 e.2} :=
        ⟨(fun e => ⟨e.val, e.property.1⟩),
          by intro a b h; cases a; cases b; cases h; rfl⟩
      exact Fintype.card_le_of_injective f f.injective
  have hCount :
      Fintype.card {e : Fin n × Fin n // r e.1 e.2} = n * (q + 1) := by
    let equiv : {e : Fin n × Fin n // r e.1 e.2} ≃
        Σ l : Fin n, {p : Fin n // r p l} := {
      toFun := fun e => ⟨e.val.2, ⟨e.val.1, e.property⟩⟩
      invFun := fun t => ⟨(t.2.val, t.1), t.2.property⟩
      left_inv := by intro e; cases e; rfl
      right_inv := by intro t; cases t with | mk l p => cases p; rfl
    }
    rw [Fintype.card_congr equiv, Fintype.card_sigma]
    simp [hline]
  have hUpper :
      Fintype.card {e : Fin n × Fin n // r e.1 e.2 ∧ P e} ≤ n * (q + 1) := by
    omega
  by_cases hlarge : n * (q + 1) ≤ (44 : ℕ) * C.size
  · change Fintype.card {e : Fin n × Fin n // r e.1 e.2 ∧ P e} ≤
      (44 : ℕ) * C.size
    omega
  · have hsmall : (44 : ℕ) * C.size < n * (q + 1) := by omega
    by_cases hout : C.output < n + n
    · exact hSmallInput q n r C hq hN hline huniq hAO hsound hsmall hout
    · exact hSmallGate q n r C hq hN hline huniq hAO hsound hsmall (Nat.le_of_not_gt hout)
