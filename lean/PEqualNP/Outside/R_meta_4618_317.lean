import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4618_317
    (hAnd : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size →
      (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) →
      (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) →
      (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) →
      have x15 : Fin x5.size → ℕ := fun (x15 : Fin x5.size) => (List.foldl (fun (x16 : List ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) => x16 ++ [(if x16.length = x2 + x2 + ↑x15 then (1 : ℕ) else (0 : ℕ)) + (List.map (fun (x18 : ℕ) => x16.getD x18 (0 : ℕ)) x17.inputs).sum]) (List.replicate (x2 + x2) (0 : ℕ)) x5.gates).getD x5.output (0 : ℕ);
      x2 ≤ ∑ x16 : Fin x5.size, (x15 x16 - (100 : ℕ)) →
      (2 : ℕ) * (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval []) x5.gates).length ≤ x5.size →
      x2 * x1 ≤ (100 : ℕ) * x5.size)
    (hOr : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size →
      (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) →
      (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) →
      (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) →
      have x15 : Fin x5.size → ℕ := fun (x15 : Fin x5.size) => (List.foldl (fun (x16 : List ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) => x16 ++ [(if x16.length = x2 + x2 + ↑x15 then (1 : ℕ) else (0 : ℕ)) + (List.map (fun (x18 : ℕ) => x16.getD x18 (0 : ℕ)) x17.inputs).sum]) (List.replicate (x2 + x2) (0 : ℕ)) x5.gates).getD x5.output (0 : ℕ);
      x2 ≤ ∑ x16 : Fin x5.size, (x15 x16 - (100 : ℕ)) →
      (2 : ℕ) * (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval []) x5.gates).length ≤ x5.size →
      x2 * x1 ≤ (100 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.Monotone2 x5 →             x5.output < x2 + x2 + x5.size →               (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) →                 (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) →                   (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) →                     have x15 : Fin x5.size → ℕ := fun (x15 : Fin x5.size) => (List.foldl (fun (x16 : List ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) => x16 ++ [(if x16.length = x2 + x2 + ↑x15 then (1 : ℕ) else (0 : ℕ)) + (List.map (fun (x18 : ℕ) => x16.getD x18 (0 : ℕ)) x17.inputs).sum]) (List.replicate (x2 + x2) (0 : ℕ)) x5.gates).getD x5.output (0 : ℕ);                     x2 ≤ ∑ x16 : Fin x5.size, (x15 x16 - (100 : ℕ)) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro x1 x2 x3 _ x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 x15 h10
  have hsum : (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval []) x5.gates).length +
      (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval []) x5.gates).length = x5.size := by
    change (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval []) x5.gates).length +
      (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => !g.op.eval []) x5.gates).length = x5.gates.length
    induction x5.gates with
    | nil => rfl
    | cons g gs ih =>
      cases hb : g.op.eval [] <;> simp [hb] <;> omega
  by_cases hle : 2 * (List.filter (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval []) x5.gates).length ≤ x5.size
  · exact hAnd x1 x2 x3 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hle
  · exact hOr x1 x2 x3 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (by omega)
