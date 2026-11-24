import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Each endpoint is essential because the circuit accepts its edge and rejects each singleton.
-- This pays for all edge sets whose size is at most 24 times one fewer than their endpoint count.
theorem PEqualNP.Outside.R_meta_3475_415
    (endpointBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (E : Finset (Fin N × Fin N)),
  1 ≤ q → (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
  (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
    (¬ ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
    circuitFun (N+N) C x = false) →
  let touches := fun (v : Fin (N+N)) (e : Fin N × Fin N) =>
    v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
  (∀ e ∈ E, circuitFun (N+N) C (fun v => decide (touches v e)) = true) →
  (E.biUnion fun e => {Fin.castAdd N e.1, Fin.natAdd N e.2}).card ≤ C.size + 1)
    (denselySupported : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)), (87 : ℕ) ≤ x1 →
       x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →
       (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →
       PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →
       (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
       let x13 : Fin (x2 + x2) →
       Fin x2 × Fin x2 →
       Prop := fun (x13 : Fin (x2 + x2)) (x14 : Fin x2 × Fin x2) => x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2; (∀ x14 ∈ x6, x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x13 x16 x14)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x2 ≤ x16)) (↑x14.1) (x2 + ↑x14.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x16 < x2)) (↑x14.1) (x2 + ↑x14.2) = Bool.false) →
       (∀ x15 ∈ x6, ∀ (x17 : Fin (x2 + x2)), x13 x17 x15 → (24 : ℕ) < (Finset.filter (x13 x17) x6).card) →
       (24 : ℕ) * ((x6.biUnion fun e => {Fin.castAdd x2 e.1, Fin.natAdd x2 e.2}).card - 1) < x6.card →
       x6.card ≤ (24 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)), (87 : ℕ) ≤ x1 →
       x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →
       (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →
       PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →
       (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
       let x13 : Fin (x2 + x2) →
       Fin x2 × Fin x2 →
       Prop := fun (x13 : Fin (x2 + x2)) (x14 : Fin x2 × Fin x2) => x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2; (∀ x14 ∈ x6, x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x13 x16 x14)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x2 ≤ x16)) (↑x14.1) (x2 + ↑x14.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x16 < x2)) (↑x14.1) (x2 + ↑x14.2) = Bool.false) →
       (∀ x15 ∈ x6, ∀ (x17 : Fin (x2 + x2)), x13 x17 x15 → (24 : ℕ) < (Finset.filter (x13 x17) x6).card) →
       x6.card ≤ (24 : ℕ) * x5.size := by
  intro q N I _ C E hq hn column unique model sound
  dsimp only
  intro covered largeDegree
  let ends := E.biUnion fun e => {Fin.castAdd N e.1, Fin.natAdd N e.2}
  have bound : ends.card ≤ C.size + 1 :=
    endpointBound q N I C E (by omega) (fun g hg => (model.2.2 g hg).le)
      sound (fun e he => (covered e he).2.1)
  by_cases paid : E.card ≤ 24 * (ends.card - 1)
  · exact paid.trans (Nat.mul_le_mul_left 24 (by omega))
  · exact denselySupported q N I C E hq hn column unique model sound covered largeDegree
      (Nat.lt_of_not_ge paid)
