import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Cut the two-level witness into its P side and its L side.
theorem PEqualNP.Outside.R_meta_2846_1
    (hP : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : Circuit), have E : (Fin (Np + Nl) → Bool) → Prop := fun z =>
  (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true);
have Cor : Circuit → Prop := fun X =>
  (∀ z, circuitFun (Np + Nl) X z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true));
have Least : Prop :=
  (∀ D : Circuit, IsAO2 (Np + Nl) D → Cor D → C.size ≤ D.size);
have Op : ℕ → GateOp := fun i => (gateAt C i).op;
have Ins : ℕ → List ℕ := fun i => (gateAt C i).inputs;
have Top : Prop :=
  (∃ T : Finset ℕ,
    (∀ i ∈ T, i < C.gates.length ∧ Op i = GateOp.or ∧
      (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length,
        (Np + Nl + i ∈ Ins k' ↔ k' = k))) ∧
    ∀ w, (∀ z, (C.wires (List.ofFn z)).getD w false = true → E z) →
      (∃ k < C.gates.length, Op k = GateOp.or ∧ w ∈ Ins k) →
      ∀ k < C.gates.length, w ∈ Ins k → k ∈ T);
(∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → IsAO2 (Np + Nl) C → Cor C → Least → Top → ∃ P : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ Op i = GateOp.or ∧ ∀ u ∈ Ins i, u ∈ P))
    (hL : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : Circuit), have E : (Fin (Np + Nl) → Bool) → Prop := fun z =>
  (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true);
have Cor : Circuit → Prop := fun X =>
  (∀ z, circuitFun (Np + Nl) X z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true));
have Least : Prop :=
  (∀ D : Circuit, IsAO2 (Np + Nl) D → Cor D → C.size ≤ D.size);
have Op : ℕ → GateOp := fun i => (gateAt C i).op;
have Ins : ℕ → List ℕ := fun i => (gateAt C i).inputs;
have Top : Prop :=
  (∃ T : Finset ℕ,
    (∀ i ∈ T, i < C.gates.length ∧ Op i = GateOp.or ∧
      (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length,
        (Np + Nl + i ∈ Ins k' ↔ k' = k))) ∧
    ∀ w, (∀ z, (C.wires (List.ofFn z)).getD w false = true → E z) →
      (∃ k < C.gates.length, Op k = GateOp.or ∧ w ∈ Ins k) →
      ∀ k < C.gates.length, w ∈ Ins k → k ∈ T);
(∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → IsAO2 (Np + Nl) C → Cor C → Least → Top → ∀ P : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ Op i = GateOp.or ∧ ∀ u ∈ Ins i, u ∈ P) → ∃ L : Finset ℕ, (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ Op i = GateOp.or ∧ ∀ u ∈ Ins i, u ∈ L) ∧ ∀ i < C.gates.length, Op i = GateOp.and → ∃ a b : ℕ, Ins i = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro Np Nl I inst C hno hAO hcor hleast hT
  obtain ⟨P, hPgood⟩ := hP Np Nl I C hno hAO hcor hleast hT
  obtain ⟨L, hLgood, hAA⟩ := hL Np Nl I C hno hAO hcor hleast hT P hPgood
  exact ⟨P, L, hPgood, hLgood, hAA⟩
