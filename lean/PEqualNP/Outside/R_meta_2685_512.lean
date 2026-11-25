import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.BicliqueBlockCost

-- Lift to normal form (every OR with an operand below the function is itself below it),
-- charge a block cover to a normal circuit, then compile the block cover two-level.
theorem PEqualNP.Outside.R_meta_2685_512
    (lift : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : Circuit),
      IsAO2 (Np + Nl) C →
      (∀ z : Fin (Np + Nl) → Bool, circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl,
        I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      ∃ D : Circuit, IsAO2 (Np + Nl) D ∧
        (∀ z : Fin (Np + Nl) → Bool, circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl,
          I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) ∧
        D.size ≤ C.size ∧
        ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.or →
          ∀ a ∈ (NestedCover.gateAt D j).inputs, ∀ b ∈ (NestedCover.gateAt D j).inputs,
            (∀ x : Fin (Np + Nl) → Bool, (D.wires (List.ofFn x)).getD a false = true →
              ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ x (Fin.castAdd Nl p) = true ∧ x (Fin.natAdd Np l) = true) →
            (∀ x : Fin (Np + Nl) → Bool, (D.wires (List.ofFn x)).getD b false = true →
              ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ x (Fin.castAdd Nl p) = true ∧ x (Fin.natAdd Np l) = true))
    (charge : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      IsAO2 (Np + Nl) C →
      (∀ z : Fin (Np + Nl) → Bool, circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl,
        I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      (∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.or →
          ∀ a ∈ (NestedCover.gateAt C j).inputs, ∀ b ∈ (NestedCover.gateAt C j).inputs,
            (∀ x : Fin (Np + Nl) → Bool, (C.wires (List.ofFn x)).getD a false = true →
              ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ x (Fin.castAdd Nl p) = true ∧ x (Fin.natAdd Np l) = true) →
            (∀ x : Fin (Np + Nl) → Bool, (C.wires (List.ofFn x)).getD b false = true →
              ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ x (Fin.castAdd Nl p) = true ∧ x (Fin.natAdd Np l) = true)) →
      HasBlockCost (SimpleGraph.fromRel fun u v : Fin (Np + Nl) =>
        ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ u = Fin.castAdd Nl p ∧ v = Fin.natAdd Np l) C.size)
    (realize : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (c : ℕ),
      HasBlockCost (SimpleGraph.fromRel fun u v : Fin (Np + Nl) =>
        ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ u = Fin.castAdd Nl p ∧ v = Fin.natAdd Np l) c →
      ∃ (D : Circuit) (P L : Finset ℕ), IsAO2 (Np + Nl) D ∧
        (∀ y : Fin (Np + Nl) → Bool, circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl,
          I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ c ∧
        (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧
          (NestedCover.gateAt D i).op = GateOp.or ∧ ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧
          (NestedCover.gateAt D i).op = GateOp.or ∧ ∀ u ∈ (NestedCover.gateAt D i).inputs, u ∈ L) ∧
        ∀ i < D.gates.length, (NestedCover.gateAt D i).op = GateOp.and → ∃ a b : ℕ,
          (NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) :
    (∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro Np Nl I _ C free ao correct
  obtain ⟨C', ao', correct', size', normal'⟩ := lift Np Nl I C ao correct
  have hb := charge Np Nl I C' free ao' correct' normal'
  obtain ⟨D, P, L, aoD, fD, sD, hP, hL, hA⟩ := realize Np Nl I C'.size hb
  exact ⟨D, P, L, aoD, fD, by omega, hP, hL, hA⟩
