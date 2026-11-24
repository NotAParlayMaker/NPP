import Mathlib
import PEqualNP.Defs

-- Cut the top-stuck least circuit case by whether an AND gate appears at all:
-- no AND gate, or some AND gate.
theorem PEqualNP.Outside.R_meta_2846_1
    (hNoAnd : let cCI := PEqualNP.CircuitLowerBounds.Circuit;
  ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : cCI),
      let cN := Np + Nl;
      let cZB := Fin (Np + Nl) → Bool;
      let cE : cZB → Prop := fun z => ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true;
      let cCF := PEqualNP.MetaComplexity.circuitFun (Np + Nl);
      let cGA := PEqualNP.MetaComplexity.NestedCover.gateAt C;
      let cAO := PEqualNP.TopForm.IsAO2 (Np + Nl);
      let cOR := PEqualNP.CircuitLowerBounds.GateOp.or;
      let cAN := PEqualNP.CircuitLowerBounds.GateOp.and;
      let cGL := C.gates.length; (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → cAO C → (∀ z : cZB, cCF C z = decide (cE z)) → (∀ D : cCI, cAO D → (∀ z : cZB, cCF D z = decide (cE z)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < cGL ∧ (cGA i).op = cOR ∧ (cN + i = C.output ∨ ∃ k ∈ T, ∀ k' < cGL, (cN + i ∈ (cGA k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : cZB, (C.wires (List.ofFn z)).getD w false = true → cE z) → (∃ k < cGL, (cGA k).op = cOR ∧ w ∈ (cGA k).inputs) → ∀ k < cGL, w ∈ (cGA k).inputs → k ∈ T) → (∀ i < cGL, (cGA i).op ≠ cAN) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < cGL, w = cN + i ∧ (cGA i).op = cOR ∧ ∀ u ∈ (cGA i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < cN) ∨ ∃ i < cGL, w = cN + i ∧ (cGA i).op = cOR ∧ ∀ u ∈ (cGA i).inputs, u ∈ L) ∧ ∀ i < cGL, (cGA i).op = cAN → ∃ a b : ℕ, (cGA i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))))
    (hAnd : let cCI := PEqualNP.CircuitLowerBounds.Circuit;
  ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : cCI),
      let cN := Np + Nl;
      let cZB := Fin (Np + Nl) → Bool;
      let cE : cZB → Prop := fun z => ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true;
      let cCF := PEqualNP.MetaComplexity.circuitFun (Np + Nl);
      let cGA := PEqualNP.MetaComplexity.NestedCover.gateAt C;
      let cAO := PEqualNP.TopForm.IsAO2 (Np + Nl);
      let cOR := PEqualNP.CircuitLowerBounds.GateOp.or;
      let cAN := PEqualNP.CircuitLowerBounds.GateOp.and;
      let cGL := C.gates.length; (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → cAO C → (∀ z : cZB, cCF C z = decide (cE z)) → (∀ D : cCI, cAO D → (∀ z : cZB, cCF D z = decide (cE z)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < cGL ∧ (cGA i).op = cOR ∧ (cN + i = C.output ∨ ∃ k ∈ T, ∀ k' < cGL, (cN + i ∈ (cGA k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : cZB, (C.wires (List.ofFn z)).getD w false = true → cE z) → (∃ k < cGL, (cGA k).op = cOR ∧ w ∈ (cGA k).inputs) → ∀ k < cGL, w ∈ (cGA k).inputs → k ∈ T) → (∃ i < cGL, (cGA i).op = cAN) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < cGL, w = cN + i ∧ (cGA i).op = cOR ∧ ∀ u ∈ (cGA i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < cN) ∨ ∃ i < cGL, w = cN + i ∧ (cGA i).op = cOR ∧ ∀ u ∈ (cGA i).inputs, u ∈ L) ∧ ∀ i < cGL, (cGA i).op = cAN → ∃ a b : ℕ, (cGA i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)))) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → C.size ≤ D.size) → (∃ T : Finset ℕ, (∀ i ∈ T, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (Np + Nl + i = C.output ∨ ∃ k ∈ T, ∀ k' < C.gates.length, (Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs ↔ k' = k))) ∧ ∀ w : ℕ, (∀ z : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z)).getD w false = true → ∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) → (∃ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → ∀ k < C.gates.length, w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k ∈ T) → (∃ P L : Finset ℕ, (∀ w ∈ P, w < Np ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < C.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, u ∈ L) ∧ ∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) := by
  intro Np Nl I _ C h1 h2 h3 h4 h5
  classical
  by_cases h : ∃ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact hAnd Np Nl I C h1 h2 h3 h4 h5 h
  · push_neg at h
    exact hNoAnd Np Nl I C h1 h2 h3 h4 h5 h
