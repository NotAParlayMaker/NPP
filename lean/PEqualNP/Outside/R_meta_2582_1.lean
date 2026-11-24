import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2582_1
    (hBlockPoint : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ({i : Fin C.gates.length | (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (q + 1) * N) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 2)
    (hBlockLine : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ((q + 1) * N < {i : Fin C.gates.length | (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 2) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 2 := by
  intro q N I inst C hq hN hdeg hline hAO hfun
  by_cases hle : {i : Fin C.gates.length | (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (q + 1) * N
  · exact hBlockPoint q N I C hq hN hdeg hline hAO hfun hle
  · have hgt : (q + 1) * N < {i : Fin C.gates.length | (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by omega
    exact hBlockLine q N I C hq hN hdeg hline hAO hfun hgt