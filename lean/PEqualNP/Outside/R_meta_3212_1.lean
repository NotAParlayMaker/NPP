import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3212_1
    (graphBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun k : ℕ => x (Fin.ofNat 8 (k / 8)) && x (Fin.ofNat 8 (k % 8))) →
      12 ≤ C.size)
    (removeConstantReads : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length ≤ 1) →
      C.eval (false :: List.ofFn (fun _ : Fin 8 => false) ++ [true]) = false →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧
        D.size + (C.gates.filter (fun g =>
          ([0, 9] : List ℕ).any (fun i => g.inputs.contains i))).length ≤ C.size ∧
        ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) = C.eval (false :: List.ofFn x ++ [true])) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.not → x3.inputs.length ≤ (1 : ℕ)) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5) x1.gates).length = (2 : ℕ) → (∀ (x5 : Fin (8 : ℕ) → Bool), x1.eval (Bool.false :: List.ofFn x5 ++ [Bool.true]) = [(1 : ℕ), (10 : ℕ), (19 : ℕ), (5 : ℕ), (14 : ℕ), (23 : ℕ), (38 : ℕ), (47 : ℕ), (60 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (8 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (8 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C hC hNot hCount hEval
  have hZero : C.eval (false :: List.ofFn (fun _ : Fin 8 => false) ++ [true]) = false := by
    rw [hEval]
    decide
  obtain ⟨D, hD, hSize, hSame⟩ := removeConstantReads C hC hNot hZero
  have hLower := graphBound D hD (fun x => (hSame x).trans (hEval x))
  rw [hCount] at hSize
  omega
