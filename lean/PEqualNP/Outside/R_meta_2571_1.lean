import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2571_1
    (main : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 43 ∧ C.output < 25 + C.size ∧
      ∀ x : Fin 25 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ i j : Fin 25, i.val < 12 ∧ 12 ≤ j.val ∧
          (i.val + j.val + 2) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
          i.val ∉ ([0, 2, 8] : List ℕ) ∧ x i = true ∧ x j = true)
    (extend : ∀ C : Circuit, Monotone2 C → C.output < 25 + C.size →
      let D : Circuit := ⟨C.gates ++ [⟨GateOp.or, [13, 15]⟩,
        ⟨GateOp.or, [25 + C.size, 21]⟩], C.output⟩
      Monotone2 D ∧ D.size = C.size + 2 ∧ ∀ x : Fin 25 → Bool,
        D.eval (List.ofFn x) = C.eval (List.ofFn x) ∧
        (D.wires (List.ofFn x)).getD (25 + C.size + 1) false =
          (x 13 || x 15 || x 21)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  obtain ⟨C, hMono, hSize, hOutput, hSpec⟩ := main
  let D : Circuit := ⟨C.gates ++ [⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.or, [25 + C.size, 21]⟩], C.output⟩
  have hD := extend C hMono hOutput
  change Monotone2 D ∧ D.size = C.size + 2 ∧ ∀ x : Fin 25 → Bool,
    D.eval (List.ofFn x) = C.eval (List.ofFn x) ∧
    (D.wires (List.ofFn x)).getD (25 + C.size + 1) false =
      (x 13 || x 15 || x 21) at hD
  refine ⟨D, 25 + C.size + 1, hD.1, ?_, ?_, ?_, ?_⟩
  · rw [hD.2.1]
    omega
  · change C.output < 25 + D.size
    rw [hD.2.1]
    omega
  · rw [hD.2.1]
    omega
  · intro x
    rw [(hD.2.2 x).1]
    exact ⟨hSpec x, fun _ => (hD.2.2 x).2⟩
