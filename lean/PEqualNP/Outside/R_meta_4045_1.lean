import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def SingerIncidence4045 (x : Fin 26 → Bool) : Prop :=
  ∃ (i j : Fin 13),
    (i = j ∨ i = j + 1 ∨ i = j + 3 ∨ i = j + 9) ∧
      x (Fin.castAdd 13 i) = true ∧ x (Fin.natAdd 13 j) = true

def SingerCircuitShape4045 (C : Circuit) : Prop :=
  ∀ (i : ℕ) (g : Gate), C.gates[i]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ (a b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + i ∧ b < 26 + i

def SingerRestriction4045 (C : Circuit) : Prop :=
  ∃ (v : Fin 26) (S : Finset ℕ), 5 ≤ S.card ∧
    ∀ j ∈ S, j < C.size ∧
      ∃ (b c : Bool) (p : ℕ), p < 26 + j ∧
        ∀ x : Fin 26 → Bool, x v = false →
          (C.wires (List.ofFn x)).getD (26 + j) false =
            (b && (C.wires (List.ofFn x)).getD p false || c)

theorem PEqualNP.Outside.R_meta_4045_1
    (hCore : ∀ C : Circuit, SingerCircuitShape4045 C → C.size ≤ 62 →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ SingerIncidence4045 x) →
      SingerRestriction4045 C)
    (hOutputBridge : ∀ (C : Circuit) (f : (Fin 26 → Bool) → ℕ → Bool),
      (∀ x : Fin 26 → Bool, ∀ i : ℕ,
        f x i = (C.wires (List.ofFn x)).getD i false) →
      (∀ x : Fin 26 → Bool, f x C.output = true ↔ SingerIncidence4045 x) →
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ SingerIncidence4045 x) :
    ∀ (x1 : Circuit) (x2 : (Fin 26 → Bool) → ℕ → Bool),
      (∀ (i : ℕ) (g : Gate), x1.gates[i]? = Option.some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ (a b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < (26 : ℕ) + i ∧ b < (26 : ℕ) + i) →
      x1.size ≤ (62 : ℕ) →
      (∀ x : Fin 26 → Bool, ∀ i : ℕ,
        x2 x i = (x1.wires (List.ofFn x)).getD i Bool.false) →
      (∀ x : Fin 26 → Bool, x2 x x1.output = Bool.true ↔
        ∃ (i j : Fin 13),
          (i = j ∨ i = j + (1 : Fin 13) ∨ i = j + (3 : Fin 13) ∨ i = j + (9 : Fin 13)) ∧
            x (Fin.castAdd (13 : ℕ) i) = Bool.true ∧
            x (Fin.natAdd (13 : ℕ) j) = Bool.true) →
      ∃ (v : Fin 26) (S : Finset ℕ), (5 : ℕ) ≤ S.card ∧
        ∀ j ∈ S, j < x1.size ∧
          ∃ (b c : Bool), ∃ p < (26 : ℕ) + j,
            ∀ x : Fin 26 → Bool, x v = Bool.false →
              x2 x ((26 : ℕ) + j) = (b && x2 x p || c) := by
  intro x1 x2 hShape hSize hWire hSpec
  have hCoreShape : SingerCircuitShape4045 x1 := hShape
  have hEval : ∀ x : Fin 26 → Bool,
      x1.eval (List.ofFn x) = true ↔ SingerIncidence4045 x :=
    hOutputBridge x1 x2 hWire hSpec
  obtain ⟨v, S, hCard, hGood⟩ := hCore x1 hCoreShape hSize hEval
  refine ⟨v, S, hCard, ?_⟩
  intro j hj
  obtain ⟨hjSize, b, c, p, hp, hEq⟩ := hGood j hj
  refine ⟨hjSize, b, c, p, hp, ?_⟩
  intro x hx
  rw [hWire x (26 + j), hWire x p]
  exact hEq x hx
