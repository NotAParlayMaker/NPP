import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3227_1
    (needFalse : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      C.gates.length = (14 : ℕ) → Monotone2 C → C.output = (23 : ℕ) →
        (∀ (x : Fin (9 : ℕ) → Bool),
          C.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ))]) =
            ([(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ),
              (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun n =>
                x (Fin.ofNat (9 : ℕ) (n / (10 : ℕ))) &&
                  x (Fin.ofNat (9 : ℕ) (n % (10 : ℕ))))) →
        ∃ m ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)],
          C.eval ((List.ofFn fun i : Fin (9 : ℕ) => m.testBit ↑i) ++ [Bool.false]) = Bool.false)
    (needTrue : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      C.gates.length = (14 : ℕ) → Monotone2 C → C.output = (23 : ℕ) →
        (∀ (x : Fin (9 : ℕ) → Bool),
          C.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ))]) =
            ([(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ),
              (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun n =>
                x (Fin.ofNat (9 : ℕ) (n / (10 : ℕ))) &&
                  x (Fin.ofNat (9 : ℕ) (n % (10 : ℕ))))) →
        ∃ m ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)],
          C.eval ((List.ofFn fun i : Fin (9 : ℕ) => m.testBit ↑i) ++ [Bool.true]) = Bool.true) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ x3 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], x2.eval ((List.ofFn fun (x4 : Fin (9 : ℕ)) => x3.testBit ↑x4) ++ [Bool.false]) = Bool.false) ∧ ∃ x3 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x2.eval ((List.ofFn fun (x4 : Fin (9 : ℕ)) => x3.testBit ↑x4) ++ [Bool.true]) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.gates.length = (14 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x3 → x3.output = (23 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ))]) = x1 x7) → x2 x3 := by
  intro F T C hlen hmono hout hcomp
  exact ⟨needFalse C hlen hmono hout hcomp, needTrue C hlen hmono hout hcomp⟩
