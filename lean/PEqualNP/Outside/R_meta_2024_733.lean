import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2024_733
    (hTable : ∀ m : Fin 512,
      let x := fun i : Fin 9 => decide ((m.val / (2 ^ (i.val % 9) : ℕ)) % 2 = 1)
      Nat.testBit 13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 m.val =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hFind : ∀ (A B : List Gate) (N : List ℕ) (o : ℕ),
      A.length + B.length ≤ 13 → (∀ g ∈ A, 9 ∉ g.inputs) → 9 ∈ N →
      let C : Circuit := ⟨A ++ ⟨GateOp.not, N⟩ :: B, o⟩
      FanInTwo C → o ≤ 24 → o ≠ 9 → (∀ g ∈ C.gates, ∀ w ∈ g.inputs, w ≤ 24) →
      ∃ m : Fin 512, let x := fun i : Fin 9 => decide ((m.val / (2 ^ (i.val % 9) : ℕ)) % 2 = 1)
        C.eval (List.ofFn x ++ [x 4 && x 6]) ≠ Nat.testBit 13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 m.val) :
    ∀ (x1 x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : List ℕ) (x4 : ℕ),   x1.length + x2.length ≤ (13 : ℕ) →     (∀ x6 ∈ x1, (9 : ℕ) ∉ x6.inputs) →       (9 : ℕ) ∈ x3 →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := x3 : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := x4 : PEqualNP.CircuitLowerBounds.Circuit };         PEqualNP.MetaComplexity.FanInTwo x8 → x4 ≤ (24 : ℕ) → x4 ≠ (9 : ℕ) → (∀ x12 ∈ x8.gates, ∀ x14 ∈ x12.inputs, x14 ≤ (24 : ℕ)) → ∃ (x13 : Fin (9 : ℕ) → Bool), x8.eval (List.ofFn x13 ++ [x13 (4 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ))]) ≠ (x13 (0 : Fin (9 : ℕ)) && x13 (1 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (2 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (3 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (4 : Fin (9 : ℕ)) || x13 (4 : Fin (9 : ℕ)) && x13 (0 : Fin (9 : ℕ)) || x13 (0 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (5 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (6 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (8 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ))) := by
  intro A B N o hLen hPre hNot
  dsimp only
  intro hFan hOut hOutNe hInputs
  obtain ⟨m, hm⟩ := hFind A B N o hLen hPre hNot hFan hOut hOutNe hInputs
  refine ⟨fun i => decide ((m.val / (2 ^ (i.val % 9) : ℕ)) % 2 = 1), ?_⟩
  have h := hTable m
  dsimp only at h hm
  rw [h] at hm
  exact hm
