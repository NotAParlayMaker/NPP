import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- With the auxiliary input fixed to false, its designated OR reader is a copy
-- (or false). Bypassing it gives one ordinary circuit that must work on both
-- cubes x4 = false and x6 = false, a total of 384 truth-table rows.
theorem PEqualNP.Outside.R_meta_2022_3
    (bypass : ∀ (n : Nat) (pre post : List Gate) (ins : List Nat) (out : Nat),
      n ∈ ins →
      let C : Circuit := ⟨pre ++ ⟨.or,ins⟩ :: post,out⟩
      FanInTwo C →
      HasCircuitSize n (fun x => C.eval (List.ofFn x ++ [false])) (pre.length + post.length))
    (lower : ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool, (x 4 && x 6) = false ∧
        D.eval (List.ofFn x) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : List ℕ) (x4 : ℕ),   x1.length + x2.length ≤ (13 : ℕ) →     (∀ x6 ∈ x1, (9 : ℕ) ∉ x6.inputs) →       (9 : ℕ) ∈ x3 →         have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x3 : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := x4 : PEqualNP.CircuitLowerBounds.Circuit };         PEqualNP.MetaComplexity.FanInTwo x8 → x4 ≤ (24 : ℕ) → x4 ≠ (9 : ℕ) → (∀ x12 ∈ x8.gates, ∀ x14 ∈ x12.inputs, x14 ≤ (24 : ℕ)) → ∃ (x13 : Fin (9 : ℕ) → Bool), x8.eval (List.ofFn x13 ++ [x13 (4 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ))]) ≠ (x13 (0 : Fin (9 : ℕ)) && x13 (1 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (2 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (3 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (4 : Fin (9 : ℕ)) || x13 (4 : Fin (9 : ℕ)) && x13 (0 : Fin (9 : ℕ)) || x13 (0 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ)) || x13 (1 : Fin (9 : ℕ)) && x13 (6 : Fin (9 : ℕ)) || x13 (2 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (3 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (5 : Fin (9 : ℕ)) && x13 (7 : Fin (9 : ℕ)) || x13 (6 : Fin (9 : ℕ)) && x13 (8 : Fin (9 : ℕ)) || x13 (8 : Fin (9 : ℕ)) && x13 (5 : Fin (9 : ℕ))) := by
  intro pre post ins out budget _ reads C fan _ _ _
  obtain ⟨D, fanD, sizeD, simulates⟩ := bypass 9 pre post ins out reads fan
  obtain ⟨x, off, fails⟩ := lower D fanD (sizeD.trans budget)
  refine ⟨x, ?_⟩
  rw [off]
  exact fun eq => fails ((simulates x).trans eq)
