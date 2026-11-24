import Mathlib
import PEqualNP.Defs

-- Restrict the bounded search to circuits whose last gate is the output, whose forward
-- references use a single false-valued index per gate, and whose nine raw inputs are read.

theorem PEqualNP.Outside.R_meta_3811_529
    (normalize : ∀ (a b : Fin 9),
      10 * a.val + b.val ∈ ([12, 13, 15, 16, 17, 18, 23, 26, 27, 28, 36, 67] : List ℕ) →
      let computes := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∀ x : Fin 9 → Bool,
        C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) =
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
            (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
            (fun e => x e.1 && x e.2)
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → computes C →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ C.size ∧ computes D ∧
          D.output + 1 = 11 + D.size ∧
          (∀ j : ℕ, ∀ i ∈ (D.gates.getD j ⟨.or, []⟩).inputs, i ≤ 11 + j) ∧
          (∀ v : Fin 9, ∃ g ∈ D.gates, v.val ∈ g.inputs))
    (bound : ∀ (a b : Fin 9),
      10 * a.val + b.val ∈ ([12, 13, 15, 16, 17, 18, 23, 26, 27, 28, 36, 67] : List ℕ) →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      D.output + 1 = 11 + D.size →
      (∀ j : ℕ, ∀ i ∈ (D.gates.getD j ⟨.or, []⟩).inputs, i ≤ 11 + j) →
      (∀ v : Fin 9, ∃ g ∈ D.gates, v.val ∈ g.inputs) →
      (∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) =
          ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
            (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] : List (Fin 9 × Fin 9)).any
            (fun e => x e.1 && x e.2)) → False) :
    ∀ (x1 x2 : Fin (9 : ℕ)), (10 : ℕ) * ↑x1 + ↑x2 ∈ [(12 : ℕ), (13 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (23 : ℕ), (26 : ℕ), (27 : ℕ), (28 : ℕ), (36 : ℕ), (67 : ℕ)] → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)), x7 x1 || x7 x2]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) → False := by
  intro a b hab C hfan hsize hcompute
  obtain ⟨D, hfanD, hsizeD, hcomputeD, hout, hreads, htotal⟩ :=
    normalize a b hab C hfan hcompute
  exact bound a b hab D hfanD (hsizeD.trans hsize) hout hreads htotal hcomputeD
