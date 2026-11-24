import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_1886_1
    (hrelabel : ∀ (n : ℕ) (σ : Fin n → Fin n) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ (x : Fin n → Bool) (b : Bool),
        D.eval (List.ofFn x ++ [b]) = C.eval (List.ofFn (x ∘ σ) ++ [b]))
    (hmonotone :
      let target := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (C : Circuit) (b : Bool), Monotone2 C → C.size ≤ 18 →
        ∃ x : Fin 10 → Bool,
          ((target x = true ∧ ∀ y : Fin 10 → Bool, y ≤ x → target y = true → y = x) ∨
            (target x = false ∧ ∀ y : Fin 10 → Bool, x ≤ y → target y = false → y = x)) ∧
          C.eval (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1]) ≠ target x)
    (hand :
      let target := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, FanInTwo C → ¬ Monotone2 C → C.size ≤ 18 →
        ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 && x 1]) ≠ target x)
    (hor :
      let target := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, FanInTwo C → ¬ Monotone2 C → C.size ≤ 18 →
        ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 1]) ≠ target x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [if x3 = Bool.true then x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) else x6 (0 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C σ b hmodel hsize
  let target := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  obtain ⟨D, hDmodel, hDsize, hDeval⟩ := hrelabel 10 σ C hmodel
  have hbound : D.size ≤ 18 := by
    rw [hDsize]
    exact hsize
  have hwitness :
      ∃ x : Fin 10 → Bool,
        D.eval (List.ofFn x ++ [if b then x 0 && x 1 else x 0 || x 1]) ≠ target x := by
    by_cases hmono : Monotone2 D
    · obtain ⟨x, _, hx⟩ := hmonotone D b hmono hbound
      exact ⟨x, hx⟩
    · cases b
      · exact hor D hDmodel hmono hbound
      · exact hand D hDmodel hmono hbound
  obtain ⟨x, hx⟩ := hwitness
  refine ⟨x, ?_⟩
  change C.eval (List.ofFn (x ∘ σ) ++ [if b then x 0 && x 1 else x 0 || x 1]) ≠ target x
  rw [← hDeval]
  exact hx
