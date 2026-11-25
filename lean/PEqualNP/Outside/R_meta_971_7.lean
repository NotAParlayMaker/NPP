import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_971_7
    (readbackNormal :
      let E : List (ℕ × ℕ) :=
        [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
         (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let bd := fun x : Fin 14 → Bool =>
        ((∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ∧
          ∀ i : Fin 14, x i = true →
            ¬ ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧
              (Function.update x i false) u = true ∧ (Function.update x i false) v = true) ∨
        (¬ (∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ∧
          ∀ i : Fin 14, x i = false →
            ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧
              (Function.update x i true) u = true ∧ (Function.update x i true) v = true)
      ∀ C : Circuit, Monotone2 C →
        ∃ C' : Circuit, Monotone2 C' ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C' ∧
          C'.size ≤ C.size ∧
          ∀ x : Fin 14 → Bool, bd x → C'.eval (List.ofFn x) = C.eval (List.ofFn x))
    (boundaryLift :
      let E : List (ℕ × ℕ) :=
        [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
         (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let bd := fun x : Fin 14 → Bool =>
        ((∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ∧
          ∀ i : Fin 14, x i = true →
            ¬ ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧
              (Function.update x i false) u = true ∧ (Function.update x i false) v = true) ∨
        (¬ (∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ∧
          ∀ i : Fin 14, x i = false →
            ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧
              (Function.update x i true) u = true ∧ (Function.update x i true) v = true)
      ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 14 → Bool, bd x →
          (C.eval (List.ofFn x) = true ↔
            ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true)) →
        ∀ x : Fin 14 → Bool,
          C.eval (List.ofFn x) = true ↔
            ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true)
    (satTail :
      let E : List (ℕ × ℕ) :=
        [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
         (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
         (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      ∀ C : Circuit, Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 14 C →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) →
        27 ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 27 ≤ C.size := by
  classical
  intro C hMono hEval
  let E : List (ℕ × ℕ) :=
    [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
     (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9),
     (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let bd := fun x : Fin 14 → Bool =>
    ((∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ∧
      ∀ i : Fin 14, x i = true →
        ¬ ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧
          (Function.update x i false) u = true ∧ (Function.update x i false) v = true) ∨
    (¬ (∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ∧
      ∀ i : Fin 14, x i = false →
        ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧
          (Function.update x i true) u = true ∧ (Function.update x i true) v = true)
  obtain ⟨C', hMono', hRB', hsize', hEq'⟩ := readbackNormal C hMono
  have hBd' : ∀ x : Fin 14 → Bool, bd x →
      (C'.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) := by
    intro x hx
    rw [hEq' x hx]
    exact hEval x
  have hFull' : ∀ x : Fin 14 → Bool,
      C'.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 14, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true :=
    boundaryLift C' hMono' hBd'
  exact le_trans (satTail C' hMono' hRB' hFull') hsize'
