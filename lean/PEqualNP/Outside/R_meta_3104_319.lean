import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3104_319
    (h_forced :
      have f : (Fin 8 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4;
      ∀ (x2 x3 : Circuit) (x4 : ℕ), FanInTwo x2 → FanInTwo x3 → x2.size + x3.size ≤ 13 →
        have w : Bool → (Fin 8 → Bool) → List Bool := fun b x => x2.wires (List.ofFn x ++ [x 1 || b]);
        (∀ x, x3.eval (w false x ++ [(w false x).getD x4 false]) = f x) →
        (∀ x, x3.eval (w true x ++ [true]) = (f x || x 0 || x 3)) →
        (w false (fun i => decide (i = 1 ∨ i = 3))).getD x4 false = false ∧
        ∃ g ∈ x3.gates, 9 + x2.size ∈ g.inputs)
    (h_core :
      have f : (Fin 8 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
        x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4;
      ∀ (x2 x3 : Circuit) (x4 : ℕ), FanInTwo x2 → FanInTwo x3 → x2.size + x3.size ≤ 13 →
        have w : Bool → (Fin 8 → Bool) → List Bool := fun b x => x2.wires (List.ofFn x ++ [x 1 || b]);
        (w false (fun i => decide (i = 1 ∨ i = 3))).getD x4 false = false →
        (∃ g ∈ x3.gates, 9 + x2.size ∈ g.inputs) →
        (∀ x, x3.eval (w false x ++ [(w false x).getD x4 false]) = f x) →
        ∃ x, x3.eval (w true x ++ [true]) ≠ (f x || x 0 || x 3)) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         have x8 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x8 : Bool) (x9 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x9 ++ [x9 (1 : Fin (8 : ℕ)) || x8]);         (∀ (x9 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.false x9 ++ [(x8 Bool.false x9).getD x4 Bool.false]) = x1 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.true x10 ++ [Bool.true]) ≠ (x1 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  intro x1 x2 x3 x4 h2 h3 hsz x8 hev0
  by_contra hno
  have hno' : ∀ x : Fin 8 → Bool,
      x3.eval (x2.wires (List.ofFn x ++ [x 1 || true]) ++ [true]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
          x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4 || x 0 || x 3) :=
    fun x => Classical.byContradiction (fun hx => hno ⟨x, hx⟩)
  obtain ⟨hf, hread⟩ := h_forced x2 x3 x4 h2 h3 hsz hev0 hno'
  obtain ⟨x, hx⟩ := h_core x2 x3 x4 h2 h3 hsz hf hread hev0
  exact hx (hno' x)
