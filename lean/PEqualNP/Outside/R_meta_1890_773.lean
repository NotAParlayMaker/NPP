import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1890_773
    (normalForm :
      let F := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      let ev := fun (C : Circuit) (x : Fin 10 → Bool) (b : Bool) => C.eval (List.ofFn x ++ [b])
      let q := fun (x : Fin 10 → Bool) => x 0 && x 2
      let rows : List ℕ := [5,69,261,773]
      ∀ (C : Circuit) (p : Fin 10 → Fin 10), FanInTwo C →
        (∀ x, ev C (x ∘ p) (q x) = F x) →
        ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ (∀ x, ev D x (q x) = F x) ∧
          ((∀ x, ev D x false = F x) ∨
          (∃ v ∈ rows, ev D (fun i => v.testBit i.val) false = true) ∨
          ∃ x, ev D x false = false ∧ ev D (fun i => if i = 0 then false else x i) false = true))
    (withoutExtra :
      let F := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, FanInTwo C → C.size ≤ 18 →
        ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [false]) ≠ F x)
    (rejectNegativeRows :
      let F := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      let ev := fun (C : Circuit) (x : Fin 10 → Bool) (b : Bool) => C.eval (List.ofFn x ++ [b])
      let rows : List ℕ := [5,69,261,773]
      ∀ D : Circuit, FanInTwo D → D.size ≤ 18 → (∀ x, ev D x (x 0 && x 2) = F x) →
        ∀ v ∈ rows, ev D (fun i => v.testBit i.val) false = false)
    (excludeDecreaseAtZero :
      let F := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
      let ev := fun (C : Circuit) (x : Fin 10 → Bool) (b : Bool) => C.eval (List.ofFn x ++ [b])
      let q := fun (x : Fin 10 → Bool) => x 0 && x 2
      ∀ D : Circuit, FanInTwo D → D.size ≤ 18 → (∀ x, ev D x (q x) = F x) →
        ¬ ∃ x, ev D x false = false ∧ ev D (fun i => if i = 0 then false else x i) false = true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C p valid bounded
  let F := fun x : Fin 10 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
        (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  change ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) ≠ F x
  by_contra h
  have computes (x : Fin 10 → Bool) : C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = F x :=
    Classical.byContradiction (fun different => h ⟨x, different⟩)
  obtain ⟨D, validD, sizeD, goodD, casesD⟩ := normalForm C p valid computes
  rcases casesD with noUse | ⟨v, hv, accepts⟩ | positive
  · obtain ⟨x, wrong⟩ := withoutExtra D validD (sizeD.trans bounded)
    exact wrong (noUse x)
  · have rejects := rejectNegativeRows D validD (sizeD.trans bounded) goodD v hv
    exact Bool.false_ne_true (rejects.symm.trans accepts)
  · exact excludeDecreaseAtZero D validD (sizeD.trans bounded) goodD positive
