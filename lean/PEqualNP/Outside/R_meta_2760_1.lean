import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The Petersen-9 edge function on an assignment `x8`. -/
def L_meta_2760_edge (x8 : Fin 9 → Bool) : Bool :=
  x8 (0 : Fin 9) && x8 (1 : Fin 9) || x8 (1 : Fin 9) && x8 (2 : Fin 9) ||
    x8 (2 : Fin 9) && x8 (3 : Fin 9) || x8 (3 : Fin 9) && x8 (4 : Fin 9) ||
      x8 (4 : Fin 9) && x8 (0 : Fin 9) || x8 (0 : Fin 9) && x8 (5 : Fin 9) ||
        x8 (1 : Fin 9) && x8 (6 : Fin 9) || x8 (2 : Fin 9) && x8 (7 : Fin 9) ||
          x8 (3 : Fin 9) && x8 (8 : Fin 9) || x8 (5 : Fin 9) && x8 (7 : Fin 9) ||
            x8 (6 : Fin 9) && x8 (8 : Fin 9) || x8 (8 : Fin 9) && x8 (5 : Fin 9)

/-- The counterexample predicate of L-meta-2760: some input on which the circuit,
run on the seed `x0..x8, ¬x0, OR(l)`, disagrees with the Petersen-9 edge function. -/
def L_meta_2760_bad (l : List ℕ) (C : Circuit) : Prop :=
  ∃ (x8 : Fin 9 → Bool),
    let x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin 9)]
    C.eval (x9 ++ [GateOp.or.eval (List.map (fun x10 : ℕ => x9.getD x10 Bool.false) l)]) ≠
      L_meta_2760_edge x8

/-- Reduction of L-meta-2760: the three membership cases of the hypothesis.
If every two-element list drawn from `{1,…,8}` containing `4`, `6`, or `7`
separately defeats every fan-in-two circuit of at most `13` gates, then the
disjoint union of the three cases gives the step. -/
theorem PEqualNP.Outside.R_meta_2760_1
    (h4 : ∀ (l : List ℕ), l.length = (2 : ℕ) →
      (∀ x3 ∈ l, (1 : ℕ) ≤ x3 ∧ x3 < (9 : ℕ)) → (4 : ℕ) ∈ l →
      ∀ (C : Circuit), FanInTwo C → C.size ≤ (13 : ℕ) → L_meta_2760_bad l C)
    (h6 : ∀ (l : List ℕ), l.length = (2 : ℕ) →
      (∀ x3 ∈ l, (1 : ℕ) ≤ x3 ∧ x3 < (9 : ℕ)) → (6 : ℕ) ∈ l →
      ∀ (C : Circuit), FanInTwo C → C.size ≤ (13 : ℕ) → L_meta_2760_bad l C)
    (h7 : ∀ (l : List ℕ), l.length = (2 : ℕ) →
      (∀ x3 ∈ l, (1 : ℕ) ≤ x3 ∧ x3 < (9 : ℕ)) → (7 : ℕ) ∈ l →
      ∀ (C : Circuit), FanInTwo C → C.size ≤ (13 : ℕ) → L_meta_2760_bad l C) :
    ∀ (x1 : List ℕ), x1.length = (2 : ℕ) →
      (∀ x3 ∈ x1, (1 : ℕ) ≤ x3 ∧ x3 < (9 : ℕ)) →
      ((4 : ℕ) ∈ x1 ∨ (6 : ℕ) ∈ x1 ∨ (7 : ℕ) ∈ x1) →
      ∀ (x5 : Circuit), FanInTwo x5 → x5.size ≤ (13 : ℕ) → L_meta_2760_bad x1 x5 := by
  intro l hl hb hmem C hfan hsize
  rcases hmem with h | h | h
  · exact h4 l hl hb h C hfan hsize
  · exact h6 l hl hb h C hfan hsize
  · exact h7 l hl hb h C hfan hsize
