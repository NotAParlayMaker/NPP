import Mathlib

/-!
The 4-cycle on `Fin 4` has 4 edges and 7 independent sets (the empty set, the four
singletons, `{0, 2}` and `{1, 3}`), so 28 (edge, independent set) pairs. They split into
exactly 4 vertex-labelled rectangles:

* label `0`: edges `{0,1}, {0,3}` times sets `∅, {1}, {3}, {1,3}`;
* label `1`: edges `{0,1}, {1,2}` times sets `{0}, {2}, {0,2}`;
* label `3`: edges `{2,3}, {0,3}` times sets `{0}, {2}, {0,2}`;
* label `2`: edges `{1,2}, {2,3}` times sets `∅, {1}, {3}, {1,3}`.

The witness is given explicitly and each of the three conditions is checked by `decide`.
-/

namespace PEqualNP.Outside.L_meta_136_aux

/-- `∃!` over `Fin 4` unfolds to `∃ i, P i ∧ ∀ j, P j → j = i`, which is decidable. -/
instance decExistsUnique (P : Fin 4 → Prop) [DecidablePred P] : Decidable (∃! i, P i) :=
  decidable_of_iff (∃ i, P i ∧ ∀ j, P j → j = i) Iff.rfl

/-- The edge side of each rectangle. -/
def A : Fin 4 → Finset (Sym2 (Fin 4)) :=
  ![{s(0, 1), s(0, 3)}, {s(0, 1), s(1, 2)}, {s(2, 3), s(0, 3)}, {s(1, 2), s(2, 3)}]

/-- The independent-set side of each rectangle. -/
def B : Fin 4 → Finset (Finset (Fin 4)) :=
  ![{∅, {1}, {3}, {1, 3}}, {{0}, {2}, {0, 2}}, {{0}, {2}, {0, 2}}, {∅, {1}, {3}, {1, 3}}]

/-- The vertex label of each rectangle. -/
def t : Fin 4 → Fin 4 := ![0, 1, 3, 2]

end PEqualNP.Outside.L_meta_136_aux

open PEqualNP.Outside.L_meta_136_aux in
theorem PEqualNP.Outside.L_meta_136 :
    ∃ (A : Fin 4 → Finset (Sym2 (Fin 4))) (B : Fin 4 → Finset (Finset (Fin 4))) (t : Fin 4 → Fin 4), (∀ i, ∀ e ∈ A i, e ∈ (SimpleGraph.cycleGraph 4).edgeFinset ∧ t i ∈ e) ∧ (∀ i, ∀ I ∈ B i, t i ∉ I) ∧ (∀ e ∈ (SimpleGraph.cycleGraph 4).edgeFinset, ∀ I : Finset (Fin 4), (∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.cycleGraph 4).Adj u w) → ∃! i : Fin 4, e ∈ A i ∧ I ∈ B i) := by
  refine ⟨A, B, t, ?_, ?_, ?_⟩
  all_goals decide
