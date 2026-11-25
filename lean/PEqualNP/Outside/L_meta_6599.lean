import Mathlib
import PEqualNP.Defs

/-!
Pointwise case analysis. For each element the two hypotheses force either
(x4 in x8, x4 not in x9, and the first pattern) or (x4 in x9, x4 not in x8, and the second
pattern). Membership of x4 is global, so splitting on x4 in x8 picks one side for all
elements, and each element is then settled by tauto.
-/

namespace PEqualNP.Outside.L_meta_6599

end PEqualNP.Outside.L_meta_6599

theorem PEqualNP.Outside.L_meta_6599 : ∀ (x1 x2 : Type) (x3 : Set x1) (x4 : x2) (x5 : x1 → x2) (x6 x7 : Set x1) (x8 x9 : Set x2), (∀ x10 ∈ x3, (x10 ∈ x6 ∧ x4 ∈ x8 ∨ x10 ∈ x7 ∧ x4 ∈ x9) ∧ (x10 ∈ x6 ∧ x5 x10 ∈ x8 ∨ x10 ∈ x7 ∧ x5 x10 ∈ x9)) → (∀ x11 ∈ x3, ¬(x11 ∈ x6 ∧ x4 ∈ x8 ∧ x5 x11 ∈ x8) ∧ ¬(x11 ∈ x7 ∧ x4 ∈ x9 ∧ x5 x11 ∈ x9)) → (∀ x12 ∈ x3, x12 ∈ x6 ∧ x12 ∈ x7 ∧ x4 ∈ x8 ∧ x4 ∉ x9 ∧ x5 x12 ∉ x8 ∧ x5 x12 ∈ x9) ∨ ∀ x12 ∈ x3, x12 ∈ x6 ∧ x12 ∈ x7 ∧ x4 ∈ x9 ∧ x4 ∉ x8 ∧ x5 x12 ∉ x9 ∧ x5 x12 ∈ x8 := by
  intro α β S y f s6 s7 s8 s9 h1 h2
  by_cases hy : y ∈ s8
  · left
    intro a ha
    have e1 := h1 a ha
    have e2 := h2 a ha
    tauto
  · right
    intro a ha
    have e1 := h1 a ha
    have e2 := h2 a ha
    tauto
