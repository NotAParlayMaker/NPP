import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L277

open PEqualNP.CircuitLowerBounds

/-- Peel the first edge off the edge list of the target. -/
lemma edgeCons (x : Fin 5 → Bool) (a b : ℕ) (ha : a < 5) (hb : b < 5) (es : List (ℕ × ℕ)) :
    (∃ u v : Fin 5, (u.val, v.val) ∈ (a, b) :: es ∧ x u = true ∧ x v = true) ↔
    (x ⟨a, ha⟩ = true ∧ x ⟨b, hb⟩ = true) ∨
      ∃ u v : Fin 5, (u.val, v.val) ∈ es ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    rcases List.mem_cons.mp h with h | h
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      exact Or.inl ⟨(show u = ⟨a, ha⟩ from Fin.ext h1) ▸ hu, (show v = ⟨b, hb⟩ from Fin.ext h2) ▸ hv⟩
    · exact Or.inr ⟨u, v, h, hu, hv⟩
  · rintro (⟨h1, h2⟩ | ⟨u, v, h, hu, hv⟩)
    · exact ⟨⟨a, ha⟩, ⟨b, hb⟩, List.mem_cons_self, h1, h2⟩
    · exact ⟨u, v, List.mem_cons_of_mem _ h, hu, hv⟩

/-- The empty edge list gives nothing. -/
lemma edgeNil (x : Fin 5 → Bool) :
    (∃ u v : Fin 5, (u.val, v.val) ∈ ([] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) ↔ False := by
  simp

/-- The circuit on all 32 inputs, checked by the kernel. -/
lemma core : ∀ a b c d e : Bool,
    (({ gates := [⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [2, 4]⟩,
        ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.and, [5, 9]⟩], output := 10 } :
        Circuit).eval [a, b, c, d, e] = true ↔
      (a = true ∧ b = true) ∨ (a = true ∧ c = true) ∨ (a = true ∧ e = true) ∨
        (b = true ∧ c = true) ∨ (c = true ∧ d = true) ∨ False) := by
  intro a b c d e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

end PEqualNP.Outside.L277

theorem PEqualNP.Outside.L_meta_277 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 6 ∧ (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 2), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · intro gate hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := rfl
    rw [hx, PEqualNP.Outside.L277.edgeCons x 0 1 (by decide) (by decide),
      PEqualNP.Outside.L277.edgeCons x 0 2 (by decide) (by decide),
      PEqualNP.Outside.L277.edgeCons x 0 4 (by decide) (by decide),
      PEqualNP.Outside.L277.edgeCons x 1 2 (by decide) (by decide),
      PEqualNP.Outside.L277.edgeCons x 2 3 (by decide) (by decide),
      PEqualNP.Outside.L277.edgeNil x]
    exact PEqualNP.Outside.L277.core (x 0) (x 1) (x 2) (x 3) (x 4)
