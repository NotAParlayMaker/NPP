import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1167 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) x := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [11, 6]⟩,
      ⟨.and, [0, 12]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    obtain ⟨a, b, c, d, e, f, g, h, rfl⟩ : ∃ a b c d e f g h : Bool, x = ![a, b, c, d, e, f, g, h] :=
      ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by ext i; fin_cases i <;> rfl⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;> rfl
