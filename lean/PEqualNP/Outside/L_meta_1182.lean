import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1182 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) x := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 4]⟩,
    ⟨.and, [0, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [5, 12]⟩,
    ⟨.and, [6, 7]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · intro x
    obtain ⟨a, b, c, d, e, f, g, h, rfl⟩ :
        ∃ a b c d e f g h : Bool, x = ![a, b, c, d, e, f, g, h] :=
      ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by ext i; fin_cases i <;> rfl⟩
    cases a <;> cases b <;> cases c <;> cases d <;>
      cases e <;> cases f <;> cases g <;> cases h <;> rfl
