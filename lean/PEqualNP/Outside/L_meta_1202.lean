import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1202 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)) x := by
  -- Wires 0 to 7 are the inputs. Wire 10 = x0 and (x1 or x2 or x3),
  -- wire 12 = x4 and (x1 or x5), wire 14 = x6 and (x5 or x7), output wire 16 is their OR.
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [4, 11]⟩,
      ⟨.or, [5, 7]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    obtain ⟨a, b, c, d, e, f, g, h, rfl⟩ : ∃ a b c d e f g h : Bool,
        x = ![a, b, c, d, e, f, g, h] :=
      ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, by ext i; fin_cases i <;> rfl⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;>
      cases h <;> rfl
