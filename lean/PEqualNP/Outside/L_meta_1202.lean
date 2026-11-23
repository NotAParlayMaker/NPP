import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1202

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [8, 3]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [4, 11]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [6, 13]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [15, 14]⟩], 16⟩

lemma circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, by decide⟩
    first | exact Or.inl rfl | exact Or.inr rfl

lemma circ_eval (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    circ.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) ||
        (b4 && b5) || (b5 && b6) || (b6 && b7)) := by
  have h : circ.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && (b1 || b2 || b3)) || (b4 && (b1 || b5)) || (b6 && (b5 || b7))) := by
    simp [circ, Circuit.eval, Circuit.wires, GateOp.eval]
  rw [h]
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide

end PEqualNP.Outside.L_meta_1202

theorem PEqualNP.Outside.L_meta_1202 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1202.circ, PEqualNP.Outside.L_meta_1202.circ_mono, by decide, ?_⟩
  intro x
  exact PEqualNP.Outside.L_meta_1202.circ_eval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
