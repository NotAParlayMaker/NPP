import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1161

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [4, 11]⟩,
    ⟨GateOp.and, [5, 7]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩], 15⟩

lemma circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma circ_size : circ.size ≤ 8 := by
  decide

lemma ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

lemma eval_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    circ.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b4 && b5) || (b4 && b6) || (b5 && b7)) := by
  simp only [circ, Circuit.eval, Circuit.wires, GateOp.eval, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false, Bool.and_true, Bool.and_or_distrib_left, Bool.or_assoc]

lemma main_proof :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨circ, circ_mono, circ_size, fun x => ?_⟩
  rw [ofFn8]
  exact eval_eq (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

end PEqualNP.Outside.L_meta_1161

theorem PEqualNP.Outside.L_meta_1161 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x :=
  PEqualNP.Outside.L_meta_1161.main_proof
