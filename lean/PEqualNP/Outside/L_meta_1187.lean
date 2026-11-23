import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1187

open PEqualNP.CircuitLowerBounds

def c : Circuit := ⟨[
  ⟨GateOp.or, [1, 2]⟩,
  ⟨GateOp.or, [8, 3]⟩,
  ⟨GateOp.and, [0, 9]⟩,
  ⟨GateOp.and, [1, 2]⟩,
  ⟨GateOp.or, [3, 5]⟩,
  ⟨GateOp.and, [4, 12]⟩,
  ⟨GateOp.and, [6, 7]⟩,
  ⟨GateOp.or, [10, 11]⟩,
  ⟨GateOp.or, [15, 13]⟩,
  ⟨GateOp.or, [16, 14]⟩
], 17⟩

set_option maxHeartbeats 0 in
lemma eval_ff :
    ∀ b c0 d e f g h : Bool,
      c.eval [false, b, c0, d, e, f, g, h] =
        ((false && b) || (false && c0) || (false && d) || (b && c0) || (d && e) || (e && f) || (g && h)) := by
  decide

set_option maxHeartbeats 0 in
lemma eval_tt :
    ∀ b c0 d e f g h : Bool,
      c.eval [true, b, c0, d, e, f, g, h] =
        ((true && b) || (true && c0) || (true && d) || (b && c0) || (d && e) || (e && f) || (g && h)) := by
  decide

end PEqualNP.Outside.L_meta_1187

theorem PEqualNP.Outside.L_meta_1187 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
        ∀ x : Fin 8 → Bool,
          C.eval (List.ofFn x) =
            (fun x : Fin 8 → Bool =>
              (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
                (x 3 && x 4) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1187.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1187.c]
  · decide
  · intro x
    have hlist : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [hlist]
    show PEqualNP.Outside.L_meta_1187.c.eval [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) ||
        (x 3 && x 4) || (x 4 && x 5) || (x 6 && x 7))
    cases x 0
    · exact PEqualNP.Outside.L_meta_1187.eval_ff (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    · exact PEqualNP.Outside.L_meta_1187.eval_tt (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
