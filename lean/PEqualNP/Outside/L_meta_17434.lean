import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17434_aux

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  { gates :=
      [ ⟨GateOp.and, [2, 3]⟩,
        ⟨GateOp.and, [5, 6]⟩,
        ⟨GateOp.and, [7, 8]⟩,
        ⟨GateOp.and, [12, 9]⟩,
        ⟨GateOp.and, [11, 4]⟩,
        ⟨GateOp.and, [10, 1]⟩,
        ⟨GateOp.or,  [14, 15]⟩,
        ⟨GateOp.and, [13, 16]⟩,
        ⟨GateOp.and, [10, 11]⟩,
        ⟨GateOp.and, [18, 9]⟩,
        ⟨GateOp.and, [1, 4]⟩,
        ⟨GateOp.and, [3, 6]⟩,
        ⟨GateOp.and, [21, 8]⟩,
        ⟨GateOp.and, [2, 5]⟩,
        ⟨GateOp.and, [23, 7]⟩,
        ⟨GateOp.or,  [22, 24]⟩,
        ⟨GateOp.and, [20, 25]⟩,
        ⟨GateOp.or,  [19, 26]⟩,
        ⟨GateOp.and, [27, 0]⟩,
        ⟨GateOp.or,  [17, 28]⟩,
        ⟨GateOp.not, [29]⟩ ],
    output := 30 }

theorem circ_fanInTwo : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

theorem bool_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) :
    (!((((b7 && b8) && b9) && (((b5 && b6) && b4) || ((b2 && b3) && b1))) ||
      (((((b2 && b3) && (b5 && b6)) && b9) ||
        ((b1 && b4) && (((b3 && b6) && b8) || ((b2 && b5) && b7)))) && b0))) =
    !((b4 && b5 && b6 && b7 && b8 && b9) ||
      (b0 && b2 && b3 && b5 && b6 && b9) ||
      (b0 && b1 && b3 && b4 && b6 && b8) ||
      (b0 && b1 && b2 && b4 && b5 && b7) ||
      (b1 && b2 && b3 && b7 && b8 && b9)) := by
  congr 1
  simp only [Bool.and_or_distrib_left, Bool.and_or_distrib_right]
  have h1 : (((b7 && b8) && b9) && ((b5 && b6) && b4)) = (b4 && b5 && b6 && b7 && b8 && b9) := by ac_rfl
  have h2 : (((b7 && b8) && b9) && ((b2 && b3) && b1)) = (b1 && b2 && b3 && b7 && b8 && b9) := by ac_rfl
  have h3 : ((((b2 && b3) && (b5 && b6)) && b9) && b0) = (b0 && b2 && b3 && b5 && b6 && b9) := by ac_rfl
  have h4 : (((b1 && b4) && ((b3 && b6) && b8)) && b0) = (b0 && b1 && b3 && b4 && b6 && b8) := by ac_rfl
  have h5 : (((b1 && b4) && ((b2 && b5) && b7)) && b0) = (b0 && b1 && b2 && b4 && b5 && b7) := by ac_rfl
  rw [h1, h2, h3, h4, h5]
  ac_rfl

theorem circ_eval : ∀ x : Fin 10 → Bool,
    circ.eval (List.ofFn x) =
      !((x 4 && x 5 && x 6 && x 7 && x 8 && x 9) ||
        (x 0 && x 2 && x 3 && x 5 && x 6 && x 9) ||
        (x 0 && x 1 && x 3 && x 4 && x 6 && x 8) ||
        (x 0 && x 1 && x 2 && x 4 && x 5 && x 7) ||
        (x 1 && x 2 && x 3 && x 7 && x 8 && x 9)) := by
  intro x
  have h : circ.eval (List.ofFn x) =
      (!((((x 7 && x 8) && x 9) && (((x 5 && x 6) && x 4) || ((x 2 && x 3) && x 1))) ||
        (((((x 2 && x 3) && (x 5 && x 6)) && x 9) ||
          ((x 1 && x 4) && (((x 3 && x 6) && x 8) || ((x 2 && x 5) && x 7)))) && x 0))) := by
    simp [circ, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, List.getD]
  rw [h]
  exact bool_eq (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)

end PEqualNP.Outside.L_meta_17434_aux

theorem PEqualNP.Outside.L_meta_17434 : (PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => !((x 4 && x 5 && x 6 && x 7 && x 8 && x 9) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9) || (x 0 && x 1 && x 3 && x 4 && x 6 && x 8) || (x 0 && x 1 && x 2 && x 4 && x 5 && x 7) || (x 1 && x 2 && x 3 && x 7 && x 8 && x 9))) 24) := by
  exact ⟨PEqualNP.Outside.L_meta_17434_aux.circ,
    PEqualNP.Outside.L_meta_17434_aux.circ_fanInTwo,
    by decide,
    PEqualNP.Outside.L_meta_17434_aux.circ_eval⟩
