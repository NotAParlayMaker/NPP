import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_801_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circ : Circuit := { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩], output := 13 }

private def mkF (b0 b1 b2 b3 b4 b5 : Bool) : Fin 6 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5

private lemma check_eval (b0 b1 b2 b3 b4 b5 : Bool) :
    (circ.eval [b0, b1, b2, b3, b4, b5] = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (3, 4)] : List (ℕ × ℕ)) ∧
        mkF b0 b1 b2 b3 b4 b5 u = true ∧ mkF b0 b1 b2 b3 b4 b5 v = true) := by
  revert b0 b1 b2 b3 b4 b5
  decide

private lemma main_proof :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 8 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hfun : mkF (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) = x := by
      funext i
      fin_cases i <;> rfl
    have hlist : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := rfl
    have h := check_eval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    rw [hfun] at h
    rw [hlist]
    exact h

end PEqualNP.Outside.L_meta_801_aux

theorem PEqualNP.Outside.L_meta_801 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 8 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 4), (0, 5), (1, 2), (2, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) :=
  PEqualNP.Outside.L_meta_801_aux.main_proof
