import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_788_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circ : Circuit := { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 17]⟩], output := 18 }

private def mkF (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Fin 8 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5
  | ⟨6, _⟩ => b6
  | ⟨7, _⟩ => b7

private lemma check_eval (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    (circ.eval [b0, b1, b2, b3, b4, b5, b6, b7] = true ↔
      ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 7), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)] : List (ℕ × ℕ)) ∧
        mkF b0 b1 b2 b3 b4 b5 b6 b7 u = true ∧ mkF b0 b1 b2 b3 b4 b5 b6 b7 v = true) := by
  revert b0 b1 b2 b3 b4 b5 b6 b7
  decide

private lemma main_proof :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 17]⟩], output := 18 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 11 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 7), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · intro x
    have hfun : mkF (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) = x := by
      funext i
      fin_cases i <;> rfl
    have hlist : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    have h := check_eval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
    rw [hfun] at h
    rw [hlist]
    exact h

end PEqualNP.Outside.L_meta_788_aux

theorem PEqualNP.Outside.L_meta_788 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 17]⟩], output := 18 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 11 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 7), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) :=
  PEqualNP.Outside.L_meta_788_aux.main_proof
