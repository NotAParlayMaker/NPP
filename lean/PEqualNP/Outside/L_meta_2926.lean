import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2926_aux

theorem clamp (x5 : List Bool) (h : x5.length = 10) (k : ℕ) :
    x5.getD k false = x5.getD (min k 10) false := by
  rcases le_or_gt k 10 with hk | hk
  · rw [min_eq_left hk]
  · rw [min_eq_right hk.le, List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

theorem ten (x5 : List Bool) (h : x5.length = 10) : x5.getD 10 false = false :=
  List.getD_eq_default _ _ (by omega)

end PEqualNP.Outside.L_meta_2926_aux

open PEqualNP.Outside.L_meta_2926_aux in
theorem PEqualNP.Outside.L_meta_2926 : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∃ (x3 : Fin (11 : ℕ)) (x4 : Fin (11 : ℕ)), x3 ≤ x4 ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : ℕ) => x5.getD x7 Bool.false) x1) = (x5.getD (↑x3) Bool.false || x5.getD (↑x4) Bool.false) := by
  intro x1 hx
  match x1, hx with
  | [], _ =>
    refine ⟨⟨10, by omega⟩, ⟨10, by omega⟩, le_refl _, fun x5 h5 => ?_⟩
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_nil, List.any_nil, ten x5 h5,
      Bool.or_false]
  | [a], _ =>
    refine ⟨⟨min a 10, by omega⟩, ⟨10, by omega⟩, by simp [Fin.le_def], fun x5 h5 => ?_⟩
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id, Bool.or_false, ten x5 h5]
    exact clamp x5 h5 a
  | [a, b], _ =>
    refine ⟨⟨min (min a 10) (min b 10), by omega⟩, ⟨max (min a 10) (min b 10), by omega⟩,
      by simp [Fin.le_def], fun x5 h5 => ?_⟩
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
      List.any_cons, List.any_nil, id, Bool.or_false]
    rw [clamp x5 h5 a, clamp x5 h5 b]
    rcases le_total (min a 10) (min b 10) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, Bool.or_comm]
  | _ :: _ :: _ :: _, h => simp at h
