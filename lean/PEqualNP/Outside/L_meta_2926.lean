import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2926

-- Clamp a wire index to at most 10: on ten inputs every index from 10 on reads false.
def cl (a : ℕ) : Fin 11 := ⟨min a 10, by omega⟩

theorem getD_cl (x : List Bool) (hx : x.length = 10) (a : ℕ) :
    x.getD (cl a : ℕ) false = x.getD a false := by
  simp only [cl]
  by_cases h : a < 10
  · rw [min_eq_left (by omega)]
  · rw [min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_2926

theorem PEqualNP.Outside.L_meta_2926 : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∃ (x3 : Fin (11 : ℕ)) (x4 : Fin (11 : ℕ)), x3 ≤ x4 ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x7 : ℕ) => x5.getD x7 Bool.false) x1) = (x5.getD (↑x3) Bool.false || x5.getD (↑x4) Bool.false) := by
  intro l hl
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨PEqualNP.Outside.L_meta_2926.cl 10, PEqualNP.Outside.L_meta_2926.cl 10, le_refl _, ?_⟩
    intro x hx
    rw [PEqualNP.Outside.L_meta_2926.getD_cl x hx, List.getD_eq_default _ _ (by omega)]
    rfl
  · refine ⟨PEqualNP.Outside.L_meta_2926.cl a, PEqualNP.Outside.L_meta_2926.cl a, le_refl _, ?_⟩
    intro x hx
    rw [PEqualNP.Outside.L_meta_2926.getD_cl x hx]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · by_cases hab : PEqualNP.Outside.L_meta_2926.cl a ≤ PEqualNP.Outside.L_meta_2926.cl b
    · refine ⟨PEqualNP.Outside.L_meta_2926.cl a, PEqualNP.Outside.L_meta_2926.cl b, hab, ?_⟩
      intro x hx
      rw [PEqualNP.Outside.L_meta_2926.getD_cl x hx, PEqualNP.Outside.L_meta_2926.getD_cl x hx]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    · refine ⟨PEqualNP.Outside.L_meta_2926.cl b, PEqualNP.Outside.L_meta_2926.cl a,
        le_of_lt (not_le.mp hab), ?_⟩
      intro x hx
      rw [PEqualNP.Outside.L_meta_2926.getD_cl x hx, PEqualNP.Outside.L_meta_2926.getD_cl x hx]
      simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.or_comm]
  · simp at hl
