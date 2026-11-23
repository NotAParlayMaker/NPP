import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1106_aux

theorem count_eraseIdx :
    ∀ (x : List Bool) (i : ℕ) (hi : i < x.length),
      x.count true =
        (x.eraseIdx i).count true + (if x[i]'hi = true then 1 else 0) := by
  intro x i hi
  induction x generalizing i with
  | nil => cases hi
  | cons a as ih =>
    cases i with
    | zero =>
      simp [List.count_cons]
    | succ j =>
      have hj : j < as.length := Nat.succ_lt_succ_iff.mp hi
      simp only [List.length_cons, List.getElem_cons_succ, List.count_cons,
        List.eraseIdx_cons_succ]
      have := ih j hj
      rw [this]
      split_ifs <;> omega

theorem getD_eq_getElem (x : List Bool) (i : ℕ) (hi : i < x.length) :
    x.getD i false = x[i]'hi := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem main (x : List Bool) (i k : ℕ) (hi : i < x.length) (hk : x.count true = k) :
    (!(x.getD i false)) = decide (k ≤ (x.eraseIdx i).count true) := by
  have hsplit := count_eraseIdx x i hi
  rw [getD_eq_getElem x i hi]
  rw [hk] at hsplit
  by_cases hx : x[i]'hi = true
  · rw [if_pos hx] at hsplit
    have hlt : (x.eraseIdx i).count true < k := by omega
    simp [hx, Nat.not_le_of_gt hlt]
  · rw [if_neg hx] at hsplit
    have : x[i]'hi = false := Bool.eq_false_iff.mpr hx
    simp [this, hsplit]

end PEqualNP.Outside.L_meta_1106_aux

theorem PEqualNP.Outside.L_meta_1106 :
    ∀ (x : List Bool) (i k : ℕ), i < x.length → x.count true = k →
      ((!(x.getD i false)) = decide (k ≤ (x.eraseIdx i).count true)) := by
  intro x i k hi hk
  exact PEqualNP.Outside.L_meta_1106_aux.main x i k hi hk
