import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1106_aux

theorem key (x : List Bool) (i : ℕ) (h : i < x.length) :
    x.count true = (x.eraseIdx i).count true + (if x.getD i false = true then 1 else 0) := by
  have e1 : x = x.take i ++ x[i] :: x.drop (i+1) := by
    simp
  have e2 : x.eraseIdx i = x.take i ++ x.drop (i+1) := List.eraseIdx_eq_take_drop_succ x i
  have e3 : x.getD i false = x[i] := by simp [List.getD_eq_getElem?_getD, h]
  rw [e2, e3]
  conv_lhs => rw [e1]
  cases x[i] <;> simp [List.count_append] <;> omega

end PEqualNP.Outside.L_meta_1106_aux

theorem PEqualNP.Outside.L_meta_1106 : ∀ (x : List Bool) (i k : ℕ), i < x.length → x.count true = k → ((!(x.getD i false)) = decide (k ≤ (x.eraseIdx i).count true)) := by
  intro x i k h hk
  subst hk
  have := PEqualNP.Outside.L_meta_1106_aux.key x i h
  revert this
  cases x.getD i false
  · intro hc
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hc
    simp [hc]
  · intro hc
    simp only [ite_true] at hc
    simp only [Bool.not_true, Bool.false_eq, decide_eq_false_iff_not]
    omega
