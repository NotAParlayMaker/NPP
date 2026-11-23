import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1106

lemma eraseIdx_count_true : ∀ (x : List Bool) (i : ℕ) (_hi : i < x.length),
    x.count true = (x.eraseIdx i).count true + (if x[i] = true then 1 else 0)
  | [], _, hi => nomatch hi
  | false :: x, 0, _ => by simp [List.count_cons, List.eraseIdx]
  | true :: x, 0, _ => by simp [List.count_cons, List.eraseIdx]
  | false :: x, i + 1, hi => by
    have hi' : i < x.length := Nat.succ_lt_succ_iff.mp hi
    simpa [List.count_cons, List.eraseIdx_cons_succ, List.getElem_cons_succ] using
      eraseIdx_count_true x i hi'
  | true :: x, i + 1, hi => by
    have hi' : i < x.length := Nat.succ_lt_succ_iff.mp hi
    have ih := eraseIdx_count_true x i hi'
    simp only [List.count_cons, List.eraseIdx_cons_succ, List.getElem_cons_succ,
      Bool.true_eq_false, ↓reduceIte]
    -- count (true::x) = count x + 1; eraseIdx keeps the leading true
    omega

end PEqualNP.Outside.L_meta_1106

open PEqualNP.Outside.L_meta_1106

theorem PEqualNP.Outside.L_meta_1106 :
    ∀ (x : List Bool) (i k : ℕ), i < x.length → x.count true = k →
      (!(x.getD i false)) = decide (k ≤ (x.eraseIdx i).count true) := by
  intro x i k hi hk
  have hget : x.getD i false = x[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hc := eraseIdx_count_true x i hi
  rw [hget]
  cases hbit : x[i]
  · have : (x.eraseIdx i).count true = k := by
      have := hc
      simp only [hbit, ↓reduceIte, add_zero] at this
      exact this.symm.trans hk
    simp [this]
  · have hcnt : (x.eraseIdx i).count true + 1 = k := by
      have := hc
      simp only [hbit, ↓reduceIte] at this
      exact this.symm.trans hk
    have : ¬ k ≤ (x.eraseIdx i).count true := by omega
    simp [this]
