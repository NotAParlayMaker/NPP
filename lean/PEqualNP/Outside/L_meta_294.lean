import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_294 :
    ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ),
    i < 2 * k → i' < 2 * k →
    m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i' →
    u = u' ∧ v = v' ∧ i = i' := by
  intro m k u v u' v' i i' hi hi' h
  have decode (radix a b c d : ℕ) (hc : c < radix) (hd : d < radix)
      (heq : radix * a + c = radix * b + d) : a = b ∧ c = d := by
    have hpos : 0 < radix := by omega
    constructor
    · have hquot := congrArg (fun n : ℕ => n / radix) heq
      simpa only [Nat.mul_add_div hpos, Nat.div_eq_of_lt hc, Nat.div_eq_of_lt hd,
        Nat.add_zero] using hquot
    · have hrem := congrArg (fun n : ℕ => n % radix) heq
      simpa only [Nat.mul_add_mod, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] using hrem
  simp only [Nat.add_assoc] at h
  have outer := decode (2 * k) (u.val * m + v.val) (u'.val * m + v'.val) i i'
    hi hi' (Nat.add_left_cancel h)
  have inner := decode m u.val u'.val v.val v'.val v.isLt v'.isLt (by
    rw [Nat.mul_comm m u.val, Nat.mul_comm m u'.val]
    exact outer.1)
  exact ⟨Fin.ext inner.1, Fin.ext inner.2, outer.2⟩
