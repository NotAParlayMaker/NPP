import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_294 :
    ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ), i < 2 * k → i' < 2 * k → m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i' → u = u' ∧ v = v' ∧ i = i' := by
  intro m k u v u' v' i i' hi hi' h
  have hk2 : 0 < 2 * k := by omega
  have hm : 0 < m := by have := u.isLt; omega
  have h0 : 2 * k * (u.val * m + v.val) + i = 2 * k * (u'.val * m + v'.val) + i' := by omega
  have hi_eq : i = i' := by
    have e1 := congrArg (· % (2 * k)) h0
    simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at e1
    exact e1
  subst hi_eq
  have hq : u.val * m + v.val = u'.val * m + v'.val := by
    have e1 := congrArg (· / (2 * k)) h0
    simp only [Nat.mul_add_div hk2, Nat.div_eq_of_lt hi, Nat.add_zero] at e1
    exact e1
  have hv_eq : v.val = v'.val := by
    have e1 := congrArg (· % m) hq
    simp only [Nat.mul_comm u.val m, Nat.mul_comm u'.val m, Nat.mul_add_mod, Nat.mod_eq_of_lt v.isLt,
      Nat.mod_eq_of_lt v'.isLt] at e1
    exact e1
  have hu_eq : u.val = u'.val := by
    have e1 := congrArg (· / m) hq
    simp only [Nat.mul_comm u.val m, Nat.mul_comm u'.val m, Nat.mul_add_div hm, Nat.div_eq_of_lt v.isLt,
      Nat.div_eq_of_lt v'.isLt, Nat.add_zero] at e1
    exact e1
  exact ⟨Fin.ext hu_eq, Fin.ext hv_eq, rfl⟩
