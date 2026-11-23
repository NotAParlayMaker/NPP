import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_294 : ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ), i < 2 * k → i' < 2 * k → m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i' → u = u' ∧ v = v' ∧ i = i' := by
  intro m k u v u' v' i i' hi hi' h
  have hk : 0 < 2 * k := by omega
  have h2 : 2 * k * (u.val * m + v.val) + i = 2 * k * (u'.val * m + v'.val) + i' := by omega
  have hA : u.val * m + v.val = u'.val * m + v'.val := by
    have h3 : (2 * k * (u.val * m + v.val) + i) / (2 * k) =
        (2 * k * (u'.val * m + v'.val) + i') / (2 * k) := by rw [h2]
    rw [Nat.mul_add_div hk, Nat.mul_add_div hk, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hi'] at h3
    simpa using h3
  have hii : i = i' := by
    rw [hA] at h2
    omega
  have hm : 0 < m := Fin.pos u
  have hu : u.val = u'.val := by
    have h3 : (u.val * m + v.val) / m = (u'.val * m + v'.val) / m := by rw [hA]
    rw [Nat.mul_comm u.val m, Nat.mul_comm u'.val m, Nat.mul_add_div hm, Nat.mul_add_div hm,
      Nat.div_eq_of_lt v.isLt, Nat.div_eq_of_lt v'.isLt] at h3
    simpa using h3
  have hv : v.val = v'.val := by
    rw [hu] at hA
    omega
  exact ⟨Fin.ext hu, Fin.ext hv, hii⟩
