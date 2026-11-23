import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_280 :
    ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ), i < 2 * k → i' < 2 * k →
      m + 2 * k * (u.val * m + v.val) + i =
        m + 2 * k * (u'.val * m + v'.val) + i' →
      u = u' ∧ v = v' ∧ i = i' := by
  intro m k u v u' v' i i' hi hi' h
  have thread :
      2 * k * (u.val * m + v.val) + i = 2 * k * (u'.val * m + v'.val) + i' :=
    Nat.add_left_cancel (by simpa only [Nat.add_assoc] using h)
  have offset : i = i' := by
    have residues := congrArg (fun x : ℕ => x % (2 * k)) thread
    simpa only [Nat.mul_add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] using residues
  rw [offset] at thread
  have slot : u.val * m + v.val = u'.val * m + v'.val :=
    Nat.mul_left_cancel (Nat.zero_lt_of_lt hi) (Nat.add_right_cancel thread)
  have column : v.val = v'.val := by
    have residues := congrArg (fun x : ℕ => x % m) slot
    simpa only [Nat.mul_add_mod', Nat.mod_eq_of_lt v.isLt, Nat.mod_eq_of_lt v'.isLt] using
      residues
  rw [column] at slot
  have row : u.val = u'.val := by
    have products := Nat.add_right_cancel slot
    exact Nat.mul_left_cancel (Nat.zero_lt_of_lt v.isLt) (by simpa only [Nat.mul_comm] using products)
  exact ⟨Fin.ext row, Fin.ext column, offset⟩
