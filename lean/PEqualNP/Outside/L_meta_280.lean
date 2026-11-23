import Mathlib
import PEqualNP.Defs

private theorem blockIndex_unique (b a a' r r' : ℕ) (hr : r < b) (hr' : r' < b)
    (h : b * a + r = b * a' + r') : a = a' ∧ r = r' := by
  have ordered (x y s t : ℕ) (hxy : x < y) (hs : s < b) : b * x + s < b * y + t := by
    have hstep := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hxy)
    rw [Nat.mul_succ] at hstep
    omega
  have ha : a = a' := by
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · have := ordered a a' r r' hlt hr
      omega
    · exact heq
    · have := ordered a' a r' r hgt hr'
      omega
  subst a'
  exact ⟨rfl, Nat.add_left_cancel h⟩

theorem PEqualNP.Outside.L_meta_280 : ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ), i < 2 * k → i' < 2 * k → m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i' → u = u' ∧ v = v' ∧ i = i' := by
  intro m k u v u' v' i i' hi hi' h
  rw [Nat.add_assoc, Nat.add_assoc] at h
  obtain ⟨hslot, hoffset⟩ := blockIndex_unique _ _ _ _ _ hi hi' (Nat.add_left_cancel h)
  rw [Nat.mul_comm u.val m, Nat.mul_comm u'.val m] at hslot
  obtain ⟨hu, hv⟩ := blockIndex_unique _ _ _ _ _ v.isLt v'.isLt hslot
  exact ⟨Fin.ext hu, Fin.ext hv, hoffset⟩
