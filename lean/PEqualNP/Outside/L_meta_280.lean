import Mathlib.Data.Fin.Basic

namespace PEqualNP.Outside.L_meta_280_aux

private lemma eq_of_mul_add_eq {d q1 q2 r1 r2 : ℕ}
    (hr1 : r1 < d) (hr2 : r2 < d) (h : d * q1 + r1 = d * q2 + r2) :
    q1 = q2 ∧ r1 = r2 := by
  have hq : q1 = q2 := by
    rcases Nat.lt_trichotomy q1 q2 with hlt | heq | hgt
    · have : d * q1 + d ≤ d * q2 := by
        calc d * q1 + d = d * (q1 + 1) := by rw [Nat.mul_succ]
          _ ≤ d * q2 := Nat.mul_le_mul_left d hlt
      omega
    · exact heq
    · have : d * q2 + d ≤ d * q1 := by
        calc d * q2 + d = d * (q2 + 1) := by rw [Nat.mul_succ]
          _ ≤ d * q1 := Nat.mul_le_mul_left d hgt
      omega
  subst hq
  exact ⟨rfl, by omega⟩

end PEqualNP.Outside.L_meta_280_aux

theorem PEqualNP.Outside.L_meta_280 :
    ∀ (m k : ℕ) (u v u' v' : Fin m) (i i' : ℕ), i < 2 * k → i' < 2 * k →
      m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i' →
      u = u' ∧ v = v' ∧ i = i' := by
  intro m k u v u' v' i i' hi hi' h
  have h1 : 2 * k * (u.val * m + v.val) + i = 2 * k * (u'.val * m + v'.val) + i' := by omega
  rcases PEqualNP.Outside.L_meta_280_aux.eq_of_mul_add_eq hi hi' h1 with ⟨hslot, hi_eq⟩
  have hslot' : m * u.val + v.val = m * u'.val + v'.val := by
    rw [Nat.mul_comm m u.val, Nat.mul_comm m u'.val]
    exact hslot
  rcases PEqualNP.Outside.L_meta_280_aux.eq_of_mul_add_eq v.isLt v'.isLt hslot' with ⟨hu, hv⟩
  exact ⟨Fin.ext hu, Fin.ext hv, hi_eq⟩
