import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_456_aux

private def phi (m k xval : ℕ) (z : Fin (m + 2 * k * (m * m))) : ℕ :=
  if z.val < m then
    if z.val = xval then 0 else 2 * k + 1
  else
    let d := z.val - m
    let q := d / (2 * k)
    let r := d % (2 * k) + 1
    let u := q / m
    let v := q % m
    if u = xval then r
    else if v = xval then 2 * k + 1 - r
    else 2 * k + 1

private lemma decode_block (m k : ℕ) (hk : 1 ≤ k) (u v : Fin m) (p : ℕ) (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2 * k) (z : Fin (m + 2 * k * (m * m)))
    (hz : z.val + 1 = m + 2 * k * (u.val * m + v.val) + p) :
    ¬ z.val < m ∧
    (z.val - m) / (2 * k) / m = u.val ∧
    (z.val - m) / (2 * k) % m = v.val ∧
    (z.val - m) % (2 * k) + 1 = p := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hd : z.val - m = 2 * k * (u.val * m + v.val) + (p - 1) := by omega
  have hdiv1 : (z.val - m) / (2 * k) = u.val * m + v.val := by
    rw [hd, Nat.mul_add_div (by omega : 0 < 2 * k), Nat.div_eq_of_lt (by omega : p - 1 < 2 * k), Nat.add_zero]
  have hmod1 : (z.val - m) % (2 * k) = p - 1 := by
    rw [hd, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : p - 1 < 2 * k)]
  have hdiv2 : (u.val * m + v.val) / m = u.val := by
    rw [mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt v.isLt, add_zero]
  have hmod2 : (u.val * m + v.val) % m = v.val := by
    rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt v.isLt]
  refine ⟨by omega, ?_, ?_, by omega⟩
  · rw [hdiv1, hdiv2]
  · rw [hdiv1, hmod2]

private lemma phi_of_Q (m k xval : ℕ) (hk : 1 ≤ k)
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))),
      Q u v p z ↔ (p = 0 ∧ z.val = u.val) ∨ (p = 2 * k + 1 ∧ z.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ z.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (u v : Fin m) (huv : u < v) (p : ℕ) (z : Fin (m + 2 * k * (m * m)))
    (hq : Q u v p z) :
    phi m k xval z =
      if u.val = xval then p
      else if v.val = xval then 2 * k + 1 - p
      else 2 * k + 1 := by
  have hne : u.val ≠ v.val := Nat.ne_of_lt huv
  rcases (hQ u v p z).1 hq with ⟨rfl, hz⟩ | ⟨rfl, hz⟩ | ⟨hp1, hp2, hz⟩
  · unfold phi
    simp only [hz, u.isLt, ↓reduceIte]
    by_cases hu : u.val = xval
    · simp [hu]
    · by_cases hv : v.val = xval <;> simp [hu, hv]
  · unfold phi
    simp only [hz, v.isLt, ↓reduceIte]
    by_cases hu : u.val = xval
    · have hv : v.val ≠ xval := by omega
      simp [hu, hv]
    · by_cases hv : v.val = xval <;> simp [hu, hv]
  · obtain ⟨hge, hdu, hdv, hdr⟩ := decode_block m k hk u v p hp1 hp2 z hz
    unfold phi
    simp only [hge, ↓reduceIte, hdu, hdv, hdr]

private lemma phi_adj_le (m k xval : ℕ) (hk : 1 ≤ k)
    (H : SimpleGraph (Fin m))
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (S : SimpleGraph (Fin (m + 2 * k * (m * m))))
    (hQ : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))),
      Q u v p z ↔ (p = 0 ∧ z.val = u.val) ∨ (p = 2 * k + 1 ∧ z.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ z.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (hS : ∀ a b : Fin (m + 2 * k * (m * m)), S.Adj a b ↔
      ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
        ((Q u v p a ∧ Q u v (p + 1) b) ∨ (Q u v p b ∧ Q u v (p + 1) a)))
    (a b : Fin (m + 2 * k * (m * m))) (hab : S.Adj a b) :
    phi m k xval b ≤ phi m k xval a + 1 := by
  obtain ⟨u, v, huv, _, p, hp, hcase⟩ := (hS a b).1 hab
  rcases hcase with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · rw [phi_of_Q m k xval hk Q hQ u v huv p a ha,
        phi_of_Q m k xval hk Q hQ u v huv (p + 1) b hb]
    split_ifs <;> omega
  · rw [phi_of_Q m k xval hk Q hQ u v huv (p + 1) a ha,
        phi_of_Q m k xval hk Q hQ u v huv p b hb]
    split_ifs <;> omega

private lemma phi_walk_le (m k xval : ℕ) (hk : 1 ≤ k)
    (H : SimpleGraph (Fin m))
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (S : SimpleGraph (Fin (m + 2 * k * (m * m))))
    (hQ : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))),
      Q u v p z ↔ (p = 0 ∧ z.val = u.val) ∨ (p = 2 * k + 1 ∧ z.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ z.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (hS : ∀ a b : Fin (m + 2 * k * (m * m)), S.Adj a b ↔
      ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
        ((Q u v p a ∧ Q u v (p + 1) b) ∨ (Q u v p b ∧ Q u v (p + 1) a)))
    {a b : Fin (m + 2 * k * (m * m))} (w : S.Walk a b) :
    phi m k xval b ≤ phi m k xval a + w.length := by
  induction w with
  | nil => simp
  | cons hadj w' ih =>
    have hstep := phi_adj_le m k xval hk H Q S hQ hS _ _ hadj
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem main_thm :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m))
      (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
      (S : SimpleGraph (Fin (m + 2 * k * (m * m)))),
      1 ≤ k →
      (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
        Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
          (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) →
      (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔
        ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
          ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) →
      ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y →
        ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hx hy hne p
  have hle := phi_walk_le m k x.val hk H Q S hQ hS p
  have hpx : phi m k x.val x = 0 := by
    unfold phi
    simp [hx]
  have hne_val : y.val ≠ x.val := fun h => hne (Fin.ext h.symm)
  have hpy : phi m k x.val y = 2 * k + 1 := by
    unfold phi
    simp [hy, hne_val]
  omega

end PEqualNP.Outside.L_meta_456_aux

theorem PEqualNP.Outside.L_meta_456 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length :=
  PEqualNP.Outside.L_meta_456_aux.main_thm
