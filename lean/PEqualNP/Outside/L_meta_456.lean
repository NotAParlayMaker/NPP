import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_456_aux

lemma decode (m K u v p z : ℕ) (hK : 0 < K) (hv : v < m) (hp1 : 1 ≤ p) (hp2 : p ≤ K)
    (hz : z + 1 = m + K * (u * m + v) + p) :
    m ≤ z ∧ (z - m) / K = u * m + v ∧ (z - m) % K = p - 1 ∧
      (u * m + v) / m = u ∧ (u * m + v) % m = v := by
  have hm : 0 < m := by omega
  have hmz : m ≤ z := by
    generalize K * (u * m + v) = T at hz
    omega
  have h1 : (z - m) / K = u * m + v ∧ (z - m) % K = p - 1 := by
    rw [Nat.div_mod_unique hK]
    constructor
    · generalize K * (u * m + v) = T at hz ⊢
      omega
    · omega
  have h2 : (u * m + v) / m = u ∧ (u * m + v) % m = v := by
    rw [Nat.div_mod_unique hm]
    exact ⟨by ring, hv⟩
  exact ⟨hmz, h1.1, h1.2, h2.1, h2.2⟩

def gpot (m k xv z : ℕ) : ℕ :=
  if z = xv then 0
  else if z < m then 2 * k + 1
  else if (z - m) / (2 * k) / m = xv then (z - m) % (2 * k) + 1
  else if (z - m) / (2 * k) % m = xv then 2 * k + 1 - ((z - m) % (2 * k) + 1)
  else 2 * k + 1

lemma g_path {m k xv u v p z : ℕ} (hk : 1 ≤ k) (hxv : xv < m) (hu : u < m) (hv : v < m)
    (huv : u < v)
    (hQ : (p = 0 ∧ z = u) ∨ (p = 2 * k + 1 ∧ z = v) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ z + 1 = m + 2 * k * (u * m + v) + p)) :
    gpot m k xv z = if u = xv then p else if v = xv then 2 * k + 1 - p else 2 * k + 1 := by
  rcases hQ with ⟨hp, hz⟩ | ⟨hp, hz⟩ | ⟨hp1, hp2, hz⟩
  · subst hp hz
    unfold gpot
    split_ifs <;> omega
  · subst hp hz
    unfold gpot
    split_ifs <;> omega
  · obtain ⟨hmz, hb, hr, hbu, hbv⟩ := decode m (2 * k) u v p z (by omega) hv hp1 hp2 hz
    unfold gpot
    rw [hb, hr, hbu, hbv]
    split_ifs <;> omega

end PEqualNP.Outside.L_meta_456_aux

open PEqualNP.Outside.L_meta_456_aux in
theorem PEqualNP.Outside.L_meta_456 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hxm hym hxy w
  have lip : ∀ a b : Fin (m + 2 * k * (m * m)), S.Adj a b →
      gpot m k x.val b.val ≤ gpot m k x.val a.val + 1 := by
    intro a b hab
    obtain ⟨u, v, huv, -, p, hp, h⟩ := (hS a b).1 hab
    have huv' : u.val < v.val := huv
    rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rw [hQ] at ha hb
      rw [g_path hk hxm u.isLt v.isLt huv' ha, g_path hk hxm u.isLt v.isLt huv' hb]
      split_ifs <;> omega
    · rw [hQ] at ha hb
      rw [g_path hk hxm u.isLt v.isLt huv' ha, g_path hk hxm u.isLt v.isLt huv' hb]
      split_ifs <;> omega
  have hwalk : ∀ (a b : Fin (m + 2 * k * (m * m))) (q : S.Walk a b),
      gpot m k x.val b.val ≤ gpot m k x.val a.val + q.length := by
    intro a b q
    induction q with
    | nil => simp
    | cons hadj q ih =>
      rw [SimpleGraph.Walk.length_cons]
      have := lip _ _ hadj
      omega
  have hgx : gpot m k x.val x.val = 0 := by
    unfold gpot
    simp
  have hgy : gpot m k x.val y.val = 2 * k + 1 := by
    have hne : y.val ≠ x.val := fun h => hxy (Fin.ext h).symm
    unfold gpot
    split_ifs <;> omega
  have := hwalk x y w
  omega
