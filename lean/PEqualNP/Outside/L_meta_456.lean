import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

namespace PEqualNP.Outside

private lemma subdiv_div_mod_unique {m k u v p : ℕ} (hk : 1 ≤ k) (hv : v < m)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) :
    ((m + 2 * k * (u * m + v) + p - 1 - m) / (2 * k) / m = u) ∧
    ((m + 2 * k * (u * m + v) + p - 1 - m) / (2 * k) % m = v) ∧
    ((m + 2 * k * (u * m + v) + p - 1 - m) % (2 * k) = p - 1) := by
  have h1 : m + 2 * k * (u * m + v) + p - 1 - m = 2 * k * (u * m + v) + (p - 1) := by omega
  rw [h1]
  have h2k : 0 < 2 * k := by omega
  have hpm : p - 1 < 2 * k := by omega
  have hdiv : (2 * k * (u * m + v) + (p - 1)) / (2 * k) = u * m + v := by
    rw [Nat.mul_add_div h2k, Nat.div_eq_of_lt hpm, Nat.add_zero]
  have hmod : (2 * k * (u * m + v) + (p - 1)) % (2 * k) = p - 1 := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hpm]
  have hm : 0 < m := by omega
  rw [hdiv, hmod]
  refine ⟨?_, ?_, rfl⟩
  · rw [Nat.mul_comm u m, Nat.mul_add_div hm, Nat.div_eq_of_lt hv, Nat.add_zero]
  · rw [Nat.mul_comm u m, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]

private def subdivPhi (m k : ℕ) (x z : Fin (m + 2 * k * (m * m))) : ℕ :=
  if z.val < m then
    if z.val = x.val then 0 else 2 * k + 1
  else
    let q := (z.val - m) / (2 * k)
    let r := (z.val - m) % (2 * k)
    if q / m = x.val then r + 1
    else if q % m = x.val then 2 * k - r
    else 2 * k + 1

private lemma subdivPhi_on_Q {m k : ℕ} (hk : 1 ≤ k)
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))),
      Q u v p z ↔ (p = 0 ∧ z.val = u.val) ∨ (p = 2 * k + 1 ∧ z.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ z.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (x : Fin (m + 2 * k * (m * m))) (u v : Fin m) (huv : u < v)
    (p : ℕ) (z : Fin (m + 2 * k * (m * m))) (hz : Q u v p z) :
    subdivPhi m k x z =
      if u.val = x.val then p
      else if v.val = x.val then 2 * k + 1 - p
      else 2 * k + 1 := by
  have huv_ne : u.val ≠ v.val := by
    have : u.val < v.val := huv
    omega
  rcases (hQ u v p z).mp hz with ⟨rfl, hzu⟩ | ⟨rfl, hzv⟩ | ⟨hp1, hp2, hzeq⟩
  · unfold subdivPhi
    have hzm : z.val < m := by omega
    rw [if_pos hzm, hzu]
    by_cases hux : u.val = x.val
    · rw [if_pos hux, if_pos hux]
    · rw [if_neg hux, if_neg hux]
      by_cases hvx : v.val = x.val
      · rw [if_pos hvx]
        omega
      · rw [if_neg hvx]
  · unfold subdivPhi
    have hzm : z.val < m := by omega
    rw [if_pos hzm, hzv]
    by_cases hux : u.val = x.val
    · have hvx : v.val ≠ x.val := by omega
      rw [if_neg hvx, if_pos hux]
    · rw [if_neg hux]
      by_cases hvx : v.val = x.val
      · rw [if_pos hvx, if_pos hvx]
        omega
      · rw [if_neg hvx, if_neg hvx]
  · unfold subdivPhi
    have hzge : ¬ z.val < m := by omega
    rw [if_neg hzge]
    have hval : z.val = m + 2 * k * (u.val * m + v.val) + p - 1 := by omega
    have hdm := subdiv_div_mod_unique (u := u.val) hk v.isLt hp1 hp2
    rw [← hval] at hdm
    simp only [hdm.1, hdm.2.1, hdm.2.2]
    by_cases hux : u.val = x.val
    · rw [if_pos hux, if_pos hux]
      omega
    · rw [if_neg hux, if_neg hux]
      by_cases hvx : v.val = x.val
      · rw [if_pos hvx, if_pos hvx]
        omega
      · rw [if_neg hvx, if_neg hvx]

theorem L_meta_456 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m))
      (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
      (S : SimpleGraph (Fin (m + 2 * k * (m * m)))),
      1 ≤ k →
      (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
        Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
          (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) →
      (∀ x y : Fin (m + 2 * k * (m * m)),
        S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧
          ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) →
      ∀ x y : Fin (m + 2 * k * (m * m)),
        x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hx hy hxy walk
  have hstep : ∀ a b : Fin (m + 2 * k * (m * m)),
      S.Adj a b → subdivPhi m k x b ≤ subdivPhi m k x a + 1 := by
    intro a b hab
    rcases (hS a b).mp hab with ⟨u, v, huv, _, p, hp, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
    · rw [subdivPhi_on_Q hk Q hQ x u v huv p a ha,
        subdivPhi_on_Q hk Q hQ x u v huv (p + 1) b hb]
      split_ifs <;> omega
    · rw [subdivPhi_on_Q hk Q hQ x u v huv p b hb,
        subdivPhi_on_Q hk Q hQ x u v huv (p + 1) a ha]
      split_ifs <;> omega
  have hwalk : ∀ {a b : Fin (m + 2 * k * (m * m))} (w : S.Walk a b),
      subdivPhi m k x b ≤ subdivPhi m k x a + w.length := by
    intro a b w
    induction w with
    | nil => simp
    | @cons a c b hac w' ih =>
      have h1 := hstep a c hac
      simp only [SimpleGraph.Walk.length_cons]
      omega
  have hbound := hwalk walk
  have hphix : subdivPhi m k x x = 0 := by
    unfold subdivPhi
    rw [if_pos hx, if_pos rfl]
  have hphiy : subdivPhi m k x y = 2 * k + 1 := by
    unfold subdivPhi
    have hne : y.val ≠ x.val := fun h => hxy (Fin.ext h).symm
    rw [if_pos hy, if_neg hne]
  omega

end PEqualNP.Outside
