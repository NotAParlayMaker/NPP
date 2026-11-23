import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Data.Set.Card

namespace PEqualNP.Outside

private lemma subdiv460_div_mod {m k : ℕ} (u : ℕ) {v p : ℕ} (hk : 1 ≤ k) (hv : v < m)
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

private lemma subdiv460_bound {m : ℕ} (k : ℕ) (u v : Fin m) (p : ℕ)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) :
    m + 2 * k * (u.val * m + v.val) + p - 1 < m + 2 * k * (m * m) := by
  have huv_lt : u.val * m + v.val + 1 ≤ m * m := by
    have h1 : u.val + 1 ≤ m := u.isLt
    have h2 : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m h1
    have h3 : (u.val + 1) * m = u.val * m + m := by ring
    omega
  have hmul : 2 * k * (u.val * m + v.val) + 2 * k ≤ 2 * k * (m * m) := by
    have := Nat.mul_le_mul_left (2 * k) huv_lt
    linarith
  omega

private def subdivVert460 {m : ℕ} (k : ℕ) (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) :
    Fin (m + 2 * k * (m * m)) :=
  if h0 : p = 0 then ⟨u.val, by omega⟩
  else if htop : p = 2 * k + 1 then ⟨v.val, by omega⟩
  else ⟨m + 2 * k * (u.val * m + v.val) + p - 1, subdiv460_bound k u v p (by omega) (by omega)⟩

private lemma eq_subdivVert460_of_Q {m k : ℕ}
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) (x : Fin (m + 2 * k * (m * m)))
    (hx : Q u v p x) : x = subdivVert460 k u v p hp := by
  apply Fin.ext
  unfold subdivVert460
  rcases (hQ u v p x).mp hx with ⟨h0, hxu⟩ | ⟨htop, hxv⟩ | ⟨hp1, hp2, hxeq⟩
  · rw [dif_pos h0]
    exact hxu
  · rw [dif_neg (by omega), dif_pos htop]
    exact hxv
  · rw [dif_neg (by omega), dif_neg (by omega)]
    dsimp
    omega

private def subdiv460Phi (m k : ℕ) (x z : Fin (m + 2 * k * (m * m))) : ℕ :=
  if z.val < m then
    if z.val = x.val then 0 else 2 * k + 1
  else
    let q := (z.val - m) / (2 * k)
    let r := (z.val - m) % (2 * k)
    if q / m = x.val then r + 1
    else if q % m = x.val then 2 * k - r
    else 2 * k + 1

private lemma subdiv460Phi_on_Q {m k : ℕ} (hk : 1 ≤ k)
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (z : Fin (m + 2 * k * (m * m))),
      Q u v p z ↔ (p = 0 ∧ z.val = u.val) ∨ (p = 2 * k + 1 ∧ z.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ z.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (x : Fin (m + 2 * k * (m * m))) (u v : Fin m) (huv : u < v)
    (p : ℕ) (z : Fin (m + 2 * k * (m * m))) (hz : Q u v p z) :
    subdiv460Phi m k x z =
      if u.val = x.val then p
      else if v.val = x.val then 2 * k + 1 - p
      else 2 * k + 1 := by
  have huv_ne : u.val ≠ v.val := by
    have : u.val < v.val := huv
    omega
  rcases (hQ u v p z).mp hz with ⟨rfl, hzu⟩ | ⟨rfl, hzv⟩ | ⟨hp1, hp2, hzeq⟩
  · unfold subdiv460Phi
    have hzm : z.val < m := by omega
    rw [if_pos hzm, hzu]
    by_cases hux : u.val = x.val
    · rw [if_pos hux, if_pos hux]
    · rw [if_neg hux, if_neg hux]
      by_cases hvx : v.val = x.val
      · rw [if_pos hvx]
        omega
      · rw [if_neg hvx]
  · unfold subdiv460Phi
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
  · unfold subdiv460Phi
    have hzge : ¬ z.val < m := by omega
    rw [if_neg hzge]
    have hval : z.val = m + 2 * k * (u.val * m + v.val) + p - 1 := by omega
    have hdm := subdiv460_div_mod u.val hk v.isLt hp1 hp2
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

private lemma ncard_le_two_of_subset_pair460 {α : Type*} [Finite α] (s : Set α) (a b : α)
    (h : s ⊆ {a, b}) : s.ncard ≤ 2 := by
  calc s.ncard ≤ ({a, b} : Set α).ncard := Set.ncard_le_ncard h (Set.toFinite _)
    _ ≤ ({b} : Set α).ncard + 1 := Set.ncard_insert_le a {b}
    _ = 2 := by simp

theorem L_meta_460 :
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
        x ≠ y → 3 ≤ (S.neighborSet x).ncard → 3 ≤ (S.neighborSet y).ncard →
        ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hxy hx3 hy3 walk
  have hdeg_lt_m : ∀ w : Fin (m + 2 * k * (m * m)), 3 ≤ (S.neighborSet w).ncard → w.val < m := by
    intro w hw3
    by_contra hge
    have hwm : m ≤ w.val := by omega
    have hm_pos : 0 < m := by
      by_contra hm0
      have hm_eq : m = 0 := by omega
      have hwlt := w.isLt
      have h0 : m + 2 * k * (m * m) = 0 := by simp [hm_eq]
      omega
    have h2k : 0 < 2 * k := by omega
    let d := w.val - m
    let q := d / (2 * k)
    let r := d % (2 * k)
    let u0_nat := q / m
    let v0_nat := q % m
    have hd_lt : d < 2 * k * (m * m) := by have := w.isLt; omega
    have hq_lt : q < m * m := Nat.div_lt_of_lt_mul hd_lt
    have hu0_lt : u0_nat < m := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have hv0_lt : v0_nat < m := Nat.mod_lt q hm_pos
    have hr_lt : r < 2 * k := Nat.mod_lt d h2k
    let u0 : Fin m := ⟨u0_nat, hu0_lt⟩
    let v0 : Fin m := ⟨v0_nat, hv0_lt⟩
    have hQ_w : ∀ (u v : Fin m) (p : ℕ), Q u v p w → u = u0 ∧ v = v0 ∧ p = r + 1 := by
      intro u v p hpw
      rcases (hQ u v p w).mp hpw with ⟨_, hwu⟩ | ⟨_, hwv⟩ | ⟨hp1, hp2, hweq⟩
      · have := u.isLt; omega
      · have := v.isLt; omega
      · have hval : w.val = m + 2 * k * (u.val * m + v.val) + p - 1 := by omega
        have hdm := subdiv460_div_mod u.val hk v.isLt hp1 hp2
        rw [← hval] at hdm
        refine ⟨Fin.ext hdm.1.symm, Fin.ext hdm.2.1.symm, ?_⟩
        have hmod : r = p - 1 := hdm.2.2
        omega
    let a : Fin (m + 2 * k * (m * m)) := subdivVert460 k u0 v0 r (by omega)
    let b : Fin (m + 2 * k * (m * m)) := subdivVert460 k u0 v0 (r + 2) (by omega)
    have hsub : S.neighborSet w ⊆ {a, b} := by
      intro z hz
      have hadj : S.Adj w z := hz
      rcases (hS w z).mp hadj with ⟨u, v, _, _, p, hp, ⟨hwq, hzq⟩ | ⟨hzq, hwq⟩⟩
      · rcases hQ_w u v p hwq with ⟨rfl, rfl, hpr⟩
        right
        have : p + 1 = r + 2 := by omega
        rw [this] at hzq
        exact eq_subdivVert460_of_Q Q hQ u0 v0 (r + 2) (by omega) z hzq
      · rcases hQ_w u v (p + 1) hwq with ⟨rfl, rfl, hpr⟩
        left
        have : p = r := by omega
        rw [this] at hzq
        exact eq_subdivVert460_of_Q Q hQ u0 v0 r (by omega) z hzq
    have hle2 : (S.neighborSet w).ncard ≤ 2 := ncard_le_two_of_subset_pair460 _ a b hsub
    omega
  have hx : x.val < m := hdeg_lt_m x hx3
  have hy : y.val < m := hdeg_lt_m y hy3
  have hstep : ∀ a b : Fin (m + 2 * k * (m * m)),
      S.Adj a b → subdiv460Phi m k x b ≤ subdiv460Phi m k x a + 1 := by
    intro a b hab
    rcases (hS a b).mp hab with ⟨u, v, huv, _, p, hp, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
    · rw [subdiv460Phi_on_Q hk Q hQ x u v huv p a ha,
        subdiv460Phi_on_Q hk Q hQ x u v huv (p + 1) b hb]
      split_ifs <;> omega
    · rw [subdiv460Phi_on_Q hk Q hQ x u v huv p b hb,
        subdiv460Phi_on_Q hk Q hQ x u v huv (p + 1) a ha]
      split_ifs <;> omega
  have hwalk : ∀ {a b : Fin (m + 2 * k * (m * m))} (w : S.Walk a b),
      subdiv460Phi m k x b ≤ subdiv460Phi m k x a + w.length := by
    intro a b w
    induction w with
    | nil => simp
    | @cons a c b hac w' ih =>
      have h1 := hstep a c hac
      simp only [SimpleGraph.Walk.length_cons]
      omega
  have hbound := hwalk walk
  have hphix : subdiv460Phi m k x x = 0 := by
    unfold subdiv460Phi
    rw [if_pos hx, if_pos rfl]
  have hphiy : subdiv460Phi m k x y = 2 * k + 1 := by
    unfold subdiv460Phi
    have hne : y.val ≠ x.val := fun h => hxy (Fin.ext h).symm
    rw [if_pos hy, if_neg hne]
  omega

end PEqualNP.Outside
