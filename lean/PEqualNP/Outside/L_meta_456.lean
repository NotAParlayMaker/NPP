import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

namespace L456

/-- The index of the `i`-th inner vertex of the path replacing the edge `u v`. -/
def enc (m k u v i : ℕ) : ℕ := m + 2 * k * (u * m + v) + i

/-- Distance to the original vertex `x0` along the subdivided edges that touch it, capped at `2k+1`. -/
def phi (m k x0 z : ℕ) : ℕ :=
  if z < m then (if z = x0 then 0 else 2 * k + 1)
  else if (z - m) / (2 * k) / m = x0 then (z - m) % (2 * k) + 1
  else if (z - m) / (2 * k) % m = x0 then 2 * k - (z - m) % (2 * k)
  else 2 * k + 1

theorem phi_orig (m k x0 z : ℕ) (hz : z < m) : phi m k x0 z = if z = x0 then 0 else 2 * k + 1 := by
  simp [phi, hz]

theorem phi_enc (m k x0 u v i : ℕ) (hk : 1 ≤ k) (hu : u < m) (hv : v < m) (hi : i < 2 * k) :
    phi m k x0 (enc m k u v i) = if u = x0 then i + 1 else if v = x0 then 2 * k - i else 2 * k + 1 := by
  have hm : 0 < m := by omega
  have hk2 : 0 < 2 * k := by omega
  have hge : ¬ (enc m k u v i < m) := by unfold enc; omega
  have hq : enc m k u v i - m = 2 * k * (u * m + v) + i := by unfold enc; omega
  have hmod : (2 * k * (u * m + v) + i) % (2 * k) = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have hdiv : (2 * k * (u * m + v) + i) / (2 * k) = u * m + v := by
    rw [Nat.mul_add_div hk2, Nat.div_eq_of_lt hi, Nat.add_zero]
  have hdiv2 : (u * m + v) / m = u := by
    rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt hv, Nat.add_zero]
  have hmod2 : (u * m + v) % m = v := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
  simp only [phi, hge, ite_false, hq, hmod, hdiv, hdiv2, hmod2]

theorem enc_ge (m k u v i : ℕ) : m ≤ enc m k u v i := by unfold enc; omega

end L456

end PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_456 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hx hy hxy p
  -- one step changes the potential by at most one
  have step : ∀ a b, S.Adj a b → L456.phi m k x.val b.val ≤ L456.phi m k x.val a.val + 1 := by
    intro a b hab
    obtain ⟨u, v, huv, hH, q, hq, h⟩ := (hS a b).1 hab
    have huv' : u.val < v.val := Fin.lt_def.1 huv
    have hum := u.isLt
    have hvm := v.isLt
    have key : ∀ a b, Q u v q a → Q u v (q + 1) b →
        L456.phi m k x.val b.val ≤ L456.phi m k x.val a.val + 1 ∧
        L456.phi m k x.val a.val ≤ L456.phi m k x.val b.val + 1 := by
      intro a b ha hb
      rcases (hQ u v q a).1 ha with ⟨hq0, hau⟩ | ⟨hq1, _⟩ | ⟨hq1, hq2, hav⟩
      · subst hq0
        rcases (hQ u v 1 b).1 hb with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, hbv⟩
        · omega
        · omega
        · have hb' : b.val = L456.enc m k u.val v.val 0 := by unfold L456.enc; omega
          rw [hau, hb', L456.phi_orig m k x.val u.val hum, L456.phi_enc m k x.val u.val v.val 0 hk hum hvm (by omega)]
          split_ifs <;> omega
      · omega
      · rcases (hQ u v (q + 1) b).1 hb with ⟨h1, _⟩ | ⟨h1, hbv⟩ | ⟨_, h2, hbv⟩
        · omega
        · have ha' : a.val = L456.enc m k u.val v.val (q - 1) := by unfold L456.enc; omega
          rw [ha', hbv, L456.phi_orig m k x.val v.val hvm, L456.phi_enc m k x.val u.val v.val (q - 1) hk hum hvm (by omega)]
          split_ifs <;> omega
        · have ha' : a.val = L456.enc m k u.val v.val (q - 1) := by unfold L456.enc; omega
          have hb' : b.val = L456.enc m k u.val v.val q := by unfold L456.enc; omega
          rw [ha', hb', L456.phi_enc m k x.val u.val v.val (q - 1) hk hum hvm (by omega),
            L456.phi_enc m k x.val u.val v.val q hk hum hvm (by omega)]
          split_ifs <;> omega
    rcases h with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact (key a b ha hb).1
    · exact (key b a hb ha).2
  -- along a walk the potential grows by at most the length
  have walk_bound : ∀ (a b : Fin (m + 2 * k * (m * m))) (w : S.Walk a b),
      L456.phi m k x.val b.val ≤ L456.phi m k x.val a.val + w.length := by
    intro a b w
    induction w with
    | nil => simp
    | cons hadj w ih =>
      rw [SimpleGraph.Walk.length_cons]
      have := step _ _ hadj
      omega
  have h0 : L456.phi m k x.val x.val = 0 := by rw [L456.phi_orig m k x.val x.val hx]; simp
  have hy' : L456.phi m k x.val y.val = 2 * k + 1 := by
    rw [L456.phi_orig m k x.val y.val hy]
    have : y.val ≠ x.val := fun h => hxy (Fin.ext h).symm
    simp [this]
  have := walk_bound x y p
  omega
