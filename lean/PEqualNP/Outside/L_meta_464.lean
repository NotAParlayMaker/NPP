import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta464

private lemma q_inner_val {m k : ℕ} {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    {u v : Fin m} {p : ℕ} {x : Fin (m + 2 * k * (m * m))}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) (hx : Q u v p x) :
    x.val + 1 = m + 2 * k * (u.val * m + v.val) + p ∧ m ≤ x.val := by
  rw [hQ] at hx
  rcases hx with ⟨h0, _⟩ | ⟨h2k, _⟩ | ⟨_, _, hval⟩
  · omega
  · omega
  · exact ⟨hval, by omega⟩

private lemma q_hub_lt {m k : ℕ} {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    {u v : Fin m} {p : ℕ} {x : Fin (m + 2 * k * (m * m))}
    (hx : Q u v p x) :
    (p = 0 → x.val = u.val ∧ x.val < m) ∧
    (p = 2 * k + 1 → x.val = v.val ∧ x.val < m) := by
  rw [hQ] at hx
  constructor
  · intro hp0
    rcases hx with ⟨_, hv⟩ | ⟨_, _⟩ | ⟨_, _, _⟩
    · exact ⟨hv, hv ▸ u.isLt⟩
    · omega
    · omega
  · intro hp2k
    rcases hx with ⟨_, _⟩ | ⟨_, hv⟩ | ⟨_, _, _⟩
    · omega
    · exact ⟨hv, hv ▸ v.isLt⟩
    · omega

private lemma q_unique_val {m k : ℕ} {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    {u v : Fin m} {p : ℕ} {x y : Fin (m + 2 * k * (m * m))}
    (hx : Q u v p x) (hy : Q u v p y) : x = y := by
  rw [hQ] at hx hy
  apply Fin.ext
  rcases hx with ⟨h0, hxv⟩ | ⟨h2k, hxv⟩ | ⟨h1, h2, hxv⟩ <;>
    rcases hy with ⟨h0', hyv⟩ | ⟨h2k', hyv⟩ | ⟨h1', h2', hyv⟩ <;>
    omega

private lemma q_unique_inner {m k : ℕ} (hk : 1 ≤ k)
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    {u₁ v₁ u₂ v₂ : Fin m} {p₁ p₂ : ℕ} {x : Fin (m + 2 * k * (m * m))}
    (h1a : 1 ≤ p₁) (h1b : p₁ ≤ 2 * k) (h2a : 1 ≤ p₂) (h2b : p₂ ≤ 2 * k)
    (hx₁ : Q u₁ v₁ p₁ x) (hx₂ : Q u₂ v₂ p₂ x) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ p₁ = p₂ := by
  have hv1 := (q_inner_val hQ h1a h1b hx₁).1
  have hv2 := (q_inner_val hQ h2a h2b hx₂).1
  have h1 : 2 * k * (u₁.val * m + v₁.val) + (p₁ - 1) =
      2 * k * (u₂.val * m + v₂.val) + (p₂ - 1) := by omega
  have hp1_lt : p₁ - 1 < 2 * k := by omega
  have hp2_lt : p₂ - 1 < 2 * k := by omega
  have hp_eq : p₁ = p₂ := by
    have hmod := congrArg (· % (2 * k)) h1
    simp [Nat.mod_eq_of_lt hp1_lt, Nat.mod_eq_of_lt hp2_lt] at hmod
    omega
  have huv_eq : u₁.val * m + v₁.val = u₂.val * m + v₂.val := by
    have h2 : 2 * k * (u₁.val * m + v₁.val) = 2 * k * (u₂.val * m + v₂.val) := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  have hm : 0 < m := Nat.zero_lt_of_lt u₁.isLt
  have hv_eq : v₁.val = v₂.val := by
    have hmod := congrArg (· % m) huv_eq
    simp [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt v₁.isLt, Nat.mod_eq_of_lt v₂.isLt] at hmod
    exact hmod
  have hu_eq : u₁.val = u₂.val := by
    have h3 : u₁.val * m = u₂.val * m := by omega
    exact Nat.eq_of_mul_eq_mul_right hm h3
  exact ⟨Fin.ext hu_eq, Fin.ext hv_eq, hp_eq⟩

private lemma inner_adj {m k : ℕ} (hk : 1 ≤ k) {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (hS : ∀ x y : Fin (m + 2 * k * (m * m)),
      S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
        ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x)))
    {u v : Fin m} {p : ℕ} {x y : Fin (m + 2 * k * (m * m))}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) (hx : Q u v p x) (hxy : S.Adj x y) :
    Q u v (p - 1) y ∨ Q u v (p + 1) y := by
  have hxm : m ≤ x.val := (q_inner_val hQ hp1 hp2 hx).2
  rw [hS] at hxy
  rcases hxy with ⟨u', v', _, _, q, hq, ⟨hxq, hyq⟩ | ⟨hyq, hxq⟩⟩
  · have hq1 : 1 ≤ q := by
      by_contra h0
      have hq0 : q = 0 := by omega
      have hlt := ((q_hub_lt hQ hxq).1 hq0).2
      omega
    obtain ⟨rfl, rfl, rfl⟩ := q_unique_inner hk hQ hp1 hp2 hq1 hq hx hxq
    exact Or.inr hyq
  · have hq2 : q + 1 ≤ 2 * k := by
      by_contra hhi
      have hqhi : q + 1 = 2 * k + 1 := by omega
      have hlt := ((q_hub_lt hQ hxq).2 hqhi).2
      omega
    obtain ⟨rfl, rfl, hpEq⟩ := q_unique_inner hk hQ hp1 hp2 (by omega) hq2 hx hxq
    have hqeq : q = p - 1 := by omega
    rw [hqeq] at hyq
    exact Or.inl hyq

private lemma trace_fwd {m k : ℕ} (hk : 1 ≤ k) {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (hS : ∀ x y : Fin (m + 2 * k * (m * m)),
      S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
        ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x)))
    {w : ℕ → Fin (m + 2 * k * (m * m))}
    (hadj : ∀ t, S.Adj (w t) (w (t + 1)))
    (hbt : ∀ t, w t ≠ w (t + 2))
    {u v : Fin m} {p₀ t₀ : ℕ}
    (hp₀ : p₀ ≤ 2 * k) (h0 : Q u v p₀ (w t₀)) (h1 : Q u v (p₀ + 1) (w (t₀ + 1))) :
    ∀ d : ℕ, p₀ + d ≤ 2 * k + 1 → Q u v (p₀ + d) (w (t₀ + d)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    cases d with
    | zero => simpa using h0
    | succ n =>
      cases n with
      | zero => simpa using h1
      | succ r =>
        have hr0 := ih r (by omega) (by omega)
        have hr1 := ih (r + 1) (by omega) (by omega)
        have hstep := inner_adj hk hQ hS (by omega) (by omega) hr1
          (by simpa [Nat.add_assoc] using hadj (t₀ + r + 1))
        rcases hstep with hback | hnext
        · exfalso
          have hsub : p₀ + (r + 1) - 1 = p₀ + r := by omega
          rw [hsub] at hback
          have hEq := q_unique_val hQ hr0 hback
          have hidx : t₀ + (r + 2) = t₀ + r + 2 := by omega
          rw [hidx] at hEq
          exact hbt (t₀ + r) hEq
        · have hidx1 : p₀ + (r + 1) + 1 = p₀ + (r + 2) := by omega
          have hidx2 : t₀ + (r + 1) + 1 = t₀ + (r + 2) := by omega
          rw [hidx1] at hnext
          simpa [Nat.add_assoc] using hnext

private lemma trace_bwd {m k : ℕ} (hk : 1 ≤ k) {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (hS : ∀ x y : Fin (m + 2 * k * (m * m)),
      S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
        ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x)))
    {w : ℕ → Fin (m + 2 * k * (m * m))}
    (hadj : ∀ t, S.Adj (w t) (w (t + 1)))
    (hbt : ∀ t, w t ≠ w (t + 2))
    {u v : Fin m} {p₀ t₀ : ℕ}
    (hp₀ : p₀ ≤ 2 * k) (h0 : Q u v (p₀ + 1) (w t₀)) (h1 : Q u v p₀ (w (t₀ + 1))) :
    ∀ d : ℕ, d ≤ p₀ + 1 → Q u v (p₀ + 1 - d) (w (t₀ + d)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    cases d with
    | zero => simpa using h0
    | succ n =>
      cases n with
      | zero => simpa using h1
      | succ r =>
        have hr0 := ih r (by omega) (by omega)
        have hr1 := ih (r + 1) (by omega) (by omega)
        have hstep := inner_adj hk hQ hS (by omega) (by omega) hr1
          (by simpa [Nat.add_assoc] using hadj (t₀ + r + 1))
        rcases hstep with hnext | hback
        · have hidx : p₀ + 1 - (r + 1) - 1 = p₀ + 1 - (r + 2) := by omega
          rw [hidx] at hnext
          simpa [Nat.add_assoc] using hnext
        · exfalso
          have hadd : p₀ + 1 - (r + 1) + 1 = p₀ + 1 - r := by omega
          rw [hadd] at hback
          have hEq := q_unique_val hQ hr0 hback
          have hidx : t₀ + (r + 2) = t₀ + r + 2 := by omega
          rw [hidx] at hEq
          exact hbt (t₀ + r) hEq

private lemma hub_step {m k : ℕ} (hk : 1 ≤ k) {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))}
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (hS : ∀ x y : Fin (m + 2 * k * (m * m)),
      S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
        ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x)))
    {w : ℕ → Fin (m + 2 * k * (m * m))}
    (hadj : ∀ t, S.Adj (w t) (w (t + 1)))
    (hbt : ∀ t, w t ≠ w (t + 2))
    {t : ℕ} (ht : (w t).val < m) :
    ∃ u v : Fin m, u < v ∧
      ((∀ d ≤ 2 * k + 1, Q u v d (w (t + d))) ∨
       (∀ d ≤ 2 * k + 1, Q u v (2 * k + 1 - d) (w (t + d)))) := by
  have he := hadj t
  rw [hS] at he
  rcases he with ⟨u, v, huv, _, p, hp, ⟨hp0, hp1⟩ | ⟨hp1, hp0⟩⟩
  · have hpz : p = 0 := by
      by_contra hne
      have hm := (q_inner_val hQ (by omega) hp hp0).2
      omega
    subst hpz
    refine ⟨u, v, huv, Or.inl ?_⟩
    intro d hd
    simpa using trace_fwd hk hQ hS hadj hbt hp hp0 hp1 d (by omega)
  · have hphi : p = 2 * k := by
      by_contra hne
      have hm := (q_inner_val hQ (by omega) (by omega) hp0).2
      omega
    subst hphi
    refine ⟨u, v, huv, Or.inr ?_⟩
    intro d hd
    exact trace_bwd hk hQ hS hadj hbt (le_refl _) hp0 hp1 d hd

private lemma cycle_getVert_inj {V : Type*} {G : SimpleGraph V} {x : V} {c : G.Walk x x}
    (hc : c.IsCycle) {a b : ℕ} (ha : a < c.length) (hb : b < c.length)
    (hEq : c.getVert a = c.getVert b) : a = b := by
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hlen : c.support.tail.length = c.length := by
    simp [SimpleGraph.Walk.length_support]
  have h3 : 3 ≤ c.length := hc.three_le_length
  have hlt_idx : ∀ i : ℕ, i < c.length → (if i = 0 then c.length - 1 else i - 1) < c.support.tail.length := by
    intro i hi
    split_ifs <;> omega
  have hget : ∀ i : ℕ, (hi : i < c.length) →
      c.support.tail[(if i = 0 then c.length - 1 else i - 1)]'(hlt_idx i hi) = c.getVert i := by
    intro i hi
    rw [List.getElem_tail]
    split_ifs with h0
    · subst h0
      have hidx : c.length - 1 + 1 = c.length := by omega
      simp only [hidx]
      rw [← SimpleGraph.Walk.getVert_eq_support_getElem c (le_refl _),
        SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
    · have hidx : i - 1 + 1 = i := by omega
      simp only [hidx]
      exact (SimpleGraph.Walk.getVert_eq_support_getElem c (le_of_lt hi)).symm
  have h1 := hget a ha
  have h2 := hget b hb
  have htailEq :
      c.support.tail[(if a = 0 then c.length - 1 else a - 1)]'(hlt_idx a ha) =
      c.support.tail[(if b = 0 then c.length - 1 else b - 1)]'(hlt_idx b hb) := by
    rw [h1, h2, hEq]
  have hidxEq := (List.Nodup.getElem_inj_iff hnodup).mp htailEq
  split_ifs at hidxEq <;> omega

end PEqualNP.Outside.Meta464

open PEqualNP.Outside.Meta464 in
theorem PEqualNP.Outside.L_meta_464 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (x : Fin (m + 2 * k * (m * m))) (c : S.Walk x x), c.IsCycle → 6 * k + 3 ≤ c.length := by
  intro m k H Q S hk hQ hS x c hc
  set L := c.length with hLdef
  have hL3 : 3 ≤ L := hc.three_le_length
  let w0 : ℕ → Fin (m + 2 * k * (m * m)) := fun t => c.getVert (t % L)
  have hw0_adj : ∀ t, S.Adj (w0 t) (w0 (t + 1)) := by
    intro t
    dsimp only [w0]
    have hlt : t % L < L := Nat.mod_lt t (by omega)
    by_cases hlast : t % L + 1 = L
    · have hmod : (t + 1) % L = 0 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < L), hlast, Nat.mod_self]
      rw [hmod]
      have h1 : S.Adj (c.getVert (t % L)) (c.getVert (t % L + 1)) := c.adj_getVert_succ hlt
      have h2 : c.getVert (t % L + 1) = c.getVert 0 := by
        rw [hlast, hLdef, SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
      rwa [h2] at h1
    · have hmod : (t + 1) % L = t % L + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < L), Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact c.adj_getVert_succ hlt
  have hw0_bt : ∀ t, w0 t ≠ w0 (t + 2) := by
    intro t hEq
    have hmodEq : t % L = (t + 2) % L :=
      cycle_getVert_inj hc (Nat.mod_lt t (by omega)) (Nat.mod_lt (t + 2) (by omega)) hEq
    have hlt : t % L < L := Nat.mod_lt t (by omega)
    have h2 : (t + 2) % L = (t % L + 2) % L := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 < L)]
    rw [h2] at hmodEq
    by_cases hcase : t % L + 2 < L
    · rw [Nat.mod_eq_of_lt hcase] at hmodEq
      omega
    · have hsub : (t % L + 2) % L = t % L + 2 - L := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hsub] at hmodEq
      omega
  have hex_hub : ∃ t₀ : ℕ, (w0 t₀).val < m := by
    have he := hw0_adj 0
    rw [hS] at he
    rcases he with ⟨u, v, _, _, p, hp, ⟨h0, h1⟩ | ⟨h1, h0⟩⟩
    · have htr := trace_fwd hk hQ hS hw0_adj hw0_bt hp h0 h1 (2 * k + 1 - p) (by omega)
      have hidx : p + (2 * k + 1 - p) = 2 * k + 1 := by omega
      rw [hidx] at htr
      exact ⟨0 + (2 * k + 1 - p), ((q_hub_lt hQ htr).2 rfl).2⟩
    · have htr := trace_bwd hk hQ hS hw0_adj hw0_bt hp h0 h1 (p + 1) (le_refl _)
      have hidx : p + 1 - (p + 1) = 0 := by omega
      rw [hidx] at htr
      exact ⟨0 + (p + 1), ((q_hub_lt hQ htr).1 rfl).2⟩
  rcases hex_hub with ⟨t₀, ht₀⟩
  let w : ℕ → Fin (m + 2 * k * (m * m)) := fun t => w0 (t₀ + t)
  have hw_adj : ∀ t, S.Adj (w t) (w (t + 1)) := fun t => by
    simpa [w, Nat.add_assoc] using hw0_adj (t₀ + t)
  have hw_bt : ∀ t, w t ≠ w (t + 2) := fun t => by
    simpa [w, Nat.add_assoc] using hw0_bt (t₀ + t)
  have hw_per : w L = w 0 := by
    dsimp only [w, w0]
    congr 1
    rw [Nat.add_zero, Nat.add_mod_right]
  have hw_hub0 : (w 0).val < m := by simpa [w] using ht₀
  have hw_hubL : (w L).val < m := by rw [hw_per]; exact hw_hub0
  obtain ⟨u₁, v₁, huv₁, hseg₁⟩ := hub_step hk hQ hS hw_adj hw_bt hw_hub0
  have hinner₁ : ∀ d, 1 ≤ d → d ≤ 2 * k → m ≤ (w d).val := by
    intro d hd1 hd2
    rcases hseg₁ with h | h
    · have hq := h d (by omega); rw [Nat.zero_add] at hq
      exact (q_inner_val hQ hd1 hd2 hq).2
    · have hq := h d (by omega); rw [Nat.zero_add] at hq
      exact (q_inner_val hQ (by omega) (by omega) hq).2
  have hhub₁ : (w (2 * k + 1)).val < m := by
    rcases hseg₁ with h | h
    · have hq := h (2 * k + 1) (le_refl _); rw [Nat.zero_add] at hq
      exact ((q_hub_lt hQ hq).2 rfl).2
    · have hq := h (2 * k + 1) (le_refl _); rw [Nat.zero_add] at hq
      exact ((q_hub_lt hQ hq).1 (by omega)).2
  have hne10 : w (2 * k + 1) ≠ w 0 := by
    intro hEq
    have hv := congrArg Fin.val hEq
    rcases hseg₁ with h | h
    · have hq0 := h 0 (by omega); rw [Nat.zero_add] at hq0
      have hq1 := h (2 * k + 1) (le_refl _); rw [Nat.zero_add] at hq1
      have h0 := ((q_hub_lt hQ hq0).1 rfl).1
      have h1 := ((q_hub_lt hQ hq1).2 rfl).1
      have : u₁.val < v₁.val := huv₁
      omega
    · have hq0 := h 0 (by omega); rw [Nat.zero_add] at hq0
      have hq1 := h (2 * k + 1) (le_refl _); rw [Nat.zero_add] at hq1
      have h0 := ((q_hub_lt hQ hq0).2 (by omega)).1
      have h1 := ((q_hub_lt hQ hq1).1 (by omega)).1
      have : u₁.val < v₁.val := huv₁
      omega
  have hL_gt1 : 2 * k + 1 < L := by
    by_contra hle
    by_cases hEq : L = 2 * k + 1
    · rw [← hEq] at hne10
      exact hne10 hw_per
    · have := hinner₁ L (by omega) (by omega)
      omega
  obtain ⟨u₂, v₂, huv₂, hseg₂⟩ := hub_step hk hQ hS hw_adj hw_bt hhub₁
  have hinner₂ : ∀ d, 1 ≤ d → d ≤ 2 * k → m ≤ (w (2 * k + 1 + d)).val := by
    intro d hd1 hd2
    rcases hseg₂ with h | h
    · exact (q_inner_val hQ hd1 hd2 (h d (by omega))).2
    · exact (q_inner_val hQ (by omega) (by omega) (h d (by omega))).2
  have hhub₂ : (w (4 * k + 2)).val < m := by
    have hidx : 2 * k + 1 + (2 * k + 1) = 4 * k + 2 := by omega
    rcases hseg₂ with h | h
    · have hq := h (2 * k + 1) (le_refl _)
      rw [hidx] at hq
      exact ((q_hub_lt hQ hq).2 rfl).2
    · have hq := h (2 * k + 1) (le_refl _)
      rw [hidx] at hq
      exact ((q_hub_lt hQ hq).1 (by omega)).2
  have hne20 : w (4 * k + 2) ≠ w 0 := by
    intro hEq
    have hv := congrArg Fin.val hEq
    have hidx2 : 2 * k + 1 + (2 * k + 1) = 4 * k + 2 := by omega
    have hbt_at : w (2 * k) ≠ w (2 * k + 2) := hw_bt (2 * k)
    rcases hseg₁ with h1 | h1 <;> rcases hseg₂ with h2 | h2
    · have hq0 := h1 0 (by omega); rw [Nat.zero_add] at hq0
      have hq1 := h1 (2 * k + 1) (le_refl _); rw [Nat.zero_add] at hq1
      have hr0 := h2 0 (by omega); rw [Nat.add_zero] at hr0
      have hr1 := h2 (2 * k + 1) (le_refl _); rw [hidx2] at hr1
      have ha0 := ((q_hub_lt hQ hq0).1 rfl).1
      have ha1 := ((q_hub_lt hQ hq1).2 rfl).1
      have hb0 := ((q_hub_lt hQ hr0).1 rfl).1
      have hb1 := ((q_hub_lt hQ hr1).2 rfl).1
      have : u₁.val < v₁.val := huv₁
      have : u₂.val < v₂.val := huv₂
      omega
    · have hq0 := h1 0 (by omega); rw [Nat.zero_add] at hq0
      have hq1 := h1 (2 * k + 1) (le_refl _); rw [Nat.zero_add] at hq1
      have hr0 := h2 0 (by omega); rw [Nat.add_zero] at hr0
      have hr1 := h2 (2 * k + 1) (le_refl _); rw [hidx2] at hr1
      have ha0 := ((q_hub_lt hQ hq0).1 rfl).1
      have ha1 := ((q_hub_lt hQ hq1).2 rfl).1
      have hb0 := ((q_hub_lt hQ hr0).2 (by omega)).1
      have hb1 := ((q_hub_lt hQ hr1).1 (by omega)).1
      have huEq : u₁ = u₂ := Fin.ext (by omega)
      have hvEq : v₁ = v₂ := Fin.ext (by omega)
      subst huEq hvEq
      have hq1' : Q u₁ v₁ (2 * k) (w (2 * k)) := by simpa using h1 (2 * k) (by omega)
      have hq2' : Q u₁ v₁ (2 * k) (w (2 * k + 2)) := by
        have := h2 1 (by omega)
        have hi1 : 2 * k + 1 - 1 = 2 * k := by omega
        have hi2 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
        rw [hi1, hi2] at this
        exact this
      exact hbt_at (q_unique_val hQ hq1' hq2')
    · have hq0 := h1 0 (by omega); rw [Nat.zero_add] at hq0
      have hq1 := h1 (2 * k + 1) (le_refl _); rw [Nat.zero_add] at hq1
      have hr0 := h2 0 (by omega); rw [Nat.add_zero] at hr0
      have hr1 := h2 (2 * k + 1) (le_refl _); rw [hidx2] at hr1
      have ha0 := ((q_hub_lt hQ hq0).2 (by omega)).1
      have ha1 := ((q_hub_lt hQ hq1).1 (by omega)).1
      have hb0 := ((q_hub_lt hQ hr0).1 rfl).1
      have hb1 := ((q_hub_lt hQ hr1).2 rfl).1
      have huEq : u₁ = u₂ := Fin.ext (by omega)
      have hvEq : v₁ = v₂ := Fin.ext (by omega)
      subst huEq hvEq
      have hq1' : Q u₁ v₁ 1 (w (2 * k)) := by
        have := h1 (2 * k) (by omega)
        have hi1 : 2 * k + 1 - 2 * k = 1 := by omega
        rw [hi1, Nat.zero_add] at this
        exact this
      have hq2' : Q u₁ v₁ 1 (w (2 * k + 2)) := by
        have := h2 1 (by omega)
        have hi2 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
        rw [hi2] at this
        exact this
      exact hbt_at (q_unique_val hQ hq1' hq2')
    · have hq0 := h1 0 (by omega); rw [Nat.zero_add] at hq0
      have hq1 := h1 (2 * k + 1) (le_refl _); rw [Nat.zero_add] at hq1
      have hr0 := h2 0 (by omega); rw [Nat.add_zero] at hr0
      have hr1 := h2 (2 * k + 1) (le_refl _); rw [hidx2] at hr1
      have ha0 := ((q_hub_lt hQ hq0).2 (by omega)).1
      have ha1 := ((q_hub_lt hQ hq1).1 (by omega)).1
      have hb0 := ((q_hub_lt hQ hr0).2 (by omega)).1
      have hb1 := ((q_hub_lt hQ hr1).1 (by omega)).1
      have : u₁.val < v₁.val := huv₁
      have : u₂.val < v₂.val := huv₂
      omega
  have hL_gt2 : 4 * k + 2 < L := by
    by_contra hle
    by_cases hEq : L = 4 * k + 2
    · rw [← hEq] at hne20
      exact hne20 hw_per
    · have h := hinner₂ (L - (2 * k + 1)) (by omega) (by omega)
      have hi : 2 * k + 1 + (L - (2 * k + 1)) = L := by omega
      rw [hi] at h
      omega
  obtain ⟨u₃, v₃, _, hseg₃⟩ := hub_step hk hQ hS hw_adj hw_bt hhub₂
  have hinner₃ : ∀ d, 1 ≤ d → d ≤ 2 * k → m ≤ (w (4 * k + 2 + d)).val := by
    intro d hd1 hd2
    rcases hseg₃ with h | h
    · exact (q_inner_val hQ hd1 hd2 (h d (by omega))).2
    · exact (q_inner_val hQ (by omega) (by omega) (h d (by omega))).2
  by_contra hlt3
  have h := hinner₃ (L - (4 * k + 2)) (by omega) (by omega)
  have hi : 4 * k + 2 + (L - (4 * k + 2)) = L := by omega
  rw [hi] at h
  omega
