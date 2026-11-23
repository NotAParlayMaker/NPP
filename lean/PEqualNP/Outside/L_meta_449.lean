import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite

namespace PEqualNP.Outside

private lemma subdiv449_bound {m k : ℕ} (u v : Fin m) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) :
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

private def subdivVert {m k : ℕ} (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) :
    Fin (m + 2 * k * (m * m)) :=
  if h0 : p = 0 then ⟨u.val, by omega⟩
  else if htop : p = 2 * k + 1 then ⟨v.val, by omega⟩
  else ⟨m + 2 * k * (u.val * m + v.val) + p - 1, subdiv449_bound u v p (by omega) (by omega)⟩

private lemma subdiv449_div_mod {m k u v p : ℕ} (hk : 1 ≤ k) (hv : v < m)
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

private lemma subdivVert_Q {m k : ℕ}
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) :
    Q u v p (subdivVert u v p hp) := by
  rw [hQ]
  unfold subdivVert
  by_cases h0 : p = 0
  · rw [dif_pos h0]
    exact Or.inl ⟨h0, rfl⟩
  · rw [dif_neg h0]
    by_cases htop : p = 2 * k + 1
    · rw [dif_pos htop]
      exact Or.inr (Or.inl ⟨htop, rfl⟩)
    · rw [dif_neg htop]
      exact Or.inr (Or.inr ⟨by omega, by omega, by dsimp; omega⟩)

private lemma eq_subdivVert_of_Q {m k : ℕ}
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))),
      Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
        (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) (x : Fin (m + 2 * k * (m * m)))
    (hx : Q u v p x) : x = subdivVert u v p hp := by
  apply Fin.ext
  unfold subdivVert
  rcases (hQ u v p x).mp hx with ⟨h0, hxu⟩ | ⟨htop, hxv⟩ | ⟨hp1, hp2, hxeq⟩
  · rw [dif_pos h0]
    exact hxu
  · rw [dif_neg (by omega), dif_pos htop]
    exact hxv
  · rw [dif_neg (by omega), dif_neg (by omega)]
    dsimp
    omega

private lemma subdivVert_internal_inj {m k : ℕ} (hk : 1 ≤ k)
    (u1 v1 u2 v2 : Fin m) (p1 p2 : ℕ)
    (hp1 : p1 ≤ 2 * k + 1) (hp2 : p2 ≤ 2 * k + 1)
    (h1a : 1 ≤ p1) (h1b : p1 ≤ 2 * k)
    (heq : subdivVert u1 v1 p1 hp1 = subdivVert u2 v2 p2 hp2) :
    u1 = u2 ∧ v1 = v2 ∧ p1 = p2 := by
  have hval := congrArg Fin.val heq
  unfold subdivVert at hval
  rw [dif_neg (by omega), dif_neg (by omega)] at hval
  have h2a : 1 ≤ p2 := by
    by_contra h0
    have hp20 : p2 = 0 := by omega
    rw [dif_pos hp20] at hval
    dsimp at hval
    have := u2.isLt
    omega
  have h2b : p2 ≤ 2 * k := by
    by_contra htop
    have hp2t : p2 = 2 * k + 1 := by omega
    rw [dif_neg (by omega), dif_pos hp2t] at hval
    dsimp at hval
    have := v2.isLt
    omega
  rw [dif_neg (by omega), dif_neg (by omega)] at hval
  dsimp at hval
  have hdm1 := subdiv449_div_mod (u := u1.val) hk v1.isLt h1a h1b
  have hdm2 := subdiv449_div_mod (u := u2.val) hk v2.isLt h2a h2b
  rw [hval] at hdm1
  refine ⟨Fin.ext (hdm1.1.symm.trans hdm2.1), Fin.ext (hdm1.2.1.symm.trans hdm2.2.1), ?_⟩
  have := hdm1.2.2.symm.trans hdm2.2.2
  omega

theorem L_meta_449 :
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
      S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard := by
  intro m k H Q S hk hQ hS
  let DirEdge := {e : Fin m × Fin m // e.1 < e.2 ∧ H.Adj e.1 e.2}
  let toH : DirEdge → H.edgeSet := fun e => ⟨s(e.1.1, e.1.2), e.2.2⟩
  have htoH_bij : Function.Bijective toH := by
    constructor
    · intro ⟨⟨u1, v1⟩, hlt1, _⟩ ⟨⟨u2, v2⟩, hlt2, _⟩ h
      have hsym : s(u1, v1) = s(u2, v2) := congrArg Subtype.val h
      rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact False.elim (lt_asymm hlt1 hlt2)
    · rintro ⟨e, he⟩
      refine Sym2.ind (fun a b => ?_) e he
      intro hab
      have hne : a ≠ b := H.ne_of_adj hab
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨⟨(a, b), hlt, hab⟩, rfl⟩
      · refine ⟨⟨(b, a), hgt, H.symm.symm _ _ hab⟩, ?_⟩
        apply Subtype.ext
        exact Sym2.eq_swap
  let toS : Fin (2 * k + 1) × DirEdge → S.edgeSet := fun ⟨p, ⟨⟨u, v⟩, huv, hadj⟩⟩ =>
    ⟨s(subdivVert u v p.val (by omega), subdivVert u v (p.val + 1) (by omega)), by
      rw [SimpleGraph.mem_edgeSet, hS]
      exact ⟨u, v, huv, hadj, p.val, by omega,
        Or.inl ⟨subdivVert_Q Q hQ u v p.val (by omega),
          subdivVert_Q Q hQ u v (p.val + 1) (by omega)⟩⟩⟩
  have htoS_bij : Function.Bijective toS := by
    constructor
    · rintro ⟨p1, ⟨⟨u1, v1⟩, huv1, _⟩⟩ ⟨p2, ⟨⟨u2, v2⟩, huv2, _⟩⟩ h
      have hp1_lt : p1.val < 2 * k + 1 := p1.isLt
      have hp2_lt : p2.val < 2 * k + 1 := p2.isLt
      have hsym :
          s(subdivVert (k := k) u1 v1 p1.val (by omega),
              subdivVert (k := k) u1 v1 (p1.val + 1) (by omega)) =
            s(subdivVert (k := k) u2 v2 p2.val (by omega),
              subdivVert (k := k) u2 v2 (p2.val + 1) (by omega)) :=
        congrArg Subtype.val h
      rcases Sym2.eq_iff.mp hsym with ⟨he1, he2⟩ | ⟨he1, he2⟩
      · by_cases hp10 : p1.val = 0
        · have ⟨hu, hv, hp⟩ :=
            subdivVert_internal_inj hk u1 v1 u2 v2 (p1.val + 1) (p2.val + 1)
              (by omega) (by omega) (by omega) (by omega) he2
          apply Prod.ext
          · dsimp
            exact Fin.ext (by omega)
          · exact Subtype.ext (Prod.ext hu hv)
        · have ⟨hu, hv, hp⟩ :=
            subdivVert_internal_inj hk u1 v1 u2 v2 p1.val p2.val
              (by omega) (by omega) (by omega) (by omega) he1
          apply Prod.ext
          · exact Fin.ext hp
          · exact Subtype.ext (Prod.ext hu hv)
      · by_cases hp10 : p1.val = 0
        · have ⟨hu, hv, hp⟩ :=
            subdivVert_internal_inj hk u1 v1 u2 v2 (p1.val + 1) p2.val
              (by omega) (by omega) (by omega) (by omega) he2
          have hp2_val : p2.val = 1 := by omega
          subst hu hv
          have hval := congrArg Fin.val he1
          unfold subdivVert at hval
          rw [dif_pos hp10] at hval
          by_cases h2k2 : 2 = 2 * k + 1
          · omega
          · rw [dif_neg (by omega), dif_neg (by omega)] at hval
            dsimp at hval
            have := u1.isLt
            omega
        · have ⟨hu, hv, hp⟩ :=
            subdivVert_internal_inj hk u1 v1 u2 v2 p1.val (p2.val + 1)
              (by omega) (by omega) (by omega) (by omega) he1
          by_cases hp1top : p1.val = 2 * k
          · subst hu hv
            have hp2_val : p2.val = 2 * k - 1 := by omega
            have hval := congrArg Fin.val he2
            unfold subdivVert at hval
            rw [dif_neg (by omega), dif_pos (by omega)] at hval
            rw [dif_neg (by omega), dif_neg (by omega)] at hval
            dsimp at hval
            have := v1.isLt
            omega
          · have ⟨_, _, hp'⟩ :=
              subdivVert_internal_inj hk u1 v1 u2 v2 (p1.val + 1) p2.val
                (by omega) (by omega) (by omega) (by omega) he2
            omega
    · rintro ⟨e, he⟩
      refine Sym2.ind (fun x y => ?_) e he
      intro hxy
      rw [SimpleGraph.mem_edgeSet, hS] at hxy
      rcases hxy with ⟨u, v, huv, hadj, p, hp, ⟨hx, hy⟩ | ⟨hy, hx⟩⟩
      · refine ⟨⟨⟨p, by omega⟩, ⟨(u, v), huv, hadj⟩⟩, ?_⟩
        apply Subtype.ext
        have hxeq := eq_subdivVert_of_Q Q hQ u v p (by omega) x hx
        have hyeq := eq_subdivVert_of_Q Q hQ u v (p + 1) (by omega) y hy
        simp [toS, hxeq, hyeq]
      · refine ⟨⟨⟨p, by omega⟩, ⟨(u, v), huv, hadj⟩⟩, ?_⟩
        apply Subtype.ext
        have hyeq := eq_subdivVert_of_Q Q hQ u v p (by omega) y hy
        have hxeq := eq_subdivVert_of_Q Q hQ u v (p + 1) (by omega) x hx
        simp [toS, hxeq, hyeq, Sym2.eq_swap]
  have hcardS : S.edgeSet.ncard = Nat.card (Fin (2 * k + 1) × DirEdge) := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (Equiv.ofBijective toS htoS_bij)).symm
  have hcardH : H.edgeSet.ncard = Nat.card DirEdge := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (Equiv.ofBijective toH htoH_bij)).symm
  rw [hcardS, hcardH, Nat.card_prod, Nat.card_fin]

end PEqualNP.Outside
