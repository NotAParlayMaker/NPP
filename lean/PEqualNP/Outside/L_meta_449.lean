import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta449

def pos (m k : ℕ) (u v : Fin m) (p : ℕ) : ℕ :=
  if p = 0 then u.val else if p = 2 * k + 1 then v.val
  else m + 2 * k * (u.val * m + v.val) + p - 1

lemma pos_mid (m k : ℕ) (u v : Fin m) (p : ℕ) (h1 : 1 ≤ p) (h2 : p ≤ 2 * k) :
    pos m k u v p = m + 2 * k * (u.val * m + v.val) + p - 1 := by
  unfold pos
  split_ifs <;> omega

lemma mid_ge (m k : ℕ) (u v : Fin m) (p : ℕ) (h : 1 ≤ p ∧ p ≤ 2 * k) :
    m ≤ pos m k u v p := by
  rw [pos_mid m k u v p h.1 h.2]
  omega

lemma small (m k : ℕ) (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1)
    (h : ¬ (1 ≤ p ∧ p ≤ 2 * k)) : pos m k u v p < m := by
  have hu := u.isLt
  have hv := v.isLt
  unfold pos
  split_ifs <;> omega

lemma divmod_inj (K w w' r r' : ℕ) (hr : r < K) (hr' : r' < K)
    (h : K * w + r = K * w' + r') : w = w' ∧ r = r' := by
  rcases lt_trichotomy w w' with hw | hw | hw
  · have := Nat.mul_le_mul_left K (Nat.succ_le_of_lt hw)
    rw [Nat.mul_succ] at this
    omega
  · subst hw
    omega
  · have := Nat.mul_le_mul_left K (Nat.succ_le_of_lt hw)
    rw [Nat.mul_succ] at this
    omega

lemma mid_inj (m k : ℕ) (u v u' v' : Fin m) (p p' : ℕ) (hp : 1 ≤ p ∧ p ≤ 2 * k)
    (hp' : 1 ≤ p' ∧ p' ≤ 2 * k) (h : pos m k u v p = pos m k u' v' p') :
    u = u' ∧ v = v' ∧ p = p' := by
  rw [pos_mid m k u v p hp.1 hp.2, pos_mid m k u' v' p' hp'.1 hp'.2] at h
  have e : 2 * k * (u.val * m + v.val) + (p - 1) =
      2 * k * (u'.val * m + v'.val) + (p' - 1) := by
    omega
  obtain ⟨hw, hpp⟩ := divmod_inj (2 * k) _ _ _ _ (by omega) (by omega) e
  have e2 : m * u.val + v.val = m * u'.val + v'.val := by
    rw [Nat.mul_comm m u.val, Nat.mul_comm m u'.val]
    exact hw
  obtain ⟨hu, hv⟩ := divmod_inj m _ _ _ _ v.isLt v'.isLt e2
  exact ⟨Fin.ext hu, Fin.ext hv, by omega⟩

lemma pos_lt (m k : ℕ) (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) :
    pos m k u v p < m + 2 * k * (m * m) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold pos
  split_ifs with h0 h1
  · omega
  · omega
  · have hw : u.val * m + v.val + 1 ≤ m * m := by nlinarith
    have := Nat.mul_le_mul_left (2 * k) hw
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

lemma Q_iff (m k : ℕ) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔
      (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) (x : Fin (m + 2 * k * (m * m))) :
    Q u v p x ↔ x.val = pos m k u v p := by
  rw [hQ]
  unfold pos
  split_ifs with h0 h1 <;> constructor <;> intro h <;> omega

theorem main : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard := by
  intro m k H Q S hk hQ hS
  have hadj : ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧
      H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
      ((x.val = pos m k u v p ∧ y.val = pos m k u v (p + 1)) ∨
        (y.val = pos m k u v p ∧ x.val = pos m k u v (p + 1))) := by
    intro x y
    rw [hS]
    constructor
    · rintro ⟨u, v, huv, ha, p, hp, h⟩
      refine ⟨u, v, huv, ha, p, hp, ?_⟩
      rwa [Q_iff m k Q hQ u v p (by omega) x, Q_iff m k Q hQ u v (p + 1) (by omega) y,
        Q_iff m k Q hQ u v p (by omega) y, Q_iff m k Q hQ u v (p + 1) (by omega) x] at h
    · rintro ⟨u, v, huv, ha, p, hp, h⟩
      refine ⟨u, v, huv, ha, p, hp, ?_⟩
      rwa [Q_iff m k Q hQ u v p (by omega) x, Q_iff m k Q hQ u v (p + 1) (by omega) y,
        Q_iff m k Q hQ u v p (by omega) y, Q_iff m k Q hQ u v (p + 1) (by omega) x]
  let D : Set (Fin m × Fin m) := {e | e.1 < e.2 ∧ H.Adj e.1 e.2}
  let T : Set ((Fin m × Fin m) × ℕ) := D ×ˢ Set.Iio (2 * k + 1)
  let g : (Fin m × Fin m) × ℕ → Sym2 ℕ := fun t =>
    s(pos m k t.1.1 t.1.2 t.2, pos m k t.1.1 t.1.2 (t.2 + 1))
  have himg : Sym2.map Fin.val '' S.edgeSet = g '' T := by
    ext e
    simp only [Set.mem_image]
    constructor
    · rintro ⟨e', he', rfl⟩
      induction e' using Sym2.ind with
      | h x y =>
        rw [SimpleGraph.mem_edgeSet, hadj] at he'
        obtain ⟨u, v, huv, ha, p, hp, h | h⟩ := he'
        · refine ⟨((u, v), p), ⟨⟨huv, ha⟩, show p < 2 * k + 1 by omega⟩, ?_⟩
          simp [g, h.1, h.2]
        · refine ⟨((u, v), p), ⟨⟨huv, ha⟩, show p < 2 * k + 1 by omega⟩, ?_⟩
          simp [g, h.1, h.2, Sym2.eq_swap]
    · rintro ⟨⟨⟨u, v⟩, p⟩, ⟨⟨huv, ha⟩, hp⟩, rfl⟩
      have hp2 : p < 2 * k + 1 := hp
      refine ⟨s(⟨pos m k u v p, pos_lt m k u v p (by omega)⟩,
        ⟨pos m k u v (p + 1), pos_lt m k u v (p + 1) (by omega)⟩), ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeSet, hadj]
        exact ⟨u, v, huv, ha, p, by omega, Or.inl ⟨rfl, rfl⟩⟩
      · simp [g]
  have hinj : Set.InjOn g T := by
    rintro ⟨⟨u, v⟩, p⟩ ⟨_, hp⟩ ⟨⟨u', v'⟩, p'⟩ ⟨_, hp'⟩ h
    have hp2 : p < 2 * k + 1 := hp
    have hp2' : p' < 2 * k + 1 := hp'
    simp only [g, Sym2.eq_iff] at h
    suffices hs : u = u' ∧ v = v' ∧ p = p' by
      obtain ⟨rfl, rfl, rfl⟩ := hs
      rfl
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hA : 1 ≤ p ∧ p ≤ 2 * k
      · by_cases hA' : 1 ≤ p' ∧ p' ≤ 2 * k
        · exact mid_inj m k u v u' v' p p' hA hA' h1
        · exfalso
          have := small m k u' v' p' (by omega) hA'
          have := mid_ge m k u v p hA
          omega
      · have hB : 1 ≤ p + 1 ∧ p + 1 ≤ 2 * k := by omega
        by_cases hB' : 1 ≤ p' + 1 ∧ p' + 1 ≤ 2 * k
        · obtain ⟨a, b, c⟩ := mid_inj m k u v u' v' (p + 1) (p' + 1) hB hB' h2
          exact ⟨a, b, by omega⟩
        · exfalso
          have := small m k u' v' (p' + 1) (by omega) hB'
          have := mid_ge m k u v (p + 1) hB
          omega
    · exfalso
      by_cases hA : 1 ≤ p ∧ p ≤ 2 * k
      · by_cases hA' : 1 ≤ p' + 1 ∧ p' + 1 ≤ 2 * k
        · obtain ⟨rfl, rfl, hpp⟩ := mid_inj m k u v u' v' p (p' + 1) hA hA' h1
          by_cases hC : 1 ≤ p + 1 ∧ p + 1 ≤ 2 * k
          · by_cases hC' : 1 ≤ p' ∧ p' ≤ 2 * k
            · have := (mid_inj m k u v u v (p + 1) p' hC hC' h2).2.2
              omega
            · have := small m k u v p' (by omega) hC'
              have := mid_ge m k u v (p + 1) hC
              omega
          · have hC' : 1 ≤ p' ∧ p' ≤ 2 * k := by omega
            have := small m k u v (p + 1) (by omega) hC
            have := mid_ge m k u v p' hC'
            omega
        · have := small m k u' v' (p' + 1) (by omega) hA'
          have := mid_ge m k u v p hA
          omega
      · have hB : 1 ≤ p + 1 ∧ p + 1 ≤ 2 * k := by omega
        by_cases hA' : 1 ≤ p' + 1 ∧ p' + 1 ≤ 2 * k
        · have := small m k u v p (by omega) hA
          have := mid_ge m k u' v' (p' + 1) hA'
          omega
        · have hC' : 1 ≤ p' ∧ p' ≤ 2 * k := by omega
          have := (mid_inj m k u v u' v' (p + 1) p' hB hC' h2).2.2
          omega
  have hD : H.edgeSet.ncard = D.ncard := by
    have hE : H.edgeSet = (fun e : Fin m × Fin m => s(e.1, e.2)) '' D := by
      ext e
      induction e using Sym2.ind with
      | h a b =>
        simp only [SimpleGraph.mem_edgeSet, Set.mem_image]
        constructor
        · intro hab
          rcases lt_trichotomy a b with h | h | h
          · exact ⟨(a, b), ⟨h, hab⟩, rfl⟩
          · exact absurd h (H.ne_of_adj hab)
          · exact ⟨(b, a), ⟨h, hab.symm⟩, Sym2.eq_swap⟩
        · rintro ⟨⟨c, d⟩, ⟨hcd, hadj2⟩, he⟩
          rw [Sym2.eq_iff] at he
          rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hadj2
          · exact hadj2.symm
    rw [hE]
    refine Set.InjOn.ncard_image ?_
    rintro ⟨a, b⟩ ⟨hab, _⟩ ⟨c, d⟩ ⟨hcd, _⟩ h
    simp only [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (lt_asymm hab hcd).elim
  have hI : (Set.Iio (2 * k + 1)).ncard = 2 * k + 1 := by
    rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  rw [hD, ← Set.ncard_image_of_injective S.edgeSet (Sym2.map.injective Fin.val_injective),
    himg, hinj.ncard_image, Set.ncard_prod, hI, Nat.mul_comm]

end PEqualNP.Outside.Meta449

theorem PEqualNP.Outside.L_meta_449 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard :=
  PEqualNP.Outside.Meta449.main
