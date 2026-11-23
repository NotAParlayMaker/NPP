import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_454 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ u : Fin m, (S.neighborSet (Fin.castLE (Nat.le_add_right m (2 * k * (m * m))) u)).ncard = (H.neighborSet u).ncard := by
  intro m k H Q S hk hQ hS w
  have hbound : ∀ a b : Fin m, m + 2 * k * (a.val * m + b.val) + 2 * k ≤ m + 2 * k * (m * m) := by
    intro a b
    have ha := a.isLt
    have hb := b.isLt
    have h0 : (a.val + 1) * m ≤ m * m := Nat.mul_le_mul_right m ha
    have h1 : a.val * m + b.val + 1 ≤ m * m := by
      have h2 : (a.val + 1) * m = a.val * m + m := by ring
      omega
    have h3 : 2 * k * (a.val * m + b.val + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left (2 * k) h1
    have h4 : 2 * k * (a.val * m + b.val + 1) = 2 * k * (a.val * m + b.val) + 2 * k := by ring
    omega
  have hx : (Fin.castLE (Nat.le_add_right m (2 * k * (m * m))) w).val = w.val := rfl
  generalize Fin.castLE (Nat.le_add_right m (2 * k * (m * m))) w = x at hx
  let f : Fin m → Fin (m + 2 * k * (m * m)) := fun v =>
    if w < v then ⟨m + 2 * k * (w.val * m + v.val), by have := hbound w v; omega⟩
    else ⟨m + 2 * k * (v.val * m + w.val) + (2 * k - 1), by have := hbound v w; omega⟩
  have hf1 : ∀ v : Fin m, w < v → (f v).val = m + 2 * k * (w.val * m + v.val) := by
    intro v hv
    simp [f, hv]
  have hf2 : ∀ v : Fin m, ¬ w < v → (f v).val = m + 2 * k * (v.val * m + w.val) + (2 * k - 1) := by
    intro v hv
    simp [f, hv]
  have hset : S.neighborSet x = f '' H.neighborSet w := by
    ext y
    simp only [SimpleGraph.mem_neighborSet, Set.mem_image]
    rw [hS]
    constructor
    · rintro ⟨u, v, huv, hadj, p, hp, h⟩
      rcases h with ⟨h1, h2⟩ | ⟨h2, h1⟩
      · rw [hQ] at h1 h2
        have hu := u.isLt
        have hw := w.isLt
        rcases h1 with ⟨hp0, hxu⟩ | ⟨hp0, hxu⟩ | ⟨hp1, hp2, hxu⟩
        · have huw : u = w := Fin.ext (by omega)
          subst huw
          refine ⟨v, hadj, Fin.ext ?_⟩
          rw [hf1 v huv]
          rcases h2 with ⟨hq, hy⟩ | ⟨hq, hy⟩ | ⟨hq1, hq2, hy⟩
          · omega
          · omega
          · omega
        · omega
        · omega
      · rw [hQ] at h1 h2
        have hv := v.isLt
        have hw := w.isLt
        rcases h1 with ⟨hp0, hxu⟩ | ⟨hp0, hxu⟩ | ⟨hp1, hp2, hxu⟩
        · omega
        · have hvw : v = w := Fin.ext (by omega)
          subst hvw
          refine ⟨u, hadj.symm, Fin.ext ?_⟩
          rw [hf2 u (not_lt.mpr huv.le)]
          rcases h2 with ⟨hq, hy⟩ | ⟨hq, hy⟩ | ⟨hq1, hq2, hy⟩
          · omega
          · omega
          · omega
        · omega
    · rintro ⟨v, hv, rfl⟩
      by_cases h : w < v
      · refine ⟨w, v, h, hv, 0, by omega, Or.inl ⟨(hQ _ _ _ _).2 (Or.inl ⟨rfl, hx⟩), (hQ _ _ _ _).2 (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))⟩⟩
        rw [hf1 v h]
      · have hne : v ≠ w := fun e => (H.ne_of_adj hv) e.symm
        have hvw : v < w := lt_of_le_of_ne (not_lt.mp h) hne
        refine ⟨v, w, hvw, hv.symm, 2 * k, le_rfl, Or.inr ⟨(hQ _ _ _ _).2 (Or.inr (Or.inr ⟨by omega, le_rfl, ?_⟩)), (hQ _ _ _ _).2 (Or.inr (Or.inl ⟨rfl, hx⟩))⟩⟩
        rw [hf2 v h]
        omega
  have hdec : ∀ K B1 B2 r1 r2 : ℕ, r1 < K → r2 < K → K * B1 + r1 = K * B2 + r2 → B1 = B2 := by
    intro K B1 B2 r1 r2 h1 h2 h
    have hK : 0 < K := by omega
    have e1 : (K * B1 + r1) / K = B1 := by
      rw [Nat.mul_add_div hK, Nat.div_eq_of_lt h1]
      simp
    have e2 : (K * B2 + r2) / K = B2 := by
      rw [Nat.mul_add_div hK, Nat.div_eq_of_lt h2]
      simp
    rw [h] at e1
    omega
  have hinj : Function.Injective f := by
    intro a b hab
    have hv : (f a).val = (f b).val := by rw [hab]
    have ha := a.isLt
    have hb := b.isLt
    have hw := w.isLt
    by_cases h1 : w < a
    · by_cases h2 : w < b
      · rw [hf1 a h1, hf1 b h2] at hv
        have e := hdec (2 * k) (w.val * m + a.val) (w.val * m + b.val) 0 0 (by omega) (by omega) (by omega)
        exact Fin.ext (by omega)
      · rw [hf1 a h1, hf2 b h2] at hv
        have e := hdec (2 * k) (w.val * m + a.val) (b.val * m + w.val) 0 (2 * k - 1) (by omega) (by omega) (by omega)
        have e' := hdec m w.val b.val a.val w.val ha hw (by rw [Nat.mul_comm m w.val, Nat.mul_comm m b.val]; exact e)
        have h3 : w.val < a.val := h1
        have h4 : ¬ w.val < b.val := h2
        rw [e'] at e
        exact Fin.ext (by omega)
    · by_cases h2 : w < b
      · rw [hf2 a h1, hf1 b h2] at hv
        have e := hdec (2 * k) (a.val * m + w.val) (w.val * m + b.val) (2 * k - 1) 0 (by omega) (by omega) (by omega)
        have e' := hdec m a.val w.val w.val b.val hw hb (by rw [Nat.mul_comm m w.val, Nat.mul_comm m a.val]; exact e)
        rw [e'] at e
        exact Fin.ext (by omega)
      · rw [hf2 a h1, hf2 b h2] at hv
        have e := hdec (2 * k) (a.val * m + w.val) (b.val * m + w.val) (2 * k - 1) (2 * k - 1) (by omega) (by omega) (by omega)
        have e' := hdec m a.val b.val w.val w.val hw hw (by rw [Nat.mul_comm m a.val, Nat.mul_comm m b.val]; exact e)
        exact Fin.ext e'
  rw [hset]
  exact Set.ncard_image_of_injective _ hinj
