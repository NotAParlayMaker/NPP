import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_281_aux

open PEqualNP.Library.Subdivision

theorem div_inj {d i i' s s' : ℕ} (hs : s < d) (hs' : s' < d)
    (h : d * i + s = d * i' + s') : i = i' ∧ s = s' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have : d * (i + 1) ≤ d * i' := Nat.mul_le_mul_left _ hlt
    rw [Nat.mul_succ] at this
    omega
  · subst heq; omega
  · have : d * (i' + 1) ≤ d * i := Nat.mul_le_mul_left _ hgt
    rw [Nat.mul_succ] at this
    omega

theorem thr_inj {m k : ℕ} {u v u' v' : Fin m} {i i' : ℕ} (hi : i < 2 * k) (hi' : i' < 2 * k)
    (h : m + 2 * k * (u.val * m + v.val) + i = m + 2 * k * (u'.val * m + v'.val) + i') :
    u = u' ∧ v = v' ∧ i = i' := by
  obtain ⟨h1, h2⟩ := div_inj (d := 2 * k) (i := u.val * m + v.val) (i' := u'.val * m + v'.val)
    hi hi' (by omega)
  have h1' : m * u.val + v.val = m * u'.val + v'.val := by
    rw [Nat.mul_comm m, Nat.mul_comm m]; exact h1
  obtain ⟨h3, h4⟩ := div_inj (d := m) v.2 v'.2 h1'
  exact ⟨Fin.ext h3, Fin.ext h4, h2⟩

theorem slot_lt {m : ℕ} (u v : Fin m) : u.val * m + v.val + 1 ≤ m * m := by
  have : (u.val + 1) * m ≤ m * m := Nat.mul_le_mul_right _ u.2
  rw [Nat.succ_mul] at this
  have := v.2
  omega

theorem thr_lt {m k : ℕ} (u v : Fin m) {i : ℕ} (hi : i < 2 * k) :
    m + 2 * k * (u.val * m + v.val) + i < nS m k := by
  have : 2 * k * (u.val * m + v.val + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ (slot_lt u v)
  rw [Nat.mul_succ] at this
  unfold nS
  rw [Nat.mul_assoc (2 * k) m m]
  omega

theorem inner_adj_iff {m k : ℕ} (H : SimpleGraph (Fin m)) (u v : Fin m) (i : Fin (2 * k))
    (x y : Fin (nS m k)) (hx : x.val = m + 2 * k * (u.val * m + v.val) + i.val) :
    (subdiv k H).Adj x y ↔ (u < v ∧ H.Adj u v) ∧
      ((y.val = if i.val = 0 then u.val else x.val - 1) ∨
       (y.val = if i.val + 1 = 2 * k then v.val else x.val + 1)) := by
  have hu := u.2
  have hv := v.2
  have hi := i.2
  constructor
  · rintro ⟨hne, ⟨u', v', huv', hadj', p, h1, h2⟩ | ⟨u', v', huv', hadj', p, h1, h2⟩⟩
    · have hu' := u'.2
      have hp := p.2
      by_cases hp0 : p.val = 0
      · rw [if_pos hp0] at h1; omega
      rw [if_neg hp0] at h1
      obtain ⟨rfl, rfl, hip⟩ := thr_inj (u := u) (v := v) (u' := u') (v' := v')
        (i := i.val) (i' := p.val - 1) hi (by omega) (by omega)
      refine ⟨⟨huv', hadj'⟩, Or.inr ?_⟩
      by_cases hp2 : p.val = 2 * k
      · rw [if_pos hp2] at h2; rw [if_pos (by omega)]; exact h2
      · rw [if_neg hp2] at h2; rw [if_neg (by omega)]; omega
    · have hv' := v'.2
      have hp := p.2
      by_cases hp2 : p.val = 2 * k
      · rw [if_pos hp2] at h2; omega
      rw [if_neg hp2] at h2
      obtain ⟨rfl, rfl, hip⟩ := thr_inj (u := u) (v := v) (u' := u') (v' := v')
        (i := i.val) (i' := p.val) hi (by omega) (by omega)
      refine ⟨⟨huv', hadj'⟩, Or.inl ?_⟩
      by_cases hp0 : p.val = 0
      · rw [if_pos hp0] at h1; rw [if_pos (by omega)]; exact h1
      · rw [if_neg hp0] at h1; rw [if_neg (by omega)]; omega
  · rintro ⟨⟨huv, hadj⟩, h | h⟩
    · refine ⟨?_, Or.inr ⟨u, v, huv, hadj, ⟨i.val, by omega⟩, ?_, ?_⟩⟩
      · intro hxy; subst hxy; split_ifs at h <;> omega
      · simp only
        split_ifs at h ⊢ <;> omega
      · simp only
        rw [if_neg (by omega)]; exact hx
    · refine ⟨?_, Or.inl ⟨u, v, huv, hadj, ⟨i.val + 1, by omega⟩, ?_, ?_⟩⟩
      · intro hxy; subst hxy; split_ifs at h <;> omega
      · simp only
        rw [if_neg (by omega)]; omega
      · simp only
        split_ifs at h ⊢ <;> omega

def FRel {m : ℕ} (k : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (m + 2 * k * m * m)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
    x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
    ((i.val = 0 ∧ y.val = u.val) ∨
      (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
      (i.val + 1 = 2 * k ∧ y.val = v.val))

theorem frel_to {m k : ℕ} {H : SimpleGraph (Fin m)} {x y : Fin (nS m k)} (h : FRel k H x y) :
    SubRel k H x y ∨ SubRel k H y x := by
  obtain ⟨u, v, huv, hadj, i, hx, h⟩ := h
  have hi := i.2
  rcases h with ⟨hi0, hy⟩ | ⟨hlt, hy⟩ | ⟨heq, hy⟩
  · refine Or.inr ⟨u, v, huv, hadj, ⟨0, by omega⟩, ?_, ?_⟩
    · show y.val = (if (0 : ℕ) = 0 then u.val else _)
      rw [if_pos rfl]; exact hy
    · show x.val = (if (0 : ℕ) = 2 * k then v.val else m + 2 * k * (u.val * m + v.val) + 0)
      rw [if_neg (by omega)]; omega
  · refine Or.inl ⟨u, v, huv, hadj, ⟨i.val + 1, by omega⟩, ?_, ?_⟩
    · show x.val = (if i.val + 1 = 0 then u.val else
        m + 2 * k * (u.val * m + v.val) + (i.val + 1) - 1)
      rw [if_neg (by omega)]; omega
    · show y.val = (if i.val + 1 = 2 * k then v.val else
        m + 2 * k * (u.val * m + v.val) + (i.val + 1))
      rw [if_neg (by omega)]; omega
  · refine Or.inl ⟨u, v, huv, hadj, ⟨i.val + 1, by omega⟩, ?_, ?_⟩
    · show x.val = (if i.val + 1 = 0 then u.val else
        m + 2 * k * (u.val * m + v.val) + (i.val + 1) - 1)
      rw [if_neg (by omega)]; omega
    · show y.val = (if i.val + 1 = 2 * k then v.val else
        m + 2 * k * (u.val * m + v.val) + (i.val + 1))
      rw [if_pos heq]; exact hy

theorem subrel_to {m k : ℕ} {H : SimpleGraph (Fin m)} (hk : 1 ≤ k) {x y : Fin (nS m k)}
    (h : SubRel k H x y) : FRel k H x y ∨ FRel k H y x := by
  obtain ⟨u, v, huv, hadj, p, hx, hy⟩ := h
  have hp := p.2
  by_cases hp0 : p.val = 0
  · rw [if_pos hp0] at hx
    rw [if_neg (by omega)] at hy
    refine Or.inr ⟨u, v, huv, hadj, ⟨0, by omega⟩, ?_, Or.inl ⟨rfl, hx⟩⟩
    show y.val = m + 2 * k * (u.val * m + v.val) + 0
    omega
  · rw [if_neg hp0] at hx
    refine Or.inl ⟨u, v, huv, hadj, ⟨p.val - 1, by omega⟩, ?_, ?_⟩
    · show x.val = m + 2 * k * (u.val * m + v.val) + (p.val - 1)
      omega
    · by_cases hp2 : p.val = 2 * k
      · rw [if_pos hp2] at hy
        exact Or.inr (Or.inr ⟨by show p.val - 1 + 1 = 2 * k; omega, hy⟩)
      · rw [if_neg hp2] at hy
        exact Or.inr (Or.inl ⟨by show p.val - 1 + 1 < 2 * k; omega,
          by show y.val = m + 2 * k * (u.val * m + v.val) + (p.val - 1) + 1; omega⟩)

theorem graph_eq {m k : ℕ} (H : SimpleGraph (Fin m)) (hk : 1 ≤ k) :
    SimpleGraph.fromRel (FRel k H) = subdiv k H := by
  ext x y
  show x ≠ y ∧ (FRel k H x y ∨ FRel k H y x) ↔ x ≠ y ∧ (SubRel k H x y ∨ SubRel k H y x)
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, frel_to h⟩
    · exact ⟨hne, (frel_to h).symm⟩
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, subrel_to hk h⟩
    · exact ⟨hne, (subrel_to hk h).symm⟩

theorem pos_eq {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (j : Fin (nS m k)) :
    (∑ u : Fin m, ∑ v : Fin m, ∑ i : Fin (2 * k),
      if u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val then i.val + 1 else 0)
      = pos k H j := by
  unfold pos
  split_ifs with h
  · obtain ⟨u0, v0, i0, huv, hadj, hj⟩ := h
    have hu : ∀ u : Fin m, u ≠ u0 → (∑ v : Fin m, ∑ i : Fin (2 * k),
        if u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val
        then i.val + 1 else 0) = 0 := by
      intro u hne
      refine Finset.sum_eq_zero (fun v _ => Finset.sum_eq_zero (fun i _ => if_neg ?_))
      rintro ⟨-, -, h'⟩
      exact hne (thr_inj i.2 i0.2 (h'.symm.trans hj)).1
    have hv : ∀ v : Fin m, v ≠ v0 → (∑ i : Fin (2 * k),
        if u0 < v ∧ H.Adj u0 v ∧ j.val = m + 2 * k * (u0.val * m + v.val) + i.val
        then i.val + 1 else 0) = 0 := by
      intro v hne
      refine Finset.sum_eq_zero (fun i _ => if_neg ?_)
      rintro ⟨-, -, h'⟩
      exact hne (thr_inj i.2 i0.2 (h'.symm.trans hj)).2.1
    have hi : ∀ i : Fin (2 * k), i ≠ i0 →
        (if u0 < v0 ∧ H.Adj u0 v0 ∧ j.val = m + 2 * k * (u0.val * m + v0.val) + i.val
          then i.val + 1 else 0) = 0 := by
      intro i hne
      refine if_neg ?_
      rintro ⟨-, -, h'⟩
      exact hne (Fin.ext (thr_inj i.2 i0.2 (h'.symm.trans hj)).2.2)
    rw [Finset.sum_eq_single u0 (fun u _ hne => hu u hne) (fun h => absurd (Finset.mem_univ _) h),
      Finset.sum_eq_single v0 (fun v _ hne => hv v hne) (fun h => absurd (Finset.mem_univ _) h),
      Finset.sum_eq_single i0 (fun i _ hne => hi i hne) (fun h => absurd (Finset.mem_univ _) h),
      if_pos ⟨huv, hadj, hj⟩]
    have e : j.val - m = i0.val + 2 * k * (u0.val * m + v0.val) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i0.2]
  · refine Finset.sum_eq_zero (fun u _ => Finset.sum_eq_zero (fun v _ =>
      Finset.sum_eq_zero (fun i _ => if_neg ?_)))
    rintro ⟨huv, hadj, hj⟩
    exact h ⟨u, v, i, huv, hadj, hj⟩

theorem pos_thr {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] {u v : Fin m}
    (huv : u < v) (hadj : H.Adj u v) {i : ℕ} (hi : i < 2 * k) (j : Fin (nS m k))
    (hj : j.val = m + 2 * k * (u.val * m + v.val) + i) : pos k H j = i + 1 := by
  unfold pos
  rw [if_pos ⟨u, v, ⟨i, hi⟩, huv, hadj, hj⟩]
  have e : j.val - m = i + 2 * k * (u.val * m + v.val) := by omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]

theorem pos_hub {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (x : Fin (nS m k))
    (hx : x.val < m) : pos k H x = 0 := by
  unfold pos
  rw [if_neg]
  rintro ⟨u, v, i, -, -, h⟩
  omega

theorem pos_ne_of_sub {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (hk : 1 ≤ k)
    {x y : Fin (nS m k)} (h : SubRel k H x y) : pos k H x ≠ 0 ∨ pos k H y ≠ 0 := by
  obtain ⟨u, v, huv, hadj, p, hx, hy⟩ := h
  have hp := p.2
  by_cases hp0 : p.val = 0
  · right
    rw [if_neg (by omega)] at hy
    have h1 := pos_thr H huv hadj (i := 0) (by omega) y (by omega)
    rw [h1]
    omega
  · left
    rw [if_neg hp0] at hx
    have h1 := pos_thr H huv hadj (i := p.val - 1) (by omega) x (by omega)
    rw [h1]
    omega

theorem lab {m k : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (hk : 1 ≤ k) :
    (∀ x y : Fin (nS m k), (subdiv k H).Adj x y → pos k H x ≠ 0 ∨ pos k H y ≠ 0) ∧
    ∀ v : Fin (nS m k), pos k H v ≠ 0 → pos k H v ≤ 2 * k ∧ ∃ a b : Fin (nS m k),
      (∀ w : Fin (nS m k), (subdiv k H).Adj v w ↔ w = a ∨ w = b) ∧
      pos k H a + 1 = pos k H v ∧ pos k H b = (pos k H v + 1) % (2 * k + 1) := by
  constructor
  · rintro x y ⟨hne, h | h⟩
    · exact pos_ne_of_sub H hk h
    · exact (pos_ne_of_sub H hk h).symm
  · intro x hx
    have hon : OnThr k H x := by
      by_contra h
      apply hx
      unfold pos
      rw [if_neg h]
    obtain ⟨u, v, i, huv, hadj, hxv⟩ := hon
    have hpx := pos_thr H huv hadj i.2 x hxv
    have hu := u.2
    have hv := v.2
    have hi := i.2
    have hN := x.2
    have h0 : m ≤ nS m k := by unfold nS; omega
    have ha_ex : ∃ a : Fin (nS m k), a.val = (if i.val = 0 then u.val else x.val - 1) :=
      ⟨⟨if i.val = 0 then u.val else x.val - 1, by split_ifs <;> omega⟩, rfl⟩
    have hb_ex : ∃ b : Fin (nS m k), b.val = (if i.val + 1 = 2 * k then v.val else x.val + 1) :=
      ⟨⟨if i.val + 1 = 2 * k then v.val else x.val + 1, by
        split_ifs with h
        · omega
        · have := thr_lt (k := k) u v (i := i.val + 1) (by omega)
          omega⟩, rfl⟩
    obtain ⟨a, ha⟩ := ha_ex
    obtain ⟨b, hb⟩ := hb_ex
    refine ⟨by rw [hpx]; omega, a, b, ?_, ?_, ?_⟩
    · intro w
      rw [inner_adj_iff H u v i x w hxv, Fin.ext_iff, Fin.ext_iff, ha, hb]
      simp only [huv, hadj, and_self, true_and]
    · rw [hpx]
      by_cases hi0 : i.val = 0
      · rw [if_pos hi0] at ha
        have h1 : pos k H a = 0 := pos_hub H a (by omega)
        omega
      · rw [if_neg hi0] at ha
        have h1 := pos_thr H huv hadj (i := i.val - 1) (by omega) a (by omega)
        omega
    · rw [hpx]
      by_cases hie : i.val + 1 = 2 * k
      · rw [if_pos hie] at hb
        have h1 : pos k H b = 0 := pos_hub H b (by omega)
        have h2 : i.val + 1 + 1 = 2 * k + 1 := by omega
        rw [h1, h2, Nat.mod_self]
      · rw [if_neg hie] at hb
        have h1 := pos_thr H huv hadj (i := i.val + 1) (by omega) b (by omega)
        rw [h1]
        exact (Nat.mod_eq_of_lt (by omega)).symm

end PEqualNP.Outside.L_meta_281_aux

theorem PEqualNP.Outside.L_meta_281 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ pos : Fin (m + 2 * k * m * m) → ℕ, (∀ j : Fin (m + 2 * k * m * m), pos j = ∑ u : Fin m, ∑ v : Fin m, ∑ i : Fin (2 * k), if u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val then i.val + 1 else 0) → (∀ u v : Fin (m + 2 * k * m * m), S.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin (m + 2 * k * m * m), pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin (m + 2 * k * m * m), (∀ w : Fin (m + 2 * k * m * m), S.Adj v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1) := by
  intro k m H _ hk S hS pos hpos
  have hS' : S = PEqualNP.Library.Subdivision.subdiv k H := by
    rw [hS]
    exact PEqualNP.Outside.L_meta_281_aux.graph_eq H hk
  have hp : pos = PEqualNP.Library.Subdivision.pos k H := by
    funext j
    exact (hpos j).trans (PEqualNP.Outside.L_meta_281_aux.pos_eq H j)
  subst hS'
  subst hp
  exact PEqualNP.Outside.L_meta_281_aux.lab H hk
