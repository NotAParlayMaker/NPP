import Mathlib
import PEqualNP.Defs

namespace Gap298


theorem aux (k N : ℕ) (Gh : SimpleGraph (Fin N)) (pos : Fin N → ℕ) (hk : 1 ≤ k)
    (h1 : ∀ u v : Fin N, Gh.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0)
    (h2 : ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, Gh.Adj v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) :
    ∀ (L : ℕ) (u v : Fin N) (w : ℕ → Fin N), pos u = 0 → pos v = 0 → u ≠ v → w 0 = u → w L = v →
      (∀ i : ℕ, i < L → Gh.Adj (w i) (w (i + 1))) → 2 * k + 1 ≤ L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro u v w hu hv huv h0 hL hadj
  by_contra hlt
  push_neg at hlt
  have hint : ∀ j, 0 < j → j < L → pos (w j) ≠ 0 := by
    intro j hj0 hjL hp
    by_cases he : w j = u
    · have := ih (L - j) (by omega) u v (fun i => w (i + j)) hu hv huv (by simpa using he)
        (by show w (L - j + j) = v; rw [Nat.sub_add_cancel hjL.le]; exact hL)
        (fun i hi => by
          have := hadj (i + j) (by omega)
          rwa [show i + j + 1 = i + 1 + j by omega] at this)
      omega
    · have := ih j hjL u (w j) w hu hp (Ne.symm he) h0 rfl (fun i hi => hadj i (by omega))
      omega
  have hnb : ∀ j, j + 2 ≤ L → w (j + 2) ≠ w j := by
    intro j hj he
    have := ih (L - 2) (by omega) u v (fun i => if i ≤ j then w i else w (i + 2)) hu hv huv
      (by simp [h0])
      (by
        show (if L - 2 ≤ j then w (L - 2) else w (L - 2 + 2)) = v
        split_ifs with hc
        · have : L - 2 = j := by omega
          rw [this, ← he, ← hL]; congr 1; omega
        · rw [← hL]; congr 1; omega)
      (fun i hi => by
        show Gh.Adj (if i ≤ j then w i else w (i + 2)) (if i + 1 ≤ j then w (i + 1) else w (i + 1 + 2))
        by_cases c1 : i + 1 ≤ j
        · rw [if_pos (by omega), if_pos c1]; exact hadj i (by omega)
        · by_cases c2 : i ≤ j
          · have hij : i = j := by omega
            subst hij
            rw [if_pos c2, if_neg c1, ← he]
            exact hadj (i + 2) (by omega)
          · rw [if_neg c2, if_neg c1]
            have := hadj (i + 2) (by omega)
            rwa [show i + 2 + 1 = i + 1 + 2 by omega] at this)
    omega
  have hL1 : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; exact absurd (h0.symm.trans hL) huv
    · exact h
  have hadj0 := hadj 0 (by omega)
  have hw1 : pos (w 1) ≠ 0 := by
    rcases h1 _ _ hadj0 with h | h
    · rw [h0] at h; exact absurd hu h
    · exact h
  have hpL : pos (w L) = 0 := by rw [hL]; exact hv
  have hp0 : pos (w 0) = 0 := by rw [h0]; exact hu
  obtain ⟨hle, a, b, hab, ha, hb⟩ := h2 (w 1) hw1
  rcases (hab (w 0)).1 hadj0.symm with h | h
  · -- upward
    have hp1 : pos (w 1) = 1 := by rw [← h] at ha; omega
    have claim : ∀ j, j + 1 ≤ L → pos (w j) = j ∧ pos (w (j + 1)) = j + 1 := by
      intro j
      induction j with
      | zero => intro _; exact ⟨hp0, hp1⟩
      | succ j ihj =>
        intro hj
        obtain ⟨e1, e2⟩ := ihj (by omega)
        refine ⟨e2, ?_⟩
        obtain ⟨_, a', b', hab', ha', hb'⟩ := h2 (w (j + 1)) (by omega)
        have hmod : (pos (w (j + 1)) + 1) % (2 * k + 1) = j + 2 := by
          rw [e2]; exact Nat.mod_eq_of_lt (by omega)
        rw [hmod] at hb'
        have hja : w j = a' := by
          rcases (hab' (w j)).1 (hadj j (by omega)).symm with h | h
          · exact h
          · rw [h] at e1; omega
        rcases (hab' (w (j + 1 + 1))).1 (hadj (j + 1) (by omega)) with h | h
        · exact absurd (h.trans hja.symm) (hnb j (by omega))
        · rw [h]; exact hb'
    have := (claim (L - 1) (by omega)).2
    rw [Nat.sub_add_cancel hL1] at this
    omega
  · -- downward
    have hp1 : pos (w 1) = 2 * k := by
      by_contra hne
      rw [← h, hp0, Nat.mod_eq_of_lt (by omega)] at hb
      omega
    have claim : ∀ j, j + 1 ≤ L → pos (w (j + 1)) = 2 * k - j ∧ pos (w j) + 1 ≠ 2 * k - j := by
      intro j
      induction j with
      | zero => intro _; exact ⟨hp1, by rw [hp0]; omega⟩
      | succ j ihj =>
        intro hj
        obtain ⟨e1, e2⟩ := ihj (by omega)
        obtain ⟨_, a', b', hab', ha', hb'⟩ := h2 (w (j + 1)) (by omega)
        have hjb : w j = b' := by
          rcases (hab' (w j)).1 (hadj j (by omega)).symm with h | h
          · rw [h] at e2; omega
          · exact h
        refine ⟨?_, by omega⟩
        rcases (hab' (w (j + 1 + 1))).1 (hadj (j + 1) (by omega)) with h | h
        · rw [h]; omega
        · exact absurd (h.trans hjb.symm) (hnb j (by omega))
    have := (claim (L - 1) (by omega)).1
    rw [Nat.sub_add_cancel hL1] at this
    omega


theorem ar1 (K a a' p p' : ℕ) (hp : 1 ≤ p) (hp2 : p ≤ K) (hp' : 1 ≤ p') (hp2' : p' ≤ K)
    (h : K * a + p = K * a' + p') : a = a' ∧ p = p' := by
  rcases lt_trichotomy a a' with h1 | h1 | h1
  · have h2 : K * (a + 1) ≤ K * a' := Nat.mul_le_mul_left _ h1
    rw [Nat.mul_succ] at h2; omega
  · subst h1; exact ⟨rfl, by omega⟩
  · have h2 : K * (a' + 1) ≤ K * a := Nat.mul_le_mul_left _ h1
    rw [Nat.mul_succ] at h2; omega

theorem ar2 (K a a' p p' : ℕ) (hp2 : p < K) (hp2' : p' < K)
    (h : a * K + p = a' * K + p') : a = a' ∧ p = p' := by
  rcases lt_trichotomy a a' with h1 | h1 | h1
  · have h2 : (a + 1) * K ≤ a' * K := Nat.mul_le_mul_right _ h1
    rw [Nat.succ_mul] at h2; omega
  · subst h1; exact ⟨rfl, by omega⟩
  · have h2 : (a' + 1) * K ≤ a * K := Nat.mul_le_mul_right _ h1
    rw [Nat.succ_mul] at h2; omega

theorem bnd (m k u v : ℕ) (hu : u < m) (hv : v < m) :
    2 * k * (u * m + v) + 2 * k ≤ 2 * k * (m * m) := by
  have h2 : (u + 1) * m ≤ m * m := Nat.mul_le_mul_right _ hu
  rw [Nat.succ_mul] at h2
  have h3 : 2 * k * (u * m + v + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_succ] at h3; exact h3

def R (m k : ℕ) (H : SimpleGraph (Fin m)) (z : Fin (m + 2 * k * (m * m))) (q : ℕ) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ 1 ≤ q ∧ q ≤ 2 * k ∧
    z.val + 1 = m + 2 * k * (u.val * m + v.val) + q

theorem main : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hx hy hxy w
  classical
  have key : ∀ (u v u' v' : Fin m) (q q' : ℕ) (z : Fin (m + 2 * k * (m * m))), 1 ≤ q → q ≤ 2 * k →
      1 ≤ q' → q' ≤ 2 * k → z.val + 1 = m + 2 * k * (u.val * m + v.val) + q →
      z.val + 1 = m + 2 * k * (u'.val * m + v'.val) + q' → u = u' ∧ v = v' ∧ q = q' := by
    intro u v u' v' q q' z h1 h2 h3 h4 e1 e2
    obtain ⟨ea, eq⟩ := ar1 (2 * k) (u.val * m + v.val) (u'.val * m + v'.val) q q' h1 h2 h3 h4 (by omega)
    obtain ⟨eu, ev⟩ := ar2 m u.val u'.val v.val v'.val v.isLt v'.isLt ea
    exact ⟨Fin.ext eu, Fin.ext ev, eq⟩
  have Runiq : ∀ z q q', R m k H z q → R m k H z q' → q = q' := by
    rintro z q q' ⟨u, v, -, -, h1, h2, e1⟩ ⟨u', v', -, -, h3, h4, e2⟩
    exact (key u v u' v' q q' z h1 h2 h3 h4 e1 e2).2.2
  obtain ⟨pos, posR, Rpos⟩ : ∃ pos : Fin (m + 2 * k * (m * m)) → ℕ,
      (∀ z q, R m k H z q → pos z = q) ∧ (∀ z, pos z ≠ 0 → R m k H z (pos z)) := by
    refine ⟨fun z => if h : ∃ q, R m k H z q then h.choose else 0, ?_, ?_⟩
    · intro z q hq
      have h : ∃ q, R m k H z q := ⟨q, hq⟩
      simp only [dif_pos h]
      exact Runiq z _ _ h.choose_spec hq
    · intro z hz
      by_cases h : ∃ q, R m k H z q
      · simp only [dif_pos h]; exact h.choose_spec
      · simp only [dif_neg h] at hz; exact absurd rfl hz
  have poslt : ∀ z : Fin (m + 2 * k * (m * m)), z.val < m → pos z = 0 := by
    intro z hz
    by_contra hne
    obtain ⟨u, v, -, -, h1, h2, e1⟩ := Rpos z hne
    omega
  have Qpos : ∀ (u v : Fin m), u < v → H.Adj u v → ∀ q z, 1 ≤ q → q ≤ 2 * k → Q u v q z → pos z = q := by
    intro u v huv hH q z h1 h2 hq
    rcases (hQ u v q z).1 hq with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e1, e2, e3⟩
    · omega
    · omega
    · exact posR z q ⟨u, v, huv, hH, e1, e2, e3⟩
  have ex : ∀ (u v : Fin m) (q : ℕ), q ≤ 2 * k + 1 → ∃ z, Q u v q z := by
    intro u v q hq
    have hb := bnd m k u.val v.val u.isLt v.isLt
    by_cases h0 : q = 0
    · exact ⟨⟨u.val, by have := u.isLt; omega⟩, (hQ _ _ _ _).2 (Or.inl ⟨h0, rfl⟩)⟩
    · by_cases h1 : q = 2 * k + 1
      · exact ⟨⟨v.val, by have := v.isLt; omega⟩, (hQ _ _ _ _).2 (Or.inr (Or.inl ⟨h1, rfl⟩))⟩
      · exact ⟨⟨m + 2 * k * (u.val * m + v.val) + q - 1, by omega⟩,
          (hQ _ _ _ _).2 (Or.inr (Or.inr ⟨by omega, by omega, by show _ - 1 + 1 = _; omega⟩))⟩
  have Quniq : ∀ (u v : Fin m) (q : ℕ) (z z' : Fin (m + 2 * k * (m * m))), Q u v q z → Q u v q z' → z = z' := by
    intro u v q z z' h1 h2
    apply Fin.ext
    rcases (hQ _ _ _ _).1 h1 with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b, c⟩ <;>
      rcases (hQ _ _ _ _).1 h2 with ⟨a', b'⟩ | ⟨a', b'⟩ | ⟨a', b', c'⟩ <;> omega
  have h1 : ∀ a b : Fin (m + 2 * k * (m * m)), S.Adj a b → pos a ≠ 0 ∨ pos b ≠ 0 := by
    intro a b hadj
    obtain ⟨u, v, huv, hH, p, hp, hc⟩ := (hS a b).1 hadj
    by_cases h0 : p = 0
    · rcases hc with ⟨_, c2⟩ | ⟨_, c2⟩
      · right; have := Qpos u v huv hH _ _ (by omega) (by omega) c2; omega
      · left; have := Qpos u v huv hH _ _ (by omega) (by omega) c2; omega
    · rcases hc with ⟨c2, _⟩ | ⟨c2, _⟩
      · left; have := Qpos u v huv hH _ _ (by omega) (by omega) c2; omega
      · right; have := Qpos u v huv hH _ _ (by omega) (by omega) c2; omega
  have h2 : ∀ z : Fin (m + 2 * k * (m * m)), pos z ≠ 0 → pos z ≤ 2 * k ∧ ∃ a b : Fin (m + 2 * k * (m * m)),
      (∀ t, S.Adj z t ↔ t = a ∨ t = b) ∧ pos a + 1 = pos z ∧ pos b = (pos z + 1) % (2 * k + 1) := by
    intro z hz
    obtain ⟨u, v, huv, hH, hq1, hq2, hT⟩ := Rpos z hz
    have Qz : Q u v (pos z) z := (hQ _ _ _ _).2 (Or.inr (Or.inr ⟨hq1, hq2, hT⟩))
    refine ⟨hq2, ?_⟩
    obtain ⟨a, ha⟩ := ex u v (pos z - 1) (by omega)
    obtain ⟨b, hb⟩ := ex u v (pos z + 1) (by omega)
    refine ⟨a, b, ?_, ?_, ?_⟩
    · intro t; constructor
      · intro hadj
        obtain ⟨u', v', huv', hH', p, hp, hc⟩ := (hS z t).1 hadj
        rcases hc with ⟨c1, c2⟩ | ⟨c1, c2⟩
        · rcases (hQ _ _ _ _).1 c1 with ⟨_, e⟩ | ⟨_, e⟩ | ⟨e1, e2, e3⟩
          · exfalso; have := u'.isLt; omega
          · exfalso; have := v'.isLt; omega
          · obtain ⟨eu, ev, e⟩ := key u v u' v' (pos z) p z hq1 hq2 e1 e2 hT e3
            subst eu; subst ev; subst e
            right; exact Quniq _ _ _ _ _ c2 hb
        · rcases (hQ _ _ _ _).1 c2 with ⟨_, e⟩ | ⟨_, e⟩ | ⟨e1, e2, e3⟩
          · exfalso; have := u'.isLt; omega
          · exfalso; have := v'.isLt; omega
          · obtain ⟨eu, ev, e⟩ := key u v u' v' (pos z) (p + 1) z hq1 hq2 e1 e2 hT e3
            subst eu; subst ev
            have e' : p = pos z - 1 := by omega
            subst e'
            left; exact Quniq _ _ _ _ _ c1 ha
      · intro h
        rcases h with h | h
        · rw [h]
          exact (hS _ _).2 ⟨u, v, huv, hH, pos z - 1, by omega,
            Or.inr ⟨ha, by rw [show pos z - 1 + 1 = pos z by omega]; exact Qz⟩⟩
        · rw [h]
          exact (hS _ _).2 ⟨u, v, huv, hH, pos z, hq2, Or.inl ⟨Qz, hb⟩⟩
    · rcases (hQ _ _ _ _).1 ha with ⟨e, e2⟩ | ⟨e, _⟩ | ⟨e1, e2, e3⟩
      · have := poslt a (by have := u.isLt; omega); omega
      · omega
      · have := posR a _ ⟨u, v, huv, hH, e1, e2, e3⟩; omega
    · rcases (hQ _ _ _ _).1 hb with ⟨e, _⟩ | ⟨e, e2⟩ | ⟨e1, e2, e3⟩
      · omega
      · have := poslt b (by have := v.isLt; omega)
        rw [this, e, Nat.mod_self]
      · have := posR b _ ⟨u, v, huv, hH, e1, e2, e3⟩
        rw [this, Nat.mod_eq_of_lt (by omega)]
  exact aux k _ S pos hk h1 h2 w.length x y (fun i => w.getVert i) (poslt x hx) (poslt y hy) hxy
    (by simp) (by simp) (fun i hi => w.adj_getVert_succ hi)

end Gap298

theorem PEqualNP.Outside.L_meta_298 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  exact Gap298.main
