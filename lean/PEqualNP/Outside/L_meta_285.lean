import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

namespace L285

/-- The index of the `i`-th inner vertex of the path replacing the edge `u v`. -/
def enc (m k u v i : ℕ) : ℕ := m + 2 * k * (u * m + v) + i

theorem enc_ge (m k u v i : ℕ) : m ≤ enc m k u v i := by
  unfold enc; omega

theorem enc_lt (m k u v i : ℕ) (hu : u < m) (hv : v < m) (hi : i < 2 * k) :
    enc m k u v i < m + 2 * k * m * m := by
  unfold enc
  have h1 : u * m + v + 1 ≤ m * m := by
    calc u * m + v + 1 ≤ u * m + m := by omega
      _ = (u + 1) * m := by ring
      _ ≤ m * m := Nat.mul_le_mul_right m hu
  have h2 : 2 * k * (u * m + v) + i < 2 * k * (u * m + v + 1) := by
    have : 2 * k * (u * m + v + 1) = 2 * k * (u * m + v) + 2 * k := by ring
    omega
  have h3 : 2 * k * (u * m + v + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ h1
  have h4 : 2 * k * (m * m) = 2 * k * m * m := by ring
  omega

theorem enc_inj (m k : ℕ) (hk : 1 ≤ k) {u v i u' v' i' : ℕ} (hv : v < m) (hv' : v' < m)
    (hi : i < 2 * k) (hi' : i' < 2 * k) (h : enc m k u v i = enc m k u' v' i') :
    u = u' ∧ v = v' ∧ i = i' := by
  unfold enc at h
  have h0 : 2 * k * (u * m + v) + i = 2 * k * (u' * m + v') + i' := by omega
  have hk2 : 0 < 2 * k := by omega
  have hi_eq : i = i' := by
    have e1 := congrArg (· % (2 * k)) h0
    simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at e1
    exact e1
  subst hi_eq
  have hq : u * m + v = u' * m + v' := by
    have e1 := congrArg (· / (2 * k)) h0
    simp only [Nat.mul_add_div hk2, Nat.div_eq_of_lt hi, Nat.add_zero] at e1
    exact e1
  have hm : 0 < m := by omega
  have hv_eq : v = v' := by
    have e1 := congrArg (· % m) hq
    simp only [Nat.mul_comm u m, Nat.mul_comm u' m, Nat.mul_add_mod, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hv'] at e1
    exact e1
  subst hv_eq
  have hu_eq : u = u' := by
    have e1 := congrArg (· / m) hq
    simp only [Nat.mul_comm u m, Nat.mul_comm u' m, Nat.mul_add_div hm, Nat.div_eq_of_lt hv, Nat.add_zero] at e1
    exact e1
  exact ⟨hu_eq, rfl, rfl⟩

/-- The relation that defines the subdivision, exactly as in the statement. -/
def Rel (m k : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (m + 2 * k * m * m)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
    ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
      (i.val + 1 = 2 * k ∧ y.val = v.val))

/-- The next vertex along the path from `u` to `v`, after the `i`-th inner vertex. -/
def nxt (m k u v i : ℕ) : ℕ := if i + 1 < 2 * k then enc m k u v (i + 1) else v

/-- The previous vertex along the path from `u` to `v`, before the `i`-th inner vertex. -/
def prv (m k u v i : ℕ) : ℕ := if i = 0 then u else enc m k u v (i - 1)

theorem nbr_of_internal (m k : ℕ) (H : SimpleGraph (Fin m)) (hk : 1 ≤ k)
    (x y : Fin (m + 2 * k * m * m)) (u v i : ℕ) (huv : u < v) (hv : v < m) (hi : i < 2 * k)
    (hx : x.val = enc m k u v i) (h : Rel m k H x y ∨ Rel m k H y x) :
    y.val = nxt m k u v i ∨ y.val = prv m k u v i := by
  rcases h with ⟨u', v', huv', _, i', hx', hy⟩ | ⟨u', v', huv', _, i', hy', hx'⟩
  · have hx'' : enc m k u v i = enc m k u'.val v'.val i'.val := by rw [← hx, hx']; rfl
    obtain ⟨rfl, rfl, rfl⟩ := enc_inj m k hk hv v'.isLt hi i'.isLt hx''
    rcases hy with ⟨h0, hy⟩ | ⟨hlt, hy⟩ | ⟨heq, hy⟩
    · right; simp [prv, h0, hy]
    · left; simp only [nxt, hlt, ite_true, enc]; omega
    · left; simp only [nxt, show ¬ (i'.val + 1 < 2 * k) by omega, ite_false]; exact hy
  · rcases hx' with ⟨h0, hx'⟩ | ⟨hlt, hx'⟩ | ⟨heq, hx'⟩
    · exfalso; have := enc_ge m k u v i; omega
    · have hx'' : enc m k u v i = enc m k u'.val v'.val (i'.val + 1) := by rw [← hx, hx']; rfl
      obtain ⟨rfl, rfl, hi'⟩ := enc_inj m k hk hv v'.isLt hi hlt hx''
      right
      simp only [prv, show ¬ (i = 0) by omega, ite_false, hy']
      congr 1 <;> omega
    · exfalso; have := enc_ge m k u v i; omega

theorem nbr_of_orig (m k : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (m + 2 * k * m * m)) (hx : x.val < m)
    (h : Rel m k H x y ∨ Rel m k H y x) :
    ∃ (u v : Fin m) (i : ℕ), u < v ∧ H.Adj u v ∧ i < 2 * k ∧ y.val = enc m k u.val v.val i ∧
      ((i = 0 ∧ x.val = u.val) ∨ (i + 1 = 2 * k ∧ x.val = v.val)) := by
  rcases h with ⟨u', v', _, _, i', hx', _⟩ | ⟨u', v', huv', hH, i', hy', hx'⟩
  · exfalso; rw [hx'] at hx; omega
  · refine ⟨u', v', i'.val, huv', hH, i'.isLt, hy', ?_⟩
    rcases hx' with ⟨h0, hx'⟩ | ⟨_, hx'⟩ | ⟨heq, hx'⟩
    · exact Or.inl ⟨h0, hx'⟩
    · exfalso; rw [hx'] at hx; omega
    · exact Or.inr ⟨heq, hx'⟩

theorem rel_src_ge (m k : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (m + 2 * k * m * m)) (h : Rel m k H x y) :
    m ≤ x.val := by
  obtain ⟨u, v, _, _, i, hx, _⟩ := h
  rw [hx]; omega

/-- An internal vertex with a neighbour carries path data. -/
theorem internal_data (m k : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (m + 2 * k * m * m)) (hx : m ≤ x.val)
    (h : Rel m k H x y ∨ Rel m k H y x) :
    ∃ (u v : Fin m) (i : ℕ), u < v ∧ H.Adj u v ∧ i < 2 * k ∧ x.val = enc m k u.val v.val i := by
  rcases h with ⟨u, v, huv, hH, i, hx', _⟩ | ⟨u, v, huv, hH, i, _, hx'⟩
  · exact ⟨u, v, i.val, huv, hH, i.isLt, hx'⟩
  · rcases hx' with ⟨_, hx'⟩ | ⟨hlt, hx'⟩ | ⟨_, hx'⟩
    · exfalso; rw [hx'] at hx; omega
    · exact ⟨u, v, i.val + 1, huv, hH, hlt, by rw [hx']; rfl⟩
    · exfalso; rw [hx'] at hx; omega

section Cycle

variable {m k : ℕ} {H : SimpleGraph (Fin m)} {L : ℕ} {d : ℕ → Fin (m + 2 * k * m * m)}

theorem ne_two (hL : 3 ≤ L) (hinj : ∀ i j, d i = d j → i % L = j % L) (t : ℕ) : d t ≠ d (t + 2) := by
  intro h
  have h1 : t ≡ t + 2 [MOD L] := hinj _ _ h
  have h2 : 0 ≡ 2 [MOD L] := Nat.ModEq.add_left_cancel' t (by simpa using h1)
  have h3 : L ∣ 2 := (Nat.modEq_zero_iff_dvd.1 h2.symm)
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem forward (hk : 1 ≤ k) (hL : 3 ≤ L)
    (hadj : ∀ t, Rel m k H (d t) (d (t + 1)) ∨ Rel m k H (d (t + 1)) (d t))
    (hinj : ∀ i j, d i = d j → i % L = j % L)
    (u v : Fin m) (huv : u < v) (p i : ℕ) (hi : i < 2 * k)
    (h0 : (d p).val = enc m k u.val v.val i) (h1 : (d (p + 1)).val = nxt m k u.val v.val i) :
    ∀ j, i + j < 2 * k →
      (d (p + j)).val = enc m k u.val v.val (i + j) ∧ (d (p + j + 1)).val = nxt m k u.val v.val (i + j) := by
  intro j
  induction j with
  | zero => intro _; simpa using ⟨h0, h1⟩
  | succ j ih =>
    intro hj
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hcur : (d (p + (j + 1))).val = enc m k u.val v.val (i + (j + 1)) := by
      rw [show p + (j + 1) = p + j + 1 by omega, ih2]
      simp only [nxt, show i + j + 1 < 2 * k by omega, ite_true]
      congr 1 <;> omega
    refine ⟨hcur, ?_⟩
    have hnb := nbr_of_internal m k H hk (d (p + (j + 1))) (d (p + (j + 1) + 1)) u.val v.val (i + (j + 1))
      (Fin.lt_def.1 huv) v.isLt (by omega) hcur (hadj _)
    rcases hnb with hnb | hnb
    · exact hnb
    · exfalso
      apply ne_two hL hinj (p + j)
      apply Fin.ext
      rw [show p + j + 2 = p + (j + 1) + 1 by omega, hnb, ih1]
      simp only [prv, show ¬ (i + (j + 1) = 0) by omega, ite_false]
      congr 1 <;> omega

theorem forward_end (hk : 1 ≤ k) (hL : 3 ≤ L)
    (hadj : ∀ t, Rel m k H (d t) (d (t + 1)) ∨ Rel m k H (d (t + 1)) (d t))
    (hinj : ∀ i j, d i = d j → i % L = j % L)
    (u v : Fin m) (huv : u < v) (p i : ℕ) (hi : i < 2 * k)
    (h0 : (d p).val = enc m k u.val v.val i) (h1 : (d (p + 1)).val = nxt m k u.val v.val i) :
    (d (p + (2 * k - i))).val = v.val := by
  have := (forward hk hL hadj hinj u v huv p i hi h0 h1 (2 * k - 1 - i) (by omega)).2
  rw [show p + (2 * k - 1 - i) + 1 = p + (2 * k - i) by omega] at this
  rw [this]
  simp only [nxt, show ¬ (i + (2 * k - 1 - i) + 1 < 2 * k) by omega, ite_false]

theorem backward (hk : 1 ≤ k) (hL : 3 ≤ L)
    (hadj : ∀ t, Rel m k H (d t) (d (t + 1)) ∨ Rel m k H (d (t + 1)) (d t))
    (hinj : ∀ i j, d i = d j → i % L = j % L)
    (u v : Fin m) (huv : u < v) (p i : ℕ) (hi : i < 2 * k)
    (h0 : (d p).val = enc m k u.val v.val i) (h1 : (d (p + 1)).val = prv m k u.val v.val i) :
    ∀ j, j ≤ i →
      (d (p + j)).val = enc m k u.val v.val (i - j) ∧ (d (p + j + 1)).val = prv m k u.val v.val (i - j) := by
  intro j
  induction j with
  | zero => intro _; simpa using ⟨h0, h1⟩
  | succ j ih =>
    intro hj
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hcur : (d (p + (j + 1))).val = enc m k u.val v.val (i - (j + 1)) := by
      rw [show p + (j + 1) = p + j + 1 by omega, ih2]
      simp only [prv, show ¬ (i - j = 0) by omega, ite_false]
      congr 1 <;> omega
    refine ⟨hcur, ?_⟩
    have hnb := nbr_of_internal m k H hk (d (p + (j + 1))) (d (p + (j + 1) + 1)) u.val v.val (i - (j + 1))
      (Fin.lt_def.1 huv) v.isLt (by omega) hcur (hadj _)
    rcases hnb with hnb | hnb
    · exfalso
      apply ne_two hL hinj (p + j)
      apply Fin.ext
      rw [show p + j + 2 = p + (j + 1) + 1 by omega, hnb, ih1]
      simp only [nxt, show i - (j + 1) + 1 < 2 * k by omega, ite_true]
      congr 1 <;> omega
    · exact hnb

theorem backward_end (hk : 1 ≤ k) (hL : 3 ≤ L)
    (hadj : ∀ t, Rel m k H (d t) (d (t + 1)) ∨ Rel m k H (d (t + 1)) (d t))
    (hinj : ∀ i j, d i = d j → i % L = j % L)
    (u v : Fin m) (huv : u < v) (p i : ℕ) (hi : i < 2 * k)
    (h0 : (d p).val = enc m k u.val v.val i) (h1 : (d (p + 1)).val = prv m k u.val v.val i) :
    (d (p + i + 1)).val = u.val := by
  have := (backward hk hL hadj hinj u v huv p i hi h0 h1 i le_rfl).2
  rw [this]
  simp [prv]

/-- From an original vertex the cycle runs through one whole subdivided edge. -/
theorem block (hk : 1 ≤ k) (hL : 3 ≤ L)
    (hadj : ∀ t, Rel m k H (d t) (d (t + 1)) ∨ Rel m k H (d (t + 1)) (d t))
    (hinj : ∀ i j, d i = d j → i % L = j % L) (p : ℕ) (hp : (d p).val < m) :
    ∃ (u v : Fin m) (dir : Bool), u < v ∧ H.Adj u v ∧
      (d p).val = (if dir then u.val else v.val) ∧ (d (p + (2 * k + 1))).val = (if dir then v.val else u.val) ∧
      ∀ j, 1 ≤ j → j ≤ 2 * k → (d (p + j)).val = enc m k u.val v.val (if dir then j - 1 else 2 * k - j) := by
  obtain ⟨u, v, i, huv, hH, hi, h1, hcase⟩ := nbr_of_orig m k H (d p) (d (p + 1)) hp (hadj p)
  have huv' := Fin.lt_def.1 huv
  rcases hcase with ⟨rfl, hp0⟩ | ⟨hi2, hp0⟩
  · -- entering at the `u` end
    have h2 : (d (p + 2)).val = nxt m k u.val v.val 0 := by
      have hnb := nbr_of_internal m k H hk (d (p + 1)) (d (p + 1 + 1)) u.val v.val 0 huv' v.isLt hi h1 (hadj _)
      rcases hnb with hnb | hnb
      · exact hnb
      · exfalso
        apply ne_two hL hinj p
        apply Fin.ext
        rw [hnb, hp0]
        simp [prv]
    refine ⟨u, v, true, huv, hH, by simpa using hp0, ?_, ?_⟩
    · have := forward_end hk hL hadj hinj u v huv (p + 1) 0 hi h1 (by simpa using h2)
      rw [show p + 1 + (2 * k - 0) = p + (2 * k + 1) by omega] at this
      simpa using this
    · intro j hj1 hj2
      have := (forward hk hL hadj hinj u v huv (p + 1) 0 hi h1 (by simpa using h2) (j - 1) (by omega)).1
      rw [show p + 1 + (j - 1) = p + j by omega] at this
      simpa using this
  · -- entering at the `v` end
    have h2 : (d (p + 2)).val = prv m k u.val v.val i := by
      have hnb := nbr_of_internal m k H hk (d (p + 1)) (d (p + 1 + 1)) u.val v.val i huv' v.isLt hi h1 (hadj _)
      rcases hnb with hnb | hnb
      · exfalso
        apply ne_two hL hinj p
        apply Fin.ext
        rw [hnb, hp0]
        simp [nxt, show ¬ (i + 1 < 2 * k) by omega]
      · exact hnb
    refine ⟨u, v, false, huv, hH, by simpa using hp0, ?_, ?_⟩
    · have := backward_end hk hL hadj hinj u v huv (p + 1) i hi h1 (by simpa using h2)
      rw [show p + 1 + i + 1 = p + (2 * k + 1) by omega] at this
      simpa using this
    · intro j hj1 hj2
      have := (backward hk hL hadj hinj u v huv (p + 1) i hi h1 (by simpa using h2) (j - 1) (by omega)).1
      rw [show p + 1 + (j - 1) = p + j by omega] at this
      rw [this]
      simp only [Bool.false_eq_true, ite_false]
      congr 1 <;> omega

end Cycle

section Count

variable {m k : ℕ} {H : SimpleGraph (Fin m)} {L : ℕ} {d : ℕ → Fin (m + 2 * k * m * m)}

theorem blocks (hk : 1 ≤ k) (hL : 3 ≤ L)
    (hadj : ∀ t, Rel m k H (d t) (d (t + 1)) ∨ Rel m k H (d (t + 1)) (d t))
    (hinj : ∀ i j, d i = d j → i % L = j % L) (h0 : (d 0).val < m) :
    ∀ r, (d (r * (2 * k + 1))).val < m ∧
      ∀ j, 1 ≤ j → j ≤ 2 * k → m ≤ (d (r * (2 * k + 1) + j)).val := by
  intro r
  induction r with
  | zero =>
    refine ⟨by simpa using h0, fun j hj1 hj2 => ?_⟩
    obtain ⟨u, v, dir, -, -, -, -, hin⟩ := block hk hL hadj hinj 0 h0
    have := hin j hj1 hj2
    simp only [Nat.zero_mul, Nat.zero_add] at this ⊢
    rw [this]
    exact enc_ge _ _ _ _ _
  | succ r ih =>
    obtain ⟨u, v, dir, -, -, -, hend, -⟩ := block hk hL hadj hinj (r * (2 * k + 1)) ih.1
    have hpos : (r + 1) * (2 * k + 1) = r * (2 * k + 1) + (2 * k + 1) := by ring
    have hend' : (d ((r + 1) * (2 * k + 1))).val < m := by
      rw [hpos, hend]
      split_ifs
      · exact v.isLt
      · exact u.isLt
    refine ⟨hend', fun j hj1 hj2 => ?_⟩
    obtain ⟨u', v', dir', -, -, -, -, hin⟩ := block hk hL hadj hinj ((r + 1) * (2 * k + 1)) hend'
    rw [hin j hj1 hj2]
    exact enc_ge _ _ _ _ _

theorem orig_dvd (hk : 1 ≤ k) (hL : 3 ≤ L)
    (hadj : ∀ t, Rel m k H (d t) (d (t + 1)) ∨ Rel m k H (d (t + 1)) (d t))
    (hinj : ∀ i j, d i = d j → i % L = j % L) (h0 : (d 0).val < m) (t : ℕ) (ht : (d t).val < m) :
    (2 * k + 1) ∣ t := by
  by_contra hnd
  have hmod : t % (2 * k + 1) ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hlt : t % (2 * k + 1) < 2 * k + 1 := Nat.mod_lt _ (by omega)
  have hdiv : t / (2 * k + 1) * (2 * k + 1) + t % (2 * k + 1) = t := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod t (2 * k + 1)
  have := (blocks hk hL hadj hinj h0 (t / (2 * k + 1))).2 (t % (2 * k + 1)) (by omega) (by omega)
  rw [hdiv] at this
  omega

theorem cycle_long (hk : 1 ≤ k) (hL : 3 ≤ L)
    (hadj : ∀ t, Rel m k H (d t) (d (t + 1)) ∨ Rel m k H (d (t + 1)) (d t))
    (hinj : ∀ i j, d i = d j → i % L = j % L) (h0 : (d 0).val < m) (hper : d L = d 0) :
    6 * k + 3 ≤ L := by
  obtain ⟨r, hr⟩ := orig_dvd hk hL hadj hinj h0 L (by rw [hper]; exact h0)
  have hr1 : 1 ≤ r := by
    rcases r with _ | r
    · simp at hr; omega
    · omega
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · exfalso
    obtain ⟨u, v, dir, huv, -, hs, he, hin⟩ := block hk hL hadj hinj 0 h0
    simp only [Nat.zero_add] at hs he hin
    have huv1 := Fin.lt_def.1 huv
    interval_cases r
    · have hL' : L = 2 * k + 1 := by omega
      have hwrap : d (2 * k + 1) = d 0 := by rw [← hL']; exact hper
      have hv : (d (2 * k + 1)).val = (d 0).val := by rw [hwrap]
      rw [he, hs] at hv
      cases dir <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hv <;> omega
    · have hL' : L = 2 * (2 * k + 1) := by omega
      have hmid : (d (2 * k + 1)).val < m := by
        rw [he]; split_ifs
        · exact v.isLt
        · exact u.isLt
      obtain ⟨u', v', dir', huv', -, hs', he', hin'⟩ := block hk hL hadj hinj (2 * k + 1) hmid
      have huv2 := Fin.lt_def.1 huv'
      have hwrap : d (2 * k + 1 + (2 * k + 1)) = d 0 := by
        rw [show 2 * k + 1 + (2 * k + 1) = L by omega]; exact hper
      have e1 : (if dir then v.val else u.val) = (if dir' then u'.val else v'.val) := by rw [← he, ← hs']
      have e2 : (if dir' then v'.val else u'.val) = (if dir then u.val else v.val) := by
        rw [← he', hwrap, hs]
      cases dir <;> cases dir' <;> simp only [Bool.false_eq_true, ite_false, ite_true] at e1 e2
      · omega
      · have hA := hin (2 * k) (by omega) le_rfl
        have hB := hin' 1 le_rfl (by omega)
        simp only [Bool.false_eq_true, ite_false, ite_true, Nat.sub_self] at hA hB
        apply ne_two hL hinj (2 * k)
        apply Fin.ext
        rw [show 2 * k + 2 = 2 * k + 1 + 1 by omega, hA, hB, e1, e2]
      · have hA := hin 1 le_rfl (by omega)
        have hB := hin' (2 * k) (by omega) le_rfl
        simp only [Bool.false_eq_true, ite_false, ite_true, Nat.sub_self] at hA hB
        have heq : d 1 = d (2 * k + 1 + 2 * k) := Fin.ext (by rw [hA, hB, e1, e2])
        have := hinj _ _ heq
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
      · omega
  · rw [hr]
    nlinarith [Nat.mul_le_mul_left (2 * k + 1) hr3]

end Count

end L285

end PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_285 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ (L : ℕ) (c : ℕ → Fin (m + 2 * k * m * m)), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → S.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L := by
  intro k m H hk S hS L c hL hinjc hadjc
  have hadj' : ∀ x y, S.Adj x y ↔ x ≠ y ∧ (L285.Rel m k H x y ∨ L285.Rel m k H y x) := by
    intro x y
    rw [hS, SimpleGraph.fromRel_adj]
    exact Iff.rfl
  have hLpos : 0 < L := by omega
  set d : ℕ → Fin (m + 2 * k * m * m) := fun t => c (t % L) with hd
  have hadj : ∀ t, L285.Rel m k H (d t) (d (t + 1)) ∨ L285.Rel m k H (d (t + 1)) (d t) := by
    intro t
    have h := (hadj' _ _).1 (hadjc (t % L) (Nat.mod_lt _ hLpos))
    have e : (t + 1) % L = (t % L + 1) % L := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < L by omega)]
    simp only [hd]
    rw [e]
    exact h.2
  have hinj : ∀ i j, d i = d j → i % L = j % L :=
    fun i j h => hinjc _ _ (Nat.mod_lt _ hLpos) (Nat.mod_lt _ hLpos) h
  have hper : ∀ p, d (p + L) = d p := fun p => by
    simp only [hd]
    rw [Nat.add_mod_right]
  have hex : ∃ p, (d p).val < m := by
    by_contra hall
    simp only [not_exists, not_lt] at hall
    obtain ⟨u, v, i, huv, _, hi, h0⟩ := L285.internal_data m k H (d 0) (d 1) (hall 0) (hadj 0)
    have hv := v.isLt
    have hu := u.isLt
    rcases L285.nbr_of_internal m k H hk (d 0) (d 1) u.val v.val i (Fin.lt_def.1 huv) v.isLt hi h0 (hadj 0)
      with h1 | h1
    · have := L285.forward_end hk hL hadj hinj u v huv 0 i hi h0 h1
      have := hall (0 + (2 * k - i))
      omega
    · have := L285.backward_end hk hL hadj hinj u v huv 0 i hi h0 h1
      have := hall (0 + i + 1)
      omega
  obtain ⟨p₀, hp₀⟩ := hex
  have hadj2 : ∀ t, L285.Rel m k H (d (p₀ + t)) (d (p₀ + t + 1)) ∨ L285.Rel m k H (d (p₀ + t + 1)) (d (p₀ + t)) :=
    fun t => hadj _
  have hinj2 : ∀ i j, d (p₀ + i) = d (p₀ + j) → i % L = j % L := fun i j h =>
    Nat.ModEq.add_left_cancel' p₀ (hinj _ _ h)
  have hper2 : d (p₀ + L) = d (p₀ + 0) := by rw [hper p₀, Nat.add_zero]
  exact L285.cycle_long (d := fun t => d (p₀ + t)) hk hL hadj2 hinj2 (by simpa using hp₀) hper2
