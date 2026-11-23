import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_285_aux

lemma dec (K m a b i a' b' i' : ℕ) (hb : b < m) (hb' : b' < m) (hi : i < K) (hi' : i' < K)
    (h : K * (a * m + b) + i = K * (a' * m + b') + i') : a = a' ∧ b = b' ∧ i = i' := by
  have hK : 0 < K := by omega
  have hm : 0 < m := by omega
  have e1 : (K * (a * m + b) + i) / K = a * m + b := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hi, Nat.add_zero]
  have e2 : (K * (a' * m + b') + i') / K = a' * m + b' := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hi', Nat.add_zero]
  have e3 : (K * (a * m + b) + i) % K = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have e4 : (K * (a' * m + b') + i') % K = i' := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi']
  have hE : a * m + b = a' * m + b' := by rw [← e1, ← e2, h]
  have hI : i = i' := by rw [← e3, ← e4, h]
  have f1 : (a * m + b) / m = a := by
    rw [Nat.mul_comm a m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb, Nat.add_zero]
  have f2 : (a' * m + b') / m = a' := by
    rw [Nat.mul_comm a' m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb', Nat.add_zero]
  have f3 : (a * m + b) % m = b := by
    rw [Nat.mul_comm a m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  have f4 : (a' * m + b') % m = b' := by
    rw [Nat.mul_comm a' m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb']
  refine ⟨?_, ?_, hI⟩
  · rw [← f1, ← f2, hE]
  · rw [← f3, ← f4, hE]

def phi (k m u0 n : ℕ) : ℕ :=
  if n < m then (if n = u0 then 0 else 2 * k + 1)
  else if ((n - m) / (2 * k)) / m = u0 then (n - m) % (2 * k) + 1
  else if ((n - m) / (2 * k)) % m = u0 then 2 * k - (n - m) % (2 * k)
  else 2 * k + 1

lemma phi_low (k m u0 n : ℕ) (h : n < m) :
    phi k m u0 n = if n = u0 then 0 else 2 * k + 1 := by
  unfold phi
  simp only [h, ite_true]

lemma phi_sub (k m u0 a b i : ℕ) (hb : b < m) (hi : i < 2 * k) :
    phi k m u0 (m + 2 * k * (a * m + b) + i) =
      if a = u0 then i + 1 else if b = u0 then 2 * k - i else 2 * k + 1 := by
  have hK : 0 < 2 * k := by omega
  have hm : 0 < m := by omega
  have h0 : ¬ (m + 2 * k * (a * m + b) + i < m) := by
    generalize 2 * k * (a * m + b) = X
    omega
  have h1 : m + 2 * k * (a * m + b) + i - m = 2 * k * (a * m + b) + i := by
    generalize 2 * k * (a * m + b) = X
    omega
  have e1 : (2 * k * (a * m + b) + i) / (2 * k) = a * m + b := by
    rw [Nat.mul_add_div hK, Nat.div_eq_of_lt hi, Nat.add_zero]
  have e3 : (2 * k * (a * m + b) + i) % (2 * k) = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have f1 : (a * m + b) / m = a := by
    rw [Nat.mul_comm a m, Nat.mul_add_div hm, Nat.div_eq_of_lt hb, Nat.add_zero]
  have f3 : (a * m + b) % m = b := by
    rw [Nat.mul_comm a m, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  unfold phi
  simp only [h0, ite_false, h1, e1, e3, f1, f3]

def Rel (k m : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (m + 2 * k * m * m)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))

lemma lip (k m : ℕ) (H : SimpleGraph (Fin m)) (u0 : ℕ) (x y : Fin (m + 2 * k * m * m))
    (h : Rel k m H x y) :
    phi k m u0 y.val ≤ phi k m u0 x.val + 1 ∧ phi k m u0 x.val ≤ phi k m u0 y.val + 1 := by
  obtain ⟨u, v, huv, -, i, hx, hy⟩ := h
  have hpx := phi_sub k m u0 u.val v.val i.val v.isLt i.isLt
  rw [← hx] at hpx
  have huv' : u.val < v.val := huv
  have hil := i.isLt
  rcases hy with ⟨hi, hy⟩ | ⟨hi, hy⟩ | ⟨hi, hy⟩
  · have hpy := phi_low k m u0 y.val (by rw [hy]; exact u.isLt)
    rw [hpx, hpy, hy]
    split_ifs <;> omega
  · have hpy := phi_sub k m u0 u.val v.val (i.val + 1) v.isLt hi
    have hy' : y.val = m + 2 * k * (u.val * m + v.val) + (i.val + 1) := by
      rw [hy, Nat.add_assoc]
    rw [← hy'] at hpy
    rw [hpx, hpy]
    split_ifs <;> omega
  · have hpy := phi_low k m u0 y.val (by rw [hy]; exact v.isLt)
    rw [hpx, hpy, hy]
    split_ifs <;> omega

lemma walk_bound (k m : ℕ) (H : SimpleGraph (Fin m)) (u0 : ℕ)
    (x y : Fin (m + 2 * k * m * m)) (p : (SimpleGraph.fromRel (Rel k m H)).Walk x y) :
    phi k m u0 y.val ≤ phi k m u0 x.val + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.fromRel_adj] at h
    rw [SimpleGraph.Walk.length_cons]
    rcases h.2 with h' | h'
    · have := (lip k m H u0 _ _ h').1
      omega
    · have := (lip k m H u0 _ _ h').2
      omega

def Lo (k m xn yn : ℕ) : Prop :=
  (∃ a b i : ℕ, b < m ∧ i + 1 < 2 * k ∧ xn = m + 2 * k * (a * m + b) + (i + 1) ∧ yn + 1 = xn) ∨
  (∃ a b : ℕ, b < m ∧ xn = m + 2 * k * (a * m + b) + 0 ∧ yn = a)

def Hi (k m xn yn : ℕ) : Prop :=
  (∃ a b i : ℕ, b < m ∧ i + 1 < 2 * k ∧ xn = m + 2 * k * (a * m + b) + i ∧ yn = xn + 1) ∨
  (∃ a b i : ℕ, b < m ∧ i + 1 = 2 * k ∧ xn = m + 2 * k * (a * m + b) + i ∧ yn = b)

lemma lo_unique (k m xn y1 y2 : ℕ) (hk : 1 ≤ k) (h1 : Lo k m xn y1) (h2 : Lo k m xn y2) : y1 = y2 := by
  rcases h1 with ⟨a, b, i, hb, hi, hx, hy⟩ | ⟨a, b, hb, hx, hy⟩ <;>
  rcases h2 with ⟨a', b', i', hb', hi', hx', hy'⟩ | ⟨a', b', hb', hx', hy'⟩
  · omega
  · have := dec (2 * k) m a b (i + 1) a' b' 0 hb hb' hi (by omega) (by omega)
    omega
  · have := dec (2 * k) m a b 0 a' b' (i' + 1) hb hb' (by omega) hi' (by omega)
    omega
  · have := dec (2 * k) m a b 0 a' b' 0 hb hb' (by omega) (by omega) (by omega)
    omega

lemma hi_unique (k m xn y1 y2 : ℕ) (h1 : Hi k m xn y1) (h2 : Hi k m xn y2) : y1 = y2 := by
  rcases h1 with ⟨a, b, i, hb, hi, hx, hy⟩ | ⟨a, b, i, hb, hi, hx, hy⟩ <;>
  rcases h2 with ⟨a', b', i', hb', hi', hx', hy'⟩ | ⟨a', b', i', hb', hi', hx', hy'⟩
  · omega
  · have := dec (2 * k) m a b i a' b' i' hb hb' (by omega) (by omega) (by omega)
    omega
  · have := dec (2 * k) m a b i a' b' i' hb hb' (by omega) (by omega) (by omega)
    omega
  · have := dec (2 * k) m a b i a' b' i' hb hb' (by omega) (by omega) (by omega)
    omega

lemma classify (k m : ℕ) (H : SimpleGraph (Fin m)) (x y : Fin (m + 2 * k * m * m))
    (hx : m ≤ x.val) (h : (SimpleGraph.fromRel (Rel k m H)).Adj x y) :
    Lo k m x.val y.val ∨ Hi k m x.val y.val := by
  rw [SimpleGraph.fromRel_adj] at h
  rcases h.2 with h' | h'
  · obtain ⟨u, v, -, -, i, hxv, hy⟩ := h'
    have hil := i.isLt
    rcases hy with ⟨hi, hy⟩ | ⟨hi, hy⟩ | ⟨hi, hy⟩
    · left
      right
      exact ⟨u.val, v.val, v.isLt, by rw [hxv, hi], hy⟩
    · right
      left
      exact ⟨u.val, v.val, i.val, v.isLt, hi, hxv, by rw [hy, hxv]⟩
    · right
      right
      exact ⟨u.val, v.val, i.val, v.isLt, hi, hxv, hy⟩
  · obtain ⟨u, v, -, -, i, hyv, hxx⟩ := h'
    have hul := u.isLt
    have hvl := v.isLt
    rcases hxx with ⟨hi, hxx⟩ | ⟨hi, hxx⟩ | ⟨hi, hxx⟩
    · omega
    · left
      left
      refine ⟨u.val, v.val, i.val, v.isLt, hi, ?_, ?_⟩
      · rw [hxx, Nat.add_assoc]
      · rw [hxx, hyv]
    · omega

def InC {N : ℕ} (L : ℕ) (c : ℕ → Fin N) (n : ℕ) : Prop := ∃ j, j < L ∧ (c j).val = n

lemma two_nbrs (k m : ℕ) (H : SimpleGraph (Fin m)) (L : ℕ) (c : ℕ → Fin (m + 2 * k * m * m))
    (hL : 3 ≤ L) (hinj : ∀ i j : ℕ, i < L → j < L → c i = c j → i = j)
    (hadj : ∀ i : ℕ, i < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c i) (c ((i + 1) % L)))
    (j : ℕ) (hj : j < L) :
    ∃ s t, s < L ∧ t < L ∧ c s ≠ c t ∧ (SimpleGraph.fromRel (Rel k m H)).Adj (c j) (c s) ∧
      (SimpleGraph.fromRel (Rel k m H)).Adj (c j) (c t) := by
  have hprev : ∀ q, q + 1 < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c q) (c (q + 1)) := by
    intro q hq
    have := hadj q (by omega)
    rw [Nat.mod_eq_of_lt hq] at this
    exact this
  have hlast : (SimpleGraph.fromRel (Rel k m H)).Adj (c (L - 1)) (c 0) := by
    have := hadj (L - 1) (by omega)
    have e : (L - 1 + 1) % L = 0 := by
      rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [e] at this
    exact this
  by_cases h0 : j = 0
  · subst h0
    refine ⟨1, L - 1, by omega, by omega, ?_, ?_, ?_⟩
    · intro h
      have := hinj 1 (L - 1) (by omega) (by omega) h
      omega
    · exact hprev 0 (by omega)
    · exact hlast.symm
  · by_cases h1 : j + 1 = L
    · refine ⟨0, j - 1, by omega, by omega, ?_, ?_, ?_⟩
      · intro h
        have := hinj 0 (j - 1) (by omega) (by omega) h
        omega
      · have e : j = L - 1 := by omega
        rw [e]
        exact hlast
      · have := hprev (j - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at this
        exact this.symm
    · refine ⟨j + 1, j - 1, by omega, by omega, ?_, ?_, ?_⟩
      · intro h
        have := hinj (j + 1) (j - 1) (by omega) (by omega) h
        omega
      · exact hprev j (by omega)
      · have := hprev (j - 1) (by omega)
        rw [Nat.sub_add_cancel (by omega)] at this
        exact this.symm

lemma has_hi (k m : ℕ) (H : SimpleGraph (Fin m)) (hk : 1 ≤ k) (L : ℕ)
    (c : ℕ → Fin (m + 2 * k * m * m))
    (hL : 3 ≤ L) (hinj : ∀ i j : ℕ, i < L → j < L → c i = c j → i = j)
    (hadj : ∀ i : ℕ, i < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c i) (c ((i + 1) % L)))
    (j : ℕ) (hj : j < L) (hm : m ≤ (c j).val) :
    ∃ t, t < L ∧ Hi k m (c j).val (c t).val := by
  obtain ⟨s, t, hs, ht, hne, a1, a2⟩ := two_nbrs k m H L c hL hinj hadj j hj
  rcases classify k m H _ _ hm a1 with h | h
  · rcases classify k m H _ _ hm a2 with h' | h'
    · exact absurd (Fin.ext (lo_unique k m _ _ _ hk h h')) hne
    · exact ⟨t, ht, h'⟩
  · exact ⟨s, hs, h⟩

lemma has_lo (k m : ℕ) (H : SimpleGraph (Fin m)) (L : ℕ)
    (c : ℕ → Fin (m + 2 * k * m * m))
    (hL : 3 ≤ L) (hinj : ∀ i j : ℕ, i < L → j < L → c i = c j → i = j)
    (hadj : ∀ i : ℕ, i < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c i) (c ((i + 1) % L)))
    (j : ℕ) (hj : j < L) (hm : m ≤ (c j).val) :
    ∃ t, t < L ∧ Lo k m (c j).val (c t).val := by
  obtain ⟨s, t, hs, ht, hne, a1, a2⟩ := two_nbrs k m H L c hL hinj hadj j hj
  rcases classify k m H _ _ hm a1 with h | h
  · exact ⟨s, hs, h⟩
  · rcases classify k m H _ _ hm a2 with h' | h'
    · exact ⟨t, ht, h'⟩
    · exact absurd (Fin.ext (hi_unique k m _ _ _ h h')) hne

lemma up (k m : ℕ) (H : SimpleGraph (Fin m)) (hk : 1 ≤ k) (L : ℕ)
    (c : ℕ → Fin (m + 2 * k * m * m))
    (hL : 3 ≤ L) (hinj : ∀ i j : ℕ, i < L → j < L → c i = c j → i = j)
    (hadj : ∀ i : ℕ, i < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c i) (c ((i + 1) % L)))
    (a b : ℕ) (hb : b < m) :
    ∀ d i : ℕ, i + d + 1 = 2 * k → InC L c (m + 2 * k * (a * m + b) + i) → InC L c b := by
  intro d
  induction d with
  | zero =>
    intro i hi hC
    obtain ⟨j, hj, hv⟩ := hC
    obtain ⟨t, ht, hH⟩ := has_hi k m H hk L c hL hinj hadj j hj (by rw [hv]; omega)
    rw [hv] at hH
    rcases hH with ⟨a', b', i', hb', hi', hx, hy⟩ | ⟨a', b', i', hb', hi', hx, hy⟩
    · have := dec (2 * k) m a b i a' b' i' hb hb' (by omega) (by omega) (by omega)
      omega
    · have := dec (2 * k) m a b i a' b' i' hb hb' (by omega) (by omega) (by omega)
      exact ⟨t, ht, by omega⟩
  | succ d ih =>
    intro i hi hC
    obtain ⟨j, hj, hv⟩ := hC
    obtain ⟨t, ht, hH⟩ := has_hi k m H hk L c hL hinj hadj j hj (by rw [hv]; omega)
    rw [hv] at hH
    rcases hH with ⟨a', b', i', hb', hi', hx, hy⟩ | ⟨a', b', i', hb', hi', hx, hy⟩
    · exact ih (i + 1) (by omega) ⟨t, ht, by omega⟩
    · have := dec (2 * k) m a b i a' b' i' hb hb' (by omega) (by omega) (by omega)
      omega

lemma down (k m : ℕ) (H : SimpleGraph (Fin m)) (L : ℕ)
    (c : ℕ → Fin (m + 2 * k * m * m))
    (hL : 3 ≤ L) (hinj : ∀ i j : ℕ, i < L → j < L → c i = c j → i = j)
    (hadj : ∀ i : ℕ, i < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c i) (c ((i + 1) % L)))
    (a b : ℕ) (hb : b < m) :
    ∀ i : ℕ, i < 2 * k → InC L c (m + 2 * k * (a * m + b) + i) → InC L c a := by
  intro i
  induction i with
  | zero =>
    intro hi hC
    obtain ⟨j, hj, hv⟩ := hC
    obtain ⟨t, ht, hH⟩ := has_lo k m H L c hL hinj hadj j hj (by rw [hv]; omega)
    rw [hv] at hH
    rcases hH with ⟨a', b', i', hb', hi', hx, hy⟩ | ⟨a', b', hb', hx, hy⟩
    · have := dec (2 * k) m a b 0 a' b' (i' + 1) hb hb' (by omega) (by omega) (by omega)
      omega
    · have := dec (2 * k) m a b 0 a' b' 0 hb hb' (by omega) (by omega) (by omega)
      exact ⟨t, ht, by omega⟩
  | succ i ih =>
    intro hi hC
    obtain ⟨j, hj, hv⟩ := hC
    obtain ⟨t, ht, hH⟩ := has_lo k m H L c hL hinj hadj j hj (by rw [hv]; omega)
    rw [hv] at hH
    rcases hH with ⟨a', b', i', hb', hi', hx, hy⟩ | ⟨a', b', hb', hx, hy⟩
    · exact ih (by omega) ⟨t, ht, by omega⟩
    · have := dec (2 * k) m a b (i + 1) a' b' 0 hb hb' (by omega) (by omega) (by omega)
      omega

lemma other_end (k m : ℕ) (H : SimpleGraph (Fin m)) (hk : 1 ≤ k) (L : ℕ)
    (c : ℕ → Fin (m + 2 * k * m * m))
    (hL : 3 ≤ L) (hinj : ∀ i j : ℕ, i < L → j < L → c i = c j → i = j)
    (hadj : ∀ i : ℕ, i < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c i) (c ((i + 1) % L)))
    (w : ℕ) (hw : w < m) (x y : Fin (m + 2 * k * m * m)) (hxw : x.val = w)
    (hy : (SimpleGraph.fromRel (Rel k m H)).Adj x y) (hyC : InC L c y.val) :
    ∃ b, b < m ∧ InC L c b ∧
      ((w < b ∧ y.val = m + 2 * k * (w * m + b)) ∨
        (b < w ∧ y.val = m + 2 * k * (b * m + w) + (2 * k - 1))) := by
  rw [SimpleGraph.fromRel_adj] at hy
  rcases hy.2 with h | h
  · obtain ⟨u, v, -, -, i, hx, -⟩ := h
    omega
  · obtain ⟨u, v, huv, -, i, hyv, hcase⟩ := h
    have huv' : u.val < v.val := huv
    have hil := i.isLt
    have hvl := v.isLt
    rcases hcase with ⟨hi, hc⟩ | ⟨hi, hc⟩ | ⟨hi, hc⟩
    · have hwu : w = u.val := by omega
      subst hwu
      have hC : InC L c (m + 2 * k * (u.val * m + v.val) + 0) := by
        rw [hyv, hi] at hyC
        exact hyC
      have hin := up k m H hk L c hL hinj hadj u.val v.val v.isLt (2 * k - 1) 0 (by omega) hC
      exact ⟨v.val, v.isLt, hin, Or.inl ⟨huv', by omega⟩⟩
    · omega
    · have hwv : w = v.val := by omega
      subst hwv
      have hC : InC L c (m + 2 * k * (u.val * m + v.val) + i.val) := by
        rw [hyv] at hyC
        exact hyC
      have hin := down k m H L c hL hinj hadj u.val v.val v.isLt i.val hil hC
      exact ⟨u.val, by omega, hin, Or.inr ⟨huv', by omega⟩⟩

lemma path_bound (k m : ℕ) (H : SimpleGraph (Fin m)) (L : ℕ)
    (c : ℕ → Fin (m + 2 * k * m * m))
    (hadj : ∀ i : ℕ, i < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c i) (c ((i + 1) % L)))
    (u0 s : ℕ) :
    ∀ t : ℕ, s + t < L → phi k m u0 (c (s + t)).val ≤ phi k m u0 (c s).val + t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro h
    have a := hadj (s + t) (by omega)
    rw [Nat.mod_eq_of_lt (by omega)] at a
    rw [SimpleGraph.fromRel_adj] at a
    have ih' := ih (by omega)
    rw [← Nat.add_assoc]
    rcases a.2 with r | r
    · have := (lip k m H u0 _ _ r).1
      omega
    · have := (lip k m H u0 _ _ r).2
      omega

lemma arc (k m : ℕ) (H : SimpleGraph (Fin m)) (L : ℕ)
    (c : ℕ → Fin (m + 2 * k * m * m)) (hL : 3 ≤ L)
    (hadj : ∀ i : ℕ, i < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c i) (c ((i + 1) % L)))
    (i j : ℕ) (hj : j < L) (hij : i < j) (hci : (c i).val < m) (hcj : (c j).val < m)
    (hne : (c i).val ≠ (c j).val) : 2 * k + 1 ≤ j - i ∧ 2 * k + 1 ≤ L - j + i := by
  constructor
  · have h1 := path_bound k m H L c hadj (c i).val i (j - i) (by omega)
    have e : i + (j - i) = j := by omega
    rw [e, phi_low k m _ _ hcj, phi_low k m _ _ hci] at h1
    split_ifs at h1 <;> omega
  · have h2 := path_bound k m H L c hadj (c j).val j (L - 1 - j) (by omega)
    have e : j + (L - 1 - j) = L - 1 := by omega
    rw [e] at h2
    have h4 := path_bound k m H L c hadj (c j).val 0 i (by omega)
    rw [Nat.zero_add] at h4
    have a := hadj (L - 1) (by omega)
    have e2 : (L - 1 + 1) % L = 0 := by
      rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [e2, SimpleGraph.fromRel_adj] at a
    have h3 : phi k m (c j).val (c 0).val ≤ phi k m (c j).val (c (L - 1)).val + 1 := by
      rcases a.2 with r | r
      · exact (lip k m H _ _ _ r).1
      · exact (lip k m H _ _ _ r).2
    rw [phi_low k m _ _ hcj] at h2
    rw [phi_low k m _ _ hci] at h4
    split_ifs at h2 h4 <;> omega

lemma arc_sym (k m : ℕ) (H : SimpleGraph (Fin m)) (L : ℕ)
    (c : ℕ → Fin (m + 2 * k * m * m)) (hL : 3 ≤ L)
    (hadj : ∀ i : ℕ, i < L → (SimpleGraph.fromRel (Rel k m H)).Adj (c i) (c ((i + 1) % L)))
    (i j : ℕ) (hi : i < L) (hj : j < L) (hci : (c i).val < m) (hcj : (c j).val < m)
    (hne : (c i).val ≠ (c j).val) :
    (i < j ∧ 2 * k + 1 ≤ j - i ∧ 2 * k + 1 ≤ L - j + i) ∨
      (j < i ∧ 2 * k + 1 ≤ i - j ∧ 2 * k + 1 ≤ L - i + j) := by
  have hij : i ≠ j := by
    intro h
    subst h
    exact hne rfl
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact Or.inl ⟨h, arc k m H L c hL hadj i j hj h hci hcj hne⟩
  · exact Or.inr ⟨h, arc k m H L c hL hadj j i hi h hcj hci (Ne.symm hne)⟩

end PEqualNP.Outside.L_meta_285_aux

open PEqualNP.Outside.L_meta_285_aux in
theorem PEqualNP.Outside.L_meta_285 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ (L : ℕ) (c : ℕ → Fin (m + 2 * k * m * m)), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → S.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L := by
  intro k m H hk S hS L c hL hinj hadj
  have hS' : S = SimpleGraph.fromRel (Rel k m H) := hS
  subst hS'
  obtain ⟨j0, hj0, ha0⟩ : ∃ j, j < L ∧ (c j).val < m := by
    by_cases h : (c 0).val < m
    · exact ⟨0, by omega, h⟩
    · obtain ⟨t, ht, hH⟩ := has_hi k m H hk L c hL hinj hadj 0 (by omega) (by omega)
      have hd : ∃ a b i, b < m ∧ i < 2 * k ∧ (c 0).val = m + 2 * k * (a * m + b) + i := by
        rcases hH with ⟨a, b, i, hb, hi, hx, -⟩ | ⟨a, b, i, hb, hi, hx, -⟩
        · exact ⟨a, b, i, hb, by omega, hx⟩
        · exact ⟨a, b, i, hb, by omega, hx⟩
      obtain ⟨a, b, i, hb, hi, hx⟩ := hd
      obtain ⟨j, hj, hv⟩ := up k m H hk L c hL hinj hadj a b hb (2 * k - 1 - i) i (by omega)
        ⟨0, by omega, hx⟩
      exact ⟨j, hj, by omega⟩
  obtain ⟨s, t, hs, ht, hne, a1, a2⟩ := two_nbrs k m H L c hL hinj hadj j0 hj0
  obtain ⟨b1, hb1, ⟨p1, hp1, hv1⟩, he1⟩ :=
    other_end k m H hk L c hL hinj hadj (c j0).val ha0 (c j0) (c s) rfl a1 ⟨s, hs, rfl⟩
  obtain ⟨b2, hb2, ⟨p2, hp2, hv2⟩, he2⟩ :=
    other_end k m H hk L c hL hinj hadj (c j0).val ha0 (c j0) (c t) rfl a2 ⟨t, ht, rfl⟩
  have hb12 : b1 ≠ b2 := by
    intro h
    subst h
    apply hne
    apply Fin.ext
    rcases he1 with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rcases he2 with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> omega
  have hn1 : (c j0).val ≠ b1 := by
    rcases he1 with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> omega
  have hn2 : (c j0).val ≠ b2 := by
    rcases he2 with ⟨h2, e2⟩ | ⟨h2, e2⟩ <;> omega
  have A1 := arc_sym k m H L c hL hadj j0 p1 hj0 hp1 ha0 (by omega) (by omega)
  have A2 := arc_sym k m H L c hL hadj j0 p2 hj0 hp2 ha0 (by omega) (by omega)
  have A3 := arc_sym k m H L c hL hadj p1 p2 hp1 hp2 (by omega) (by omega) (by omega)
  omega
