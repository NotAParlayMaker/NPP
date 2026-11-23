import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_492_aux

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

lemma deg_le (k m : ℕ) (H : SimpleGraph (Fin m)) (hk : 1 ≤ k) (x : Fin (m + 2 * k * m * m))
    (hx : m ≤ x.val) : ((SimpleGraph.fromRel (Rel k m H)).neighborSet x).ncard ≤ 2 := by
  by_contra hc
  have hc' : 2 < ((SimpleGraph.fromRel (Rel k m H)).neighborSet x).ncard := by omega
  rw [Set.two_lt_ncard] at hc'
  obtain ⟨y1, h1, y2, h2, y3, h3, n12, n13, n23⟩ := hc'
  have c1 := classify k m H x y1 hx h1
  have c2 := classify k m H x y2 hx h2
  have c3 := classify k m H x y3 hx h3
  rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> rcases c3 with c3 | c3
  · exact n12 (Fin.ext (lo_unique k m _ _ _ hk c1 c2))
  · exact n12 (Fin.ext (lo_unique k m _ _ _ hk c1 c2))
  · exact n13 (Fin.ext (lo_unique k m _ _ _ hk c1 c3))
  · exact n23 (Fin.ext (hi_unique k m _ _ _ c2 c3))
  · exact n23 (Fin.ext (lo_unique k m _ _ _ hk c2 c3))
  · exact n13 (Fin.ext (hi_unique k m _ _ _ c1 c3))
  · exact n12 (Fin.ext (hi_unique k m _ _ _ c1 c2))
  · exact n12 (Fin.ext (hi_unique k m _ _ _ c1 c2))

end PEqualNP.Outside.L_meta_492_aux

open PEqualNP.Outside.L_meta_492_aux in
theorem PEqualNP.Outside.L_meta_492 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ u v : Fin (m + 2 * k * m * m), u ≠ v → 3 ≤ (S.neighborSet u).ncard → 3 ≤ (S.neighborSet v).ncard → ∀ p : S.Walk u v, 2 * k + 1 ≤ p.length := by
  intro k m H hk S hS u v huv hu hv p
  have hS' : S = SimpleGraph.fromRel (Rel k m H) := hS
  subst hS'
  have hum : u.val < m := by
    by_contra hc
    have := deg_le k m H hk u (by omega)
    omega
  have hvm : v.val < m := by
    by_contra hc
    have := deg_le k m H hk v (by omega)
    omega
  have hb := walk_bound k m H u.val u v p
  have hne : v.val ≠ u.val := fun h => huv (Fin.ext h.symm)
  rw [phi_low k m u.val u.val hum, phi_low k m u.val v.val hvm] at hb; simp only [ite_true, hne, ite_false] at hb
  omega
