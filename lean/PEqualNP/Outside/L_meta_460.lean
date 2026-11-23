import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_460_aux

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

def RelN (k m xn yn : ℕ) : Prop :=
  ∃ a b i : ℕ, a < b ∧ b < m ∧ i < 2 * k ∧ xn = m + 2 * k * (a * m + b) + i ∧
    ((i = 0 ∧ yn = a) ∨ (i + 1 < 2 * k ∧ yn = m + 2 * k * (a * m + b) + i + 1) ∨
      (i + 1 = 2 * k ∧ yn = b))

lemma lipN (k m u0 xn yn : ℕ) (h : RelN k m xn yn) :
    phi k m u0 yn ≤ phi k m u0 xn + 1 ∧ phi k m u0 xn ≤ phi k m u0 yn + 1 := by
  obtain ⟨a, b, i, hab, hb, hi, hx, hy⟩ := h
  have hpx := phi_sub k m u0 a b i hb hi
  rw [← hx] at hpx
  rcases hy with ⟨hi0, hy⟩ | ⟨hi1, hy⟩ | ⟨hi1, hy⟩
  · have hpy := phi_low k m u0 yn (by omega)
    rw [hpx, hpy, hy]
    split_ifs <;> omega
  · have hpy := phi_sub k m u0 a b (i + 1) hb hi1
    have hy' : yn = m + 2 * k * (a * m + b) + (i + 1) := by
      rw [hy, Nat.add_assoc]
    rw [← hy'] at hpy
    rw [hpx, hpy]
    split_ifs <;> omega
  · have hpy := phi_low k m u0 yn (by omega)
    rw [hpx, hpy, hy]
    split_ifs <;> omega

lemma classifyN (k m xn yn : ℕ) (hx : m ≤ xn) (h : RelN k m xn yn ∨ RelN k m yn xn) :
    Lo k m xn yn ∨ Hi k m xn yn := by
  rcases h with h' | h'
  · obtain ⟨a, b, i, hab, hb, hi, hxv, hy⟩ := h'
    rcases hy with ⟨hi0, hy⟩ | ⟨hi1, hy⟩ | ⟨hi1, hy⟩
    · left
      right
      exact ⟨a, b, hb, by rw [hxv, hi0], hy⟩
    · right
      left
      exact ⟨a, b, i, hb, hi1, hxv, by rw [hy, hxv]⟩
    · right
      right
      exact ⟨a, b, i, hb, hi1, hxv, hy⟩
  · obtain ⟨a, b, i, hab, hb, hi, hyv, hxx⟩ := h'
    rcases hxx with ⟨hi0, hxx⟩ | ⟨hi1, hxx⟩ | ⟨hi1, hxx⟩
    · omega
    · left
      left
      refine ⟨a, b, i, hb, hi1, ?_, ?_⟩
      · rw [hxx, Nat.add_assoc]
      · rw [hxx, hyv]
    · omega

lemma adj_rel (m k : ℕ) (hk : 1 ≤ k) (u v : ℕ) (huv : u < v) (hv : v < m) (p xn yn : ℕ)
    (hp : p ≤ 2 * k)
    (hx : (p = 0 ∧ xn = u) ∨ (p = 2 * k + 1 ∧ xn = v) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ xn + 1 = m + 2 * k * (u * m + v) + p))
    (hy : (p + 1 = 0 ∧ yn = u) ∨ (p + 1 = 2 * k + 1 ∧ yn = v) ∨
      (1 ≤ p + 1 ∧ p + 1 ≤ 2 * k ∧ yn + 1 = m + 2 * k * (u * m + v) + (p + 1))) :
    RelN k m xn yn ∨ RelN k m yn xn := by
  rcases hx with ⟨hp0, hxu⟩ | ⟨hp0, hxu⟩ | ⟨hp1, hp2, hxu⟩
  · rcases hy with ⟨hq, hyv⟩ | ⟨hq, hyv⟩ | ⟨hq1, hq2, hyv⟩
    · omega
    · omega
    · right
      exact ⟨u, v, 0, huv, hv, by omega, by omega, Or.inl ⟨rfl, hxu⟩⟩
  · omega
  · rcases hy with ⟨hq, hyv⟩ | ⟨hq, hyv⟩ | ⟨hq1, hq2, hyv⟩
    · omega
    · left
      exact ⟨u, v, p - 1, huv, hv, by omega, by omega, Or.inr (Or.inr ⟨by omega, hyv⟩)⟩
    · left
      exact ⟨u, v, p - 1, huv, hv, by omega, by omega, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩

lemma walk_bound {N : ℕ} (k m u0 : ℕ) (S : SimpleGraph (Fin N))
    (hrel : ∀ x y : Fin N, S.Adj x y → RelN k m x.val y.val ∨ RelN k m y.val x.val)
    (x y : Fin N) (p : S.Walk x y) :
    phi k m u0 y.val ≤ phi k m u0 x.val + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.Walk.length_cons]
    rcases hrel _ _ h with h' | h'
    · have := (lipN k m u0 _ _ h').1
      omega
    · have := (lipN k m u0 _ _ h').2
      omega

lemma deg_le {N : ℕ} (k m : ℕ) (hk : 1 ≤ k) (S : SimpleGraph (Fin N))
    (hrel : ∀ x y : Fin N, S.Adj x y → RelN k m x.val y.val ∨ RelN k m y.val x.val)
    (x : Fin N) (hx : m ≤ x.val) : (S.neighborSet x).ncard ≤ 2 := by
  by_contra hc
  have hc' : 2 < (S.neighborSet x).ncard := by omega
  rw [Set.two_lt_ncard] at hc'
  obtain ⟨y1, h1, y2, h2, y3, h3, n12, n13, n23⟩ := hc'
  have c1 := classifyN k m x.val y1.val hx (hrel _ _ h1)
  have c2 := classifyN k m x.val y2.val hx (hrel _ _ h2)
  have c3 := classifyN k m x.val y3.val hx (hrel _ _ h3)
  rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2 <;> rcases c3 with c3 | c3
  · exact n12 (Fin.ext (lo_unique k m _ _ _ hk c1 c2))
  · exact n12 (Fin.ext (lo_unique k m _ _ _ hk c1 c2))
  · exact n13 (Fin.ext (lo_unique k m _ _ _ hk c1 c3))
  · exact n23 (Fin.ext (hi_unique k m _ _ _ c2 c3))
  · exact n23 (Fin.ext (lo_unique k m _ _ _ hk c2 c3))
  · exact n13 (Fin.ext (hi_unique k m _ _ _ c1 c3))
  · exact n12 (Fin.ext (hi_unique k m _ _ _ c1 c2))
  · exact n12 (Fin.ext (hi_unique k m _ _ _ c1 c2))

end PEqualNP.Outside.L_meta_460_aux

open PEqualNP.Outside.L_meta_460_aux in
theorem PEqualNP.Outside.L_meta_460 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x ≠ y → 3 ≤ (S.neighborSet x).ncard → 3 ≤ (S.neighborSet y).ncard → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hxy hx hy p
  have hrel : ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y →
      RelN k m x.val y.val ∨ RelN k m y.val x.val := by
    intro x y h
    obtain ⟨u, v, huv, -, q, hq, hc⟩ := (hS x y).mp h
    have huv' : u.val < v.val := huv
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact adj_rel m k hk u.val v.val huv' v.isLt q x.val y.val hq ((hQ u v q x).mp h1)
        ((hQ u v (q + 1) y).mp h2)
    · exact (adj_rel m k hk u.val v.val huv' v.isLt q y.val x.val hq ((hQ u v q y).mp h1)
        ((hQ u v (q + 1) x).mp h2)).symm
  have hxm : x.val < m := by
    by_contra hc
    have := deg_le k m hk S hrel x (by omega)
    omega
  have hym : y.val < m := by
    by_contra hc
    have := deg_le k m hk S hrel y (by omega)
    omega
  have hb := walk_bound k m x.val S hrel x y p
  have hne : y.val ≠ x.val := fun h => hxy (Fin.ext h.symm)
  rw [phi_low k m x.val x.val hxm, phi_low k m x.val y.val hym] at hb
  simp only [ite_true, hne, ite_false] at hb
  omega
