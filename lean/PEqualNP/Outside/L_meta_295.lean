import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Aux295

private def ptv (m k a b p : ℕ) : ℕ :=
  if p = 0 then a else if p = 2 * k + 1 then b else m + 2 * k * (a * m + b) + (p - 1)

private theorem ptv_cases (m k a b p : ℕ) (hp : p ≤ 2 * k + 1) :
    (p = 0 ∧ ptv m k a b p = a) ∨ (p = 2 * k + 1 ∧ ptv m k a b p = b) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ ptv m k a b p = m + 2 * k * (a * m + b) + (p - 1)) := by
  unfold ptv
  split_ifs with h0 h1
  · exact Or.inl ⟨h0, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, rfl⟩)
  · exact Or.inr (Or.inr ⟨by omega, by omega, rfl⟩)

private theorem block_le {m a b : ℕ} (ha : a < m) (hb : b < m) : a * m + b + 1 ≤ m * m := by
  have h1 : (a + 1) * m ≤ m * m := Nat.mul_le_mul_right m ha
  have h2 : (a + 1) * m = a * m + m := by ring
  omega

private theorem ptv_lt {m k a b p : ℕ} (ha : a < m) (hb : b < m) (hp : p ≤ 2 * k + 1) :
    ptv m k a b p < m + 2 * k * (m * m) := by
  have h1 : 2 * k * (a * m + b + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ (block_le ha hb)
  have h2 : 2 * k * (a * m + b + 1) = 2 * k * (a * m + b) + 2 * k := by ring
  rcases ptv_cases m k a b p hp with ⟨-, h⟩ | ⟨-, h⟩ | ⟨h3, h4, h⟩ <;> omega

private theorem trich (m k a b c d : ℕ) (hb : b < m) (hd : d < m) :
    (a = c ∧ b = d ∧ 2 * k * (a * m + b) = 2 * k * (c * m + d)) ∨
      2 * k * (a * m + b) + 2 * k ≤ 2 * k * (c * m + d) ∨
      2 * k * (c * m + d) + 2 * k ≤ 2 * k * (a * m + b) := by
  rcases Nat.lt_trichotomy (a * m + b) (c * m + d) with h | h | h
  · right
    left
    have h1 : 2 * k * (a * m + b + 1) ≤ 2 * k * (c * m + d) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h)
    have h2 : 2 * k * (a * m + b + 1) = 2 * k * (a * m + b) + 2 * k := by ring
    omega
  · left
    have hac : a = c := by
      rcases Nat.lt_trichotomy a c with h1 | h1 | h1
      · exfalso
        have h2 : (a + 1) * m ≤ c * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt h1)
        have h3 : (a + 1) * m = a * m + m := by ring
        omega
      · exact h1
      · exfalso
        have h2 : (c + 1) * m ≤ a * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt h1)
        have h3 : (c + 1) * m = c * m + m := by ring
        omega
    subst hac
    have hbd : b = d := by omega
    subst hbd
    exact ⟨rfl, rfl, rfl⟩
  · right
    right
    have h1 : 2 * k * (c * m + d + 1) ≤ 2 * k * (a * m + b) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h)
    have h2 : 2 * k * (c * m + d + 1) = 2 * k * (c * m + d) + 2 * k := by ring
    omega

private theorem key {m k a b c d p q : ℕ} (hk : 1 ≤ k) (ha : a < m) (hb : b < m) (hc : c < m)
    (hd : d < m) (hp : p ≤ 2 * k) (hq : q ≤ 2 * k)
    (h : (ptv m k a b p = ptv m k c d q ∧ ptv m k a b (p + 1) = ptv m k c d (q + 1)) ∨
      (ptv m k a b p = ptv m k c d (q + 1) ∧ ptv m k a b (p + 1) = ptv m k c d q)) :
    a = c ∧ b = d ∧ p = q := by
  have c1 := ptv_cases m k a b p (by omega)
  have c2 := ptv_cases m k a b (p + 1) (by omega)
  have c3 := ptv_cases m k c d q (by omega)
  have c4 := ptv_cases m k c d (q + 1) (by omega)
  have t := trich m k a b c d hb hd
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · omega
  · omega

private def pt (m k : ℕ) (u v : Fin m) (p : ℕ) : Fin (m + 2 * k * (m * m)) :=
  if h : p ≤ 2 * k + 1 then ⟨ptv m k u.val v.val p, ptv_lt u.isLt v.isLt h⟩
  else ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩

private theorem pt_val {m k : ℕ} (u v : Fin m) {p : ℕ} (hp : p ≤ 2 * k + 1) :
    (pt m k u v p).val = ptv m k u.val v.val p := by
  unfold pt
  simp [hp]

private theorem q_iff {m k : ℕ} (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (hQ : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p))
    (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))) (hp : p ≤ 2 * k + 1) :
    Q u v p x ↔ x = pt m k u v p := by
  rw [hQ, Fin.ext_iff, pt_val u v hp]
  have c := ptv_cases m k u.val v.val p hp
  constructor
  · intro h
    omega
  · intro h
    omega

private def arcs {m : ℕ} (H : SimpleGraph (Fin m)) : Set (Fin m × Fin m) :=
  {q | q.1 < q.2 ∧ H.Adj q.1 q.2}

private def pairOf {m : ℕ} (q : Fin m × Fin m) : Sym2 (Fin m) :=
  s(q.1, q.2)

private def edgeOf (m k : ℕ) (t : (Fin m × Fin m) × ℕ) : Sym2 (Fin (m + 2 * k * (m * m))) :=
  s(pt m k t.1.1 t.1.2 t.2, pt m k t.1.1 t.1.2 (t.2 + 1))

private theorem edgeSet_eq {m : ℕ} (H : SimpleGraph (Fin m)) : H.edgeSet = pairOf '' arcs H := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · intro hxy
      rcases lt_or_gt_of_ne (H.ne_of_adj hxy) with hlt | hgt
      · exact ⟨(x, y), ⟨hlt, hxy⟩, rfl⟩
      · exact ⟨(y, x), ⟨hgt, hxy.symm⟩, Sym2.eq_swap⟩
    · rintro ⟨⟨a, b⟩, ⟨-, hab⟩, he⟩
      have he2 : s(a, b) = s(x, y) := he
      rw [Sym2.eq_iff] at he2
      rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]
        exact hab
      · rw [← h1, ← h2]
        exact hab.symm

private theorem pairOf_injOn {m : ℕ} (H : SimpleGraph (Fin m)) : Set.InjOn pairOf (arcs H) := by
  rintro ⟨a, b⟩ ⟨hab, -⟩ ⟨c, d⟩ ⟨hcd, -⟩ he
  have he2 : s(a, b) = s(c, d) := he
  rw [Sym2.eq_iff] at he2
  rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · exfalso
    have h3 : a < b := hab
    have h4 : c < d := hcd
    rw [h1, h2] at h3
    exact lt_asymm h3 h4

private theorem edgeOf_injOn {m k : ℕ} (hk : 1 ≤ k) (H : SimpleGraph (Fin m)) :
    Set.InjOn (edgeOf m k) (arcs H ×ˢ ((Finset.range (2 * k + 1) : Finset ℕ) : Set ℕ)) := by
  rintro ⟨⟨u, v⟩, p⟩ ⟨-, hp⟩ ⟨⟨c, d⟩, q⟩ ⟨-, hq⟩ he
  have hp1 : p < 2 * k + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hp)
  have hq1 : q < 2 * k + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hq)
  have he2 : s(pt m k u v p, pt m k u v (p + 1)) = s(pt m k c d q, pt m k c d (q + 1)) := he
  rw [Sym2.eq_iff] at he2
  have hkey : u.val = c.val ∧ v.val = d.val ∧ p = q := by
    apply key hk u.isLt v.isLt c.isLt d.isLt (by omega) (by omega)
    rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      rw [pt_val u v (by omega), pt_val c d (by omega)] at e1
      rw [pt_val u v (by omega), pt_val c d (by omega)] at e2
      exact ⟨e1, e2⟩
    · right
      have e1 := congrArg Fin.val h1
      have e2 := congrArg Fin.val h2
      rw [pt_val u v (by omega), pt_val c d (by omega)] at e1
      rw [pt_val u v (by omega), pt_val c d (by omega)] at e2
      exact ⟨e1, e2⟩
  obtain ⟨h1, h2, h3⟩ := hkey
  have hu : u = c := Fin.ext h1
  have hv : v = d := Fin.ext h2
  rw [hu, hv, h3]

end PEqualNP.Outside.Aux295

theorem PEqualNP.Outside.L_meta_295 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard := by
  intro m k H Q S hk hQ hS
  have hAdj : ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧
      ∃ p : ℕ, p ≤ 2 * k ∧ ((x = Aux295.pt m k u v p ∧ y = Aux295.pt m k u v (p + 1)) ∨
        (y = Aux295.pt m k u v p ∧ x = Aux295.pt m k u v (p + 1))) := by
    intro x y
    rw [hS]
    constructor
    · rintro ⟨u, v, huv, hH, p, hp, h⟩
      refine ⟨u, v, huv, hH, p, hp, ?_⟩
      rw [Aux295.q_iff Q hQ u v p x (by omega), Aux295.q_iff Q hQ u v (p + 1) y (by omega),
        Aux295.q_iff Q hQ u v p y (by omega), Aux295.q_iff Q hQ u v (p + 1) x (by omega)] at h
      exact h
    · rintro ⟨u, v, huv, hH, p, hp, h⟩
      refine ⟨u, v, huv, hH, p, hp, ?_⟩
      rw [Aux295.q_iff Q hQ u v p x (by omega), Aux295.q_iff Q hQ u v (p + 1) y (by omega),
        Aux295.q_iff Q hQ u v p y (by omega), Aux295.q_iff Q hQ u v (p + 1) x (by omega)]
      exact h
  have hE : S.edgeSet = Aux295.edgeOf m k ''
      (Aux295.arcs H ×ˢ ((Finset.range (2 * k + 1) : Finset ℕ) : Set ℕ)) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      rw [SimpleGraph.mem_edgeSet, hAdj]
      constructor
      · rintro ⟨u, v, huv, hH, p, hp, h⟩
        refine ⟨((u, v), p), ⟨⟨huv, hH⟩, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))⟩, ?_⟩
        have goal2 : s(Aux295.pt m k u v p, Aux295.pt m k u v (p + 1)) = s(x, y) := by
          rw [Sym2.eq_iff]
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1.symm, h2.symm⟩
          · exact Or.inr ⟨h1.symm, h2.symm⟩
        exact goal2
      · rintro ⟨⟨⟨u, v⟩, p⟩, ⟨⟨huv, hH⟩, hp⟩, he⟩
        have hp1 : p < 2 * k + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hp)
        have he2 : s(Aux295.pt m k u v p, Aux295.pt m k u v (p + 1)) = s(x, y) := he
        rw [Sym2.eq_iff] at he2
        refine ⟨u, v, huv, hH, p, by omega, ?_⟩
        rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h1.symm, h2.symm⟩
  rw [hE, (Aux295.edgeOf_injOn hk H).ncard_image, Set.ncard_prod, Set.ncard_coe_finset,
    Finset.card_range, Aux295.edgeSet_eq H, (Aux295.pairOf_injOn H).ncard_image]
  ring
