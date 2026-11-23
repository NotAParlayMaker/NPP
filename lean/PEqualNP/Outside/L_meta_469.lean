import Mathlib
import PEqualNP.Defs

theorem lmeta469_divmod (c a a' r r' : ℕ) (hr : r < c) (hr' : r' < c)
    (h : c * a + r = c * a' + r') : a = a' ∧ r = r' := by
  have hc : 0 < c := by omega
  have h1 := (Nat.div_mod_unique (a := c * a + r) (b := c) (c := r) (d := a) hc).2
    ⟨by ring, hr⟩
  have h2 := (Nat.div_mod_unique (a := c * a + r) (b := c) (c := r') (d := a') hc).2
    ⟨by rw [h]; ring, hr'⟩
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

theorem lmeta469_bound (m k u v r : ℕ) (hu : u < m) (hv : v < m) (hr : r < 2 * k) :
    m + 2 * k * (u * m + v) + r < m + 2 * k * (m * m) := by
  have h1 : u * m + v + 1 ≤ m * m := by
    calc u * m + v + 1 ≤ u * m + m := by omega
      _ = (u + 1) * m := by ring
      _ ≤ m * m := Nat.mul_le_mul_right _ hu
  have h2 : 2 * k * (u * m + v) + 2 * k ≤ 2 * k * (m * m) := by
    calc 2 * k * (u * m + v) + 2 * k = 2 * k * (u * m + v + 1) := by ring
      _ ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ h1
  omega

theorem lmeta469_edges (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)).card
      = H.edgeSet.ncard := by
  rw [← Set.ncard_coe_finset]
  have hset : H.edgeSet = (fun p : Fin m × Fin m => s(p.1, p.2)) ''
      (↑(Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)) :
        Set (Fin m × Fin m)) := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [SimpleGraph.mem_edgeSet, Set.mem_image, Finset.coe_filter,
        Finset.mem_univ, true_and, Set.mem_ofPred_eq, Prod.exists]
      constructor
      · intro hab
        rcases lt_trichotomy a b with h | h | h
        · exact ⟨a, b, ⟨h, hab⟩, rfl⟩
        · exact absurd h (H.ne_of_adj hab)
        · exact ⟨b, a, ⟨h, hab.symm⟩, Sym2.eq_swap⟩
      · rintro ⟨c, d, ⟨_, hcd⟩, heq⟩
        rw [← SimpleGraph.mem_edgeSet, ← heq]
        exact hcd
  rw [hset, Set.InjOn.ncard_image]
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hab hcd
  simp only [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · exfalso
    subst h1
    subst h2
    exact lt_asymm hab.1 hcd.1

theorem PEqualNP.Outside.L_meta_469 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → T'.card = T.card + k * H.edgeSet.ncard := by
  classical
  intro m k H T T' hT
  set E : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2) with hE
  have hEcard : E.card = H.edgeSet.ncard := lmeta469_edges m H
  have hb : ∀ u : Fin m, (if u ∈ T then 1 else 0) ≤ 1 := by
    intro u
    split_ifs <;> omega
  let g : (Fin m × Fin m) × Fin k → Fin (m + 2 * k * (m * m)) := fun q =>
    ⟨m + 2 * k * (q.1.1.val * m + q.1.2.val) + (2 * q.2.val + if q.1.1 ∈ T then 1 else 0),
      lmeta469_bound m k _ _ _ q.1.1.isLt q.1.2.isLt (by have := hb q.1.1; have := q.2.isLt; omega)⟩
  have hgval : ∀ q, (g q).val =
      m + 2 * k * (q.1.1.val * m + q.1.2.val) + (2 * q.2.val + if q.1.1 ∈ T then 1 else 0) :=
    fun q => rfl
  have hginj : Function.Injective g := by
    rintro ⟨⟨u, v⟩, j⟩ ⟨⟨u', v'⟩, j'⟩ heq
    have hv := congrArg Fin.val heq
    rw [hgval, hgval] at hv
    simp only at hv
    have hr : (2 * j.val + if u ∈ T then 1 else 0) < 2 * k := by
      have := hb u; have := j.isLt; omega
    have hr' : (2 * j'.val + if u' ∈ T then 1 else 0) < 2 * k := by
      have := hb u'; have := j'.isLt; omega
    obtain ⟨h1, h2⟩ := lmeta469_divmod (2 * k) (u.val * m + v.val) (u'.val * m + v'.val) _ _ hr hr' (by omega)
    have hm : 0 < m := by have := u.isLt; omega
    have hvm : v.val < m := v.isLt
    have hvm' : v'.val < m := v'.isLt
    obtain ⟨h3, h4⟩ := lmeta469_divmod m u.val u'.val v.val v'.val hvm hvm' (by
      rw [mul_comm m u.val, mul_comm m u'.val]; exact h1)
    have hu : u = u' := Fin.ext h3
    have hv' : v = v' := Fin.ext h4
    subst hu
    subst hv'
    have hj : j = j' := by
      apply Fin.ext
      split_ifs at h2 <;> omega
    rw [hj]
  have hle : m ≤ m + 2 * k * (m * m) := Nat.le_add_right _ _
  have hT'eq : T' = T.image (Fin.castLE hle) ∪ (E ×ˢ (Finset.univ : Finset (Fin k))).image g := by
    ext x
    rw [hT x, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (⟨u, hu, hx⟩ | ⟨u, v, i, hi, huv, hadj, hx, hpar⟩)
      · left
        exact ⟨u, hu, Fin.ext (by simp [hx])⟩
      · right
        refine ⟨⟨⟨u, v⟩, ⟨i / 2, by omega⟩⟩, ?_, ?_⟩
        · simp [hE, huv, hadj]
        · apply Fin.ext
          rw [hgval, hx]
          simp only
          split_ifs with hu
          · have := hpar.2 hu
            omega
          · have : ¬ i % 2 = 1 := fun h => hu (hpar.1 h)
            omega
    · rintro (⟨u, hu, hx⟩ | ⟨⟨⟨u, v⟩, j⟩, hq, hx⟩)
      · left
        exact ⟨u, hu, by rw [← hx]; simp⟩
      · right
        simp only [hE, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
          and_true] at hq
        refine ⟨u, v, 2 * j.val + (if u ∈ T then 1 else 0), ?_, hq.1, hq.2, ?_, ?_⟩
        · have := hb u; have := j.isLt; omega
        · rw [← hx, hgval]
        · split_ifs with hu
          · simp only [hu, iff_true]
            omega
          · simp only [hu, iff_false]
            omega
  have hdisj : Disjoint (T.image (Fin.castLE hle)) ((E ×ˢ (Finset.univ : Finset (Fin k))).image g) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_image] at hx1 hx2
    obtain ⟨u, _, hu⟩ := hx1
    obtain ⟨q, _, hq⟩ := hx2
    have h1 : x.val < m := by rw [← hu]; simp
    have h2 : m ≤ x.val := by rw [← hq, hgval]; omega
    omega
  rw [hT'eq, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (Fin.castLE_injective hle),
    Finset.card_image_of_injective _ hginj, Finset.card_product, Finset.card_univ,
    Fintype.card_fin, hEcard, mul_comm]
