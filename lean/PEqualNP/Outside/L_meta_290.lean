import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private lemma hq_lt {m : ℕ} (u v : Fin m) : u.val * m + v.val < m * m := by
  have hu : u.val < m := u.isLt
  have hv : v.val < m := v.isLt
  calc
    u.val * m + v.val < u.val * m + m := Nat.add_lt_add_left hv _
    _ = (u.val + 1) * m := by ring
    _ ≤ m * m := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hu)

private lemma idx_lt {m k : ℕ} (u v : Fin m) (i : Fin (2 * k)) :
    m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m := by
  have hq : u.val * m + v.val < m * m := hq_lt u v
  have h1 : 2 * k * (u.val * m + v.val) + i.val <
      2 * k * (u.val * m + v.val) + 2 * k := Nat.add_lt_add_left i.isLt _
  have h2 : 2 * k * (u.val * m + v.val) + 2 * k =
      2 * k * ((u.val * m + v.val) + 1) := by ring
  have h3 : (u.val * m + v.val) + 1 ≤ m * m := by omega
  have h4 : 2 * k * ((u.val * m + v.val) + 1) ≤ 2 * k * (m * m) :=
    Nat.mul_le_mul_left (2 * k) h3
  rw [h2] at h1
  have key : 2 * k * (u.val * m + v.val) + i.val < 2 * k * (m * m) :=
    lt_of_lt_of_le h1 h4
  calc
    m + 2 * k * (u.val * m + v.val) + i.val
        = m + (2 * k * (u.val * m + v.val) + i.val) := by ring
    _ < m + 2 * k * (m * m) := Nat.add_lt_add_left key m
    _ = m + 2 * k * m * m := by ring

private def orig {m k : ℕ} (u : Fin m) : Fin (m + 2 * k * m * m) :=
  ⟨u.val, by have := u.isLt; omega⟩

private def idx {m k : ℕ} (p : Fin m × Fin m) (i : Fin (2 * k)) :
    Fin (m + 2 * k * m * m) :=
  ⟨m + 2 * k * (p.1.val * m + p.2.val) + i.val, idx_lt p.1 p.2 i⟩

private lemma idx_inj {m k : ℕ} {p : Fin m × Fin m} {i j : Fin (2 * k)}
    (h : idx p i = idx p j) : i = j := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [idx] at hv
  omega

private lemma orig_ne_idx {m k : ℕ} (u : Fin m) (p : Fin m × Fin m) (i : Fin (2 * k)) :
    orig (k := k) u ≠ idx p i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [orig, idx] at hv
  have hu : u.val < m := u.isLt
  omega

private lemma idx_ne_orig {m k : ℕ} (p : Fin m × Fin m) (i : Fin (2 * k)) (u : Fin m) :
    idx p i ≠ orig (k := k) u := fun h => orig_ne_idx u p i h.symm

private lemma orig_inj {m k : ℕ} {u v : Fin m} (h : orig (k := k) u = orig (k := k) v) :
    u = v := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [orig] using hv

private lemma idx_ne_of_val_ne {m k : ℕ} {p : Fin m × Fin m} {i j : Fin (2 * k)}
    (h : i.val ≠ j.val) : idx p i ≠ idx p j :=
  fun hh => h (congrArg Fin.val (idx_inj hh))

private lemma mul_add_cancel {c a b i j : ℕ} (hc : 0 < c) (hi : i < c) (hj : j < c)
    (h : a * c + i = b * c + j) : a = b ∧ i = j := by
  have h' : c * a + i = c * b + j := by
    rw [Nat.mul_comm c a, Nat.mul_comm c b]
    exact h
  have ha : (c * a + i) / c = a := by
    rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hi]
    simp
  have hb : (c * b + j) / c = b := by
    rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hj]
    simp
  have hab : a = b := by rw [← ha, ← hb, h']
  subst hab
  exact ⟨rfl, by omega⟩

private lemma pair_eq_of_q_eq {m : ℕ} (hm : 0 < m) {u v u' v' : Fin m}
    (h : u.val * m + v.val = u'.val * m + v'.val) : u = u' ∧ v = v' := by
  obtain ⟨hu, hv⟩ := mul_add_cancel (c := m) (a := u.val) (b := u'.val)
    (i := v.val) (j := v'.val) hm v.isLt v'.isLt h
  exact ⟨Fin.ext hu, Fin.ext hv⟩

private def blk {m k : ℕ} (p : Fin m × Fin m) : Finset (Fin (m + 2 * k * m * m)) :=
  (Finset.univ : Finset (Fin (2 * k))).image (fun i => idx p i)

private lemma mem_blk {m k : ℕ} {p : Fin m × Fin m} {x : Fin (m + 2 * k * m * m)} :
    x ∈ blk p ↔ ∃ i : Fin (2 * k), idx p i = x := by
  simp [blk]

private lemma blk_val_ge {m k : ℕ} {p : Fin m × Fin m} {x : Fin (m + 2 * k * m * m)}
    (hx : x ∈ blk p) : m ≤ x.val := by
  rw [mem_blk] at hx
  obtain ⟨i, rfl⟩ := hx
  simp only [idx]
  omega

private lemma blk_disjoint {m k : ℕ} (hk : 0 < k) (hm : 0 < m)
    {p q : Fin m × Fin m} (hpq : p ≠ q) :
    Disjoint (blk (k := k) p) (blk (k := k) q) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [mem_blk] at hx hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, hji⟩ := hy
  have hv : (q.1.val * m + q.2.val) * (2 * k) + j.val =
      (p.1.val * m + p.2.val) * (2 * k) + i.val := by
    have h := congrArg Fin.val hji
    simp only [idx] at h
    rw [Nat.mul_comm (2 * k) (q.1.val * m + q.2.val),
      Nat.mul_comm (2 * k) (p.1.val * m + p.2.val)] at h
    omega
  obtain ⟨hq, -⟩ := mul_add_cancel (c := 2 * k)
    (a := q.1.val * m + q.2.val) (b := p.1.val * m + p.2.val)
    (i := j.val) (j := i.val) (by omega) j.isLt i.isLt hv
  obtain ⟨h1, h2⟩ := pair_eq_of_q_eq hm hq
  exact hpq (Prod.ext h1.symm h2.symm)

private def rel {m k : ℕ} (H : SimpleGraph (Fin m))
    (x y : Fin (m + 2 * k * m * m)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
    x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
      ((i.val = 0 ∧ y.val = u.val) ∨
       (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
       (i.val + 1 = 2 * k ∧ y.val = v.val))

private def eIdx {k : ℕ} (j : Fin k) : Fin (2 * k) := ⟨2 * j.val, by omega⟩

private def oIdx {k : ℕ} (j : Fin k) : Fin (2 * k) := ⟨2 * j.val + 1, by omega⟩

private def mF {k : ℕ} (j : Fin (k - 1)) : Fin (2 * k) := ⟨2 * j.val + 1, by omega⟩

private def mG {k : ℕ} (j : Fin (k - 1)) : Fin (2 * k) := ⟨2 * j.val + 2, by omega⟩

private def zIdx {k : ℕ} (hk : 0 < k) : Fin (2 * k) := ⟨0, by omega⟩

private def lIdx {k : ℕ} (hk : 0 < k) : Fin (2 * k) := ⟨2 * k - 1, by omega⟩

private lemma adj_step {m k : ℕ} {H : SimpleGraph (Fin m)} {p : Fin m × Fin m}
    (hp : p.1 < p.2) (hE : H.Adj p.1 p.2) (i : Fin (2 * k))
    (h : i.val + 1 < 2 * k) :
    (SimpleGraph.fromRel (rel H)).Adj (idx p i) (idx p ⟨i.val + 1, h⟩) := by
  refine ⟨?_, Or.inl ⟨p.1, p.2, hp, hE, i, rfl, Or.inr (Or.inl ⟨h, ?_⟩)⟩⟩
  · intro he
    have hv := congrArg Fin.val he
    simp only [idx] at hv
    omega
  · simp only [idx]
    ring

private lemma adj_even_odd {m k : ℕ} {H : SimpleGraph (Fin m)} {p : Fin m × Fin m}
    (hp : p.1 < p.2) (hE : H.Adj p.1 p.2) (j : Fin k) :
    (SimpleGraph.fromRel (rel H)).Adj (idx p (eIdx j)) (idx p (oIdx j)) := by
  refine ⟨?_, Or.inl ⟨p.1, p.2, hp, hE, eIdx j, rfl, Or.inr (Or.inl ⟨?_, ?_⟩)⟩⟩
  · intro he
    have hv := congrArg Fin.val he
    simp only [idx, eIdx, oIdx] at hv
    omega
  · simp only [eIdx, oIdx]
    omega
  · simp only [idx, eIdx, oIdx]
    ring

private lemma adj_mid {m k : ℕ} {H : SimpleGraph (Fin m)} {p : Fin m × Fin m}
    (hp : p.1 < p.2) (hE : H.Adj p.1 p.2) (j : Fin (k - 1)) :
    (SimpleGraph.fromRel (rel H)).Adj (idx p (mF j)) (idx p (mG j)) := by
  refine ⟨?_, Or.inl ⟨p.1, p.2, hp, hE, mF j, rfl, Or.inr (Or.inl ⟨?_, ?_⟩)⟩⟩
  · intro he
    have hv := congrArg Fin.val he
    simp only [idx, mF, mG] at hv
    omega
  · simp only [mF]
    omega
  · simp only [idx, mF, mG]
    ring

private lemma adj_first {m k : ℕ} {H : SimpleGraph (Fin m)} {p : Fin m × Fin m}
    (hp : p.1 < p.2) (hE : H.Adj p.1 p.2) (hk : 0 < k) :
    (SimpleGraph.fromRel (rel H)).Adj (idx p (zIdx hk)) (orig (k := k) p.1) := by
  refine ⟨idx_ne_orig p _ p.1, Or.inl ⟨p.1, p.2, hp, hE, zIdx hk, rfl, Or.inl ⟨?_, ?_⟩⟩⟩
  · simp only [zIdx]
  · simp only [orig]

private lemma adj_last {m k : ℕ} {H : SimpleGraph (Fin m)} {p : Fin m × Fin m}
    (hp : p.1 < p.2) (hE : H.Adj p.1 p.2) (hk : 0 < k) :
    (SimpleGraph.fromRel (rel H)).Adj (idx p (lIdx hk)) (orig (k := k) p.2) := by
  refine ⟨idx_ne_orig p _ p.2, Or.inl ⟨p.1, p.2, hp, hE, lIdx hk, rfl,
    Or.inr (Or.inr ⟨?_, ?_⟩)⟩⟩
  · simp only [lIdx]
    omega
  · simp only [orig]

private lemma card_le_pick {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι]
    (U : Finset α) (f g : ι → α)
    (hU : ∀ i, f i ∈ U ∨ g i ∈ U)
    (hdisj : ∀ i j, i ≠ j →
      f i ≠ f j ∧ f i ≠ g j ∧ g i ≠ f j ∧ g i ≠ g j) :
    Fintype.card ι ≤ U.card := by
  classical
  let pick : ι → α := fun i => if f i ∈ U then f i else g i
  have hpick : ∀ i, pick i ∈ U := by
    intro i
    dsimp only [pick]
    split_ifs with h
    · exact h
    · exact (hU i).resolve_left h
  have hinj : Function.Injective pick := by
    intro i j hij
    by_contra hne
    obtain ⟨hff, hfg, hgf, hgg⟩ := hdisj i j hne
    dsimp only [pick] at hij
    split_ifs at hij with hi hj
    · exact hff hij
    · exact hfg hij
    · exact hgf hij
    · exact hgg hij
  have hsub : (Finset.univ.image pick) ⊆ U := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact hpick i
  have hcard : (Finset.univ.image pick).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hle := Finset.card_le_card hsub
  omega

private lemma block_lower_k {m k : ℕ} {H : SimpleGraph (Fin m)} {p : Fin m × Fin m}
    (hp : p.1 < p.2) (hE : H.Adj p.1 p.2) {U : Finset (Fin (m + 2 * k * m * m))}
    (hU : ∀ x y, (SimpleGraph.fromRel (rel H)).Adj x y → x ∈ U ∨ y ∈ U) :
    k ≤ (U ∩ blk (k := k) p).card := by
  let f : Fin k → Fin (m + 2 * k * m * m) := fun j => idx p (eIdx j)
  let g : Fin k → Fin (m + 2 * k * m * m) := fun j => idx p (oIdx j)
  have hU' : ∀ j, f j ∈ U ∩ blk (k := k) p ∨ g j ∈ U ∩ blk (k := k) p := by
    intro j
    rcases hU _ _ (adj_even_odd (k := k) hp hE j) with h | h
    · exact Or.inl (Finset.mem_inter.mpr ⟨h, mem_blk.mpr ⟨eIdx j, rfl⟩⟩)
    · exact Or.inr (Finset.mem_inter.mpr ⟨h, mem_blk.mpr ⟨oIdx j, rfl⟩⟩)
  have hdisj : ∀ i j : Fin k, i ≠ j →
      f i ≠ f j ∧ f i ≠ g j ∧ g i ≠ f j ∧ g i ≠ g j := by
    intro i j hij
    have hvne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact idx_ne_of_val_ne (by simp only [eIdx]; omega)
    · exact idx_ne_of_val_ne (by simp only [f, g, eIdx, oIdx]; omega)
    · exact idx_ne_of_val_ne (by simp only [f, g, eIdx, oIdx]; omega)
    · exact idx_ne_of_val_ne (by simp only [g, oIdx]; omega)
  have hmain := card_le_pick (U ∩ blk (k := k) p) f g hU' hdisj
  simpa using hmain

private lemma block_lower_both {m k : ℕ} {H : SimpleGraph (Fin m)} {p : Fin m × Fin m}
    (hp : p.1 < p.2) (hE : H.Adj p.1 p.2) {U : Finset (Fin (m + 2 * k * m * m))}
    (hU : ∀ x y, (SimpleGraph.fromRel (rel H)).Adj x y → x ∈ U ∨ y ∈ U)
    (h0 : orig (k := k) p.1 ∉ U) (h1 : orig (k := k) p.2 ∉ U) (hk : 0 < k) :
    k + 1 ≤ (U ∩ blk (k := k) p).card := by
  have hz : idx p (zIdx hk) ∈ U :=
    (hU _ _ (adj_first (k := k) hp hE hk)).resolve_right h0
  have hl : idx p (lIdx hk) ∈ U :=
    (hU _ _ (adj_last (k := k) hp hE hk)).resolve_right h1
  let f : Fin (k - 1) ⊕ Bool → Fin (m + 2 * k * m * m) := fun x =>
    match x with
    | Sum.inl j => idx p (mF j)
    | Sum.inr b => if b then idx p (lIdx hk) else idx p (zIdx hk)
  let g : Fin (k - 1) ⊕ Bool → Fin (m + 2 * k * m * m) := fun x =>
    match x with
    | Sum.inl j => idx p (mG j)
    | Sum.inr b => if b then idx p (lIdx hk) else idx p (zIdx hk)
  have hU' : ∀ x, f x ∈ U ∩ blk (k := k) p ∨ g x ∈ U ∩ blk (k := k) p := by
    intro x
    match x with
    | Sum.inl j =>
      rcases hU _ _ (adj_mid (k := k) hp hE j) with h | h
      · exact Or.inl (Finset.mem_inter.mpr ⟨h, mem_blk.mpr ⟨mF j, rfl⟩⟩)
      · exact Or.inr (Finset.mem_inter.mpr ⟨h, mem_blk.mpr ⟨mG j, rfl⟩⟩)
    | Sum.inr b =>
      cases b
      · exact Or.inl (Finset.mem_inter.mpr ⟨hz, mem_blk.mpr ⟨zIdx hk, rfl⟩⟩)
      · exact Or.inr (Finset.mem_inter.mpr ⟨hl, mem_blk.mpr ⟨lIdx hk, rfl⟩⟩)
  have hdisj : ∀ x y : Fin (k - 1) ⊕ Bool, x ≠ y →
      f x ≠ f y ∧ f x ≠ g y ∧ g x ≠ f y ∧ g x ≠ g y := by
    intro x y hxy
    match x, y with
    | Sum.inl i, Sum.inl j =>
      have hvne : i.val ≠ j.val := by
        intro h
        exact hxy (by rw [Fin.ext h])
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        exact idx_ne_of_val_ne (by simp only [f, g, mF, mG]; omega)
    | Sum.inl i, Sum.inr b =>
      cases b
      · refine ⟨?_, ?_, ?_, ?_⟩ <;>
          exact idx_ne_of_val_ne (by simp only [f, g, mF, mG, zIdx]; omega)
      · refine ⟨?_, ?_, ?_, ?_⟩ <;>
          exact idx_ne_of_val_ne (by simp only [f, g, mF, mG, lIdx]; omega)
    | Sum.inr b, Sum.inl j =>
      cases b
      · refine ⟨?_, ?_, ?_, ?_⟩ <;>
          exact idx_ne_of_val_ne (by simp only [f, g, mF, mG, zIdx]; omega)
      · refine ⟨?_, ?_, ?_, ?_⟩ <;>
          exact idx_ne_of_val_ne (by simp only [f, g, mF, mG, lIdx]; omega)
    | Sum.inr false, Sum.inr false => exact absurd rfl hxy
    | Sum.inr true, Sum.inr true => exact absurd rfl hxy
    | Sum.inr false, Sum.inr true =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        exact idx_ne_of_val_ne (by simp only [zIdx, lIdx]; omega)
    | Sum.inr true, Sum.inr false =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        exact idx_ne_of_val_ne (by simp only [zIdx, lIdx]; omega)
  have hmain := card_le_pick (U ∩ blk (k := k) p) f g hU' hdisj
  have hc : Fintype.card (Fin (k - 1) ⊕ Bool) = k + 1 := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool]
    omega
  omega


private noncomputable def pairEdges {m : ℕ} (H : SimpleGraph (Fin m)) : Finset (Fin m × Fin m) :=
  by classical exact Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)

private lemma pairEdges_card {m : ℕ} (H : SimpleGraph (Fin m)) :
    (pairEdges H).card = H.edgeSet.ncard := by
  classical
  letI : Fintype H.edgeSet := Fintype.ofFinite H.edgeSet
  have h1 : (pairEdges H).card = H.edgeFinset.card := by
    refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
    · intro p hp
      rw [pairEdges, Finset.mem_filter] at hp
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hp.2.2
    · intro p hp q hq hpq
      rw [pairEdges, Finset.mem_filter] at hp hq
      rw [Sym2.eq_iff] at hpq
      rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · have hp1 : p.1 < p.2 := hp.2.1
        have hq1 : q.1 < q.2 := hq.2.1
        omega
    · intro e he
      revert he
      refine Sym2.ind (f := fun x => x ∈ H.edgeFinset →
        ∃ p, ∃ _ : p ∈ pairEdges H, s(p.1, p.2) = x) ?_ e
      intro a b he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      have hne : a ≠ b := H.ne_of_adj he
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨(a, b), ?_, ?_⟩
        · rw [pairEdges, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hlt, he⟩
        · rfl
      · refine ⟨(b, a), ?_, ?_⟩
        · rw [pairEdges, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hgt, he.symm⟩
        · rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩
  have h2 : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  omega


theorem L_meta_290 : ∀ (k m c : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → (∀ T : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → c ≤ T.card) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro k m c H hk hcov S hS U hU
  rw [hS] at hU
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · haveI : Fintype H.edgeSet := Fintype.ofFinite H.edgeSet
    have hc0 : c = 0 := by
      have hle : c ≤ (∅ : Finset (Fin 0)).card := by
        apply hcov
        intro u v huv
        exact u.elim0
      simpa using hle
    subst hc0
    have hEempty : H.edgeFinset = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      intro hne
      obtain ⟨e, he⟩ := hne
      revert he
      refine Sym2.ind (fun a b he => ?_) e
      exact a.elim0
    have hE0 : H.edgeSet.ncard = 0 := by
      have h2 : H.edgeSet.ncard = H.edgeFinset.card := by
        rw [Set.ncard_eq_toFinset_card']
        rfl
      rw [h2, hEempty]
      simp
    rw [hE0]
    omega
  have hkpos : 0 < k := hk
  let o : Fin m → Fin (m + 2 * k * m * m) := fun u => orig (k := k) u
  let A : Finset (Fin m) := Finset.univ.filter (fun u => o u ∈ U)
  let P : Finset (Fin m × Fin m) := pairEdges H
  let D : Finset (Fin m × Fin m) := P.filter (fun p => p.1 ∉ A ∧ p.2 ∉ A)
  let Orig : Finset (Fin (m + 2 * k * m * m)) := U.filter (fun x => x.val < m)
  have ho_inj : Function.Injective o := fun a b h => orig_inj h
  have hOrig_eq : Orig = A.image o := by
    ext x
    constructor
    · intro hx
      simp only [Orig, Finset.mem_filter] at hx
      obtain ⟨hxU, hxm⟩ := hx
      refine Finset.mem_image.mpr ⟨⟨x.val, hxm⟩, ?_, ?_⟩
      · have hox : o ⟨x.val, hxm⟩ = x := by
          apply Fin.ext
          simp [o, orig]
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hox]
        exact hxU
      · apply Fin.ext
        simp [o, orig]
    · intro hx
      rw [Finset.mem_image] at hx
      obtain ⟨u, huA, rfl⟩ := hx
      simp only [Orig, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at huA
        exact huA
      · simp [o, orig]
  have hOrig_card : Orig.card = A.card := by
    rw [hOrig_eq]
    exact Finset.card_image_of_injective _ ho_inj
  have hmemP : ∀ p : Fin m × Fin m, p ∈ P ↔ p.1 < p.2 ∧ H.Adj p.1 p.2 := by
    intro p
    simp only [P, pairEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmemD : ∀ p : Fin m × Fin m, p ∈ D ↔ p ∈ P ∧ p.1 ∉ A ∧ p.2 ∉ A := by
    intro p
    simp only [D, Finset.mem_filter, and_assoc]
  have hTcover : ∀ u v : Fin m, H.Adj u v →
      u ∈ A ∪ D.image (fun p => p.1) ∨ v ∈ A ∪ D.image (fun p => p.1) := by
    intro u v huv
    by_cases hu : u ∈ A
    · exact Or.inl (Finset.mem_union_left _ hu)
    by_cases hv : v ∈ A
    · exact Or.inr (Finset.mem_union_left _ hv)
    · have hne : u ≠ v := H.ne_of_adj huv
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpP : (u, v) ∈ P := (hmemP (u, v)).mpr ⟨hlt, huv⟩
        have hpD : (u, v) ∈ D := (hmemD (u, v)).mpr ⟨hpP, hu, hv⟩
        exact Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(u, v), hpD, rfl⟩))
      · have hpP : (v, u) ∈ P := (hmemP (v, u)).mpr ⟨hgt, huv.symm⟩
        have hpD : (v, u) ∈ D := (hmemD (v, u)).mpr ⟨hpP, hv, hu⟩
        exact Or.inr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v, u), hpD, rfl⟩))
  have hcT : c ≤ (A ∪ D.image (fun p => p.1)).card := hcov _ hTcover
  have hTcard : (A ∪ D.image (fun p => p.1)).card ≤ A.card + D.card := by
    have h1 := Finset.card_union_le A (D.image (fun p => p.1))
    have h2 := Finset.card_image_le (s := D) (f := fun p : Fin m × Fin m => p.1)
    omega
  have hcAD : c ≤ A.card + D.card := le_trans hcT hTcard
  have hblock : ∀ p ∈ P, k + (if p ∈ D then 1 else 0) ≤
      (U ∩ blk (k := k) p).card := by
    intro p hpP
    have hp : p.1 < p.2 := ((hmemP p).mp hpP).1
    have hE : H.Adj p.1 p.2 := ((hmemP p).mp hpP).2
    by_cases hpD : p ∈ D
    · have hnotA1 : p.1 ∉ A := ((hmemD p).mp hpD).2.1
      have hnotA2 : p.2 ∉ A := ((hmemD p).mp hpD).2.2
      have ho1 : orig (k := k) p.1 ∉ U := fun h => hnotA1 (by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h)
      have ho2 : orig (k := k) p.2 ∉ U := fun h => hnotA2 (by
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h)
      have hb := block_lower_both hp hE hU ho1 ho2 hkpos
      simpa [hpD] using hb
    · have hb := block_lower_k hp hE hU
      simpa [hpD] using hb
  have hsum_le : ∑ p ∈ P, (k + (if p ∈ D then 1 else 0)) ≤
      ∑ p ∈ P, (U ∩ blk (k := k) p).card := Finset.sum_le_sum hblock
  have hsum_val : ∑ p ∈ P, (k + (if p ∈ D then 1 else 0)) = k * P.card + D.card := by
    rw [Finset.sum_add_distrib]
    have hPk : ∑ p ∈ P, k = k * P.card := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    have hDc : ∑ p ∈ P, (if p ∈ D then 1 else 0) = D.card := by
      rw [Finset.sum_boole]
      have hPD : P.filter (fun p => p ∈ D) = D := by
        ext p
        rw [Finset.mem_filter]
        constructor
        · rintro ⟨-, hpD⟩
          exact hpD
        · intro hpD
          exact ⟨((hmemD p).mp hpD).1, hpD⟩
      rw [hPD]
      simp
    rw [hPk, hDc]
  have hsum_lower : k * P.card + D.card ≤
      ∑ p ∈ P, (U ∩ blk (k := k) p).card := by
    rw [← hsum_val]
    exact hsum_le
  let W : Finset (Fin (m + 2 * k * m * m)) :=
    Orig ∪ P.biUnion (fun p => U ∩ blk (k := k) p)
  have hWsub : W ⊆ U := by
    intro x hx
    simp only [W, Finset.mem_union] at hx
    rcases hx with hx | hx
    · simp only [Orig, Finset.mem_filter] at hx
      exact hx.1
    · rw [Finset.mem_biUnion] at hx
      obtain ⟨p, -, hxp⟩ := hx
      exact (Finset.mem_inter.mp hxp).1
  have hdisj_orig : Disjoint Orig (P.biUnion (fun p => U ∩ blk (k := k) p)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Orig, Finset.mem_filter] at hx
    rw [Finset.mem_biUnion] at hy
    obtain ⟨p, -, hxp⟩ := hy
    have hge : m ≤ x.val := blk_val_ge (Finset.mem_inter.mp hxp).2
    omega
  have hpd : (↑P : Set (Fin m × Fin m)).PairwiseDisjoint
      (fun p => U ∩ blk (k := k) p) := by
    intro p hp q hq hpq
    change Disjoint (U ∩ blk (k := k) p) (U ∩ blk (k := k) q)
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.disjoint_left.mp (blk_disjoint hkpos hm hpq)
      (Finset.mem_inter.mp hx).2) (Finset.mem_inter.mp hy).2
  have hWcard : W.card = Orig.card + ∑ p ∈ P, (U ∩ blk (k := k) p).card := by
    simp only [W]
    rw [Finset.card_union_of_disjoint hdisj_orig, Finset.card_biUnion hpd]
  have hWle : W.card ≤ U.card := Finset.card_le_card hWsub
  have hlower : A.card + (k * P.card + D.card) ≤ U.card := by
    calc
      A.card + (k * P.card + D.card) = Orig.card + (k * P.card + D.card) := by
        rw [hOrig_card]
      _ ≤ Orig.card + ∑ p ∈ P, (U ∩ blk (k := k) p).card :=
        Nat.add_le_add_left hsum_lower _
      _ = W.card := by rw [hWcard]
      _ ≤ U.card := hWle
  have hPcard : P.card = H.edgeSet.ncard := by
    simpa [P] using pairEdges_card H
  rw [hPcard] at hlower
  omega


end PEqualNP.Outside
