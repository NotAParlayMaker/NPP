import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_289_aux

open Finset

/-- A set meeting every consecutive pair below `2 k` has at least `k` elements below `2 k`. -/
theorem pairs_k (k : ℕ) (T : Finset ℕ) (h : ∀ i, i + 1 < 2 * k → i ∈ T ∨ i + 1 ∈ T) :
    k ≤ (T.filter (· < 2 * k)).card := by
  classical
  let f : ℕ → ℕ := fun t => if 2 * t ∈ T then 2 * t else 2 * t + 1
  have hf : ∀ t ∈ range k, f t ∈ T.filter (· < 2 * k) := by
    intro t ht
    rw [mem_range] at ht
    simp only [f, mem_filter]
    split_ifs with h1
    · exact ⟨h1, by omega⟩
    · rcases h (2 * t) (by omega) with h2 | h2
      · exact absurd h2 h1
      · exact ⟨h2, by omega⟩
  have hinj : Set.InjOn f (range k) := by
    intro a _ b _ hab
    have ha : f a / 2 = a := by simp only [f]; split_ifs <;> omega
    have hb : f b / 2 = b := by simp only [f]; split_ifs <;> omega
    rw [← ha, ← hb, hab]
  simpa using card_le_card_of_injOn f hf hinj

/-- If also both ends `0` and `2 k - 1` are in the set, it has at least `k + 1` of them. -/
theorem pairs_k1 (k : ℕ) (hk : 1 ≤ k) (T : Finset ℕ)
    (h : ∀ i, i + 1 < 2 * k → i ∈ T ∨ i + 1 ∈ T) (h0 : 0 ∈ T) (hl : 2 * k - 1 ∈ T) :
    k + 1 ≤ (T.filter (· < 2 * k)).card := by
  classical
  let f : ℕ → ℕ := fun t =>
    if t = 0 then 0 else if t = k then 2 * k - 1 else if 2 * t - 1 ∈ T then 2 * t - 1 else 2 * t
  have hf : ∀ t ∈ range (k + 1), f t ∈ T.filter (· < 2 * k) := by
    intro t ht
    rw [mem_range] at ht
    simp only [f, mem_filter]
    split_ifs with h1 h2 h3
    · exact ⟨h0, by omega⟩
    · exact ⟨hl, by omega⟩
    · exact ⟨h3, by omega⟩
    · rcases h (2 * t - 1) (by omega) with h4 | h4
      · exact absurd h4 h3
      · exact ⟨by rwa [show 2 * t - 1 + 1 = 2 * t by omega] at h4, by omega⟩
  have hinj : Set.InjOn f (range (k + 1)) := by
    intro a ha b hb hab
    rw [coe_range, Set.mem_Iio] at ha hb
    have ga : (f a + 1) / 2 = a := by simp only [f]; split_ifs <;> omega
    have gb : (f b + 1) / 2 = b := by simp only [f]; split_ifs <;> omega
    rw [← ga, ← gb, hab]
  simpa using card_le_card_of_injOn f hf hinj

theorem code_lt (m : ℕ) (u v : Fin m) : u.val * m + v.val < m * m := by
  have hu := u.2
  have hv := v.2
  calc u.val * m + v.val < u.val * m + m := by omega
    _ = (u.val + 1) * m := by ring
    _ ≤ m * m := Nat.mul_le_mul_right _ hu

theorem block_lt (k m : ℕ) (u v : Fin m) (i : ℕ) (hi : i < 2 * k) :
    m + 2 * k * (u.val * m + v.val) + i < m + 2 * k * m * m := by
  have h := code_lt m u v
  have : 2 * k * (u.val * m + v.val) + 2 * k ≤ 2 * k * m * m := by
    calc 2 * k * (u.val * m + v.val) + 2 * k = 2 * k * (u.val * m + v.val + 1) := by ring
      _ ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ h
      _ = 2 * k * m * m := by ring
  omega

theorem code_inj (m : ℕ) (u v u' v' : Fin m) (h : u.val * m + v.val = u'.val * m + v'.val) :
    u = u' ∧ v = v' := by
  have hv := v.2
  have hv' := v'.2
  have h1 : (u.val * m + v.val) / m = u.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, zero_add]
  have h2 : (u'.val * m + v'.val) / m = u'.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv', zero_add]
  have hu : u.val = u'.val := by rw [← h1, ← h2, h]
  refine ⟨Fin.ext hu, Fin.ext ?_⟩
  rw [hu] at h
  omega

theorem edge_count (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    H.edgeSet.ncard = (univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)).card := by
  have hset : H.edgeSet = ((univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)).image
      (fun p => s(p.1, p.2)) : Finset (Sym2 (Fin m))) := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [SimpleGraph.mem_edgeSet, coe_image, coe_filter, mem_univ, true_and,
        Set.mem_image, Set.mem_setOf_eq, Prod.exists]
      constructor
      · intro hab
        rcases lt_trichotomy a b with h | h | h
        · exact ⟨a, b, ⟨h, hab⟩, rfl⟩
        · exact absurd h (H.ne_of_adj hab)
        · exact ⟨b, a, ⟨h, hab.symm⟩, Sym2.eq_swap⟩
      · rintro ⟨x, y, ⟨_, hxy⟩, he⟩
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxy
        · exact hxy.symm
  rw [hset, Set.ncard_coe_finset]
  apply card_image_of_injOn
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hab hcd
  rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exfalso
    subst h1; subst h2
    exact absurd (hab.1.trans hcd.1) (lt_irrefl _)

theorem div_code (k c y : ℕ) (hk : 1 ≤ k) (h1 : 2 * k * c ≤ y) (h2 : y < 2 * k * c + 2 * k) :
    y / (2 * k) = c := by
  apply Nat.div_eq_of_lt_le
  · rw [mul_comm]; exact h1
  · have : (c + 1) * (2 * k) = 2 * k * c + 2 * k := by ring
    rw [this]; exact h2


end PEqualNP.Outside.L_meta_289_aux

open PEqualNP.Outside.L_meta_289_aux Finset in
theorem PEqualNP.Outside.L_meta_289 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ U : Finset (Fin (m + 2 * k * m * m)), (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ U ∨ y ∈ U) → ∀ R : Finset (Fin m), (∀ u : Fin m, u ∈ R ↔ (∃ x ∈ U, x.val = u.val) ∨ ∃ v : Fin m, u < v ∧ H.Adj u v ∧ (∀ x ∈ U, x.val ≠ u.val) ∧ (∀ x ∈ U, x.val ≠ v.val)) → (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧ R.card + k * H.edgeSet.ncard ≤ U.card := by
  intro k m H hk S hS U hU R hR
  classical
  subst hS
  set Uv : Finset ℕ := U.image Fin.val with hUv
  have inUv : ∀ x ∈ U, x.val ∈ Uv := fun x hx => mem_image_of_mem _ hx
  have outUv : ∀ u : ℕ, (∀ x ∈ U, x.val ≠ u) ↔ u ∉ Uv := by
    intro u
    constructor
    · intro h hu
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hu
      exact h x hx rfl
    · intro h x hx e
      exact h (e ▸ inUv x hx)
  have firstUv : ∀ u : ℕ, (∃ x ∈ U, x.val = u) ↔ u ∈ Uv := by
    intro u; simp [hUv]
  -- the cover part
  have hcov : ∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R := by
    have one : ∀ u v : Fin m, u < v → H.Adj u v → u ∈ R ∨ v ∈ R := by
      intro u v huv hadj
      by_cases hu : u.val ∈ Uv
      · exact Or.inl ((hR u).2 (Or.inl ((firstUv _).2 hu)))
      · by_cases hv : v.val ∈ Uv
        · exact Or.inr ((hR v).2 (Or.inl ((firstUv _).2 hv)))
        · exact Or.inl ((hR u).2 (Or.inr ⟨v, huv, hadj, (outUv _).2 hu, (outUv _).2 hv⟩))
    intro u v hadj
    rcases lt_trichotomy u v with h | h | h
    · exact one u v h hadj
    · exact absurd h (H.ne_of_adj hadj)
    · exact (one v u h hadj.symm).symm
  refine ⟨hcov, ?_⟩
  -- the counting part
  set E : Finset (Fin m × Fin m) := univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2) with hE
  set E2 := E.filter (fun p => p.1.val ∉ Uv ∧ p.2.val ∉ Uv) with hE2
  let base : Fin m × Fin m → ℕ := fun p => m + 2 * k * (p.1.val * m + p.2.val)
  let block : Fin m × Fin m → Finset ℕ := fun p => Uv.filter (fun x => base p ≤ x ∧ x < base p + 2 * k)
  set O := Uv.filter (· < m) with hO
  -- each path meets `U` in at least `k` vertices, `k + 1` if both its ends are outside `U`
  have hblock : ∀ p ∈ E, k + (if p ∈ E2 then 1 else 0) ≤ (block p).card := by
    intro p hp
    obtain ⟨u, v⟩ := p
    have huv : u < v ∧ H.Adj u v := by simpa [hE] using hp
    let xv : (i : ℕ) → i < 2 * k → Fin (m + 2 * k * m * m) :=
      fun i hi => ⟨base (u, v) + i, block_lt k m u v i hi⟩
    have hne : ∀ (a b : Fin (m + 2 * k * m * m)), a.val ≠ b.val → a ≠ b :=
      fun a b h e => h (congrArg Fin.val e)
    set T := (range (2 * k)).filter (fun i => base (u, v) + i ∈ Uv) with hT
    have hpair : ∀ i, i + 1 < 2 * k → i ∈ T ∨ i + 1 ∈ T := by
      intro i hi
      have := hU (xv i (by omega)) (xv (i + 1) hi) (by
        rw [SimpleGraph.fromRel_adj]
        refine ⟨hne _ _ (by simp [xv]), Or.inl ⟨u, v, huv.1, huv.2, ⟨i, by omega⟩, rfl, ?_⟩⟩
        exact Or.inr (Or.inl ⟨hi, by simp [xv, base]; ring⟩))
      rcases this with h | h
      · exact Or.inl (by simpa [hT] using ⟨by omega, inUv _ h⟩)
      · exact Or.inr (by simpa [hT] using ⟨hi, inUv _ h⟩)
    have hTle : T.card ≤ (block (u, v)).card := by
      apply card_le_card_of_injOn (fun i => base (u, v) + i)
      · intro i hi
        have hi' := mem_filter.1 hi
        simp only [block]
        rw [mem_coe, mem_filter]
        exact ⟨hi'.2, by omega, by have := mem_range.1 hi'.1; omega⟩
      · intro a _ b _ e; simpa using e
    have hTk : (T.filter (· < 2 * k)).card ≤ T.card := card_filter_le _ _
    by_cases h2 : (u, v) ∈ E2
    · have hout : u.val ∉ Uv ∧ v.val ∉ Uv := (mem_filter.1 h2).2
      have h0 : 0 ∈ T := by
        have := hU (xv 0 (by omega)) ⟨u.val, by have := u.2; omega⟩ (by
          rw [SimpleGraph.fromRel_adj]
          refine ⟨hne _ _ (by simp [xv, base]; omega),
            Or.inl ⟨u, v, huv.1, huv.2, ⟨0, by omega⟩, by simp [xv, base], Or.inl ⟨rfl, rfl⟩⟩⟩)
        rcases this with h | h
        · simpa [hT] using ⟨by omega, inUv _ h⟩
        · exact absurd (inUv _ h) hout.1
      have hl : 2 * k - 1 ∈ T := by
        have := hU (xv (2 * k - 1) (by omega)) ⟨v.val, by have := v.2; omega⟩ (by
          rw [SimpleGraph.fromRel_adj]
          refine ⟨hne _ _ (by simp [xv, base]; omega),
            Or.inl ⟨u, v, huv.1, huv.2, ⟨2 * k - 1, by omega⟩, by simp [xv, base],
              Or.inr (Or.inr ⟨by simp; omega, rfl⟩)⟩⟩)
        rcases this with h | h
        · simpa [hT] using ⟨by omega, inUv _ h⟩
        · exact absurd (inUv _ h) hout.2
      have := pairs_k1 k hk T hpair h0 hl
      rw [if_pos h2]; omega
    · have := pairs_k k T hpair
      rw [if_neg h2]; omega
  -- the blocks and the original vertices are disjoint pieces of `Uv`
  have hdisjB : (E : Set (Fin m × Fin m)).PairwiseDisjoint block := by
    intro p _ q _ hpq
    rw [Function.onFun, disjoint_left]
    intro x hxp hxq
    simp only [block, mem_filter] at hxp hxq
    have c1 := div_code k (p.1.val * m + p.2.val) (x - m) hk (by
      have := hxp.2.1; simp only [base] at this; omega) (by
      have := hxp.2.2; have := hxp.2.1; simp only [base] at *; omega)
    have c2 := div_code k (q.1.val * m + q.2.val) (x - m) hk (by
      have := hxq.2.1; simp only [base] at this; omega) (by
      have := hxq.2.2; have := hxq.2.1; simp only [base] at *; omega)
    obtain ⟨e1, e2⟩ := code_inj m _ _ _ _ (c1.symm.trans c2)
    exact hpq (Prod.ext e1 e2)
  have hdisjO : Disjoint O (E.biUnion block) := by
    rw [disjoint_left]
    intro x hxO hxB
    obtain ⟨p, _, hx⟩ := mem_biUnion.1 hxB
    simp only [block, mem_filter, base] at hx
    have := (mem_filter.1 hxO).2
    omega
  have hsub : O ∪ E.biUnion block ⊆ Uv := by
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact (mem_filter.1 h).1
    · obtain ⟨p, _, hx⟩ := mem_biUnion.1 h
      exact (mem_filter.1 hx).1
  have hUcard : U.card = Uv.card := (card_image_of_injective _ Fin.val_injective).symm
  have hsum : O.card + ∑ p ∈ E, (block p).card ≤ U.card := by
    rw [hUcard, ← card_biUnion hdisjB, ← card_union_of_disjoint hdisjO]
    exact card_le_card hsub
  have hsum2 : E.card * k + E2.card ≤ ∑ p ∈ E, (block p).card := by
    calc E.card * k + E2.card = ∑ p ∈ E, (k + if p ∈ E2 then 1 else 0) := by
          rw [sum_add_distrib, sum_const, smul_eq_mul, ← card_filter]
          congr 2
          ext p; simp [hE2]
      _ ≤ _ := sum_le_sum hblock
  -- `R` is covered by the original vertices in `U` and one vertex per edge in `E2`
  have hR1 : (univ.filter (fun u : Fin m => u.val ∈ Uv)).card ≤ O.card := by
    apply card_le_card_of_injOn Fin.val
    · intro u hu
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hu
      simp [hO, hu]
    · intro a _ b _ e; exact Fin.ext e
  have hRsub : R ⊆ univ.filter (fun u : Fin m => u.val ∈ Uv) ∪ E2.image Prod.fst := by
    intro u hu
    rcases (hR u).1 hu with h | ⟨v, huv, hadj, hu', hv'⟩
    · exact mem_union_left _ (by simpa using (firstUv _).1 h)
    · refine mem_union_right _ (mem_image.2 ⟨(u, v), ?_, rfl⟩)
      simp [hE2, hE, huv, hadj, (outUv _).1 hu', (outUv _).1 hv']
  have hRcard : R.card ≤ O.card + E2.card := by
    calc R.card ≤ (univ.filter (fun u : Fin m => u.val ∈ Uv) ∪ E2.image Prod.fst).card :=
          card_le_card hRsub
      _ ≤ (univ.filter (fun u : Fin m => u.val ∈ Uv)).card + (E2.image Prod.fst).card :=
          card_union_le _ _
      _ ≤ O.card + E2.card := Nat.add_le_add hR1 card_image_le
  rw [edge_count m H]
  have : k * E.card = E.card * k := mul_comm _ _
  rw [← hE] at *
  linarith
