import Mathlib
import PEqualNP.Defs

private lemma block_coordinates {width a b i j : ℕ} (hi : i < width) (hj : j < width)
    (h : width * a + i = width * b + j) : a = b ∧ i = j := by
  have separated {x y p q : ℕ} (hxy : x < y) (hp : p < width) :
      width * x + p < width * y + q := calc
    width * x + p < width * x + width := Nat.add_lt_add_left hp _
    _ = width * (x + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ width * y := Nat.mul_le_mul_left _ hxy
    _ ≤ width * y + q := by omega
  have hab : a = b := by
    rcases lt_trichotomy a b with hl | he | hg
    · exact ((separated (q := j) hl hi).ne h).elim
    · exact he
    · exact ((separated (q := i) hg hj).ne h.symm).elim
  exact ⟨hab, by rw [hab] at h; omega⟩

private lemma pair_code_lt {m : ℕ} (u v : Fin m) : u.val * m + v.val < m * m := calc
  u.val * m + v.val < u.val * m + m := Nat.add_lt_add_left v.isLt _
  _ = (u.val + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
  _ ≤ m * m := Nat.mul_le_mul_right _ u.isLt

private def path_vertex {r m : ℕ} (u v : Fin m) (j : ℕ) : Fin (m + r * m * m) :=
  if hz : j = 0 then ⟨u.val, by have := u.isLt; omega⟩
  else if he : r < j then ⟨v.val, by have := v.isLt; omega⟩
  else ⟨m + r * (u.val * m + v.val) + (j - 1), by
    have hcode : r * (u.val * m + v.val + 1) ≤ r * (m * m) :=
      Nat.mul_le_mul_left r (pair_code_lt u v)
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hcode
    omega⟩

private lemma path_vertex_first {r m : ℕ} (u v : Fin m) :
    (path_vertex (r := r) u v 0).val = u.val := by simp [path_vertex]

private lemma path_vertex_last {r m : ℕ} (u v : Fin m) :
    (path_vertex (r := r) u v (r + 1)).val = v.val := by
  simp [path_vertex, show r < r + 1 by omega]

private lemma path_vertex_inside {r m : ℕ} (u v : Fin m) {j : ℕ}
    (hj : 1 ≤ j) (hjr : j ≤ r) :
    (path_vertex (r := r) u v j).val = m + r * (u.val * m + v.val) + (j - 1) := by
  simp [path_vertex, show j ≠ 0 by omega, show ¬r < j by omega]

private lemma interior_match {r m : ℕ} {u v a b : Fin m} {i j : ℕ}
    (hi : 1 ≤ i ∧ i ≤ r) (hj : j ≤ r + 1)
    (he : path_vertex (r := r) u v i = path_vertex (r := r) a b j) :
    u = a ∧ v = b ∧ i = j := by
  have hv := congrArg Fin.val he
  rw [path_vertex_inside u v hi.1 hi.2] at hv
  by_cases hjz : j = 0
  · rw [hjz, path_vertex_first] at hv
    have := a.isLt
    omega
  by_cases hjl : j = r + 1
  · rw [hjl, path_vertex_last] at hv
    have := b.isLt
    omega
  rw [path_vertex_inside (r := r) a b (j := j) (by omega) (by omega)] at hv
  have h := block_coordinates (width := r) (i := i - 1) (j := j - 1)
    (by omega) (by omega) (by omega : r * (u.val * m + v.val) + (i - 1) =
      r * (a.val * m + b.val) + (j - 1))
  have hcode := h.1
  rw [Nat.mul_comm u.val m, Nat.mul_comm a.val m] at hcode
  have hpair := block_coordinates v.isLt b.isLt hcode
  exact ⟨Fin.ext hpair.1, Fin.ext hpair.2, by have := h.2; omega⟩

private lemma path_vertex_injective {r m : ℕ} {u v : Fin m} (huv : u < v)
    {i j : ℕ} (hi : i ≤ r + 1) (hj : j ≤ r + 1)
    (he : path_vertex (r := r) u v i = path_vertex (r := r) u v j) : i = j := by
  by_cases hi' : 1 ≤ i ∧ i ≤ r
  · exact (interior_match hi' hj he).2.2
  by_cases hj' : 1 ≤ j ∧ j ≤ r
  · exact (interior_match hj' hi he.symm).2.2.symm
  have hends_i : i = 0 ∨ i = r + 1 := by omega
  have hends_j : j = 0 ∨ j = r + 1 := by omega
  have hv := congrArg Fin.val he
  have hlt : u.val < v.val := huv
  rcases hends_i with rfl | rfl <;> rcases hends_j with rfl | rfl <;>
    simp only [path_vertex_first, path_vertex_last] at hv <;> omega

private def ordered_edges {m : ℕ} (H : SimpleGraph (Fin m)) :=
  {p : Fin m × Fin m // p.1 < p.2 ∧ H.Adj p.1 p.2}

private lemma ordered_edges_card {m : ℕ} (H : SimpleGraph (Fin m)) :
    Nat.card (ordered_edges H) = H.edgeSet.ncard := by
  classical
  let f : ordered_edges H → H.edgeSet := fun p =>
    ⟨s(p.val.1, p.val.2), (H.mem_edgeSet).2 p.property.2⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · rintro ⟨⟨a, b⟩, hab, _⟩ ⟨⟨c, d⟩, hcd, _⟩ he
    have hv : s(a, b) = s(c, d) := congrArg Subtype.val he
    rcases Sym2.eq_iff.1 hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (lt_asymm hab hcd).elim
  · rintro ⟨z, hz⟩
    revert hz
    refine Sym2.inductionOn z ?_
    intro a b hz
    have hadj : H.Adj a b := (H.mem_edgeSet).1 hz
    rcases lt_or_gt_of_ne hadj.ne with hab | hba
    · exact ⟨⟨(a, b), hab, hadj⟩, rfl⟩
    · exact ⟨⟨(b, a), hba, hadj.symm⟩, Subtype.ext (Sym2.eq_iff.2 (Or.inr ⟨rfl, rfl⟩))⟩

private def subdivision_rel {m : ℕ} (r : ℕ) (H : SimpleGraph (Fin m))
    (x y : Fin (m + r * m * m)) : Prop :=
  ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin r,
    x.val = m + r * (u.val * m + v.val) + i.val ∧
      ((i.val = 0 ∧ y.val = u.val) ∨
        (i.val + 1 < r ∧ y.val = m + r * (u.val * m + v.val) + i.val + 1) ∨
        (i.val + 1 = r ∧ y.val = v.val))

private def subdivision_edge {r m : ℕ} {H : SimpleGraph (Fin m)}
    (p : ordered_edges H) (j : Fin (r + 1)) : Sym2 (Fin (m + r * m * m)) :=
  s(path_vertex (r := r) p.val.1 p.val.2 j.val,
    path_vertex (r := r) p.val.1 p.val.2 (j.val + 1))

private lemma segment_mem {r m : ℕ} {H : SimpleGraph (Fin m)} (hr : 0 < r)
    (p : ordered_edges H) (j : Fin (r + 1)) :
    subdivision_edge p j ∈ (SimpleGraph.fromRel (subdivision_rel r H)).edgeSet := by
  classical
  rcases p with ⟨⟨u, v⟩, huv, hadj⟩
  have hj := j.isLt
  change s(path_vertex (r := r) u v j.val, path_vertex (r := r) u v (j.val + 1)) ∈
    (SimpleGraph.fromRel (subdivision_rel r H)).edgeSet
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
  constructor
  · intro he
    have := path_vertex_injective huv (by omega) (by omega) he
    omega
  · by_cases hjz : j.val = 0
    · right
      refine ⟨u, v, huv, hadj, ⟨0, hr⟩, ?_, Or.inl ⟨rfl, ?_⟩⟩
      · rw [hjz, path_vertex_inside (r := r) u v (j := 0 + 1) (by omega) (by omega)]
      · rw [hjz, path_vertex_first]
    · left
      refine ⟨u, v, huv, hadj, ⟨j.val - 1, by omega⟩,
        path_vertex_inside u v (by omega) (by omega), Or.inr ?_⟩
      by_cases h : j.val < r
      · left
        refine ⟨by dsimp; omega, ?_⟩
        rw [path_vertex_inside (r := r) u v (j := j.val + 1) (by omega) (by omega)]
        dsimp
        omega
      · right
        refine ⟨by dsimp; omega, ?_⟩
        rw [show j.val = r by omega, path_vertex_last]

private lemma rel_is_segment {r m : ℕ} {H : SimpleGraph (Fin m)}
    {x y : Fin (m + r * m * m)} (h : subdivision_rel r H x y) :
    ∃ (p : ordered_edges H) (j : Fin (r + 1)), subdivision_edge p j = s(x, y) := by
  classical
  rcases h with ⟨u, v, huv, hadj, i, hx, hcases⟩
  have hi := i.isLt
  rcases hcases with ⟨hiz, hy⟩ | ⟨him, hy⟩ | ⟨hil, hy⟩
  · refine ⟨⟨(u, v), huv, hadj⟩, ⟨0, by omega⟩, Sym2.eq_iff.2 (Or.inr ⟨?_, ?_⟩)⟩
    · exact Fin.ext ((path_vertex_first u v).trans hy.symm)
    · apply Fin.ext
      change (path_vertex (r := r) u v 1).val = x.val
      rw [path_vertex_inside (r := r) u v (j := 1) (by omega) (by omega), hx, hiz]
  · refine ⟨⟨(u, v), huv, hadj⟩, ⟨i.val + 1, by omega⟩,
      Sym2.eq_iff.2 (Or.inl ⟨?_, ?_⟩)⟩
    · apply Fin.ext
      change (path_vertex (r := r) u v (i.val + 1)).val = x.val
      rw [path_vertex_inside (r := r) u v (j := i.val + 1) (by omega) (by omega), hx]
      omega
    · apply Fin.ext
      change (path_vertex (r := r) u v (i.val + 1 + 1)).val = y.val
      rw [path_vertex_inside (r := r) u v (j := i.val + 1 + 1) (by omega) (by omega), hy]
      omega
  · refine ⟨⟨(u, v), huv, hadj⟩, ⟨i.val + 1, by omega⟩,
      Sym2.eq_iff.2 (Or.inl ⟨?_, ?_⟩)⟩
    · apply Fin.ext
      change (path_vertex (r := r) u v (i.val + 1)).val = x.val
      rw [path_vertex_inside (r := r) u v (j := i.val + 1) (by omega) (by omega), hx]
      omega
    · apply Fin.ext
      change (path_vertex (r := r) u v (i.val + 1 + 1)).val = y.val
      rw [hil, path_vertex_last, hy]

private lemma segment_injective {r m : ℕ} {H : SimpleGraph (Fin m)} (hr : 0 < r) :
    Function.Injective (fun (pj : ordered_edges H × Fin (r + 1)) => subdivision_edge pj.1 pj.2) := by
  rintro ⟨⟨⟨u, v⟩, huv, _⟩, i⟩ ⟨⟨⟨a, b⟩, _, _⟩, j⟩ he
  have hi := i.isLt
  have hj := j.isLt
  change s(path_vertex (r := r) u v i.val, path_vertex (r := r) u v (i.val + 1)) =
    s(path_vertex (r := r) a b j.val, path_vertex (r := r) a b (j.val + 1)) at he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · by_cases hiz : i.val = 0
    · obtain ⟨rfl, rfl, h⟩ := interior_match (by omega) (by omega) h₂
      have hij : i = j := Fin.ext (by omega)
      subst j
      rfl
    · obtain ⟨rfl, rfl, h⟩ := interior_match (by omega) (by omega) h₁
      have hij : i = j := Fin.ext h
      subst j
      rfl
  · have hcoords : u = a ∧ v = b := by
      by_cases hiz : i.val = 0
      · obtain ⟨ha, hb, _⟩ := interior_match (by omega) (by omega) h₂
        exact ⟨ha, hb⟩
      · obtain ⟨ha, hb, _⟩ := interior_match (by omega) (by omega) h₁
        exact ⟨ha, hb⟩
    obtain ⟨rfl, rfl⟩ := hcoords
    have h₁' := path_vertex_injective huv (by omega) (by omega) h₁
    have h₂' := path_vertex_injective huv (by omega) (by omega) h₂
    omega

theorem PEqualNP.Outside.L_meta_286 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)), 1 ≤ k → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard := by
  intro k m H hk S hS
  classical
  change S = SimpleGraph.fromRel (subdivision_rel (2 * k) H) at hS
  subst S
  let r := 2 * k
  have hr : 0 < r := by dsimp [r]; omega
  let f : ordered_edges H × Fin (r + 1) →
      (SimpleGraph.fromRel (subdivision_rel r H)).edgeSet := fun p =>
    ⟨subdivision_edge p.1 p.2, segment_mem hr p.1 p.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      exact segment_injective hr (congrArg Subtype.val hpq)
    · rintro ⟨z, hz⟩
      revert hz
      refine Sym2.inductionOn z ?_
      intro x y hxy
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj] at hxy
      rcases hxy.2 with h | h
      · obtain ⟨p, j, hpj⟩ := rel_is_segment h
        exact ⟨(p, j), Subtype.ext hpj⟩
      · obtain ⟨p, j, hpj⟩ := rel_is_segment h
        exact ⟨(p, j), Subtype.ext (hpj.trans (Sym2.eq_iff.2 (Or.inr ⟨rfl, rfl⟩)))⟩
  calc
    _ = Nat.card (ordered_edges H × Fin (r + 1)) :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = (r + 1) * H.edgeSet.ncard := by
      rw [Nat.card_prod, ordered_edges_card, Nat.card_fin, Nat.mul_comm]
