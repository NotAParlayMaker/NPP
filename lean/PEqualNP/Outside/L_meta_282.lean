import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_282_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-! ### Part 1: Graph G282 (two triangles joined by one edge) -/

def edgesList : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)]

def isEdge (u v : Fin 6) : Prop :=
  (u.val, v.val) ∈ edgesList ∨ (v.val, u.val) ∈ edgesList

instance : DecidableRel isEdge := fun u v =>
  inferInstanceAs (Decidable ((u.val, v.val) ∈ edgesList ∨ (v.val, u.val) ∈ edgesList))

def edgeG (x : Fin 6 → Bool) : Bool :=
  decide (∃ u v : Fin 6, (u.val, v.val) ∈ edgesList ∧ x u = true ∧ x v = true)

def sing (u : Fin 6) : Fin 6 → Bool :=
  fun i => decide (i = u)

def pair (u v : Fin 6) : Fin 6 → Bool :=
  fun i => decide (i = u ∨ i = v)

def orOf (S : Finset (Fin 6)) (x : Fin 6 → Bool) : Bool :=
  decide (∃ i ∈ S, x i = true)

lemma edgeG_false : edgeG (fun _ => false) = false := by decide

lemma edgeG_sing (u : Fin 6) : edgeG (sing u) = false := by
  revert u; decide

lemma edgeG_pair (u v : Fin 6) : edgeG (pair u v) = true ↔ isEdge u v := by
  revert u v; decide

lemma isEdge_symm {u v : Fin 6} (h : isEdge u v) : isEdge v u := by
  revert u v h; decide

lemma isEdge_irrefl (u : Fin 6) : ¬isEdge u u := by
  revert u; decide

lemma orOf_sing (S : Finset (Fin 6)) (u : Fin 6) : orOf S (sing u) = true ↔ u ∈ S := by
  simp only [orOf, sing, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hu; exact ⟨u, hu, rfl⟩

lemma orOf_pair (S : Finset (Fin 6)) (u v : Fin 6) :
    orOf S (pair u v) = true ↔ u ∈ S ∨ v ∈ S := by
  simp only [orOf, pair, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl | rfl⟩
    · exact Or.inl hi
    · exact Or.inr hi
  · rintro (hu | hv)
    · exact ⟨u, hu, Or.inl rfl⟩
    · exact ⟨v, hv, Or.inr rfl⟩

lemma orOf_union (S T : Finset (Fin 6)) (x : Fin 6 → Bool) :
    orOf (S ∪ T) x = (orOf S x || orOf T x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [orOf, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union]
  constructor
  · rintro ⟨i, hi | hi, hxi⟩
    · exact Or.inl ⟨i, hi, hxi⟩
    · exact Or.inr ⟨i, hi, hxi⟩
  · rintro (⟨i, hi, hxi⟩ | ⟨i, hi, hxi⟩)
    · exact ⟨i, Or.inl hi, hxi⟩
    · exact ⟨i, Or.inr hi, hxi⟩

lemma orOf_empty (x : Fin 6 → Bool) : orOf ∅ x = false := by
  simp [orOf]

lemma orOf_singleton (u : Fin 6) (x : Fin 6 → Bool) : orOf {u} x = x u := by
  apply Bool.eq_iff_iff.mpr
  simp [orOf]

lemma orOf_erase (S : Finset (Fin 6)) (v : Fin 6) (x : Fin 6 → Bool) (hx : x v = false) :
    orOf (S.erase v) x = orOf S x := by
  apply Bool.eq_iff_iff.mpr
  simp only [orOf, decide_eq_true_eq, Finset.mem_erase]
  constructor
  · rintro ⟨i, ⟨_, hi⟩, hxi⟩; exact ⟨i, hi, hxi⟩
  · rintro ⟨i, hi, hxi⟩
    refine ⟨i, ⟨?_, hi⟩, hxi⟩
    rintro rfl
    rw [hx] at hxi
    cases hxi

/-! ### Part 2: Pure combinatorial lemmas on G282 -/

lemma no_k22 (u1 u2 v1 v2 : Fin 6) (hu : u1 ≠ u2) (hv : v1 ≠ v2)
    (h11 : isEdge u1 v1) (h12 : isEdge u1 v2) (h21 : isEdge u2 v1) (h22 : isEdge u2 v2) :
    False := by
  revert u1 u2 v1 v2 hu hv h11 h12 h21 h22; decide

lemma c4_free_biclique {S T : Finset (Fin 6)}
    (hST : ∀ u v : Fin 6, u ∈ S → v ∈ T → isEdge u v) :
    S.card ≤ 1 ∨ T.card ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp h.2
  exact no_k22 u1 u2 v1 v2 hune hvne
    (hST u1 v1 hu1 hv1) (hST u1 v2 hu1 hv2) (hST u2 v1 hu2 hv1) (hST u2 v2 hu2 hv2)

lemma biclique_edges {S T : Finset (Fin 6)}
    (hle : ∀ x : Fin 6 → Bool, (orOf S x && orOf T x) = true → edgeG x = true) :
    ∀ u v : Fin 6, u ∈ S → v ∈ T → isEdge u v := by
  intro u v hu hv
  have hp : (orOf S (pair u v) && orOf T (pair u v)) = true := by
    simp only [Bool.and_eq_true, orOf_pair]
    exact ⟨Or.inl hu, Or.inr hv⟩
  exact (edgeG_pair u v).mp (hle (pair u v) hp)

lemma biclique_edges_del {v : Fin 6} {S T : Finset (Fin 6)}
    (hSv : v ∉ S) (hTv : v ∉ T)
    (hle : ∀ x : Fin 6 → Bool, x v = false → (orOf S x && orOf T x) = true → edgeG x = true) :
    ∀ a b : Fin 6, a ∈ S → b ∈ T → isEdge a b := by
  intro a b ha hb
  have hav : a ≠ v := fun h => hSv (h ▸ ha)
  have hbv : b ≠ v := fun h => hTv (h ▸ hb)
  have hxv : pair a b v = false := by
    simp only [pair, decide_eq_false_iff_not, not_or]
    exact ⟨hav.symm, hbv.symm⟩
  have hp : (orOf S (pair a b) && orOf T (pair a b)) = true := by
    simp only [Bool.and_eq_true, orOf_pair]
    exact ⟨Or.inl ha, Or.inr hb⟩
  exact (edgeG_pair a b).mp (hle (pair a b) hxv hp)

lemma star_center_of_biclique {S T : Finset (Fin 6)}
    (hST : ∀ u v : Fin 6, u ∈ S → v ∈ T → isEdge u v) :
    ∃ w : Fin 6, ∀ u v : Fin 6,
      (orOf S (pair u v) && orOf T (pair u v)) = true → u = w ∨ v = w := by
  rcases c4_free_biclique hST with hS | hT
  · rcases Finset.card_le_one_iff_subset_singleton.mp hS with ⟨w, hw⟩
    refine ⟨w, fun u v h => ?_⟩
    simp only [Bool.and_eq_true, orOf_pair] at h
    rcases h.1 with hu | hv
    · exact Or.inl (Finset.mem_singleton.mp (hw hu))
    · exact Or.inr (Finset.mem_singleton.mp (hw hv))
  · rcases Finset.card_le_one_iff_subset_singleton.mp hT with ⟨w, hw⟩
    refine ⟨w, fun u v h => ?_⟩
    simp only [Bool.and_eq_true, orOf_pair] at h
    rcases h.2 with hu | hv
    · exact Or.inl (Finset.mem_singleton.mp (hw hu))
    · exact Or.inr (Finset.mem_singleton.mp (hw hv))

lemma no_3factor_2k2 {A B C : Finset (Fin 6)}
    {a b c d : Fin 6}
    (hac : ¬isEdge a c) (had : ¬isEdge a d) (hbc : ¬isEdge b c) (hbd : ¬isEdge b d)
    (hle : ∀ u w : Fin 6, u ∈ ({a, b} : Finset (Fin 6)) → w ∈ ({c, d} : Finset (Fin 6)) →
      (orOf A (pair u w) && orOf B (pair u w) && orOf C (pair u w)) = true → edgeG (pair u w) = true)
    (hab : (orOf A (pair a b) && orOf B (pair a b) && orOf C (pair a b)) = true)
    (hcd : (orOf A (pair c d) && orOf B (pair c d) && orOf C (pair c d)) = true) :
    False := by
  simp only [Bool.and_eq_true, orOf_pair] at hab hcd
  rcases hab with ⟨⟨hA1, hB1⟩, hC1⟩
  rcases hcd with ⟨⟨hA2, hB2⟩, hC2⟩
  have check : ∀ u w : Fin 6, u ∈ ({a, b} : Finset (Fin 6)) → w ∈ ({c, d} : Finset (Fin 6)) →
      ¬isEdge u w → (u ∈ A ∨ w ∈ A) → (u ∈ B ∨ w ∈ B) → (u ∈ C ∨ w ∈ C) → False := by
    intro u w hu hw hne hA hB hC
    have ht : (orOf A (pair u w) && orOf B (pair u w) && orOf C (pair u w)) = true := by
      simp only [Bool.and_eq_true, orOf_pair]
      exact ⟨⟨hA, hB⟩, hC⟩
    exact hne ((edgeG_pair u w).mp (hle u w hu hw ht))
  rcases hA1 with haA | hbA <;> rcases hB1 with haB | hbB <;> rcases hC1 with haC | hbC
  · rcases hC2 with hc | hd
    · exact check a c (by simp) (by simp) hac (Or.inl haA) (Or.inl haB) (Or.inr hc)
    · exact check a d (by simp) (by simp) had (Or.inl haA) (Or.inl haB) (Or.inr hd)
  · rcases hC2 with hc | hd
    · exact check a c (by simp) (by simp) hac (Or.inl haA) (Or.inl haB) (Or.inr hc)
    · exact check a d (by simp) (by simp) had (Or.inl haA) (Or.inl haB) (Or.inr hd)
  · rcases hB2 with hc | hd
    · exact check a c (by simp) (by simp) hac (Or.inl haA) (Or.inr hc) (Or.inl haC)
    · exact check a d (by simp) (by simp) had (Or.inl haA) (Or.inr hd) (Or.inl haC)
  · rcases hA2 with hc | hd
    · exact check b c (by simp) (by simp) hbc (Or.inr hc) (Or.inl hbB) (Or.inl hbC)
    · exact check b d (by simp) (by simp) hbd (Or.inr hd) (Or.inl hbB) (Or.inl hbC)
  · rcases hA2 with hc | hd
    · exact check a c (by simp) (by simp) hac (Or.inr hc) (Or.inl haB) (Or.inl haC)
    · exact check a d (by simp) (by simp) had (Or.inr hd) (Or.inl haB) (Or.inl haC)
  · rcases hB2 with hc | hd
    · exact check b c (by simp) (by simp) hbc (Or.inl hbA) (Or.inr hc) (Or.inl hbC)
    · exact check b d (by simp) (by simp) hbd (Or.inl hbA) (Or.inr hd) (Or.inl hbC)
  · rcases hC2 with hc | hd
    · exact check b c (by simp) (by simp) hbc (Or.inl hbA) (Or.inl hbB) (Or.inr hc)
    · exact check b d (by simp) (by simp) hbd (Or.inl hbA) (Or.inl hbB) (Or.inr hd)
  · rcases hC2 with hc | hd
    · exact check b c (by simp) (by simp) hbc (Or.inl hbA) (Or.inl hbB) (Or.inr hc)
    · exact check b d (by simp) (by simp) hbd (Or.inl hbA) (Or.inl hbB) (Or.inr hd)

lemma no_vc_size_2_del (v w1 w2 : Fin 6) :
    ∃ u1 u2 : Fin 6, u1 ≠ v ∧ u2 ≠ v ∧ isEdge u1 u2 ∧ u1 ≠ w1 ∧ u2 ≠ w1 ∧ u1 ≠ w2 ∧ u2 ≠ w2 := by
  revert v w1 w2; decide

lemma del_v_ind2k2 (v : Fin 6) :
    ∃ a b c d : Fin 6,
      a ≠ v ∧ b ≠ v ∧ c ≠ v ∧ d ≠ v ∧
      isEdge a b ∧ isEdge c d ∧
      ¬isEdge a c ∧ ¬isEdge a d ∧ ¬isEdge b c ∧ ¬isEdge b d ∧
      ∀ u : Fin 6, u ≠ v →
        (∀ w1 w2 : Fin 6, w1 ≠ v → w2 ≠ v → isEdge w1 w2 → isEdge u w1 ∨ isEdge u w2) →
        u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ d := by
  revert v; decide

/-- No 2-AND monotone expression computes `edgeG` on `{x | x v = false}`. -/
lemma no_2and_del_v (v : Fin 6)
    (A0 B0 A1 B1 S : Finset (Fin 6)) (b c e0 e1 : Bool)
    (heq : ∀ x : Fin 6 → Bool, x v = false →
      (let p0 := orOf A0 x && orOf B0 x
       let p1 := (orOf A1 x || (b && p0)) && (orOf B1 x || (c && p0))
       orOf S x || (e0 && p0) || (e1 && p1)) = edgeG x) :
    False := by
  -- Erase v from all sets
  let A0' := A0.erase v
  let B0' := B0.erase v
  let A1' := A1.erase v
  let B1' := B1.erase v
  let S' := S.erase v
  have heq' : ∀ x : Fin 6 → Bool, x v = false →
      (let p0 := orOf A0' x && orOf B0' x
       let p1 := (orOf A1' x || (b && p0)) && (orOf B1' x || (c && p0))
       orOf S' x || (e0 && p0) || (e1 && p1)) = edgeG x := by
    intro x hxv
    have h := heq x hxv
    simpa only [A0', B0', A1', B1', S', orOf_erase _ v x hxv] using h
  -- First, S' = ∅
  have hS' : S' = ∅ := by
    by_contra hne
    obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have huv : u ≠ v := (Finset.mem_erase.mp hu).1
    have hxv : sing u v = false := by simp [sing, huv.symm]
    have h1 := heq' (sing u) hxv
    have hSu : orOf S' (sing u) = true := (orOf_sing S' u).mpr hu
    rw [hSu, edgeG_sing] at h1
    simp at h1
  -- Case split on e0, e1, b, c
  have htwo_biclique :
      ∀ X0 Y0 X1 Y1 : Finset (Fin 6),
        v ∉ X0 → v ∉ Y0 → v ∉ X1 → v ∉ Y1 →
        (∀ x : Fin 6 → Bool, x v = false →
          ((orOf X0 x && orOf Y0 x) || (orOf X1 x && orOf Y1 x)) = edgeG x) → False := by
    intro X0 Y0 X1 Y1 hX0v hY0v hX1v hY1v h2
    have hle0 : ∀ x, x v = false → (orOf X0 x && orOf Y0 x) = true → edgeG x = true := by
      intro x hxv h; rw [← h2 x hxv, h]; simp
    have hle1 : ∀ x, x v = false → (orOf X1 x && orOf Y1 x) = true → edgeG x = true := by
      intro x hxv h; rw [← h2 x hxv, h]; simp
    obtain ⟨w0, hw0⟩ := star_center_of_biclique (biclique_edges_del hX0v hY0v hle0)
    obtain ⟨w1, hw1⟩ := star_center_of_biclique (biclique_edges_del hX1v hY1v hle1)
    obtain ⟨u1, u2, hu1v, hu2v, hedge, h10, h20, h11, h21⟩ := no_vc_size_2_del v w0 w1
    have hxv : pair u1 u2 v = false := by
      simp only [pair, decide_eq_false_iff_not, not_or]; exact ⟨hu1v.symm, hu2v.symm⟩
    have ht := h2 (pair u1 u2) hxv
    rw [(edgeG_pair u1 u2).mpr hedge] at ht
    simp only [Bool.or_eq_true] at ht
    rcases ht with h0 | h1
    · rcases hw0 u1 u2 h0 with rfl | rfl <;> contradiction
    · rcases hw1 u1 u2 h1 with rfl | rfl <;> contradiction
  have h_nested :
      ∀ X1 Y1 : Finset (Fin 6),
        v ∉ X1 → v ∉ Y1 →
        (∀ x : Fin 6 → Bool, x v = false →
          ((orOf X1 x || (orOf A0' x && orOf B0' x)) && orOf Y1 x) = edgeG x) → False := by
    intro X1 Y1 hX1v hY1v hnest
    obtain ⟨a, b', c', d, hav, hbv, hcv, hdv, hab, hcd, hac, had, hbc, hbd, hA1_excl⟩ :=
      del_v_ind2k2 v
    -- Every u ∈ X1 must satisfy: for all edges (w1, w2) of G - v, isEdge u w1 ∨ isEdge u w2
    have hY1_vc : ∀ w1 w2 : Fin 6, w1 ≠ v → w2 ≠ v → isEdge w1 w2 → w1 ∈ Y1 ∨ w2 ∈ Y1 := by
      intro w1 w2 hw1v hw2v hedge
      have hxv : pair w1 w2 v = false := by
        simp only [pair, decide_eq_false_iff_not, not_or]; exact ⟨hw1v.symm, hw2v.symm⟩
      have ht := hnest (pair w1 w2) hxv
      rw [(edgeG_pair w1 w2).mpr hedge] at ht
      simp only [Bool.and_eq_true, orOf_pair] at ht
      exact ht.2
    have hX1_disj : ∀ u ∈ X1, u ≠ a ∧ u ≠ b' ∧ u ≠ c' ∧ u ≠ d := by
      intro u hu
      have huv : u ≠ v := fun h => hX1v (h ▸ hu)
      refine hA1_excl u huv (fun w1 w2 hw1v hw2v hedge => ?_)
      have hcov : ∀ y ∈ Y1, isEdge u y := by
        intro y hy
        have hyv : y ≠ v := fun h => hY1v (h ▸ hy)
        have hxv : pair u y v = false := by
          simp only [pair, decide_eq_false_iff_not, not_or]; exact ⟨huv.symm, hyv.symm⟩
        have ht : ((orOf X1 (pair u y) || (orOf A0' (pair u y) && orOf B0' (pair u y))) &&
            orOf Y1 (pair u y)) = true := by
          simp only [Bool.and_eq_true, Bool.or_eq_true, orOf_pair]
          exact ⟨Or.inl (Or.inl hu), Or.inr hy⟩
        rw [hnest (pair u y) hxv] at ht
        exact (edgeG_pair u y).mp ht
      rcases hY1_vc w1 w2 hw1v hw2v hedge with hw1 | hw2
      · exact Or.inl (hcov w1 hw1)
      · exact Or.inr (hcov w2 hw2)
    have hX1_ab : orOf X1 (pair a b') = false := by
      cases h : orOf X1 (pair a b')
      · rfl
      · exfalso; rcases (orOf_pair X1 a b').mp h with ha | hb
        · exact (hX1_disj a ha).1 rfl
        · exact (hX1_disj b' hb).2.1 rfl
    have hX1_cd : orOf X1 (pair c' d) = false := by
      cases h : orOf X1 (pair c' d)
      · rfl
      · exfalso; rcases (orOf_pair X1 c' d).mp h with hc | hd
        · exact (hX1_disj c' hc).2.2.1 rfl
        · exact (hX1_disj d hd).2.2.2 rfl
    have h3_ab : (orOf A0' (pair a b') && orOf B0' (pair a b') && orOf Y1 (pair a b')) = true := by
      have hxv : pair a b' v = false := by
        simp only [pair, decide_eq_false_iff_not, not_or]; exact ⟨hav.symm, hbv.symm⟩
      have ht := hnest (pair a b') hxv
      rw [hX1_ab, (edgeG_pair a b').mpr hab] at ht
      simpa using ht
    have h3_cd : (orOf A0' (pair c' d) && orOf B0' (pair c' d) && orOf Y1 (pair c' d)) = true := by
      have hxv : pair c' d v = false := by
        simp only [pair, decide_eq_false_iff_not, not_or]; exact ⟨hcv.symm, hdv.symm⟩
      have ht := hnest (pair c' d) hxv
      rw [hX1_cd, (edgeG_pair c' d).mpr hcd] at ht
      simpa using ht
    have h3_le : ∀ u w : Fin 6, u ∈ ({a, b'} : Finset (Fin 6)) → w ∈ ({c', d} : Finset (Fin 6)) →
        (orOf A0' (pair u w) && orOf B0' (pair u w) && orOf Y1 (pair u w)) = true →
        edgeG (pair u w) = true := by
      intro u w hu hw ht
      have huv : u ≠ v := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      have hwv : w ≠ v := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      have hxv : pair u w v = false := by
        simp only [pair, decide_eq_false_iff_not, not_or]; exact ⟨huv.symm, hwv.symm⟩
      rw [← hnest (pair u w) hxv]
      simp only [Bool.and_eq_true] at ht ⊢
      exact ⟨Bool.or_eq_true _ _ |>.mpr (Or.inr (Bool.and_eq_true _ _ |>.mpr ht.1)), ht.2⟩
    exact no_3factor_2k2 hac had hbc hbd h3_le h3_ab h3_cd
  cases e0 <;> cases e1
  · -- e0 = false, e1 = false
    obtain ⟨u1, u2, hu1v, hu2v, hedge, _⟩ := no_vc_size_2_del v 0 0
    have hxv : pair u1 u2 v = false := by
      simp only [pair, decide_eq_false_iff_not, not_or]; exact ⟨hu1v.symm, hu2v.symm⟩
    have h := heq' (pair u1 u2) hxv
    rw [hS', orOf_empty, (edgeG_pair u1 u2).mpr hedge] at h
    simp at h
  · -- e0 = false, e1 = true
    cases b <;> cases c
    · apply htwo_biclique ∅ ∅ A1' B1' (by simp) (by simp) (Finset.notMem_erase v A1) (Finset.notMem_erase v B1)
      intro x hxv
      have h := heq' x hxv
      rw [hS', orOf_empty] at h
      simpa [orOf_empty] using h
    · apply h_nested B1' A1' (Finset.notMem_erase v B1) (Finset.notMem_erase v A1)
      intro x hxv
      have h := heq' x hxv
      rw [hS', orOf_empty] at h
      simpa [Bool.and_comm] using h
    · apply h_nested A1' B1' (Finset.notMem_erase v A1) (Finset.notMem_erase v B1)
      intro x hxv
      have h := heq' x hxv
      rw [hS', orOf_empty] at h
      simpa using h
    · apply htwo_biclique A0' B0' A1' B1'
        (Finset.notMem_erase v A0) (Finset.notMem_erase v B0)
        (Finset.notMem_erase v A1) (Finset.notMem_erase v B1)
      intro x hxv
      have h := heq' x hxv
      rw [hS', orOf_empty] at h
      rw [← h]
      cases orOf A0' x <;> cases orOf B0' x <;> cases orOf A1' x <;> cases orOf B1' x <;> rfl
  · -- e0 = true, e1 = false
    apply htwo_biclique A0' B0' ∅ ∅
      (Finset.notMem_erase v A0) (Finset.notMem_erase v B0) (by simp) (by simp)
    intro x hxv
    have h := heq' x hxv
    rw [hS', orOf_empty] at h
    simpa [orOf_empty] using h
  · -- e0 = true, e1 = true: p0 || ((A1' || b*p0) && (B1' || c*p0)) = p0 || (A1' && B1')
    apply htwo_biclique A0' B0' A1' B1'
      (Finset.notMem_erase v A0) (Finset.notMem_erase v B0)
      (Finset.notMem_erase v A1) (Finset.notMem_erase v B1)
    intro x hxv
    have h := heq' x hxv
    rw [hS', orOf_empty] at h
    rw [← h]
    cases b <;> cases c <;>
      cases orOf A0' x <;> cases orOf B0' x <;> cases orOf A1' x <;> cases orOf B1' x <;> rfl

/-! ### Part 3: Non-edge killing bound (for Case B2) -/

def nonEdges : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun p => p.1.val < p.2.val ∧ ¬isEdge p.1 p.2)

lemma nonEdges_card : nonEdges.card = 8 := by decide

def killed (f : (Fin 6 → Bool) → Bool) : Finset (Fin 6 × Fin 6) :=
  nonEdges.filter (fun p => f (pair p.1 p.2) = false)

lemma killed_edgeG : (killed edgeG).card = 8 := by decide

lemma two_nonedges_have_edge (u1 v1 u2 v2 : Fin 6)
    (h1 : u1.val < v1.val) (hne1 : ¬isEdge u1 v1)
    (h2 : u2.val < v2.val) (hne2 : ¬isEdge u2 v2)
    (hdiff : (u1, v1) ≠ (u2, v2)) :
    isEdge u1 u2 ∨ isEdge u1 v2 ∨ isEdge v1 u2 ∨ isEdge v1 v2 := by
  revert u1 v1 u2 v2 h1 hne1 h2 hne2 hdiff; decide

lemma vc_kills_le_one {S : Finset (Fin 6)}
    (hge : ∀ x : Fin 6 → Bool, edgeG x = true → orOf S x = true) :
    (killed (orOf S)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p1 hp1 p2 hp2
  by_contra hdiff
  simp only [killed, nonEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
  have hnotS : ∀ u v : Fin 6, orOf S (pair u v) = false → u ∉ S ∧ v ∉ S := by
    intro u v hf
    constructor
    · intro hu; have := (orOf_pair S u v).mpr (Or.inl hu); rw [hf] at this; cases this
    · intro hv; have := (orOf_pair S u v).mpr (Or.inr hv); rw [hf] at this; cases this
  obtain ⟨hu1, hv1⟩ := hnotS p1.1 p1.2 hp1.2
  obtain ⟨hu2, hv2⟩ := hnotS p2.1 p2.2 hp2.2
  have hedge := two_nonedges_have_edge p1.1 p1.2 p2.1 p2.2 hp1.1.1 hp1.1.2 hp2.1.1 hp2.1.2 hdiff
  have kill_edge : ∀ a b : Fin 6, isEdge a b → a ∉ S → b ∉ S → False := by
    intro a b hab ha hb
    have ht := hge (pair a b) ((edgeG_pair a b).mpr hab)
    rcases (orOf_pair S a b).mp ht with h | h
    · exact ha h
    · exact hb h
  rcases hedge with h | h | h | h
  · exact kill_edge p1.1 p2.1 h hu1 hu2
  · exact kill_edge p1.1 p2.2 h hu1 hv2
  · exact kill_edge p1.2 p2.1 h hv1 hu2
  · exact kill_edge p1.2 p2.2 h hv1 hv2

lemma killed_and_le (f g : (Fin 6 → Bool) → Bool) :
    (killed (fun x => f x && g x)).card ≤ (killed f).card + (killed g).card := by
  have hsub : killed (fun x => f x && g x) ⊆ killed f ∪ killed g := by
    intro p hp
    simp only [killed, Finset.mem_filter, Finset.mem_union, Bool.and_eq_false_iff] at hp ⊢
    rcases hp.2 with h1 | h2
    · exact Or.inl ⟨hp.1, h1⟩
    · exact Or.inr ⟨hp.1, h2⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

lemma or_and_kills_le_two {T L R : Finset (Fin 6)}
    (hge : ∀ x : Fin 6 → Bool, edgeG x = true → (orOf T x || (orOf L x && orOf R x)) = true) :
    (killed (fun x => orOf T x || (orOf L x && orOf R x))).card ≤ 2 := by
  have heq : (fun x => orOf T x || (orOf L x && orOf R x)) =
      (fun x => orOf (T ∪ L) x && orOf (T ∪ R) x) := by
    funext x
    rw [orOf_union, orOf_union]
    cases orOf T x <;> cases orOf L x <;> cases orOf R x <;> rfl
  rw [heq]
  have hge1 : ∀ x, edgeG x = true → orOf (T ∪ L) x = true := by
    intro x hx
    have h := hge x hx
    rw [congrFun heq x] at h
    exact (Bool.and_eq_true _ _).mp h |>.1
  have hge2 : ∀ x, edgeG x = true → orOf (T ∪ R) x = true := by
    intro x hx
    have h := hge x hx
    rw [congrFun heq x] at h
    exact (Bool.and_eq_true _ _).mp h |>.2
  calc (killed (fun x => orOf (T ∪ L) x && orOf (T ∪ R) x)).card
      ≤ (killed (orOf (T ∪ L))).card + (killed (orOf (T ∪ R))).card := killed_and_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add (vc_kills_le_one hge1) (vc_kills_le_one hge2)

lemma nested_kills_le_three {S2 S1 T1 L R : Finset (Fin 6)}
    (hge : ∀ x : Fin 6 → Bool, edgeG x = true →
      (orOf S2 x || ((orOf S1 x || (orOf L x && orOf R x)) && orOf T1 x)) = true) :
    (killed (fun x => orOf S2 x || ((orOf S1 x || (orOf L x && orOf R x)) && orOf T1 x))).card ≤ 3 := by
  have heq : (fun x => orOf S2 x || ((orOf S1 x || (orOf L x && orOf R x)) && orOf T1 x)) =
      (fun x => (orOf (S2 ∪ S1) x || (orOf L x && orOf R x)) && orOf (S2 ∪ T1) x) := by
    funext x
    rw [orOf_union, orOf_union]
    cases orOf S2 x <;> cases orOf S1 x <;> cases orOf T1 x <;> cases orOf L x <;> cases orOf R x <;> rfl
  rw [heq]
  have hge1 : ∀ x, edgeG x = true → (orOf (S2 ∪ S1) x || (orOf L x && orOf R x)) = true := by
    intro x hx
    have h := hge x hx
    rw [congrFun heq x] at h
    exact (Bool.and_eq_true _ _).mp h |>.1
  have hge2 : ∀ x, edgeG x = true → orOf (S2 ∪ T1) x = true := by
    intro x hx
    have h := hge x hx
    rw [congrFun heq x] at h
    exact (Bool.and_eq_true _ _).mp h |>.2
  calc (killed (fun x => (orOf (S2 ∪ S1) x || (orOf L x && orOf R x)) && orOf (S2 ∪ T1) x)).card
      ≤ (killed (fun x => orOf (S2 ∪ S1) x || (orOf L x && orOf R x))).card +
          (killed (orOf (S2 ∪ T1))).card := killed_and_le _ _
    _ ≤ 2 + 1 := Nat.add_le_add (or_and_kills_le_two hge1) (vc_kills_le_one hge2)

/-! ### Part 4: Case-specific helpers for 3-AND skeleton -/

lemma tri_pigeonhole {A B : Finset (Fin 6)} (t0 t1 t2 : Fin 6)
    (_h01 : t0 ≠ t1) (_h02 : t0 ≠ t2) (_h12 : t1 ≠ t2)
    (hA01 : t0 ∈ A ∨ t1 ∈ A) (hA02 : t0 ∈ A ∨ t2 ∈ A) (hA12 : t1 ∈ A ∨ t2 ∈ A)
    (hB01 : t0 ∈ B ∨ t1 ∈ B) (hB02 : t0 ∈ B ∨ t2 ∈ B) (hB12 : t1 ∈ B ∨ t2 ∈ B) :
    ∃ u : Fin 6, (u = t0 ∨ u = t1 ∨ u = t2) ∧ u ∈ A ∧ u ∈ B := by
  by_cases h0A : t0 ∈ A
  · by_cases h0B : t0 ∈ B
    · exact ⟨t0, Or.inl rfl, h0A, h0B⟩
    · have h1B : t1 ∈ B := hB01.resolve_left h0B
      have h2B : t2 ∈ B := hB02.resolve_left h0B
      rcases hA12 with h1A | h2A
      · exact ⟨t1, Or.inr (Or.inl rfl), h1A, h1B⟩
      · exact ⟨t2, Or.inr (Or.inr rfl), h2A, h2B⟩
  · have h1A : t1 ∈ A := hA01.resolve_left h0A
    have h2A : t2 ∈ A := hA02.resolve_left h0A
    rcases hB12 with h1B | h2B
    · exact ⟨t1, Or.inr (Or.inl rfl), h1A, h1B⟩
    · exact ⟨t2, Or.inr (Or.inr rfl), h2A, h2B⟩

lemma tri_count_ge_two {X : Finset (Fin 6)} {t0 t1 t2 : Fin 6}
    (h01 : t0 ∈ X ∨ t1 ∈ X) (h02 : t0 ∈ X ∨ t2 ∈ X) (h12 : t1 ∈ X ∨ t2 ∈ X) :
    2 ≤ (if t0 ∈ X then 1 else 0) + (if t1 ∈ X then 1 else 0) + (if t2 ∈ X then 1 else 0) := by
  by_cases h0 : t0 ∈ X <;> by_cases h1 : t1 ∈ X <;> by_cases h2 : t2 ∈ X <;> simp_all

lemma three_of_four_of_count {A B C D : Finset (Fin 6)} {u : Fin 6}
    (h : 3 ≤ (if u ∈ A then 1 else 0) + (if u ∈ B then 1 else 0) +
             (if u ∈ C then 1 else 0) + (if u ∈ D then 1 else 0)) :
    (u ∈ A ∧ u ∈ B ∧ u ∈ C) ∨ (u ∈ A ∧ u ∈ B ∧ u ∈ D) ∨
    (u ∈ A ∧ u ∈ C ∧ u ∈ D) ∨ (u ∈ B ∧ u ∈ C ∧ u ∈ D) := by
  by_cases ha : u ∈ A <;> by_cases hb : u ∈ B <;> by_cases hc : u ∈ C <;> by_cases hd : u ∈ D <;>
    simp_all

lemma four_tri_pigeonhole {A B C D : Finset (Fin 6)} (t0 t1 t2 : Fin 6)
    (hA01 : t0 ∈ A ∨ t1 ∈ A) (hA02 : t0 ∈ A ∨ t2 ∈ A) (hA12 : t1 ∈ A ∨ t2 ∈ A)
    (hB01 : t0 ∈ B ∨ t1 ∈ B) (hB02 : t0 ∈ B ∨ t2 ∈ B) (hB12 : t1 ∈ B ∨ t2 ∈ B)
    (hC01 : t0 ∈ C ∨ t1 ∈ C) (hC02 : t0 ∈ C ∨ t2 ∈ C) (hC12 : t1 ∈ C ∨ t2 ∈ C)
    (hD01 : t0 ∈ D ∨ t1 ∈ D) (hD02 : t0 ∈ D ∨ t2 ∈ D) (hD12 : t1 ∈ D ∨ t2 ∈ D) :
    ∃ u : Fin 6, (u = t0 ∨ u = t1 ∨ u = t2) ∧
      ((u ∈ A ∧ u ∈ B ∧ u ∈ C) ∨ (u ∈ A ∧ u ∈ B ∧ u ∈ D) ∨
       (u ∈ A ∧ u ∈ C ∧ u ∈ D) ∨ (u ∈ B ∧ u ∈ C ∧ u ∈ D)) := by
  have hA := tri_count_ge_two hA01 hA02 hA12
  have hB := tri_count_ge_two hB01 hB02 hB12
  have hC := tri_count_ge_two hC01 hC02 hC12
  have hD := tri_count_ge_two hD01 hD02 hD12
  let c : Fin 6 → ℕ := fun u =>
    (if u ∈ A then 1 else 0) + (if u ∈ B then 1 else 0) +
    (if u ∈ C then 1 else 0) + (if u ∈ D then 1 else 0)
  have hsum : 8 ≤ c t0 + c t1 + c t2 := by simp only [c]; omega
  have hge3 : 3 ≤ c t0 ∨ 3 ≤ c t1 ∨ 3 ≤ c t2 := by omega
  rcases hge3 with h0 | h1 | h2
  · exact ⟨t0, Or.inl rfl, three_of_four_of_count h0⟩
  · exact ⟨t1, Or.inr (Or.inl rfl), three_of_four_of_count h1⟩
  · exact ⟨t2, Or.inr (Or.inr rfl), three_of_four_of_count h2⟩

lemma adj_tri1_tri2_only23 (t1 t2 u : Fin 6)
    (ht1 : t1 = 0 ∨ t1 = 1 ∨ t1 = 2) (ht2 : t2 = 3 ∨ t2 = 4 ∨ t2 = 5)
    (h1 : isEdge u t1) (h2 : isEdge u t2) : u = 2 ∨ u = 3 := by
  revert t1 t2 u ht1 ht2 h1 h2; decide

lemma adj_2_tri2_eq3 (t2 : Fin 6) (ht2 : t2 = 3 ∨ t2 = 4 ∨ t2 = 5) (h : isEdge 2 t2) :
    t2 = 3 := by
  revert t2 ht2 h; decide

lemma nbhd_0 (w : Fin 6) (h : isEdge 0 w) : w = 1 ∨ w = 2 := by revert w h; decide
lemma nbhd_1 (w : Fin 6) (h : isEdge 1 w) : w = 0 ∨ w = 2 := by revert w h; decide
lemma nbhd_4 (w : Fin 6) (h : isEdge 4 w) : w = 3 ∨ w = 5 := by revert w h; decide
lemma nbhd_5 (w : Fin 6) (h : isEdge 5 w) : w = 3 ∨ w = 4 := by revert w h; decide

lemma tri1_nonadj_45 {u v : Fin 6} (hu : u = 0 ∨ u = 1 ∨ u = 2) (hv : v = 4 ∨ v = 5) :
    ¬isEdge u v := by
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl <;> decide

lemma tri2_nonadj_01 {u v : Fin 6} (hu : u = 0 ∨ u = 1) (hv : v = 3 ∨ v = 4 ∨ v = 5) :
    ¬isEdge u v := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> decide

/-- Case A: `edgeG = ((S1 || (L0 && R0)) && T1) || ((S2 || (L0 && R0)) && T2)` with `|T1|, |T2| ≥ 2` is impossible. -/
lemma no_caseA {L0 R0 S1 T1 S2 T2 : Finset (Fin 6)}
    (hT1_card : 2 ≤ T1.card) (hT2_card : 2 ≤ T2.card)
    (heq : ∀ x : Fin 6 → Bool,
      (((orOf S1 x || (orOf L0 x && orOf R0 x)) && orOf T1 x) ||
       ((orOf S2 x || (orOf L0 x && orOf R0 x)) && orOf T2 x)) = edgeG x) :
    False := by
  let T := T1 ∪ T2
  have hS1T1_le : ∀ x, (orOf S1 x && orOf T1 x) = true → edgeG x = true := by
    intro x h; rw [← heq x]; simp only [Bool.and_eq_true] at h; simp [h.1, h.2]
  have hS2T2_le : ∀ x, (orOf S2 x && orOf T2 x) = true → edgeG x = true := by
    intro x h; rw [← heq x]; simp only [Bool.and_eq_true] at h; simp [h.1, h.2]
  have h3_le : ∀ x, (orOf L0 x && orOf R0 x && orOf T x) = true → edgeG x = true := by
    intro x h
    rw [← heq x]
    simp only [Bool.and_eq_true, T, orOf_union, Bool.or_eq_true] at h ⊢
    rcases h.2 with h1 | h2
    · exact Or.inl ⟨Or.inr h.1, h1⟩
    · exact Or.inr ⟨Or.inr h.1, h2⟩
  have hT_vc : ∀ u v : Fin 6, isEdge u v → u ∈ T ∨ v ∈ T := by
    intro u v huv
    have h := heq (pair u v)
    rw [(edgeG_pair u v).mpr huv] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, orOf_pair] at h
    rcases h with ⟨_, hu | hv⟩ | ⟨_, hu | hv⟩
    · exact Or.inl (Finset.mem_union_left _ hu)
    · exact Or.inr (Finset.mem_union_left _ hv)
    · exact Or.inl (Finset.mem_union_right _ hu)
    · exact Or.inr (Finset.mem_union_right _ hv)
  -- Since |T1| >= 2 and |T2| >= 2, by C4-freeness |S1| <= 1 and |S2| <= 1
  have hS1_le1 : S1.card ≤ 1 := by
    rcases c4_free_biclique (biclique_edges hS1T1_le) with h | h
    · exact h
    · omega
  have hS2_le1 : S2.card ≤ 1 := by
    rcases c4_free_biclique (biclique_edges hS2T2_le) with h | h
    · exact h
    · omega
  -- Helper: if neither S1 nor S2 meets {3, 4, 5}, then L0 & R0 & T covers all of {3, 4, 5}, contradiction!
  have no_miss_tri2 : (∀ u ∈ S1, u ≠ 3 ∧ u ≠ 4 ∧ u ≠ 5) → (∀ u ∈ S2, u ≠ 3 ∧ u ≠ 4 ∧ u ≠ 5) → False := by
    intro h1 h2
    have hcov : ∀ a b : Fin 6, (a = 3 ∨ a = 4 ∨ a = 5) → (b = 3 ∨ b = 4 ∨ b = 5) → isEdge a b →
        (a ∈ L0 ∨ b ∈ L0) ∧ (a ∈ R0 ∨ b ∈ R0) := by
      intro a b ha hb hab
      have h := heq (pair a b)
      rw [(edgeG_pair a b).mpr hab] at h
      have hS1ab : orOf S1 (pair a b) = false := by
        simp only [orOf, pair, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
        intro u hu hor
        have := h1 u hu
        rcases hor with rfl | rfl
        · rcases ha with rfl | rfl | rfl <;> tauto
        · rcases hb with rfl | rfl | rfl <;> tauto
      have hS2ab : orOf S2 (pair a b) = false := by
        simp only [orOf, pair, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
        intro u hu hor
        have := h2 u hu
        rcases hor with rfl | rfl
        · rcases ha with rfl | rfl | rfl <;> tauto
        · rcases hb with rfl | rfl | rfl <;> tauto
      rw [hS1ab, hS2ab] at h
      simp only [Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, orOf_pair] at h
      rcases h with ⟨hLR, _⟩ | ⟨hLR, _⟩ <;> exact hLR
    have h34 := hcov 3 4 (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide)
    have h35 := hcov 3 5 (Or.inl rfl) (Or.inr (Or.inr rfl)) (by decide)
    have h45 := hcov 4 5 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (by decide)
    obtain ⟨v, hv, hvL, hvR⟩ := tri_pigeonhole 3 4 5 (by decide) (by decide) (by decide)
      h34.1 h35.1 h45.1 h34.2 h35.2 h45.2
    have hT01 : (0 : Fin 6) ∈ T ∨ (1 : Fin 6) ∈ T := hT_vc 0 1 (by decide)
    rcases hT01 with h0T | h1T
    · have hne := tri2_nonadj_01 (Or.inl rfl) hv
      have ht : (orOf L0 (pair 0 v) && orOf R0 (pair 0 v) && orOf T (pair 0 v)) = true := by
        simp only [Bool.and_eq_true, orOf_pair]
        exact ⟨⟨Or.inr hvL, Or.inr hvR⟩, Or.inl h0T⟩
      exact hne ((edgeG_pair 0 v).mp (h3_le (pair 0 v) ht))
    · have hne := tri2_nonadj_01 (Or.inr rfl) hv
      have ht : (orOf L0 (pair 1 v) && orOf R0 (pair 1 v) && orOf T (pair 1 v)) = true := by
        simp only [Bool.and_eq_true, orOf_pair]
        exact ⟨⟨Or.inr hvL, Or.inr hvR⟩, Or.inl h1T⟩
      exact hne ((edgeG_pair 1 v).mp (h3_le (pair 1 v) ht))
  -- Symmetrically, if neither S1 nor S2 meets {0, 1, 2}, contradiction!
  have no_miss_tri1 : (∀ u ∈ S1, u ≠ 0 ∧ u ≠ 1 ∧ u ≠ 2) → (∀ u ∈ S2, u ≠ 0 ∧ u ≠ 1 ∧ u ≠ 2) → False := by
    intro h1 h2
    have hcov : ∀ a b : Fin 6, (a = 0 ∨ a = 1 ∨ a = 2) → (b = 0 ∨ b = 1 ∨ b = 2) → isEdge a b →
        (a ∈ L0 ∨ b ∈ L0) ∧ (a ∈ R0 ∨ b ∈ R0) := by
      intro a b ha hb hab
      have h := heq (pair a b)
      rw [(edgeG_pair a b).mpr hab] at h
      have hS1ab : orOf S1 (pair a b) = false := by
        simp only [orOf, pair, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
        intro u hu hor
        have := h1 u hu
        rcases hor with rfl | rfl
        · rcases ha with rfl | rfl | rfl <;> tauto
        · rcases hb with rfl | rfl | rfl <;> tauto
      have hS2ab : orOf S2 (pair a b) = false := by
        simp only [orOf, pair, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
        intro u hu hor
        have := h2 u hu
        rcases hor with rfl | rfl
        · rcases ha with rfl | rfl | rfl <;> tauto
        · rcases hb with rfl | rfl | rfl <;> tauto
      rw [hS1ab, hS2ab] at h
      simp only [Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, orOf_pair] at h
      rcases h with ⟨hLR, _⟩ | ⟨hLR, _⟩ <;> exact hLR
    have h01 := hcov 0 1 (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide)
    have h02 := hcov 0 2 (Or.inl rfl) (Or.inr (Or.inr rfl)) (by decide)
    have h12 := hcov 1 2 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (by decide)
    obtain ⟨u, hu, huL, huR⟩ := tri_pigeonhole 0 1 2 (by decide) (by decide) (by decide)
      h01.1 h02.1 h12.1 h01.2 h02.2 h12.2
    have hT45 : (4 : Fin 6) ∈ T ∨ (5 : Fin 6) ∈ T := hT_vc 4 5 (by decide)
    rcases hT45 with h4T | h5T
    · have hne := tri1_nonadj_45 hu (Or.inl rfl)
      have ht : (orOf L0 (pair u 4) && orOf R0 (pair u 4) && orOf T (pair u 4)) = true := by
        simp only [Bool.and_eq_true, orOf_pair]
        exact ⟨⟨Or.inl huL, Or.inl huR⟩, Or.inr h4T⟩
      exact hne ((edgeG_pair u 4).mp (h3_le (pair u 4) ht))
    · have hne := tri1_nonadj_45 hu (Or.inr rfl)
      have ht : (orOf L0 (pair u 5) && orOf R0 (pair u 5) && orOf T (pair u 5)) = true := by
        simp only [Bool.and_eq_true, orOf_pair]
        exact ⟨⟨Or.inl huL, Or.inl huR⟩, Or.inr h5T⟩
      exact hne ((edgeG_pair u 5).mp (h3_le (pair u 5) ht))
  -- Therefore S1 and S2 must both be singletons, one in {0,1,2} and one in {3,4,5}!
  obtain ⟨u1, hu1_sub⟩ := Finset.card_le_one_iff_subset_singleton.mp hS1_le1
  obtain ⟨u2, hu2_sub⟩ := Finset.card_le_one_iff_subset_singleton.mp hS2_le1
  -- Helper when S1 = {p} with p in {0,1,2} and S2 = {q} with q in {3,4,5}
  have handle_opp : ∀ (p q : Fin 6) (P Q : Finset (Fin 6)),
      p ∈ ({0, 1, 2} : Finset (Fin 6)) → q ∈ ({3, 4, 5} : Finset (Fin 6)) →
      2 ≤ P.card → 2 ≤ Q.card →
      (∀ w ∈ P, isEdge p w) → (∀ w ∈ Q, isEdge q w) →
      P ∪ Q = T →
      (∀ a b : Fin 6, isEdge a b → a ≠ p → b ≠ p → a ≠ q → b ≠ q →
        (orOf L0 (pair a b) && orOf R0 (pair a b) && orOf T (pair a b)) = true) →
      False := by
    intro p q P Q hp hq hPcard hQcard hPedge hQedge hPQT hmiss
    have h3_pair : ∀ a b c d : Fin 6, isEdge a b → isEdge c d →
        a ≠ p → b ≠ p → a ≠ q → b ≠ q → c ≠ p → d ≠ p → c ≠ q → d ≠ q →
        ¬isEdge a c → ¬isEdge a d → ¬isEdge b c → ¬isEdge b d → False := by
      intro a b c d hab hcd hap hbp haq hbq hcp hdp hcq hdq hac had hbc hbd
      exact no_3factor_2k2 hac had hbc hbd (fun u w _ _ h => h3_le (pair u w) h)
        (hmiss a b hab hap hbp haq hbq) (hmiss c d hcd hcp hdp hcq hdq)
    -- Shared helper for the 4 cases p ∈ {0,1}, q ∈ {4,5}
    have opp_01_45 : ∀ (a1 b2 : Fin 6),
        a1 ≠ 2 → b2 ≠ 3 →
        (∀ w ∈ P, w = a1 ∨ w = 2) → (∀ w ∈ Q, w = 3 ∨ w = b2) →
        isEdge a1 2 → isEdge 3 b2 →
        a1 ≠ p → (2 : Fin 6) ≠ p → a1 ≠ q → (2 : Fin 6) ≠ q →
        (3 : Fin 6) ≠ p → b2 ≠ p → (3 : Fin 6) ≠ q → b2 ≠ q →
        ¬isEdge a1 3 → ¬isEdge a1 b2 → False := by
      intro a1 b2 ha12 hb23 hPsub' hQsub' ha1_2 h3_b2 ha1p h2p ha1q h2q h3p hb2p h3q hb2q ha13 ha1b2
      have hPsub : P ⊆ {a1, 2} := fun w hw => by
        simp only [Finset.mem_insert, Finset.mem_singleton]; exact hPsub' w hw
      have hPeq : P = {a1, 2} :=
        Finset.eq_of_subset_of_card_le hPsub (by rw [Finset.card_pair ha12]; exact hPcard)
      have ha1T : a1 ∈ T := by rw [← hPQT, hPeq]; simp
      have h2T : (2 : Fin 6) ∈ T := by rw [← hPQT, hPeq]; simp
      have h12 := hmiss a1 2 ha1_2 ha1p h2p ha1q h2q
      have h3b := hmiss 3 b2 h3_b2 h3p hb2p h3q hb2q
      simp only [Bool.and_eq_true, orOf_pair] at h12 h3b
      have h2_not_both : ¬((2 : Fin 6) ∈ L0 ∧ (2 : Fin 6) ∈ R0) := by
        rintro ⟨hL, hR⟩
        have ht : (orOf L0 (sing 2) && orOf R0 (sing 2) && orOf T (sing 2)) = true := by
          simp only [Bool.and_eq_true, orOf_sing]; exact ⟨⟨hL, hR⟩, h2T⟩
        have := h3_le (sing 2) ht; rw [edgeG_sing] at this; cases this
      rcases h12.1.1 with ha1L | h2L
      · have h3nR : (3 : Fin 6) ∉ R0 := fun h3R => by
          have ht : (orOf L0 (pair a1 3) && orOf R0 (pair a1 3) && orOf T (pair a1 3)) = true := by
            simp only [Bool.and_eq_true, orOf_pair]; exact ⟨⟨Or.inl ha1L, Or.inr h3R⟩, Or.inl ha1T⟩
          exact ha13 ((edgeG_pair a1 3).mp (h3_le _ ht))
        have hb2nR : b2 ∉ R0 := fun hb2R => by
          have ht : (orOf L0 (pair a1 b2) && orOf R0 (pair a1 b2) && orOf T (pair a1 b2)) = true := by
            simp only [Bool.and_eq_true, orOf_pair]; exact ⟨⟨Or.inl ha1L, Or.inr hb2R⟩, Or.inl ha1T⟩
          exact ha1b2 ((edgeG_pair a1 b2).mp (h3_le _ ht))
        rcases h3b.1.2 with h3R | hb2R <;> contradiction
      · have ha1R : a1 ∈ R0 := h12.1.2.resolve_right (fun h2R => h2_not_both ⟨h2L, h2R⟩)
        have h3nL : (3 : Fin 6) ∉ L0 := fun h3L => by
          have ht : (orOf L0 (pair a1 3) && orOf R0 (pair a1 3) && orOf T (pair a1 3)) = true := by
            simp only [Bool.and_eq_true, orOf_pair]; exact ⟨⟨Or.inr h3L, Or.inl ha1R⟩, Or.inl ha1T⟩
          exact ha13 ((edgeG_pair a1 3).mp (h3_le _ ht))
        have hb2nL : b2 ∉ L0 := fun hb2L => by
          have ht : (orOf L0 (pair a1 b2) && orOf R0 (pair a1 b2) && orOf T (pair a1 b2)) = true := by
            simp only [Bool.and_eq_true, orOf_pair]; exact ⟨⟨Or.inr hb2L, Or.inl ha1R⟩, Or.inl ha1T⟩
          exact ha1b2 ((edgeG_pair a1 b2).mp (h3_le _ ht))
        rcases h3b.1.1 with h3L | hb2L <;> contradiction
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    · exact h3_pair 1 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact opp_01_45 1 5 (by decide) (by decide) (fun w hw => nbhd_0 w (hPedge w hw))
        (fun w hw => nbhd_4 w (hQedge w hw)) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact opp_01_45 1 4 (by decide) (by decide) (fun w hw => nbhd_0 w (hPedge w hw))
        (fun w hw => nbhd_5 w (hQedge w hw)) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact h3_pair 0 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact opp_01_45 0 5 (by decide) (by decide) (fun w hw => nbhd_1 w (hPedge w hw))
        (fun w hw => nbhd_4 w (hQedge w hw)) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact opp_01_45 0 4 (by decide) (by decide) (fun w hw => nbhd_1 w (hPedge w hw))
        (fun w hw => nbhd_5 w (hQedge w hw)) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact h3_pair 0 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact h3_pair 0 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact h3_pair 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Check whether S1 and S2 are empty or in opposite triangles
  have mem_t1_ne_t2 : ∀ u : Fin 6, u ∈ ({0, 1, 2} : Finset (Fin 6)) → u ≠ 3 ∧ u ≠ 4 ∧ u ≠ 5 := by decide
  have not_t1_ne_t1 : ∀ u : Fin 6, u ∉ ({0, 1, 2} : Finset (Fin 6)) → u ≠ 0 ∧ u ≠ 1 ∧ u ≠ 2 := by decide
  have not_t1_mem_t2 : ∀ u : Fin 6, u ∉ ({0, 1, 2} : Finset (Fin 6)) → u ∈ ({3, 4, 5} : Finset (Fin 6)) := by decide
  by_cases hS1e : S1 = ∅
  · by_cases hu2_t1 : u2 ∈ ({0, 1, 2} : Finset (Fin 6))
    · apply no_miss_tri2
      · simp [hS1e]
      · intro u hu; have heq_u := Finset.mem_singleton.mp (hu2_sub hu); subst heq_u
        exact mem_t1_ne_t2 u hu2_t1
    · apply no_miss_tri1
      · simp [hS1e]
      · intro u hu; have heq_u := Finset.mem_singleton.mp (hu2_sub hu); subst heq_u
        exact not_t1_ne_t1 u hu2_t1
  · by_cases hS2e : S2 = ∅
    · by_cases hu1_t1 : u1 ∈ ({0, 1, 2} : Finset (Fin 6))
      · apply no_miss_tri2
        · intro u hu; have heq_u := Finset.mem_singleton.mp (hu1_sub hu); subst heq_u
          exact mem_t1_ne_t2 u hu1_t1
        · simp [hS2e]
      · apply no_miss_tri1
        · intro u hu; have heq_u := Finset.mem_singleton.mp (hu1_sub hu); subst heq_u
          exact not_t1_ne_t1 u hu1_t1
        · simp [hS2e]
    · have hu1_mem : u1 ∈ S1 := by
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS1e
        have := Finset.mem_singleton.mp (hu1_sub hx); subst this; exact hx
      have hu2_mem : u2 ∈ S2 := by
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS2e
        have := Finset.mem_singleton.mp (hu2_sub hx); subst this; exact hx
      have hmiss_common : ∀ a b : Fin 6, isEdge a b → a ≠ u1 → b ≠ u1 → a ≠ u2 → b ≠ u2 →
          (orOf L0 (pair a b) && orOf R0 (pair a b) && orOf T (pair a b)) = true := by
        intro a b hab hau1 hbu1 hau2 hbu2
        have h := heq (pair a b)
        rw [(edgeG_pair a b).mpr hab] at h
        have h1 : orOf S1 (pair a b) = false := by
          cases hv : orOf S1 (pair a b)
          · rfl
          · exfalso; rcases (orOf_pair S1 a b).mp hv with ha | hb
            · exact hau1 (Finset.mem_singleton.mp (hu1_sub ha))
            · exact hbu1 (Finset.mem_singleton.mp (hu1_sub hb))
        have h2 : orOf S2 (pair a b) = false := by
          cases hv : orOf S2 (pair a b)
          · rfl
          · exfalso; rcases (orOf_pair S2 a b).mp hv with ha | hb
            · exact hau2 (Finset.mem_singleton.mp (hu2_sub ha))
            · exact hbu2 (Finset.mem_singleton.mp (hu2_sub hb))
        rw [h1, h2] at h
        simp only [Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, T, orOf_union] at h ⊢
        rcases h with ⟨hLR, hT1⟩ | ⟨hLR, hT2⟩
        · exact ⟨hLR, Or.inl hT1⟩
        · exact ⟨hLR, Or.inr hT2⟩
      by_cases hu1_t1 : u1 ∈ ({0, 1, 2} : Finset (Fin 6))
      · by_cases hu2_t1 : u2 ∈ ({0, 1, 2} : Finset (Fin 6))
        · apply no_miss_tri2
          · intro u hu; have := Finset.mem_singleton.mp (hu1_sub hu); subst this; exact mem_t1_ne_t2 u hu1_t1
          · intro u hu; have := Finset.mem_singleton.mp (hu2_sub hu); subst this; exact mem_t1_ne_t2 u hu2_t1
        · have hu2_t2 : u2 ∈ ({3, 4, 5} : Finset (Fin 6)) := not_t1_mem_t2 u2 hu2_t1
          exact handle_opp u1 u2 T1 T2 hu1_t1 hu2_t2 hT1_card hT2_card
            (fun w hw => biclique_edges hS1T1_le u1 w hu1_mem hw)
            (fun w hw => biclique_edges hS2T2_le u2 w hu2_mem hw)
            rfl hmiss_common
      · have hu1_t2 : u1 ∈ ({3, 4, 5} : Finset (Fin 6)) := not_t1_mem_t2 u1 hu1_t1
        by_cases hu2_t1 : u2 ∈ ({0, 1, 2} : Finset (Fin 6))
        · exact handle_opp u2 u1 T2 T1 hu2_t1 hu1_t2 hT2_card hT1_card
            (fun w hw => biclique_edges hS2T2_le u2 w hu2_mem hw)
            (fun w hw => biclique_edges hS1T1_le u1 w hu1_mem hw)
            (Finset.union_comm T2 T1)
            (fun a b hab hau2 hbu2 hau1 hbu1 => hmiss_common a b hab hau1 hbu1 hau2 hbu2)
        · apply no_miss_tri1
          · intro u hu; have := Finset.mem_singleton.mp (hu1_sub hu); subst this; exact not_t1_ne_t1 u hu1_t1
          · intro u hu; have := Finset.mem_singleton.mp (hu2_sub hu); subst this; exact not_t1_ne_t1 u hu2_t1

/-- Case B1a: `edgeG = (L0 && R0 && T2) || (L1 && R1 && T2)` is impossible. -/
lemma no_caseB1_two3 {L0 R0 L1 R1 T2 : Finset (Fin 6)}
    (heq : ∀ x : Fin 6 → Bool,
      ((orOf L0 x && orOf R0 x && orOf T2 x) || (orOf L1 x && orOf R1 x && orOf T2 x)) = edgeG x) :
    False := by
  have h1_le : ∀ x, (orOf L0 x && orOf R0 x && orOf T2 x) = true → edgeG x = true := by
    intro x h; rw [← heq x, h]; simp
  have h2_le : ∀ x, (orOf L1 x && orOf R1 x && orOf T2 x) = true → edgeG x = true := by
    intro x h; rw [← heq x, h]; simp
  have hT2_vc : ∀ u v : Fin 6, isEdge u v → u ∈ T2 ∨ v ∈ T2 := by
    intro u v huv
    have h := heq (pair u v)
    rw [(edgeG_pair u v).mpr huv] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, orOf_pair] at h
    rcases h with ⟨_, hT⟩ | ⟨_, hT⟩ <;> exact hT
  have handle_one : ∀ (A B C D : Finset (Fin 6)),
      (∀ x, (orOf A x && orOf B x && orOf T2 x) = true → edgeG x = true) →
      (∀ x, (orOf C x && orOf D x && orOf T2 x) = true → edgeG x = true) →
      (∀ x, ((orOf A x && orOf B x && orOf T2 x) || (orOf C x && orOf D x && orOf T2 x)) = edgeG x) →
      (orOf A (pair 0 1) && orOf B (pair 0 1) && orOf T2 (pair 0 1)) = true →
      False := by
    intro A B C D hAB_le hCD_le hsum hAB01
    -- Since A & B & T2 covers (0,1), it misses ALL of (3,4), (3,5), (4,5) -> C & D & T2 covers all 3!
    have hCD_cov : ∀ a b : Fin 6, (a = 3 ∨ a = 4 ∨ a = 5) → (b = 3 ∨ b = 4 ∨ b = 5) → isEdge a b →
        (a ∈ C ∨ b ∈ C) ∧ (a ∈ D ∨ b ∈ D) := by
      intro a b ha hb hab
      have hAB_miss : (orOf A (pair a b) && orOf B (pair a b) && orOf T2 (pair a b)) = false := by
        cases hval : (orOf A (pair a b) && orOf B (pair a b) && orOf T2 (pair a b))
        · rfl
        · exfalso
          exact no_3factor_2k2 (tri2_nonadj_01 (Or.inl rfl) ha) (tri2_nonadj_01 (Or.inl rfl) hb)
            (tri2_nonadj_01 (Or.inr rfl) ha) (tri2_nonadj_01 (Or.inr rfl) hb)
            (fun u w _ _ h => hAB_le (pair u w) h) hAB01 hval
      have h := hsum (pair a b)
      rw [hAB_miss, (edgeG_pair a b).mpr hab] at h
      simp only [Bool.false_or, Bool.and_eq_true, orOf_pair] at h
      exact h.1
    have h34 := hCD_cov 3 4 (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide)
    have h35 := hCD_cov 3 5 (Or.inl rfl) (Or.inr (Or.inr rfl)) (by decide)
    have h45 := hCD_cov 4 5 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (by decide)
    obtain ⟨v, hv, hvC, hvD⟩ := tri_pigeonhole 3 4 5 (by decide) (by decide) (by decide)
      h34.1 h35.1 h45.1 h34.2 h35.2 h45.2
    rcases hT2_vc 0 1 (by decide) with h0T | h1T
    · have ht : (orOf C (pair 0 v) && orOf D (pair 0 v) && orOf T2 (pair 0 v)) = true := by
        simp only [Bool.and_eq_true, orOf_pair]; exact ⟨⟨Or.inr hvC, Or.inr hvD⟩, Or.inl h0T⟩
      exact tri2_nonadj_01 (Or.inl rfl) hv ((edgeG_pair 0 v).mp (hCD_le _ ht))
    · have ht : (orOf C (pair 1 v) && orOf D (pair 1 v) && orOf T2 (pair 1 v)) = true := by
        simp only [Bool.and_eq_true, orOf_pair]; exact ⟨⟨Or.inr hvC, Or.inr hvD⟩, Or.inl h1T⟩
      exact tri2_nonadj_01 (Or.inr rfl) hv ((edgeG_pair 1 v).mp (hCD_le _ ht))
  have h01 := heq (pair 0 1)
  rw [(edgeG_pair 0 1).mpr (by decide)] at h01
  simp only [Bool.or_eq_true] at h01
  rcases h01 with h1 | h2
  · exact handle_one L0 R0 L1 R1 h1_le h2_le heq h1
  · exact handle_one L1 R1 L0 R0 h2_le h1_le (fun x => by rw [Bool.or_comm]; exact heq x) h2

/-- Case B1b: `edgeG = (S1 || (L0 && R0)) && T1 && T2` is impossible. -/
lemma no_caseB1_four {S1 L0 R0 T1 T2 : Finset (Fin 6)}
    (heq : ∀ x : Fin 6 → Bool,
      ((orOf S1 x || (orOf L0 x && orOf R0 x)) && orOf T1 x && orOf T2 x) = edgeG x) :
    False := by
  have hT1_vc : ∀ u v : Fin 6, isEdge u v → u ∈ T1 ∨ v ∈ T1 := by
    intro u v huv; have h := heq (pair u v); rw [(edgeG_pair u v).mpr huv] at h
    simp only [Bool.and_eq_true, orOf_pair] at h; exact h.1.2
  have hT2_vc : ∀ u v : Fin 6, isEdge u v → u ∈ T2 ∨ v ∈ T2 := by
    intro u v huv; have h := heq (pair u v); rw [(edgeG_pair u v).mpr huv] at h
    simp only [Bool.and_eq_true, orOf_pair] at h; exact h.2
  have h4_le : ∀ x, (orOf L0 x && orOf R0 x && orOf T1 x && orOf T2 x) = true → edgeG x = true := by
    intro x h; rw [← heq x]
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨⟨Or.inr h.1.1, h.1.2⟩, h.2⟩
  -- Every u ∈ S1 must be adjacent to EVERY w ∈ T1 ∩ T2!
  have hS1_adj : ∀ u ∈ S1, ∀ w : Fin 6, w ∈ T1 → w ∈ T2 → isEdge u w := by
    intro u hu w hw1 hw2
    have ht : ((orOf S1 (pair u w) || (orOf L0 (pair u w) && orOf R0 (pair u w))) &&
        orOf T1 (pair u w) && orOf T2 (pair u w)) = true := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, orOf_pair]
      exact ⟨⟨Or.inl (Or.inl hu), Or.inr hw1⟩, Or.inr hw2⟩
    rw [heq] at ht
    exact (edgeG_pair u w).mp ht
  -- T1 ∩ T2 intersects both {0,1,2} and {3,4,5}!
  obtain ⟨t1, ht1, ht1_1, ht1_2⟩ := tri_pigeonhole 0 1 2 (by decide) (by decide) (by decide)
    (hT1_vc 0 1 (by decide)) (hT1_vc 0 2 (by decide)) (hT1_vc 1 2 (by decide))
    (hT2_vc 0 1 (by decide)) (hT2_vc 0 2 (by decide)) (hT2_vc 1 2 (by decide))
  obtain ⟨t2, ht2, ht2_1, ht2_2⟩ := tri_pigeonhole 3 4 5 (by decide) (by decide) (by decide)
    (hT1_vc 3 4 (by decide)) (hT1_vc 3 5 (by decide)) (hT1_vc 4 5 (by decide))
    (hT2_vc 3 4 (by decide)) (hT2_vc 3 5 (by decide)) (hT2_vc 4 5 (by decide))
  -- Therefore any u ∈ S1 must be 2 or 3, and cannot have both 2 and 3!
  have hS1_only23 : ∀ u ∈ S1, u = 2 ∨ u = 3 := by
    intro u hu
    exact adj_tri1_tri2_only23 t1 t2 u ht1 ht2 (hS1_adj u hu t1 ht1_1 ht1_2) (hS1_adj u hu t2 ht2_1 ht2_2)
  have hS1_not_both : ¬((2 : Fin 6) ∈ S1 ∧ (3 : Fin 6) ∈ S1) := by
    rintro ⟨h2, h3⟩
    have ht2_eq3 : t2 = 3 := adj_2_tri2_eq3 t2 ht2 (hS1_adj 2 h2 t2 ht2_1 ht2_2)
    subst ht2_eq3
    exact isEdge_irrefl 3 (hS1_adj 3 h3 3 ht2_1 ht2_2)
  -- Helper: if S1 doesn't meet {3,4,5}, then L0, R0, T1, T2 all cover {3,4,5} and hit {0,1} -> contradiction!
  have no_S1_miss_tri2 : (∀ u ∈ S1, u ≠ 3 ∧ u ≠ 4 ∧ u ≠ 5) → False := by
    intro hS1_no
    have hLR : ∀ a b : Fin 6, (a = 3 ∨ a = 4 ∨ a = 5) → (b = 3 ∨ b = 4 ∨ b = 5) → isEdge a b →
        (a ∈ L0 ∨ b ∈ L0) ∧ (a ∈ R0 ∨ b ∈ R0) := by
      intro a b ha hb hab
      have h := heq (pair a b)
      rw [(edgeG_pair a b).mpr hab] at h
      have hS1ab : orOf S1 (pair a b) = false := by
        simp only [orOf, pair, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
        intro u hu hor; have := hS1_no u hu
        rcases hor with rfl | rfl
        · rcases ha with rfl | rfl | rfl <;> tauto
        · rcases hb with rfl | rfl | rfl <;> tauto
      rw [hS1ab] at h
      simp only [Bool.false_or, Bool.and_eq_true, orOf_pair] at h
      exact h.1.1
    have h01_S1 : orOf S1 (pair 0 1) = false := by
      simp only [orOf, pair, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
      intro u hu hor
      have h23 := hS1_only23 u hu
      rcases hor with rfl | rfl <;> rcases h23 with h | h <;> simp at h
    have h01_LR : ((0 : Fin 6) ∈ L0 ∨ (1 : Fin 6) ∈ L0) ∧ ((0 : Fin 6) ∈ R0 ∨ (1 : Fin 6) ∈ R0) := by
      have h := heq (pair 0 1); rw [h01_S1, (edgeG_pair 0 1).mpr (by decide)] at h
      simp only [Bool.false_or, Bool.and_eq_true, orOf_pair] at h; exact h.1.1
    have h34 := hLR 3 4 (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide)
    have h35 := hLR 3 5 (Or.inl rfl) (Or.inr (Or.inr rfl)) (by decide)
    have h45 := hLR 4 5 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (by decide)
    obtain ⟨v, hv, h3of4⟩ := four_tri_pigeonhole 3 4 5
      h34.1 h35.1 h45.1 h34.2 h35.2 h45.2
      (hT1_vc 3 4 (by decide)) (hT1_vc 3 5 (by decide)) (hT1_vc 4 5 (by decide))
      (hT2_vc 3 4 (by decide)) (hT2_vc 3 5 (by decide)) (hT2_vc 4 5 (by decide))
    have finish : ∀ u : Fin 6, (u = 0 ∨ u = 1) →
        (u ∈ L0 ∨ v ∈ L0) → (u ∈ R0 ∨ v ∈ R0) → (u ∈ T1 ∨ v ∈ T1) → (u ∈ T2 ∨ v ∈ T2) → False := by
      intro u hu hL hR h1 h2
      have ht : (orOf L0 (pair u v) && orOf R0 (pair u v) && orOf T1 (pair u v) && orOf T2 (pair u v)) = true := by
        simp only [Bool.and_eq_true, orOf_pair]; exact ⟨⟨⟨hL, hR⟩, h1⟩, h2⟩
      exact tri2_nonadj_01 hu hv ((edgeG_pair u v).mp (h4_le _ ht))
    rcases h3of4 with ⟨hL, hR, h1⟩ | ⟨hL, hR, h2⟩ | ⟨hL, h1, h2⟩ | ⟨hR, h1, h2⟩
    · rcases hT2_vc 0 1 (by decide) with h0 | h1'
      · exact finish 0 (Or.inl rfl) (Or.inr hL) (Or.inr hR) (Or.inr h1) (Or.inl h0)
      · exact finish 1 (Or.inr rfl) (Or.inr hL) (Or.inr hR) (Or.inr h1) (Or.inl h1')
    · rcases hT1_vc 0 1 (by decide) with h0 | h1'
      · exact finish 0 (Or.inl rfl) (Or.inr hL) (Or.inr hR) (Or.inl h0) (Or.inr h2)
      · exact finish 1 (Or.inr rfl) (Or.inr hL) (Or.inr hR) (Or.inl h1') (Or.inr h2)
    · rcases h01_LR.2 with h0 | h1'
      · exact finish 0 (Or.inl rfl) (Or.inr hL) (Or.inl h0) (Or.inr h1) (Or.inr h2)
      · exact finish 1 (Or.inr rfl) (Or.inr hL) (Or.inl h1') (Or.inr h1) (Or.inr h2)
    · rcases h01_LR.1 with h0 | h1'
      · exact finish 0 (Or.inl rfl) (Or.inl h0) (Or.inr hR) (Or.inr h1) (Or.inr h2)
      · exact finish 1 (Or.inr rfl) (Or.inl h1') (Or.inr hR) (Or.inr h1) (Or.inr h2)
  -- Symmetrically if S1 doesn't meet {0,1,2}
  have no_S1_miss_tri1 : (∀ u ∈ S1, u ≠ 0 ∧ u ≠ 1 ∧ u ≠ 2) → False := by
    intro hS1_no
    have hLR : ∀ a b : Fin 6, (a = 0 ∨ a = 1 ∨ a = 2) → (b = 0 ∨ b = 1 ∨ b = 2) → isEdge a b →
        (a ∈ L0 ∨ b ∈ L0) ∧ (a ∈ R0 ∨ b ∈ R0) := by
      intro a b ha hb hab
      have h := heq (pair a b)
      rw [(edgeG_pair a b).mpr hab] at h
      have hS1ab : orOf S1 (pair a b) = false := by
        simp only [orOf, pair, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
        intro u hu hor; have := hS1_no u hu
        rcases hor with rfl | rfl
        · rcases ha with rfl | rfl | rfl <;> tauto
        · rcases hb with rfl | rfl | rfl <;> tauto
      rw [hS1ab] at h
      simp only [Bool.false_or, Bool.and_eq_true, orOf_pair] at h
      exact h.1.1
    have h45_S1 : orOf S1 (pair 4 5) = false := by
      simp only [orOf, pair, decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
      intro u hu hor
      have h23 := hS1_only23 u hu
      rcases hor with rfl | rfl <;> rcases h23 with h | h <;> simp at h
    have h45_LR : ((4 : Fin 6) ∈ L0 ∨ (5 : Fin 6) ∈ L0) ∧ ((4 : Fin 6) ∈ R0 ∨ (5 : Fin 6) ∈ R0) := by
      have h := heq (pair 4 5); rw [h45_S1, (edgeG_pair 4 5).mpr (by decide)] at h
      simp only [Bool.false_or, Bool.and_eq_true, orOf_pair] at h; exact h.1.1
    have h01 := hLR 0 1 (Or.inl rfl) (Or.inr (Or.inl rfl)) (by decide)
    have h02 := hLR 0 2 (Or.inl rfl) (Or.inr (Or.inr rfl)) (by decide)
    have h12 := hLR 1 2 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (by decide)
    obtain ⟨u, hu, h3of4⟩ := four_tri_pigeonhole 0 1 2
      h01.1 h02.1 h12.1 h01.2 h02.2 h12.2
      (hT1_vc 0 1 (by decide)) (hT1_vc 0 2 (by decide)) (hT1_vc 1 2 (by decide))
      (hT2_vc 0 1 (by decide)) (hT2_vc 0 2 (by decide)) (hT2_vc 1 2 (by decide))
    have finish : ∀ v : Fin 6, (v = 4 ∨ v = 5) →
        (u ∈ L0 ∨ v ∈ L0) → (u ∈ R0 ∨ v ∈ R0) → (u ∈ T1 ∨ v ∈ T1) → (u ∈ T2 ∨ v ∈ T2) → False := by
      intro v hv hL hR h1 h2
      have ht : (orOf L0 (pair u v) && orOf R0 (pair u v) && orOf T1 (pair u v) && orOf T2 (pair u v)) = true := by
        simp only [Bool.and_eq_true, orOf_pair]; exact ⟨⟨⟨hL, hR⟩, h1⟩, h2⟩
      exact tri1_nonadj_45 hu hv ((edgeG_pair u v).mp (h4_le _ ht))
    rcases h3of4 with ⟨hL, hR, h1⟩ | ⟨hL, hR, h2⟩ | ⟨hL, h1, h2⟩ | ⟨hR, h1, h2⟩
    · rcases hT2_vc 4 5 (by decide) with h4 | h5
      · exact finish 4 (Or.inl rfl) (Or.inl hL) (Or.inl hR) (Or.inl h1) (Or.inr h4)
      · exact finish 5 (Or.inr rfl) (Or.inl hL) (Or.inl hR) (Or.inl h1) (Or.inr h5)
    · rcases hT1_vc 4 5 (by decide) with h4 | h5
      · exact finish 4 (Or.inl rfl) (Or.inl hL) (Or.inl hR) (Or.inr h4) (Or.inl h2)
      · exact finish 5 (Or.inr rfl) (Or.inl hL) (Or.inl hR) (Or.inr h5) (Or.inl h2)
    · rcases h45_LR.2 with h4 | h5
      · exact finish 4 (Or.inl rfl) (Or.inl hL) (Or.inr h4) (Or.inl h1) (Or.inl h2)
      · exact finish 5 (Or.inr rfl) (Or.inl hL) (Or.inr h5) (Or.inl h1) (Or.inl h2)
    · rcases h45_LR.1 with h4 | h5
      · exact finish 4 (Or.inl rfl) (Or.inr h4) (Or.inl hR) (Or.inl h1) (Or.inl h2)
      · exact finish 5 (Or.inr rfl) (Or.inr h5) (Or.inl hR) (Or.inl h1) (Or.inl h2)
  by_cases h3 : (3 : Fin 6) ∈ S1
  · have h2 : (2 : Fin 6) ∉ S1 := fun h2 => hS1_not_both ⟨h2, h3⟩
    apply no_S1_miss_tri1
    intro u hu
    rcases hS1_only23 u hu with rfl | rfl
    · exact absurd hu h2
    · exact ⟨by decide, by decide, by decide⟩
  · apply no_S1_miss_tri2
    intro u hu
    rcases hS1_only23 u hu with rfl | rfl
    · exact ⟨by decide, by decide, by decide⟩
    · exact absurd hu h3

/-! ### Part 5: Master theorem for 3-AND monotone skeleton -/

theorem no_3and_skeleton
    (L0 R0 L1 R1 L2 R2 S3 : Finset (Fin 6))
    (b10 c10 b20 b21 c20 c21 d0 d1 d2 : Bool)
    (heq : ∀ x : Fin 6 → Bool,
      (let a0 := orOf L0 x && orOf R0 x
       let a1 := (orOf L1 x || (b10 && a0)) && (orOf R1 x || (c10 && a0))
       let a2 := (orOf L2 x || (b20 && a0) || (b21 && a1)) &&
                 (orOf R2 x || (c20 && a0) || (c21 && a1))
       orOf S3 x || (d0 && a0) || (d1 && a1) || (d2 && a2)) = edgeG x) :
    False := by
  let a0 : (Fin 6 → Bool) → Bool := fun x => orOf L0 x && orOf R0 x
  let a1 : (Fin 6 → Bool) → Bool := fun x => (orOf L1 x || (b10 && a0 x)) && (orOf R1 x || (c10 && a0 x))
  let a2 : (Fin 6 → Bool) → Bool := fun x =>
    (orOf L2 x || (b20 && a0 x) || (b21 && a1 x)) && (orOf R2 x || (c20 && a0 x) || (c21 && a1 x))
  -- S3 = ∅
  have hS3 : S3 = ∅ := by
    by_contra hne
    obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h := heq (sing u)
    have hSu : orOf S3 (sing u) = true := (orOf_sing S3 u).mpr hu
    rw [hSu, edgeG_sing] at h
    simp at h
  have heq' : ∀ x : Fin 6 → Bool, ((d0 && a0 x) || (d1 && a1 x) || (d2 && a2 x)) = edgeG x := by
    intro x; have h := heq x; rw [hS3, orOf_empty] at h; simpa [a0, a1, a2] using h
  -- Helper: killing a0 at some vertex v gives a 2-AND expression on G - v -> contradiction!
  have no_kill_a0 : ∀ v : Fin 6, (∀ x, x v = false → a0 x = false) → False := by
    intro v hv
    apply no_2and_del_v v L1 R1 L2 R2 ∅ b21 c21 d1 d2
    intro x hxv
    have ha0 : a0 x = false := hv x hxv
    have h := heq' x
    rw [← h]
    simp only [a1, a2, ha0, Bool.and_false, Bool.or_false, Bool.false_or, orOf_empty]
  -- Helper: killing a1 at some vertex v gives a 2-AND expression on G - v -> contradiction!
  have no_kill_a1 : ∀ v : Fin 6, (∀ x, x v = false → a1 x = false) → False := by
    intro v hv
    apply no_2and_del_v v L0 R0 L2 R2 ∅ b20 c20 d0 d2
    intro x hxv
    have ha1 : a1 x = false := hv x hxv
    have h := heq' x
    rw [← h]
    simp only [a0, a2, ha1, Bool.and_false, Bool.or_false, Bool.false_or, orOf_empty]
  -- Helper: killing a2 at some vertex v gives a 2-AND expression on G - v -> contradiction!
  have no_kill_a2 : ∀ v : Fin 6, (∀ x, x v = false → a2 x = false) → False := by
    intro v hv
    apply no_2and_del_v v L0 R0 L1 R1 ∅ b10 c10 d0 d1
    intro x hxv
    have ha2 : a2 x = false := hv x hxv
    have h := heq' x
    rw [← h]
    simp only [a0, a1, ha2, Bool.and_false, Bool.or_false, Bool.false_or, orOf_empty]
  -- Corollary: a0 ≤ edgeG is impossible!
  have no_a0_le : (∀ x, a0 x = true → edgeG x = true) → False := by
    intro hle
    rcases c4_free_biclique (biclique_edges hle) with hL | hR
    · obtain ⟨v, hv⟩ := Finset.card_le_one_iff_subset_singleton.mp hL
      apply no_kill_a0 v
      intro x hxv
      have hL0 : orOf L0 x = false := by
        simp only [orOf, decide_eq_false_iff_not, not_exists, not_and]
        intro i hi hxi; have := Finset.mem_singleton.mp (hv hi); subst this
        rw [hxv] at hxi; cases hxi
      simp [a0, hL0]
    · obtain ⟨v, hv⟩ := Finset.card_le_one_iff_subset_singleton.mp hR
      apply no_kill_a0 v
      intro x hxv
      have hR0 : orOf R0 x = false := by
        simp only [orOf, decide_eq_false_iff_not, not_exists, not_and]
        intro i hi hxi; have := Finset.mem_singleton.mp (hv hi); subst this
        rw [hxv] at hxi; cases hxi
      simp [a0, hR0]
  -- Helper: pure biclique S & T killed by card ≤ 1
  have card_ge_2_of_a1_factor : ∀ T : Finset (Fin 6), (∀ x, a1 x = true → orOf T x = true) → 2 ≤ T.card := by
    intro T hT
    by_contra hlt
    have hle1 : T.card ≤ 1 := by omega
    obtain ⟨v, hv⟩ := Finset.card_le_one_iff_subset_singleton.mp hle1
    apply no_kill_a1 v
    intro x hxv
    cases ha1 : a1 x
    · rfl
    · exfalso
      have hTx := hT x ha1
      simp only [orOf, decide_eq_true_eq] at hTx
      obtain ⟨i, hi, hxi⟩ := hTx
      have := Finset.mem_singleton.mp (hv hi); subst this
      rw [hxv] at hxi; cases hxi
  have card_ge_2_of_a2_factor : ∀ T : Finset (Fin 6), (∀ x, a2 x = true → orOf T x = true) → 2 ≤ T.card := by
    intro T hT
    by_contra hlt
    have hle1 : T.card ≤ 1 := by omega
    obtain ⟨v, hv⟩ := Finset.card_le_one_iff_subset_singleton.mp hle1
    apply no_kill_a2 v
    intro x hxv
    cases ha2 : a2 x
    · rfl
    · exfalso
      have hTx := hT x ha2
      simp only [orOf, decide_eq_true_eq] at hTx
      obtain ⟨i, hi, hxi⟩ := hTx
      have := Finset.mem_singleton.mp (hv hi); subst this
      rw [hxv] at hxi; cases hxi
  -- d0 must be false!
  have hd0 : d0 = false := by
    cases hd : d0
    · rfl
    · exfalso; apply no_a0_le; intro x hx; rw [← heq' x, hd, hx]; simp
  rw [hd0] at heq'
  simp only [Bool.false_and, Bool.false_or] at heq'
  -- Helper for Case A: edgeG = a1 || ((L2 || b20*a0) && (R2 || c20*a0))
  have handle_caseA :
      (∀ x, (a1 x || ((orOf L2 x || (b20 && a0 x)) && (orOf R2 x || (c20 && a0 x)))) = edgeG x) → False := by
    intro hsum
    have ha1_le : ∀ x, a1 x = true → edgeG x = true := by
      intro x h; rw [← hsum x, h]; simp
    have ha2'_le : ∀ x, ((orOf L2 x || (b20 && a0 x)) && (orOf R2 x || (c20 && a0 x))) = true → edgeG x = true := by
      intro x h; rw [← hsum x, h]; simp
    -- Helper: a2' can't have b20 = c20 = false (biclique!) or b20 = c20 = true (a0 ≤ edgeG!)
    -- Actually, notice killing a2' at v gives a 2-AND circuit (a0, a1) on G - v!
    have no_kill_a2' : ∀ v : Fin 6,
        (∀ x, x v = false → ((orOf L2 x || (b20 && a0 x)) && (orOf R2 x || (c20 && a0 x))) = false) → False := by
      intro v hv
      apply no_2and_del_v v L0 R0 L1 R1 ∅ b10 c10 false true
      intro x hxv
      have h := hsum x
      rw [hv x hxv] at h
      simpa [a0, a1, orOf_empty] using h
    have card_ge_2_a2' : ∀ T : Finset (Fin 6),
        (∀ x, ((orOf L2 x || (b20 && a0 x)) && (orOf R2 x || (c20 && a0 x))) = true → orOf T x = true) →
        2 ≤ T.card := by
      intro T hT
      by_contra hlt
      have hle1 : T.card ≤ 1 := by omega
      obtain ⟨v, hv⟩ := Finset.card_le_one_iff_subset_singleton.mp hle1
      apply no_kill_a2' v
      intro x hxv
      cases hval : ((orOf L2 x || (b20 && a0 x)) && (orOf R2 x || (c20 && a0 x)))
      · rfl
      · exfalso
        obtain ⟨i, hi, hxi⟩ := (decide_eq_true_eq.mp (hT x hval))
        have := Finset.mem_singleton.mp (hv hi); subst this
        rw [hxv] at hxi; cases hxi
    -- Neither (b10, c10) nor (b20, c20) can be (false, false) or (true, true)!
    have hbc1 : (b10 = true ∧ c10 = false) ∨ (b10 = false ∧ c10 = true) := by
      cases hb1 : b10 <;> cases hc1 : c10
      · exfalso
        have hle : ∀ x, (orOf L1 x && orOf R1 x) = true → edgeG x = true := by
          intro x hx; apply ha1_le; simpa [a1, hb1, hc1] using hx
        rcases c4_free_biclique (biclique_edges hle) with hL | hR
        · have := card_ge_2_of_a1_factor L1 (fun x hx => by simp [a1, hb1, hc1] at hx; exact hx.1); omega
        · have := card_ge_2_of_a1_factor R1 (fun x hx => by simp [a1, hb1, hc1] at hx; exact hx.2); omega
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exfalso; apply no_a0_le; intro x hx; apply ha1_le; simp [a1, hb1, hc1, hx]
    have hbc2 : (b20 = true ∧ c20 = false) ∨ (b20 = false ∧ c20 = true) := by
      cases hb2 : b20 <;> cases hc2 : c20
      · exfalso
        have hle : ∀ x, (orOf L2 x && orOf R2 x) = true → edgeG x = true := by
          intro x hx; apply ha2'_le; simpa [hb2, hc2] using hx
        rcases c4_free_biclique (biclique_edges hle) with hL | hR
        · have := card_ge_2_a2' L2 (fun x hx => by simp [hb2, hc2] at hx; exact hx.1); omega
        · have := card_ge_2_a2' R2 (fun x hx => by simp [hb2, hc2] at hx; exact hx.2); omega
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exfalso; apply no_a0_le; intro x hx; apply ha2'_le; simp [hb2, hc2, hx]
    rcases hbc1 with ⟨hb1, hc1⟩ | ⟨hb1, hc1⟩ <;> rcases hbc2 with ⟨hb2, hc2⟩ | ⟨hb2, hc2⟩
    · apply no_caseA (L0 := L0) (R0 := R0) (S1 := L1) (T1 := R1) (S2 := L2) (T2 := R2)
      · exact card_ge_2_of_a1_factor R1 (fun x hx => by simp [a1, hb1, hc1] at hx; exact hx.2)
      · exact card_ge_2_a2' R2 (fun x hx => by simp [hb2, hc2] at hx; exact hx.2)
      · intro x; simpa [a0, a1, hb1, hc1, hb2, hc2] using hsum x
    · apply no_caseA (L0 := L0) (R0 := R0) (S1 := L1) (T1 := R1) (S2 := R2) (T2 := L2)
      · exact card_ge_2_of_a1_factor R1 (fun x hx => by simp [a1, hb1, hc1] at hx; exact hx.2)
      · exact card_ge_2_a2' L2 (fun x hx => by simp [hb2, hc2] at hx; exact hx.1)
      · intro x; simpa [a0, a1, hb1, hc1, hb2, hc2, Bool.and_comm] using hsum x
    · apply no_caseA (L0 := L0) (R0 := R0) (S1 := R1) (T1 := L1) (S2 := L2) (T2 := R2)
      · exact card_ge_2_of_a1_factor L1 (fun x hx => by simp [a1, hb1, hc1] at hx; exact hx.1)
      · exact card_ge_2_a2' R2 (fun x hx => by simp [hb2, hc2] at hx; exact hx.2)
      · intro x; simpa [a0, a1, hb1, hc1, hb2, hc2, Bool.and_comm] using hsum x
    · apply no_caseA (L0 := L0) (R0 := R0) (S1 := R1) (T1 := L1) (S2 := R2) (T2 := L2)
      · exact card_ge_2_of_a1_factor L1 (fun x hx => by simp [a1, hb1, hc1] at hx; exact hx.1)
      · exact card_ge_2_a2' L2 (fun x hx => by simp [hb2, hc2] at hx; exact hx.1)
      · intro x; simpa [a0, a1, hb1, hc1, hb2, hc2, Bool.and_comm] using hsum x
  -- Now split on d1, d2!
  cases hd1 : d1 <;> cases hd2 : d2
  · -- d1 = false, d2 = false
    have h := heq' (pair 0 1)
    rw [hd1, hd2, (edgeG_pair 0 1).mpr (by decide)] at h
    simp at h
  · -- d1 = false, d2 = true: edgeG = a2!
    rw [hd1, hd2] at heq'
    simp only [Bool.false_and, Bool.true_and, Bool.false_or] at heq'
    -- Cannot have b20 = c20 = true (else a0 ≤ edgeG)
    have hnot_both20 : ¬(b20 = true ∧ c20 = true) := by
      rintro ⟨hb, hc⟩; apply no_a0_le; intro x hx; rw [← heq' x]; simp [a2, hb, hc, hx]
    -- Helper for Case B when a1 is on LEFT of a2 only (b21 = true, c21 = false)
    have handle_caseB : ∀ (S2 T2 : Finset (Fin 6)) (sb tb : Bool),
        ¬(sb = true ∧ tb = true) →
        (∀ x, ((orOf S2 x || (sb && a0 x) || a1 x) && (orOf T2 x || (tb && a0 x))) = edgeG x) → False := by
      intro S2 T2 sb tb hnot_both hB
      cases htb : tb
      · -- Case B1: R2 = orOf T2 is a vertex cover!
        rw [htb] at hB
        simp only [Bool.false_and, Bool.or_false] at hB
        have hT2_vc : ∀ u v : Fin 6, isEdge u v → u ∈ T2 ∨ v ∈ T2 := by
          intro u v huv; have h := hB (pair u v); rw [(edgeG_pair u v).mpr huv] at h
          simp only [Bool.and_eq_true, orOf_pair] at h; exact h.2
        -- S2 must be ∅! (No single vertex is adjacent to all of T2!)
        have hS2_empty : S2 = ∅ := by
          by_contra hne
          obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          have hadj : ∀ w ∈ T2, isEdge u w := by
            intro w hw
            have ht : ((orOf S2 (pair u w) || (sb && a0 (pair u w)) || a1 (pair u w)) &&
                orOf T2 (pair u w)) = true := by
              simp only [Bool.and_eq_true, Bool.or_eq_true, orOf_pair]
              exact ⟨Or.inl (Or.inl (Or.inl hu)), Or.inr hw⟩
            rw [hB] at ht; exact (edgeG_pair u w).mp ht
          have h01 := hT2_vc 0 1 (by decide)
          have h02 := hT2_vc 0 2 (by decide)
          have h12 := hT2_vc 1 2 (by decide)
          have h34 := hT2_vc 3 4 (by decide)
          have h35 := hT2_vc 3 5 (by decide)
          have h45 := hT2_vc 4 5 (by decide)
          -- T2 has >= 2 vertices in {0,1,2} and >= 2 in {3,4,5}, so no vertex u is adjacent to all of T2!
          have hn1 : ∃ w ∈ T2, ¬isEdge u w := by
            fin_cases u
            · rcases h34 with h | h
              · exact ⟨3, h, by decide⟩
              · exact ⟨4, h, by decide⟩
            · rcases h34 with h | h
              · exact ⟨3, h, by decide⟩
              · exact ⟨4, h, by decide⟩
            · rcases h45 with h | h
              · exact ⟨4, h, by decide⟩
              · exact ⟨5, h, by decide⟩
            · rcases h01 with h | h
              · exact ⟨0, h, by decide⟩
              · exact ⟨1, h, by decide⟩
            · rcases h01 with h | h
              · exact ⟨0, h, by decide⟩
              · exact ⟨1, h, by decide⟩
            · rcases h01 with h | h
              · exact ⟨0, h, by decide⟩
              · exact ⟨1, h, by decide⟩
          obtain ⟨w, hwT, hnw⟩ := hn1
          exact hnw (hadj w hwT)
        rw [hS2_empty] at hB
        simp only [orOf_empty, Bool.false_or] at hB
        cases hsb : sb
        · -- sb = false: edgeG = a1 && T2!
          rw [hsb] at hB; simp only [Bool.false_and, Bool.false_or] at hB
          cases hb1 : b10 <;> cases hc1 : c10
          · -- a1 = L1 && R1 -> edgeG = L1 && R1 && T2 -> kills 2K2!
            have h3 : ∀ x, (orOf L1 x && orOf R1 x && orOf T2 x) = edgeG x := by
              intro x; simpa [a1, hb1, hc1] using hB x
            exact @no_3factor_2k2 L1 R1 T2 0 1 4 5 (by decide) (by decide) (by decide) (by decide)
              (fun u w _ _ h => by rw [← h3]; exact h)
              (by rw [h3, (edgeG_pair 0 1).mpr (by decide)])
              (by rw [h3, (edgeG_pair 4 5).mpr (by decide)])
          · -- b10 = false, c10 = true: edgeG = (R1 || a0) && L1 && T2!
            apply no_caseB1_four (S1 := R1) (L0 := L0) (R0 := R0) (T1 := L1) (T2 := T2)
            intro x
            have h := hB x; simp only [a1, a0, hb1, hc1, Bool.false_and, Bool.true_and, Bool.or_false] at h
            rw [← h]; cases orOf L1 x <;> cases orOf R1 x <;> cases orOf L0 x <;> cases orOf R0 x <;> cases orOf T2 x <;> rfl
          · -- b10 = true, c10 = false: edgeG = (L1 || a0) && R1 && T2!
            apply no_caseB1_four (S1 := L1) (L0 := L0) (R0 := R0) (T1 := R1) (T2 := T2)
            intro x
            have h := hB x; simp only [a1, a0, hb1, hc1, Bool.false_and, Bool.true_and, Bool.or_false] at h
            exact h
          · -- b10 = true, c10 = true: edgeG = (a0 || (L1 && R1)) && T2!
            apply no_caseB1_two3 (L0 := L0) (R0 := R0) (L1 := L1) (R1 := R1) (T2 := T2)
            intro x
            have h := hB x; simp only [a1, a0, hb1, hc1, Bool.true_and] at h
            rw [← h]; cases orOf L1 x <;> cases orOf R1 x <;> cases orOf L0 x <;> cases orOf R0 x <;> cases orOf T2 x <;> rfl
        · -- sb = true: edgeG = (a0 || a1) && T2 = (a0 && T2) || (L1 && R1 && T2)!
          rw [hsb] at hB; simp only [Bool.true_and] at hB
          apply no_caseB1_two3 (L0 := L0) (R0 := R0) (L1 := L1) (R1 := R1) (T2 := T2)
          intro x
          have h := hB x; rw [← h]
          simp only [a0, a1]
          cases b10 <;> cases c10 <;>
            cases orOf L0 x <;> cases orOf R0 x <;> cases orOf L1 x <;> cases orOf R1 x <;> cases orOf T2 x <;> rfl
      · -- Case B2: tb = true (so sb = false!): edgeG = (S2 || a1) && (T2 || a0)!
        have hsb : sb = false := by
          cases hs : sb with
          | false => rfl
          | true => exact absurd ⟨hs, htb⟩ hnot_both
        rw [hsb, htb] at hB
        simp only [Bool.false_and, Bool.true_and, Bool.or_false] at hB
        have hL_ge : ∀ x, edgeG x = true → (orOf S2 x || a1 x) = true := by
          intro x hx; rw [← hB x] at hx; exact (Bool.and_eq_true _ _).mp hx |>.1
        have hR_ge : ∀ x, edgeG x = true → (orOf T2 x || a0 x) = true := by
          intro x hx; rw [← hB x] at hx; exact (Bool.and_eq_true _ _).mp hx |>.2
        have hR_kill : (killed (fun x => orOf T2 x || a0 x)).card ≤ 2 :=
          or_and_kills_le_two hR_ge
        have h8 : (killed edgeG).card ≤
            (killed (fun x => orOf S2 x || a1 x)).card + (killed (fun x => orOf T2 x || a0 x)).card := by
          have heq_f : edgeG = (fun x => (orOf S2 x || a1 x) && (orOf T2 x || a0 x)) :=
            funext (fun x => (hB x).symm)
          rw [heq_f]
          exact killed_and_le _ _
        cases hb1 : b10 <;> cases hc1 : c10
        · -- Form 2b-i: a1 = L1 && R1 -> L kills ≤ 2 -> 2 + 2 < 8!
          have hL_eq : (fun x => orOf S2 x || a1 x) = (fun x => orOf S2 x || (orOf L1 x && orOf R1 x)) := by
            funext x; simp [a1, hb1, hc1]
          have hL_kill : (killed (fun x => orOf S2 x || a1 x)).card ≤ 2 := by
            rw [hL_eq]
            exact or_and_kills_le_two (fun x hx => by rw [← congrFun hL_eq x]; exact hL_ge x hx)
          rw [killed_edgeG] at h8; omega
        · -- Form 2b-ii (b10=false, c10=true): L kills ≤ 3 -> 3 + 2 < 8!
          have hL_eq : (fun x => orOf S2 x || a1 x) =
              (fun x => orOf S2 x || ((orOf R1 x || (orOf L0 x && orOf R0 x)) && orOf L1 x)) := by
            funext x; simp [a1, a0, hb1, hc1, Bool.and_comm]
          have hL_kill : (killed (fun x => orOf S2 x || a1 x)).card ≤ 3 := by
            rw [hL_eq]
            exact nested_kills_le_three (fun x hx => by rw [← congrFun hL_eq x]; exact hL_ge x hx)
          rw [killed_edgeG] at h8; omega
        · -- Form 2b-ii (b10=true, c10=false): L kills ≤ 3 -> 3 + 2 < 8!
          have hL_eq : (fun x => orOf S2 x || a1 x) =
              (fun x => orOf S2 x || ((orOf L1 x || (orOf L0 x && orOf R0 x)) && orOf R1 x)) := by
            funext x; simp [a1, a0, hb1, hc1]
          have hL_kill : (killed (fun x => orOf S2 x || a1 x)).card ≤ 3 := by
            rw [hL_eq]
            exact nested_kills_le_three (fun x hx => by rw [← congrFun hL_eq x]; exact hL_ge x hx)
          rw [killed_edgeG] at h8; omega
        · -- b10 = true, c10 = true: a0 ≤ a1 ≤ L and a0 ≤ R -> a0 ≤ edgeG -> contradiction!
          apply no_a0_le; intro x hx; rw [← hB x]; simp [a1, hb1, hc1, hx]
    -- Now split on b21, c21!
    cases hb21 : b21 <;> cases hc21 : c21
    · -- Neither side of a2 uses a1 -> 2-AND circuit (a0, a2)!
      apply no_kill_a1 0; intro x _
      -- Actually just invoke no_2and_del_v directly!
      exfalso
      apply no_2and_del_v 0 L0 R0 L2 R2 ∅ b20 c20 false true
      intro x _
      have h := heq' x
      simpa [a0, a2, hb21, hc21, orOf_empty] using h
    · -- b21 = false, c21 = true: swap L2 and R2!
      apply handle_caseB R2 L2 c20 b20 (fun ⟨hc, hb⟩ => hnot_both20 ⟨hb, hc⟩)
      intro x; have h := heq' x
      simpa [a2, hb21, hc21, Bool.and_comm] using h
    · -- b21 = true, c21 = false
      apply handle_caseB L2 R2 b20 c20 hnot_both20
      intro x; have h := heq' x
      simpa [a2, hb21, hc21] using h
    · -- b21 = true, c21 = true: a2 = a1 || ((L2 || b20*a0) && (R2 || c20*a0)) -> Case A!
      apply handle_caseA
      intro x
      have h := heq' x
      rw [← h]
      simp only [a2, hb21, hc21, Bool.true_and]
      cases orOf L2 x <;> cases b20 <;> cases a0 x <;> cases a1 x <;> cases orOf R2 x <;> cases c20 <;> rfl
  · -- d1 = true, d2 = false -> 2-AND circuit (a0, a1)!
    apply no_2and_del_v 0 L0 R0 L1 R1 ∅ b10 c10 false true
    intro x _
    have h := heq' x
    simpa [a0, a1, hd1, hd2, orOf_empty] using h
  · -- d1 = true, d2 = true: edgeG = a1 || a2 = a1 || ((L2 || b20*a0) && (R2 || c20*a0)) -> Case A!
    apply handle_caseA
    intro x
    have h := heq' x
    rw [← h]
    simp only [hd1, hd2, Bool.true_and, a2]
    cases a1 x <;> cases b21 <;> cases c21 <;>
      cases orOf L2 x <;> cases b20 <;> cases a0 x <;> cases orOf R2 x <;> cases c20 <;> rfl

/-! ### Part 6: Normalize any Monotone2 circuit with ≤ 3 AND gates to the 3-AND skeleton -/

def evalSpan (acts : List ((Fin 6 → Bool) → Bool)) (S : Finset (Fin 6)) (M : Finset ℕ)
    (x : Fin 6 → Bool) : Bool :=
  orOf S x || decide (∃ m ∈ M, acts.getD m (fun _ => false) x = true)

def IsSpan (acts : List ((Fin 6 → Bool) → Bool)) (f : (Fin 6 → Bool) → Bool) : Prop :=
  ∃ S M, (∀ m ∈ M, m < acts.length) ∧ ∀ x, f x = evalSpan acts S M x

def Rep (acts : List ((Fin 6 → Bool) → Bool)) (f : (Fin 6 → Bool) → Bool) : Prop :=
  (∀ x, f x = true) ∨ IsSpan acts f

def IsValidActs (acts : List ((Fin 6 → Bool) → Bool)) : Prop :=
  ∀ m < acts.length,
    ∃ S1 M1 S2 M2,
      (∀ k ∈ M1, k < m) ∧ (∀ k ∈ M2, k < m) ∧
      ∀ x, acts.getD m (fun _ => false) x = (evalSpan acts S1 M1 x && evalSpan acts S2 M2 x)

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD, List.getElem?_append_left hi]

lemma evalSpan_append (acts : List ((Fin 6 → Bool) → Bool)) (fn : (Fin 6 → Bool) → Bool)
    (S : Finset (Fin 6)) (M : Finset ℕ) (hM : ∀ m ∈ M, m < acts.length) (x : Fin 6 → Bool) :
    evalSpan (acts ++ [fn]) S M x = evalSpan acts S M x := by
  unfold evalSpan
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨m, hm, hmx⟩
    rw [getD_append_left acts [fn] m _ (hM m hm)] at hmx
    exact ⟨m, hm, hmx⟩
  · rintro ⟨m, hm, hmx⟩
    exact ⟨m, hm, by rw [getD_append_left acts [fn] m _ (hM m hm)]; exact hmx⟩

lemma isSpan_append {acts : List ((Fin 6 → Bool) → Bool)} {f : (Fin 6 → Bool) → Bool}
    (fn : (Fin 6 → Bool) → Bool) (h : IsSpan acts f) : IsSpan (acts ++ [fn]) f := by
  obtain ⟨S, M, hM, hfx⟩ := h
  refine ⟨S, M, fun m hm => by simp only [List.length_append, List.length_singleton]; exact Nat.lt_succ_of_lt (hM m hm), fun x => ?_⟩
  rw [hfx x, evalSpan_append acts fn S M hM x]

lemma rep_append {acts : List ((Fin 6 → Bool) → Bool)} {f : (Fin 6 → Bool) → Bool}
    (fn : (Fin 6 → Bool) → Bool) (h : Rep acts f) : Rep (acts ++ [fn]) f := by
  rcases h with ht | hs
  · exact Or.inl ht
  · exact Or.inr (isSpan_append fn hs)

lemma isSpan_false (acts : List ((Fin 6 → Bool) → Bool)) : IsSpan acts (fun _ => false) := by
  refine ⟨∅, ∅, by simp, fun x => ?_⟩
  simp [evalSpan, orOf_empty]

lemma isSpan_or {acts : List ((Fin 6 → Bool) → Bool)} {f g : (Fin 6 → Bool) → Bool}
    (hf : IsSpan acts f) (hg : IsSpan acts g) : IsSpan acts (fun x => f x || g x) := by
  obtain ⟨S1, M1, hM1, hf⟩ := hf
  obtain ⟨S2, M2, hM2, hg⟩ := hg
  refine ⟨S1 ∪ S2, M1 ∪ M2, ?_, fun x => ?_⟩
  · intro m hm
    rcases Finset.mem_union.mp hm with h1 | h2
    · exact hM1 m h1
    · exact hM2 m h2
  · dsimp only
    rw [hf x, hg x]
    apply Bool.eq_iff_iff.mpr
    simp only [evalSpan, orOf_union, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union]
    constructor
    · rintro ((hS1 | ⟨m, hm, hmx⟩) | (hS2 | ⟨m, hm, hmx⟩))
      · exact Or.inl (Or.inl hS1)
      · exact Or.inr ⟨m, Or.inl hm, hmx⟩
      · exact Or.inl (Or.inr hS2)
      · exact Or.inr ⟨m, Or.inr hm, hmx⟩
    · rintro ((hS1 | hS2) | ⟨m, hm1 | hm2, hmx⟩)
      · exact Or.inl (Or.inl hS1)
      · exact Or.inr (Or.inl hS2)
      · exact Or.inl (Or.inr ⟨m, hm1, hmx⟩)
      · exact Or.inr (Or.inr ⟨m, hm2, hmx⟩)

lemma rep_or {acts : List ((Fin 6 → Bool) → Bool)} {f g : (Fin 6 → Bool) → Bool}
    (hf : Rep acts f) (hg : Rep acts g) : Rep acts (fun x => f x || g x) := by
  rcases hf with ht | hsf
  · exact Or.inl (fun x => by dsimp only; rw [ht x]; simp)
  · rcases hg with ht | hsg
    · exact Or.inl (fun x => by dsimp only; rw [ht x]; simp)
    · exact Or.inr (isSpan_or hsf hsg)

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWire_length (gs : List Gate) (init : List Bool) :
    (gs.foldl stepWire init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (stepWire init g)]
    simp [stepWire]
    omega

lemma normalize_gates (gs : List Gate) (A : Finset ℕ)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hA : ∀ j g, gs[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∃ acts : List ((Fin 6 → Bool) → Bool),
      acts.length ≤ (A.filter (· < gs.length)).card ∧
      IsValidActs acts ∧
      ∀ w : ℕ, Rep acts (fun x => (gs.foldl stepWire (List.ofFn x)).getD w false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], by simp, by simp [IsValidActs], fun w => ?_⟩
    by_cases hw : w < 6
    · right
      refine ⟨{⟨w, hw⟩}, ∅, by simp, fun x => ?_⟩
      simp only [List.foldl_nil, evalSpan, orOf_singleton, Finset.notMem_empty, false_and,
        exists_false, decide_false, Bool.or_false, List.getD]
      rw [List.getElem?_ofFn]
      simp [hw]
    · right
      refine ⟨∅, ∅, by simp, fun x => ?_⟩
      simp only [List.foldl_nil, evalSpan, orOf_empty, Finset.notMem_empty, false_and,
        exists_false, decide_false, Bool.false_or, List.getD]
      have hge : (List.ofFn x).length ≤ w := by simp; omega
      rw [List.getElem?_eq_none hge]
      rfl
  | append_singleton gs g ih =>
    have hmono_gs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_append_left _ hg')
    have hA_gs : ∀ j g', gs[j]? = some g' → g'.op = GateOp.and → j ∈ A := by
      intro j g' hj hop
      have hlen : j < gs.length := (List.getElem?_eq_some_iff.mp hj).1
      apply hA j g' _ hop
      rw [List.getElem?_append_left hlen]; exact hj
    obtain ⟨acts, hcard, hvalid, hrep⟩ := ih hmono_gs hA_gs
    let prev : (Fin 6 → Bool) → List Bool := fun x => gs.foldl stepWire (List.ofFn x)
    have hprev_len : ∀ x, (prev x).length = 6 + gs.length := fun x => by
      simp [prev, foldl_stepWire_length]
    let fnew : (Fin 6 → Bool) → Bool := fun x =>
      g.op.eval (g.inputs.map fun i => (prev x).getD i false)
    have hfold : ∀ x, ((gs ++ [g]).foldl stepWire (List.ofFn x)) = prev x ++ [fnew x] := fun x => by
      simp [prev, fnew, stepWire, List.foldl_append]
    have hget_prev : ∀ w, w < 6 + gs.length → ∀ x,
        ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false = (prev x).getD w false := by
      intro w hw x
      rw [hfold x]
      exact getD_append_left (prev x) [fnew x] w false (by rw [hprev_len x]; exact hw)
    have hget_new : ∀ x,
        ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD (6 + gs.length) false = fnew x := by
      intro x
      rw [hfold x, List.getD, List.getElem?_append_right (by rw [hprev_len x])]
      simp [hprev_len x]
    have hget_hi : ∀ w, 6 + gs.length < w → ∀ x : Fin 6 → Bool,
        ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false = false := by
      intro w hw x
      rw [hfold x, List.getD, List.getElem?_eq_none]
      · rfl
      · simp [hprev_len x]; omega
    -- Helper to finish when we don't append to acts
    have finish_same : Rep acts fnew →
        ∃ acts' : List ((Fin 6 → Bool) → Bool),
          acts'.length ≤ (A.filter (· < (gs ++ [g]).length)).card ∧
          IsValidActs acts' ∧
          ∀ w : ℕ, Rep acts' (fun x => ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false) := by
      intro hrf
      refine ⟨acts, ?_, hvalid, fun w => ?_⟩
      · refine le_trans hcard (Finset.card_le_card (fun j hj => ?_))
        simp only [Finset.mem_filter, List.length_append, List.length_singleton] at hj ⊢
        exact ⟨hj.1, Nat.lt_succ_of_lt hj.2⟩
      · rcases lt_trichotomy w (6 + gs.length) with hlt | rfl | hgt
        · have : (fun x => ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false) =
              (fun x => (prev x).getD w false) := funext (hget_prev w hlt)
          rw [this]; exact hrep w
        · have : (fun x => ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD (6 + gs.length) false) = fnew :=
            funext hget_new
          rw [this]; exact hrf
        · have : (fun x => ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false) = (fun _ => false) :=
            funext (hget_hi w hgt)
          rw [this]; exact Or.inr (isSpan_false acts)
    have hg_mono := hmono g (by simp)
    have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg_mono.1
    rcases hg_op with hop_and | hop_or
    · -- g.op = .and
      have hjA : gs.length ∈ A := by
        apply hA gs.length g _ hop_and
        rw [List.getElem?_append_right (le_refl _)]
        simp
      have hcard_inc : (A.filter (· < gs.length)).card + 1 ≤
          (A.filter (· < (gs ++ [g]).length)).card := by
        have hsub : insert gs.length (A.filter (· < gs.length)) ⊆
            A.filter (· < (gs ++ [g]).length) := by
          intro j hj
          simp only [Finset.mem_insert, Finset.mem_filter, List.length_append, List.length_singleton] at hj ⊢
          rcases hj with rfl | ⟨h1, h2⟩
          · exact ⟨hjA, Nat.lt_succ_self _⟩
          · exact ⟨h1, Nat.lt_succ_of_lt h2⟩
        have hnotmem : gs.length ∉ A.filter (· < gs.length) := by simp
        calc (A.filter (· < gs.length)).card + 1
            = (insert gs.length (A.filter (· < gs.length))).card := (Finset.card_insert_of_notMem hnotmem).symm
          _ ≤ (A.filter (· < (gs ++ [g]).length)).card := Finset.card_le_card hsub
      rcases hlen : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨w', t⟩⟩⟩
      · -- inputs = [] -> constTrue!
        apply finish_same
        left; intro x; simp [fnew, hop_and, hlen, GateOp.eval]
      · -- inputs = [u] -> copy wire u!
        apply finish_same
        have : fnew = fun x => (prev x).getD u false := by
          funext x; simp [fnew, hop_and, hlen, GateOp.eval]
        rw [this]; exact hrep u
      · -- inputs = [u, v]
        have hfnew_eq : fnew = fun x => (prev x).getD u false && (prev x).getD v false := by
          funext x; simp [fnew, hop_and, hlen, GateOp.eval]
        rcases hrep u with huT | huS
        · apply finish_same
          have : fnew = fun x => (prev x).getD v false := by
            funext x; rw [hfnew_eq]; dsimp only [prev]; dsimp only at huT; rw [huT x]; simp
          rw [this]; exact hrep v
        · rcases hrep v with hvT | hvS
          · apply finish_same
            have : fnew = fun x => (prev x).getD u false := by
              funext x; rw [hfnew_eq]; dsimp only [prev]; dsimp only at hvT; rw [hvT x]; simp
            rw [this]; exact Or.inr huS
          · -- Both u and v are IsSpan -> append fnew to acts!
            obtain ⟨Su, Mu, hMu, hfu⟩ := huS
            obtain ⟨Sv, Mv, hMv, hfv⟩ := hvS
            refine ⟨acts ++ [fnew], ?_, ?_, ?_⟩
            · simpa only [List.length_append, List.length_singleton] using
                le_trans (Nat.add_le_add_right hcard 1) hcard_inc
            · intro m hm
              simp only [List.length_append, List.length_singleton] at hm
              rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
              · obtain ⟨S1, M1, S2, M2, hM1, hM2, hmeq⟩ := hvalid m hlt
                refine ⟨S1, M1, S2, M2, hM1, hM2, fun x => ?_⟩
                rw [getD_append_left acts [fnew] m _ hlt, hmeq x,
                  evalSpan_append acts fnew S1 M1 (fun k hk => lt_trans (hM1 k hk) hlt),
                  evalSpan_append acts fnew S2 M2 (fun k hk => lt_trans (hM2 k hk) hlt)]
              · refine ⟨Su, Mu, Sv, Mv, hMu, hMv, fun x => ?_⟩
                have hget : (acts ++ [fnew]).getD acts.length (fun _ => false) x = fnew x := by
                  simp [List.getD]
                rw [hget, evalSpan_append acts fnew Su Mu hMu x,
                  evalSpan_append acts fnew Sv Mv hMv x, hfnew_eq]
                dsimp only [prev]
                dsimp only at hfu hfv
                rw [hfu x, hfv x]
            · intro w
              rcases lt_trichotomy w (6 + gs.length) with hlt | rfl | hgt
              · have : (fun x => ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false) =
                    (fun x => (prev x).getD w false) := funext (hget_prev w hlt)
                rw [this]; exact rep_append fnew (hrep w)
              · have : (fun x => ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD (6 + gs.length) false) = fnew :=
                  funext hget_new
                rw [this]
                right
                refine ⟨∅, {acts.length}, by simp, fun x => ?_⟩
                simp [evalSpan, orOf_empty, List.getD]
              · have : (fun x => ((gs ++ [g]).foldl stepWire (List.ofFn x)).getD w false) = (fun _ => false) :=
                  funext (hget_hi w hgt)
                rw [this]; exact Or.inr (isSpan_false _)
      · -- inputs length >= 3 contradicts length ≤ 2
        have := hg_mono.2; rw [hlen] at this; simp at this
    · -- g.op = .or
      apply finish_same
      rcases hlen : g.inputs with _ | ⟨u, _ | ⟨v, _ | ⟨w', t⟩⟩⟩
      · right
        have : fnew = fun _ => false := by funext x; simp [fnew, hop_or, hlen, GateOp.eval]
        rw [this]; exact isSpan_false acts
      · have : fnew = fun x => (prev x).getD u false := by
          funext x; simp [fnew, hop_or, hlen, GateOp.eval]
        rw [this]; exact hrep u
      · have : fnew = fun x => (prev x).getD u false || (prev x).getD v false := by
          funext x; simp [fnew, hop_or, hlen, GateOp.eval]
        rw [this]; exact rep_or (hrep u) (hrep v)
      · have := hg_mono.2; rw [hlen] at this; simp at this

/-! ### Part 7: Extract 3-AND skeleton and conclude L_meta_282 -/

lemma evalSpan_lt0 (acts : List ((Fin 6 → Bool) → Bool)) (S : Finset (Fin 6)) (M : Finset ℕ)
    (hM : ∀ k ∈ M, k < 0) (x : Fin 6 → Bool) :
    evalSpan acts S M x = orOf S x := by
  have hMe : M = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk; exact absurd (hM k hk) (Nat.not_lt_zero k)
  simp [evalSpan, hMe]

lemma evalSpan_lt1 (acts : List ((Fin 6 → Bool) → Bool)) (S : Finset (Fin 6)) (M : Finset ℕ)
    (hM : ∀ k ∈ M, k < 1) (x : Fin 6 → Bool) :
    evalSpan acts S M x = (orOf S x || (decide (0 ∈ M) && acts.getD 0 (fun _ => false) x)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [evalSpan, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hS | ⟨m, hm, hmx⟩)
    · exact Or.inl hS
    · have hm0 : m = 0 := by have := hM m hm; omega
      subst hm0
      exact Or.inr ⟨hm, hmx⟩
  · rintro (hS | ⟨h0, h0x⟩)
    · exact Or.inl hS
    · exact Or.inr ⟨0, h0, h0x⟩

lemma evalSpan_lt2 (acts : List ((Fin 6 → Bool) → Bool)) (S : Finset (Fin 6)) (M : Finset ℕ)
    (hM : ∀ k ∈ M, k < 2) (x : Fin 6 → Bool) :
    evalSpan acts S M x =
      (orOf S x || (decide (0 ∈ M) && acts.getD 0 (fun _ => false) x) ||
        (decide (1 ∈ M) && acts.getD 1 (fun _ => false) x)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [evalSpan, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hS | ⟨m, hm, hmx⟩)
    · exact Or.inl (Or.inl hS)
    · have : m = 0 ∨ m = 1 := by have := hM m hm; omega
      rcases this with rfl | rfl
      · exact Or.inl (Or.inr ⟨hm, hmx⟩)
      · exact Or.inr ⟨hm, hmx⟩
  · rintro ((hS | ⟨h0, h0x⟩) | ⟨h1, h1x⟩)
    · exact Or.inl hS
    · exact Or.inr ⟨0, h0, h0x⟩
    · exact Or.inr ⟨1, h1, h1x⟩

lemma evalSpan_lt3 (acts : List ((Fin 6 → Bool) → Bool)) (S : Finset (Fin 6)) (M : Finset ℕ)
    (hM : ∀ k ∈ M, k < 3) (x : Fin 6 → Bool) :
    evalSpan acts S M x =
      (orOf S x || (decide (0 ∈ M) && acts.getD 0 (fun _ => false) x) ||
        (decide (1 ∈ M) && acts.getD 1 (fun _ => false) x) ||
        (decide (2 ∈ M) && acts.getD 2 (fun _ => false) x)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [evalSpan, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hS | ⟨m, hm, hmx⟩)
    · exact Or.inl (Or.inl (Or.inl hS))
    · have : m = 0 ∨ m = 1 ∨ m = 2 := by have := hM m hm; omega
      rcases this with rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inr ⟨hm, hmx⟩))
      · exact Or.inl (Or.inr ⟨hm, hmx⟩)
      · exact Or.inr ⟨hm, hmx⟩
  · rintro (((hS | ⟨h0, h0x⟩) | ⟨h1, h1x⟩) | ⟨h2, h2x⟩)
    · exact Or.inl hS
    · exact Or.inr ⟨0, h0, h0x⟩
    · exact Or.inr ⟨1, h1, h1x⟩
    · exact Or.inr ⟨2, h2, h2x⟩

theorem main_proof :
    ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (PEqualNP.MetaComplexity.Monotone2 C ∧
        (∃ A : Finset ℕ, A.card ≤ 3 ∧
          ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
            C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧
      (∀ x : Fin 6 → Bool,
        (C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 6,
            (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧
            x u = true ∧ x v = true)) := by
  rintro ⟨C, ⟨hmono, ⟨A, hAcard, hA⟩⟩, heval⟩
  have heval_eq : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = edgeG x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [edgeG, edgesList, decide_eq_true_eq]
    exact heval x
  obtain ⟨acts, hacts_len, hvalid, hrep⟩ := normalize_gates C.gates A hmono hA
  have hlen3 : acts.length ≤ 3 :=
    le_trans hacts_len (le_trans (Finset.card_filter_le A _) hAcard)
  -- Output wire representation
  have hrep_out : Rep acts edgeG := by
    have h := hrep C.output
    have hfun : (fun x => (C.gates.foldl stepWire (List.ofFn x)).getD C.output false) = edgeG := by
      funext x
      rw [← heval_eq x]
      rfl
    rwa [hfun] at h
  -- Cannot be constTrue since edgeG (fun _ => false) = false
  rcases hrep_out with hconst | ⟨S3, M3, hM3, hS3⟩
  · have h := hconst (fun _ => false); rw [edgeG_false] at h; cases h
  -- Extract parameters for a0, a1, a2
  have h0 : ∃ L0 R0 : Finset (Fin 6), ∀ x, acts.getD 0 (fun _ => false) x = (orOf L0 x && orOf R0 x) := by
    by_cases hlt : 0 < acts.length
    · obtain ⟨S1, M1, S2, M2, hM1, hM2, heq0⟩ := hvalid 0 hlt
      refine ⟨S1, S2, fun x => ?_⟩
      rw [heq0 x, evalSpan_lt0 acts S1 M1 hM1 x, evalSpan_lt0 acts S2 M2 hM2 x]
    · refine ⟨∅, ∅, fun x => ?_⟩
      simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none,
        orOf_empty, Bool.and_self]
  have h1 : ∃ (L1 R1 : Finset (Fin 6)) (b10 c10 : Bool), ∀ x,
      acts.getD 1 (fun _ => false) x =
        ((orOf L1 x || (b10 && acts.getD 0 (fun _ => false) x)) &&
         (orOf R1 x || (c10 && acts.getD 0 (fun _ => false) x))) := by
    by_cases hlt : 1 < acts.length
    · obtain ⟨S1, M1, S2, M2, hM1, hM2, heq1⟩ := hvalid 1 hlt
      refine ⟨S1, S2, decide (0 ∈ M1), decide (0 ∈ M2), fun x => ?_⟩
      rw [heq1 x, evalSpan_lt1 acts S1 M1 hM1 x, evalSpan_lt1 acts S2 M2 hM2 x]
    · refine ⟨∅, ∅, false, false, fun x => ?_⟩
      simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none,
        orOf_empty, Bool.false_and, Bool.or_false, Bool.and_self]
  have h2 : ∃ (L2 R2 : Finset (Fin 6)) (b20 b21 c20 c21 : Bool), ∀ x,
      acts.getD 2 (fun _ => false) x =
        ((orOf L2 x || (b20 && acts.getD 0 (fun _ => false) x) || (b21 && acts.getD 1 (fun _ => false) x)) &&
         (orOf R2 x || (c20 && acts.getD 0 (fun _ => false) x) || (c21 && acts.getD 1 (fun _ => false) x))) := by
    by_cases hlt : 2 < acts.length
    · obtain ⟨S1, M1, S2, M2, hM1, hM2, heq2⟩ := hvalid 2 hlt
      refine ⟨S1, S2, decide (0 ∈ M1), decide (1 ∈ M1), decide (0 ∈ M2), decide (1 ∈ M2), fun x => ?_⟩
      rw [heq2 x, evalSpan_lt2 acts S1 M1 hM1 x, evalSpan_lt2 acts S2 M2 hM2 x]
    · refine ⟨∅, ∅, false, false, false, false, fun x => ?_⟩
      simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt), Option.getD_none,
        orOf_empty, Bool.false_and, Bool.or_false, Bool.and_self]
  obtain ⟨L0, R0, ha0⟩ := h0
  obtain ⟨L1, R1, b10, c10, ha1⟩ := h1
  obtain ⟨L2, R2, b20, b21, c20, c21, ha2⟩ := h2
  apply no_3and_skeleton L0 R0 L1 R1 L2 R2 S3 b10 c10 b20 b21 c20 c21
    (decide (0 ∈ M3)) (decide (1 ∈ M3)) (decide (2 ∈ M3))
  intro x
  have hM3_lt : ∀ k ∈ M3, k < 3 := fun k hk => lt_of_lt_of_le (hM3 k hk) hlen3
  have hout := hS3 x
  rw [evalSpan_lt3 acts S3 M3 hM3_lt x] at hout
  rw [hout]
  simp only [ha2 x, ha1 x, ha0 x]

end PEqualNP.Outside.L_meta_282_aux

theorem PEqualNP.Outside.L_meta_282 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) :=
  PEqualNP.Outside.L_meta_282_aux.main_proof
