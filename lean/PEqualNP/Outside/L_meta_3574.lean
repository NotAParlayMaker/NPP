import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3574

-- Union-find count. Fm m maps every element to a class label; at each listed set of size at
-- least two inside S, all classes meeting that set are merged into one. Each merge loses at
-- most one class of S (the set is a union of two pieces, each already inside one class), and
-- at the end S is one class.
noncomputable def mrg {n : ℕ} (T : Finset (Fin n)) (f : Fin n → Fin n) (c : Fin n) : Fin n :=
  if h : (T.image f).Nonempty then (if c ∈ T.image f then (T.image f).min' h else c) else c

def P {n : ℕ} (S : Finset (Fin n)) (L : List (Finset (Fin n))) (m : ℕ) : Prop :=
  1 < (L.getD m ∅).card ∧ L.getD m ∅ ⊆ S

noncomputable def Fm {n : ℕ} (S : Finset (Fin n)) (L : List (Finset (Fin n))) :
    ℕ → Fin n → Fin n
  | 0 => id
  | m + 1 => if 1 < (L.getD m ∅).card ∧ L.getD m ∅ ⊆ S then
      (mrg (L.getD m ∅) (Fm S L m)) ∘ (Fm S L m) else Fm S L m

theorem mrg_const {n : ℕ} (T : Finset (Fin n)) (f : Fin n → Fin n) (x y : Fin n) (hx : x ∈ T)
    (hy : y ∈ T) : mrg T f (f x) = mrg T f (f y) := by
  have hne : (T.image f).Nonempty := ⟨f x, Finset.mem_image_of_mem f hx⟩
  simp only [mrg, hne, dite_true, Finset.mem_image_of_mem f hx, Finset.mem_image_of_mem f hy,
    ite_true]

theorem image_step {n : ℕ} (S T : Finset (Fin n)) (f : Fin n → Fin n) (hT : T ⊆ S)
    (hne : T.Nonempty) :
    (S.image f).card + 1 ≤ (S.image (mrg T f ∘ f)).card + (T.image f).card := by
  have hTi : (T.image f).Nonempty := hne.image f
  set m0 := (T.image f).min' hTi
  have hm0 : m0 ∈ T.image f := Finset.min'_mem _ _
  have hsub : (S.image f \ T.image f) ∪ {m0} ⊆ S.image (mrg T f ∘ f) := by
    intro c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · obtain ⟨hc1, hc2⟩ := Finset.mem_sdiff.1 hc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc1
      refine Finset.mem_image.2 ⟨x, hx, ?_⟩
      simp only [Function.comp, mrg, hTi, dite_true, hc2, ite_false]
    · rw [Finset.mem_singleton.1 hc]
      obtain ⟨y, hy, hfy⟩ := Finset.mem_image.1 hm0
      refine Finset.mem_image.2 ⟨y, hT hy, ?_⟩
      simp only [Function.comp, mrg, hTi, dite_true, Finset.mem_image_of_mem f hy, ite_true, m0]
  have hdis : Disjoint (S.image f \ T.image f) {m0} := by
    rw [Finset.disjoint_singleton_right]
    intro h
    exact (Finset.mem_sdiff.1 h).2 hm0
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_singleton] at h1
  have h2 : T.image f ⊆ S.image f := Finset.image_subset_image hT
  have h3 := Finset.card_sdiff_add_card_eq_card h2
  omega

def cnt {n : ℕ} (S : Finset (Fin n)) (L : List (Finset (Fin n))) (m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun j => 1 < (L.getD j ∅).card ∧ L.getD j ∅ ⊆ S)).card

theorem inv {n : ℕ} (S : Finset (Fin n)) (L : List (Finset (Fin n)))
    (hL : ∀ (k : ℕ) (X : Finset (Fin n)), L[k]? = some X → ∃ A B : Finset (Fin n), X = A ∪ B ∧
      (A.card ≤ 1 ∨ A ∈ L.take k) ∧ (B.card ≤ 1 ∨ B ∈ L.take k)) :
    ∀ m : ℕ, (∀ i < m, 1 < (L.getD i ∅).card ∧ L.getD i ∅ ⊆ S →
      ∀ x ∈ L.getD i ∅, ∀ y ∈ L.getD i ∅, Fm S L m x = Fm S L m y) ∧
      S.card ≤ (S.image (Fm S L m)).card + cnt S L m := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
    simp [Fm, cnt]
  | succ m ih =>
    obtain ⟨ihc, ihn⟩ := ih
    by_cases hP : 1 < (L.getD m ∅).card ∧ L.getD m ∅ ⊆ S
    · have hFm : Fm S L (m + 1) = mrg (L.getD m ∅) (Fm S L m) ∘ Fm S L m := by
        rw [Fm, ite_eq_left hP]
      have hmlt : m < L.length := by
        by_contra h
        push Not at h
        rw [List.getD_eq_default _ _ h] at hP
        simp at hP
      have hget : L[m]? = some (L.getD m ∅) := by
        rw [List.getD_eq_getElem _ _ hmlt, List.getElem?_eq_getElem hmlt]
      obtain ⟨A, B, hAB, hA, hB⟩ := hL m _ hget
      have piece : ∀ C : Finset (Fin n), C ⊆ L.getD m ∅ → (C.card ≤ 1 ∨ C ∈ L.take m) →
          ∀ x ∈ C, ∀ y ∈ C, Fm S L m x = Fm S L m y := by
        intro C hCT hC x hx y hy
        by_cases hc1 : C.card ≤ 1
        · rw [Finset.card_le_one.1 hc1 x hx y hy]
        · rcases hC with hC | hC
          · exact absurd hC hc1
          · obtain ⟨i, hi, hiC⟩ := List.mem_iff_getElem.1 hC
            rw [List.length_take] at hi
            have him : i < m := by omega
            have hiL : i < L.length := by omega
            have hCi : L.getD i ∅ = C := by
              rw [List.getD_eq_getElem _ _ hiL, ← hiC, List.getElem_take]
            have hPi : 1 < (L.getD i ∅).card ∧ L.getD i ∅ ⊆ S := by
              rw [hCi]
              exact ⟨by omega, hCT.trans hP.2⟩
            exact ihc i him hPi x (by rw [hCi]; exact hx) y (by rw [hCi]; exact hy)
      have hone : ∀ C : Finset (Fin n), C ⊆ L.getD m ∅ → (C.card ≤ 1 ∨ C ∈ L.take m) →
          (C.image (Fm S L m)).card ≤ 1 := by
        intro C hCT hC
        apply Finset.card_le_one.2
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
        exact piece C hCT hC x hx y hy
      have hTimg : ((L.getD m ∅).image (Fm S L m)).card ≤ 2 := by
        rw [hAB, Finset.image_union]
        refine (Finset.card_union_le _ _).trans ?_
        have h1 := hone A (hAB ▸ Finset.subset_union_left) hA
        have h2 := hone B (hAB ▸ Finset.subset_union_right) hB
        omega
      have hne : (L.getD m ∅).Nonempty := Finset.card_pos.1 (by omega)
      have hstep := image_step S (L.getD m ∅) (Fm S L m) hP.2 hne
      refine ⟨?_, ?_⟩
      · intro i hi hPi x hx y hy
        rw [hFm]
        by_cases him : i = m
        · subst him
          exact mrg_const _ _ x y hx hy
        · have := ihc i (by omega) hPi x hx y hy
          simp only [Function.comp, this]
      · rw [hFm]
        have hc : cnt S L (m + 1) = cnt S L m + 1 := by
          simp only [cnt, Finset.range_add_one, Finset.filter_insert, hP, and_self, ↓reduceIte]
          rw [Finset.card_insert_of_notMem (by simp)]
        rw [hc]
        omega
    · have hFm : Fm S L (m + 1) = Fm S L m := by
        rw [Fm, ite_eq_right hP]
      have hc : cnt S L (m + 1) = cnt S L m := by
        simp only [cnt, Finset.range_add_one, Finset.filter_insert, hP, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · intro i hi hPi
        rw [hFm]
        have : i ≠ m := fun h => hP (h ▸ hPi)
        exact ihc i (by omega) hPi
      · rw [hFm, hc]
        exact ihn

end PEqualNP.Outside.L_meta_3574

theorem PEqualNP.Outside.L_meta_3574 : ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) := by
  intro n L hL S hS
  by_cases h1 : S.card ≤ 1
  · omega
  · obtain ⟨k, hk, hkS⟩ := List.mem_iff_getElem.1 hS
    have hgetk : L.getD k ∅ = S := by rw [List.getD_eq_getElem _ _ hk, hkS]
    have hPk : 1 < (L.getD k ∅).card ∧ L.getD k ∅ ⊆ S := by
      rw [hgetk]
      exact ⟨by omega, Finset.Subset.refl _⟩
    obtain ⟨hc, hn⟩ := PEqualNP.Outside.L_meta_3574.inv S L hL L.length
    have hconst := hc k hk hPk
    have himg : (S.image (PEqualNP.Outside.L_meta_3574.Fm S L L.length)).card ≤ 1 := by
      apply Finset.card_le_one.2
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
      exact hconst x (by rw [hgetk]; exact hx) y (by rw [hgetk]; exact hy)
    have hcnt : PEqualNP.Outside.L_meta_3574.cnt S L L.length =
        Fintype.card {x6 : Fin L.length // 1 < (L.get x6).card ∧ L.get x6 ⊆ S} := by
      rw [Fintype.card_subtype, PEqualNP.Outside.L_meta_3574.cnt, ← Finset.card_map Fin.valEmbedding]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply]
      constructor
      · rintro ⟨hj, hPj⟩
        refine ⟨⟨j, hj⟩, ?_, rfl⟩
        rw [List.get_eq_getElem, ← List.getD_eq_getElem L ∅ hj]
        exact hPj
      · rintro ⟨⟨j', hj'⟩, hQ, rfl⟩
        refine ⟨hj', ?_⟩
        rw [List.getD_eq_getElem L ∅ hj']
        rw [List.get_eq_getElem] at hQ
        exact hQ
    omega
