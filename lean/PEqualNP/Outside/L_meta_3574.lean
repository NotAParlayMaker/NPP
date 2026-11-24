import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3574
open PEqualNP.CircuitLowerBounds



def NN {n : ℕ} (L : List (Finset (Fin n))) (X W : Finset (Fin n)) : Finset (Fin L.length) :=
  Finset.univ.filter fun i => 1 < (L.get i).card ∧ L.get i ⊆ X ∧ ¬ L.get i ⊆ W

def br {n : ℕ} (X W : Finset (Fin n)) : ℕ := if Disjoint X W then 1 else 0

def GG {n : ℕ} (L : List (Finset (Fin n))) (X : Finset (Fin n)) : Prop :=
  ∀ W, (X \ W).card ≤ (NN L X W).card + br X W

theorem small_good {n : ℕ} (L : List (Finset (Fin n))) (X : Finset (Fin n)) (h : X.card ≤ 1) :
    GG L X := by
  intro W
  unfold br
  split_ifs with hd
  · have := Finset.card_le_card (Finset.sdiff_subset (s := X) (t := W))
    omega
  · obtain ⟨a, ha, haW⟩ := Finset.not_disjoint_iff.1 hd
    have hsub : X ⊆ W := by
      intro b hb
      rw [Finset.card_le_one.1 h b hb a ha]; exact haW
    rw [Finset.sdiff_eq_empty_iff_subset.2 hsub]
    simp

theorem step {n : ℕ} (L : List (Finset (Fin n)))
    (h : ∀ (i : ℕ) (S : Finset (Fin n)), L[i]? = some S → ∃ A B : Finset (Fin n), S = A ∪ B ∧
      (A.card ≤ 1 ∨ A ∈ L.take i) ∧ (B.card ≤ 1 ∨ B ∈ L.take i))
    (k : Fin L.length) (hprev : ∀ j : Fin L.length, j.1 < k.1 → GG L (L.get j)) :
    GG L (L.get k) := by
  obtain ⟨A, B, hS, hA, hB⟩ := h k.1 (L.get k) (List.getElem?_eq_getElem k.2)
  have good : ∀ Y : Finset (Fin n), (Y.card ≤ 1 ∨ Y ∈ L.take k.1) → GG L Y := by
    intro Y hY
    rcases hY with hY | hY
    · exact small_good L Y hY
    · obtain ⟨i, hi, e⟩ := List.getElem_of_mem hY
      rw [List.getElem_take] at e
      have hlt : i < k.1 := by rw [List.length_take] at hi; omega
      have hlt' : i < L.length := lt_trans hlt k.2
      have := hprev ⟨i, hlt'⟩ hlt
      rw [show L.get ⟨i, hlt'⟩ = Y from e] at this
      exact this
  have gA := good A hA
  have gB := good B hB
  by_cases hBA : B ⊆ A
  · rw [hS, Finset.union_eq_left.2 hBA]; exact gA
  by_cases hAB : A ⊆ B
  · rw [hS, Finset.union_eq_right.2 hAB]; exact gB
  intro W
  by_cases hSW : L.get k ⊆ W
  · rw [Finset.sdiff_eq_empty_iff_subset.2 hSW]; simp
  have hbig : 1 < (L.get k).card := by
    obtain ⟨a, ha, haB⟩ := Finset.not_subset.1 hAB
    obtain ⟨b, hb, hbA⟩ := Finset.not_subset.1 hBA
    rw [Finset.one_lt_card]
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [hS]; exact Finset.mem_union_left _ ha
    · rw [hS]; exact Finset.mem_union_right _ hb
    · intro hab; rw [hab] at ha; exact hbA ha
  have hAS : A ⊆ L.get k := by rw [hS]; exact Finset.subset_union_left
  have hBS : B ⊆ L.get k := by rw [hS]; exact Finset.subset_union_right
  have h1 : (L.get k \ W).card ≤ (A \ W).card + (B \ (W ∪ A)).card := by
    have hsub : L.get k \ W ⊆ (A \ W) ∪ (B \ (W ∪ A)) := by
      intro x hx
      rw [hS] at hx
      simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
      tauto
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hkA : k ∉ NN L A W := by
    intro hk
    have := (Finset.mem_filter.1 hk).2.2.1
    exact hBA (fun x hx => this (hBS hx))
  have hkB : k ∉ NN L B (W ∪ A) := by
    intro hk
    have := (Finset.mem_filter.1 hk).2.2.1
    exact hAB (fun x hx => this (hAS hx))
  have hdis : Disjoint (NN L A W) (NN L B (W ∪ A)) := by
    rw [Finset.disjoint_left]
    intro i hi hi2
    have h3 := (Finset.mem_filter.1 hi).2.2.1
    have h4 := (Finset.mem_filter.1 hi2).2.2.2
    exact h4 (fun x hx => Finset.mem_union_right _ (h3 hx))
  have h2 : (NN L A W).card + (NN L B (W ∪ A)).card + 1 ≤ (NN L (L.get k) W).card := by
    have hsub : insert k (NN L A W ∪ NN L B (W ∪ A)) ⊆ NN L (L.get k) W := by
      intro i hi
      rcases Finset.mem_insert.1 hi with hi | hi
      · rw [hi]
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hbig, Finset.Subset.refl _, hSW⟩
      · rcases Finset.mem_union.1 hi with hi | hi
        · obtain ⟨_, p1, p2, p3⟩ := Finset.mem_filter.1 hi
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, p1, fun x hx => hAS (p2 hx), p3⟩
        · obtain ⟨_, p1, p2, p3⟩ := Finset.mem_filter.1 hi
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, p1, fun x hx => hBS (p2 hx),
            fun hc => p3 (fun x hx => Finset.mem_union_left _ (hc hx))⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by
      intro hk; rcases Finset.mem_union.1 hk with hk | hk
      · exact hkA hk
      · exact hkB hk), Finset.card_union_of_disjoint hdis] at hc
    exact hc
  have h3 : br A W + br B (W ∪ A) ≤ 1 + br (L.get k) W := by
    unfold br
    split_ifs with d1 d2 d3 d3 d2 d3 d3 <;> try omega
    exfalso
    apply d3
    rw [hS, Finset.disjoint_union_left]
    exact ⟨d1, Disjoint.mono_right Finset.subset_union_left d2⟩
  have := gA W
  have := gB (W ∪ A)
  omega

theorem main {n : ℕ} (L : List (Finset (Fin n)))
    (h : ∀ (i : ℕ) (S : Finset (Fin n)), L[i]? = some S → ∃ A B : Finset (Fin n), S = A ∪ B ∧
      (A.card ≤ 1 ∨ A ∈ L.take i) ∧ (B.card ≤ 1 ∨ B ∈ L.take i)) :
    ∀ m, ∀ k : Fin L.length, k.1 = m → GG L (L.get k) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk
    apply step L h
    intro j hj
    exact ih j.1 (hk ▸ hj) j rfl

end PEqualNP.Outside.L_meta_3574

open PEqualNP.Outside.L_meta_3574 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3574 : ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) := by
  intro n L h S hS
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hS
  have g := main L h i ⟨i, hi⟩ rfl ∅
  rw [show L.get ⟨i, hi⟩ = S from e] at g
  rw [Finset.sdiff_empty] at g
  have hbr : br S ∅ = 1 := by unfold br; simp
  rw [hbr] at g
  refine le_trans g ?_
  rw [Fintype.card_subtype]
  apply Nat.add_le_add_right
  apply Finset.card_le_card
  intro j hj
  obtain ⟨_, p1, p2, _⟩ := Finset.mem_filter.1 hj
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, p1, p2⟩
