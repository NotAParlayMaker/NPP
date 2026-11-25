import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8835
open PEqualNP.CircuitLowerBounds



def supF (x2 : ℕ) (a b : ℕ → ℕ) : ℕ → ℕ → Finset ℕ
  | 0, w => if w < x2 then {w} else ∅
  | k + 1, w => if w = x2 + k then supF x2 a b k (a k) ∪ supF x2 a b k (b k) else supF x2 a b k w

theorem supF_top (x2 : ℕ) (a b : ℕ → ℕ) (k : ℕ) :
    supF x2 a b (k + 1) (x2 + k) = supF x2 a b k (a k) ∪ supF x2 a b k (b k) := by
  simp [supF]

theorem supF_old (x2 : ℕ) (a b : ℕ → ℕ) (k w : ℕ) (h : w ≠ x2 + k) :
    supF x2 a b (k + 1) w = supF x2 a b k w := by
  simp [supF, h]

theorem supF_sub (x2 : ℕ) (a b : ℕ → ℕ) : ∀ k w, supF x2 a b k w ⊆ Finset.range x2 := by
  intro k
  induction k with
  | zero =>
    intro w
    by_cases h : w < x2
    · simp [supF, h]
    · simp [supF, h]
  | succ k ih =>
    intro w
    by_cases h : w = x2 + k
    · subst h
      rw [supF_top]
      exact Finset.union_subset (ih _) (ih _)
    · rw [supF_old _ _ _ _ _ h]
      exact ih w

theorem supF_cnt (x2 : ℕ) (a b : ℕ → ℕ) : ∀ k (W : Finset ℕ),
    (W.biUnion (supF x2 a b k)).card ≤ k + W.card := by
  intro k
  induction k with
  | zero =>
    intro W
    refine le_trans Finset.card_biUnion_le ?_
    rw [zero_add, Finset.card_eq_sum_ones]
    apply Finset.sum_le_sum
    intro j _
    by_cases h : j < x2
    · simp [supF, h]
    · simp [supF, h]
  | succ k ih =>
    intro W
    by_cases hW : x2 + k ∈ W
    · have hsub : W.biUnion (supF x2 a b (k + 1))
          ⊆ (W.erase (x2 + k) ∪ {a k, b k}).biUnion (supF x2 a b k) := by
        intro i hi
        rw [Finset.mem_biUnion] at hi ⊢
        obtain ⟨j, hj, hij⟩ := hi
        by_cases hjk : j = x2 + k
        · subst hjk
          rw [supF_top] at hij
          rcases Finset.mem_union.1 hij with h | h
          · exact ⟨a k, by simp, h⟩
          · exact ⟨b k, by simp, h⟩
        · rw [supF_old _ _ _ _ _ hjk] at hij
          exact ⟨j, by simp [hj, hjk], hij⟩
      have h1 := Finset.card_le_card hsub
      have h2 := ih (W.erase (x2 + k) ∪ {a k, b k})
      have h3 : (W.erase (x2 + k) ∪ {a k, b k}).card ≤ (W.erase (x2 + k)).card + 2 :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left Finset.card_le_two _)
      have h4 := Finset.card_erase_of_mem hW
      have h5 := Finset.card_pos.2 ⟨_, hW⟩
      omega
    · have heq : W.biUnion (supF x2 a b (k + 1)) = W.biUnion (supF x2 a b k) :=
        Finset.biUnion_congr rfl (fun j hj => supF_old _ _ _ _ _ (by rintro rfl; exact hW hj))
      rw [heq]
      exact le_trans (ih W) (by omega)

end PEqualNP.Outside.L_meta_8835

open PEqualNP.Outside.L_meta_8835 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8835 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1), x4 < x2 + x3 → (∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x5 (x2 + x7) = x5 x9 ∪ x5 x10 ∨ x5 (x2 + x7) = x5 x9 ∨ x5 (x2 + x7) = ∅ ∨ x5 (x2 + x7) = x5 x9 ∩ x5 x10) → (∀ x8 < x2, ∃ (x10 : x1) (x11 : x1), (∀ x12 < x2, x12 ≠ x8 → (x10 ∈ x5 x12 ↔ x11 ∈ x5 x12)) ∧ x10 ∈ x5 x4 ∧ x11 ∉ x5 x4) → x2 ≤ x3 + (1 : ℕ) := by
  intro α x2 x3 x4 X hx4 h hess
  have h' : ∀ j, ∃ p q, j < x3 → (p < x2 + j ∧ q < x2 + j ∧
      (X (x2 + j) = X p ∪ X q ∨ X (x2 + j) = X p ∨ X (x2 + j) = ∅ ∨ X (x2 + j) = X p ∩ X q)) := by
    intro j
    by_cases hj : j < x3
    · obtain ⟨p, hp, q, hq, hpq⟩ := h j hj
      exact ⟨p, q, fun _ => ⟨hp, hq, hpq⟩⟩
    · exact ⟨0, 0, fun hh => absurd hh hj⟩
  choose a b hab using h'
  have sem : ∀ k, k ≤ x3 → ∀ w, w < x2 + k → ∀ p q : α,
      (∀ i ∈ supF x2 a b k w, p ∈ X i → q ∈ X i) → p ∈ X w → q ∈ X w := by
    intro k
    induction k with
    | zero =>
      intro _ w hw p q hi hp
      have hw' : w < x2 := by omega
      exact hi w (by simp [supF, hw']) hp
    | succ k ih =>
      intro hk w hw p q hi hp
      by_cases hwk : w = x2 + k
      · subst hwk
        obtain ⟨ha, hb, hc⟩ := hab k (by omega)
        rw [supF_top] at hi
        have iha := ih (by omega) (a k) ha p q (fun i hi' => hi i (Finset.mem_union_left _ hi'))
        have ihb := ih (by omega) (b k) hb p q (fun i hi' => hi i (Finset.mem_union_right _ hi'))
        rcases hc with hc | hc | hc | hc
        · rw [hc] at hp ⊢
          rcases hp with hp | hp
          · exact Or.inl (iha hp)
          · exact Or.inr (ihb hp)
        · rw [hc] at hp ⊢
          exact iha hp
        · rw [hc] at hp
          exact absurd hp (Set.notMem_empty _)
        · rw [hc] at hp ⊢
          exact ⟨iha hp.1, ihb hp.2⟩
      · rw [supF_old _ _ _ _ _ hwk] at hi
        exact ih (by omega) w (by omega) p q hi hp
  have hsub : Finset.range x2 ⊆ supF x2 a b x3 x4 := by
    intro i hi
    by_contra hni
    obtain ⟨p, q, hpq, hp, hq⟩ := hess i (Finset.mem_range.1 hi)
    apply hq
    refine sem x3 le_rfl x4 hx4 p q (fun j hj hpj => ?_) hp
    have hj2 : j < x2 := Finset.mem_range.1 (supF_sub x2 a b x3 x4 hj)
    have hji : j ≠ i := fun e => hni (e ▸ hj)
    exact (hpq j hj2 hji).1 hpj
  have h1 := Finset.card_le_card hsub
  have h2 := supF_cnt x2 a b x3 {x4}
  rw [Finset.card_range] at h1
  have h3 : (supF x2 a b x3 x4).card ≤ x3 + 1 := by simpa using h2
  omega
