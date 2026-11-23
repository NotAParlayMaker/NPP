import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_228

-- Two inputs can differ at a position only if the update acts there.
lemma eq_of_ne_update {n : ℕ} {x : Fin n → Bool} {i j : Fin n}
    (h : x j ≠ (Function.update x i (!x i)) j) : j = i := by
  by_contra hji
  exact h (Function.update_of_ne hji (!x i) x).symm

-- A matrix over the rationals with a nonzero entry has rank at least one.
lemma one_le_rank_of_entry {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m n ℚ) {a : m} {b : n} (h : A a b ≠ 0) : 1 ≤ A.rank := by
  have hpos : 0 < A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨A.col b, Submodule.subset_span (Set.mem_range_self b)⟩, ?_⟩
    rintro hzero
    apply h
    have hv : A.col b = (0 : m → ℚ) := congrArg Subtype.val hzero
    have hz : A.col b a = 0 := by rw [hv]; rfl
    simpa [Matrix.col_apply] using hz
  omega

-- A nonzero matrix has a nonzero entry.
lemma exists_entry_of_ne_zero {m n : Type} (A : Matrix m n ℚ) (h : A ≠ 0) :
    ∃ a : m, ∃ b : n, A a b ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  exact h (funext fun a => funext fun b => hcon a b)

-- An input the function depends on gives a nonzero literal matrix: the typing must type
-- the pair (x, update x i (!x i)) at position i, since the two inputs differ nowhere else.
lemma exists_ne_zero_literal {n : ℕ} {f : (Fin n → Bool) → Bool}
    {τ : (Fin n → Bool) → (Fin n → Bool) → ℕ} (hτ : IsTyping n f τ) {i : Fin n}
    (hi : ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))) :
    ∃ b : Bool, typedMatrix n f τ i b ≠ 0 := by
  obtain ⟨x, hx⟩ := hi
  have hdiff : ∀ j : Fin n, x j ≠ (Function.update x i (!x i)) j → j = i :=
    fun j hj => eq_of_ne_update hj
  rcases hfx : f x with _ | _
  · -- f x = false, so the update is true: the pair is typed with the update row first
    have hfy : f (Function.update x i (!x i)) = true := by
      cases h : f (Function.update x i (!x i)) with
      | false => exact absurd (by rw [hfx, h]) hx
      | true => rfl
    obtain ⟨j, hτj, hne⟩ := hτ (Function.update x i (!x i)) x hfy hfx
    have hji : j = i := hdiff j (Ne.symm hne)
    rw [hji] at hτj
    refine ⟨Function.update x i (!x i) i, ?_⟩
    intro hzero
    have h1 : typedMatrix n f τ i (Function.update x i (!x i) i)
        (Function.update x i (!x i)) x = 1 := by
      simp [typedMatrix, hfy, hfx, hτj]
    rw [hzero] at h1
    exact zero_ne_one h1
  · -- f x = true, so the update is false
    have hfy : f (Function.update x i (!x i)) = false := by
      cases h : f (Function.update x i (!x i)) with
      | false => rfl
      | true => exact absurd (by rw [hfx, h]) hx
    obtain ⟨j, hτj, hne⟩ := hτ x (Function.update x i (!x i)) hfx hfy
    have hji : j = i := hdiff j hne
    rw [hji] at hτj
    refine ⟨x i, ?_⟩
    intro hzero
    have h1 : typedMatrix n f τ i (x i) x (Function.update x i (!x i)) = 1 := by
      simp [typedMatrix, hfx, hfy, hτj]
    rw [hzero] at h1
    exact zero_ne_one h1

end PEqualNP.Outside.L_meta_228

open PEqualNP.Outside.L_meta_228

theorem PEqualNP.Outside.L_meta_228 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s →
    (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  intro n f s h
  obtain ⟨τ, hτ, hsum⟩ := h
  have key : ∀ i ∈ Finset.univ.filter
      (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))),
      1 ≤ ∑ b : Bool, (typedMatrix n f τ i b).rank := by
    intro i hi
    obtain ⟨b, hb⟩ :=
      exists_ne_zero_literal (f := f) (τ := τ) hτ (Finset.mem_filter.1 hi).2
    obtain ⟨r, c, hrc⟩ := exists_entry_of_ne_zero _ hb
    have h1 : 1 ≤ (typedMatrix n f τ i b).rank := one_le_rank_of_entry _ hrc
    calc (1 : ℕ) = 1 := rfl
      _ ≤ (typedMatrix n f τ i b).rank := h1
      _ ≤ ∑ c : Bool, (typedMatrix n f τ i c).rank :=
          Finset.single_le_sum (f := fun c : Bool => (typedMatrix n f τ i c).rank)
            (fun c _ => Nat.zero_le _) (Finset.mem_univ b)
  calc (Finset.univ.filter
      (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card
      = ∑ i ∈ Finset.univ.filter
          (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))),
          (1 : ℕ) := Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ Finset.univ.filter
          (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))),
          ∑ b : Bool, (typedMatrix n f τ i b).rank := Finset.sum_le_sum key
    _ ≤ ∑ i : Fin n, ∑ b : Bool, (typedMatrix n f τ i b).rank :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => Nat.zero_le _)
    _ ≤ s := hsum
