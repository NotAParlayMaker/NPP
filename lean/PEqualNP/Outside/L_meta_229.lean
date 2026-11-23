import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_229

open PEqualNP.MetaComplexity

abbrev orN (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x => decide (∃ i : Fin n, x i = true)

def allFalse (n : ℕ) : Fin n → Bool := fun _ => false

lemma orN_false_iff (n : ℕ) (y : Fin n → Bool) :
    orN n y = false ↔ y = allFalse n := by
  constructor
  · intro hy
    funext i
    have : ¬ ∃ j : Fin n, y j = true := by
      simpa [orN, decide_eq_true_iff] using hy
    have hyi : y i ≠ true := fun h => this ⟨i, h⟩
    cases hyi' : y i
    · rfl
    · exact absurd hyi' hyi
  · intro hy
    subst hy
    simp [orN, allFalse]

lemma orN_true_iff (n : ℕ) (x : Fin n → Bool) :
    orN n x = true ↔ ∃ i : Fin n, x i = true := by
  simp [orN]

lemma typedMatrix_false_bit_eq_zero (n : ℕ)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (hτ : IsTyping n (orN n) τ)
    (i : Fin n) :
    typedMatrix n (orN n) τ i false = 0 := by
  ext x y
  change (if orN n x = true ∧ orN n y = false ∧ τ x y = (i : ℕ) ∧ x i = false then (1 : ℚ) else 0) = 0
  split_ifs with h
  · rcases h with ⟨hx, hy, hτxy, hxi⟩
    obtain ⟨j, hj, hne⟩ := hτ x y hx hy
    have hij : j = i := Fin.ext (hj.symm.trans hτxy)
    subst hij
    have hy' : y = allFalse n := (orN_false_iff n y).mp hy
    have hxtrue : x j = true := by
      have hyj : y j = false := by rw [hy']; rfl
      cases hxj : x j
      · exact False.elim (hne (by rw [hxj, hyj]))
      · rfl
    exact False.elim (Bool.false_ne_true (hxi.symm.trans hxtrue))
  · rfl

lemma rank_le_one_of_single_col {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℚ) (c : α) (h : ∀ x y, y ≠ c → M x y = 0) :
    M.rank ≤ 1 := by
  have heq : M = Matrix.vecMulVec (fun x => M x c) (Pi.single c (1 : ℚ)) := by
    ext x y
    simp only [Matrix.vecMulVec_apply, Pi.single_apply, mul_ite, mul_one, mul_zero]
    by_cases hy : y = c
    · simp [hy]
    · simp [hy, h x y hy]
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

lemma typedMatrix_rank_le_one (n : ℕ)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (i : Fin n) (b : Bool) :
    (typedMatrix n (orN n) τ i b).rank ≤ 1 := by
  refine rank_le_one_of_single_col _ (allFalse n) ?_
  intro x y hy
  change (if orN n x = true ∧ orN n y = false ∧ τ x y = (i : ℕ) ∧ x i = b then (1 : ℚ) else 0) = 0
  split_ifs with h
  · exact False.elim (hy ((orN_false_iff n y).mp h.2.1))
  · rfl

lemma unit_true (n : ℕ) (j : Fin n) :
    orN n (fun i => decide (i = j)) = true := by
  refine (orN_true_iff n _).mpr ⟨j, ?_⟩
  simp

lemma typedMatrix_unit_entry (n : ℕ)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (hτ : IsTyping n (orN n) τ)
    (j : Fin n) :
    typedMatrix n (orN n) τ j true (fun i => decide (i = j)) (allFalse n) = 1 := by
  have hx : orN n (fun i => decide (i = j)) = true := unit_true n j
  have hy : orN n (allFalse n) = false := (orN_false_iff n _).mpr rfl
  obtain ⟨k, hk, hne⟩ := hτ (fun i => decide (i = j)) (allFalse n) hx hy
  have hkj : k = j := by
    have hbit : decide (k = j) = true := by
      cases hdec : decide (k = j)
      · exact False.elim (hne (by simp [allFalse, hdec]))
      · rfl
    exact of_decide_eq_true hbit
  have hτxy : τ (fun i => decide (i = j)) (allFalse n) = (j : ℕ) := by
    rw [hk, hkj]
  have hbitj : (fun i => decide (i = j)) j = true := by simp
  change (if orN n (fun i => decide (i = j)) = true ∧ orN n (allFalse n) = false ∧
      τ (fun i => decide (i = j)) (allFalse n) = (j : ℕ) ∧
      (fun i => decide (i = j)) j = true then (1 : ℚ) else 0) = 1
  simp [hx, hy, hτxy]

lemma typedMatrix_true_rank_pos (n : ℕ)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (hτ : IsTyping n (orN n) τ)
    (j : Fin n) :
    1 ≤ (typedMatrix n (orN n) τ j true).rank := by
  have hentry := typedMatrix_unit_entry n τ hτ j
  have hne : typedMatrix n (orN n) τ j true ≠ 0 := by
    intro hz
    have := congr_fun (congr_fun hz (fun i => decide (i = j))) (allFalse n)
    simp [hentry] at this
  have hr0 : (typedMatrix n (orN n) τ j true).rank = 0 →
      typedMatrix n (orN n) τ j true = 0 := by
    intro hr
    rw [Matrix.rank_eq_finrank_span_cols] at hr
    have hbot : Submodule.span ℚ (Set.range (typedMatrix n (orN n) τ j true).col) = ⊥ :=
      Submodule.finrank_eq_zero.mp hr
    ext x y
    have hcol : (typedMatrix n (orN n) τ j true).col y = 0 := by
      have : (typedMatrix n (orN n) τ j true).col y ∈
          Submodule.span ℚ (Set.range (typedMatrix n (orN n) τ j true).col) :=
        Submodule.subset_span ⟨y, rfl⟩
      simpa [hbot] using this
    exact congr_fun hcol x
  have : (typedMatrix n (orN n) τ j true).rank ≠ 0 := fun h => hne (hr0 h)
  omega

lemma sum_ranks_eq_sum_true (n : ℕ)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (hτ : IsTyping n (orN n) τ) :
    (∑ i : Fin n, ∑ b : Bool, (typedMatrix n (orN n) τ i b).rank) =
      ∑ i : Fin n, (typedMatrix n (orN n) τ i true).rank := by
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fintype.sum_bool, typedMatrix_false_bit_eq_zero n τ hτ i, Matrix.rank_zero,
    add_zero]

lemma sum_ranks_ge (n : ℕ)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (hτ : IsTyping n (orN n) τ) :
    n ≤ ∑ i : Fin n, ∑ b : Bool, (typedMatrix n (orN n) τ i b).rank := by
  rw [sum_ranks_eq_sum_true n τ hτ]
  calc
    n = ∑ _i : Fin n, 1 := by simp
    _ ≤ ∑ i : Fin n, (typedMatrix n (orN n) τ i true).rank :=
      Finset.sum_le_sum fun i _ => typedMatrix_true_rank_pos n τ hτ i

lemma sum_ranks_le (n : ℕ)
    (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ) (hτ : IsTyping n (orN n) τ) :
    (∑ i : Fin n, ∑ b : Bool, (typedMatrix n (orN n) τ i b).rank) ≤ n := by
  rw [sum_ranks_eq_sum_true n τ hτ]
  calc
    ∑ i : Fin n, (typedMatrix n (orN n) τ i true).rank
      ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => typedMatrix_rank_le_one n τ i true
    _ = n := by simp

noncomputable def stdTyping (n : ℕ) : (Fin n → Bool) → (Fin n → Bool) → ℕ :=
  fun x _ => if h : ∃ i : Fin n, x i = true then (Classical.choose h).val else 0

lemma stdTyping_isTyping (n : ℕ) : IsTyping n (orN n) (stdTyping n) := by
  intro x y hx hy
  have hex : ∃ i : Fin n, x i = true := (orN_true_iff n x).mp hx
  have hy' : y = allFalse n := (orN_false_iff n y).mp hy
  refine ⟨Classical.choose hex, ?_, ?_⟩
  · simp [stdTyping, hex]
  · have hxj : x (Classical.choose hex) = true := Classical.choose_spec hex
    simp [hy', allFalse, hxj]

lemma hasTypedRank_n (n : ℕ) (_hn : 1 ≤ n) : HasTypedRank n (orN n) n := by
  refine ⟨stdTyping n, stdTyping_isTyping n, ?_⟩
  exact sum_ranks_le n (stdTyping n) (stdTyping_isTyping n)

lemma not_hasTypedRank_pred (n : ℕ) (_hn : 1 ≤ n) :
    ¬ HasTypedRank n (orN n) (n - 1) := by
  rintro ⟨τ, hτ, hr⟩
  have hge := sum_ranks_ge n τ hτ
  have : n ≤ n - 1 := le_trans hge hr
  omega

end PEqualNP.Outside.L_meta_229

theorem PEqualNP.Outside.L_meta_229 :
    ∀ n : ℕ, 1 ≤ n →
      PEqualNP.MetaComplexity.HasTypedRank n
        (fun x => decide (∃ i : Fin n, x i = true)) n ∧
      ¬ PEqualNP.MetaComplexity.HasTypedRank n
        (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_229.hasTypedRank_n n hn,
    PEqualNP.Outside.L_meta_229.not_hasTypedRank_pred n hn⟩
