import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_208

open PEqualNP.MetaComplexity

lemma true_input (x : Fin 2 → Bool) (hx : (x 0 && x 1) = true) :
    x = fun _ => true := by
  funext i
  have h := Bool.and_eq_true_iff.mp hx
  fin_cases i <;> simp_all

lemma rank_le_one (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ)
    (i : Fin 2) (b : Bool) :
    (typedMatrix 2 (fun x => x 0 && x 1) τ i b).rank ≤ 1 := by
  classical
  have h := Matrix.rank_le_card_of_support_subset
    (typedMatrix 2 (fun x => x 0 && x 1) τ i b) {fun _ => true} (by
      rw [Function.support_subset_iff']
      intro x hx
      have hfx : (x 0 && x 1) ≠ true := by
        intro h
        apply hx
        simp [true_input x h]
      funext y
      simp [Matrix.row, typedMatrix, hfx])
  simpa using h

lemma rank_false (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ) (i : Fin 2) :
    (typedMatrix 2 (fun x => x 0 && x 1) τ i false).rank = 0 := by
  have hzero : typedMatrix 2 (fun x => x 0 && x 1) τ i false = 0 := by
    ext x y
    by_cases hx : (x 0 && x 1) = true
    · rw [true_input x hx]
      simp [typedMatrix]
    · simp [typedMatrix, hx]
  rw [hzero, Matrix.rank_zero]

lemma rank_ge_one {α β : Type} [Fintype β] (M : Matrix α β ℚ)
    (x : α) (y : β) (h : M x y = 1) : 1 ≤ M.rank := by
  have hs : M.submatrix (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) =
      (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    ext i j
    fin_cases i
    fin_cases j
    simpa using h
  have hr := Matrix.rank_submatrix_le M (fun _ : Fin 1 => x) (fun _ : Fin 1 => y)
  rw [hs] at hr
  simpa using hr

end PEqualNP.Outside.L_meta_208

theorem PEqualNP.Outside.L_meta_208 : PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 2 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 1 := by
  classical
  constructor
  · let τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ :=
      fun _ y => if y 0 = false then 0 else 1
    refine ⟨τ, ?_, ?_⟩
    · intro x y hx hy
      have hx' := PEqualNP.Outside.L_meta_208.true_input x hx
      subst x
      by_cases hy0 : y 0 = false
      · refine ⟨0, ?_, ?_⟩ <;> simp [τ, hy0]
      · have hy0' : y 0 = true := by cases h : y 0 <;> simp_all
        have hy1 : y 1 = false := by simpa [hy0'] using hy
        refine ⟨1, ?_, ?_⟩ <;> simp [τ, hy0, hy1]
    · simp only [Fin.sum_univ_two, Fintype.sum_bool,
        PEqualNP.Outside.L_meta_208.rank_false, Nat.add_zero]
      exact Nat.add_le_add
        (PEqualNP.Outside.L_meta_208.rank_le_one τ 0 true)
        (PEqualNP.Outside.L_meta_208.rank_le_one τ 1 true)
  · rintro ⟨τ, hτ, hr⟩
    have ht0 : τ ![true, true] ![false, true] = 0 := by
      obtain ⟨i, hi, hd⟩ := hτ ![true, true] ![false, true] rfl rfl
      fin_cases i
      · simpa using hi
      · simp at hd
    have ht1 : τ ![true, true] ![true, false] = 1 := by
      obtain ⟨i, hi, hd⟩ := hτ ![true, true] ![true, false] rfl rfl
      fin_cases i
      · simp at hd
      · simpa using hi
    have h0 := PEqualNP.Outside.L_meta_208.rank_ge_one
      (PEqualNP.MetaComplexity.typedMatrix 2 (fun x => x 0 && x 1) τ 0 true)
      ![true, true] ![false, true] (by
        simp [PEqualNP.MetaComplexity.typedMatrix, ht0])
    have h1 := PEqualNP.Outside.L_meta_208.rank_ge_one
      (PEqualNP.MetaComplexity.typedMatrix 2 (fun x => x 0 && x 1) τ 1 true)
      ![true, true] ![true, false] (by
        simp [PEqualNP.MetaComplexity.typedMatrix, ht1])
    simp only [Fin.sum_univ_two, Fintype.sum_bool] at hr
    omega
