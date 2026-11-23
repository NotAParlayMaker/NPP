import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta228

open PEqualNP.MetaComplexity

private lemma rank_pos_of_entry_ne_zero {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (M : Matrix α β ℚ) (x : α) (y : β)
    (h : M x y ≠ 0) : 1 ≤ M.rank := by
  have hne : M.mulVecLin (Pi.single y 1) ≠ 0 := by
    intro h0
    have hx := congrFun h0 x
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one,
      one_smul, Pi.zero_apply] at hx
    exact h hx
  rw [Matrix.rank, Nat.succ_le_iff, Module.finrank_pos_iff]
  exact ⟨⟨⟨M.mulVecLin (Pi.single y 1), LinearMap.mem_range_self _ _⟩, 0,
    by simpa using fun hc => h (congrFun hc x)⟩⟩

private lemma main_proof (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : HasTypedRank n f s) :
    (Finset.univ.filter (fun i : Fin n =>
      ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  classical
  obtain ⟨τ, hτ, hrank⟩ := h
  let D : Finset (Fin n) := Finset.univ.filter (fun i : Fin n =>
    ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))
  have hterm : ∀ i ∈ D, 1 ≤ ∑ b : Bool, (typedMatrix n f τ i b).rank := by
    intro i hi
    obtain ⟨x0, hx0⟩ := (Finset.mem_filter.mp hi).2
    let x1 := Function.update x0 i (!x0 i)
    obtain ⟨x, y, hfx, hfy, hagree⟩ :
        ∃ x y : Fin n → Bool, f x = true ∧ f y = false ∧ ∀ j, j ≠ i → x j = y j := by
      cases hx0t : f x0
      · have hx1t : f x1 = true := by
          cases h1 : f x1
          · exact absurd (hx0t.trans h1.symm) hx0
          · rfl
        exact ⟨x1, x0, hx1t, hx0t, fun j hj => Function.update_of_ne hj _ _⟩
      · have hx1f : f x1 = false := by
          cases h1 : f x1
          · rfl
          · exact absurd (hx0t.trans h1.symm) hx0
        exact ⟨x0, x1, hx0t, hx1f, fun j hj => (Function.update_of_ne hj _ _).symm⟩
    obtain ⟨k, hτk, hxk⟩ := hτ x y hfx hfy
    have hki : k = i := by
      by_contra hne
      exact hxk (hagree k hne)
    subst hki
    have h1 : typedMatrix n f τ k (x k) x y ≠ 0 := by
      simp [typedMatrix, hfx, hfy, hτk]
    have hr := rank_pos_of_entry_ne_zero (typedMatrix n f τ k (x k)) x y h1
    have hle : (typedMatrix n f τ k (x k)).rank ≤ ∑ b : Bool, (typedMatrix n f τ k b).rank :=
      Finset.single_le_sum (f := fun b : Bool => (typedMatrix n f τ k b).rank)
        (fun b _ => Nat.zero_le _) (Finset.mem_univ (x k))
    omega
  calc D.card
      = ∑ _i ∈ D, 1 := by simp
    _ ≤ ∑ i ∈ D, ∑ b : Bool, (typedMatrix n f τ i b).rank := Finset.sum_le_sum hterm
    _ ≤ ∑ i : Fin n, ∑ b : Bool, (typedMatrix n f τ i b).rank :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D) (fun _ _ _ => Nat.zero_le _)
    _ ≤ s := hrank

end PEqualNP.Outside.LMeta228

theorem PEqualNP.Outside.L_meta_228 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s →
    (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  exact PEqualNP.Outside.LMeta228.main_proof
