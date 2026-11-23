import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_228

theorem one_le_rank {m k : Type} [Fintype m] [Fintype k] [DecidableEq k]
    (A : Matrix m k ℚ) (x : m) (y : k) (h : A x y ≠ 0) : 1 ≤ A.rank := by
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hb : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hm : A.mulVecLin (Pi.single y 1) ∈ LinearMap.range A.mulVecLin :=
    LinearMap.mem_range_self _ _
  rw [hb, Submodule.mem_bot] at hm
  have hx := congrFun hm x
  simp at hx
  exact h hx

theorem flip_pair {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (x : Fin n → Bool)
    (hx : f x ≠ f (Function.update x i (!x i))) :
    ∃ a c : Fin n → Bool, f a = true ∧ f c = false ∧ c = Function.update a i (!a i) := by
  cases h1 : f x <;> cases h2 : f (Function.update x i (!x i))
  · rw [h1, h2] at hx; exact absurd rfl hx
  · refine ⟨Function.update x i (!x i), x, h2, h1, ?_⟩
    simp
  · exact ⟨x, _, h1, h2, rfl⟩
  · rw [h1, h2] at hx; exact absurd rfl hx

end PEqualNP.Outside.L_meta_228

theorem PEqualNP.Outside.L_meta_228 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasTypedRank n f s →
    (Finset.univ.filter (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i)))).card ≤ s := by
  rintro n f s ⟨τ, hτ, hr⟩
  have key : ∀ i ∈ Finset.univ.filter
      (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))),
      1 ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨x, hx⟩ := hi
    obtain ⟨a, c, ha, hc, rfl⟩ := PEqualNP.Outside.L_meta_228.flip_pair f i x hx
    obtain ⟨j, hj, hne⟩ := hτ a _ ha hc
    have hji : j = i := by
      by_contra hji
      exact hne (by rw [Function.update_of_ne hji])
    subst hji
    calc 1 ≤ (PEqualNP.MetaComplexity.typedMatrix n f τ j (a j)).rank :=
          PEqualNP.Outside.L_meta_228.one_le_rank _ a (Function.update a j (!a j))
            (by simp [PEqualNP.MetaComplexity.typedMatrix, ha, hc, hj])
      _ ≤ ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank :=
          Finset.single_le_sum
            (f := fun b => (PEqualNP.MetaComplexity.typedMatrix n f τ j b).rank)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ (a j))
  calc _ = ∑ i ∈ Finset.univ.filter
        (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))), 1 := by
        simp
    _ ≤ ∑ i ∈ Finset.univ.filter
        (fun i : Fin n => ∃ x : Fin n → Bool, f x ≠ f (Function.update x i (!x i))),
        ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank :=
        Finset.sum_le_sum key
    _ ≤ ∑ i : Fin n, ∑ b : Bool, (PEqualNP.MetaComplexity.typedMatrix n f τ i b).rank :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ s := hr
