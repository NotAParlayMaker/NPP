import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private theorem union_inter_bound {n t : ℕ} (G : SimpleGraph (Fin n))
    (hMin : ∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) →
      t ≤ S.card)
    (A B C : Finset (Fin n)) (hBA : B ⊆ A) (hC : C.card = t)
    (hCover : ∀ u v : Fin n, G.Adj u v → u ∈ C ∨ v ∈ C)
    (hCross : ∀ u v : Fin n, G.Adj u v → u ∉ A → v ∈ B)
    (hSize : A.card + B.card ≤ 2 * t) :
    (A ∪ C).card + (B ∩ C).card ≤ 2 * t := by
  have hNewCover : ∀ u v : Fin n, G.Adj u v →
      u ∈ B ∪ (A ∩ C) ∨ v ∈ B ∪ (A ∩ C) := by
    intro u v huv
    by_cases huB : u ∈ B
    · exact Or.inl (Finset.mem_union.mpr (Or.inl huB))
    by_cases hvB : v ∈ B
    · exact Or.inr (Finset.mem_union.mpr (Or.inl hvB))
    have huA : u ∈ A := by
      by_contra hn
      exact hvB (hCross u v huv hn)
    have hvA : v ∈ A := by
      by_contra hn
      exact huB (hCross v u huv.symm hn)
    rcases hCover u v huv with hu | hv
    · exact Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨huA, hu⟩)))
    · exact Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hvA, hv⟩)))
  have hLow := hMin (B ∪ (A ∩ C)) hNewCover
  have hInter : B ∩ (A ∩ C) = B ∩ C := by
    ext v
    simp only [Finset.mem_inter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hBA h.1, h.2⟩⟩
  have h₁ := Finset.card_union_add_card_inter A C
  have h₂ := Finset.card_union_add_card_inter B (A ∩ C)
  rw [hInter] at h₂
  omega

theorem L_meta_215 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)), (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card) → (∀ w : Fin n, ∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card = t ∧ w ∈ S) → n ≤ 2 * t := by
  intro n t G hMin hEvery
  by_cases hzero : n = 0
  · simp [hzero]
  obtain ⟨C₀, hC₀Cover, hC₀Size, _⟩ :=
    hEvery ⟨0, Nat.pos_of_ne_zero hzero⟩
  have grow : ∀ W : Finset (Fin n), ∃ A B : Finset (Fin n),
      W ⊆ A ∧ B ⊆ A ∧ A.card + B.card ≤ 2 * t ∧
        ∀ u v : Fin n, G.Adj u v → u ∉ A → v ∈ B := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      refine ⟨C₀, C₀, Finset.empty_subset _, Finset.Subset.refl _, ?_, ?_⟩
      · omega
      · intro u v huv hu
        exact (hC₀Cover u v huv).resolve_left hu
    | @insert w W _ ih =>
      obtain ⟨A, B, hWA, hBA, hSize, hCross⟩ := ih
      obtain ⟨C, hCover, hC, hwC⟩ := hEvery w
      refine ⟨A ∪ C, B ∩ C, ?_, ?_,
        union_inter_bound G hMin A B C hBA hC hCover hCross hSize, ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Finset.mem_union.mpr (Or.inr hwC)
        · exact Finset.mem_union.mpr (Or.inl (hWA hv))
      · intro v hv
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mp hv).2)
      · intro u v huv hu
        have huA : u ∉ A := fun h => hu (Finset.mem_union.mpr (Or.inl h))
        have huC : u ∉ C := fun h => hu (Finset.mem_union.mpr (Or.inr h))
        exact Finset.mem_inter.mpr
          ⟨hCross u v huv huA, (hCover u v huv).resolve_left huC⟩
  obtain ⟨A, B, hA, _, hSize, _⟩ := grow Finset.univ
  have hCard : n = A.card := by
    have hEq : A = Finset.univ := Finset.Subset.antisymm (Finset.subset_univ A) hA
    simp [hEq]
  omega

end PEqualNP.Outside
