import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3767 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)) (x8 x9 : Finset ℕ), x7.card ≤ x1 → x9 ⊆ x8 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → ↑x12 ∈ x9 ∨ x2 + ↑x13 ∈ x9) → (∀ (x13 : Fin x2), (↑x13 ∈ x8 ↔ ∃ x14 ∈ x7, x3 x13 x14) ∧ (x2 + ↑x13 ∈ x8 ↔ x13 ∉ x7)) → ∀ (x14 : Fin x2), (↑x14 ∈ x9 ↔ ∃ x15 ∈ x7, x3 x14 x15) ∧ (x2 + ↑x14 ∈ x9 ↔ x14 ∉ x7) := by
  intro q N I _ hcard huniq S x8 x9 hS hsub hinc h8 l
  constructor
  · constructor
    · intro h
      exact (h8 l).1.1 (hsub h)
    · rintro ⟨m, hm, hI⟩
      rcases hinc l m hI with h | h
      · exact h
      · exact absurd hm ((h8 m).2.1 (hsub h))
  · constructor
    · intro h
      exact (h8 l).2.1 (hsub h)
    · intro hl
      by_contra hcon
      have hcov : ∀ p : Fin N, I p l → ∃ m ∈ S, I p m := by
        intro p hp
        rcases hinc p l hp with h | h
        · exact (h8 p).1.1 (hsub h)
        · exact absurd h hcon
      choose f hfS hfI using hcov
      have hle : Fintype.card {p : Fin N // I p l} ≤ Fintype.card {m // m ∈ S} := by
        apply Fintype.card_le_of_injective (fun p => ⟨f p.1 p.2, hfS p.1 p.2⟩)
        intro a b hab
        simp only [Subtype.mk.injEq] at hab
        by_contra hne
        have hne2 : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
        obtain ⟨c, hc, hu⟩ := huniq a.1 b.1 hne2
        have h1 := hu l ⟨a.2, b.2⟩
        have hb : I b.1 (f a.1 a.2) := by
          rw [hab]
          exact hfI b.1 b.2
        have h2 := hu (f a.1 a.2) ⟨hfI a.1 a.2, hb⟩
        have h3 : f a.1 a.2 = l := h2.trans h1.symm
        exact hl (h3 ▸ hfS a.1 a.2)
      rw [hcard, Fintype.card_coe] at hle
      omega
