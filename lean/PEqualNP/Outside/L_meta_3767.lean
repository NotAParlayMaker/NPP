import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3767 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)) (x8 x9 : Finset ℕ), x7.card ≤ x1 → x9 ⊆ x8 → (∀ (x12 x13 : Fin x2), x3 x12 x13 → ↑x12 ∈ x9 ∨ x2 + ↑x13 ∈ x9) → (∀ (x13 : Fin x2), (↑x13 ∈ x8 ↔ ∃ x14 ∈ x7, x3 x13 x14) ∧ (x2 + ↑x13 ∈ x8 ↔ x13 ∉ x7)) → ∀ (x14 : Fin x2), (↑x14 ∈ x9 ↔ ∃ x15 ∈ x7, x3 x14 x15) ∧ (x2 + ↑x14 ∈ x9 ↔ x14 ∉ x7) := by
  intro q N I _ hline huniq X W V hcard hsub hcover hW p
  refine ⟨⟨fun h => ((hW p).1).mp (hsub h), ?_⟩, ⟨fun h => ((hW p).2).mp (hsub h), ?_⟩⟩
  · rintro ⟨l, hl, hpl⟩
    rcases hcover p l hpl with h | h
    · exact h
    · exact absurd hl (((hW l).2).mp (hsub h))
  · intro hp
    by_contra hne
    have key : ∀ r : { r : Fin N // I r p }, ∃ m : { m : Fin N // m ∈ X }, I r.1 m.1 := by
      intro r
      rcases hcover r.1 p r.2 with h | h
      · obtain ⟨m, hm, hrm⟩ := ((hW r.1).1).mp (hsub h)
        exact ⟨⟨m, hm⟩, hrm⟩
      · exact absurd h hne
    choose f hf using key
    have finj : Function.Injective f := by
      intro r r' hrr
      by_contra hne'
      have hne2 : r.1 ≠ r'.1 := fun h => hne' (Subtype.ext h)
      obtain ⟨m, _, hm⟩ := huniq r.1 r'.1 hne2
      have h1 : (f r).1 = m := hm _ ⟨hf r, by rw [hrr]; exact hf r'⟩
      have h2 : p = m := hm _ ⟨r.2, r'.2⟩
      exact hp (by rw [h2, ← h1]; exact (f r).2)
    have hle := Fintype.card_le_of_injective f finj
    rw [hline p, Fintype.card_coe] at hle
    omega
