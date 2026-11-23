import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_307 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → ∀ c : ℕ, (∀ S : Finset V, (∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S) → c ≤ S.card) ↔ (∀ S : Finset (Fin N), (∀ a b, G'.Adj a b → a ∈ S ∨ b ∈ S) → c ≤ S.card) := by
  classical
  intro V G0 N num G' hlt hinj hadj c
  constructor
  · intro h S' hS'
    let P : Fin N → Prop := fun a => ∃ u v, G0.Adj u v ∧ num u = a.val
    let T := S'.filter P
    have hP : ∀ a : {a : Fin N // a ∈ T}, P a.1 := fun a => (Finset.mem_filter.mp a.2).2
    let S : Finset V := T.attach.image fun a => Classical.choose (hP a)
    have hmem : ∀ u v (huv : G0.Adj u v), (⟨num u, hlt u v huv⟩ : Fin N) ∈ S' → u ∈ S := by
      intro u v huv hin
      have hT : (⟨num u, hlt u v huv⟩ : Fin N) ∈ T :=
        Finset.mem_filter.mpr ⟨hin, u, v, huv, rfl⟩
      refine Finset.mem_image.mpr ⟨⟨_, hT⟩, Finset.mem_attach _ _, ?_⟩
      obtain ⟨v', hadj', hnum'⟩ := Classical.choose_spec (hP ⟨_, hT⟩)
      exact hinj _ _ _ _ hadj' huv hnum'
    have hcov : ∀ u v, G0.Adj u v → u ∈ S ∨ v ∈ S := by
      intro u v huv
      have hG : G'.Adj ⟨num u, hlt u v huv⟩ ⟨num v, hlt v u huv.symm⟩ :=
        (hadj _ _).mpr ⟨u, v, huv, rfl, rfl⟩
      rcases hS' _ _ hG with h1 | h1
      · exact Or.inl (hmem u v huv h1)
      · exact Or.inr (hmem v u huv.symm h1)
    calc c ≤ S.card := h S hcov
      _ ≤ T.attach.card := Finset.card_image_le
      _ = T.card := Finset.card_attach
      _ ≤ S'.card := Finset.card_filter_le _ _
  · intro h S hS
    let S' : Finset (Fin N) := Finset.univ.filter fun a : Fin N => a.val ∈ S.image num
    have hcov : ∀ a b, G'.Adj a b → a ∈ S' ∨ b ∈ S' := by
      intro a b hab
      obtain ⟨u, v, huv, hu, hv⟩ := (hadj a b).mp hab
      rcases hS u v huv with h1 | h1
      · exact Or.inl (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨u, h1, hu⟩⟩)
      · exact Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨v, h1, hv⟩⟩)
    calc c ≤ S'.card := h S' hcov
      _ ≤ (S.image num).card :=
        Finset.card_le_card_of_injOn (fun a : Fin N => a.val)
          (fun a ha => (Finset.mem_filter.mp ha).2)
          (fun a _ b _ hab => Fin.ext hab)
      _ ≤ S.card := Finset.card_image_le
