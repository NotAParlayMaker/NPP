import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_684 :
    ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
      (L : G →+ H) (A : AddSubgroup H) (g : H),
      Nat.card {t : G // L t - g ∈ A} = 0 ∨
      Nat.card {t : G // L t - g ∈ A} =
        Nat.card L.ker * Nat.card (A ⊓ L.range : AddSubgroup H) := by
  intro G H _ _ _ _ L A g
  classical
  by_cases hex : ∃ t : G, L t - g ∈ A
  · right
    obtain ⟨t₀, ht₀⟩ := hex
    let E : {t : G // L t - g ∈ A} ≃ A.comap L :=
      { toFun := fun t => ⟨t.val - t₀, by
          change L (t.val - t₀) ∈ A
          convert A.sub_mem t.property ht₀ using 1 <;> simp [map_sub]⟩
        invFun := fun t => ⟨t.val + t₀, by
          change L (t.val + t₀) - g ∈ A
          convert A.add_mem t.property ht₀ using 1 <;> simp [map_add, add_sub_assoc]⟩
        left_inv := by intro t; apply Subtype.ext; simp
        right_inv := by intro t; apply Subtype.ext; simp }
    let F : A.comap L →+ (A ⊓ L.range : AddSubgroup H) :=
      { toFun := fun t => ⟨L t.val, t.property, ⟨t.val, rfl⟩⟩
        map_zero' := by apply Subtype.ext; exact L.map_zero
        map_add' := by intro x y; apply Subtype.ext; exact L.map_add _ _ }
    have hsur : Function.Surjective F := by
      intro y
      obtain ⟨t, ht⟩ := y.property.2
      refine ⟨⟨t, ?_⟩, ?_⟩
      · change L t ∈ A
        rw [ht]
        exact y.property.1
      · apply Subtype.ext
        exact ht
    let K : F.ker ≃ L.ker :=
      { toFun := fun t => ⟨t.val.val, by
          have h := congrArg Subtype.val t.property
          exact h⟩
        invFun := fun t => ⟨⟨t.val, by
          change L t.val ∈ A
          rw [show L t.val = 0 from t.property]
          exact A.zero_mem⟩, by
            apply Subtype.ext
            exact t.property⟩
        left_inv := by intro t; apply Subtype.ext; apply Subtype.ext; rfl
        right_inv := by intro t; apply Subtype.ext; rfl }
    calc
      Nat.card {t : G // L t - g ∈ A} = Nat.card (A.comap L) := Nat.card_congr E
      _ = Nat.card F.ker * Nat.card (A ⊓ L.range : AddSubgroup H) :=
        (AddSubgroup.card_ker_mul_card_of_surjective hsur).symm
      _ = Nat.card L.ker * Nat.card (A ⊓ L.range : AddSubgroup H) := by
        rw [Nat.card_congr K]
  · left
    haveI : IsEmpty {t : G // L t - g ∈ A} := ⟨fun t => hex ⟨t.val, t.property⟩⟩
    simp
