import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_684

private lemma main_proof (G H : Type) [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (L : G →+ H) (A : AddSubgroup H) (g : H) :
    Nat.card {t : G // L t - g ∈ A} = 0 ∨
    Nat.card {t : G // L t - g ∈ A} = Nat.card L.ker * Nat.card (A ⊓ L.range : AddSubgroup H) := by
  classical
  by_cases hne : Nonempty {t : G // L t - g ∈ A}
  · right
    rcases hne with ⟨⟨t0, ht0⟩⟩
    let sec : (A ⊓ L.range : AddSubgroup H) → G := fun y => Classical.choose y.2.2
    have hsec : ∀ y : (A ⊓ L.range : AddSubgroup H), L (sec y) = y.1 :=
      fun y => Classical.choose_spec y.2.2
    let toY : {t : G // L t - g ∈ A} → (A ⊓ L.range : AddSubgroup H) := fun t =>
      ⟨L (t.1 - t0), ⟨by
        have hsub : L (t.1 - t0) = (L t.1 - g) - (L t0 - g) := by
          rw [map_sub]
          abel
        rw [hsub]
        exact A.sub_mem t.2 ht0, ⟨t.1 - t0, rfl⟩⟩⟩
    let toK : {t : G // L t - g ∈ A} → L.ker := fun t =>
      ⟨(t.1 - t0) - sec (toY t), by
        change L ((t.1 - t0) - sec (toY t)) = 0
        rw [map_sub, hsec (toY t), sub_self]⟩
    let invF : L.ker × (A ⊓ L.range : AddSubgroup H) → {t : G // L t - g ∈ A} := fun p =>
      ⟨p.1.1 + sec p.2 + t0, by
        have hk : L p.1.1 = 0 := p.1.2
        have heq : L (p.1.1 + sec p.2 + t0) - g = p.2.1 + (L t0 - g) := by
          rw [map_add, map_add, hk, zero_add, hsec p.2]
          abel
        rw [heq]
        exact A.add_mem p.2.2.1 ht0⟩
    let e : {t : G // L t - g ∈ A} ≃ L.ker × (A ⊓ L.range : AddSubgroup H) :=
      { toFun := fun t => (toK t, toY t)
        invFun := invF
        left_inv := fun t => by
          apply Subtype.ext
          change ((t.1 - t0) - sec (toY t)) + sec (toY t) + t0 = t.1
          abel
        right_inv := fun p => by
          rcases p with ⟨k, y⟩
          have hy : toY (invF (k, y)) = y := by
            apply Subtype.ext
            change L (k.1 + sec y + t0 - t0) = y.1
            have hk : L k.1 = 0 := k.2
            rw [add_sub_cancel_right, map_add, hk, zero_add, hsec y]
          apply Prod.ext
          · apply Subtype.ext
            change (k.1 + sec y + t0 - t0) - sec (toY (invF (k, y))) = k.1
            rw [hy]
            abel
          · exact hy }
    rw [Nat.card_congr e, Nat.card_prod]
  · left
    have hE : IsEmpty {t : G // L t - g ∈ A} := not_nonempty_iff.mp hne
    rw [Nat.card_congr (@Equiv.equivOfIsEmpty _ Empty hE _), Nat.card_eq_fintype_card]
    simp

end PEqualNP.Outside.L_meta_684

theorem PEqualNP.Outside.L_meta_684 :
    ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (L : G →+ H) (A : AddSubgroup H) (g : H),
    Nat.card {t : G // L t - g ∈ A} = 0 ∨
    Nat.card {t : G // L t - g ∈ A} = Nat.card L.ker * Nat.card (A ⊓ L.range : AddSubgroup H) := by
  intro G H _ _ _ _ L A g
  exact PEqualNP.Outside.L_meta_684.main_proof G H L A g
