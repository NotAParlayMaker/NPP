import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_684 : ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (L : G →+ H) (A : AddSubgroup H) (g : H),
    Nat.card {t : G // L t - g ∈ A} = 0 ∨
    Nat.card {t : G // L t - g ∈ A} = Nat.card L.ker * Nat.card (A ⊓ L.range : AddSubgroup H) := by
  intro G H _ _ _ _ L A g
  classical
  by_cases h : ∃ t : G, L t - g ∈ A
  · right
    obtain ⟨t₀, ht₀⟩ := h
    let e : {t : G // L t - g ∈ A} ≃ A.comap L :=
      { toFun := fun t => ⟨t.val - t₀, by
          change L (t.val - t₀) ∈ A
          rw [map_sub]
          have ht := A.sub_mem t.property ht₀
          convert ht using 1; abel⟩
        invFun := fun t => ⟨t.val + t₀, by
          rw [map_add]
          have ht := A.add_mem t.property ht₀
          convert ht using 1; abel⟩
        left_inv := fun t => Subtype.ext (sub_add_cancel t.val t₀)
        right_inv := fun t => Subtype.ext (add_sub_cancel_right t.val t₀) }
    have hk : Nat.card (L.domRestrict (A.comap L)).ker = Nat.card L.ker := by
      rw [AddMonoidHom.ker_domRestrict]
      exact Nat.card_congr
        (AddSubgroup.addSubgroupOfEquivOfLe (AddMonoidHom.ker_le_comap L A)).toEquiv
    calc
      Nat.card {t : G // L t - g ∈ A} = Nat.card (A.comap L) := Nat.card_congr e
      _ = Nat.card (L.domRestrict (A.comap L)).ker *
          Nat.card (L.domRestrict (A.comap L)).range :=
        (AddSubgroup.card_ker_mul_card_range (L.domRestrict (A.comap L))).symm
      _ = Nat.card L.ker * Nat.card (A ⊓ L.range : AddSubgroup H) := by
        rw [hk, AddMonoidHom.domRestrict_range, AddSubgroup.map_comap_eq, inf_comm]
  · left
    exact Nat.card_eq_zero.mpr (Or.inl ⟨fun t => h ⟨t.val, t.property⟩⟩)
