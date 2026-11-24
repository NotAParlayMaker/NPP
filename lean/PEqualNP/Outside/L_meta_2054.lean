import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2054_aux

private abbrev incident (p l : Fin 13) : Prop :=
  (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

private def avoid (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => ∀ p ∈ S, ¬ incident p l)

private def bad : Finset (Finset (Fin 13)) :=
  ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter (fun S => 3 < (avoid S).card)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem bad_empty : bad.card = 0 := by
  decide +kernel

private theorem four (S : Finset (Fin 13))
    (hS : S ∈ (Finset.univ : Finset (Fin 13)).powersetCard 4) :
    (avoid S).card ≤ 3 := by
  by_contra! h
  have hm : S ∈ bad := Finset.mem_filter.mpr ⟨hS, h⟩
  have hn : bad.Nonempty := ⟨S, hm⟩
  have hp := Finset.card_pos.mpr hn
  rw [bad_empty] at hp
  omega

end PEqualNP.Outside.L_meta_2054_aux

theorem PEqualNP.Outside.L_meta_2054 :
    let inc : Fin 13 → Fin 13 → Prop :=
      fun p l => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
    ∀ A B : Finset (Fin 13),
      (∀ p ∈ A, ∀ l ∈ B, ¬ inc p l) → A.card ≤ 3 ∨ B.card ≤ 3 := by
  intro inc A B h
  by_cases hA : A.card ≤ 3
  · exact Or.inl hA
  · apply Or.inr
    obtain ⟨S, hSA, hsize⟩ := Finset.exists_subset_card_eq (n := 4) (s := A) (by omega)
    have hB : B ⊆ L_meta_2054_aux.avoid S := by
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => h p (hSA hp) l hl⟩
    exact (Finset.card_le_card hB).trans
      (L_meta_2054_aux.four S (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hsize⟩))
