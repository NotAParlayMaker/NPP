import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3771

def good (z : Fin 13) : Bool := !(z.val == 0 || z.val == 1 || z.val == 3 || z.val == 9)

set_option maxRecDepth 100000 in
theorem key : ∀ a b c d : Fin 13, a < b → b < c → c < d →
    ((List.finRange 13).filter fun y =>
      good (a + y) && good (b + y) && good (c + y) && good (d + y)).length ≤ 3 := by
  decide +kernel

theorem good_iff (z : Fin 13) :
    good z = true ↔ z ∉ ({0, 1, 3, 9} : Finset (Fin 13)) := by
  revert z
  decide

theorem four (A : Finset (Fin 13)) (h : A.card = 4) :
    ∃ a b c d : Fin 13, a < b ∧ b < c ∧ c < d ∧ a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A := by
  have hl : A.sort.length = 4 := by simp [h]
  have hs := (Finset.sortedLT_sort A).pairwise
  have hm : ∀ x, x ∈ A.sort ↔ x ∈ A := fun x => Finset.mem_sort _
  generalize A.sort = l at hl hs hm
  match l, hl, hs, hm with
  | [a, b, c, d], _, hs, hm =>
    simp at hs
    exact ⟨a, b, c, d, by grind, by grind, by grind, (hm a).1 (by simp),
      (hm b).1 (by simp), (hm c).1 (by simp), (hm d).1 (by simp)⟩

end PEqualNP.Outside.L_meta_3771

theorem PEqualNP.Outside.L_meta_3771 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ x1) → x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) := by
  intro x1 A B h
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  obtain ⟨A', hA', hc'⟩ := Finset.exists_subset_card_eq (s := A) (n := 4) (by omega)
  obtain ⟨a, b, c, d, hab, hbc, hcd, ha, hb, hc2, hd⟩ :=
    PEqualNP.Outside.L_meta_3771.four A' hc'
  have hk := PEqualNP.Outside.L_meta_3771.key a b c d hab hbc hcd
  have hsub : B ⊆ ((List.finRange 13).filter fun y =>
      PEqualNP.Outside.L_meta_3771.good (a + y) && PEqualNP.Outside.L_meta_3771.good (b + y) &&
      PEqualNP.Outside.L_meta_3771.good (c + y) &&
      PEqualNP.Outside.L_meta_3771.good (d + y)).toFinset := by
    intro y hy
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
      Bool.and_eq_true, PEqualNP.Outside.L_meta_3771.good_iff]
    exact ⟨⟨⟨h a (hA' ha) y hy, h b (hA' hb) y hy⟩, h c (hA' hc2) y hy⟩, h d (hA' hd) y hy⟩
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le ((List.finRange 13).filter fun y =>
      PEqualNP.Outside.L_meta_3771.good (a + y) && PEqualNP.Outside.L_meta_3771.good (b + y) &&
      PEqualNP.Outside.L_meta_3771.good (c + y) &&
      PEqualNP.Outside.L_meta_3771.good (d + y))
  omega
