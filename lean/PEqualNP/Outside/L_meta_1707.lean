import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1707

def lines : List (Finset (Fin 21)) := [{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}]

theorem key : ∀ x ∈ ({0, 6, 7, 8} : Finset (Fin 21)), ∀ y ∈ ({2, 10, 15, 20} : Finset (Fin 21)),
    ∃ m ∈ lines, 3 ≤ (({3, 4, 11, x, y} : Finset (Fin 21)) ∩ m).card := by
  decide +kernel

theorem ex1 : ∀ m ∈ lines, ((({3, 4, 11} : Finset (Fin 21))) ∩ m).card ≤ 2 := by
  intro m hm
  unfold lines at hm
  fin_cases hm <;> decide

theorem ex2 : ∀ p ∈ ({3, 4, 11} : Finset (Fin 21)), p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21)) := by
  decide +kernel

theorem main (A : Finset (Fin 21)) (h : ∀ m ∈ lines, (A ∩ m).card ≤ 2)
    (h3 : ({3, 4, 11} : Finset (Fin 21)) ⊆ A) :
    A ∩ ({0, 6, 7, 8} : Finset (Fin 21)) = ∅ ∨ A ∩ ({2, 10, 15, 20} : Finset (Fin 21)) = ∅ := by
  by_contra hc
  obtain ⟨hx, hy⟩ := not_or.mp hc
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hx
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hy
  rw [Finset.mem_inter] at hx hy
  obtain ⟨m, hm, hcard⟩ := key x hx.2 y hy.2
  have hS : ({3, 4, 11, x, y} : Finset (Fin 21)) ⊆ A := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h3 (by decide)
    · exact h3 (by decide)
    · exact h3 (by decide)
    · exact hx.1
    · exact hy.1
  have h1 := Finset.card_le_card (Finset.inter_subset_inter hS (Finset.Subset.refl m))
  have h2 := h m hm
  omega

end PEqualNP.Outside.L_meta_1707

theorem PEqualNP.Outside.L_meta_1707 : (∀ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A → (A ∩ ({0, 6, 7, 8} : Finset (Fin 21)) = ∅ ∨ A ∩ ({2, 10, 15, 20} : Finset (Fin 21)) = ∅)) ∧ ∃ A : Finset (Fin 21), (∀ m ∈ ([{1, 5, 9, 13, 17}, {0, 5, 6, 7, 8}, {2, 5, 10, 15, 20}, {4, 5, 12, 14, 19}, {3, 5, 11, 16, 18}, {0, 1, 2, 3, 4}, {1, 6, 10, 14, 18}, {1, 8, 12, 16, 20}, {1, 7, 11, 15, 19}, {0, 9, 10, 11, 12}, {2, 6, 9, 16, 19}, {4, 8, 9, 15, 18}, {3, 7, 9, 14, 20}, {0, 17, 18, 19, 20}, {3, 6, 12, 15, 17}, {2, 8, 11, 14, 17}, {4, 7, 10, 16, 17}, {0, 13, 14, 15, 16}, {4, 6, 11, 13, 20}, {3, 8, 10, 13, 19}, {2, 7, 12, 13, 18}] : List (Finset (Fin 21))), (A ∩ m).card ≤ 2) ∧ (∀ p ∈ A, p ∉ ({1, 5, 9, 13, 17} : Finset (Fin 21))) ∧ ({3, 4, 11} : Finset (Fin 21)) ⊆ A := by
  refine ⟨fun A h => PEqualNP.Outside.L_meta_1707.main A h.1 h.2.2, ?_⟩
  exact ⟨{3, 4, 11}, PEqualNP.Outside.L_meta_1707.ex1, PEqualNP.Outside.L_meta_1707.ex2, Finset.Subset.refl _⟩
