import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6816

def L : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]

def B : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (L.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ))

def a0 : Fin (285 : ℕ) := ⟨0, by decide⟩

def a1 : Fin (285 : ℕ) := ⟨1, by decide⟩

theorem dec : ∀ j < 26, ¬ ((L.getD ((a0.val + 1) / 13) 0).testBit (j / 13 * 13 + (j + 13 - (a0.val + 1) % 13) % 13) = true ∧ (L.getD ((a1.val + 1) / 13) 0).testBit (j / 13 * 13 + (j + 13 - (a1.val + 1) % 13) % 13) = true) := by
  decide +kernel

theorem key : ∀ s ∈ B, ¬ (a0 ∈ s ∧ a1 ∈ s) := by
  intro s hs h
  obtain ⟨h0, h1⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
  have hj' := List.mem_range.mp hj
  exact dec j hj' ⟨(List.mem_filter.mp (List.mem_toFinset.mp h0)).2, (List.mem_filter.mp (List.mem_toFinset.mp h1)).2⟩

theorem helper : ∀ (x3 : List (Finset (Fin (285 : ℕ)))),   x3.length ≤ (61 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (Finset (Fin (285 : ℕ))) := B ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) →       ∀ x6 ∈ B ++ x3, ∀ x8 ∈ B ++ x3, x6 ∈ B ∨ x8 ∈ B → ¬x6 ⊆ x8 → ¬x8 ⊆ x6 → x6 ∩ x8 ≠ (List.filter (fun (x13 : Fin (285 : ℕ)) => Decidable.decide (↑x13 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset := by
  intro x3 _ _ x6 h6 x8 h8 hor _ _ heq
  have m0 : a0 ∈ x6 ∩ x8 := by
    rw [heq]
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_finRange _, by decide⟩)
  have m1 : a1 ∈ x6 ∩ x8 := by
    rw [heq]
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_finRange _, by decide⟩)
  rw [Finset.mem_inter] at m0 m1
  rcases hor with h | h
  · exact key x6 h ⟨m0.1, m1.1⟩
  · exact key x8 h ⟨m0.2, m1.2⟩

end PEqualNP.Outside.L_meta_6816

theorem PEqualNP.Outside.L_meta_6816 : have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))),   x3.length ≤ (61 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) →       ∀ x6 ∈ x2 ++ x3, ∀ x8 ∈ x2 ++ x3, x6 ∈ x2 ∨ x8 ∈ x2 → ¬x6 ⊆ x8 → ¬x8 ⊆ x6 → x6 ∩ x8 ≠ (List.filter (fun (x13 : Fin (285 : ℕ)) => Decidable.decide (↑x13 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset := by
  exact PEqualNP.Outside.L_meta_6816.helper
