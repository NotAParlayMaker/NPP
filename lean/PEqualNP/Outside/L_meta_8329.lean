import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8329

def s1 : Finset (Fin (7 : ℕ) × Fin (7 : ℕ)) := {x1 : Fin (7 : ℕ) × Fin (7 : ℕ) | x1.1 = x1.2 ∨ x1.1 = x1.2 + (1 : Fin (7 : ℕ)) ∨ x1.1 = x1.2 + (3 : Fin (7 : ℕ))}

def s2 : Finset (Fin (7 : ℕ) × Fin (7 : ℕ)) := {x2 : Fin (7 : ℕ) × Fin (7 : ℕ) | x2.1 = x2.2}

theorem helper : s2 ⊆ s1 ∧ (∀ x3 ∈ s2, ∀ x5 ∈ s2, x3.1 = x5.1 → x3 = x5) ∧ (∀ x3 ∈ s2, ∀ x5 ∈ s2, x3.2 = x5.2 → x3 = x5) ∧ (∀ (x3 x4 x5 x6 : Fin (7 : ℕ)), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ s1 ∧ (x3, x6) ∈ s1 ∧ (x4, x5) ∈ s1 ∧ (x4, x6) ∈ s1)) ∧ s1.card = (21 : ℕ) ∧ s2.card = (7 : ℕ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · have h : ∀ (a b : Fin 7), (a, b) ∈ s1 ↔ (a = b ∨ a = b + 1 ∨ a = b + 3) := by
      intro a b
      simp [s1]
    intro a b c d hab hcd
    simp only [h]
    revert a b c d
    decide +kernel
  · decide +kernel
  · decide +kernel

end PEqualNP.Outside.L_meta_8329

theorem PEqualNP.Outside.L_meta_8329 : have x1 : Finset (Fin (7 : ℕ) × Fin (7 : ℕ)) := {x1 : Fin (7 : ℕ) × Fin (7 : ℕ) | x1.1 = x1.2 ∨ x1.1 = x1.2 + (1 : Fin (7 : ℕ)) ∨ x1.1 = x1.2 + (3 : Fin (7 : ℕ))}; have x2 : Finset (Fin (7 : ℕ) × Fin (7 : ℕ)) := {x2 : Fin (7 : ℕ) × Fin (7 : ℕ) | x2.1 = x2.2}; x2 ⊆ x1 ∧ (∀ x3 ∈ x2, ∀ x5 ∈ x2, x3.1 = x5.1 → x3 = x5) ∧ (∀ x3 ∈ x2, ∀ x5 ∈ x2, x3.2 = x5.2 → x3 = x5) ∧ (∀ (x3 x4 x5 x6 : Fin (7 : ℕ)), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x1 ∧ (x3, x6) ∈ x1 ∧ (x4, x5) ∈ x1 ∧ (x4, x6) ∈ x1)) ∧ x1.card = (21 : ℕ) ∧ x2.card = (7 : ℕ) := PEqualNP.Outside.L_meta_8329.helper
