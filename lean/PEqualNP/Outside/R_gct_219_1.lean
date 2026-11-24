import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_gct_219_1
    (lower_bound : ∀ L : Submodule ℂ (Fin 4 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      Module.finrank ℂ L = 7 →
      let rank := fun i : Fin 4 =>
        Module.finrank ℂ (L.map (LinearMap.funLeft ℂ ℂ (fun j : Fin 5 => (i, j))))
      ∀ i, 2 ≤ rank i)
    (exclude_two : ∀ L : Submodule ℂ (Fin 4 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      Module.finrank ℂ L = 7 →
      let rank := fun i : Fin 4 =>
        Module.finrank ℂ (L.map (LinearMap.funLeft ℂ ℂ (fun j : Fin 5 => (i, j))))
      (∀ i, 2 ≤ rank i) → ∀ i, 3 ≤ rank i)
    (exclude_three : ∀ L : Submodule ℂ (Fin 4 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      Module.finrank ℂ L = 7 →
      let rank := fun i : Fin 4 =>
        Module.finrank ℂ (L.map (LinearMap.funLeft ℂ ℂ (fun j : Fin 5 => (i, j))))
      (∀ i, 3 ≤ rank i) → ∀ i, 4 ≤ rank i)
    (exclude_four : ∀ L : Submodule ℂ (Fin 4 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) →
      Module.finrank ℂ L = 7 →
      let rank := fun i : Fin 4 =>
        Module.finrank ℂ (L.map (LinearMap.funLeft ℂ ℂ (fun j : Fin 5 => (i, j))))
      (∀ i, 4 ≤ rank i) → False) :
    ¬ (∃ L : Submodule ℂ (Fin 4 × Fin 5 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) ∧ Module.finrank ℂ L = 7) := by
  rintro ⟨L, level, dim⟩
  have two := lower_bound L level dim
  have three := exclude_two L level dim two
  have four := exclude_three L level dim three
  exact exclude_four L level dim four
