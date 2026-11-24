import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Field.Rat

namespace PEqualNP.Outside.L_meta_457

def triangle : List (Fin 3 × Fin 3) := [(0, 1), (0, 2), (1, 2)]

lemma singleton_independent (i : Fin 3) :
    ∀ f ∈ triangle, ¬ (f.1 ∈ ({i} : Finset (Fin 3)) ∧ f.2 ∈ ({i} : Finset (Fin 3))) := by
  decide +revert

-- Choosing a single marked vertex forces its two edges away. The
-- third edge picks one remaining endpoint, isolating the other edge.
set_option maxRecDepth 2048 in
lemma triangle_zero (τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3)
    (hτ : ∀ e ∈ triangle, ∀ i : Fin 3,
      (τ e {i} = e.1 ∨ τ e {i} = e.2) ∧ τ e {i} ≠ i)
    (c : Fin 3 × Fin 3 → ℚ)
    (hc : ∀ i v : Fin 3, ((triangle.filter (fun e => τ e {i} = v)).map c).sum = 0) :
    c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 := by
  have h₀₁₀ : τ (0, 1) {0} = 1 := ((hτ (0, 1) (by decide) 0).1).resolve_left (hτ (0, 1) (by decide) 0).2
  have h₀₂₀ : τ (0, 2) {0} = 2 := ((hτ (0, 2) (by decide) 0).1).resolve_left (hτ (0, 2) (by decide) 0).2
  have h₀₁₁ : τ (0, 1) {1} = 0 := ((hτ (0, 1) (by decide) 1).1).resolve_right (hτ (0, 1) (by decide) 1).2
  have h₁₂₁ : τ (1, 2) {1} = 2 := ((hτ (1, 2) (by decide) 1).1).resolve_left (hτ (1, 2) (by decide) 1).2
  have h₀₂₂ : τ (0, 2) {2} = 0 := ((hτ (0, 2) (by decide) 2).1).resolve_right (hτ (0, 2) (by decide) 2).2
  have h₁₂₂ : τ (1, 2) {2} = 1 := ((hτ (1, 2) (by decide) 2).1).resolve_right (hτ (1, 2) (by decide) 2).2
  have x₁ := hc 0 1
  have x₂ := hc 0 2
  have y₀ := hc 1 0
  have y₂ := hc 1 2
  have z₀ := hc 2 0
  have z₁ := hc 2 1
  have ha := (hτ (1, 2) (by decide) 0).1
  have hb := (hτ (0, 2) (by decide) 1).1
  have hd := (hτ (0, 1) (by decide) 2).1
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hd with hd | hd <;>
    simp [triangle, h₀₁₀, h₀₂₀, h₀₁₁, h₁₂₁, h₀₂₂, h₁₂₂, ha, hb, hd] at x₁ x₂ y₀ y₂ z₀ z₁ <;>
    grind

end PEqualNP.Outside.L_meta_457

open PEqualNP.Outside.L_meta_457

theorem PEqualNP.Outside.L_meta_457 :
    ∀ E : List (Fin 3 × Fin 3), E = [(0, 1), (0, 2), (1, 2)] →
      ∀ τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3,
        (∀ e ∈ E, ∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
          (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) →
        ∀ c : Fin 3 × Fin 3 → ℚ,
          (∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
            ∀ v : Fin 3, ((E.filter (fun e => τ e I = v)).map c).sum = 0) →
          ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hc
  subst E
  obtain ⟨ha, hb, hd⟩ := triangle_zero τ (fun e he i => by
    have h := hτ e he {i} (singleton_independent i)
    simpa only [Finset.mem_singleton] using h) c (fun i => hc {i} (singleton_independent i))
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> assumption
