import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_457 : ∀ E : List (Fin 3 × Fin 3), E = [(0, 1), (0, 2), (1, 2)] → ∀ τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3, (∀ e ∈ E, ∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 3 × Fin 3 → ℚ, (∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 3, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hc
  subst hE
  have i0 : ∀ f ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)],
      ¬ (f.1 ∈ ({0} : Finset (Fin 3)) ∧ f.2 ∈ ({0} : Finset (Fin 3))) := by decide
  have i1 : ∀ f ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)],
      ¬ (f.1 ∈ ({1} : Finset (Fin 3)) ∧ f.2 ∈ ({1} : Finset (Fin 3))) := by decide
  have i2 : ∀ f ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)],
      ¬ (f.1 ∈ ({2} : Finset (Fin 3)) ∧ f.2 ∈ ({2} : Finset (Fin 3))) := by decide
  have m01 : ((0 : Fin 3), (1 : Fin 3)) ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)] := by decide
  have m02 : ((0 : Fin 3), (2 : Fin 3)) ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)] := by decide
  have m12 : ((1 : Fin 3), (2 : Fin 3)) ∈ [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)] := by decide
  have a01_0 : τ (0, 1) {0} = 1 := by
    have := hτ _ m01 _ i0
    revert this
    generalize τ (0, 1) {0} = a
    decide +revert
  have a02_0 : τ (0, 2) {0} = 2 := by
    have := hτ _ m02 _ i0
    revert this
    generalize τ (0, 2) {0} = a
    decide +revert
  have a01_1 : τ (0, 1) {1} = 0 := by
    have := hτ _ m01 _ i1
    revert this
    generalize τ (0, 1) {1} = a
    decide +revert
  have a12_1 : τ (1, 2) {1} = 2 := by
    have := hτ _ m12 _ i1
    revert this
    generalize τ (1, 2) {1} = a
    decide +revert
  have a02_2 : τ (0, 2) {2} = 0 := by
    have := hτ _ m02 _ i2
    revert this
    generalize τ (0, 2) {2} = a
    decide +revert
  have a12_2 : τ (1, 2) {2} = 1 := by
    have := hτ _ m12 _ i2
    revert this
    generalize τ (1, 2) {2} = a
    decide +revert
  have b0 : τ (1, 2) {0} = 1 ∨ τ (1, 2) {0} = 2 := by
    have := hτ _ m12 _ i0
    revert this
    generalize τ (1, 2) {0} = a
    decide +revert
  have b1 : τ (0, 2) {1} = 0 ∨ τ (0, 2) {1} = 2 := by
    have := hτ _ m02 _ i1
    revert this
    generalize τ (0, 2) {1} = a
    decide +revert
  have b2 : τ (0, 1) {2} = 0 ∨ τ (0, 1) {2} = 1 := by
    have := hτ _ m01 _ i2
    revert this
    generalize τ (0, 1) {2} = a
    decide +revert
  have s01 := hc {0} i0 1
  have s02 := hc {0} i0 2
  have s10 := hc {1} i1 0
  have s12 := hc {1} i1 2
  have s20 := hc {2} i2 0
  have s21 := hc {2} i2 1
  simp only [List.filter_cons, List.filter_nil, a01_0, a02_0, a01_1, a12_1, a02_2, a12_2]
    at s01 s02 s10 s12 s20 s21
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases b0 with h0 | h0 <;> rcases b1 with h1 | h1 <;> rcases b2 with h2 | h2 <;>
    simp [h0, h1, h2] at s01 s02 s10 s12 s20 s21 <;>
    rcases he with rfl | rfl | rfl <;> linarith
