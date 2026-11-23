import Mathlib
import PEqualNP.Defs

-- For each singleton independent set, the two incident edges must point away.
theorem PEqualNP.Outside.L_meta_356 : ∀ E : List (Fin 3 × Fin 3), E = [(0, 1), (0, 2), (1, 2)] → ∀ τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3, (∀ e ∈ E, ∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 3 × Fin 3 → ℚ, (∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 3, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  classical
  rintro E rfl τ hτ c heq e he
  have ind0 : ∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ¬ (f.1 ∈ ({0} : Finset (Fin 3)) ∧ f.2 ∈ ({0} : Finset (Fin 3))) := by decide
  have h0_01 := hτ (0, 1) (by decide) {0} ind0
  have t0_01 : τ (0, 1) {0} = 1 := by
    simpa only [Prod.fst, Prod.snd] using
      h0_01.1.resolve_left (fun h => h0_01.2 (Finset.mem_singleton.mpr h))
  have h0_02 := hτ (0, 2) (by decide) {0} ind0
  have t0_02 : τ (0, 2) {0} = 2 := by
    simpa only [Prod.fst, Prod.snd] using
      h0_02.1.resolve_left (fun h => h0_02.2 (Finset.mem_singleton.mpr h))
  have h0_12 := hτ (1, 2) (by decide) {0} ind0
  have s01 := heq {0} ind0 1
  have s02 := heq {0} ind0 2
  have ind1 : ∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ¬ (f.1 ∈ ({1} : Finset (Fin 3)) ∧ f.2 ∈ ({1} : Finset (Fin 3))) := by decide
  have h1_01 := hτ (0, 1) (by decide) {1} ind1
  have t1_01 : τ (0, 1) {1} = 0 := by
    simpa only [Prod.fst, Prod.snd] using
      h1_01.1.resolve_right (fun h => h1_01.2 (Finset.mem_singleton.mpr h))
  have h1_02 := hτ (0, 2) (by decide) {1} ind1
  have h1_12 := hτ (1, 2) (by decide) {1} ind1
  have t1_12 : τ (1, 2) {1} = 2 := by
    simpa only [Prod.fst, Prod.snd] using
      h1_12.1.resolve_left (fun h => h1_12.2 (Finset.mem_singleton.mpr h))
  have s10 := heq {1} ind1 0
  have s12 := heq {1} ind1 2
  have ind2 : ∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ¬ (f.1 ∈ ({2} : Finset (Fin 3)) ∧ f.2 ∈ ({2} : Finset (Fin 3))) := by decide
  have h2_01 := hτ (0, 1) (by decide) {2} ind2
  have h2_02 := hτ (0, 2) (by decide) {2} ind2
  have t2_02 : τ (0, 2) {2} = 0 := by
    simpa only [Prod.fst, Prod.snd] using
      h2_02.1.resolve_right (fun h => h2_02.2 (Finset.mem_singleton.mpr h))
  have h2_12 := hτ (1, 2) (by decide) {2} ind2
  have t2_12 : τ (1, 2) {2} = 1 := by
    simpa only [Prod.fst, Prod.snd] using
      h2_12.1.resolve_right (fun h => h2_12.2 (Finset.mem_singleton.mpr h))
  have s20 := heq {2} ind2 0
  have s21 := heq {2} ind2 1
  rcases h0_12.1 with q0 | q0 <;>
    rcases h1_02.1 with q1 | q1 <;>
    rcases h2_01.1 with q2 | q2
  all_goals
    simp (config := { decide := true }) [t0_01, t0_02, t1_01, t1_12, t2_02, t2_12, q0, q1, q2] at s01 s02 s10 s12 s20 s21
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> linarith
