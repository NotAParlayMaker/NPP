import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_301 : ∀ (k : ℕ) (c : ℕ → Bool), (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) → k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k c cover
  let pick (j : ℕ) := if c j = true then j else j + 1
  have bounds (j : ℕ) : j ≤ pick j ∧ pick j ≤ j + 1 := by
    dsimp [pick]
    split_ifs <;> omega
  have picked (j : ℕ) (hj : j ≤ 2 * k) : c (pick j) = true := by
    dsimp [pick]
    split_ifs with h
    · exact h
    · exact (cover j hj).resolve_left h
  let S := (Finset.Icc 1 (2 * k)).filter (fun j => c j = true)
  have count (s n : ℕ) (h : ∀ i < n, pick (2 * i + s) ∈ S) : n ≤ S.card := by
    have maps : Set.MapsTo (fun i => pick (2 * i + s)) (Finset.range n) S :=
      fun i hi => h i (Finset.mem_range.mp hi)
    have inj : Set.InjOn (fun i => pick (2 * i + s)) (Finset.range n) := by
      intro i _ j _ heq
      have := bounds (2 * i + s)
      have := bounds (2 * j + s)
      dsimp only at heq
      omega
    simpa using Finset.card_le_card_of_injOn _ maps inj
  by_cases ends : c 0 = false ∧ c (2 * k + 1) = false
  · rw [ite_eq_left ends]
    apply count 0 (k + 1)
    intro i hi
    simp only [Nat.add_zero]
    have h := picked (2 * i) (by omega)
    have b := bounds (2 * i)
    have left : pick (2 * i) ≠ 0 := by
      intro e
      simp [e, ends.1] at h
    have right : pick (2 * i) ≠ 2 * k + 1 := by
      intro e
      simp [e, ends.2] at h
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, h⟩
  · rw [ite_eq_right ends, Nat.add_zero]
    apply count 1 k
    intro i hi
    have b := bounds (2 * i + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, picked _ (by omega)⟩
