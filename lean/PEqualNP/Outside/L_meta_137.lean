import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_137 : ∀ (m : ℕ) (r1 r2 r3 : Fin m → ℚ), (∀ j, r1 j = 0 ∨ r1 j = 1) → (∀ j, r2 j = 0 ∨ r2 j = 1) → (∀ j, r3 j = 0 ∨ r3 j = 1) → r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 → (∃ j, r1 j = 1 ∧ r2 j = 1) → (∃ j, r1 j = 1 ∧ r3 j = 1) → (∃ j, r2 j = 1 ∧ r3 j = 1) → LinearIndependent ℚ ![r1, r2, r3] := by
  intro m r1 r2 r3 h1 h2 h3 n12 n13 n23 h12 h13 h23
  obtain ⟨j1, a1, b1⟩ := h12
  obtain ⟨j2, a2, c2⟩ := h13
  obtain ⟨j3, b3, c3⟩ := h23
  obtain ⟨k12, hk12⟩ := Function.ne_iff.mp n12
  obtain ⟨k13, hk13⟩ := Function.ne_iff.mp n13
  obtain ⟨k23, hk23⟩ := Function.ne_iff.mp n23
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Every column gives one linear equation on the three coefficients.
  have E : ∀ k, g 0 * r1 k + g 1 * r2 k + g 2 * r3 k = 0 := by
    intro k
    have := congrFun hg k
    simpa [Fin.sum_univ_three] using this
  have e1 := E j1
  have e2 := E j2
  have e3 := E j3
  have f12 := E k12
  have f13 := E k13
  have f23 := E k23
  rw [a1, b1] at e1
  rw [a2, c2] at e2
  rw [b3, c3] at e3
  -- Step 1: one of the three coefficients vanishes.
  have hor : g 0 = 0 ∨ g 1 = 0 ∨ g 2 = 0 := by
    rcases h3 j1 with x | x <;> rw [x] at e1 <;>
    rcases h2 j2 with y | y <;> rw [y] at e2 <;>
    rcases h1 j3 with z | z <;> rw [z] at e3 <;>
    rcases h1 k12 with p | p <;> rcases h2 k12 with q | q <;> rcases h3 k12 with s | s <;>
    rw [p, q, s] at f12 <;> rw [p, q] at hk12 <;>
    first
    | exact absurd rfl hk12
    | (left; linarith)
    | (right; left; linarith)
    | (right; right; linarith)
  -- Step 2: the two remaining coefficients vanish as well.
  have key : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 := by
    rcases hor with h | h | h
    · rw [h, zero_mul, zero_add] at e3 f23
      rcases h2 k23 with q | q <;> rcases h3 k23 with s | s <;>
      rw [q, s] at f23 <;> rw [q, s] at hk23 <;>
      first
      | exact absurd rfl hk23
      | exact ⟨h, by linarith, by linarith⟩
    · rw [h, zero_mul, add_zero] at e2 f13
      rcases h1 k13 with p | p <;> rcases h3 k13 with s | s <;>
      rw [p, s] at f13 <;> rw [p, s] at hk13 <;>
      first
      | exact absurd rfl hk13
      | exact ⟨by linarith, h, by linarith⟩
    · rw [h, zero_mul, add_zero] at e1 f12
      rcases h1 k12 with p | p <;> rcases h2 k12 with q | q <;>
      rw [p, q] at f12 <;> rw [p, q] at hk12 <;>
      first
      | exact absurd rfl hk12
      | exact ⟨by linarith, by linarith, h⟩
  intro i
  fin_cases i
  · exact key.1
  · exact key.2.1
  · exact key.2.2
