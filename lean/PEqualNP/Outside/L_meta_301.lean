import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Card

theorem PEqualNP.Outside.L_meta_301 : ∀ (k : ℕ) (c : ℕ → Bool), (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) → k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k c cover
  let inner := (Finset.Icc 1 (2 * k)).filter (fun j => c j = true)
  -- Take one covered vertex per edge in a matching. Its disjoint intervals
  -- ensure that the selected vertices are all different.
  have count (n offset : ℕ) (hit : ∀ j < n, ∃ v ∈ inner,
      offset + 2 * j ≤ v ∧ v ≤ offset + 2 * j + 1) : n ≤ inner.card := by
    classical
    choose v hv using fun j : Fin n => hit j j.isLt
    have injective : Function.Injective v := by
      intro a b eq
      apply Fin.ext
      have ha := (hv a).2
      have hb := (hv b).2
      omega
    calc n = (Finset.univ.image v).card := by
           rw [Finset.card_image_of_injective _ injective]
           simp
         _ ≤ inner.card := Finset.card_le_card (by
           intro i hi
           obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
           exact (hv j).1)
  by_cases ends : c 0 = false ∧ c (2 * k + 1) = false
  · simp only [ends]
    apply count (k + 1) 0
    intro j hj
    rcases cover (2 * j) (by omega) with left | right
    · have nz : 2 * j ≠ 0 := by
        intro eq
        rw [eq, ends.1] at left
        contradiction
      exact ⟨2 * j, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, left⟩,
        by omega, by omega⟩
    · have ne : 2 * j + 1 ≠ 2 * k + 1 := by
        intro eq
        rw [eq, ends.2] at right
        contradiction
      exact ⟨2 * j + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, right⟩,
        by omega, by omega⟩
  · simp only [ends, ite_false, Nat.add_zero]
    apply count k 1
    intro j hj
    rcases cover (1 + 2 * j) (by omega) with left | right
    · exact ⟨1 + 2 * j, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, left⟩,
        by omega, by omega⟩
    · exact ⟨1 + 2 * j + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, right⟩,
        by omega, by omega⟩
