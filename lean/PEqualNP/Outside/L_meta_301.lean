import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_301 : ∀ (k : ℕ) (c : ℕ → Bool), (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) → k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k c hcov
  let pick (p : ℕ) := if c p = true then p else p + 1
  have hp (p : ℕ) : p ≤ pick p ∧ pick p ≤ p+1 := by
    dsimp [pick]
    split <;> omega
  have hv (p : ℕ) (h : p ≤ 2*k) : c (pick p) = true := by
    dsimp [pick]
    split
    · assumption
    · exact (hcov p h).resolve_left (by assumption)
  have count (a n : ℕ)
      (inside : ∀ i < n, 1 ≤ pick (a+2*i) ∧ pick (a+2*i) ≤ 2*k)
      (last : ∀ i < n, a+2*i ≤ 2*k) :
      n ≤ ((Finset.Icc 1 (2*k)).filter (fun j => c j = true)).card := by
    rw [← Finset.card_range n]
    apply Finset.card_le_card_of_injOn (fun i => pick (a+2*i))
    · intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (inside i hi'), hv _ (last i hi')⟩
    · intro i _ j _ he
      change pick (a+2*i) = pick (a+2*j) at he
      have := hp (a+2*i)
      have := hp (a+2*j)
      omega
  by_cases ends : c 0 = false ∧ c (2*k+1) = false
  · simp only [ite_eq_left ends]
    apply count 0 (k+1) _ (by intros; omega)
    intro i hi
    have h := hp (0+2*i)
    have v := hv (0+2*i) (by omega)
    have hn0 : pick (0+2*i) ≠ 0 := by intro e; rw [e, ends.1] at v; contradiction
    have hn1 : pick (0+2*i) ≠ 2*k+1 := by intro e; rw [e, ends.2] at v; contradiction
    omega
  · simp only [ite_eq_right ends, Nat.add_zero]
    apply count 1 k _ (by intros; omega)
    intro i hi
    have := hp (1+2*i)
    omega
