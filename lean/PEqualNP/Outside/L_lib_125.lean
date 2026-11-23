import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_125 :
    ∀ (α : Type) (D : (ℕ → ℕ) → Set α) (p' q : ℕ),
      1 ≤ p' → p' < q →
      (∀ s : ℕ, 1 ≤ s → D (fun m => 2 ^ (q * s * m)) ⊆ D (fun m => 2 ^ (p' * s * m))) →
      ∀ i r : ℕ, 1 ≤ r →
        D (fun m => 2 ^ (q ^ i * r * m)) ⊆ D (fun m => 2 ^ (p' ^ i * r * m)) := by
  intro α D p' q hp' hpq hstep i r hr
  have hq0 : 0 < q := lt_of_le_of_lt (Nat.zero_le p') hpq
  have key : ∀ i : ℕ, ∀ r : ℕ, 1 ≤ r →
      ∀ x, x ∈ D (fun m => 2 ^ (q ^ i * r * m)) →
        x ∈ D (fun m => 2 ^ (p' ^ i * r * m)) := by
    intro i
    induction i with
    | zero =>
      intro r hr x hx
      have h : (fun m => 2 ^ (q ^ 0 * r * m)) = (fun m => 2 ^ (p' ^ 0 * r * m)) := by
        funext m
        rw [pow_zero, pow_zero, one_mul, one_mul]
      rw [h] at hx
      exact hx
    | succ i ih =>
      intro r hr x hx
      have hpos : 1 ≤ q ^ i * r := one_le_mul (le_of_lt (pow_pos hq0 i)) hr
      have hx1 : x ∈ D (fun m => 2 ^ (q * (q ^ i * r) * m)) := by
        have e : (fun m => 2 ^ (q * (q ^ i * r) * m)) =
            (fun m => 2 ^ (q ^ (i + 1) * r * m)) := by
          funext m
          rw [show q * (q ^ i * r) * m = q ^ (i + 1) * r * m from by
            rw [pow_succ]; ring]
        rw [e]
        exact hx
      have hA : x ∈ D (fun m => 2 ^ (p' * (q ^ i * r) * m)) := hstep (q ^ i * r) hpos hx1
      have hA' : x ∈ D (fun m => 2 ^ (q ^ i * (p' * r) * m)) := by
        have e : (fun m => 2 ^ (q ^ i * (p' * r) * m)) =
            (fun m => 2 ^ (p' * (q ^ i * r) * m)) := by
          funext m
          rw [show q ^ i * (p' * r) * m = p' * (q ^ i * r) * m from by ring]
        rw [e]
        exact hA
      have hB : x ∈ D (fun m => 2 ^ (p' ^ i * (p' * r) * m)) :=
        ih (p' * r) (one_le_mul hp' hr) hA'
      have e : (fun m => 2 ^ (p' ^ i * (p' * r) * m)) =
          (fun m => 2 ^ (p' ^ (i + 1) * r * m)) := by
        funext m
        rw [show p' ^ i * (p' * r) * m = p' ^ (i + 1) * r * m from by
          rw [pow_succ]; ring]
      rw [e] at hB
      exact hB
  intro x hx
  exact key i r hr x hx
