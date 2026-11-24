∀ {m : ℕ} {F : Type} [Field F] (A B : (Fin m → Bool) → F) (r : Fin m → F),
  (∀ i, r i ≠ 0 ∧ r i ≠ 1) → ∀ (x₀ : Fin m → Bool), A x₀ ≠ B x₀ → (∀ x, x ≠ x₀ → A x = B x) →
  (∑ x, A x * ∏ i, (if x i then r i else 1 - r i)) ≠ (∑ x, B x * ∏ i, (if x i then r i else 1 - r i))
