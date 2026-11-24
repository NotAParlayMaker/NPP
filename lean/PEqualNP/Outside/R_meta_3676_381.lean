import Mathlib
import PEqualNP.Defs

-- Negate each OR wire and absorb that phase into its readers.
theorem PEqualNP.Outside.R_meta_3676_381
    (normalize : ∀ (n : ℕ) (op : Fin n → Bool) (a b : Fin n → ℕ × Bool)
      (v : (Fin 8 → Bool) → ℕ → Bool),
      (∀ x j, v x (10+j.val) = if op j then
        (v x (a j).1 ^^ (a j).2) && (v x (b j).1 ^^ (b j).2)
        else (v x (a j).1 ^^ (a j).2) || (v x (b j).1 ^^ (b j).2)) →
      ∃ (phase : ℕ → Bool) (l r : Fin n → ℕ × Bool) (u : (Fin 8 → Bool) → ℕ → Bool),
        (∀ q < 10, phase q = false) ∧ (∀ x q, u x q = (v x q ^^ phase q)) ∧
        (∀ j, (l j).1 = (a j).1 ∧ (r j).1 = (b j).1) ∧
        (∀ x j, u x (10+j.val) = ((u x (l j).1 ^^ (l j).2) && (u x (r j).1 ^^ (r j).2))))
    (positive : ∀ (n : ℕ) (a b : Fin n → ℕ × Bool) (o : ℕ) (u : (Fin 8 → Bool) → ℕ → Bool),
      n ≤ 11 → (∀ j, (a j).1 < 10+j.val ∧ (b j).1 < 10+j.val) → o < 10+n →
      (∀ (x : Fin 8 → Bool) (i : Fin 8), u x (i : Fin 8).val = x i) →
      (∀ x, u x 8 = false ∧ u x 9 = false) →
      (∀ x j, u x (10+j.val) = ((u x (a j).1 ^^ (a j).2) && (u x (b j).1 ^^ (b j).2))) →
      ∃ x, u x o ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
          (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 5 && x 7)))
    (negative : ∀ (n : ℕ) (a b : Fin n → ℕ × Bool) (o : ℕ) (u : (Fin 8 → Bool) → ℕ → Bool),
      n ≤ 11 → (∀ j, (a j).1 < 10+j.val ∧ (b j).1 < 10+j.val) → o < 10+n →
      (∀ (x : Fin 8 → Bool) (i : Fin 8), u x (i : Fin 8).val = x i) →
      (∀ x, u x 8 = false ∧ u x 9 = false) →
      (∀ x j, u x (10+j.val) = ((u x (a j).1 ^^ (a j).2) && (u x (b j).1 ^^ (b j).2))) →
      ∃ x, (!(u x o)) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
          (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 5 && x 7))) :
∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ) (x6 : (Fin (8 : ℕ) → Bool) → ℕ → Bool),   x1 ≤ (11 : ℕ) →     (∀ (x8 : Fin x1), (x3 x8).1 < (10 : ℕ) + ↑x8 ∧ (x4 x8).1 < (10 : ℕ) + ↑x8) →       x5 < (10 : ℕ) + x1 →         (∀ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ)), x6 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (8 : ℕ) → Bool), x6 x11 (8 : ℕ) = Bool.false ∧ x6 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (8 : ℕ) → Bool) (x13 : Fin x1),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x6 x12 x14.1 ^^ x14.2;                 x6 x12 ((10 : ℕ) + ↑x13) = if x2 x13 = Bool.true then x14 (x3 x13) && x14 (x4 x13) else x14 (x3 x13) || x14 (x4 x13)) →               ∃ (x13 : Fin (8 : ℕ) → Bool), (!x6 x13 x5) ≠ (x13 (0 : Fin (8 : ℕ)) && x13 (1 : Fin (8 : ℕ)) || x13 (1 : Fin (8 : ℕ)) && x13 (2 : Fin (8 : ℕ)) || x13 (2 : Fin (8 : ℕ)) && x13 (3 : Fin (8 : ℕ)) || x13 (3 : Fin (8 : ℕ)) && x13 (4 : Fin (8 : ℕ)) || x13 (4 : Fin (8 : ℕ)) && x13 (0 : Fin (8 : ℕ)) || x13 (0 : Fin (8 : ℕ)) && x13 (5 : Fin (8 : ℕ)) || x13 (1 : Fin (8 : ℕ)) && x13 (6 : Fin (8 : ℕ)) || x13 (2 : Fin (8 : ℕ)) && x13 (7 : Fin (8 : ℕ)) || x13 (5 : Fin (8 : ℕ)) && x13 (7 : Fin (8 : ℕ))) := by

  intro n op a b o v budget order out raw zero gate
  obtain ⟨phase,l,r,u,rawPhase,hValue,hIndex,hGate⟩ := normalize n op a b v gate
  have order' (j : Fin n) : (l j).1 < 10+j.val ∧ (r j).1 < 10+j.val := by
    rw [(hIndex j).1,(hIndex j).2]
    exact order j
  have raw' (x : Fin 8 → Bool) (i : Fin 8) : u x i.val = x i := by
    rw [hValue,raw,rawPhase _ (by have := i.isLt; omega)]
    cases x i <;> rfl
  have zero' (x : Fin 8 → Bool) : u x 8 = false ∧ u x 9 = false := by
    rw [hValue,hValue,(zero x).1,(zero x).2,rawPhase _ (by decide),rawPhase _ (by decide)]
    decide
  cases h : phase o with
  | false =>
    obtain ⟨x, hx⟩ := negative n l r o u budget order' out raw' zero' hGate
    rw [hValue,h] at hx
    exact ⟨x,by simpa using hx⟩
  | true =>
    obtain ⟨x, hx⟩ := positive n l r o u budget order' out raw' zero' hGate
    rw [hValue,h] at hx
    exact ⟨x,by simpa using hx⟩
