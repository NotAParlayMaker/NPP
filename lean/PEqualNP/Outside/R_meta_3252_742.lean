import Mathlib
import PEqualNP.Defs

-- On a pair of singleton inputs the first gate accepting the pair alone must be an intersection.
-- With twelve points and twelve lines, uniqueness of the line through two points caps each
-- of its two rectangles at forty-six incident pairs.
theorem PEqualNP.Outside.R_meta_3252_742
    (small : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      0 < q →
      (∀ l, Fintype.card {p : Fin n // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))),
        let m := n+n
        let one := fun (p r : Fin n) => decide (r=p)
        o < m+s →
        (∀ p : Fin n, W p.val = {z | z.1 p = true} ∧ W (n+p.val) = {z | z.2 p = true}) →
        (∀ i < s, ∃ a b, max a b < m+i ∧ W (m+i) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
        (∀ p l, I p l → (one p,one l) ∈ W o) →
        (∀ L : Fin n → Bool, Fintype.card {l : Fin n // L l = true} ≤ q →
          ((fun p => decide (¬∃ l, I p l ∧ L l = true)),L) ∉ W o) →
        let A := fun (d : Bool) (w : ℕ) => {p : Fin n |
          (if d then (one p,fun _ => false) else (fun _ => false,one p)) ∈ W w}
        (∀ w < m+s, ∀ d, (A d w).ncard ≤ 12) → n*(q+1) ≤ 92*s)
    (large : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      100 < q → n = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin n // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))),
        let m := n+n
        let one := fun (p r : Fin n) => decide (r=p)
        o < m+s →
        (∀ p : Fin n, W p.val = {z | z.1 p = true} ∧ W (n+p.val) = {z | z.2 p = true}) →
        (∀ i < s, ∃ a b, max a b < m+i ∧ W (m+i) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
        (∀ p l, I p l → (one p,one l) ∈ W o) →
        (∀ L : Fin n → Bool, Fintype.card {l : Fin n // L l = true} ≤ q →
          ((fun p => decide (¬∃ l, I p l ∧ L l = true)),L) ∉ W o) →
        let A := fun (d : Bool) (w : ℕ) => {p : Fin n |
          (if d then (one p,fun _ => false) else (fun _ => false,one p)) ∈ W w}
        (∃ i < s, ∃ d : Bool, ∃ p r : Fin n, p ≠ r ∧ p ∈ A d (m+i) ∧ r ∈ A d (m+i) ∧
          ¬∃ a < m+i, ∃ b < m+i, A d (m+i) = A d a ∪ A d b) →
        (∃ w < m+s, ∃ d, 12 < (A d w).ncard) → n*q ≤ 100*s)
    : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 →               (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) →                 (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) →                   (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) →                     (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) →                       (have x19 : Bool → ℕ → Set (Fin x2) := fun (x19 : Bool) (x20 : ℕ) => {x21 : Fin x2 | (if x19 = Bool.true then (x13 x21, fun (x22 : Fin x2) => Bool.false) else (fun (x22 : Fin x2) => Bool.false, x13 x21)) ∈ x11 x20};                         ∃ x20 < x9, ∃ (x21 : Bool) (x22 : Fin x2) (x23 : Fin x2), x22 ≠ x23 ∧ x22 ∈ x19 x21 (x12 + x20) ∧ x23 ∈ x19 x21 (x12 + x20) ∧ ¬∃ x24 < x12 + x20, ∃ x25 < x12 + x20, x19 x21 (x12 + x20) = x19 x21 x24 ∪ x19 x21 x25) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  dsimp only at small large ⊢
  intro q n I _ hq order degree unique s o W out raw ops pos neg witness
  let A (d : Bool) (w : ℕ) := {p : Fin n |
    (if d then ((fun r => decide (r=p)),fun _ => false)
      else (fun _ => false,(fun r => decide (r=p)))) ∈ W w}
  by_cases cap : ∀ w < n+n+s, ∀ d, (A d w).ncard ≤ 12
  · have bound := small q n I (by omega) degree unique s o W out raw ops pos neg cap
    calc
      n*q ≤ n*(q+1) := Nat.mul_le_mul_left n (Nat.le_succ q)
      _ ≤ 92*s := bound
      _ ≤ 100*s := Nat.mul_le_mul_right s (by decide)
  · push Not at cap
    exact large q n I hq order degree unique s o W out raw ops pos neg witness cap
