import Mathlib
import PEqualNP.Defs

-- Cut by the number of paid negations.
-- free: with every negation free, twelve binary gates do not compute the edge function.
-- That settles two or three paid negations, since then at most twelve binary gates remain.
-- low: the posted step with at most one paid negation.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_3334_1
  (free : ∀ (n : Nat) (op : Fin n → Bool) (l r : Fin n → Nat × Bool)
    (out : Nat × Bool) (w : (Fin 9 → Bool) → Nat → Bool),
    n ≤ 12 →
    (∀ j, (l j).1 < 10 + j.val ∧ (r j).1 < 10 + j.val) →
    out.1 < 10 + n →
    (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
    (∀ x j, let v := fun p : Nat × Bool => w x p.1 ^^ p.2
      w x (10+j.val) = if op j then v (l j) && v (r j) else v (l j) || v (r j)) →
    ∃ x : Fin 9 → Bool, (w x out.1 ^^ out.2) ≠
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
  (low : ∀ (b : Nat) (op : Fin (b+1) → Bool) (l r : Fin (b+1) → Nat × Bool)
    (neg : Bool) (paid : Finset Nat) (w : (Fin 9 → Bool) → Nat → Bool),
    paid.card ≤ 1 → b + 1 + paid.card ≤ 14 →
    (∀ j, (l j).1 < 10 + j.val ∧ (r j).1 < 10 + j.val) →
    (have ok : Nat × Bool → Prop := fun p => (p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid);
      ok (10 + b, neg) ∧ ∀ j, ok (l j) ∧ ok (r j)) →
    (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
    (∀ x j, let v := fun p : Nat × Bool => w x p.1 ^^ p.2
      w x (10+j.val) = if op j then v (l j) && v (r j) else v (l j) || v (r j)) →
    9 ≤ (l (Fin.last b)).1 → 9 ≤ (r (Fin.last b)).1 →
    ∃ x : Fin 9 → Bool, (w x (10 + b) ^^ neg) ≠
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => List.foldl (fun (x2 : Bool) (x3 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x2 || x1 x3.1 && x1 x3.2) Bool.false [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))]; ∀ (x2 : ℕ) (x3 : Fin (x2 + (1 : ℕ)) → Bool) (x4 x5 : Fin (x2 + (1 : ℕ)) → ℕ × Bool) (x6 : Bool) (x7 : Finset ℕ) (x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x7.card ≤ (3 : ℕ) →     x2 + (1 : ℕ) + x7.card ≤ (14 : ℕ) →       (∀ (x11 : Fin (x2 + (1 : ℕ))), (x4 x11).1 < (10 : ℕ) + ↑x11 ∧ (x5 x11).1 < (10 : ℕ) + ↑x11) →         (have x12 : ℕ × Bool → Prop := fun (x12 : ℕ × Bool) => x12.2 = Bool.true → x12.1 = (0 : ℕ) ∨ x12.1 = (9 : ℕ) ∨ x12.1 ∈ x7;           x12 ((10 : ℕ) + x2, x6) ∧ ∀ (x13 : Fin (x2 + (1 : ℕ))), x12 (x4 x13) ∧ x12 (x5 x13)) →           (∀ (x13 : Fin (9 : ℕ) → Bool) (x14 : Fin (9 : ℕ)), x8 x13 ↑x14 = x13 x14) →             (∀ (x14 : Fin (9 : ℕ) → Bool), x8 x14 (9 : ℕ) = Bool.false) →               (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (x2 + (1 : ℕ))),                   have x17 : ℕ × Bool → Bool := fun (x17 : ℕ × Bool) => x8 x15 x17.1 ^^ x17.2;                   x8 x15 ((10 : ℕ) + ↑x16) = if x3 x16 = Bool.true then x17 (x4 x16) && x17 (x5 x16) else x17 (x4 x16) || x17 (x5 x16)) →                 (9 : ℕ) ≤ (x4 (Fin.last x2)).1 → (9 : ℕ) ≤ (x5 (Fin.last x2)).1 → ¬∀ (x18 : Fin (9 : ℕ) → Bool), (x8 x18 ((10 : ℕ) + x2) ^^ x6) = x1 x18 := by
  intro target b op l r neg paid w hcard hcost hback hpaid raw zero step hl hr
  have packed_eq : ∀ x : Fin 9 → Bool, target x =
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by
    decide +kernel
  intro correct
  by_cases few : paid.card ≤ 1
  · obtain ⟨x, hx⟩ := low b op l r neg paid w few hcost hback hpaid raw zero step hl hr
    exact hx ((correct x).trans (packed_eq x))
  · obtain ⟨x, hx⟩ := free (b+1) op l r (10 + b, neg) w (by omega) hback
      (by change 10 + b < 10 + (b+1); omega) raw zero step
    exact hx ((correct x).trans (packed_eq x))
