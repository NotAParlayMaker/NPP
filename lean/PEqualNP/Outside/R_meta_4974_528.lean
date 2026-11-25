import Mathlib
import PEqualNP.Defs

-- Under any fixed switch assignment, point support is computed by unions and copies.
theorem PEqualNP.Outside.R_meta_4974_528
    (fixedSelectors :
      let shapes (m s : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ) :=
        ∀ j : Fin s, ∃ a < m+j.val, ∃ b < m+j.val,
          (∀ z, D z (m+j.val) = D z a ∪ D z b) ∨
          (∀ z, D z (m+j.val) = if z j then D z a else D z b) ∨
          ∀ z, D z (m+j.val) = ∅
      let selector (n s : ℕ) (I : Fin n → Fin n → Prop)
          (D : (Fin s → Bool) → ℕ → Finset ℕ) (z : Fin s → Bool) (l : Fin n) :=
        ∃ w < n+n+s, ∀ p : Fin n, p.val ∈ D z w ↔ I p l
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        (∀ l, Fintype.card {p // I p l} = q+1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
        ∀ (s : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ),
          (∀ z w, w<n+n → D z w = {w}) → shapes (n+n) s D →
          ∀ (z : Fin s → Bool) (L : Finset (Fin n)), (∀ l∈L, selector n s I D z l) → L.card*q ≤ s)
    (multipleSwitches :
      let shapes (m s : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ) :=
        ∀ j : Fin s, ∃ a < m+j.val, ∃ b < m+j.val,
          (∀ z, D z (m+j.val) = D z a ∪ D z b) ∨
          (∀ z, D z (m+j.val) = if z j then D z a else D z b) ∨
          ∀ z, D z (m+j.val) = ∅
      let selector (n s : ℕ) (I : Fin n → Fin n → Prop)
          (D : (Fin s → Bool) → ℕ → Finset ℕ) (z : Fin s → Bool) (l : Fin n) :=
        ∃ w < n+n+s, ∀ p : Fin n, p.val ∈ D z w ↔ I p l
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        (∀ l, Fintype.card {p // I p l} = q+1) →
        ∀ (s o : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ),
          o<n+n+s → (∀ z w, w<n+n → D z w = {w}) → shapes (n+n) s D →
          (∀ p : Fin n, p.val ∉ D (fun _ => false) o) →
          ∀ l, ¬ selector n s I D (fun _ => false) l → ∀ z : Fin s → Bool,
            (∀ p : Fin n, p.val ∈ D z o ↔ I p l) →
            2 ≤ ({j : Fin s | z j = true} : Set (Fin s)).ncard)
    (remaining :
      let shapes (m s : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ) :=
        ∀ j : Fin s, ∃ a < m+j.val, ∃ b < m+j.val,
          (∀ z, D z (m+j.val) = D z a ∪ D z b) ∨
          (∀ z, D z (m+j.val) = if z j then D z a else D z b) ∨
          ∀ z, D z (m+j.val) = ∅
      let selector (n s : ℕ) (I : Fin n → Fin n → Prop)
          (D : (Fin s → Bool) → ℕ → Finset ℕ) (z : Fin s → Bool) (l : Fin n) :=
        ∃ w < n+n+s, ∀ p : Fin n, p.val ∈ D z w ↔ I p l
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        300 ≤ q → n=q^2+q+1 →
        (∀ l, Fintype.card {p // I p l} = q+1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
        ∀ (s o : ℕ) (D : (Fin s → Bool) → ℕ → Finset ℕ),
          o < n+n+s → 3*n ≤ s+1 →
          (∀ z w, w<n+n → D z w = {w}) → shapes (n+n) s D →
          (∀ z p l, I p l → p.val ∈ D z o ∨ n+l.val ∈ D z o) →
          (∀ p : Fin n, p.val ∉ D (fun _ => false) o ∧ n+p.val ∈ D (fun _ => false) o) →
          (∀ T : Finset (Fin n), T.card ≤ q → ∃ z, ∀ p : Fin n,
            (p.val ∈ D z o ↔ ∃ l ∈ T, I p l) ∧ (n+p.val ∈ D z o ↔ p ∉ T)) →
          (∀ (z : Fin s → Bool) (L : Finset (Fin n)), (∀ l∈L, selector n s I D z l) → 100*L.card < n) →
          (∀ l, ¬ selector n s I D (fun _ => false) l → ∀ z : Fin s → Bool,
            (∀ p : Fin n, p.val ∈ D z o ↔ I p l) →
            2 ≤ ({j : Fin s | z j = true} : Set (Fin s)).ncard) →
          n*q ≤ 100*s) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : (Fin x9 → Bool) → ℕ → Finset ℕ),             x10 < x2 + x2 + x9 →               (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) →                 (∀ (x14 : Fin x9 → Bool), ∀ x15 < x2 + x2, x11 x14 x15 = {x15}) →                   (∀ (x15 : Fin x9), ∃ x16 < x2 + x2 + ↑x15, ∃ x17 < x2 + x2 + ↑x15, (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = x11 x18 x16 ∪ x11 x18 x17) ∨ (∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = if x18 x15 = Bool.true then x11 x18 x16 else x11 x18 x17) ∨ ∀ (x18 : Fin x9 → Bool), x11 x18 (x2 + x2 + ↑x15) = ∅) →                     (∀ (x16 : Fin x9 → Bool) (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x11 x16 x10 ∨ x2 + ↑x18 ∈ x11 x16 x10) →                       (∀ (x17 : Fin x2), ↑x17 ∉ x11 (fun (x18 : Fin x9) => Bool.false) x10 ∧ x2 + ↑x17 ∈ x11 (fun (x18 : Fin x9) => Bool.false) x10) →                         (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∃ (x20 : Fin x9 → Bool), ∀ (x21 : Fin x2), (↑x21 ∈ x11 x20 x10 ↔ ∃ x22 ∈ x18, x3 x21 x22) ∧ (x2 + ↑x21 ∈ x11 x20 x10 ↔ x21 ∉ x18)) →                           (∀ (x19 : Fin x9 → Bool) (x20 : ℕ),                               have x21 : Fin x9 → Bool := fun (x21 : Fin x9) => if ↑x21 < x20 ∧ x11 x19 (x2 + x2 + ↑x21) ⊆ x11 x19 x10 then x19 x21 else Bool.false;                               x11 x21 x10 ⊆ x11 (fun (x22 : Fin x9) => Bool.false) x10 ∪ x11 x19 x10 ∧ (x9 ≤ x20 → x11 x21 x10 = x11 x19 x10)) →                             x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q n I inst large count degree unique s o D out sparse inputs shapes safe baseline realize replay
  by_contra! short
  have scarce (z : Fin s → Bool) (L : Finset (Fin n))
      (selected : ∀ l∈L, ∃ w<n+n+s, ∀ p : Fin n, p.val ∈ D z w ↔ I p l) :
      100*L.card < n := by
    have bound := fixedSelectors q n I degree unique s D inputs shapes z L selected
    have scaled : (100*L.card)*q < n*q := calc
      (100*L.card)*q = 100*(L.card*q) := by ring
      _ ≤ 100*s := Nat.mul_le_mul_left 100 bound
      _ < n*q := short
    exact Nat.lt_of_mul_lt_mul_right scaled
  have done := remaining q n I large count degree unique s o D out sparse inputs shapes safe baseline realize scarce
    (multipleSwitches q n I degree s o D out inputs shapes (fun p => (baseline p).1))
  omega
