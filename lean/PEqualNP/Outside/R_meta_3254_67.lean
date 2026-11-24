import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000
open scoped Classical in
theorem PEqualNP.Outside.R_meta_3254_67
    (pairBound : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 → (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) → (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) → (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) → (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) → 3*x2 ≤ x9+1)
    (largeSparse : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 → (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) → (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) → (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) → (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) → let covered : Set (Fin x2 × Fin x2) := {x19 | x3 x19.1 x19.2 ∧ ∃ x20 < x9, x11 (x12 + x20) ⊆ x11 x10 ∧ (x13 x19.1, x13 x19.2) ∈ x11 (x12 + x20) ∧ ∃ (x21 : ℕ) (x22 : ℕ), Max.max x21 x22 < x12 + x20 ∧ x11 (x12 + x20) = x11 x21 ∩ x11 x22 ∧ ∃ (x23 : Set (Fin x2 → Bool)) (x24 : Set (Fin x2 → Bool)), x11 x21 = x23 ×ˢ Set.univ ∧ x11 x22 = Set.univ ×ˢ x24}; covered.ncard ≤ 4*x9 → 3*x2 ≤ x9+1 → (∃ l : Fin x2, 25*({e : Fin x2 × Fin x2 | e ∈ covered ∧ e.2=l} : Set _).ncard < x1) → x2 * x1 ≤ (100 : ℕ) * x9) : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 → (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) → (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) → (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) → (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) → {x19 : Fin x2 × Fin x2 | x3 x19.1 x19.2 ∧ ∃ x20 < x9, x11 (x12 + x20) ⊆ x11 x10 ∧ (x13 x19.1, x13 x19.2) ∈ x11 (x12 + x20) ∧ ∃ (x21 : ℕ) (x22 : ℕ), Max.max x21 x22 < x12 + x20 ∧ x11 (x12 + x20) = x11 x21 ∩ x11 x22 ∧ ∃ (x23 : Set (Fin x2 → Bool)) (x24 : Set (Fin x2 → Bool)), x11 x21 = x23 ×ˢ Set.univ ∧ x11 x22 = Set.univ ×ˢ x24}.ncard ≤ (4 : ℕ) * x9 → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I dec hq order degrees unique s out S
  dsimp only
  intro bound inputs steps yes no few
  have low := pairBound q N I hq order degrees unique s out S bound inputs steps yes no
  by_contra! small
  have big : 300≤q := by
    by_contra! h
    have hN : 100≤N := by omega
    have scaled := Nat.mul_le_mul_left N (show q≤299 by omega)
    omega
  apply small.not_ge
  apply largeSparse q N I big order degrees unique s out S bound inputs steps yes no few low
  have sparse (U : Set (Fin N × Fin N)) (fewU : U.ncard ≤ 4*s) :
      ∃ l : Fin N, 25*({e : Fin N × Fin N | e∈U ∧ e.2=l} : Set _).ncard < q := by
    let C := U.toFinset
    have count : C.card≤4*s := by
      change U.toFinset.card ≤ 4*s
      rw [←Set.ncard_eq_toFinset_card']
      exact fewU
    have eq (l : Fin N) : ({e : Fin N × Fin N | e∈U ∧ e.2=l} : Set _).ncard = (C.filter (fun e => e.2=l)).card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext e
      simp [C]
    simp only [eq]
    by_contra! dense
    have add := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun l _ => dense l)
    have sum : (∑ l : Fin N, (C.filter (fun e => e.2 = l)).card) = C.card := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter C Finset.univ Prod.snd
    rw [← Finset.mul_sum,sum] at add
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at add
    change N*q ≤ 25*C.card at add
    omega
  exact sparse _ few
