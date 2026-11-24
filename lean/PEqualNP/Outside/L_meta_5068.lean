import Mathlib

namespace PEqualNP.Outside.L_meta_5068_aux

theorem card_inc (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) :
    ({x : Fin N × Fin N | I x.1 x.2} : Set (Fin N × Fin N)).ncard = N * (q + 1) := by
  rw [Set.ncard_eq_toFinset_card']
  rw [Set.toFinset_setOf, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have : ∀ l : Fin N, (∑ p : Fin N, if I p l then 1 else 0) = q + 1 := by
    intro l
    rw [← Finset.card_filter, ← Fintype.card_subtype]
    exact h l
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PEqualNP.Outside.L_meta_5068_aux

theorem PEqualNP.Outside.L_meta_5068 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x2 → Fin x2 → Prop) [x5 : DecidableRel x4],   (∀ (x6 : Fin x2), Fintype.card { x7 : Fin x2 // x4 x7 x6 } = x1 + (1 : ℕ)) →     ∀ x7 ⊆ {x8 : Fin x2 × Fin x2 | x4 x8.1 x8.2},       x7.ncard ≤ (4 : ℕ) * x3 →         (100 : ℕ) * x3 < x2 * x1 →           have x11 : Set (Fin x2 × Fin x2) := {x11 : Fin x2 × Fin x2 | x4 x11.1 x11.2} \ x7;           (96 : ℕ) * x3 + x2 < x11.ncard ∧ (24 : ℕ) * (x2 * x1) + (25 : ℕ) * x2 < (25 : ℕ) * x11.ncard := by
  intro q N k I _ h S hS hk hq
  have hA := PEqualNP.Outside.L_meta_5068_aux.card_inc q N I h
  have hfin : ({x : Fin N × Fin N | I x.1 x.2} : Set (Fin N × Fin N)).Finite := Set.toFinite _
  have hd := Set.ncard_diff hS (hfin.subset hS)
  have hle := Set.ncard_le_ncard hS hfin
  show 96 * k + N < (({x : Fin N × Fin N | I x.1 x.2} : Set (Fin N × Fin N)) \ S).ncard ∧
    24 * (N * q) + 25 * N < 25 * (({x : Fin N × Fin N | I x.1 x.2} : Set (Fin N × Fin N)) \ S).ncard
  rw [hd, hA]
  rw [hA] at hle
  have e : N * (q + 1) = N * q + N := by ring
  rw [e] at hle ⊢
  constructor <;> omega
