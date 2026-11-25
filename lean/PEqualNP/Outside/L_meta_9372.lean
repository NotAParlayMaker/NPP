import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9372_aux

def Z (i j : Fin 16) : Bool := !((([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val)

def nz : Finset (Fin 16) := Finset.univ.erase 0

theorem row7 : ∀ x ∈ nz, (nz.filter fun y => Z x y = true).card = 7 := by decide +kernel
theorem col7 : ∀ y ∈ nz, (nz.filter fun x => Z x y = true).card = 7 := by decide +kernel
theorem row3 : ∀ x ∈ nz, ∀ x' ∈ nz, x ≠ x' →
    (nz.filter fun y => Z x y = true ∧ Z x' y = true).card ≤ 3 := by decide +kernel
theorem col3 : ∀ y ∈ nz, ∀ y' ∈ nz, y ≠ y' →
    (nz.filter fun x => Z x y = true ∧ Z x y' = true).card ≤ 3 := by decide +kernel
theorem nzc : nz.card = 15 := by decide +kernel

def cnt (A : Finset (Fin 16)) : ℕ := (nz.filter fun x => x ∈ A).card

def cl (m : ℕ) : ℕ := (m + 2) / 3

theorem le_cl (m : ℕ) : m ≤ 3 * cl m := by unfold cl; omega

-- A set with at least two nonzero members leaves at most three common zeros.
theorem few (P : Fin 16 → Fin 16 → Bool)
    (p7 : ∀ x ∈ nz, (nz.filter fun y => P x y = true).card = 7)
    (p3 : ∀ x ∈ nz, ∀ x' ∈ nz, x ≠ x' →
      (nz.filter fun y => P x y = true ∧ P x' y = true).card ≤ 3)
    (A B : Finset (Fin 16)) (h : ∀ i ∈ A, ∀ j ∈ B, P i j = true) :
    (1 ≤ cnt A → cnt B ≤ 7) ∧ (2 ≤ cnt A → cnt B ≤ 3) := by
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := Finset.card_pos.mp ha
    have hx' := Finset.mem_filter.mp hx
    rw [← p7 x hx'.1]
    apply Finset.card_le_card
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hy'.1, h x hx'.2 y hy'.2⟩
  · intro ha
    obtain ⟨x, hx, x', hx', ne⟩ := Finset.one_lt_card.mp ha
    have h1 := Finset.mem_filter.mp hx
    have h2 := Finset.mem_filter.mp hx'
    refine le_trans (Finset.card_le_card ?_) (p3 x h1.1 x' h2.1 ne)
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hy'.1, h x h1.2 y hy'.2, h x' h2.2 y hy'.2⟩

theorem weight (a b : ℕ) (h1 : 1 ≤ a → b ≤ 7) (h2 : 2 ≤ a → b ≤ 3)
    (h3 : 1 ≤ b → a ≤ 7) (h4 : 2 ≤ b → a ≤ 3) :
    a * cl b + b * cl a + 2 * (a * b) ≤ 24 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [cl]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [cl]
  have hb7 := h1 ha
  have ha7 := h3 hb
  unfold cl
  interval_cases a <;> interval_cases b <;> simp_all

theorem dbl {n : ℕ} (A : Fin n → Finset (Fin 16)) (f : Fin n → ℕ) :
    ∑ x ∈ nz, ∑ k : Fin n, (if x ∈ A k then f k else 0) = ∑ k : Fin n, cnt (A k) * f k := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  rfl

theorem rowArea {n : ℕ} (P : Fin 16 → Fin 16 → Bool)
    (p7 : ∀ x ∈ nz, (nz.filter fun y => P x y = true).card = 7)
    (A B : Fin n → Finset (Fin 16))
    (hc : ∀ i j, P i j = true → ∃ k, i ∈ A k ∧ j ∈ B k) (x : Fin 16) (hx : x ∈ nz) :
    7 ≤ ∑ k : Fin n, (if x ∈ A k then cnt (B k) else 0) := by
  rw [← p7 x hx, ← Finset.sum_filter]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_biUnion_le
    (s := Finset.univ.filter fun k : Fin n => x ∈ A k)
    (t := fun k => nz.filter fun y => y ∈ B k))
  intro y hy
  have hy' := Finset.mem_filter.mp hy
  obtain ⟨k, h1, h2⟩ := hc x y hy'.2
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, h1⟩,
    Finset.mem_filter.mpr ⟨hy'.1, h2⟩⟩

theorem rowCount {n : ℕ} (P : Fin 16 → Fin 16 → Bool)
    (p7 : ∀ x ∈ nz, (nz.filter fun y => P x y = true).card = 7)
    (A B : Fin n → Finset (Fin 16))
    (hc : ∀ i j, P i j = true → ∃ k, i ∈ A k ∧ j ∈ B k) :
    45 ≤ ∑ k : Fin n, cnt (A k) * cl (cnt (B k)) ∧ 105 ≤ ∑ k : Fin n, cnt (A k) * cnt (B k) := by
  constructor
  · rw [← dbl A fun k => cl (cnt (B k))]
    have each : ∀ x ∈ nz, 3 ≤ ∑ k : Fin n, (if x ∈ A k then cl (cnt (B k)) else 0) := by
      intro x hx
      have h := rowArea P p7 A B hc x hx
      have u : ∑ k : Fin n, (if x ∈ A k then cnt (B k) else 0) ≤
          3 * ∑ k : Fin n, (if x ∈ A k then cl (cnt (B k)) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k _
        split
        · exact le_cl _
        · omega
      omega
    have s := Finset.card_nsmul_le_sum nz _ 3 each
    rw [nzc, smul_eq_mul] at s
    omega
  · rw [← dbl A fun k => cnt (B k)]
    have s := Finset.card_nsmul_le_sum nz _ 7 (fun x hx => rowArea P p7 A B hc x hx)
    rw [nzc, smul_eq_mul] at s
    omega

theorem main {n : ℕ} (A B : Fin n → Finset (Fin 16))
    (hz : ∀ k, ∀ i ∈ A k, ∀ j ∈ B k, Z i j = true)
    (hc : ∀ i j, Z i j = true → ∃ k, i ∈ A k ∧ j ∈ B k) : 13 ≤ n := by
  have r := rowCount Z row7 A B hc
  have c := rowCount (fun j i => Z i j) col7 B A
    (fun j i h => by obtain ⟨k, h1, h2⟩ := hc i j h; exact ⟨k, h2, h1⟩)
  have w : ∀ k ∈ (Finset.univ : Finset (Fin n)), cnt (A k) * cl (cnt (B k)) +
      cnt (B k) * cl (cnt (A k)) + 2 * (cnt (A k) * cnt (B k)) ≤ 24 := by
    intro k _
    have f := few Z row7 row3 (A k) (B k) (hz k)
    have g := few (fun j i => Z i j) col7 col3 (B k) (A k) (fun j hj i hi => hz k i hi j hj)
    exact weight _ _ f.1 f.2 g.1 g.2
  have s := Finset.sum_le_card_nsmul _ _ 24 w
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at s
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at s
  have r1 := r.1
  have r2 := r.2
  have c1 := c.1
  omega

end PEqualNP.Outside.L_meta_9372_aux

theorem PEqualNP.Outside.L_meta_9372 : ¬ (∃ L : List (Finset (Fin 16) × Finset (Fin 16)), L.length ≤ 12 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 16) (j : Fin 16), (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L, len, zero, cover⟩
  have h := PEqualNP.Outside.L_meta_9372_aux.main (n := L.length)
    (fun k => (L.get k).1) (fun k => (L.get k).2)
    (fun k i hi j hj => by
      have := zero (L.get k) (List.get_mem L k) i hi j hj
      simp only [PEqualNP.Outside.L_meta_9372_aux.Z, this, Bool.not_false])
    (fun i j hij => by
      have hf : (([0, 43690, 52428, 26214, 61680, 23130, 15420, 38550, 65280, 21930, 13260, 39270, 4080, 42330, 49980, 27030] : List ℕ).getD i.val 0).testBit j.val = false := by
        simpa only [PEqualNP.Outside.L_meta_9372_aux.Z, Bool.not_eq_true'] using hij
      obtain ⟨r, hr, h1, h2⟩ := cover i j hf
      obtain ⟨k, hk⟩ := List.get_of_mem hr
      exact ⟨k, hk ▸ h1, hk ▸ h2⟩)
  omega
