import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1628

open Finset

-- One greedy step. Let every line meet A in at most two points. A point that cannot be added
-- to A lies outside A on a line meeting A in two points. Two lines share one point, so such a
-- line is fixed by the two points of A on it: there are at most choose |A| 2 of them, each with
-- q - 1 points outside A. A set W with more points than that has a point keeping A an arc.
theorem extend {N q : ℕ} (L : Fin N → Finset (Fin N))
    (hcard : ∀ i, (L i).card = q + 1)
    (hmeet : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (A W : Finset (Fin N)) (hA : ∀ i, (A ∩ L i).card ≤ 2)
    (hW : A.card.choose 2 * (q - 1) < W.card) :
    ∃ w ∈ W, ∀ i, (insert w A ∩ L i).card ≤ 2 := by
  by_contra hcon
  push Not at hcon
  set S : Finset (Fin N) := univ.filter (fun i => 2 ≤ (A ∩ L i).card) with hS
  have hsub : W ⊆ S.biUnion (fun i => L i \ A) := by
    intro w hw
    obtain ⟨i, hi⟩ := hcon w hw
    have hwA : w ∉ A := by
      intro h
      rw [insert_eq_of_mem h] at hi
      exact absurd (hA i) (not_le.mpr hi)
    have hwL : w ∈ L i := by
      by_contra h
      rw [insert_inter_of_notMem h] at hi
      exact absurd (hA i) (not_le.mpr hi)
    rw [insert_inter_of_mem hwL, card_insert_of_notMem (fun h => hwA (mem_inter.mp h).1)] at hi
    rw [mem_biUnion]
    refine ⟨i, ?_, mem_sdiff.mpr ⟨hwL, hwA⟩⟩
    rw [hS, mem_filter]
    exact ⟨mem_univ i, by omega⟩
  have hSle : S.card ≤ A.card.choose 2 := by
    rw [← card_powersetCard]
    apply card_le_card_of_injOn (fun i => A ∩ L i)
    · intro i hi
      rw [mem_coe, hS, mem_filter] at hi
      rw [mem_coe, mem_powersetCard]
      exact ⟨inter_subset_left, le_antisymm (hA i) hi.2⟩
    · intro i hi j hj hij
      rw [mem_coe, hS, mem_filter] at hi hj
      have hij' : A ∩ L i = A ∩ L j := hij
      by_contra hne
      have hsub2 : A ∩ L i ⊆ L i ∩ L j := by
        intro x hx
        have hx' : x ∈ A ∩ L j := hij' ▸ hx
        exact mem_inter.mpr ⟨(mem_inter.mp hx).2, (mem_inter.mp hx').2⟩
      have h1 := card_le_card hsub2
      rw [hmeet i j hne] at h1
      omega
  have hpiece : ∀ i ∈ S, (L i \ A).card = q - 1 := by
    intro i hi
    rw [hS, mem_filter] at hi
    have h2 : (L i ∩ A).card = 2 := by
      rw [inter_comm]
      exact le_antisymm (hA i) hi.2
    have h3 := card_sdiff_add_card_inter (L i) A
    rw [h2, hcard i] at h3
    omega
  have hB : W.card ≤ S.card * (q - 1) := by
    calc W.card ≤ (S.biUnion (fun i => L i \ A)).card := card_le_card hsub
      _ ≤ ∑ i ∈ S, (L i \ A).card := card_biUnion_le
      _ = ∑ i ∈ S, (q - 1) := sum_congr rfl hpiece
      _ = S.card * (q - 1) := by rw [sum_const, smul_eq_mul]
  have h4 := Nat.mul_le_mul_right (q - 1) hSle
  exact lt_irrefl _ ((hB.trans h4).trans_lt hW)

-- The counting bound used at both steps.
theorem arith (a k q : ℕ) (ha : a ≤ k + 1) : a.choose 2 * (q - 1) * 2 ≤ (k + 1) * k * q := by
  have h1 : a.choose 2 * 2 ≤ a * (a - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_le_self _ _
  have h2 : a * (a - 1) ≤ (k + 1) * k := Nat.mul_le_mul ha (by omega)
  calc a.choose 2 * (q - 1) * 2 = a.choose 2 * 2 * (q - 1) := by ring
    _ ≤ (k + 1) * k * (q - 1) := Nat.mul_le_mul_right _ (h1.trans h2)
    _ ≤ (k + 1) * k * q := Nat.mul_le_mul_left _ (Nat.sub_le q 1)

end PEqualNP.Outside.L_meta_1628

theorem PEqualNP.Outside.L_meta_1628 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (l : Fin N) (T Y Z : Finset (Fin N)), 2 ≤ q → N = q * q + q + 1 → (∀ i0 : Fin N, (L i0).card = q + 1) → (∀ i1 j1 : Fin N, i1 ≠ j1 → (L i1 ∩ L j1).card = 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! k1 : Fin N, p1 ∈ L k1 ∧ p2 ∈ L k1) → (∀ t ∈ T, t ∉ L l) → (∀ i2 : Fin N, (T ∩ L i2).card ≤ 2) → (∀ y ∈ Y, y ∉ L l) → (∀ z ∈ Z, z ∉ L l) → (T.card + 1) * T.card * q < 2 * Y.card → (T.card + 1) * T.card * q < 2 * Z.card → ∃ u ∈ Y, ∃ v ∈ Z, ∀ i3 : Fin N, (insert v (insert u T) ∩ L i3).card ≤ 2 := by
  intro q N L l T Y Z _ _ hcard hmeet _ _ hT _ _ hY hZ
  have hY' : T.card.choose 2 * (q - 1) < Y.card := by
    have := PEqualNP.Outside.L_meta_1628.arith T.card T.card q (Nat.le_succ _)
    omega
  obtain ⟨u, hu, hTu⟩ := PEqualNP.Outside.L_meta_1628.extend L hcard hmeet T Y hT hY'
  have hZ' : (insert u T).card.choose 2 * (q - 1) < Z.card := by
    have := PEqualNP.Outside.L_meta_1628.arith (insert u T).card T.card q
      (Finset.card_insert_le u T)
    omega
  obtain ⟨v, hv, hTuv⟩ := PEqualNP.Outside.L_meta_1628.extend L hcard hmeet (insert u T) Z hTu hZ'
  exact ⟨u, hu, v, hv, hTuv⟩
