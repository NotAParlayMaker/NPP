import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1628

theorem ext1 (q N : ℕ) (L : Fin N → Finset (Fin N)) (S W : Finset (Fin N)) (m : ℕ)
    (hcard : ∀ i : Fin N, (L i).card = q + 1)
    (hint : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hS : ∀ i : Fin N, (S ∩ L i).card ≤ 2)
    (hm : S.card ≤ m + 1)
    (hW : (m + 1) * m * q < 2 * W.card) :
    ∃ w ∈ W, ∀ i : Fin N, (insert w S ∩ L i).card ≤ 2 := by
  classical
  let sec : Finset (Fin N) := Finset.univ.filter (fun i => (S ∩ L i).card = 2)
  have hsecm : ∀ i : Fin N, i ∈ sec ↔ (S ∩ L i).card = 2 := by
    intro i
    simp [sec]
  let B : Finset (Fin N) := sec.biUnion (fun i => L i \ S)
  have hsecc : sec.card ≤ S.card.choose 2 := by
    rw [← Finset.card_powersetCard 2 S]
    apply Finset.card_le_card_of_injOn (fun i => S ∩ L i)
    · intro i hi
      have hi' : (S ∩ L i).card = 2 := (hsecm i).mp (Finset.mem_coe.mp hi)
      exact Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hi'⟩)
    · intro i hi j hj hij
      by_contra hne
      have h1 := hint i j hne
      have hi' : (S ∩ L i).card = 2 := (hsecm i).mp (Finset.mem_coe.mp hi)
      have hij' : S ∩ L i = S ∩ L j := hij
      have hsub : S ∩ L i ⊆ L i ∩ L j := by
        intro x hx
        have hx2 : x ∈ S ∩ L j := hij' ▸ hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hx2).2⟩
      have h2 := Finset.card_le_card hsub
      omega
  have hBc : B.card ≤ sec.card * q := by
    calc B.card ≤ ∑ i ∈ sec, (L i \ S).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ sec, q := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : (S ∩ L i).card = 2 := (hsecm i).mp hi
          have h1 := Finset.card_sdiff_add_card_inter (L i) S
          have h2 := hcard i
          rw [Finset.inter_comm] at h1
          omega
      _ = sec.card * q := by simp
  have hch : 2 * S.card.choose 2 ≤ (m + 1) * m := by
    have h1 : S.card.choose 2 ≤ (m + 1).choose 2 := Nat.choose_le_choose 2 hm
    have h2 : (m + 1).choose 2 = (m + 1) * m / 2 := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel]
    have h3 : 2 * ((m + 1) * m / 2) ≤ (m + 1) * m := Nat.mul_div_le _ _
    omega
  have hlt : B.card < W.card := by
    have h1 : sec.card * q ≤ S.card.choose 2 * q := Nat.mul_le_mul_right q hsecc
    have h2 : 2 * S.card.choose 2 * q ≤ (m + 1) * m * q := Nat.mul_le_mul_right q hch
    have h3 : 2 * S.card.choose 2 * q = 2 * (S.card.choose 2 * q) := by ring
    omega
  obtain ⟨w, hwW, hwB⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨w, hwW, fun i => ?_⟩
  by_cases hwS : w ∈ S
  · rw [Finset.insert_eq_of_mem hwS]
    exact hS i
  by_cases hwi : w ∈ L i
  · have hne : (S ∩ L i).card ≠ 2 := by
      intro h2
      apply hwB
      exact Finset.mem_biUnion.mpr ⟨i, (hsecm i).mpr h2, Finset.mem_sdiff.mpr ⟨hwi, hwS⟩⟩
    have h1 := hS i
    have h3 : insert w S ∩ L i ⊆ insert w (S ∩ L i) := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert] at hx ⊢
      tauto
    have h4 := Finset.card_le_card h3
    have h5 := Finset.card_insert_le w (S ∩ L i)
    omega
  · rw [Finset.insert_inter_of_notMem hwi]
    exact hS i

end PEqualNP.Outside.L_meta_1628

theorem PEqualNP.Outside.L_meta_1628 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (l : Fin N) (T Y Z : Finset (Fin N)), 2 ≤ q → N = q * q + q + 1 → (∀ i0 : Fin N, (L i0).card = q + 1) → (∀ i1 j1 : Fin N, i1 ≠ j1 → (L i1 ∩ L j1).card = 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! k1 : Fin N, p1 ∈ L k1 ∧ p2 ∈ L k1) → (∀ t ∈ T, t ∉ L l) → (∀ i2 : Fin N, (T ∩ L i2).card ≤ 2) → (∀ y ∈ Y, y ∉ L l) → (∀ z ∈ Z, z ∉ L l) → (T.card + 1) * T.card * q < 2 * Y.card → (T.card + 1) * T.card * q < 2 * Z.card → ∃ u ∈ Y, ∃ v ∈ Z, ∀ i3 : Fin N, (insert v (insert u T) ∩ L i3).card ≤ 2 := by
  intro q N L l T Y Z _ _ hcard hint _ _ hT _ _ hY hZ
  obtain ⟨u, hu, hu2⟩ := PEqualNP.Outside.L_meta_1628.ext1 q N L T Y T.card hcard hint hT
    (Nat.le_succ _) hY
  obtain ⟨v, hv, hv2⟩ := PEqualNP.Outside.L_meta_1628.ext1 q N L (insert u T) Z T.card hcard hint hu2
    (Finset.card_insert_le u T) hZ
  exact ⟨u, hu, v, hv, hv2⟩
