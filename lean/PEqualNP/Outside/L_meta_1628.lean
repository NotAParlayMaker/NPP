import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1628

/-- One greedy step: an arc off the line `l` gains a point of `W`. -/
theorem ext (q N : ℕ) (L : Fin N → Finset (Fin N)) (l : Fin N) (T W : Finset (Fin N))
    (hcard : ∀ i : Fin N, (L i).card = q + 1)
    (hmeet : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hline : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! k : Fin N, p1 ∈ L k ∧ p2 ∈ L k)
    (hT : ∀ t ∈ T, t ∉ L l) (harc : ∀ i : Fin N, (T ∩ L i).card ≤ 2)
    (hW : ∀ w ∈ W, w ∉ L l) (hbig : T.card * (T.card - 1) * q < 2 * W.card) :
    ∃ u ∈ W, ∀ i : Fin N, (insert u T ∩ L i).card ≤ 2 := by
  classical
  let Bad : Finset (Fin N) := W.filter fun w => ∃ i, w ∈ L i ∧ 2 ≤ (T ∩ L i).card
  let S : Finset (Fin N) → Finset (Fin N) := fun t =>
    Finset.univ.filter fun x => x ∉ L l ∧ ∃ i, t ⊆ L i ∧ x ∈ L i
  have hsub : Bad ⊆ (T.powersetCard 2).biUnion S := by
    intro w hw
    simp only [Bad, Finset.mem_filter] at hw
    obtain ⟨hwW, i, hwi, h2⟩ := hw
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
    rw [Finset.mem_inter] at ha hb
    simp only [Finset.mem_biUnion, Finset.mem_powersetCard]
    refine ⟨{a, b}, ⟨?_, Finset.card_pair hab⟩, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha.1
      · exact hb.1
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hW w hwW, i, ?_, hwi⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha.2
      · exact hb.2
  have hS : ∀ t ∈ T.powersetCard 2, (S t).card ≤ q := by
    intro t ht
    obtain ⟨htT, htc⟩ := Finset.mem_powersetCard.1 ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 htc
    obtain ⟨k, ⟨hak, hbk⟩, huniq⟩ := hline a b hab
    have haT : a ∈ T := htT (by simp)
    have hkl : k ≠ l := fun h => hT a haT (h ▸ hak)
    have h1 : S {a, b} ⊆ L k \ L l := by
      intro x hx
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨hxl, i, hti, hxi⟩ := hx
      have hik : i = k := huniq i ⟨hti (by simp), hti (by simp)⟩
      rw [Finset.mem_sdiff]
      exact ⟨hik ▸ hxi, hxl⟩
    have h2 := Finset.card_sdiff_add_card_inter (L k) (L l)
    rw [hcard, hmeet k l hkl] at h2
    have := Finset.card_le_card h1
    omega
  have hBad : Bad.card ≤ (T.card.choose 2) * q := by
    calc Bad.card ≤ ((T.powersetCard 2).biUnion S).card := Finset.card_le_card hsub
      _ ≤ ∑ t ∈ T.powersetCard 2, (S t).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ T.powersetCard 2, q := Finset.sum_le_sum hS
      _ = (T.card.choose 2) * q := by simp [Finset.card_powersetCard]
  have hch : 2 * (T.card.choose 2) ≤ T.card * (T.card - 1) := by
    rw [Nat.choose_two_right, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have hlt : Bad.card < W.card := by
    have : 2 * Bad.card ≤ T.card * (T.card - 1) * q := by
      calc 2 * Bad.card ≤ 2 * ((T.card.choose 2) * q) := Nat.mul_le_mul_left 2 hBad
        _ = (2 * (T.card.choose 2)) * q := by ring
        _ ≤ T.card * (T.card - 1) * q := Nat.mul_le_mul_right q hch
    omega
  obtain ⟨u, huW, huB⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨u, huW, fun i => ?_⟩
  by_cases hui : u ∈ L i
  · have h1 : (T ∩ L i).card ≤ 1 := by
      by_contra hcon
      apply huB
      simp only [Bad, Finset.mem_filter]
      exact ⟨huW, i, hui, by omega⟩
    have hsub2 : insert u T ∩ L i ⊆ insert u (T ∩ L i) := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_insert] at hx
      rw [Finset.mem_insert, Finset.mem_inter]
      rcases hx.1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx.2⟩
    have := (Finset.card_le_card hsub2).trans (Finset.card_insert_le u (T ∩ L i))
    omega
  · have hsub2 : insert u T ∩ L i ⊆ T ∩ L i := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_insert] at hx
      rw [Finset.mem_inter]
      rcases hx.1 with h | h
      · exact absurd (h ▸ hx.2) hui
      · exact ⟨h, hx.2⟩
    exact (Finset.card_le_card hsub2).trans (harc i)

end PEqualNP.Outside.L_meta_1628

theorem PEqualNP.Outside.L_meta_1628 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (l : Fin N) (T Y Z : Finset (Fin N)), 2 ≤ q → N = q * q + q + 1 → (∀ i0 : Fin N, (L i0).card = q + 1) → (∀ i1 j1 : Fin N, i1 ≠ j1 → (L i1 ∩ L j1).card = 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! k1 : Fin N, p1 ∈ L k1 ∧ p2 ∈ L k1) → (∀ t ∈ T, t ∉ L l) → (∀ i2 : Fin N, (T ∩ L i2).card ≤ 2) → (∀ y ∈ Y, y ∉ L l) → (∀ z ∈ Z, z ∉ L l) → (T.card + 1) * T.card * q < 2 * Y.card → (T.card + 1) * T.card * q < 2 * Z.card → ∃ u ∈ Y, ∃ v ∈ Z, ∀ i3 : Fin N, (insert v (insert u T) ∩ L i3).card ≤ 2 := by
  classical
  intro q N L l T Y Z _ _ hcard hmeet hline hT harc hY hZ hbY hbZ
  have hmul : T.card * (T.card - 1) * q ≤ (T.card + 1) * T.card * q := by
    apply Nat.mul_le_mul_right
    calc T.card * (T.card - 1) ≤ T.card * T.card := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ (T.card + 1) * T.card := Nat.mul_le_mul_right _ (Nat.le_succ _)
  obtain ⟨u, hu, harc1⟩ := PEqualNP.Outside.L_meta_1628.ext q N L l T Y hcard hmeet hline hT harc
    hY (by omega)
  have hT1 : ∀ t ∈ insert u T, t ∉ L l := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | h
    · exact hY t hu
    · exact hT t h
  have hc1 : (insert u T).card ≤ T.card + 1 := Finset.card_insert_le u T
  have hmul1 : (insert u T).card * ((insert u T).card - 1) * q ≤ (T.card + 1) * T.card * q := by
    apply Nat.mul_le_mul_right
    exact Nat.mul_le_mul hc1 (by omega)
  obtain ⟨v, hv, harc2⟩ := PEqualNP.Outside.L_meta_1628.ext q N L l (insert u T) Z hcard hmeet
    hline hT1 harc1 hZ (by omega)
  exact ⟨u, hu, v, hv, harc2⟩
