import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1663

theorem two_pts {N : ℕ} (L : Fin N → Finset (Fin N))
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) {i j a b : Fin N} (hij : i ≠ j)
    (ha1 : a ∈ L i) (ha2 : a ∈ L j) (hb1 : b ∈ L i) (hb2 : b ∈ L j) : a = b := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (hI i j hij)
  have h1 : a ∈ L i ∩ L j := Finset.mem_inter.mpr ⟨ha1, ha2⟩
  have h2 : b ∈ L i ∩ L j := Finset.mem_inter.mpr ⟨hb1, hb2⟩
  rw [hx, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

end PEqualNP.Outside.L_meta_1663

theorem PEqualNP.Outside.L_meta_1663 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ w W : Fin N, (w = s ∧ W = Ms ∨ w = p ∧ W = Mp) → ∀ P ∈ L W,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L Mv)))) ∧
    (∀ w S1 : Fin N, (w = s ∨ w = p) → w ∈ L S1 → (∀ u : Fin N, (u = v ∨ u = s ∨ u = p) → u ∈ L S1 → u = w) → ∀ P ∈ L Mv,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S)) ∧ (P ∈ L S1 ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S1)))) := by
  intro q N L v s p Mv Ms Mp _hq _hN _hcard hI hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have hvs : v ≠ s := by
    intro h
    apply hnc Ms
    refine ⟨hvMs, ?_, hpMs⟩
    rw [← h]
    exact hvMs
  have hvp : v ≠ p := by
    intro h
    apply hnc Mp
    refine ⟨hvMp, hsMp, ?_⟩
    rw [← h]
    exact hvMp
  have hsp : s ≠ p := by
    intro h
    apply hnc Mp
    refine ⟨hvMp, hsMp, ?_⟩
    rw [← h]
    exact hsMp
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  refine ⟨?_, ?_⟩
  · intro w W hwW P hP hc
    obtain ⟨h1, h2⟩ := hc
    have hwS : w ∉ L S := by
      rcases hwW with ⟨hw, _⟩ | ⟨hw, _⟩
      · rw [hw]
        exact hsS
      · rw [hw]
        exact hpS
    have hPS : P ∈ L S := by
      rcases h1 with h1 | ⟨_, _, _, h⟩
      · exact h1
      · exact absurd h hwS
    have hvW : v ∈ L W := by
      rcases hwW with ⟨_, hW⟩ | ⟨_, hW⟩
      · rw [hW]
        exact hvMs
      · rw [hW]
        exact hvMp
    have hWS : W ≠ S := by
      intro h
      rcases hwW with ⟨_, hW⟩ | ⟨_, hW⟩
      · apply hpS
        rw [← h, hW]
        exact hpMs
      · apply hsS
        rw [← h, hW]
        exact hsMp
    have hPv : P = v := PEqualNP.Outside.L_meta_1663.two_pts L hI hWS hP hPS hvW hvS
    rw [hPv] at h2
    rcases h2 with h2 | ⟨h, _, _, _⟩
    · exact hvMv h2
    · exact h rfl
  · intro w S1 hw hwS1 hu P hP hc
    obtain ⟨h1, h2⟩ := hc
    have hvS1 : v ∉ L S1 := by
      intro h
      have hvw := hu v (Or.inl rfl) h
      rcases hw with hw | hw
      · exact hvs (hvw.trans hw)
      · exact hvp (hvw.trans hw)
    have hPS1 : P ∈ L S1 := by
      rcases h2 with h2 | ⟨_, _, _, h⟩
      · exact h2
      · exact absurd h hvS1
    have hwMv : w ∈ L Mv := by
      rcases hw with hw | hw
      · rw [hw]
        exact hsMv
      · rw [hw]
        exact hpMv
    have hMvS1 : Mv ≠ S1 := by
      intro h
      rcases hw with hw | hw
      · have hpw := hu p (Or.inr (Or.inr rfl)) (by rw [← h]; exact hpMv)
        exact hsp (hpw.trans hw).symm
      · have hsw := hu s (Or.inr (Or.inl rfl)) (by rw [← h]; exact hsMv)
        exact hsp (hsw.trans hw)
    have hPw : P = w := PEqualNP.Outside.L_meta_1663.two_pts L hI hMvS1 hP hPS1 hwMv hwS1
    rw [hPw] at h1
    rcases h1 with h1 | ⟨_, h1b, h1c, _⟩
    · rcases hw with hw | hw
      · rw [hw] at h1
        exact hsS h1
      · rw [hw] at h1
        exact hpS h1
    · rcases hw with hw | hw
      · exact h1b hw
      · exact h1c hw
