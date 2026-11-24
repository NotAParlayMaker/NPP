import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1663

lemma two_pts {N : ℕ} (L : Fin N → Finset (Fin N))
    (h : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (i j : Fin N) (hij : i ≠ j)
    (a b : Fin N) (ha : a ∈ L i) (ha' : a ∈ L j) (hb : b ∈ L i) (hb' : b ∈ L j) : a = b :=
  Finset.card_le_one.mp (le_of_eq (h i j hij)) a (Finset.mem_inter.mpr ⟨ha, ha'⟩) b
    (Finset.mem_inter.mpr ⟨hb, hb'⟩)

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
  intro q N L v s p Mv Ms Mp _ _ _ hI hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hvs : v ≠ s := by
    rintro rfl
    exact hnc Ms ⟨hvMs, hvMs, hpMs⟩
  have hvp : v ≠ p := by
    rintro rfl
    exact hnc Mp ⟨hvMp, hsMp, hvMp⟩
  have hsp : s ≠ p := by
    rintro rfl
    exact hnc Ms ⟨hvMs, hpMs, hpMs⟩
  have hMsS : Ms ≠ S := by
    rintro rfl
    exact hpS hpMs
  have hMpS : Mp ≠ S := by
    rintro rfl
    exact hsS hsMp
  constructor
  · intro w W hw P hP hAB
    obtain ⟨hA, hB⟩ := hAB
    have hwS : w ∉ L S := by
      rcases hw with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hsS
      · exact hpS
    have hPS : P ∈ L S := by
      rcases hA with h | ⟨_, _, _, h⟩
      · exact h
      · exact absurd h hwS
    have hPv : P = v := by
      rcases hw with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact PEqualNP.Outside.L_meta_1663.two_pts L hI W S hMsS P v hP hPS hvMs hvS
      · exact PEqualNP.Outside.L_meta_1663.two_pts L hI W S hMpS P v hP hPS hvMp hvS
    rcases hB with h | ⟨h, _⟩
    · exact hvMv (hPv ▸ h)
    · exact h hPv
  · intro w S1 hw hwS1 huniq P hP hAB
    obtain ⟨hA, hB⟩ := hAB
    have hvS1 : v ∉ L S1 := by
      intro h
      have := huniq v (Or.inl rfl) h
      rcases hw with rfl | rfl
      · exact hvs this
      · exact hvp this
    have hPS1 : P ∈ L S1 := by
      rcases hB with h | ⟨_, _, _, h⟩
      · exact h
      · exact absurd h hvS1
    have hwMv : w ∈ L Mv := by
      rcases hw with rfl | rfl
      · exact hsMv
      · exact hpMv
    have hne : Mv ≠ S1 := by
      rintro rfl
      rcases hw with rfl | rfl
      · exact hsp (huniq p (Or.inr (Or.inr rfl)) hpMv).symm
      · exact hsp (huniq s (Or.inr (Or.inl rfl)) hsMv)
    have hPw : P = w :=
      PEqualNP.Outside.L_meta_1663.two_pts L hI Mv S1 hne P w hP hPS1 hwMv hwS1
    have hwS : w ∉ L S := by
      rcases hw with rfl | rfl
      · exact hsS
      · exact hpS
    rcases hA with h | ⟨_, h1, h2, _⟩
    · exact hwS (hPw ▸ h)
    · rcases hw with rfl | rfl
      · exact h1 hPw
      · exact h2 hPw
