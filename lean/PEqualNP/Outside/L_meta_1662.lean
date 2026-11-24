import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1662 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ Q ∈ L S, Q ≠ v → Q ∉ L Mp ∧ p ∉ L Mp ∧
      ∀ S2 : Fin N, S2 ≠ S → v ∈ L S2 → s ∉ L S2 → p ∉ L S2 → Q ∉ L S2 ∧ p ∉ L S2) ∧
    (∀ S2 : Fin N, S2 ≠ S → v ∈ L S2 → s ∉ L S2 → p ∉ L S2 → ∀ B : Fin N, (B = s ∨ B = p) → ∀ P ∈ L S2,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ B ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ B ∈ L Mv)))) ∧
    (∀ K : Fin N, v ∉ L K → s ∉ L K → p ∉ L K → ∀ B : Fin N, (B = v ∨ B = s ∨ B = p) →
      ∀ P1 ∈ L K, ∀ P2 ∈ L K, (P1 ∈ L S ∨ B ∈ L S) → (P1 ∈ L Mv ∨ B ∈ L Mv) →
        (P2 ∈ L S ∨ B ∈ L S) → (P2 ∈ L Mv ∨ B ∈ L Mv) → P1 = P2) ∧
    v ∉ L Mv := by
  intro q N L v s p Mv Ms Mp hq hN hcard hint hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have uniq : ∀ i j : Fin N, i ≠ j → ∀ x y : Fin N, x ∈ L i → x ∈ L j → y ∈ L i → y ∈ L j → x = y := by
    intro i j hij x y hxi hxj hyi hyj
    have h := hint i j hij
    exact Finset.card_le_one.mp (le_of_eq h) x (Finset.mem_inter.mpr ⟨hxi, hxj⟩) y
      (Finset.mem_inter.mpr ⟨hyi, hyj⟩)
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hpMp : p ∉ L Mp := fun h => hnc Mp ⟨hvMp, hsMp, h⟩
  refine ⟨?_, ?_, ?_, hvMv⟩
  · intro Q hQ hQv
    refine ⟨?_, hpMp, ?_⟩
    · intro hQMp
      by_cases hSM : S = Mp
      · exact hsS (by rw [hSM]; exact hsMp)
      · exact hQv (uniq S Mp hSM Q v hQ hQMp hvS hvMp)
    · intro S2 hS2 hvS2 hsS2 hpS2
      refine ⟨?_, hpS2⟩
      intro hQS2
      exact hQv (uniq S2 S hS2 Q v hQS2 hQ hvS2 hvS)
  · intro S2 hS2 hvS2 hsS2 hpS2 B hB P hP
    rintro ⟨h1, h2⟩
    have hBS : B ∉ L S := by
      rcases hB with hB | hB
      · rw [hB]; exact hsS
      · rw [hB]; exact hpS
    have hPS : P ∈ L S := by
      rcases h1 with h | ⟨_, _, _, h⟩
      · exact h
      · exact absurd h hBS
    have hPv : P = v := uniq S2 S hS2 P v hP hPS hvS2 hvS
    rcases h2 with h | ⟨h, _⟩
    · exact hvMv (by rw [← hPv]; exact h)
    · exact h hPv
  · intro K hvK hsK hpK B hB P1 hP1 P2 hP2 a1 b1 a2 b2
    rcases hB with hB | hB
    · have hBM : B ∉ L Mv := by rw [hB]; exact hvMv
      have hKM : K ≠ Mv := fun h => hsK (by rw [h]; exact hsMv)
      exact uniq K Mv hKM P1 P2 hP1 (b1.resolve_right hBM) hP2 (b2.resolve_right hBM)
    · have hBS : B ∉ L S := by
        rcases hB with hB | hB
        · rw [hB]; exact hsS
        · rw [hB]; exact hpS
      have hKS : K ≠ S := fun h => hvK (by rw [h]; exact hvS)
      exact uniq K S hKS P1 P2 hP1 (a1.resolve_right hBS) hP2 (a2.resolve_right hBS)
