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
  classical
  intro q N L v s p Mv Ms Mp _ _ _ hmeet hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have two : ∀ (a b : Fin N) (z w : Fin N), a ≠ b → z ∈ L a → z ∈ L b → w ∈ L a → w ∈ L b →
      z = w := by
    intro a b z w hab hza hzb hwa hwb
    exact Finset.card_le_one.1 (hmeet a b hab).le z (Finset.mem_inter.2 ⟨hza, hzb⟩) w
      (Finset.mem_inter.2 ⟨hwa, hwb⟩)
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hpMp : p ∉ L Mp := fun h => hnc Mp ⟨hvMp, hsMp, h⟩
  have hSMp : S ≠ Mp := fun h => hsS (h ▸ hsMp)
  refine ⟨?_, ?_, ?_, hvMv⟩
  · intro Q hQ hQv
    refine ⟨fun hQM => hQv (two S Mp Q v hSMp hQ hQM hvS hvMp), hpMp, ?_⟩
    intro S2 hS2 hvS2 _ hpS2
    exact ⟨fun hQ2 => hQv (two S S2 Q v (Ne.symm hS2) hQ hQ2 hvS hvS2), hpS2⟩
  · intro S2 hS2 hvS2 _ _ B hB P hP
    rintro ⟨h1, h2⟩
    have hBS : B ∉ L S := by
      rcases hB with rfl | rfl
      · exact hsS
      · exact hpS
    have hPv : P = v := by
      rcases h1 with h | ⟨_, _, _, h⟩
      · exact two S S2 P v (Ne.symm hS2) h hP hvS hvS2
      · exact absurd h hBS
    rcases h2 with h | ⟨h, _⟩
    · exact hvMv (hPv ▸ h)
    · exact h hPv
  · intro K hvK hsK _ B hB P1 hP1 P2 hP2 a1 b1 a2 b2
    rcases hB with rfl | hB
    · have hKM : K ≠ Mv := fun h => hsK (h ▸ hsMv)
      have c1 : P1 ∈ L Mv := by
        rcases b1 with h | h
        · exact h
        · exact absurd h hvMv
      have c2 : P2 ∈ L Mv := by
        rcases b2 with h | h
        · exact h
        · exact absurd h hvMv
      exact two K Mv P1 P2 hKM hP1 c1 hP2 c2
    · have hBS : B ∉ L S := by
        rcases hB with rfl | rfl
        · exact hsS
        · exact hpS
      have hKS : K ≠ S := fun h => hvK (h ▸ hvS)
      have c1 : P1 ∈ L S := by
        rcases a1 with h | h
        · exact h
        · exact absurd h hBS
      have c2 : P2 ∈ L S := by
        rcases a2 with h | h
        · exact h
        · exact absurd h hBS
      exact two K S P1 P2 hKS hP1 c1 hP2 c2
