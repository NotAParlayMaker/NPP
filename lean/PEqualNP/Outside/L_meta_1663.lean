import Mathlib
import PEqualNP.Defs

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
  classical
  intro q N L v s p Mv Ms Mp _ _ _ hmeet hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have two : ∀ (a b : Fin N) (z w : Fin N), a ≠ b → z ∈ L a → z ∈ L b → w ∈ L a → w ∈ L b →
      z = w := by
    intro a b z w hab hza hzb hwa hwb
    exact Finset.card_le_one.1 (hmeet a b hab).le z (Finset.mem_inter.2 ⟨hza, hzb⟩) w
      (Finset.mem_inter.2 ⟨hwa, hwb⟩)
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hsp : s ≠ p := fun h => hnc Ms ⟨hvMs, h ▸ hpMs, hpMs⟩
  constructor
  · intro w W hwW P hP
    rintro ⟨h1, h2⟩
    have hwS : w ∉ L S := by
      rcases hwW with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hsS
      · exact hpS
    have hvW : v ∈ L W := by
      rcases hwW with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact hvMs
      · exact hvMp
    have hWS : W ≠ S := by
      rcases hwW with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact fun h => hpS (h ▸ hpMs)
      · exact fun h => hsS (h ▸ hsMp)
    have hPv : P = v := by
      rcases h1 with h | ⟨_, _, _, h⟩
      · exact two W S P v hWS hP h hvW hvS
      · exact absurd h hwS
    rcases h2 with h | ⟨h, _⟩
    · exact hvMv (hPv ▸ h)
    · exact h hPv
  · intro w S1 hw hwS1 honly P hP
    rintro ⟨h1, h2⟩
    have hwMv : w ∈ L Mv := by
      rcases hw with rfl | rfl
      · exact hsMv
      · exact hpMv
    have hwS : w ∉ L S := by
      rcases hw with rfl | rfl
      · exact hsS
      · exact hpS
    have hvS1 : v ∉ L S1 := by
      intro h
      have := honly v (Or.inl rfl) h
      exact hwS (this ▸ hvS)
    have hMS1 : Mv ≠ S1 := by
      intro h
      rcases hw with rfl | rfl
      · exact hsp (honly p (Or.inr (Or.inr rfl)) (h ▸ hpMv)).symm
      · exact hsp (honly s (Or.inr (Or.inl rfl)) (h ▸ hsMv))
    have hPw : P = w := by
      rcases h2 with h | ⟨_, _, _, h⟩
      · exact two Mv S1 P w hMS1 hP h hwMv hwS1
      · exact absurd h hvS1
    rcases h1 with h | ⟨_, h2', h3', _⟩
    · exact hwS (hPw ▸ h)
    · rcases hw with rfl | rfl
      · exact h2' hPw
      · exact h3' hPw
