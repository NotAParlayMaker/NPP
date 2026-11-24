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
  intro q N L v s p Mv Ms Mp _ _ _ hint hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have uniq : ∀ i j : Fin N, i ≠ j → ∀ a b : Fin N, a ∈ L i → a ∈ L j → b ∈ L i → b ∈ L j → a = b := by
    intro i j hij a b hai haj hbi hbj
    exact Finset.card_le_one.mp (le_of_eq (hint i j hij)) a (Finset.mem_inter.mpr ⟨hai, haj⟩) b
      (Finset.mem_inter.mpr ⟨hbi, hbj⟩)
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hSMs : S ≠ Ms := by
    intro h
    rw [h] at hpS
    exact hpS hpMs
  have hSMp : S ≠ Mp := by
    intro h
    rw [h] at hsS
    exact hsS hsMp
  have hvs : v ≠ s := by
    intro h
    rw [h] at hvS
    exact hsS hvS
  have hvp : v ≠ p := by
    intro h
    rw [h] at hvS
    exact hpS hvS
  have partA : ∀ w W : Fin N, w ∉ L S → v ∈ L W → S ≠ W → ∀ P ∈ L W,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L Mv))) := by
    intro w W hwS hvW hSW P hPW hc
    obtain ⟨h1, h2⟩ := hc
    have hPS : P ∈ L S := by
      rcases h1 with h | ⟨_, _, _, h⟩
      · exact h
      · exact absurd h hwS
    have hPv : P = v := uniq S W hSW P v hPS hPW hvS hvW
    rcases h2 with h | ⟨h, _⟩
    · rw [hPv] at h
      exact hvMv h
    · exact h hPv
  refine ⟨?_, ?_⟩
  · intro w W hW
    rcases hW with ⟨hw, hW⟩ | ⟨hw, hW⟩
    · rw [hw, hW]
      exact partA s Ms hsS hvMs hSMs
    · rw [hw, hW]
      exact partA p Mp hpS hvMp hSMp
  · intro w S1 hw hwS1 honly P hPMv hc
    obtain ⟨h1, h2⟩ := hc
    have hvw : v ≠ w := by
      rcases hw with h | h
      · rw [h]
        exact hvs
      · rw [h]
        exact hvp
    have hvS1 : v ∉ L S1 := fun h => hvw (honly v (Or.inl rfl) h)
    have hwMv : w ∈ L Mv := by
      rcases hw with h | h
      · rw [h]
        exact hsMv
      · rw [h]
        exact hpMv
    have hwS : w ∉ L S := by
      rcases hw with h | h
      · rw [h]
        exact hsS
      · rw [h]
        exact hpS
    have hS1Mv : S1 ≠ Mv := by
      intro h
      have e1 : s = w := honly s (Or.inr (Or.inl rfl)) (by rw [h]; exact hsMv)
      have e2 : p = w := honly p (Or.inr (Or.inr rfl)) (by rw [h]; exact hpMv)
      have hsp : s = p := e1.trans e2.symm
      have hsMs : s ∈ L Ms := by
        rw [hsp]
        exact hpMs
      exact hnc Ms ⟨hvMs, hsMs, hpMs⟩
    have hPS1 : P ∈ L S1 := by
      rcases h2 with h | ⟨_, _, _, h⟩
      · exact h
      · exact absurd h hvS1
    have hPw : P = w := uniq S1 Mv hS1Mv P w hPS1 hPMv hwS1 hwMv
    rcases h1 with h | ⟨_, hs, hp, _⟩
    · rw [hPw] at h
      exact hwS h
    · rcases hw with h | h
      · exact hs (hPw.trans h)
      · exact hp (hPw.trans h)
