import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1663

theorem inter_uniq {N : ℕ} (L : Fin N → Finset (Fin N))
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (i j : Fin N) (h : i ≠ j) (a b : Fin N)
    (ha : a ∈ L i) (ha' : a ∈ L j) (hb : b ∈ L i) (hb' : b ∈ L j) : a = b :=
  Finset.card_le_one.mp (hI i j h).le a (Finset.mem_inter.mpr ⟨ha, ha'⟩) b (Finset.mem_inter.mpr ⟨hb, hb'⟩)

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
  intro q N L v s p Mv Ms Mp hq hN hc hI hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hsp : s ≠ p := by
    intro h
    apply hnc Ms
    refine ⟨hvMs, ?_, hpMs⟩
    rw [h]
    exact hpMs
  have hSMp : S ≠ Mp := by
    intro h
    rw [h] at hsS
    exact hsS hsMp
  have hSMs : S ≠ Ms := by
    intro h
    rw [h] at hpS
    exact hpS hpMs
  refine ⟨?_, ?_⟩
  · intro w W hw P hP
    rintro ⟨h1, h2⟩
    have hPv : P = v := by
      rcases hw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
      · rw [hw2] at hP
        rw [hw1] at h1
        have c : P ∈ L S := by
          rcases h1 with h1 | ⟨_, _, _, h1⟩
          · exact h1
          · exact absurd h1 hsS
        exact PEqualNP.Outside.L_meta_1663.inter_uniq L hI S Ms hSMs P v c hP hvS hvMs
      · rw [hw2] at hP
        rw [hw1] at h1
        have c : P ∈ L S := by
          rcases h1 with h1 | ⟨_, _, _, h1⟩
          · exact h1
          · exact absurd h1 hpS
        exact PEqualNP.Outside.L_meta_1663.inter_uniq L hI S Mp hSMp P v c hP hvS hvMp
    rcases h2 with h2 | ⟨h2, _⟩
    · rw [hPv] at h2
      exact hvMv h2
    · exact h2 hPv
  · intro w S1 hw hwS1 hu P hP
    rintro ⟨h1, h2⟩
    have hwMv : w ∈ L Mv := by
      rcases hw with h | h
      · rw [h]; exact hsMv
      · rw [h]; exact hpMv
    have hwS : w ∉ L S := by
      rcases hw with h | h
      · rw [h]; exact hsS
      · rw [h]; exact hpS
    have hvS1 : v ∉ L S1 := by
      intro h
      have e : v = w := hu v (Or.inl rfl) h
      rw [e] at hvMv
      exact hvMv hwMv
    have hS1Mv : S1 ≠ Mv := by
      intro h
      rw [h] at hu
      have e1 : s = w := hu s (Or.inr (Or.inl rfl)) hsMv
      have e2 : p = w := hu p (Or.inr (Or.inr rfl)) hpMv
      exact hsp (e1.trans e2.symm)
    have c : P ∈ L S1 := by
      rcases h2 with h2 | ⟨_, _, _, h2⟩
      · exact h2
      · exact absurd h2 hvS1
    have hPw : P = w := PEqualNP.Outside.L_meta_1663.inter_uniq L hI S1 Mv hS1Mv P w c hP hwS1 hwMv
    rcases h1 with h1 | ⟨_, h3, h4, _⟩
    · rw [hPw] at h1
      exact hwS h1
    · rcases hw with h | h
      · exact h3 (hPw.trans h)
      · exact h4 (hPw.trans h)
