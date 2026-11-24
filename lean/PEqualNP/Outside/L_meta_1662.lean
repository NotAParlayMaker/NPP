import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1662_aux

open Finset

theorem eq_of_both {N : ℕ} {L : Fin N → Finset (Fin N)} {i j : Fin N}
    (hinter : (L i ∩ L j).card = 1)
    {a b : Fin N} (hai : a ∈ L i) (haj : a ∈ L j) (hbi : b ∈ L i) (hbj : b ∈ L j) : b = a := by
  have ha : a ∈ L i ∩ L j := mem_inter.mpr ⟨hai, haj⟩
  have hb : b ∈ L i ∩ L j := mem_inter.mpr ⟨hbi, hbj⟩
  obtain ⟨x, hx⟩ := card_eq_one.mp hinter
  have hax : a = x := by simpa [hx] using ha
  have hbx : b = x := by simpa [hx] using hb
  exact hbx.trans hax.symm

end PEqualNP.Outside.L_meta_1662_aux

open PEqualNP.Outside.L_meta_1662_aux

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
  intro q N L v s p Mv Ms Mp hq hN hcard hinter hnon
    hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have hvMv : v ∉ L Mv := by
    intro hv
    exact hnon Mv ⟨hv, hsMv, hpMv⟩
  have hpMp : p ∉ L Mp := by
    intro hp
    exact hnon Mp ⟨hvMp, hsMp, hp⟩
  have hSMp : S ≠ Mp := by
    intro h
    exact hsS (h ▸ hsMp)
  refine ⟨?_, ?_, ?_, hvMv⟩
  · intro Q hQ hQv
    refine ⟨?_, hpMp, ?_⟩
    · intro hQMp
      exact hQv (eq_of_both (hinter S Mp hSMp) hvS hvMp hQ hQMp)
    · intro S2 hS2 hvS2 hsS2 hpS2
      refine ⟨?_, hpS2⟩
      intro hQS2
      exact hQv (eq_of_both (hinter S S2 hS2.symm) hvS hvS2 hQ hQS2)
  · intro S2 hS2 hvS2 hsS2 hpS2 B hB P hP hboth
    rcases hboth with ⟨hA, hC⟩
    have hPv : P ≠ v → P ∉ L S := by
      intro hPneq hPS
      exact hPneq (eq_of_both (hinter S2 S hS2) hvS2 hvS hP hPS)
    have hPs : P ≠ s := by
      intro h
      exact hsS2 (h ▸ hP)
    have hPp : P ≠ p := by
      intro h
      exact hpS2 (h ▸ hP)
    by_cases hPeq : P = v
    · rcases hC with hPM | hside
      · exact hvMv (hPeq ▸ hPM)
      · exact hside.1 hPeq
    · have hPnotS : P ∉ L S := hPv hPeq
      have hBinS : B ∈ L S := by
        rcases hA with hPS | hside
        · exact (hPnotS hPS).elim
        · exact hside.2.2.2
      rcases hB with rfl | rfl
      · exact hsS hBinS
      · exact hpS hBinS
  · intro K hvK hsK hpK B hB P1 hP1 P2 hP2 hP1S hP1M hP2S hP2M
    rcases hB with rfl | rfl | rfl
    · have h1 : P1 ∈ L Mv := by
        rcases hP1M with h | h
        · exact h
        · exact (hvMv h).elim
      have h2 : P2 ∈ L Mv := by
        rcases hP2M with h | h
        · exact h
        · exact (hvMv h).elim
      have hne : K ≠ Mv := by
        intro h
        exact hsK (h ▸ hsMv)
      exact eq_of_both (hinter K Mv hne) hP2 h2 hP1 h1
    · have h1 : P1 ∈ L S := by
        rcases hP1S with h | h
        · exact h
        · exact (hsS h).elim
      have h2 : P2 ∈ L S := by
        rcases hP2S with h | h
        · exact h
        · exact (hsS h).elim
      have hne : K ≠ S := by
        intro h
        exact hvK (h ▸ hvS)
      exact eq_of_both (hinter S K hne.symm) h2 hP2 h1 hP1
    · have h1 : P1 ∈ L S := by
        rcases hP1S with h | h
        · exact h
        · exact (hpS h).elim
      have h2 : P2 ∈ L S := by
        rcases hP2S with h | h
        · exact h
        · exact (hpS h).elim
      have hne : K ≠ S := by
        intro h
        exact hvK (h ▸ hvS)
      exact eq_of_both (hinter S K hne.symm) h2 hP2 h1 hP1
