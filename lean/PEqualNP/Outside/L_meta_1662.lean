import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1662

theorem inter_uniq {N : ℕ} (L : Fin N → Finset (Fin N))
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (i j : Fin N) (h : i ≠ j) (a b : Fin N)
    (ha : a ∈ L i) (ha' : a ∈ L j) (hb : b ∈ L i) (hb' : b ∈ L j) : a = b :=
  Finset.card_le_one.mp (hI i j h).le a (Finset.mem_inter.mpr ⟨ha, ha'⟩) b (Finset.mem_inter.mpr ⟨hb, hb'⟩)

end PEqualNP.Outside.L_meta_1662

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
  intro q N L v s p Mv Ms Mp hq hN hc hI hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hpMp : p ∉ L Mp := fun h => hnc Mp ⟨hvMp, hsMp, h⟩
  have hSMp : S ≠ Mp := by
    intro h
    rw [h] at hsS
    exact hsS hsMp
  refine ⟨?_, ?_, ?_, hvMv⟩
  · intro Q hQ hQv
    refine ⟨fun h => hQv ?_, hpMp, ?_⟩
    · exact PEqualNP.Outside.L_meta_1662.inter_uniq L hI S Mp hSMp Q v hQ h hvS hvMp
    · intro S2 hne hv2 hs2 hp2
      refine ⟨fun h => hQv ?_, hp2⟩
      exact PEqualNP.Outside.L_meta_1662.inter_uniq L hI S S2 (Ne.symm hne) Q v hQ h hvS hv2
  · intro S2 hne hv2 hs2 hp2 B hB P hP
    have hBS : B ∉ L S := by
      rcases hB with h | h
      · rw [h]; exact hsS
      · rw [h]; exact hpS
    rintro ⟨h1, h2⟩
    rcases h1 with h1 | ⟨_, _, _, h1⟩
    · have hPv : P = v :=
        PEqualNP.Outside.L_meta_1662.inter_uniq L hI S S2 (Ne.symm hne) P v h1 hP hvS hv2
      rcases h2 with h2 | ⟨h2, _⟩
      · rw [hPv] at h2
        exact hvMv h2
      · exact h2 hPv
    · exact hBS h1
  · intro K hvK hsK hpK B hB P1 hP1 P2 hP2 a1 b1 a2 b2
    have hKS : K ≠ S := by
      intro h
      rw [h] at hvK
      exact hvK hvS
    have hKM : K ≠ Mv := by
      intro h
      rw [h] at hsK
      exact hsK hsMv
    rcases hB with h | h | h
    · rw [h] at b1 b2
      have c1 : P1 ∈ L Mv := b1.resolve_right hvMv
      have c2 : P2 ∈ L Mv := b2.resolve_right hvMv
      exact PEqualNP.Outside.L_meta_1662.inter_uniq L hI K Mv hKM P1 P2 hP1 c1 hP2 c2
    · rw [h] at a1 a2
      have c1 : P1 ∈ L S := a1.resolve_right hsS
      have c2 : P2 ∈ L S := a2.resolve_right hsS
      exact PEqualNP.Outside.L_meta_1662.inter_uniq L hI K S hKS P1 P2 hP1 c1 hP2 c2
    · rw [h] at a1 a2
      have c1 : P1 ∈ L S := a1.resolve_right hpS
      have c2 : P2 ∈ L S := a2.resolve_right hpS
      exact PEqualNP.Outside.L_meta_1662.inter_uniq L hI K S hKS P1 P2 hP1 c1 hP2 c2
