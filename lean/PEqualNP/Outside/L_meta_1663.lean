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
  intro q N L v s p Mv Ms Mp _ _ _ hinter hncol hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have hv_nMv : v ∉ L Mv := fun hv => hncol Mv ⟨hv, hsMv, hpMv⟩
  have hs_nMs : s ∉ L Ms := fun hs => hncol Ms ⟨hvMs, hs, hpMs⟩
  have hp_nMp : p ∉ L Mp := fun hp => hncol Mp ⟨hvMp, hsMp, hp⟩
  have hvs : v ≠ s := fun h => hs_nMs (h ▸ hvMs)
  have hvp : v ≠ p := fun h => hp_nMp (h ▸ hvMp)
  have huniq : ∀ i j x y : Fin N, i ≠ j → x ∈ L i → x ∈ L j → y ∈ L i → y ∈ L j → x = y := by
    intro i j x y hij hxi hxj hyi hyj
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hinter i j hij)
    have hxc : x = c := Finset.mem_singleton.mp (hc ▸ Finset.mem_inter.mpr ⟨hxi, hxj⟩)
    have hyc : y = c := Finset.mem_singleton.mp (hc ▸ Finset.mem_inter.mpr ⟨hyi, hyj⟩)
    exact hxc.trans hyc.symm
  constructor
  · intro w W hw P hPW ⟨h1, h2⟩
    have hPS : P ∈ L S := by
      rcases h1 with hPS | ⟨_, _, _, hwS⟩
      · exact hPS
      · rcases hw with ⟨hws, _⟩ | ⟨hwp, _⟩
        · exact absurd (hws ▸ hwS) hsS
        · exact absurd (hwp ▸ hwS) hpS
    have hPv : P = v := by
      rcases hw with ⟨_, hW⟩ | ⟨_, hW⟩
      · have hne : S ≠ Ms := fun h => hpS (h ▸ hpMs)
        exact huniq S Ms P v hne hPS (hW ▸ hPW) hvS hvMs
      · have hne : S ≠ Mp := fun h => hsS (h ▸ hsMp)
        exact huniq S Mp P v hne hPS (hW ▸ hPW) hvS hvMp
    subst hPv
    rcases h2 with hPMv | ⟨hPne, _⟩
    · exact hv_nMv hPMv
    · exact hPne rfl
  · intro w S1 hw hwS1 hall P hPMv ⟨h1, h2⟩
    have hv_nS1 : v ∉ L S1 := by
      intro hvS1
      have hvw := hall v (Or.inl rfl) hvS1
      rcases hw with hws | hwp
      · exact hvs (hvw.trans hws)
      · exact hvp (hvw.trans hwp)
    have hPS1 : P ∈ L S1 := by
      rcases h2 with hPS1 | ⟨_, _, _, hvS1⟩
      · exact hPS1
      · exact absurd hvS1 hv_nS1
    rcases hw with hws | hwp
    · have hp_nS1 : p ∉ L S1 := by
        intro hpS1
        have hps := (hall p (Or.inr (Or.inr rfl)) hpS1).trans hws
        exact hp_nMp (hps.symm ▸ hsMp)
      have hne : S1 ≠ Mv := fun h => hp_nS1 (h ▸ hpMv)
      have hPs : P = s := huniq S1 Mv P s hne hPS1 hPMv (hws ▸ hwS1) hsMv
      subst hPs
      rcases h1 with hPS | ⟨_, hPne, _⟩
      · exact hsS hPS
      · exact hPne rfl
    · have hs_nS1 : s ∉ L S1 := by
        intro hsS1
        have hsp := (hall s (Or.inr (Or.inl rfl)) hsS1).trans hwp
        exact hs_nMs (hsp.symm ▸ hpMs)
      have hne : S1 ≠ Mv := fun h => hs_nS1 (h ▸ hsMv)
      have hPp : P = p := huniq S1 Mv P p hne hPS1 hPMv (hwp ▸ hwS1) hpMv
      subst hPp
      rcases h1 with hPS | ⟨_, _, hPne, _⟩
      · exact hpS hPS
      · exact hPne rfl
