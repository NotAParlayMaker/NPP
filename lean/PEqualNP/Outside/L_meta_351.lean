import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_351 : ∀ (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop), (∀ i : Fin b, ∀ j ∈ PG i, j < i) → (∀ i : Fin b, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) → ∀ H : Fin b, (∃ g : Fin b, g ≠ H) → (∀ g : Fin b, g ≠ H → (∃ (u : Fin n) (I : Finset (Fin n)), u ∈ PV g ∧ u ∉ RV g ∧ (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧ (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H) ∧ (∃ (u : Fin n) (I : Finset (Fin n)), u ∈ RV g ∧ u ∉ PV g ∧ (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) ∧ (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ u ∉ I ∧ (∃ w ∈ I, G.Adj u w) ∧ val I H)) → ∀ a c : Fin n, G.Adj a c → ¬ ∀ i : Fin b, i ≠ H → ((a ∉ PV i ∧ c ∉ PV i) ∨ (a ∉ RV i ∧ c ∉ RV i)) := by
  intro n b G PV RV PG RG OV OG val hPG hRG hval hout H hne hlock a c hac hbare
  have hOV : ∀ v ∈ OV, False := by
    intro v hv
    obtain ⟨x, hx, y, hy, hxy⟩ := (hout {v}).1 (Or.inl ⟨v, hv, by simp⟩)
    rw [Finset.mem_singleton] at hx hy
    subst hx
    subst hy
    exact G.loopless.irrefl _ hxy
  have hindep : ∀ I : Finset (Fin n), (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) →
      ∀ j ∈ OG, ¬ val I j := by
    intro I hI j hj hv
    obtain ⟨x, hx, y, hy, hxy⟩ := (hout I).1 (Or.inr ⟨j, hj, hv⟩)
    exact hI x hx y hy hxy
  have hflip : ∀ (u : Fin n) (I : Finset (Fin n)),
      (∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) → (∃ w ∈ I, G.Adj u w) →
      (∀ j : Fin b, val (insert u I) j → val I j) → False := by
    intro u I hI hw hsame
    obtain ⟨w, hwI, huw⟩ := hw
    rcases (hout (insert u I)).2
      ⟨u, Finset.mem_insert_self u I, w, Finset.mem_insert_of_mem hwI, huw⟩ with
      ⟨v, hv, _⟩ | ⟨j, hj, hjv⟩
    · exact hOV v hv
    · exact hindep I hI j hj (hsame j hjv)
  have hPH : ∀ g : Fin b, g ≠ H → H ∉ PG g := by
    intro g hg hmem
    obtain ⟨⟨u, I, _, huR, hu, hI, _, hw, hIH⟩, _⟩ := hlock g hg
    refine hflip u I hI hw ?_
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      intro h
      by_cases hjH : j = H
      · rw [hjH]; exact hIH
      rw [hval] at h ⊢
      refine ⟨?_, ?_⟩
      · by_cases hjg : j = g
        · exact Or.inr ⟨H, by rw [hjg]; exact hmem, hIH⟩
        · rcases h.1 with ⟨v, hv, hvX⟩ | ⟨k, hk, hkX⟩
          · rcases Finset.mem_insert.1 hvX with rfl | hvI
            · rcases hu j (Or.inl hv) with h1 | h1
              · exact absurd h1 hjg
              · exact absurd h1 hjH
            · exact Or.inl ⟨v, hv, hvI⟩
          · exact Or.inr ⟨k, hk, ih k (hPG j k hk) hkX⟩
      · rcases h.2 with ⟨v, hv, hvX⟩ | ⟨k, hk, hkX⟩
        · rcases Finset.mem_insert.1 hvX with rfl | hvI
          · rcases hu j (Or.inr hv) with h1 | h1
            · rw [h1] at hv
              exact absurd hv huR
            · exact absurd h1 hjH
          · exact Or.inl ⟨v, hv, hvI⟩
        · exact Or.inr ⟨k, hk, ih k (hRG j k hk) hkX⟩
  have hRH : ∀ g : Fin b, g ≠ H → H ∉ RG g := by
    intro g hg hmem
    obtain ⟨_, ⟨u, I, _, huP, hu, hI, _, hw, hIH⟩⟩ := hlock g hg
    refine hflip u I hI hw ?_
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      intro h
      by_cases hjH : j = H
      · rw [hjH]; exact hIH
      rw [hval] at h ⊢
      refine ⟨?_, ?_⟩
      · rcases h.1 with ⟨v, hv, hvX⟩ | ⟨k, hk, hkX⟩
        · rcases Finset.mem_insert.1 hvX with rfl | hvI
          · rcases hu j (Or.inl hv) with h1 | h1
            · rw [h1] at hv
              exact absurd hv huP
            · exact absurd h1 hjH
          · exact Or.inl ⟨v, hv, hvI⟩
        · exact Or.inr ⟨k, hk, ih k (hPG j k hk) hkX⟩
      · by_cases hjg : j = g
        · exact Or.inr ⟨H, by rw [hjg]; exact hmem, hIH⟩
        · rcases h.2 with ⟨v, hv, hvX⟩ | ⟨k, hk, hkX⟩
          · rcases Finset.mem_insert.1 hvX with rfl | hvI
            · rcases hu j (Or.inr hv) with h1 | h1
              · exact absurd h1 hjg
              · exact absurd h1 hjH
            · exact Or.inl ⟨v, hv, hvI⟩
          · exact Or.inr ⟨k, hk, ih k (hRG j k hk) hkX⟩
  have hOH : H ∉ OG := by
    intro hmem
    obtain ⟨g, hg⟩ := hne
    obtain ⟨⟨u, I, _, _, _, hI, _, _, hIH⟩, _⟩ := hlock g hg
    exact hindep I hI H hmem hIH
  have hfalse : ∀ i : Fin b, i ≠ H → ¬ val {a, c} i := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro hiH h
      rw [hval] at h
      rcases hbare i hiH with ⟨ha, hc⟩ | ⟨ha, hc⟩
      · rcases h.1 with ⟨v, hv, hvX⟩ | ⟨k, hk, hkX⟩
        · rw [Finset.mem_insert, Finset.mem_singleton] at hvX
          rcases hvX with rfl | rfl
          · exact ha hv
          · exact hc hv
        · exact ih k (hPG i k hk) (fun e => hPH i hiH (e ▸ hk)) hkX
      · rcases h.2 with ⟨v, hv, hvX⟩ | ⟨k, hk, hkX⟩
        · rw [Finset.mem_insert, Finset.mem_singleton] at hvX
          rcases hvX with rfl | rfl
          · exact ha hv
          · exact hc hv
        · exact ih k (hRG i k hk) (fun e => hRH i hiH (e ▸ hk)) hkX
  rcases (hout {a, c}).2 ⟨a, by simp, c, by simp, hac⟩ with ⟨v, hv, _⟩ | ⟨j, hj, hjv⟩
  · exact hOV v hv
  · exact hfalse j (fun e => hOH (e ▸ hj)) hjv
