import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1653 : ∀ (N L k : ℕ) (line : Fin L → Finset (Fin N)) (A : Finset (Fin N)) (B : Fin k → Finset (Fin N)),
  (∀ p r : Fin N, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
  (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
  (∀ i : Fin k, B i ⊆ A ∧ (B i).Nonempty) →
  (¬ ∃ T : Finset (Fin N), T ⊆ A ∧
      (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      ∀ i : Fin k, (T ∩ B i).Nonempty) →
  (∀ i0 : Fin k, ∃ T : Finset (Fin N), T ⊆ A ∧
      (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      ∀ i : Fin k, i ≠ i0 → (T ∩ B i).Nonempty) →
  ∀ i0 : Fin k, ∃ T : Finset (Fin N), T ⊆ A ∧ T.card + 1 ≤ k ∧ Disjoint T (B i0) ∧
      (∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      ∀ u ∈ B i0, ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ u ∈ line j := by
  classical
  intro N L k line A B _ _ hB hno hmin i0
  obtain ⟨T', hT'A, hT'arc, hT'hit⟩ := hmin i0
  have hex : ∀ i : Fin k, ∃ x : Fin N, i ≠ i0 → x ∈ T' ∩ B i := by
    intro i
    by_cases h : i = i0
    · obtain ⟨x, _⟩ := (hB i).2
      exact ⟨x, fun h' => absurd h h'⟩
    · obtain ⟨x, hx⟩ := hT'hit i h
      exact ⟨x, fun _ => hx⟩
  choose g hg using hex
  have hTex : ∃ T : Finset (Fin N), T ⊆ T' ∧ (∀ i : Fin k, i ≠ i0 → g i ∈ T ∩ B i) ∧ T.card + 1 ≤ k := by
    refine ⟨(Finset.univ.erase i0).image g, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_inter.mp (hg i (Finset.ne_of_mem_erase hi))).1
    · intro i hi
      exact Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem g (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩),
        (Finset.mem_inter.mp (hg i hi)).2⟩
    · have h1 : ((Finset.univ.erase i0).image g).card ≤ (Finset.univ.erase i0).card := Finset.card_image_le
      have h2 : (Finset.univ.erase i0).card = (Finset.univ : Finset (Fin k)).card - 1 :=
        Finset.card_erase_of_mem (Finset.mem_univ i0)
      have h3 : (Finset.univ : Finset (Fin k)).card = k := by simp
      have h4 : 0 < k := i0.pos
      omega
  obtain ⟨T, hTsub, hThit, hTcard⟩ := hTex
  have hTA : T ⊆ A := hTsub.trans hT'A
  have hTarc : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c →
      ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j :=
    fun a ha b hb c hc => hT'arc a (hTsub ha) b (hTsub hb) c (hTsub hc)
  have hdisj : Disjoint T (B i0) := by
    rw [Finset.disjoint_left]
    intro x hx hxB
    apply hno
    refine ⟨T, hTA, hTarc, ?_⟩
    intro i
    by_cases h : i = i0
    · subst h
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, hxB⟩⟩
    · exact ⟨g i, hThit i h⟩
  refine ⟨T, hTA, hTcard, hdisj, hTarc, ?_⟩
  intro u hu
  by_contra hcon
  apply hno
  refine ⟨insert u T, Finset.insert_subset_iff.mpr ⟨(hB i0).1 hu, hTA⟩, ?_, ?_⟩
  · intro a ha b hb c hc hab hac hbc hj
    obtain ⟨j, haj, hbj, hcj⟩ := hj
    rcases Finset.mem_insert.mp ha with hau | ha'
    · have hb' : b ∈ T := (Finset.mem_insert.mp hb).resolve_left (fun h => hab (hau.trans h.symm))
      have hc' : c ∈ T := (Finset.mem_insert.mp hc).resolve_left (fun h => hac (hau.trans h.symm))
      exact hcon ⟨b, hb', c, hc', hbc, j, hbj, hcj, hau ▸ haj⟩
    · rcases Finset.mem_insert.mp hb with hbu | hb'
      · have hc' : c ∈ T := (Finset.mem_insert.mp hc).resolve_left (fun h => hbc (hbu.trans h.symm))
        exact hcon ⟨a, ha', c, hc', hac, j, haj, hcj, hbu ▸ hbj⟩
      · rcases Finset.mem_insert.mp hc with hcu | hc'
        · exact hcon ⟨a, ha', b, hb', hab, j, haj, hbj, hcu ▸ hcj⟩
        · exact hTarc a ha' b hb' c hc' hab hac hbc ⟨j, haj, hbj, hcj⟩
  · intro i
    by_cases h : i = i0
    · subst h
      exact ⟨u, Finset.mem_inter.mpr ⟨Finset.mem_insert_self u T, hu⟩⟩
    · exact ⟨g i, Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp (hThit i h)).1,
        (Finset.mem_inter.mp (hThit i h)).2⟩⟩
