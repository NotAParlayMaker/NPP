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
  obtain ⟨T0, hT0A, hT0arc, hT0hit⟩ := hmin i0
  -- one point of T0 in each B i, i other than i0
  have hch : ∀ i : Fin k, ∃ t : Fin N, i ≠ i0 → t ∈ T0 ∩ B i := by
    intro i
    by_cases h : i = i0
    · exact ⟨(hB i).2.choose, fun h' => absurd h h'⟩
    · obtain ⟨t, ht⟩ := hT0hit i h
      exact ⟨t, fun _ => ht⟩
  choose f hf using hch
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (Fin N), T = (Finset.univ.erase i0).image f := ⟨_, rfl⟩
  have hTsub : T ⊆ T0 := by
    intro t ht
    rw [hTdef] at ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_inter.mp (hf i (Finset.ne_of_mem_erase hi))).1
  have hTarc : ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c →
      ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j :=
    fun a ha b hb c hc => hT0arc a (hTsub ha) b (hTsub hb) c (hTsub hc)
  have hThit : ∀ i : Fin k, i ≠ i0 → (T ∩ B i).Nonempty := by
    intro i hi
    refine ⟨f i, Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp (hf i hi)).2⟩⟩
    rw [hTdef]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩, rfl⟩
  have hTcard : T.card + 1 ≤ k := by
    have h1 : T.card ≤ (Finset.univ.erase i0 : Finset (Fin k)).card := by
      rw [hTdef]
      exact Finset.card_image_le
    have h2 : (Finset.univ.erase i0 : Finset (Fin k)).card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have h3 : 0 < k := Fin.pos i0
    omega
  have hdisj : Disjoint T (B i0) := by
    rw [Finset.disjoint_left]
    intro t ht htB
    apply hno
    refine ⟨T, hTsub.trans hT0A, hTarc, ?_⟩
    intro i
    by_cases h : i = i0
    · rw [h]
      exact ⟨t, Finset.mem_inter.mpr ⟨ht, htB⟩⟩
    · exact hThit i h
  refine ⟨T, hTsub.trans hT0A, hTcard, hdisj, hTarc, ?_⟩
  intro u hu
  by_contra hcon
  apply hno
  refine ⟨insert u T, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with hxu | hx
    · rw [hxu]
      exact (hB i0).1 hu
    · exact hT0A (hTsub hx)
  · intro a ha b hb c hc hab hac hbc hj
    obtain ⟨j, haj, hbj, hcj⟩ := hj
    rcases Finset.mem_insert.mp ha with hau | ha
    · have hb' : b ∈ T := (Finset.mem_insert.mp hb).resolve_left (fun h => hab (hau.trans h.symm))
      have hc' : c ∈ T := (Finset.mem_insert.mp hc).resolve_left (fun h => hac (hau.trans h.symm))
      rw [hau] at haj
      exact hcon ⟨b, hb', c, hc', hbc, j, hbj, hcj, haj⟩
    · rcases Finset.mem_insert.mp hb with hbu | hb
      · have hc' : c ∈ T := (Finset.mem_insert.mp hc).resolve_left (fun h => hbc (hbu.trans h.symm))
        rw [hbu] at hbj
        exact hcon ⟨a, ha, c, hc', hac, j, haj, hcj, hbj⟩
      · rcases Finset.mem_insert.mp hc with hcu | hc
        · rw [hcu] at hcj
          exact hcon ⟨a, ha, b, hb, hab, j, haj, hbj, hcj⟩
        · exact hTarc a ha b hb c hc hab hac hbc ⟨j, haj, hbj, hcj⟩
  · intro i
    by_cases h : i = i0
    · rw [h]
      exact ⟨u, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hu⟩⟩
    · obtain ⟨t, ht⟩ := hThit i h
      exact ⟨t, Finset.mem_inter.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp ht).1, (Finset.mem_inter.mp ht).2⟩⟩
