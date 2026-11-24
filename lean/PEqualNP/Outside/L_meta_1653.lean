import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1653

def IsArc {N L : ℕ} (line : Fin L → Finset (Fin N)) (T : Finset (Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a ≠ b → a ≠ c → b ≠ c →
    ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j

lemma arc_mono {N L : ℕ} (line : Fin L → Finset (Fin N)) (T T' : Finset (Fin N))
    (h : T' ⊆ T) (hT : IsArc line T) : IsArc line T' :=
  fun a ha b hb c hc hab hac hbc => hT a (h ha) b (h hb) c (h hc) hab hac hbc

lemma main : ∀ (N L k : ℕ) (line : Fin L → Finset (Fin N)) (A : Finset (Fin N)) (B : Fin k → Finset (Fin N)),
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
  intro N L k line A B _ _ hB hno hmin i0
  classical
  obtain ⟨T0, hT0A, hT0arc, hT0hit⟩ := hmin i0
  let pick : Fin k → Fin N := fun i =>
    if h : i ≠ i0 then (hT0hit i h).choose else (hB i).2.choose
  have hpick : ∀ i, i ≠ i0 → pick i ∈ T0 ∩ B i := by
    intro i hi
    simp only [pick, hi, ne_eq, not_false_eq_true, ↓reduceDIte]
    exact (hT0hit i hi).choose_spec
  let T : Finset (Fin N) := (Finset.univ.filter (fun i : Fin k => i ≠ i0)).image pick
  have hTsub : T ⊆ T0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_inter.mp (hpick i (Finset.mem_filter.mp hi).2)).1
  have hTarc : IsArc line T := arc_mono line T0 T hTsub hT0arc
  have hThit : ∀ i, i ≠ i0 → (T ∩ B i).Nonempty := by
    intro i hi
    refine ⟨pick i, Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp (hpick i hi)).2⟩⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  have hTA : T ⊆ A := hTsub.trans hT0A
  have hcard : T.card + 1 ≤ k := by
    have h1 : T.card ≤ (Finset.univ.filter (fun i : Fin k => i ≠ i0)).card := Finset.card_image_le
    have h2 : (Finset.univ.filter (fun i : Fin k => i ≠ i0)).card = k - 1 := by
      rw [Finset.filter_ne' Finset.univ i0, Finset.card_erase_of_mem (Finset.mem_univ _)]
      simp
    have : 1 ≤ k := by have := i0.isLt; omega
    omega
  have hdisj : Disjoint T (B i0) := by
    rw [Finset.disjoint_left]
    intro x hxT hxB
    apply hno
    refine ⟨T, hTA, hTarc, fun i => ?_⟩
    by_cases hi : i = i0
    · subst hi; exact ⟨x, Finset.mem_inter.mpr ⟨hxT, hxB⟩⟩
    · exact hThit i hi
  refine ⟨T, hTA, hcard, hdisj, hTarc, ?_⟩
  intro u hu
  have huT : u ∉ T := fun h => Finset.disjoint_left.mp hdisj h hu
  by_contra hcon
  push Not at hcon
  apply hno
  refine ⟨insert u T, Finset.insert_subset ((hB i0).1 hu) hTA, ?_, fun i => ?_⟩
  · intro a ha b hb c hc hab hac hbc hcol
    obtain ⟨j, haj, hbj, hcj⟩ := hcol
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · rcases Finset.mem_insert.mp hb with rfl | hb'
      · exact hab rfl
      rcases Finset.mem_insert.mp hc with rfl | hc'
      · exact hac rfl
      exact hcon b hb' c hc' hbc j hbj hcj haj
    rcases Finset.mem_insert.mp hb with rfl | hb'
    · rcases Finset.mem_insert.mp hc with rfl | hc'
      · exact hbc rfl
      exact hcon a ha' c hc' hac j haj hcj hbj
    rcases Finset.mem_insert.mp hc with rfl | hc'
    · exact hcon a ha' b hb' hab j haj hbj hcj
    exact hTarc a ha' b hb' c hc' hab hac hbc ⟨j, haj, hbj, hcj⟩
  · by_cases hi : i = i0
    · subst hi; exact ⟨u, Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hu⟩⟩
    · obtain ⟨x, hx⟩ := hThit i hi
      exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp hx).2⟩⟩

end PEqualNP.Outside.L_meta_1653

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
      ∀ u ∈ B i0, ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ u ∈ line j :=
  PEqualNP.Outside.L_meta_1653.main
