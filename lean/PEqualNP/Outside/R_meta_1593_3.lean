import Mathlib
import PEqualNP.Defs

-- A cut that counts over several vertices at once.
-- First child: some nonempty set Z of cubic vertices can be deleted together at a price of
-- four gates per vertex of Z. Under the formula edges + cover - 1 this holds for every
-- independent set inside a minimum cover, so the prover may choose Z freely.
-- Second child: putting one vertex with at most three neighbours back costs at most four gates.
-- Putting back all of Z but one vertex gives the step for that vertex.
theorem PEqualNP.Outside.R_meta_1593_3
    (hset : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
      (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) →
      (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      ∃ Z : Finset (Fin n), Z.Nonempty ∧ (∀ z ∈ Z, z ∉ A) ∧
        ∀ (f f' : (Fin n → Bool) → Bool),
          (∀ x : Fin n → Bool, f x = true ↔ ((∃ a ∈ A, x a = true) ∨
            ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
          (∀ x : Fin n → Bool, f' x = true ↔ ((∃ a ∈ A, x a = true) ∨
            ∃ i j : Fin n, G.Adj i j ∧ i ∉ Z ∧ j ∉ Z ∧ x i = true ∧ x j = true)) →
          ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s →
            ∃ t : ℕ, t + 4 * Z.card ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n f' t)
    (hadd : ∀ (n : ℕ) (f g : (Fin n → Bool) → Bool) (w : Fin n) (N : Finset (Fin n)) (t : ℕ),
      N.card ≤ 3 →
      (∀ x : Fin n → Bool, g x = true ↔ (f x = true ∨ (x w = true ∧ ∃ u ∈ N, x u = true))) →
      PEqualNP.MetaComplexity.HasCircuitSize n f t →
      PEqualNP.MetaComplexity.HasCircuitSize n g (t + 4)) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) → (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i1 j1 : Fin n, G.Adj i1 j1) → ∃ z : Fin n, z ∉ A ∧ ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) s → ∃ t : ℕ, t + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x' : Fin n → Bool => @decide ((∃ a' ∈ A, x' a' = true) ∨ ∃ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i3 j3 ∧ x' i3 = true ∧ x' j3 = true) (Classical.propDecidable _)) t := by
  classical
  intro n G A hdeg hgirth hA hedge
  obtain ⟨Z, ⟨z, hz⟩, hZA, hZ⟩ := hset n G A hdeg hgirth hA hedge
  refine ⟨z, hZA z hz, ?_⟩
  intro s hs
  obtain ⟨t, hts, hsize⟩ := hZ _
    (fun x : Fin n → Bool =>
      @decide ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ i ∉ Z ∧ j ∉ Z ∧ x i = true ∧ x j = true)
        (Classical.propDecidable _))
    (by intro x; simp only [decide_eq_true_eq])
    (by intro x; simp only [decide_eq_true_eq]) s hs
  have key : ∀ k : ℕ, ∀ Y : Finset (Fin n), Y ⊆ Z → z ∈ Y → Y.card + k = Z.card →
      PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
        @decide ((∃ a ∈ A, x a = true) ∨
          ∃ i j : Fin n, G.Adj i j ∧ i ∉ Y ∧ j ∉ Y ∧ x i = true ∧ x j = true)
          (Classical.propDecidable _)) (t + 4 * k) := by
    intro k
    induction k with
    | zero =>
      intro Y hYZ _ hcard
      have hYeq : Y = Z := Finset.eq_of_subset_of_card_le hYZ (by omega)
      rw [hYeq]
      exact hsize
    | succ k ih =>
      intro Y hYZ hzY hcard
      obtain ⟨w, hwZ, hwY⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card (by omega : Y.card < Z.card)
      have hY' := ih (insert w Y) (Finset.insert_subset hwZ hYZ) (Finset.mem_insert_of_mem hzY)
        (by rw [Finset.card_insert_of_notMem hwY]; omega)
      have hN : (Finset.univ.filter (fun u : Fin n => G.Adj w u ∧ u ∉ Y)).card ≤ 3 := by
        have h3 := hdeg w (hZA w hwZ)
        have hsub : ((Finset.univ.filter (fun u : Fin n => G.Adj w u ∧ u ∉ Y) : Finset (Fin n)) :
            Set (Fin n)) ⊆ G.neighborSet w := by
          intro u hu
          exact (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2.1
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_coe_finset] at hle
        omega
      have h4 := hadd n _
        (fun x : Fin n → Bool =>
          @decide ((∃ a ∈ A, x a = true) ∨
            ∃ i j : Fin n, G.Adj i j ∧ i ∉ Y ∧ j ∉ Y ∧ x i = true ∧ x j = true)
            (Classical.propDecidable _))
        w _ (t + 4 * k) hN
        (by
          intro x
          simp only [decide_eq_true_eq, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
            true_and, not_or]
          constructor
          · rintro (h | ⟨i, j, hij, hi, hj, hxi, hxj⟩)
            · exact Or.inl (Or.inl h)
            · by_cases hiw : i = w
              · subst hiw
                exact Or.inr ⟨hxi, j, ⟨hij, hj⟩, hxj⟩
              · by_cases hjw : j = w
                · subst hjw
                  exact Or.inr ⟨hxj, i, ⟨hij.symm, hi⟩, hxi⟩
                · exact Or.inl (Or.inr ⟨i, j, hij, ⟨hiw, hi⟩, ⟨hjw, hj⟩, hxi, hxj⟩)
          · rintro ((h | ⟨i, j, hij, ⟨_, hi⟩, ⟨_, hj⟩, hxi, hxj⟩) | ⟨hxw, u, ⟨hwu, huY⟩, hxu⟩)
            · exact Or.inl h
            · exact Or.inr ⟨i, j, hij, hi, hj, hxi, hxj⟩
            · exact Or.inr ⟨w, u, hwu, hwY, huY, hxw, hxu⟩)
        hY'
      have harith : t + 4 * (k + 1) = t + 4 * k + 4 := by ring
      rw [harith]
      exact h4
  have hc : 1 ≤ Z.card := Finset.card_pos.mpr ⟨z, hz⟩
  have h1 := key (Z.card - 1) {z} (Finset.singleton_subset_iff.mpr hz)
    (Finset.mem_singleton_self z) (by rw [Finset.card_singleton]; omega)
  refine ⟨t + 4 * (Z.card - 1), by omega, ?_⟩
  have hfun2 : (fun x' : Fin n → Bool =>
      @decide ((∃ a' ∈ A, x' a' = true) ∨
        ∃ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i3 j3 ∧
          x' i3 = true ∧ x' j3 = true) (Classical.propDecidable _)) =
      (fun x : Fin n → Bool =>
        @decide ((∃ a ∈ A, x a = true) ∨
          ∃ i j : Fin n, G.Adj i j ∧ i ∉ ({z} : Finset (Fin n)) ∧ j ∉ ({z} : Finset (Fin n)) ∧
            x i = true ∧ x j = true) (Classical.propDecidable _)) := by
    funext x
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Finset.mem_singleton, SimpleGraph.deleteEdges_adj,
      SimpleGraph.mk'_mem_incidenceSet_iff]
    constructor
    · rintro (h | ⟨i, j, ⟨hij, hn⟩, hxi, hxj⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, j, hij, fun h => hn ⟨hij, Or.inl h.symm⟩,
          fun h => hn ⟨hij, Or.inr h.symm⟩, hxi, hxj⟩
    · rintro (h | ⟨i, j, hij, hi, hj, hxi, hxj⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, j, ⟨hij, fun hh => hh.2.elim (fun h => hi h.symm) (fun h => hj h.symm)⟩,
          hxi, hxj⟩
  rw [hfun2]
  exact h1
