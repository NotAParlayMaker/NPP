import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_349 : ∀ (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop), (∀ i : Fin b, ∀ j ∈ PG i, j < i) → (∀ i : Fin b, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) → ∀ (g H : Fin b) (u : Fin n), g ≠ H → u ∈ PV g → u ∉ RV g → (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) → ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → u ∉ I → (∃ w ∈ I, G.Adj u w) → val I H → (∀ v ∈ PV g, v ∉ I) ∧ (∀ j ∈ PG g, ¬ val I j) ∧ H ∉ PG g := by
  classical
  intro n b G PV RV PG RG OV OG val hPG hRG hval hout g H u _ huP huR hu I hI huI hw hIH
  obtain ⟨w, hwI, hadj⟩ := hw
  have hnotP : ¬ ((∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j) := by
    intro hP
    have mono : ∀ (i : Fin b) (S : Finset (Fin n)) (T : Finset (Fin b)),
        (∀ j ∈ T, (val (insert u I) j ↔ val I j)) →
        ((∃ v ∈ S, v ∈ I) ∨ ∃ j ∈ T, val I j) →
        ((∃ v ∈ S, v ∈ insert u I) ∨ ∃ j ∈ T, val (insert u I) j) := by
      intro i S T hT h
      rcases h with ⟨v, hvS, hvI⟩ | ⟨j, hjT, hj⟩
      · exact Or.inl ⟨v, hvS, Finset.mem_insert_of_mem hvI⟩
      · exact Or.inr ⟨j, hjT, (hT j hjT).mpr hj⟩
    have back : ∀ (S : Finset (Fin n)) (T : Finset (Fin b)), u ∉ S →
        (∀ j ∈ T, (val (insert u I) j ↔ val I j)) →
        ((∃ v ∈ S, v ∈ insert u I) ∨ ∃ j ∈ T, val (insert u I) j) →
        ((∃ v ∈ S, v ∈ I) ∨ ∃ j ∈ T, val I j) := by
      intro S T huS hT h
      rcases h with ⟨v, hvS, hvI⟩ | ⟨j, hjT, hj⟩
      · rcases Finset.mem_insert.mp hvI with hvu | hvI'
        · exact absurd (hvu ▸ hvS) huS
        · exact Or.inl ⟨v, hvS, hvI'⟩
      · exact Or.inr ⟨j, hjT, (hT j hjT).mp hj⟩
    have key : ∀ m : ℕ, ∀ i : Fin b, i.val = m → (val (insert u I) i ↔ val I i) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i him
        have IH : ∀ j : Fin b, j < i → (val (insert u I) j ↔ val I j) :=
          fun j hj => ih j.val (by rw [← him]; exact hj) j rfl
        have IHP : ∀ j ∈ PG i, (val (insert u I) j ↔ val I j) := fun j hj => IH j (hPG i j hj)
        have IHR : ∀ j ∈ RG i, (val (insert u I) j ↔ val I j) := fun j hj => IH j (hRG i j hj)
        constructor
        · intro hX
          by_cases hiH : i = H
          · rw [hiH]
            exact hIH
          · have hX' := (hval (insert u I) i).mp hX
            by_cases hig : i = g
            · refine (hval I i).mpr ⟨?_, ?_⟩
              · rw [hig]
                exact hP
              · exact back (RV i) (RG i) (by rw [hig]; exact huR) IHR hX'.2
            · have h1 : u ∉ PV i := fun h => (hu i (Or.inl h)).elim hig hiH
              have h2 : u ∉ RV i := fun h => (hu i (Or.inr h)).elim hig hiH
              exact (hval I i).mpr ⟨back (PV i) (PG i) h1 IHP hX'.1, back (RV i) (RG i) h2 IHR hX'.2⟩
        · intro hIi
          have hI' := (hval I i).mp hIi
          exact (hval (insert u I) i).mpr
            ⟨mono i (PV i) (PG i) IHP hI'.1, mono i (RV i) (RG i) IHR hI'.2⟩
    have hedge : (∃ v ∈ OV, v ∈ insert u I) ∨ ∃ j ∈ OG, val (insert u I) j :=
      (hout (insert u I)).mpr
        ⟨u, Finset.mem_insert_self u I, w, Finset.mem_insert_of_mem hwI, hadj⟩
    have hno : ¬ ((∃ v ∈ OV, v ∈ I) ∨ ∃ j ∈ OG, val I j) := by
      intro h
      obtain ⟨a, haI, c, hcI, hac⟩ := (hout I).mp h
      exact hI a haI c hcI hac
    rcases hedge with ⟨v, hvO, hvX⟩ | ⟨j, hjO, hj⟩
    · rcases Finset.mem_insert.mp hvX with hvu | hvI
      · obtain ⟨a, ha, c, hc, hac⟩ := (hout {u}).mp
          (Or.inl ⟨u, hvu ▸ hvO, Finset.mem_singleton_self u⟩)
        rw [Finset.mem_singleton] at ha hc
        rw [ha, hc] at hac
        exact G.ne_of_adj hac rfl
      · exact hno (Or.inl ⟨v, hvO, hvI⟩)
    · exact hno (Or.inr ⟨j, hjO, (key j.val j rfl).mp hj⟩)
  exact ⟨fun v hv hvI => hnotP (Or.inl ⟨v, hv, hvI⟩),
    fun j hj hvj => hnotP (Or.inr ⟨j, hj, hvj⟩),
    fun hH => hnotP (Or.inr ⟨H, hH, hIH⟩)⟩
