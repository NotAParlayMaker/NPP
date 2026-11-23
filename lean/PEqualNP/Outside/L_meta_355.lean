import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private theorem fin2_other (a b c : Fin 2) (hab : a ≠ b) (hca : c ≠ a) : c = b := by
  revert a b c; decide

theorem L_meta_355 : ∀ E : List (Fin 4 × Fin 4), E = [(0, 1), (1, 2), (2, 3)] → ∀ (PV RV : Fin 2 → Finset (Fin 4)) (PG RG : Fin 2 → Finset (Fin 2)) (OV : Finset (Fin 4)) (OG : Finset (Fin 2)) (val : Finset (Fin 4) → Fin 2 → Prop), (∀ i : Fin 2, ∀ j ∈ PG i, j < i) → (∀ i : Fin 2, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin 4)) (i : Fin 2), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin 4), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ e ∈ E, e.1 ∈ X ∧ e.2 ∈ X) → ∀ (g H : Fin 2) (u : Fin 4), g ≠ H → u ∈ PV g → u ∉ RV g → (∀ i : Fin 2, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) → ∀ I : Finset (Fin 4), (∀ e ∈ E, ¬ (e.1 ∈ I ∧ e.2 ∈ I)) → u ∉ I → (∃ w ∈ I, (u, w) ∈ E ∨ (w, u) ∈ E) → val I H → (∀ v ∈ PV g, v ∉ I) ∧ (∀ j ∈ PG g, ¬ val I j) ∧ H ∉ PG g := by
  intro E hE PV RV PG RG OV OG val _ hRG hval hout g H u hgH _ hu' _ I hI huI hwI hH
  subst hE
  obtain ⟨w, hw, hwE⟩ := hwI
  have hqI : ¬ ∃ e ∈ [((0 : Fin 4), (1 : Fin 4)), (1, 2), (2, 3)], e.1 ∈ I ∧ e.2 ∈ I := by
    rintro ⟨e, he, h1, h2⟩
    exact hI e he ⟨h1, h2⟩
  have houtI := mt (hout I).1 hqI
  have hHOG : H ∉ OG := fun h => houtI (Or.inr ⟨H, h, hH⟩)
  have hqX : ∃ e ∈ [((0 : Fin 4), (1 : Fin 4)), (1, 2), (2, 3)],
      e.1 ∈ insert u I ∧ e.2 ∈ insert u I := by
    rcases hwE with hwE | hwE
    · exact ⟨(u, w), hwE, Finset.mem_insert_self u I, Finset.mem_insert_of_mem hw⟩
    · exact ⟨(w, u), hwE, Finset.mem_insert_of_mem hw, Finset.mem_insert_self u I⟩
  have hOV : ∀ v ∈ OV, False := by
    intro v hv
    obtain ⟨e, he, h1, h2⟩ := (hout {v}).1 (Or.inl ⟨v, hv, Finset.mem_singleton_self v⟩)
    rw [Finset.mem_singleton] at h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact absurd (h1.trans h2.symm) (by decide)
  have hgX : val (insert u I) g ∧ g ∈ OG := by
    rcases (hout (insert u I)).2 hqX with ⟨v, hv, _⟩ | ⟨j, hj, hvj⟩
    · exact (hOV v hv).elim
    · by_cases hjg : j = g
      · subst hjg
        exact ⟨hvj, hj⟩
      · have hjH := fin2_other g H j hgH hjg
        subst hjH
        exact (hHOG hj).elim
  have hnotI : ¬ val I g := fun h => houtI (Or.inr ⟨g, hgX.2, h⟩)
  have key : ((∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j) → False := by
    intro hP
    have hRI : ¬ ((∃ v ∈ RV g, v ∈ I) ∨ ∃ j ∈ RG g, val I j) :=
      fun hR => hnotI ((hval I g).2 ⟨hP, hR⟩)
    have hRGe : ∀ j ∈ RG g, False := by
      intro j hj
      have hjH := fin2_other g H j hgH (ne_of_lt (hRG g j hj))
      subst hjH
      exact hRI (Or.inr ⟨j, hj, hH⟩)
    rcases ((hval (insert u I) g).1 hgX.1).2 with ⟨v, hv, hvX⟩ | ⟨j, hj, _⟩
    · rcases Finset.mem_insert.1 hvX with rfl | hvI
      · exact hu' hv
      · exact hRI (Or.inl ⟨v, hv, hvI⟩)
    · exact hRGe j hj
  exact ⟨fun v hv hvI => key (Or.inl ⟨v, hv, hvI⟩), fun j hj hvj => key (Or.inr ⟨j, hj, hvj⟩),
    fun hHP => key (Or.inr ⟨H, hHP, hH⟩)⟩

end PEqualNP.Outside
