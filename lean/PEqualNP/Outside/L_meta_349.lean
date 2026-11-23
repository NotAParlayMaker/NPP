import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_349

theorem left_false (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop)
    (hP : ∀ i : Fin b, ∀ j ∈ PG i, j < i) (hR : ∀ i : Fin b, ∀ j ∈ RG i, j < i)
    (hv : ∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j)))
    (ho : ∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c)
    (g H : Fin b) (u : Fin n) (hgH : g ≠ H) (hug : u ∉ RV g)
    (hu : ∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H)
    (I : Finset (Fin n)) (hI : ∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) (huw : ∃ w ∈ I, G.Adj u w)
    (hH : val I H)
    (hL : (∃ v ∈ PV g, v ∈ I) ∨ ∃ j ∈ PG g, val I j) : False := by
  have hmem : ∀ v, v ∈ insert u I ↔ v = u ∨ v ∈ I := fun v => Finset.mem_insert
  have key : ∀ i : Fin b, (val (insert u I) i ↔ val I i) := by
    intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have gP : (∃ j ∈ PG i, val (insert u I) j) ↔ ∃ j ∈ PG i, val I j := by
        constructor
        · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (ih j (hP i j hj)).1 h⟩
        · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (ih j (hP i j hj)).2 h⟩
      have gR : (∃ j ∈ RG i, val (insert u I) j) ↔ ∃ j ∈ RG i, val I j := by
        constructor
        · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (ih j (hR i j hj)).1 h⟩
        · rintro ⟨j, hj, h⟩; exact ⟨j, hj, (ih j (hR i j hj)).2 h⟩
      have mono : ∀ S : Finset (Fin n), (∃ v ∈ S, v ∈ I) → ∃ v ∈ S, v ∈ insert u I := by
        rintro S ⟨v, hv1, hv2⟩; exact ⟨v, hv1, Finset.mem_insert_of_mem hv2⟩
      rw [hv (insert u I) i, hv I i, gP, gR]
      by_cases hig : i = g
      · subst hig
        have eR : (∃ v ∈ RV i, v ∈ insert u I) ↔ ∃ v ∈ RV i, v ∈ I := by
          constructor
          · rintro ⟨v, h1, h2⟩
            rcases (hmem v).1 h2 with h | h
            · subst h; exact absurd h1 hug
            · exact ⟨v, h1, h⟩
          · exact mono _
        rw [eR]
        constructor
        · rintro ⟨_, h⟩; exact ⟨hL, h⟩
        · rintro ⟨h1, h⟩; exact ⟨h1.elim (fun h => Or.inl (mono _ h)) Or.inr, h⟩
      · by_cases hiH : i = H
        · subst hiH
          have := (hv I i).1 hH
          constructor
          · intro _; exact this
          · rintro ⟨h1, h2⟩
            exact ⟨h1.elim (fun h => Or.inl (mono _ h)) Or.inr, h2.elim (fun h => Or.inl (mono _ h)) Or.inr⟩
        · have nP : u ∉ PV i := fun h => (hu i (Or.inl h)).elim hig hiH
          have nR : u ∉ RV i := fun h => (hu i (Or.inr h)).elim hig hiH
          have e : ∀ S : Finset (Fin n), u ∉ S → ((∃ v ∈ S, v ∈ insert u I) ↔ ∃ v ∈ S, v ∈ I) := by
            intro S hS
            constructor
            · rintro ⟨v, h1, h2⟩
              rcases (hmem v).1 h2 with h | h
              · subst h; exact absurd h1 hS
              · exact ⟨v, h1, h⟩
            · exact mono _
          rw [e _ nP, e _ nR]
  obtain ⟨w, hw, huw⟩ := huw
  have hX := (ho (insert u I)).2 ⟨u, Finset.mem_insert_self u I, w, Finset.mem_insert_of_mem hw, huw⟩
  have notI : ¬ ((∃ v ∈ OV, v ∈ I) ∨ ∃ j ∈ OG, val I j) := by
    intro h
    obtain ⟨a, ha, c, hc, hac⟩ := (ho I).1 h
    exact hI a ha c hc hac
  rcases hX with ⟨v, hv1, hv2⟩ | ⟨j, hj, h⟩
  · rcases (hmem v).1 hv2 with h | h
    · subst h
      obtain ⟨a, ha, c, hc, hac⟩ := (ho {v}).1 (Or.inl ⟨v, hv1, Finset.mem_singleton_self v⟩)
      rw [Finset.mem_singleton] at ha hc
      subst ha; subst hc
      exact G.irrefl hac
    · exact notI (Or.inl ⟨v, hv1, h⟩)
  · exact notI (Or.inr ⟨j, hj, (key j).1 h⟩)

end PEqualNP.Outside.L_meta_349

theorem PEqualNP.Outside.L_meta_349 : ∀ (n b : ℕ) (G : SimpleGraph (Fin n)) (PV RV : Fin b → Finset (Fin n)) (PG RG : Fin b → Finset (Fin b)) (OV : Finset (Fin n)) (OG : Finset (Fin b)) (val : Finset (Fin n) → Fin b → Prop), (∀ i : Fin b, ∀ j ∈ PG i, j < i) → (∀ i : Fin b, ∀ j ∈ RG i, j < i) → (∀ (X : Finset (Fin n)) (i : Fin b), val X i ↔ (((∃ v ∈ PV i, v ∈ X) ∨ ∃ j ∈ PG i, val X j) ∧ ((∃ v ∈ RV i, v ∈ X) ∨ ∃ j ∈ RG i, val X j))) → (∀ X : Finset (Fin n), ((∃ v ∈ OV, v ∈ X) ∨ ∃ j ∈ OG, val X j) ↔ ∃ a ∈ X, ∃ c ∈ X, G.Adj a c) → ∀ (g H : Fin b) (u : Fin n), g ≠ H → u ∈ PV g → u ∉ RV g → (∀ i : Fin b, (u ∈ PV i ∨ u ∈ RV i) → i = g ∨ i = H) → ∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → u ∉ I → (∃ w ∈ I, G.Adj u w) → val I H → (∀ v ∈ PV g, v ∉ I) ∧ (∀ j ∈ PG g, ¬ val I j) ∧ H ∉ PG g := by
  intro n b G PV RV PG RG OV OG val hP hR hv ho g H u hgH _ hug hu I hI _ huw hH
  have L := PEqualNP.Outside.L_meta_349.left_false n b G PV RV PG RG OV OG val hP hR hv ho g H u hgH hug hu I hI huw hH
  refine ⟨fun v hv1 hv2 => L (Or.inl ⟨v, hv1, hv2⟩), fun j hj h => L (Or.inr ⟨j, hj, h⟩), fun h => L (Or.inr ⟨H, h, hH⟩)⟩
