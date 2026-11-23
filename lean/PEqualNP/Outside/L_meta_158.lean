import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_158 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (mk : Fin n → Fin n → Prop) [DecidableRel mk],
    (∀ u v : Fin n, G.Adj u v → mk u v ∨ mk v u) →
    ∃ T : Finset (Fin n), (∀ u w : Fin n, G.Adj u w → u ∈ T ∨ w ∈ T) ∧
      T.card ≤
        (G.edgeFinset.filter (fun e => ∀ a b : Fin n, e = s(a, b) → mk a b ∧ mk b a)).card +
        (Finset.univ.filter (fun u => ∃ v : Fin n, G.Adj u v ∧ ¬ mk u v)).card := by
  intro n G _ mk _ _
  let both := G.edgeFinset.filter (fun e => ∀ a b : Fin n, e = s(a, b) → mk a b ∧ mk b a)
  let missed := Finset.univ.filter (fun u => ∃ v : Fin n, G.Adj u v ∧ ¬ mk u v)
  let pick := fun e : Sym2 (Fin n) => e.out.1
  refine ⟨both.image pick ∪ missed, ?_, ?_⟩
  · intro u w huw
    by_cases hu : mk u w
    · by_cases hw : mk w u
      · have he : s(u, w) ∈ both := by
          refine Finset.mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huw, ?_⟩
          intro a b hab
          rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hu, hw⟩
          · exact ⟨hw, hu⟩
        have hp : pick s(u, w) ∈ both.image pick ∪ missed :=
          Finset.mem_union_left _ (Finset.mem_image_of_mem pick he)
        rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(u, w)) with h | h
        · exact Or.inl (h ▸ hp)
        · exact Or.inr (h ▸ hp)
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, u, huw.symm, hw⟩))
    · exact Or.inl (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, w, huw, hu⟩))
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right Finset.card_image_le _)
