import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6750

lemma aux {α : Type} [DecidableEq α] (E : Finset α) (I : Finset ℕ) (f : ℕ → Finset α) :
    ∀ k : ℕ, ∀ T : Finset α, T.card = k → T ⊆ E →
      (E \ T).card ≤ (I.filter (fun i => Disjoint T (f i))).card →
      ∃ T' ⊆ E, (E \ T').card ≤ (I.filter (fun i => Disjoint T' (f i))).card ∧
        ∀ i ∈ I, (T' ∩ f i).card ≠ 1 := by
  intro k
  induction k with
  | zero =>
    intro T hT hTE hle
    refine ⟨T, hTE, hle, fun i _ => ?_⟩
    rw [Finset.card_eq_zero.mp hT]
    simp
  | succ k ih =>
    intro T hT hTE hle
    by_cases hgood : ∀ i ∈ I, (T ∩ f i).card ≠ 1
    · exact ⟨T, hTE, hle, hgood⟩
    · push_neg at hgood
      obtain ⟨i, hi, h1⟩ := hgood
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp h1
      have heT : e ∈ T := (Finset.mem_inter.mp (by rw [he]; simp)).1
      have hef : e ∈ f i := (Finset.mem_inter.mp (by rw [he]; simp)).2
      apply ih (T.erase e) (by rw [Finset.card_erase_of_mem heT, hT]; rfl)
        ((Finset.erase_subset _ _).trans hTE)
      have hnd : ¬ Disjoint T (f i) := by
        rw [Finset.not_disjoint_iff]
        exact ⟨e, heT, hef⟩
      have hd : Disjoint (T.erase e) (f i) := by
        rw [Finset.disjoint_left]
        intro a ha haf
        have : a ∈ T ∩ f i := Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase ha, haf⟩
        rw [he, Finset.mem_singleton] at this
        exact Finset.ne_of_mem_erase ha this
      have hsub : insert i (I.filter (fun j => Disjoint T (f j))) ⊆
          I.filter (fun j => Disjoint (T.erase e) (f j)) := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Finset.mem_filter.mpr ⟨hi, hd⟩
        · rw [Finset.mem_filter] at hj ⊢
          exact ⟨hj.1, hj.2.mono_left (Finset.erase_subset _ _)⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by
        intro h
        exact hnd (Finset.mem_filter.mp h).2)] at hc
      have hE : E \ T.erase e = insert e (E \ T) := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
        constructor
        · rintro ⟨haE, hna⟩
          by_cases hae : a = e
          · exact Or.inl hae
          · exact Or.inr ⟨haE, fun haT => hna ⟨hae, haT⟩⟩
        · rintro (rfl | ⟨haE, hna⟩)
          · exact ⟨hTE heT, fun h => h.1 rfl⟩
          · exact ⟨haE, fun h => hna h.2⟩
      rw [hE]
      have := Finset.card_insert_le e (E \ T)
      omega

end PEqualNP.Outside.L_meta_6750

theorem PEqualNP.Outside.L_meta_6750 : ∀ (x1 : Finset (Sym2 (Fin (11 : ℕ)))) (x2 : Finset ℕ) (x3 : ℕ → Finset (Sym2 (Fin (11 : ℕ)))), ∃ x4 ⊆ x1, (x1 \ x4).card ≤ {x5 ∈ x2 | Disjoint x4 (x3 x5)}.card ∧ ∀ x5 ∈ x2, (x4 ∩ x3 x5).card ≠ (1 : ℕ) := by
  intro E I f
  have h := PEqualNP.Outside.L_meta_6750.aux E I f E.card E rfl (Finset.Subset.refl _) (by simp)
  exact h
