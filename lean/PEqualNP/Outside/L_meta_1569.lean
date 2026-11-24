import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1569

-- LS and MS are disjoint and neither holds 0
theorem disj : ∀ t : Fin 13, t ∈ ({4, 10, 12} : Finset (Fin 13)) → t ∈ ({1, 5, 11} : Finset (Fin 13)) → False := by decide

theorem ls_ne : (0 : Fin 13) ∉ ({4, 10, 12} : Finset (Fin 13)) := by decide

theorem ms_ne : (0 : Fin 13) ∉ ({1, 5, 11} : Finset (Fin 13)) := by decide

-- a clique without 0 holding an LS-MS pair is exactly that pair
theorem pair_card (S : Finset (Fin 13)) (h0 : (0 : Fin 13) ∉ S)
    (hS : (∀ t ∈ S, ∀ u ∈ S, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))))
    (hp : (∃ l ∈ S, ∃ m ∈ S, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))) :
    S.card = 2 := by
  obtain ⟨l, hl, m, hm, hlL, hmM⟩ := hp
  have hlm : l ≠ m := by
    intro h
    subst h
    exact disj l hlL hmM
  have hl0 : l ≠ 0 := fun h => h0 (h ▸ hl)
  have hm0 : m ≠ 0 := fun h => h0 (h ▸ hm)
  have hsub : S = {l, m} := by
    ext t
    constructor
    · intro ht
      by_contra hne
      have ht0 : t ≠ 0 := fun h => h0 (h ▸ ht)
      have hne1 : t ≠ l := by
        intro h
        exact hne (by rw [h]; exact Finset.mem_insert_self _ _)
      have hne2 : t ≠ m := by
        intro h
        exact hne (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have h1 := hS t ht l hl hne1
      have h2 := hS t ht m hm hne2
      rcases h1 with h1 | h1 | h1
      · rcases h1 with h1 | h1
        · exact ht0 h1
        · exact hl0 h1
      · exact disj l hlL h1.2
      · rcases h2 with h2 | h2 | h2
        · rcases h2 with h2 | h2
          · exact ht0 h2
          · exact hm0 h2
        · exact disj t h2.1 h1.1
        · exact disj m h2.2 hmM
    · intro ht
      rcases Finset.mem_insert.mp ht with h | h
      · rw [h]
        exact hl
      · rw [Finset.mem_singleton.mp h]
        exact hm
  rw [hsub]
  exact Finset.card_pair hlm

-- a clique without 0 and without an LS-MS pair has at most one member
theorem nopair_card (S : Finset (Fin 13)) (h0 : (0 : Fin 13) ∉ S)
    (hS : (∀ t ∈ S, ∀ u ∈ S, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))))
    (hp : ¬ (∃ l ∈ S, ∃ m ∈ S, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))) :
    S.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  have hb0 : b ≠ 0 := fun h => h0 (h ▸ hb)
  rcases hS a ha b hb hne with h | h | h
  · rcases h with h | h
    · exact ha0 h
    · exact hb0 h
  · exact hp ⟨a, ha, b, hb, h.1, h.2⟩
  · exact hp ⟨b, hb, a, ha, h.2, h.1⟩

theorem perSet (S : Finset (Fin 13))
    (hS : (∀ t ∈ S, ∀ u ∈ S, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))))
    [Decidable ((0 : Fin 13) ∈ S ∧ 2 ≤ S.card)]
    [Decidable (∃ l ∈ S, ∃ m ∈ S, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))] :
    S.card - 1 = (if ((0 : Fin 13) ∈ S ∧ 2 ≤ S.card) then 1 else 0) +
      (if (∃ l ∈ S, ∃ m ∈ S, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13))) then 1 else 0) := by
  by_cases h0 : (0 : Fin 13) ∈ S
  · have hc : (S.erase 0).card = S.card - 1 := Finset.card_erase_of_mem h0
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨0, h0⟩
    have hE : (∀ t ∈ S.erase 0, ∀ u ∈ S.erase 0, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) :=
      fun t ht u hu htu => hS t (Finset.mem_of_mem_erase ht) u (Finset.mem_of_mem_erase hu) htu
    have hn0 : (0 : Fin 13) ∉ S.erase 0 := by simp
    by_cases hp : (∃ l ∈ S, ∃ m ∈ S, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))
    · have hp' : (∃ l ∈ S.erase 0, ∃ m ∈ S.erase 0, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13))) := by
        obtain ⟨l, hl, m, hm, hlL, hmM⟩ := hp
        refine ⟨l, Finset.mem_erase.mpr ⟨?_, hl⟩, m, Finset.mem_erase.mpr ⟨?_, hm⟩, hlL, hmM⟩
        · intro h
          rw [h] at hlL
          exact ls_ne hlL
        · intro h
          rw [h] at hmM
          exact ms_ne hmM
      have h2 := pair_card _ hn0 hE hp'
      have hc2 : (0 : Fin 13) ∈ S ∧ 2 ≤ S.card := ⟨h0, by omega⟩
      rw [if_pos hp, if_pos hc2]
      omega
    · have hp' : ¬ (∃ l ∈ S.erase 0, ∃ m ∈ S.erase 0, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13))) := by
        rintro ⟨l, hl, m, hm, hlL, hmM⟩
        exact hp ⟨l, Finset.mem_of_mem_erase hl, m, Finset.mem_of_mem_erase hm, hlL, hmM⟩
      have h2 := nopair_card _ hn0 hE hp'
      rw [if_neg hp]
      by_cases hc2 : 2 ≤ S.card
      · have hc3 : (0 : Fin 13) ∈ S ∧ 2 ≤ S.card := ⟨h0, hc2⟩
        rw [if_pos hc3]
        omega
      · have hc3 : ¬ ((0 : Fin 13) ∈ S ∧ 2 ≤ S.card) := fun h => hc2 h.2
        rw [if_neg hc3]
        omega
  · have hc3 : ¬ ((0 : Fin 13) ∈ S ∧ 2 ≤ S.card) := fun h => h0 h.1
    rw [if_neg hc3]
    by_cases hp : (∃ l ∈ S, ∃ m ∈ S, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))
    · have h2 := pair_card S h0 hS hp
      rw [if_pos hp]
      omega
    · have h2 := nopair_card S h0 hS hp
      rw [if_neg hp]
      omega

end PEqualNP.Outside.L_meta_1569

theorem PEqualNP.Outside.L_meta_1569 : ∀ (k : ℕ) (K : Fin k → Finset (Fin 13)),
    (∀ i : Fin k, ∀ t ∈ K i, ∀ u ∈ K i, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) →
    ∑ i : Fin k, ((K i).card - 1) =
      (Finset.univ.filter (fun i : Fin k => (0 : Fin 13) ∈ K i ∧ 2 ≤ (K i).card)).card +
      (Finset.univ.filter (fun i : Fin k => ∃ l ∈ K i, ∃ m ∈ K i, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))).card := by
  intro k K h
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact PEqualNP.Outside.L_meta_1569.perSet (K i) (h i)
