import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1569

lemma not_both (a : Fin 13) : a ∈ ({4, 10, 12} : Finset (Fin 13)) → a ∉ ({1, 5, 11} : Finset (Fin 13)) := by
  revert a
  decide

lemma zero_not_ls : (0 : Fin 13) ∉ ({4, 10, 12} : Finset (Fin 13)) := by decide

lemma zero_not_ms : (0 : Fin 13) ∉ ({1, 5, 11} : Finset (Fin 13)) := by decide

-- One clique: its size minus one is the vertex 0 term plus the cross pair term.
lemma key (K : Finset (Fin 13))
    (hK : ∀ t ∈ K, ∀ u ∈ K, t ≠ u → ((t = 0 ∨ u = 0) ∨
      (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨
      (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) :
    K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
      (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13))
        then 1 else 0) := by
  set A := K.erase 0 with hAdef
  have hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      (a ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ b ∈ ({1, 5, 11} : Finset (Fin 13))) ∨
      (a ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ b ∈ ({4, 10, 12} : Finset (Fin 13))) := by
    intro a ha b hb hab
    rw [Finset.mem_erase] at ha hb
    rcases hK a ha.2 b hb.2 hab with h | h | h
    · rcases h with h | h
      · exact absurd h ha.1
      · exact absurd h hb.1
    · exact Or.inl h
    · exact Or.inr h
  have hA2 : A.card ≤ 2 := by
    by_contra hc
    push_neg at hc
    obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
    rcases hA a ha b hb hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hA a ha c hc' hac with ⟨_, h4⟩ | ⟨h3, _⟩
      · rcases hA b hb c hc' hbc with ⟨h5, _⟩ | ⟨_, h6⟩
        · exact not_both b h5 h2
        · exact not_both c h6 h4
      · exact not_both a h1 h3
    · rcases hA a ha c hc' hac with ⟨h3, _⟩ | ⟨_, h4⟩
      · exact not_both a h3 h1
      · rcases hA b hb c hc' hbc with ⟨_, h6⟩ | ⟨h5, _⟩
        · exact not_both c h4 h6
        · exact not_both b h2 h5
  have hpair : (∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧
      m ∈ ({1, 5, 11} : Finset (Fin 13))) ↔ 2 ≤ A.card := by
    constructor
    · rintro ⟨l, hl, m, hm, hlL, hmM⟩
      have hl0 : l ≠ 0 := fun h => zero_not_ls (h ▸ hlL)
      have hm0 : m ≠ 0 := fun h => zero_not_ms (h ▸ hmM)
      have hlm : l ≠ m := fun h => not_both l hlL (h ▸ hmM)
      have : 1 < A.card := Finset.one_lt_card.mpr
        ⟨l, Finset.mem_erase.mpr ⟨hl0, hl⟩, m, Finset.mem_erase.mpr ⟨hm0, hm⟩, hlm⟩
      omega
    · intro h2
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
      have ha' := (Finset.mem_erase.mp ha).2
      have hb' := (Finset.mem_erase.mp hb).2
      rcases hA a ha b hb hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', b, hb', h1, h2⟩
      · exact ⟨b, hb', a, ha', h2, h1⟩
  by_cases h0 : (0 : Fin 13) ∈ K
  · have hc : K.card = A.card + 1 := (Finset.card_erase_add_one h0).symm
    rw [hc]
    by_cases h2 : 2 ≤ A.card
    · have hp := hpair.mpr h2
      rw [if_pos ⟨h0, by omega⟩, if_pos hp]
      omega
    · have hp : ¬ (∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧
          m ∈ ({1, 5, 11} : Finset (Fin 13))) := fun h => h2 (hpair.mp h)
      rw [if_neg hp]
      by_cases h1 : 1 ≤ A.card
      · rw [if_pos ⟨h0, by omega⟩]
        omega
      · rw [if_neg (fun h => by omega)]
        omega
  · have hc : K.card = A.card := by
      rw [hAdef, Finset.erase_eq_of_notMem h0]
    rw [hc, if_neg (fun h => h0 h.1)]
    by_cases h2 : 2 ≤ A.card
    · rw [if_pos (hpair.mpr h2)]
      omega
    · rw [if_neg (fun h => h2 (hpair.mp h))]
      omega

end PEqualNP.Outside.L_meta_1569

theorem PEqualNP.Outside.L_meta_1569 : ∀ (k : ℕ) (K : Fin k → Finset (Fin 13)),
    (∀ i : Fin k, ∀ t ∈ K i, ∀ u ∈ K i, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) →
    ∑ i : Fin k, ((K i).card - 1) =
      (Finset.univ.filter (fun i : Fin k => (0 : Fin 13) ∈ K i ∧ 2 ≤ (K i).card)).card +
      (Finset.univ.filter (fun i : Fin k => ∃ l ∈ K i, ∃ m ∈ K i, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))).card := by
  intro k K hK
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => PEqualNP.Outside.L_meta_1569.key (K i) (hK i))
