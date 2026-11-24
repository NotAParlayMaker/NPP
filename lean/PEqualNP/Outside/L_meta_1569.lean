import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1569_aux

abbrev lefts : Finset (Fin 13) := {4, 10, 12}
abbrev rights : Finset (Fin 13) := {1, 5, 11}

abbrev Adj (x y : Fin 13) : Prop :=
  (x = 0 ∨ y = 0) ∨ (x ∈ lefts ∧ y ∈ rights) ∨ (x ∈ rights ∧ y ∈ lefts)

abbrev Paired (S : Finset (Fin 13)) : Prop :=
  ∃ l ∈ S, ∃ m ∈ S, l ∈ lefts ∧ m ∈ rights

private theorem left_ne_zero : ∀ x : Fin 13, x ∈ lefts → x ≠ 0 := by decide
private theorem right_ne_zero : ∀ x : Fin 13, x ∈ rights → x ≠ 0 := by decide
private theorem separate : ∀ x : Fin 13, x ∈ lefts → x ∉ rights := by decide

private theorem common_neighbor (x l m : Fin 13) (hl : l ∈ lefts) (hm : m ∈ rights)
    (hxl : Adj x l) (hxm : Adj x m) : x = 0 := by
  by_contra hx
  have hl0 := left_ne_zero l hl
  have hm0 := right_ne_zero m hm
  have hlr := separate l hl
  have hml : m ∉ lefts := fun h => separate m h hm
  rcases hxl with (h | h) | ⟨_, h⟩ | ⟨hr, _⟩
  · exact hx h
  · exact hl0 h
  · exact hlr h
  · rcases hxm with (h | h) | ⟨hlx, _⟩ | ⟨_, h⟩
    · exact hx h
    · exact hm0 h
    · exact separate x hlx hr
    · exact hml h

lemma count_one (S : Finset (Fin 13))
    (h : ∀ t ∈ S, ∀ u ∈ S, t ≠ u → Adj t u) :
    S.card - 1 = (if (0 : Fin 13) ∈ S ∧ 2 ≤ S.card then 1 else 0) +
      (if Paired S then 1 else 0) := by
  by_cases hp : Paired S
  · obtain ⟨l, hl, m, hm, hL, hR⟩ := hp
    have hne : l ≠ m := by rintro rfl; exact separate l hL hR
    have herase : S.erase 0 = {l, m} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        obtain ⟨hx0, hxS⟩ := Finset.mem_erase.mp hx
        by_contra! hn
        exact hx0 (common_neighbor x l m hL hR (h x hxS l hl hn.1) (h x hxS m hm hn.2))
      · rintro (rfl | rfl)
        · exact Finset.mem_erase.mpr ⟨left_ne_zero _ hL, hl⟩
        · exact Finset.mem_erase.mpr ⟨right_ne_zero _ hR, hm⟩
    have two : (S.erase 0).card = 2 := by rw [herase]; simp [hne]
    have hp' : Paired S := ⟨l,hl,m,hm,hL,hR⟩
    by_cases hz : (0 : Fin 13) ∈ S
    · have n := Finset.card_erase_add_one hz
      have three : S.card = 3 := by omega
      simp [hz, three, hp']
    · rw [Finset.erase_eq_of_notMem hz] at two
      simp [hz, two, hp']
  · have small : (S.erase 0).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      obtain ⟨hx0,hxS⟩ := Finset.mem_erase.mp hx
      obtain ⟨hy0,hyS⟩ := Finset.mem_erase.mp hy
      by_contra ne
      rcases h x hxS y hyS ne with (h0 | h0) | ⟨hL,hR⟩ | ⟨hR,hL⟩
      · exact hx0 h0
      · exact hy0 h0
      · exact hp ⟨x,hxS,y,hyS,hL,hR⟩
      · exact hp ⟨y,hyS,x,hxS,hL,hR⟩
    by_cases hz : (0 : Fin 13) ∈ S
    · have n := Finset.card_erase_add_one hz
      by_cases hn : 2 ≤ S.card <;> simp [hz, hp, hn] <;> omega
    · rw [Finset.erase_eq_of_notMem hz] at small
      simp [hz, hp]
      omega

end PEqualNP.Outside.L_meta_1569_aux

theorem PEqualNP.Outside.L_meta_1569 : ∀ (k : ℕ) (K : Fin k → Finset (Fin 13)),
    (∀ i : Fin k, ∀ t ∈ K i, ∀ u ∈ K i, t ≠ u → ((t = 0 ∨ u = 0) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) →
    ∑ i : Fin k, ((K i).card - 1) =
      (Finset.univ.filter (fun i : Fin k => (0 : Fin 13) ∈ K i ∧ 2 ≤ (K i).card)).card +
      (Finset.univ.filter (fun i : Fin k => ∃ l ∈ K i, ∃ m ∈ K i, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)))).card := by
  intro k K h
  have total := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin k))) rfl
    (fun i _ => PEqualNP.Outside.L_meta_1569_aux.count_one (K i) (h i))
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] using total
