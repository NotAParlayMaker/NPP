import Mathlib
import PEqualNP.Defs

-- Four distinct points forbid all but at most three partners: the four translates of
-- the difference set cover at least ten of the thirteen residues. Checked for every
-- choice of four distinct points by the kernel.
namespace PEqualNP.Outside.L_meta_3771

def bad (a b : Fin 13) : Bool := decide (a + b ∈ ({0, 1, 3, 9} : Finset (Fin 13)))

def check (a1 a2 a3 a4 : Fin 13) : Bool :=
  decide (a1 = a2) || decide (a1 = a3) || decide (a1 = a4) || decide (a2 = a3) ||
    decide (a2 = a4) || decide (a3 = a4) ||
    decide ((Finset.univ.filter fun b : Fin 13 =>
      !bad a1 b && !bad a2 b && !bad a3 b && !bad a4 b).card ≤ 3)

lemma check_all : ∀ a1 a2 a3 a4 : Fin 13, check a1 a2 a3 a4 = true := by decide +kernel

lemma four (a1 a2 a3 a4 : Fin 13) (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h14 : a1 ≠ a4)
    (h23 : a2 ≠ a3) (h24 : a2 ≠ a4) (h34 : a3 ≠ a4) :
    (Finset.univ.filter fun b : Fin 13 =>
      !bad a1 b && !bad a2 b && !bad a3 b && !bad a4 b).card ≤ 3 := by
  have h := check_all a1 a2 a3 a4
  simp only [check, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · exact absurd h h12
  · exact absurd h h13
  · exact absurd h h14
  · exact absurd h h23
  · exact absurd h h24
  · exact absurd h h34
  · exact h

lemma pick {s : Finset (Fin 13)} (h : 0 < s.card) : ∃ a, a ∈ s := Finset.card_pos.mp h

end PEqualNP.Outside.L_meta_3771

open PEqualNP.Outside.L_meta_3771 in
theorem PEqualNP.Outside.L_meta_3771 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ x1) → x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) := by
  intro D A B h
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨a1, h1⟩ := pick (s := A) (by omega)
  obtain ⟨a2, h2⟩ := pick (s := A.erase a1) (by rw [Finset.card_erase_of_mem h1]; omega)
  have g2 := Finset.mem_erase.mp h2
  obtain ⟨a3, h3⟩ := pick (s := (A.erase a1).erase a2) (by
    rw [Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1]; omega)
  have g3a := Finset.mem_erase.mp h3
  have g3b := Finset.mem_erase.mp g3a.2
  obtain ⟨a4, h4⟩ := pick (s := ((A.erase a1).erase a2).erase a3) (by
    rw [Finset.card_erase_of_mem h3, Finset.card_erase_of_mem h2,
      Finset.card_erase_of_mem h1]; omega)
  have g4a := Finset.mem_erase.mp h4
  have g4b := Finset.mem_erase.mp g4a.2
  have g4c := Finset.mem_erase.mp g4b.2
  have hsub : B ⊆ Finset.univ.filter fun b : Fin 13 =>
      !bad a1 b && !bad a2 b && !bad a3 b && !bad a4 b := by
    intro b hb
    have e1 := h a1 h1 b hb
    have e2 := h a2 g2.2 b hb
    have e3 := h a3 g3b.2 b hb
    have e4 := h a4 g4c.2 b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨⟨⟨e1, e2⟩, e3⟩, e4⟩
  have hle := (Finset.card_le_card hsub).trans
    (four a1 a2 a3 a4 g2.1.symm g3b.1.symm g4c.1.symm g3a.1.symm g4b.1.symm g4a.1.symm)
  omega
