import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1463

-- The Paley tournament on Z/7: u beats v when v - u is a nonzero square mod 7.
abbrev dom (u v : Fin 7) : Prop :=
  (v.val + 7 - u.val) % 7 = 1 ∨ (v.val + 7 - u.val) % 7 = 2 ∨ (v.val + 7 - u.val) % 7 = 4

theorem dom_asymm : ∀ u v : Fin 7, dom u v → dom v u → False := by
  decide

theorem dom_two : ∀ y1 y2 : Fin 7, ∃ a : Fin 7, a ≠ y1 ∧ a ≠ y2 ∧ dom a y1 ∧ dom a y2 := by
  decide

theorem cover_two {α : Type} [DecidableEq α] (s A : Finset α) (hs : s ⊆ A) (hA : A.Nonempty)
    (h2 : s.card ≤ 2) : ∃ y1 ∈ A, ∃ y2 ∈ A, s ⊆ {y1, y2} := by
  obtain ⟨z, hz⟩ := hA
  rcases Nat.lt_or_ge s.card 2 with h | h
  · rcases Nat.lt_or_ge s.card 1 with h' | h'
    · have : s = ∅ := Finset.card_eq_zero.mp (by omega : s.card = 0)
      exact ⟨z, hz, z, hz, by simp [this]⟩
    · obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp (by omega : s.card = 1)
      have hy : y ∈ A := hs (Finset.mem_singleton_self y)
      exact ⟨y, hy, y, hy, by simp⟩
  · obtain ⟨x, y, _, rfl⟩ := Finset.card_eq_two.mp (by omega : s.card = 2)
    exact ⟨x, hs (by simp), y, hs (by simp), le_refl _⟩

end PEqualNP.Outside.L_meta_1463

open PEqualNP.Outside.L_meta_1463

theorem PEqualNP.Outside.L_meta_1463 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ A ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ A, r (f i) y := by
  intro n m S A hA h2
  let e : {x // x ∈ A} ≃ Fin 7 := A.equivFin.trans (finCongr hA)
  let r : Fin n → Fin n → Prop := fun a b => ∃ ha : a ∈ A, ∃ hb : b ∈ A, dom (e ⟨a, ha⟩) (e ⟨b, hb⟩)
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  have key : ∀ i : Fin m, ∃ a, a ∈ A ∧ a ∉ S i ∧ ∀ y ∈ S i ∩ A, r a y := by
    intro i
    obtain ⟨y1, hy1, y2, hy2, hsub⟩ :=
      cover_two (S i ∩ A) A Finset.inter_subset_right hne (h2 i)
    obtain ⟨a7, ha1, ha2, hd1, hd2⟩ := dom_two (e ⟨y1, hy1⟩) (e ⟨y2, hy2⟩)
    have hea : e ⟨(e.symm a7).val, (e.symm a7).property⟩ = a7 := by
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    have hn1 : (e.symm a7).val ≠ y1 := by
      intro h
      apply ha1
      rw [← hea]
      congr 1
      exact Subtype.ext h
    have hn2 : (e.symm a7).val ≠ y2 := by
      intro h
      apply ha2
      rw [← hea]
      congr 1
      exact Subtype.ext h
    refine ⟨(e.symm a7).val, (e.symm a7).property, ?_, ?_⟩
    · intro hS
      have hmem := hsub (Finset.mem_inter.mpr ⟨hS, (e.symm a7).property⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact hn1 h
      · exact hn2 h
    · intro y hy
      have hmem := hsub hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      refine ⟨(e.symm a7).property, (Finset.mem_inter.mp hy).2, ?_⟩
      rw [hea]
      rcases hmem with rfl | rfl
      · exact hd1
      · exact hd2
  choose f hf using key
  refine ⟨r, f, ?_, hf⟩
  intro a b hab hba
  obtain ⟨ha, hb, h1⟩ := hab
  obtain ⟨hb', ha', h2'⟩ := hba
  exact dom_asymm _ _ h1 h2'
