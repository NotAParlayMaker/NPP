import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4763
open PEqualNP.CircuitLowerBounds



theorem cnt_core {α β : Type} [DecidableEq α] [DecidableEq β] (A B : Finset α) (E : Finset β)
    (hBA : B ⊆ A) (g : α → β) (maps : ∀ p ∈ A, p ∉ B → g p ∈ E)
    (inj : ∀ p ∈ A, p ∉ B → ∀ p' ∈ A, p' ∉ B → g p = g p' → p = p') :
    A.card ≤ E.card + B.card := by
  have h1 : (A \ B).card ≤ E.card := by
    apply Finset.card_le_card_of_injOn g
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_sdiff] at hp
      exact maps p hp.1 hp.2
    · intro p hp p' hp' h
      rw [Finset.mem_coe, Finset.mem_sdiff] at hp hp'
      exact inj p hp.1 hp.2 p' hp'.1 hp'.2 h
  have h2 := Finset.card_sdiff_add_card_eq_card hBA
  omega

end PEqualNP.Outside.L_meta_4763

open PEqualNP.Outside.L_meta_4763 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4763 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), ∀ x8 ∈ x7, x1 + (2 : ℕ) ≤ x7.card + Fintype.card { x10 : Fin x2 // x3 x10 x8 ∧ ∀ x11 ∈ x7.erase x8, ¬x3 x10 x11 } := by
  intro q N I _ h1 h2 S l hl
  classical
  have hA := h1 l
  have key : (Finset.univ.filter fun p : Fin N => I p l).card ≤ (S.erase l).card
      + (Finset.univ.filter fun p : Fin N => I p l ∧ ∀ l' ∈ S.erase l, ¬ I p l').card := by
    apply cnt_core _ _ _ ?_ (fun p => if h : ∃ l' ∈ S.erase l, I p l' then h.choose else l)
    · intro p hp hnp
      have hpl := (Finset.mem_filter.1 hp).2
      have hex : ∃ l' ∈ S.erase l, I p l' := by
        by_contra hno
        exact hnp (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpl, fun l' hl' hI => hno ⟨l', hl', hI⟩⟩)
      rw [dif_pos hex]
      exact hex.choose_spec.1
    · intro p hp hnp p' hp' hnp' heq
      have hpl := (Finset.mem_filter.1 hp).2
      have hpl' := (Finset.mem_filter.1 hp').2
      have hex : ∃ l' ∈ S.erase l, I p l' := by
        by_contra hno
        exact hnp (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpl, fun l' hl' hI => hno ⟨l', hl', hI⟩⟩)
      have hex' : ∃ l' ∈ S.erase l, I p' l' := by
        by_contra hno
        exact hnp' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hpl', fun l' hl' hI => hno ⟨l', hl', hI⟩⟩)
      rw [dif_pos hex, dif_pos hex'] at heq
      by_contra hne
      obtain ⟨l0, _, huniq⟩ := h2 p p' hne
      have e1 := huniq l ⟨hpl, hpl'⟩
      have e2 := huniq hex.choose ⟨hex.choose_spec.2, by rw [heq]; exact hex'.choose_spec.2⟩
      have hmem := hex.choose_spec.1
      rw [e2, ← e1] at hmem
      exact (Finset.mem_erase.1 hmem).1 rfl
    · intro p hp
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hp).2.1⟩
  have hE : (S.erase l).card + 1 = S.card := Finset.card_erase_add_one hl
  simp only [Fintype.card_subtype] at hA ⊢
  convert (show q + 2 ≤ S.card + (Finset.univ.filter fun p : Fin N => I p l ∧ ∀ l' ∈ S.erase l, ¬ I p l').card from by
    have hA' : (Finset.univ.filter fun p : Fin N => I p l).card = q + 1 := by convert hA
    omega) using 3
