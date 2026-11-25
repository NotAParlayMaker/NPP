import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7634_aux

-- Every point of a projective plane of order q lies on exactly q + 1 lines.
theorem lines_through {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  haveI : Nonempty (Fin N) := ⟨p⟩
  have hex : ∀ p' : Fin N, p' ≠ p → ∃ l, I p l ∧ I p' l :=
    fun p' h => (hU p p' (Ne.symm h)).exists
  choose! g hg using hex
  have h1 := Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ.filter (fun p' => p' ≠ p))
    (t := Finset.univ.filter (fun l => I p l)) (by
      intro p' hp'
      simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq] at hp' ⊢
      exact (hg p' hp').1)
  have h2 : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.filter (fun p' => p' ≠ p)).filter (fun p' => g p' = l)).card = q := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have : (Finset.univ.filter (fun p' => p' ≠ p)).filter (fun p' => g p' = l) =
        (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨hne, rfl⟩
        exact ⟨hne, (hg p' hne).2⟩
      · rintro ⟨hne, hp'⟩
        exact ⟨hne, (hU p p' (Ne.symm hne)).unique (hg p' hne) ⟨hl, hp'⟩⟩
    rw [this, Finset.card_erase_of_mem (by simp [hl]), ← Fintype.card_subtype, hL]
    simp
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [← h1, hN, Nat.add_sub_cancel]
  ring

end PEqualNP.Outside.L_meta_7634_aux

theorem PEqualNP.Outside.L_meta_7634 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : Fin x2), x3 x9 x10 → ((Finset.filter (x3 x9) Finset.univ).erase x10).card = x1 ∧ ∃ (x12 : Fin x2 → Fin x2), ∀ (x13 x14 : Fin x2), x13 ≠ x9 → x3 x9 x14 → (x3 x13 x14 ↔ x12 x13 = x14) := by
  classical
  intro q N I _ hq hN hL hU p l hpl
  refine ⟨?_, ?_⟩
  · rw [Finset.card_erase_of_mem (by simp [hpl]), PEqualNP.Outside.L_meta_7634_aux.lines_through hq hN hL hU p]
    simp
  · have hex : ∀ r : Fin N, r ≠ p → ∃ m, I p m ∧ I r m := fun r h => (hU p r (Ne.symm h)).exists
    choose! g hg using hex
    refine ⟨g, fun r m hr hpm => ?_⟩
    constructor
    · intro hrm
      exact (hU p r (Ne.symm hr)).unique (hg r hr) ⟨hpm, hrm⟩
    · rintro rfl
      exact (hg r hr).2
