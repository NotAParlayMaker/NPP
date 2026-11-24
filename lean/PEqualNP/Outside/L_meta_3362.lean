import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3362_aux

theorem mul_le_add_of (a b : ℕ) (h : a ≤ 1 ∨ b ≤ 1) : a * b ≤ a + b := by
  rcases h with h | h
  · calc a * b ≤ 1 * b := Nat.mul_le_mul_right b h
      _ = b := one_mul b
      _ ≤ a + b := Nat.le_add_left b a
  · calc a * b ≤ a * 1 := Nat.mul_le_mul_left a h
      _ = a := mul_one a
      _ ≤ a + b := Nat.le_add_right a b

end PEqualNP.Outside.L_meta_3362_aux

theorem PEqualNP.Outside.L_meta_3362 :
    ∀ (x1 x2 x3 : ℕ) (x4 : Fin x1 → Fin x1 → Prop) [x5 : DecidableRel x4], (∀ (x6 : Fin x1), Fintype.card { x7 : Fin x1 // x4 x7 x6 } = x2) → (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x4 x7 x10 ∧ x4 x8 x10) → ∀ (x8 x9 : Fin x3 → Finset (Fin x1)), (∀ (x10 : Fin x3), ∀ x11 ∈ x8 x10, ∀ x13 ∈ x9 x10, x4 x11 x13) → (∀ (x11 x12 : Fin x1), x4 x11 x12 → ∃ (x14 : Fin x3), x11 ∈ x8 x14 ∧ x12 ∈ x9 x14) → x1 * x2 ≤ ∑ x12 : Fin x3, ((x8 x12).card + (x9 x12).card) := by
  intro x1 x2 x3 I _ hdeg huniq A B hcov1 hcov2
  have star : ∀ t, (A t).card ≤ 1 ∨ (B t).card ≤ 1 := by
    intro t
    by_contra hc
    push Not at hc
    obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.mp hc.1
    obtain ⟨l, hl, l', hl', hll⟩ := Finset.one_lt_card.mp hc.2
    obtain ⟨m, _, hmu⟩ := huniq p p' hpp
    have e1 := hmu l ⟨hcov1 t p hp l hl, hcov1 t p' hp' l hl⟩
    have e2 := hmu l' ⟨hcov1 t p hp l' hl', hcov1 t p' hp' l' hl'⟩
    exact hll (e1.trans e2.symm)
  set E := (Finset.univ : Finset (Fin x1 × Fin x1)).filter (fun e => I e.1 e.2) with hE
  have hfib : ∀ l : Fin x1, (E.filter (fun e => e.2 = l)).card = x2 := by
    intro l
    rw [← hdeg l, Fintype.card_subtype]
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
      rw [← he.2]
      exact he.1
    · intro e1 he1 e2 he2 h
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at he1 he2
      exact Prod.ext h (he1.2.trans he2.2.symm)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine ⟨(p, l), ?_, rfl⟩
      simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hp
  have hEcard : E.card = x1 * x2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun e => e.2) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp only [hfib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hsub : E ⊆ Finset.univ.biUnion (fun t => A t ×ˢ B t) := by
    intro e he
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨t, h1, h2⟩ := hcov2 e.1 e.2 he
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, Finset.mem_product.mpr ⟨h1, h2⟩⟩
  calc x1 * x2 = E.card := hEcard.symm
    _ ≤ (Finset.univ.biUnion (fun t => A t ×ˢ B t)).card := Finset.card_le_card hsub
    _ ≤ ∑ t, (A t ×ˢ B t).card := Finset.card_biUnion_le
    _ = ∑ t, (A t).card * (B t).card := by simp only [Finset.card_product]
    _ ≤ _ := Finset.sum_le_sum (fun t _ =>
      PEqualNP.Outside.L_meta_3362_aux.mul_le_add_of _ _ (star t))
