import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6218 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3],
      (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) →
      {x6 : Fin x2 × Fin x2 | x3 x6.1 x6.2}.ncard = x2 * (x1 + (1 : ℕ)) := by
  intro x1 x2 x3 hdec hcol
  have hfib : ∀ y : Fin x2,
      ((Finset.univ.filter (fun p : Fin x2 × Fin x2 => x3 p.1 p.2)).filter (fun p => p.2 = y)).card
        = x1 + 1 := by
    intro y
    rw [← hcol y]
    rw [Fintype.card_subtype]
    apply Finset.card_nbij (fun p : Fin x2 × Fin x2 => p.1)
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
      simpa [hp.2] using hp.1
    · intro p1 h1 p2 h2 he
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h1 h2
      exact Prod.ext he (by rw [h1.2, h2.2])
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
      exact ⟨(x, y), by simpa using hx, rfl⟩
  have h : (Finset.univ.filter (fun p : Fin x2 × Fin x2 => x3 p.1 p.2)).card = x2 * (x1 + 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin x2 × Fin x2 => p.2) (t := Finset.univ)
      (fun p _ => Finset.mem_univ p.2)]
    simp [hfib, Finset.sum_const, Finset.card_univ]
  rw [Set.ncard_eq_toFinset_card]
  simpa using h
