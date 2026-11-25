import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6218

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6218

theorem PEqualNP.Outside.L_meta_6218 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → {x6 : Fin x2 × Fin x2 | x3 x6.1 x6.2}.ncard = x2 * (x1 + (1 : ℕ)) := by
  intro q N I _ h
  classical
  have e : {x : Fin N × Fin N | I x.1 x.2} = ↑(Finset.univ.filter fun x : Fin N × Fin N => I x.1 x.2) := by
    ext x; simp
  rw [e, Set.ncard_coe_finset]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun x _ => Finset.mem_univ _)]
  have : ∀ b : Fin N, ((Finset.univ.filter fun x : Fin N × Fin N => I x.1 x.2).filter fun x => x.2 = b).card = q + 1 := by
    intro b
    rw [← h b, Fintype.card_subtype]
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [← hx.2]; exact hx.1
    · intro x hx y hy hxy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact Prod.ext hxy (hx.2.trans hy.2.symm)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact ⟨(a, b), by simpa using ha, rfl⟩
  rw [Finset.sum_congr rfl fun b _ => this b]
  simp
