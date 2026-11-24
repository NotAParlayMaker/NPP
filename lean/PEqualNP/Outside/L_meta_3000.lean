import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3000 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ x9 ∉ x7, ∃ (x11 : Fin x2), x3 x11 x9 ∧ ∀ x12 ∈ x7, ¬x3 x11 x12 := by
  intro q n incident _ lineSize common chosen bound line outside
  classical
  by_contra noPoint
  have cover (p : {p : Fin n // incident p line}) :
      ∃ other : {m : Fin n // m ∈ chosen}, incident p.val other.val := by
    by_contra! miss
    exact noPoint ⟨p.val, p.property, fun m hm => miss ⟨m, hm⟩⟩
  choose assign belongs using cover
  have injective : Function.Injective assign := by
    intro p r eq
    apply Subtype.ext
    by_contra different
    obtain ⟨only, _, unique⟩ := common p.val r.val different
    have hline : line = only := unique _ ⟨p.property, r.property⟩
    have hother : (assign p).val = only := unique _ ⟨belongs p, by rw [eq]; exact belongs r⟩
    have same : (assign p).val = line := hother.trans hline.symm
    exact outside (same ▸ (assign p).property)
  have count := Fintype.card_le_of_injective assign injective
  rw [lineSize line, Fintype.card_coe] at count
  omega
