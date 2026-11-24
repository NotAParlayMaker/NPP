import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3037_aux

theorem main (n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] :
    have f : Finset (Fin n) → Fin (n + n) → Bool := fun S i =>
      Fin.addCases (fun p => decide (¬∃ l ∈ S, I p l)) (fun l => decide (l ∈ S)) i
    ∀ S : Finset (Fin n),
      Fintype.card { l : Fin n // f S (Fin.natAdd n l) = true } = S.card ∧
      ¬∃ p l : Fin n, I p l ∧ f S (Fin.castAdd n p) = true ∧ f S (Fin.natAdd n l) = true := by
  intro f S
  constructor
  · have heq : { l : Fin n // f S (Fin.natAdd n l) = true } ≃ { l : Fin n // l ∈ S } :=
      Equiv.subtypeEquivRight fun l => by
        simp only [f, Fin.addCases_right, decide_eq_true_eq]
    rw [Fintype.card_congr heq, Fintype.card_coe]
  · rintro ⟨p, l, hI, hp, hl⟩
    simp only [f, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
    exact hp ⟨l, hl, hI⟩

end PEqualNP.Outside.L_meta_3037_aux

theorem PEqualNP.Outside.L_meta_3037 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2],   have x4 : Finset (Fin x1) → Fin (x1 + x1) → Bool := fun (x4 : Finset (Fin x1)) (x5 : Fin (x1 + x1)) => Fin.addCases (fun (x6 : Fin x1) => Decidable.decide ¬∃ x7 ∈ x4, x2 x6 x7) (fun (x6 : Fin x1) => Decidable.decide (x6 ∈ x4)) x5;   ∀ (x5 : Finset (Fin x1)), Fintype.card { x6 : Fin x1 // x4 x5 (Fin.natAdd x1 x6) = Bool.true } = x5.card ∧ ¬∃ (x6 : Fin x1) (x7 : Fin x1), x2 x6 x7 ∧ x4 x5 (Fin.castAdd x1 x6) = Bool.true ∧ x4 x5 (Fin.natAdd x1 x7) = Bool.true :=
  fun x1 x2 _ => PEqualNP.Outside.L_meta_3037_aux.main x1 x2
