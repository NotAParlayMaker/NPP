import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3949 : ∀ (x1 : Type) [x2 : DecidableEq x1] (x3 : List (x1 × x1)) (x4 : x1), (∀ x5 ∈ x3, x5.1 ≠ x5.2) → ∀ (x6 : x1 → Bool), x6 x4 = Bool.false → ∀ (x8 : Bool), (x3.any fun (x9 : x1 × x1) => Function.update x6 x4 x8 x9.1 && Function.update x6 x4 x8 x9.2) = ((x3.any fun (x9 : x1 × x1) => x6 x9.1 && x6 x9.2) || x8 && x3.any fun (x9 : x1 × x1) => Decidable.decide (x9.1 = x4) && x6 x9.2 || Decidable.decide (x9.2 = x4) && x6 x9.1) := by
  intro α _ l v hl x hv b
  induction l with
  | nil => simp
  | cons e l ih =>
    obtain ⟨a, c⟩ := e
    have hac : a ≠ c := hl (a, c) (by simp)
    have ih' := ih (fun y hy => hl y (by simp [hy]))
    simp only [List.any_cons]
    rw [ih']
    by_cases ha : a = v
    · subst ha
      have hc : c ≠ a := fun h => hac h.symm
      simp [Function.update, hc, hv]
      cases b <;> cases x c <;> simp
    · by_cases hc : c = v
      · subst hc
        simp [Function.update, ha, hv]
        cases b <;> cases x a <;> simp
      · simp [Function.update, ha, hc]
        cases b <;> simp [Bool.or_assoc]
