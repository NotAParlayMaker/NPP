import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3949 : ∀ (x1 : Type) [x2 : DecidableEq x1] (x3 : List (x1 × x1)) (x4 : x1), (∀ x5 ∈ x3, x5.1 ≠ x5.2) → ∀ (x6 : x1 → Bool), x6 x4 = Bool.false → ∀ (x8 : Bool), (x3.any fun (x9 : x1 × x1) => Function.update x6 x4 x8 x9.1 && Function.update x6 x4 x8 x9.2) = ((x3.any fun (x9 : x1 × x1) => x6 x9.1 && x6 x9.2) || x8 && x3.any fun (x9 : x1 × x1) => Decidable.decide (x9.1 = x4) && x6 x9.2 || Decidable.decide (x9.2 = x4) && x6 x9.1) := by
  intro α _ E v hE x hx b
  induction E with
  | nil => simp
  | cons e E ih =>
    have he : e.1 ≠ e.2 := hE e List.mem_cons_self
    have ih' := ih (fun f hf => hE f (List.mem_cons_of_mem _ hf))
    simp only [List.any_cons]
    rw [ih']
    obtain ⟨a, c⟩ := e
    simp only at he ⊢
    by_cases ha : a = v
    · subst ha
      have hc : c ≠ a := fun h => he h.symm
      simp only [Function.update_apply, hc, ↓reduceIte, hx, decide_true, decide_false,
        Bool.true_and, Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or]
      cases b <;> cases x c <;> simp
    · by_cases hc : c = v
      · subst hc
        simp only [Function.update_apply, ha, ↓reduceIte, hx, decide_true, decide_false,
          Bool.true_and, Bool.false_and, Bool.and_false, Bool.or_false, Bool.false_or]
        cases b <;> cases x a <;> simp
      · simp only [Function.update_apply, ha, hc, ↓reduceIte, decide_false, Bool.false_and,
          Bool.or_false]
        cases b <;> simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
