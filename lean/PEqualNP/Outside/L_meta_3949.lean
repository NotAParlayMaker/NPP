import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3949 : ∀ (x1 : Type) [x2 : DecidableEq x1] (x3 : List (x1 × x1)) (x4 : x1), (∀ x5 ∈ x3, x5.1 ≠ x5.2) → ∀ (x6 : x1 → Bool), x6 x4 = Bool.false → ∀ (x8 : Bool), (x3.any fun (x9 : x1 × x1) => Function.update x6 x4 x8 x9.1 && Function.update x6 x4 x8 x9.2) = ((x3.any fun (x9 : x1 × x1) => x6 x9.1 && x6 x9.2) || x8 && x3.any fun (x9 : x1 × x1) => Decidable.decide (x9.1 = x4) && x6 x9.2 || Decidable.decide (x9.2 = x4) && x6 x9.1) := by
  intro α _ l a hl f hf b
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.any_cons]
    rw [ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
    have he := hl e List.mem_cons_self
    obtain ⟨u, v⟩ := e
    simp only at he ⊢
    by_cases hu : u = a <;> by_cases hv : v = a
    · exact absurd (hu.trans hv.symm) he
    · subst hu
      simp only [Function.update_self, Function.update_of_ne hv, hf, decide_true, decide_false, hv]
      cases b <;> cases f v <;> simp
    · subst hv
      simp only [Function.update_self, Function.update_of_ne hu, hf, decide_true, decide_false, hu]
      cases b <;> cases f u <;> simp
    · simp only [Function.update_of_ne hu, Function.update_of_ne hv, hu, hv, decide_false]
      cases b <;> cases f u <;> cases f v <;> simp
