import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8589_aux

def F (x1 : List (ℕ × ℕ)) : (List (ℕ × ℕ → Bool) → Bool) → List (ℕ × ℕ → Bool) → Bool :=
  fun (x4 : List (ℕ × ℕ → Bool) → Bool) (x5 : List (ℕ × ℕ → Bool)) => List.casesOn x5 Bool.true fun (x6 : ℕ × ℕ → Bool) (x7 : List (ℕ × ℕ → Bool)) => x1.any fun (x8 : ℕ × ℕ) => x6 x8 && x4 (List.filter (fun (x9 : ℕ × ℕ → Bool) => !x9 x8) x7)

theorem key (x1 : List (ℕ × ℕ)) : ∀ (n : ℕ) (xs : List (ℕ × ℕ → Bool)),
    (F x1)^[n] List.isEmpty xs = Bool.true →
    ∃ (x6 : List (ℕ × ℕ)), x6.length ≤ n ∧ (∀ x7 ∈ x6, x7 ∈ x1) ∧ ∀ x7 ∈ xs, x6.any x7 = Bool.true := by
  intro n
  induction n with
  | zero =>
    intro xs h
    simp at h
    subst h
    exact ⟨[], by simp, by simp, by simp⟩
  | succ n ih =>
    intro xs h
    rw [Function.iterate_succ_apply'] at h
    cases xs with
    | nil => exact ⟨[], by simp, by simp, by simp⟩
    | cons p ps =>
      simp only [F, List.any_eq_true, Bool.and_eq_true] at h
      obtain ⟨e, he, hpe, hr⟩ := h
      obtain ⟨S, hl, hS, hq⟩ := ih _ hr
      refine ⟨e :: S, by simp; omega, ?_, ?_⟩
      · intro y hy
        simp at hy
        rcases hy with rfl | hy
        · exact he
        · exact hS y hy
      · intro q hq'
        simp at hq'
        rcases hq' with rfl | hq'
        · simp [hpe]
        · by_cases hqe : q e = Bool.true
          · simp [hqe]
          · have := hq q (by simp [hq', hqe])
            simp [this]

end PEqualNP.Outside.L_meta_8589_aux

theorem PEqualNP.Outside.L_meta_8589 : ∀ (x1 : List (ℕ × ℕ)) (x2 : List (ℕ × ℕ → Bool)) (x3 : ℕ),   have x4 : (List (ℕ × ℕ → Bool) → Bool) → List (ℕ × ℕ → Bool) → Bool := fun (x4 : List (ℕ × ℕ → Bool) → Bool) (x5 : List (ℕ × ℕ → Bool)) => List.casesOn x5 Bool.true fun (x6 : ℕ × ℕ → Bool) (x7 : List (ℕ × ℕ → Bool)) => x1.any fun (x8 : ℕ × ℕ) => x6 x8 && x4 (List.filter (fun (x9 : ℕ × ℕ → Bool) => !x9 x8) x7);   x4^[x3] List.isEmpty x2 = Bool.true → ∃ (x6 : List (ℕ × ℕ)), x6.length ≤ x3 ∧ (∀ x7 ∈ x6, x7 ∈ x1) ∧ ∀ x7 ∈ x2, x6.any x7 = Bool.true := by
  intro x1 x2 x3
  exact PEqualNP.Outside.L_meta_8589_aux.key x1 x3 x2
