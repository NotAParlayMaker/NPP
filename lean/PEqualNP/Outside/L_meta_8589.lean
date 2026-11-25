import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8589

theorem key (x1 : List (ℕ × ℕ))
    (F : (List (ℕ × ℕ → Bool) → Bool) → List (ℕ × ℕ → Bool) → Bool)
    (hcons : ∀ g h t, F g (h :: t) = x1.any (fun p => h p && g (t.filter fun k => !k p))) :
    ∀ (n : ℕ) (x2 : List (ℕ × ℕ → Bool)), F^[n] List.isEmpty x2 = true →
      ∃ x6 : List (ℕ × ℕ), x6.length ≤ n ∧ (∀ x7 ∈ x6, x7 ∈ x1) ∧ ∀ x7 ∈ x2, x6.any x7 = true := by
  intro n
  induction n with
  | zero =>
    intro x2 h
    cases x2 with
    | nil => exact ⟨[], by simp, by simp, by simp⟩
    | cons hd tl => simp at h
  | succ n ih =>
    intro x2 h
    rw [Function.iterate_succ_apply'] at h
    cases x2 with
    | nil => exact ⟨[], by simp, by simp, by simp⟩
    | cons hd tl =>
      rw [hcons, List.any_eq_true] at h
      obtain ⟨p, hp, hpp⟩ := h
      rw [Bool.and_eq_true] at hpp
      obtain ⟨h1, h2⟩ := hpp
      obtain ⟨s, hs1, hs2, hs3⟩ := ih _ h2
      refine ⟨p :: s, by simp only [List.length_cons]; omega, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hp
        · exact hs2 x hx
      · intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · simp [h1]
        · by_cases hkp : k p = true
          · simp [hkp]
          · have hmem : k ∈ tl.filter (fun k => !k p) := by
              rw [List.mem_filter]
              exact ⟨hk, by simpa using hkp⟩
            have := hs3 k hmem
            simp [this]

end PEqualNP.Outside.L_meta_8589

theorem PEqualNP.Outside.L_meta_8589 : ∀ (x1 : List (ℕ × ℕ)) (x2 : List (ℕ × ℕ → Bool)) (x3 : ℕ),   have x4 : (List (ℕ × ℕ → Bool) → Bool) → List (ℕ × ℕ → Bool) → Bool := fun (x4 : List (ℕ × ℕ → Bool) → Bool) (x5 : List (ℕ × ℕ → Bool)) => List.casesOn x5 Bool.true fun (x6 : ℕ × ℕ → Bool) (x7 : List (ℕ × ℕ → Bool)) => x1.any fun (x8 : ℕ × ℕ) => x6 x8 && x4 (List.filter (fun (x9 : ℕ × ℕ → Bool) => !x9 x8) x7);   x4^[x3] List.isEmpty x2 = Bool.true → ∃ (x6 : List (ℕ × ℕ)), x6.length ≤ x3 ∧ (∀ x7 ∈ x6, x7 ∈ x1) ∧ ∀ x7 ∈ x2, x6.any x7 = Bool.true := by
  intro x1 x2 x3
  exact PEqualNP.Outside.L_meta_8589.key x1 _ (fun g h t => rfl) x3 x2
