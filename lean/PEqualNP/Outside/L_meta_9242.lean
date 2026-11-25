import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9242
open PEqualNP.CircuitLowerBounds



def stp (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) : List ℕ :=
  x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]

theorem mono : ∀ (l : List (Bool × ℕ × ℕ)) (U V : List ℕ) (a b : ℕ), U.length = V.length →
    (∀ i, (U.getD i 0).testBit a = true → (V.getD i 0).testBit b = true) →
    ∀ i, ((l.foldl stp U).getD i 0).testBit a = true → ((l.foldl stp V).getD i 0).testBit b = true := by
  intro l
  induction l with
  | nil => intro U V a b _ h i; exact h i
  | cons s l ih =>
    intro U V a b hl h i
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · simp [stp, hl]
    · intro k
      unfold stp
      rcases Nat.lt_trichotomy k U.length with hk | hk | hk
      · have hk' : k < V.length := hl ▸ hk
        rw [List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ hk']
        exact h k
      · have e1 : ∀ x : ℕ, (U ++ [x]).getD k 0 = x := by intro x; subst hk; simp
        have e2 : ∀ x : ℕ, (V ++ [x]).getD k 0 = x := by intro x; rw [hk, hl]; simp
        rw [e1, e2]
        by_cases hs : s.1 = true
        · rw [if_pos hs, if_pos hs, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true]
          rintro (h1 | h1)
          · exact Or.inl (h _ h1)
          · exact Or.inr (h _ h1)
        · rw [if_neg hs, if_neg hs, Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true]
          rintro ⟨h1, h2⟩
          exact ⟨h _ h1, h _ h2⟩
      · have e1 : ∀ x : ℕ, (U ++ [x]).getD k 0 = 0 := by
          intro x; apply List.getD_eq_default; simp; omega
        rw [e1]
        intro h0
        simp at h0

end PEqualNP.Outside.L_meta_9242

open PEqualNP.Outside.L_meta_9242 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9242 : ∀ (x1 : List (Bool × ℕ × ℕ)) (x2 x3 : List ℕ) (x4 x5 : ℕ), x2.length = x3.length → (∀ (x7 : ℕ), (x2.getD x7 (0 : ℕ)).testBit x4 = Bool.true → (x3.getD x7 (0 : ℕ)).testBit x5 = Bool.true) → ∀ (x8 : ℕ), ((List.foldl (fun (x9 : List ℕ) (x10 : Bool × ℕ × ℕ) => x9 ++ [if x10.1 = Bool.true then x9.getD x10.2.1 (0 : ℕ) ||| x9.getD x10.2.2 (0 : ℕ) else x9.getD x10.2.1 (0 : ℕ) &&& x9.getD x10.2.2 (0 : ℕ)]) x2 x1).getD x8 (0 : ℕ)).testBit x4 = Bool.true → ((List.foldl (fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) => x10 ++ [if x11.1 = Bool.true then x10.getD x11.2.1 (0 : ℕ) ||| x10.getD x11.2.2 (0 : ℕ) else x10.getD x11.2.1 (0 : ℕ) &&& x10.getD x11.2.2 (0 : ℕ)]) x3 x1).getD x8 (0 : ℕ)).testBit x5 = Bool.true := by
  intro x1 x2 x3 x4 x5 hl h
  exact mono x1 x2 x3 x4 x5 hl h
