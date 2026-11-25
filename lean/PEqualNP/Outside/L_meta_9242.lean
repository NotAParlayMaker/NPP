import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9242_aux

theorem getD_app (L : List ℕ) (a i : ℕ) :
    (L ++ [a]).getD i 0 = if i < L.length then L.getD i 0 else if i = L.length then a else 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem key (x1 : List (Bool × ℕ × ℕ)) (x4 x5 : ℕ) : ∀ (L L' : List ℕ), L.length = L'.length →
    (∀ i, (L.getD i 0).testBit x4 = true → (L'.getD i 0).testBit x5 = true) →
    ∀ i, ((List.foldl (fun (x9 : List ℕ) (x10 : Bool × ℕ × ℕ) => x9 ++ [if x10.1 = true then x9.getD x10.2.1 0 ||| x9.getD x10.2.2 0 else x9.getD x10.2.1 0 &&& x9.getD x10.2.2 0]) L x1).getD i 0).testBit x4 = true →
      ((List.foldl (fun (x9 : List ℕ) (x10 : Bool × ℕ × ℕ) => x9 ++ [if x10.1 = true then x9.getD x10.2.1 0 ||| x9.getD x10.2.2 0 else x9.getD x10.2.1 0 &&& x9.getD x10.2.2 0]) L' x1).getD i 0).testBit x5 = true := by
  induction x1 with
  | nil => intro L L' _ h; simpa using h
  | cons g gs ih =>
    intro L L' hl h
    simp only [List.foldl_cons]
    apply ih
    · simp [hl]
    · intro i hi
      obtain ⟨b, p, q⟩ := g
      have hp := h p
      have hq := h q
      rw [getD_app] at hi ⊢
      rw [← hl]
      by_cases h1 : i < L.length
      · rw [if_pos h1] at hi ⊢
        exact h i hi
      · rw [if_neg h1] at hi ⊢
        by_cases h2 : i = L.length
        · rw [if_pos h2] at hi ⊢
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_land, Bool.and_eq_true] at hi ⊢
            exact ⟨hp hi.1, hq hi.2⟩
          · simp only [↓reduceIte, Nat.testBit_lor, Bool.or_eq_true] at hi ⊢
            rcases hi with hi | hi
            · exact Or.inl (hp hi)
            · exact Or.inr (hq hi)
        · rw [if_neg h2, Nat.zero_testBit] at hi
          exact absurd hi (by simp)

end PEqualNP.Outside.L_meta_9242_aux

theorem PEqualNP.Outside.L_meta_9242 : ∀ (x1 : List (Bool × ℕ × ℕ)) (x2 x3 : List ℕ) (x4 x5 : ℕ), x2.length = x3.length → (∀ (x7 : ℕ), (x2.getD x7 (0 : ℕ)).testBit x4 = Bool.true → (x3.getD x7 (0 : ℕ)).testBit x5 = Bool.true) → ∀ (x8 : ℕ), ((List.foldl (fun (x9 : List ℕ) (x10 : Bool × ℕ × ℕ) => x9 ++ [if x10.1 = Bool.true then x9.getD x10.2.1 (0 : ℕ) ||| x9.getD x10.2.2 (0 : ℕ) else x9.getD x10.2.1 (0 : ℕ) &&& x9.getD x10.2.2 (0 : ℕ)]) x2 x1).getD x8 (0 : ℕ)).testBit x4 = Bool.true → ((List.foldl (fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) => x10 ++ [if x11.1 = Bool.true then x10.getD x11.2.1 (0 : ℕ) ||| x10.getD x11.2.2 (0 : ℕ) else x10.getD x11.2.1 (0 : ℕ) &&& x10.getD x11.2.2 (0 : ℕ)]) x3 x1).getD x8 (0 : ℕ)).testBit x5 = Bool.true := by
  intro x1 x2 x3 x4 x5 hl h x8
  exact PEqualNP.Outside.L_meta_9242_aux.key x1 x4 x5 x2 x3 hl h x8
