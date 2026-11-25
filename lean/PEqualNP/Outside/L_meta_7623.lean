import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7623
open PEqualNP.CircuitLowerBounds



theorem sn_ne (L : List ℕ) (s : ℕ) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [s]).getD j 0 = L.getD j 0 := by
  by_cases hj : j < L.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem sn_eq (L : List ℕ) (s : ℕ) : (L ++ [s]).getD L.length 0 = s := by
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_7623

open PEqualNP.Outside.L_meta_7623 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7623 : have x1 : List ℕ → ℕ → List ℕ := fun (x1 : List ℕ) (x2 : ℕ) => x1 ++ [if x2 < (4096 : ℕ) then x1.getD (x2 % (64 : ℕ)) (0 : ℕ) &&& x1.getD (x2 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ) else x1.getD (x2 % (64 : ℕ)) (0 : ℕ) ||| x1.getD (x2 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]; ∀ (x2 x3 : List ℕ) (x4 : List (Fin (8192 : ℕ))) (x5 x6 : ℕ), x2.length = x3.length → (∀ (x8 : ℕ), (x2.getD x8 (0 : ℕ)).testBit x5 = Bool.true → (x3.getD x8 (0 : ℕ)).testBit x6 = Bool.true) → ∀ (x9 : ℕ), ((List.foldl x1 x2 (List.map Fin.val x4)).getD x9 (0 : ℕ)).testBit x5 = Bool.true → ((List.foldl x1 x3 (List.map Fin.val x4)).getD x9 (0 : ℕ)).testBit x6 = Bool.true := by
  intro f U V cs a b hlen h
  have key : ∀ (l : List ℕ) (U V : List ℕ), U.length = V.length →
      (∀ i, (U.getD i 0).testBit a = true → (V.getD i 0).testBit b = true) →
      ∀ i, ((List.foldl f U l).getD i 0).testBit a = true →
        ((List.foldl f V l).getD i 0).testBit b = true := by
    intro l
    induction l with
    | nil => intro U V _ h i hi; exact h i hi
    | cons c t ih =>
      intro U V hl h
      rw [List.foldl_cons, List.foldl_cons]
      apply ih _ _ (by simp [f, hl])
      intro i hi
      simp only [f] at hi ⊢
      rcases Nat.lt_trichotomy i U.length with h1 | h1 | h1
      · rw [sn_ne _ _ _ (by omega)] at hi
        rw [sn_ne _ _ _ (by omega)]
        exact h i hi
      · subst h1
        rw [sn_eq] at hi
        rw [hl, sn_eq]
        split at hi
        · rename_i hc
          rw [if_pos hc]
          rw [Nat.testBit_and, Bool.and_eq_true] at hi ⊢
          exact ⟨h _ hi.1, h _ hi.2⟩
        · rename_i hc
          rw [if_neg hc]
          rw [Nat.testBit_or, Bool.or_eq_true] at hi ⊢
          exact hi.imp (h _) (h _)
      · rw [sn_ne _ _ _ (by omega)] at hi
        rw [sn_ne _ _ _ (by omega)]
        exact h i hi
  exact key _ U V hlen h
