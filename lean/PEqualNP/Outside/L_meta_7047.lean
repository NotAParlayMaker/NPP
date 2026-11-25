import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7047

def stp (W : List ℕ) (c : Fin 8192) : List ℕ :=
  W ++ [if c.val < 4096 then W.getD (c.val % 64) 0 &&& W.getD (c.val / 64 % 64) 0
    else W.getD (c.val % 64) 0 ||| W.getD (c.val / 64 % 64) 0]

lemma snoc' (W : List ℕ) (v m : ℕ) (h : m = W.length) : (W ++ [v]).getD m 0 = v := by
  subst h
  simp

lemma stp_eq (W : List ℕ) (c : Fin 8192) : stp W c =
    W ++ [if c.val < 4096 then W.getD (c.val % 64) 0 &&& W.getD (c.val / 64 % 64) 0
      else W.getD (c.val % 64) 0 ||| W.getD (c.val / 64 % 64) 0] := rfl

lemma main (n : ℕ) (l : List ℕ) (f : ℕ → ℕ) (hl : l.length = n)
    (hin : ∀ i < n, l.getD i 0 = f i) :
    ∀ k, n + k ≤ 64 →
      (∀ j < k, ∃ (a b : ℕ) (t : Bool), a < n + j ∧ b < n + j ∧
        f (n + j) = if t = true then f a ||| f b else f a &&& f b) →
      ∃ cs : List (Fin 8192), cs.length = k ∧ (cs.foldl stp l).length = n + k ∧
        ∀ i < n + k, (cs.foldl stp l).getD i 0 = f i := by
  intro k
  induction k with
  | zero =>
    intro _ _
    exact ⟨[], rfl, by simpa using hl, by simpa using hin⟩
  | succ k ih =>
    intro hle hg
    obtain ⟨cs, hlen, hW, hval⟩ := ih (by omega) (fun j hj => hg j (by omega))
    obtain ⟨a, b, t, ha, hb, hf⟩ := hg k (by omega)
    have hc : ∃ c : Fin 8192,
        (if c.val < 4096 then (cs.foldl stp l).getD (c.val % 64) 0 &&&
            (cs.foldl stp l).getD (c.val / 64 % 64) 0
          else (cs.foldl stp l).getD (c.val % 64) 0 |||
            (cs.foldl stp l).getD (c.val / 64 % 64) 0) = f (n + k) := by
      cases t with
      | false =>
        refine ⟨⟨a + 64 * b, by omega⟩, ?_⟩
        have h1 : (a + 64 * b) % 64 = a := by omega
        have h2 : (a + 64 * b) / 64 % 64 = b := by omega
        have h3 : a + 64 * b < 4096 := by omega
        dsimp only
        rw [if_pos h3, h1, h2, hval a (by omega), hval b (by omega), hf]
        simp
      | true =>
        refine ⟨⟨a + 64 * b + 4096, by omega⟩, ?_⟩
        have h1 : (a + 64 * b + 4096) % 64 = a := by omega
        have h2 : (a + 64 * b + 4096) / 64 % 64 = b := by omega
        have h3 : ¬ (a + 64 * b + 4096 < 4096) := by omega
        dsimp only
        rw [if_neg h3, h1, h2, hval a (by omega), hval b (by omega), hf]
        simp
    obtain ⟨c, hcv⟩ := hc
    refine ⟨cs ++ [c], by simp [hlen], ?_, ?_⟩
    · rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [stp_eq]
      rw [List.length_append, hW]
      simp
      omega
    · intro i hi
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases h1 : i < n + k
      · rw [stp_eq]
        rw [List.getD_append _ _ _ _ (by rw [hW]; exact h1)]
        exact hval i h1
      · have hi' : i = n + k := by omega
        subst hi'
        rw [stp_eq]
        rw [snoc' _ _ _ hW.symm]
        exact hcv

end PEqualNP.Outside.L_meta_7047

theorem PEqualNP.Outside.L_meta_7047 : ∀ (x1 x2 : ℕ) (x3 : List ℕ) (x4 : ℕ → ℕ), x3.length = x1 → x1 + x2 ≤ (64 : ℕ) → (∀ x7 < x1, x3.getD x7 (0 : ℕ) = x4 x7) → (∀ x8 < x2, ∃ (x10 : ℕ) (x11 : ℕ) (x12 : Bool), x10 < x1 + x8 ∧ x11 < x1 + x8 ∧ x4 (x1 + x8) = if x12 = Bool.true then x4 x10 ||| x4 x11 else x4 x10 &&& x4 x11) → ∃ (x9 : List (Fin (8192 : ℕ))), x9.length = x2 ∧ ∀ x10 < x1 + x2, (List.foldl (fun (x12 : List ℕ) (x13 : Fin (8192 : ℕ)) => x12 ++ [if ↑x13 < (4096 : ℕ) then x12.getD (↑x13 % (64 : ℕ)) (0 : ℕ) &&& x12.getD (↑x13 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ) else x12.getD (↑x13 % (64 : ℕ)) (0 : ℕ) ||| x12.getD (↑x13 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]) x3 x9).getD x10 (0 : ℕ) = x4 x10 := by
  intro n k l f hl hle hin hg
  obtain ⟨cs, h1, _, h3⟩ := PEqualNP.Outside.L_meta_7047.main n l f hl hin k hle hg
  exact ⟨cs, h1, h3⟩
