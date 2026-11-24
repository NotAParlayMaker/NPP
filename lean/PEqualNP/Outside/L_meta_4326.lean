import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- L-meta-4326. The statement is a pure unfolding: the desk's predicate on subsets of the
-- 42 points and lines of the plane of order 4 says that the subset is independent and that
-- every element outside it is incident with a member of it, and the conclusion spells that
-- out as two halves. No counting, no incidence fact, and no use of the particular difference
-- set is needed.

theorem PEqualNP.Outside.L_meta_4326 :
  have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : Fin (42 : ℕ) → Bool), x2 x3 ↔ (∀ (x4 x5 : Fin (42 : ℕ)), x3 x4 = Bool.true → x3 x5 = Bool.true → ¬x1 x4 x5) ∧ ∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.false → ∃ (x6 : Fin (42 : ℕ)), x3 x6 = Bool.true ∧ (x1 x4 x6 ∨ x1 x6 x4) := by
  intro R P S
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b ha hb
      have h1 := (h a).1 ha
      exact fun hab => h1 b hb (Or.inl hab)
    · intro a ha
      by_contra hno
      have hc : ∀ b, S b = Bool.true → ¬(R a b ∨ R b a) := by
        intro b hb hinc
        exact hno ⟨b, hb, hinc⟩
      have htrue : S a = Bool.true := (h a).2 hc
      rw [ha] at htrue
      exact Bool.noConfusion htrue
  · intro h a
    constructor
    · intro ha b hb
      have h1 := h.1 a b ha hb
      have h2 := h.1 b a hb ha
      exact fun hinc => hinc.elim h1 h2
    · intro hc
      by_contra hS
      have hfalse : S a = Bool.false := by
        cases hv : S a with
        | false => rfl
        | true => exact absurd hv hS
      obtain ⟨b, hb, hinc⟩ := h.2 a hfalse
      exact hc b hb hinc
