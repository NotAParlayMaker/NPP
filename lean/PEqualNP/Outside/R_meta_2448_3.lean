import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2448_3
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' → PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → C.size ≤ C'.size))
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → (∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' → PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → C.size ≤ C'.size) → PEqualNP.EdgeOwnership.HasStarProfile n G C) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6.size ≤ x7.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x6 := by
  intro n G inst htri hquad
  obtain ⟨C, hmono, hfun, hleast⟩ := h1 n G htri hquad
  exact ⟨C, hmono, hfun, hleast, h2 n G C hmono hfun hleast⟩
