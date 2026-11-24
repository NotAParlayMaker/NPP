import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

/-- The general cubic deletion bound reduces to circuits smaller than every cover construction. -/
theorem PEqualNP.Outside.R_meta_2636_3
  (star : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool),
    (∀ v ∉ S, (G.neighborSet v).ncard = 3) →
    (∀ u w, G.Adj u w → u ∉ S) → (∃ u w, G.Adj u w) →
    (∀ x, f x = true ↔ (∃ a ∈ S, x a = true) ∨ ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) →
    ∀ T : Finset (Fin n), (∀ u w, G.Adj u w → u∈T ∨ w∈T) →
      ∃ v ∉ S, ∃ t : ℕ, t+5 ≤ S.card + G.edgeSet.ncard + T.card ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) t)
  (strict : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool),
    (∀ v ∉ S, (G.neighborSet v).ncard = 3) →
    (∀ (p : Fin n) (c : G.Walk p p), c.IsCycle → 7 ≤ c.length) →
    (∀ u w, G.Adj u w → u ∉ S) → (∃ u w, G.Adj u w) →
    (∀ x, f x = true ↔ (∃ a ∈ S, x a = true) ∨ ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) →
    ∀ s : ℕ, HasCircuitSize n f s →
      (∀ T : Finset (Fin n), (∀ u w, G.Adj u w → u∈T ∨ w∈T) → s+1 < S.card + G.edgeSet.ncard + T.card) →
      ∃ v ∉ S, ∃ t : ℕ, t+4 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → (∀ (x9 : Fin x1 → Bool), x4 x9 = Bool.true ↔ (∃ x10 ∈ x3, x9 x10 = Bool.true) ∨ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x10 → ∃ x12 ∉ x3, ∃ (x13 : ℕ), x13 + (4 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x14 : Fin x1 → Bool) => x4 (Function.update x14 x12 Bool.false)) x13
:= by
  intro n G S f hd hg hi he hf s hs
  classical
  by_cases above : ∃ T : Finset (Fin n), (∀ u w, G.Adj u w → u∈T ∨ w∈T) ∧
      S.card+G.edgeSet.ncard+T.card ≤ s+1
  · obtain ⟨T,hT,ht⟩ := above
    obtain ⟨v,hv,t,hcost,hf'⟩ := star n G S f hd hi he hf T hT
    exact ⟨v,hv,t,by omega,hf'⟩
  · apply strict n G S f hd hg hi he hf s hs
    intro T hT
    exact lt_of_not_ge (fun h => above ⟨T,hT,h⟩)
