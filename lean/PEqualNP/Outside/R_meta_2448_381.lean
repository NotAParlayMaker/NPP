import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A triangle-free intersecting family of edges has a common vertex.
-- Minimize the number of gates with a disjoint owned pair among circuits of least size.
theorem PEqualNP.Outside.R_meta_2448_381
    (overlapStar : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (R : Fin n → Fin n → Prop),
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b, R a b → G.Adj a b) →
      (∀ a b c d, R a b → R c d → a = c ∨ a = d ∨ b = c ∨ b = d) →
      (∀ a b, ¬ R a b) ∨ ∃ c, ∀ a b, R a b → a = c ∨ b = c)
    (existsCircuit : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅)
    (exchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let conflict (D : Circuit) (j : ℕ) :=
        ∃ a b c d, G.Adj a b ∧ Owns n D j a b ∧ G.Adj c d ∧ Owns n D j c d ∧
          ¬ (a = c ∨ a = d ∨ b = c ∨ b = d)
      let cost (D : Circuit) := {j | conflict D j}.ncard
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ j, conflict C j → (∀ i < j, ¬ conflict C i) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧ cost D < cost C) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6.size ≤ x7.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x6 := by

  classical
  intro n G inst triangle four
  let sizeOk k := ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ C.size = k
  obtain ⟨C₀,mono₀,eval₀⟩ := existsCircuit n G
  have someSize : ∃ k, sizeOk k := ⟨C₀.size,C₀,mono₀,eval₀,rfl⟩
  let conflict (D : Circuit) (j : ℕ) :=
    ∃ a b c d, G.Adj a b ∧ Owns n D j a b ∧ G.Adj c d ∧ Owns n D j c d ∧
      ¬ (a = c ∨ a = d ∨ b = c ∨ b = d)
  let cost (D : Circuit) := {j | conflict D j}.ncard
  let costOk k := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
    D.size = Nat.find someSize ∧ cost D = k
  obtain ⟨E,monoE,evalE,sizeE⟩ := Nat.find_spec someSize
  have someCost : ∃ k, costOk k := ⟨cost E,E,monoE,evalE,sizeE,rfl⟩
  obtain ⟨C,mono,eval,size,leastCost⟩ := Nat.find_spec someCost
  have least (D : Circuit) (m : Monotone2 D) (e : circuitFun n D = graphFun G ∅) :
      C.size ≤ D.size := by
    rw [size]
    exact Nat.find_min' someSize (show sizeOk D.size from ⟨D,m,e,rfl⟩)
  have noConflict : ∀ j, ¬ conflict C j := by
    intro j hj
    have someConflict : ∃ i, conflict C i := ⟨j,hj⟩
    have minimal : IsMinimalMonoCircuit n C := ⟨mono, fun D m e => least D m (e.trans eval)⟩
    obtain ⟨D,m,e,budget,drop⟩ :=
      exchange n G C triangle four minimal eval (Nat.find someConflict)
        (Nat.find_spec someConflict) (fun _ h => Nat.find_min someConflict h)
    have sizeD := (le_antisymm budget (least D m e)).trans size
    have lower := Nat.find_min' someCost (show costOk (cost D) from ⟨D,m,e,sizeD,rfl⟩)
    change cost D < cost C at drop
    omega
  refine ⟨C,mono,eval,least,?_⟩
  intro j _ _
  obtain empty | ⟨v,center⟩ := overlapStar n G (fun a b => G.Adj a b ∧ Owns n C j a b)
    triangle (fun _ _ h => h.1) (by
      intro a b c d h₁ h₂
      by_contra disjoint
      exact noConflict j ⟨a,b,c,d,h₁.1,h₁.2,h₂.1,h₂.2,disjoint⟩)
  · exact Or.inl (fun a b h own => empty a b ⟨h,own⟩)
  · exact Or.inr ⟨v,fun a b h own => center a b ⟨h,own⟩⟩
