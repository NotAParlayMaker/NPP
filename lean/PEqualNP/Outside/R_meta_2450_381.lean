import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- For a safe monotone circuit, testing the edge pairs is sufficient for full correctness.
-- Apply the replacement only to the earliest AND gate without an owned edge.
theorem PEqualNP.Outside.R_meta_2450_381
    (testPairs : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      Monotone2 C →
      (∀ x, circuitFun n C x = true → graphFun G ∅ x = true) →
      (∀ u v, G.Adj u v → circuitFun n C (pairInput u v) = true) →
      circuitFun n C = graphFun G ∅)
    (replace : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let owned := fun (D : Circuit) j => ∃ u v, G.Adj u v ∧ Owns n D j u v
      let bad := fun (D : Circuit) j => j < D.size ∧ (gateAt D j).op = .and ∧ ¬ owned D j
      let cost := fun D => {j | bad D j}.ncard
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → HasStarProfile n G C →
      ∀ j, bad C j → (∀ i < j, ¬ bad C i) →
      ∃ D : Circuit, Monotone2 D ∧ HasStarProfile n G D ∧ D.size ≤ C.size ∧
        cost D < cost C ∧
        (∀ x, circuitFun n D x = true → graphFun G ∅ x = true) ∧
        (∀ u v, G.Adj u v → circuitFun n D (pairInput u v) = true)) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) → (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x9 → x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x4.size ≤ x9.size) → PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ PEqualNP.MetaComplexity.circuitFun x1 x11 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x11.size ≤ x4.size ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧ ∀ x12 < x11.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16 := by

  classical
  intro n G inst C triangle four hmono computes least star
  let owned (D : Circuit) j := ∃ u v, G.Adj u v ∧ Owns n D j u v
  let bad (D : Circuit) j := j < D.size ∧ (gateAt D j).op = .and ∧ ¬ owned D j
  let cost (D : Circuit) := {j | bad D j}.ncard
  let candidate k := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧
    D.size ≤ C.size ∧ HasStarProfile n G D ∧ cost D = k
  have available : ∃ k, candidate k := ⟨cost C,C,hmono,computes,le_rfl,star,rfl⟩
  obtain ⟨D,hm,hf,hs,profile,hcost⟩ := Nat.find_spec available
  refine ⟨D,hm,hf,hs,profile,?_⟩
  intro j hj hop
  by_contra noOwner
  have existsBad : ∃ i, bad D i := ⟨j,hj,hop,noOwner⟩
  have isLeast : IsMinimalMonoCircuit n D := by
    refine ⟨hm,?_⟩
    intro E he hE
    exact hs.trans (least E he (hE.trans hf))
  obtain ⟨E,hmE,profileE,hsE,smaller,safe,pairs⟩ :=
    replace n G D triangle four isLeast hf profile (Nat.find existsBad)
      (Nat.find_spec existsBad) (fun _ hi => Nat.find_min existsBad hi)
  have computesE := testPairs n G E hmE safe pairs
  have minimal := Nat.find_min' available
    (show candidate (cost E) from ⟨E,hmE,computesE,hsE.trans hs,profileE,rfl⟩)
  change cost E < cost D at smaller
  omega
