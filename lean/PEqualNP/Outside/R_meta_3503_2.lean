import Mathlib.Data.Fin.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- A vertex cover assigns each incidence to exactly one star.
-- The construction charges the incidence count plus the number of chosen vertices minus one.
theorem PEqualNP.Outside.R_meta_3503_2
    (construct :
    ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I],
    let target := fun x : Fin (n+m) → Bool => decide (∃ a b, I a b ∧
      x (a.castAdd m) = true ∧ x (b.natAdd n) = true)
    let edges := Fintype.card { e : Fin n × Fin m // I e.1 e.2 }
    let cover (A : Finset (Fin n)) (B : Finset (Fin m)) := ∀ a b, I a b → a ∈ A ∨ b ∈ B
    ∀ A B, cover A B → ∃ (D : Circuit) (P L : Finset ℕ),
      IsAO2 (n+m) D ∧ circuitFun (n+m) D = target ∧ D.size ≤ edges + A.card + B.card - 1 ∧
      (let side (k : Bool) := if k then P else L
       ∀ k w, w ∈ side k → (if k then w < n else n ≤ w ∧ w < n+m) ∨
         ∃ j < D.gates.length, w = n+m+j ∧ (gateAt D j).op = .or ∧
           ∀ v ∈ (gateAt D j).inputs, v ∈ side k) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and → ∃ a b,
        (gateAt D j).inputs = [a,b] ∧ (a ∈ P ∧ b ∈ L ∨ a ∈ L ∧ b ∈ P))
    (starForest :
    ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I],
    let target := fun x : Fin (n+m) → Bool => decide (∃ a b, I a b ∧
      x (a.castAdd m) = true ∧ x (b.natAdd n) = true)
    let edges := Fintype.card { e : Fin n × Fin m // I e.1 e.2 }
    let cover (A : Finset (Fin n)) (B : Finset (Fin m)) := ∀ a b, I a b → a ∈ A ∨ b ∈ B
    let internal := ∃ a b, I a b ∧
      (∃ q r, q ≠ r ∧ I a q ∧ I a r) ∧ (∃ u v, u ≠ v ∧ I u b ∧ I v b)
    ∀ C : Circuit, IsAO2 (n+m) C → circuitFun (n+m) C = target → ¬internal →
    ∃ A B, cover A B ∧ edges + A.card + B.card ≤ C.size+1)
    (lower :
    ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I],
    let target := fun x : Fin (n+m) → Bool => decide (∃ a b, I a b ∧
      x (a.castAdd m) = true ∧ x (b.natAdd n) = true)
    let edges := Fintype.card { e : Fin n × Fin m // I e.1 e.2 }
    let cover (A : Finset (Fin n)) (B : Finset (Fin m)) := ∀ a b, I a b → a ∈ A ∨ b ∈ B
    let internal := ∃ a b, I a b ∧
      (∃ q r, q ≠ r ∧ I a q ∧ I a r) ∧ (∃ u v, u ≠ v ∧ I u b ∧ I v b)
    ∀ C : Circuit, (∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬(I a b ∧ I a b' ∧ I a' b ∧ I a' b')) → IsAO2 (n+m) C → circuitFun (n+m) C = target →
      internal →
    ∃ A B, cover A B ∧ edges + A.card + B.card ≤ C.size+1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ (x15 ∈ x10 ∧ x16 ∈ x11 ∨ x15 ∈ x11 ∧ x16 ∈ x10) := by
  intro n m I _ C noSquare valid computes
  have eq : circuitFun (n+m) C = _ := funext computes
  have budget : ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
      (∀ a b, I a b → a ∈ A ∨ b ∈ B) ∧
      Fintype.card {e : Fin n × Fin m // I e.1 e.2} + A.card + B.card ≤ C.size+1 := by
    by_cases h : ∃ a b, I a b ∧
        (∃ q r, q ≠ r ∧ I a q ∧ I a r) ∧ (∃ u v, u ≠ v ∧ I u b ∧ I v b)
    · exact lower n m I C noSquare valid eq h
    · exact starForest n m I C valid eq h
  obtain ⟨A,B,covers,budget⟩ := budget
  obtain ⟨D,P,L,shape,eval,cost,lanes,gates⟩ := construct n m I A B covers
  refine ⟨D,P,L,shape,congrFun eval,?_,?_,?_,gates⟩
  · omega
  · exact lanes true
  · exact lanes false
