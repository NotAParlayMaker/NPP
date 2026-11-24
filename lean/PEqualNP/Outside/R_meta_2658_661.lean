import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_2658_661
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∃ u v,G.Adj u v) → Monotone2 C → circuitFun n C=graphFun G ∅ →
      ∃ A : Circuit, IsAO2 n A ∧ circuitFun n A=graphFun G ∅ ∧ A.size≤C.size)
    (oneOmission : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Circuit),
      (∃ u v,G.Adj u v) → (∀ a b c d : Fin n, a≠b → a≠c → a≠d → b≠c → b≠d → c≠d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a) →
      IsAO2 n A → circuitFun n A=graphFun G ∅ →
      (∀ u v a b : Fin n, G.Adj u v → G.Adj a b → ¬ (∃ j p q, andOn A j p q ∧ orp A n u.val p ∧ orp A n v.val q ∧ orp A n (n+j) A.output) → ¬ (∃ j p q, andOn A j p q ∧ orp A n a.val p ∧ orp A n b.val q ∧ orp A n (n+j) A.output) → s(u,v)=s(a,b)) → ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧ D.size≤A.size ∧
        ∀ j (g : Gate),D.gates[j]?=some g → g.op=.and →
          ∀ x : Fin n→Bool,(D.wires (List.ofFn x)).getD (n+j) false=true → D.eval (List.ofFn x)=true)
    (multipleOmissions : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Circuit),
      (∃ u v,G.Adj u v) → (∀ a b c d : Fin n, a≠b → a≠c → a≠d → b≠c → b≠d → c≠d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a) →
      IsAO2 n A → circuitFun n A=graphFun G ∅ →
      (¬ (∀ u v a b : Fin n, G.Adj u v → G.Adj a b → ¬ (∃ j p q, andOn A j p q ∧ orp A n u.val p ∧ orp A n v.val q ∧ orp A n (n+j) A.output) → ¬ (∃ j p q, andOn A j p q ∧ orp A n a.val p ∧ orp A n b.val q ∧ orp A n (n+j) A.output) → s(u,v)=s(a,b))) → ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧ D.size≤A.size ∧
        ∀ j (g : Gate),D.gates[j]?=some g → g.op=.and →
          ∀ x : Fin n→Bool,(D.wires (List.ofFn x)).getD (n+j) false=true → D.eval (List.ofFn x)=true) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) ∧ x8.size ≤ x3.size ∧ ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x8.gates[x9]? = Option.some x10 → x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1 → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x9) Bool.false = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ x13 x15 = Bool.true ∧ x13 x16 = Bool.true := by
  classical
  intro n G C edge noFour model computes
  have graphTruth (x : Fin n→Bool) : graphFun G ∅ x=true ↔
      ∃ u v,G.Adj u v ∧ x u=true ∧ x v=true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)),x a=true) ||
      decide (∃ u v,G.Adj u v ∧ x u=true ∧ x v=true))=true ↔ _
    simp
  have law : circuitFun n C=graphFun G ∅ := by
    funext x
    exact Bool.eq_iff_iff.mpr ((computes x).trans
      (graphTruth x).symm)
  obtain ⟨A,ok,correct,small⟩ := normalize n G C edge model law
  have normalized : ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧ D.size≤A.size ∧
        ∀ j (g : Gate),D.gates[j]?=some g → g.op=.and →
          ∀ x : Fin n→Bool,(D.wires (List.ofFn x)).getD (n+j) false=true → D.eval (List.ofFn x)=true := by
    by_cases threshold : ∀ u v a b : Fin n, G.Adj u v → G.Adj a b → ¬ (∃ j p q, andOn A j p q ∧ orp A n u.val p ∧ orp A n v.val q ∧ orp A n (n+j) A.output) → ¬ (∃ j p q, andOn A j p q ∧ orp A n a.val p ∧ orp A n b.val q ∧ orp A n (n+j) A.output) → s(u,v)=s(a,b)
    · exact oneOmission n G A edge noFour ok correct threshold
    · exact multipleOmissions n G A edge noFour ok correct threshold
  obtain ⟨D,monotone,semantics,budget,sound⟩ := normalized
  have values (x : Fin n→Bool) : D.eval (List.ofFn x)=graphFun G ∅ x := congrFun semantics x
  refine ⟨D,monotone,fun x=>?_,budget.trans small,fun j g slot op x on=>?_⟩
  · rw [values]
    exact graphTruth x
  · have out := sound j g slot op x on
    rw [values] at out
    exact (graphTruth x).mp out
