import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

-- Start with a least circuit in top form. Handle a single dirty AND gate directly;
-- with several, the induction needs only a smaller count at equal minimum size.
theorem PEqualNP.Outside.R_meta_2658_1
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size ≤ C.size)
    (one : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      (junk G C).card = 1 →
      ∃ D : Circuit, IsLeastAO G D ∧ (junk G D).card = 0)
    (many : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      2 ≤ (junk G C).card →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ (junk G D).card < (junk G C).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) →
      PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) →
      ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) ∧
        x8.size ≤ x3.size ∧ ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x8.gates[x9]? = Option.some x10 →
          x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1 → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x9) Bool.false = Bool.true →
            ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ x13 x15 = Bool.true ∧ x13 x16 = Bool.true := by
  classical
  intro n G C nonempty noCycle monotone computes
  have edges : G.edgeFinset.Nonempty := by
    obtain ⟨u, v, huv⟩ := nonempty
    exact ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr huv⟩
  have noFour : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro u hu v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    by_contra huv
    exact noCycle a u b v hu.1.ne hab hv.1.ne hu.2.ne.symm huv hv.2.ne
      hu.1 hu.2.symm hv.2 hv.1.symm
  have graphSpec (x : Fin n → Bool) :
      graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp
  have computesGraph : circuitFun n C = graphFun G ∅ := by
    funext x
    exact Bool.eq_iff_iff.mpr ((computes x).trans (graphSpec x).symm)
  obtain ⟨D, leastD, topD, sizeD⟩ := normalize n G C edges monotone computesGraph
  let feasible (k : ℕ) : Prop :=
    ∃ A : Circuit, IsLeastAO G A ∧ TopForm G A ∧ (junk G A).card = k
  have existsFeasible : ∃ k, feasible k := ⟨(junk G D).card, D, leastD, topD, rfl⟩
  obtain ⟨B, leastB, topB, countB⟩ := Nat.find_spec existsFeasible
  have clean : ∃ E : Circuit, IsLeastAO G E ∧ (junk G E).card = 0 := by
    by_cases zero : (junk G B).card = 0
    · exact ⟨B, leastB, zero⟩
    by_cases single : (junk G B).card = 1
    · exact one n G B noFour edges leastB topB single
    obtain ⟨A, leastA, topA, smaller⟩ := many n G B noFour edges leastB topB (by omega)
    have minimum : Nat.find existsFeasible ≤ (junk G A).card :=
      Nat.find_min' existsFeasible (show feasible _ from ⟨A, leastA, topA, rfl⟩)
    exact False.elim ((not_lt_of_ge minimum) (countB ▸ smaller))
  obtain ⟨E, leastE, emptyE⟩ := clean
  have sizeE : E.size ≤ D.size := leastE.2.2 D leastD.1 leastD.2.1
  refine ⟨E, ?_, ?_, sizeE.trans sizeD, ?_⟩
  · intro g hg
    obtain ⟨allowed, _, binary⟩ := leastE.1
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using allowed g hg,
      le_of_eq (binary g hg)⟩
  · intro x
    change circuitFun n E x = true ↔ _
    rw [leastE.2.1]
    exact graphSpec x
  · intro i g hget hop x hval
    by_contra noEdge
    have hi : i < E.gates.length := by
      by_contra! outOfRange
      rw [List.getElem?_eq_none outOfRange] at hget
      contradiction
    have hgate : gateAt E i = g := by
      change E.gates.getD i _ = _
      rw [List.getD_eq_getElem?_getD, hget]
      rfl
    have hfalse : graphFun G ∅ x = false :=
      Bool.eq_false_of_not_eq_true (fun htrue => noEdge ((graphSpec x).mp htrue))
    have dirty : IsDirtyAnd n G E i :=
      ⟨(congrArg Gate.op hgate).trans hop, hi, x, hval, hfalse⟩
    have hmem : i ∈ junk G E := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, dirty⟩
    rw [Finset.card_eq_zero.mp emptyE] at hmem
    exact Finset.notMem_empty i hmem
