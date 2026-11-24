import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2448_661
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C ∧ PEqualNP.TopForm.TopForm G C ∧
        ∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 E →
          PEqualNP.MetaComplexity.circuitFun n E = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
          C.size ≤ E.size)
    (small : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 E →
          PEqualNP.MetaComplexity.circuitFun n E = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
          C.size ≤ E.size) →
        (∀ i j, PEqualNP.ReadTwo.isAnd C i → ¬PEqualNP.ReadTwo.orp C n (n + i) C.output →
          PEqualNP.ReadTwo.isAnd C j → ¬PEqualNP.ReadTwo.orp C n (n + j) C.output → i = j) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
          PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
          D.size ≤ C.size ∧ PEqualNP.EdgeOwnership.HasStarProfile n G D)
    (large : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 E →
          PEqualNP.MetaComplexity.circuitFun n E = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
          C.size ≤ E.size) →
        (∃ i j, PEqualNP.ReadTwo.isAnd C i ∧ ¬PEqualNP.ReadTwo.orp C n (n + i) C.output ∧
          PEqualNP.ReadTwo.isAnd C j ∧ ¬PEqualNP.ReadTwo.orp C n (n + j) C.output ∧ i ≠ j) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
          PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
          D.size ≤ C.size ∧ PEqualNP.EdgeOwnership.HasStarProfile n G D) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6.size ≤ x7.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x6 := by
  intro n G _ triangle four
  have no4 : PEqualNP.TopForm.NoFourCycle G := by
    intro a b distinct
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨_,aU,bU⟩ := Finset.mem_filter.mp hu
    obtain ⟨_,aV,bV⟩ := Finset.mem_filter.mp hv
    exact (four a u b v aU bU.symm bV aV.symm).resolve_left distinct
  obtain ⟨C,least,top,minimum⟩ := normalize n G
  have witness :
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        D.size ≤ C.size ∧ PEqualNP.EdgeOwnership.HasStarProfile n G D := by
    classical
    by_cases many : ∃ i j, PEqualNP.ReadTwo.isAnd C i ∧ ¬PEqualNP.ReadTwo.orp C n (n + i) C.output ∧
        PEqualNP.ReadTwo.isAnd C j ∧ ¬PEqualNP.ReadTwo.orp C n (n + j) C.output ∧ i ≠ j
    · exact large n G triangle no4 C least top minimum many
    · apply small n G triangle no4 C least top minimum
      intro i j andI internalI andJ internalJ
      by_contra unequal
      exact many ⟨i,j,andI,internalI,andJ,internalJ,unequal⟩
  obtain ⟨D,mono,sem,paid,profile⟩ := witness
  exact ⟨D,mono,sem,fun E model same => paid.trans (minimum E model same),profile⟩
