import Mathlib.Combinatorics.SimpleGraph.Finite
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Reduce the C4-free monotone edge-function lower bound to TopForm normalization
-- and the combined AND-gate plus OR-gate count with and without dirty AND gates.
theorem PEqualNP.Outside.R_meta_612_47 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      NoFourCycle G → G.edgeFinset.Nonempty →
      ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size ≤ C.size) →
    (∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty →
      (∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) →
      IsLeastAO G D → TopForm G D → junk G D = ∅ →
      G.edgeFinset.card + t ≤
        (tops G D).card + (orT G D).card + (orN G D).card + 1) →
    (∀ (n t : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty →
      (∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card) →
      IsLeastAO G D → TopForm G D → (junk G D).Nonempty →
      G.edgeFinset.card + t ≤
        (tops G D).card + (junk G D).card + (orT G D).card + (orN G D).card + 1) →
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  intro normalize cleanCase dirtyCase n t G C hedge hno4 hexCover hminCover hmono heval
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  letI : DecidableEq GateOp := gateOpDecEq
  have hNoFour : NoFourCycle G := by
    intro a b hab
    by_contra hgt
    have h1lt : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card := by omega
    exact Exists.elim (Finset.one_lt_card.mp h1lt) fun w1 hw1_rest =>
      Exists.elim hw1_rest.2 fun w2 hw2_rest =>
        have hw1 := (Finset.mem_filter.mp hw1_rest.1).2
        have hw2 := (Finset.mem_filter.mp hw2_rest.1).2
        hno4 a w1 b w2 hw1.1.ne hab hw2.1.ne hw1.2.ne.symm hw2_rest.2 hw2.2.ne
          hw1.1 hw1.2.symm hw2.2 hw2.1.symm
  have hNonempty : G.edgeFinset.Nonempty :=
    Exists.elim hedge fun u hu => Exists.elim hu fun v huv => ⟨s(u, v), G.mem_edgeFinset.mpr huv⟩
  have hFun : circuitFun n C = graphFun G ∅ := by
    funext x
    change C.eval (List.ofFn x) =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    have hempty : decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) = false := by simp
    rw [hempty, Bool.false_or]
    by_cases hx : ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true
    · rw [(heval x).mpr hx]
      exact (decide_eq_true hx).symm
    · have hcf : C.eval (List.ofFn x) = false :=
        Bool.eq_false_iff.mpr fun ht => hx ((heval x).mp ht)
      rw [hcf]
      exact (decide_eq_false hx).symm
  exact Exists.elim (normalize n G hNoFour hNonempty C hmono hFun) fun D hD => by
    have hLeast : IsLeastAO G D := hD.1
    have hTop : TopForm G D := hD.2.1
    have hSizeLe : D.size ≤ C.size := hD.2.2
    have hAO : AndOrOnly D := hLeast.1.1
    have hGateOp : ∀ j < D.gates.length,
        (gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or := by
      intro j hj
      have hget : gateAt D j = D.gates[j] := List.getD_eq_getElem _ _ hj
      rw [hget]
      exact hAO D.gates[j] (List.getElem_mem hj)
    have hJunkIff : ∀ j < D.gates.length,
        IsDirtyAnd n G D j ↔ (gateAt D j).op = GateOp.and ∧ ¬ BelowF G D j := by
      intro j hj
      change ((gateAt D j).op = GateOp.and ∧
          (j < D.gates.length ∧ ∃ x : Fin n → Bool, gateVal n D j x = true ∧ graphFun G ∅ x = false)) ↔
        (gateAt D j).op = GateOp.and ∧ ¬ (∀ x : Fin n → Bool, gateVal n D j x = true → graphFun G ∅ x = true)
      refine ⟨fun h => ⟨h.1, fun hb => Exists.elim h.2.2 fun x hx => by
          have hgx := hb x hx.1
          rw [hgx] at hx
          exact Bool.noConfusion hx.2⟩,
        fun h => ⟨h.1, hj, ?_⟩⟩
      by_contra hno
      apply h.2
      intro x hx
      by_contra hnot
      exact hno ⟨x, hx, Bool.eq_false_iff.mpr hnot⟩
    have mem_tops : ∀ j, j ∈ tops G D ↔ j < D.gates.length ∧ ((gateAt D j).op = GateOp.and ∧ BelowF G D j) :=
      fun _ => Finset.mem_filter.trans (and_congr_left' Finset.mem_range)
    have mem_junk : ∀ j, j ∈ junk G D ↔ j < D.gates.length ∧ IsDirtyAnd n G D j :=
      fun _ => Finset.mem_filter.trans (and_congr_left' Finset.mem_range)
    have mem_orT : ∀ j, j ∈ orT G D ↔ j < D.gates.length ∧ ((gateAt D j).op = GateOp.or ∧ BelowF G D j) :=
      fun _ => Finset.mem_filter.trans (and_congr_left' Finset.mem_range)
    have mem_orN : ∀ j, j ∈ orN G D ↔ j < D.gates.length ∧ ((gateAt D j).op = GateOp.or ∧ ¬ BelowF G D j) :=
      fun _ => Finset.mem_filter.trans (and_congr_left' Finset.mem_range)
    have hDisj1 : Disjoint (tops G D) (junk G D) := by
      refine Finset.disjoint_left.mpr (fun j h1 h2 => ?_)
      have a1 := (mem_tops j).mp h1
      have a2 := (mem_junk j).mp h2
      exact ((hJunkIff j a1.1).mp a2.2).2 a1.2.2
    have hDisj2 : Disjoint (orT G D) (orN G D) := by
      refine Finset.disjoint_left.mpr (fun j h1 h2 => ?_)
      exact ((mem_orN j).mp h2).2.2 ((mem_orT j).mp h1).2.2
    have hDisjAO : Disjoint (tops G D ∪ junk G D) (orT G D ∪ orN G D) := by
      refine Finset.disjoint_left.mpr (fun j h1 h2 => ?_)
      have hand : (gateAt D j).op = GateOp.and :=
        (Finset.mem_union.mp h1).elim
          (fun h => ((mem_tops j).mp h).2.1)
          (fun h => ((mem_junk j).mp h).2.1)
      have hor : (gateAt D j).op = GateOp.or :=
        (Finset.mem_union.mp h2).elim
          (fun h => ((mem_orT j).mp h).2.1)
          (fun h => ((mem_orN j).mp h).2.1)
      rw [hand] at hor
      exact GateOp.noConfusion hor
    have hUnion : (tops G D ∪ junk G D) ∪ (orT G D ∪ orN G D) = Finset.range D.gates.length := by
      ext j
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_range,
          mem_tops j, mem_junk j, mem_orT j, mem_orN j]
      constructor
      · intro h
        exact h.elim
          (fun hL => hL.elim (fun x => x.1) (fun x => x.1))
          (fun hR => hR.elim (fun x => x.1) (fun x => x.1))
      · intro hj
        exact (hGateOp j hj).elim
          (fun hand =>
            if hb : BelowF G D j then Or.inl (Or.inl ⟨hj, hand, hb⟩)
            else Or.inl (Or.inr ⟨hj, (hJunkIff j hj).mpr ⟨hand, hb⟩⟩))
          (fun hor =>
            if hb : BelowF G D j then Or.inr (Or.inl ⟨hj, hor, hb⟩)
            else Or.inr (Or.inr ⟨hj, hor, hb⟩))
    have hPart : (tops G D).card + (junk G D).card + (orT G D).card + (orN G D).card = D.size := by
      have c1 := Finset.card_union_of_disjoint hDisjAO
      have c2 := Finset.card_union_of_disjoint hDisj1
      have c3 := Finset.card_union_of_disjoint hDisj2
      rw [hUnion, Finset.card_range, c2, c3] at c1
      have hds : D.size = D.gates.length := rfl
      omega
    have hEdgeCard : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
    rw [hEdgeCard]
    by_cases hJ : (junk G D).Nonempty
    · have hB := dirtyCase n t G D hNoFour hNonempty hexCover hminCover hLeast hTop hJ
      omega
    · have hEmpty : junk G D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
      have hB := cleanCase n t G D hNoFour hNonempty hexCover hminCover hLeast hTop hEmpty
      have hZero : (junk G D).card = 0 := by rw [hEmpty]; exact Finset.card_empty
      omega
