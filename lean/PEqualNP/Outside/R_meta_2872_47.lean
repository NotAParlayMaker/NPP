import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Finite
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Construct the bipartite SimpleGraph on Fin (x1 + x2), prove 2-colorability, NoFourCycle,
-- edge cardinality, and weak matching-cover duality x4.card <= S.card, then reduce to
-- TopForm normalization and the clean vs dirty-AND bipartite bounds.
theorem PEqualNP.Outside.R_meta_2872_47 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.Colorable 2 → NoFourCycle G → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size ≤ C.size) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      G.Colorable 2 → NoFourCycle G → G.edgeFinset.Nonempty →
      IsLeastAO G D → TopForm G D → junk G D = ∅ →
      ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
        G.edgeFinset.card + S.card ≤ D.size + 1) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      G.Colorable 2 → NoFourCycle G → G.edgeFinset.Nonempty →
      IsLeastAO G D → TopForm G D → (junk G D).Nonempty →
      ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
        G.edgeFinset.card + S.card ≤ D.size + 1) →
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  intro norm cleanBip dirtyBip n m E M C hRect hAO hEval hSub hRow hCol
  by_cases hE : E.Nonempty
  · let adjRel : Fin (n + m) → Fin (n + m) → Prop := fun u v =>
      ∃ e ∈ E, (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
        (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2)
    have hCastNeNat : ∀ (p : Fin n) (l : Fin m), Fin.castAdd m p ≠ Fin.natAdd n l := by
      intro p l h
      have hv : (Fin.castAdd m p).val = (Fin.natAdd n l).val := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have hp := p.isLt
      omega
    let G : SimpleGraph (Fin (n + m)) := {
      Adj := adjRel
      symm := ⟨fun _ _ h => Exists.elim h fun e he => ⟨e, he.1, he.2.symm⟩⟩
      loopless := ⟨fun u h => Exists.elim h fun e he =>
        he.2.elim (fun h1 => hCastNeNat e.1 e.2 (h1.1.symm.trans h1.2))
          (fun h2 => hCastNeNat e.1 e.2 (h2.1.symm.trans h2.2))⟩
    }
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    have hCol2 : G.Colorable 2 := by
      refine ⟨SimpleGraph.Coloring.mk (fun v : Fin (n + m) => if v.val < n then (0 : Fin 2) else (1 : Fin 2)) ?_⟩
      intro u v hadj
      exact Exists.elim hadj fun e he =>
        he.2.elim
          (fun h1 => by
            rw [h1.1, h1.2]
            have hp : (Fin.castAdd m e.1).val < n := e.1.isLt
            have hl : ¬ (Fin.natAdd n e.2).val < n := by rw [Fin.val_natAdd]; omega
            simp only [hp, hl, ↓reduceIte]
            decide)
          (fun h2 => by
            rw [h2.1, h2.2]
            have hp : (Fin.castAdd m e.1).val < n := e.1.isLt
            have hl : ¬ (Fin.natAdd n e.2).val < n := by rw [Fin.val_natAdd]; omega
            simp only [hp, hl, ↓reduceIte]
            decide)
    have hCastInj : Function.Injective (Fin.castAdd m : Fin n → Fin (n + m)) :=
      Fin.castAdd_injective n m
    have hNatInj : Function.Injective (Fin.natAdd n : Fin m → Fin (n + m)) :=
      Fin.natAdd_injective m n
    have hAdjPair : ∀ (p : Fin n) (l : Fin m),
        G.Adj (Fin.castAdd m p) (Fin.natAdd n l) ↔ (p, l) ∈ E := by
      intro p l
      constructor
      · intro h
        exact Exists.elim h fun e he =>
          he.2.elim
            (fun h1 => by
              have ep : p = e.1 := hCastInj h1.1
              have el : l = e.2 := hNatInj h1.2
              rw [ep, el]
              exact he.1)
            (fun h2 => (hCastNeNat e.1 l h2.1.symm).elim)
      · intro hpl
        exact ⟨(p, l), hpl, Or.inl ⟨rfl, rfl⟩⟩
    have hNoFour : NoFourCycle G := by
      intro a b hab
      by_contra hgt
      have h1lt : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card := by omega
      exact Exists.elim (Finset.one_lt_card.mp h1lt) fun w1 hw1_rest =>
        Exists.elim hw1_rest.2 fun w2 hw2_rest => by
          have hw1 := (Finset.mem_filter.mp hw1_rest.1).2
          have hw2 := (Finset.mem_filter.mp hw2_rest.1).2
          have hw12 : w1 ≠ w2 := hw2_rest.2
          exact Exists.elim hw1.1 fun e1 he1 =>
            he1.2.elim
              (fun ha1 => by
                have hb_left : ∃ p2 : Fin n, b = Fin.castAdd m p2 :=
                  Exists.elim hw1.2 fun eb heb =>
                    heb.2.elim (fun h => ⟨eb.1, h.1⟩)
                      (fun h => (hCastNeNat eb.1 e1.2 (h.1.symm.trans ha1.2)).elim)
                have hw2_right : ∃ l2 : Fin m, w2 = Fin.natAdd n l2 :=
                  Exists.elim hw2.1 fun ec hec =>
                    hec.2.elim (fun h => ⟨ec.2, h.2⟩)
                      (fun h => (hCastNeNat e1.1 ec.2 (ha1.1.symm.trans h.2)).elim)
                exact Exists.elim hb_left fun p2 hp2 =>
                  Exists.elim hw2_right fun l2 hl2 => by
                    have hp_ne : e1.1 ≠ p2 := fun h => hab (ha1.1.trans (h ▸ hp2.symm))
                    have hl_ne : e1.2 ≠ l2 := fun h => hw12 (ha1.2.trans (h ▸ hl2.symm))
                    have m1 : (e1.1, e1.2) ∈ E := he1.1
                    have m2 : (e1.1, l2) ∈ E := (hAdjPair e1.1 l2).mp (by rw [← ha1.1, ← hl2]; exact hw2.1)
                    have m3 : (p2, e1.2) ∈ E := (hAdjPair p2 e1.2).mp (by rw [← hp2, ← ha1.2]; exact hw1.2)
                    have m4 : (p2, l2) ∈ E := (hAdjPair p2 l2).mp (by rw [← hp2, ← hl2]; exact hw2.2)
                    exact hRect e1.1 p2 e1.2 l2 hp_ne hl_ne ⟨m1, m2, m3, m4⟩)
              (fun ha2 => by
                have hb_right : ∃ l2 : Fin m, b = Fin.natAdd n l2 :=
                  Exists.elim hw1.2 fun eb heb =>
                    heb.2.elim (fun h => (hCastNeNat e1.1 eb.2 (ha2.1.symm.trans h.2)).elim)
                      (fun h => ⟨eb.2, h.2⟩)
                have hw2_left : ∃ p2 : Fin n, w2 = Fin.castAdd m p2 :=
                  Exists.elim hw2.1 fun ec hec =>
                    hec.2.elim (fun h => (hCastNeNat ec.1 e1.2 (h.1.symm.trans ha2.2)).elim)
                      (fun h => ⟨ec.1, h.1⟩)
                exact Exists.elim hb_right fun l2 hl2 =>
                  Exists.elim hw2_left fun p2 hp2 => by
                    have hp_ne : e1.1 ≠ p2 := fun h => hw12 (ha2.1.trans (h ▸ hp2.symm))
                    have hl_ne : e1.2 ≠ l2 := fun h => hab (ha2.2.trans (h ▸ hl2.symm))
                    have m1 : (e1.1, e1.2) ∈ E := he1.1
                    have m2 : (e1.1, l2) ∈ E := (hAdjPair e1.1 l2).mp (by rw [← ha2.1, ← hl2]; exact hw1.2.symm)
                    have m3 : (p2, e1.2) ∈ E := (hAdjPair p2 e1.2).mp (by rw [← hp2, ← ha2.2]; exact hw2.1.symm)
                    have m4 : (p2, l2) ∈ E := (hAdjPair p2 l2).mp (by rw [← hp2, ← hl2]; exact hw2.2.symm)
                    exact hRect e1.1 p2 e1.2 l2 hp_ne hl_ne ⟨m1, m2, m3, m4⟩)
    let edgeEmb : Fin n × Fin m → Sym2 (Fin (n + m)) :=
      fun e => s(Fin.castAdd m e.1, Fin.natAdd n e.2)
    have hEdgeEq : G.edgeFinset = E.image edgeEmb := by
      ext z
      rw [G.mem_edgeFinset, Finset.mem_image]
      refine Sym2.ind (fun u v => ?_) z
      change G.Adj u v ↔ ∃ a ∈ E, s(Fin.castAdd m a.1, Fin.natAdd n a.2) = s(u, v)
      constructor
      · intro h
        exact Exists.elim h fun e he => ⟨e, he.1,
          he.2.elim (fun h1 => by rw [h1.1, h1.2])
            (fun h2 => by rw [h2.1, h2.2, Sym2.eq_swap])⟩
      · intro h
        exact Exists.elim h fun e he => by
          have hpair := Sym2.eq_iff.mp he.2
          exact ⟨e, he.1, hpair.elim (fun h1 => Or.inl ⟨h1.1.symm, h1.2.symm⟩)
            (fun h2 => Or.inr ⟨h2.1.symm, h2.2.symm⟩)⟩
    have hEmbInj : Set.InjOn edgeEmb ↑E := by
      intro e1 _ e2 _ heq
      have hp := Sym2.eq_iff.mp heq
      exact hp.elim
        (fun h1 => Prod.ext (hCastInj h1.1) (hNatInj h1.2))
        (fun h2 => (hCastNeNat e1.1 e2.2 h2.1).elim)
    have hEdgeCard : G.edgeFinset.card = E.card := by
      rw [hEdgeEq, Finset.card_image_of_injOn hEmbInj]
    have hGNonempty : G.edgeFinset.Nonempty := by
      rw [hEdgeEq]
      exact hE.image edgeEmb
    have hFun : circuitFun (n + m) C = graphFun G ∅ := by
      funext x
      rw [hEval x]
      change Decidable.decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) =
        (decide (∃ a ∈ (∅ : Finset (Fin (n + m))), x a = true) ||
          decide (∃ u v : Fin (n + m), G.Adj u v ∧ x u = true ∧ x v = true))
      have hempty : decide (∃ a ∈ (∅ : Finset (Fin (n + m))), x a = true) = false := by simp
      rw [hempty, Bool.false_or]
      have hiff : (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) ↔
          (∃ u v : Fin (n + m), G.Adj u v ∧ x u = true ∧ x v = true) := by
        constructor
        · intro h
          exact Exists.elim h fun p hp => Exists.elim hp fun l hpl =>
            ⟨Fin.castAdd m p, Fin.natAdd n l, (hAdjPair p l).mpr hpl.1, hpl.2.1, hpl.2.2⟩
        · intro h
          exact Exists.elim h fun u hu => Exists.elim hu fun v huv =>
            Exists.elim huv.1 fun e he =>
              he.2.elim
                (fun h1 => ⟨e.1, e.2, he.1, h1.1 ▸ huv.2.1, h1.2 ▸ huv.2.2⟩)
                (fun h2 => ⟨e.1, e.2, he.1, h2.1 ▸ huv.2.2, h2.2 ▸ huv.2.1⟩)
      by_cases hx : ∃ u v : Fin (n + m), G.Adj u v ∧ x u = true ∧ x v = true
      · rw [@decide_eq_true _ _ (hiff.mpr hx), decide_eq_true hx]
      · have hnx : ¬ (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true) :=
          fun hp => hx (hiff.mp hp)
        rw [@decide_eq_false _ _ hnx, decide_eq_false hx]
    have hMatchLeCover : ∀ S : Finset (Fin (n + m)), CoverPromise.IsVertexCover G S → M.card ≤ S.card := by
      intro S hCov
      let SL : Finset (Fin (n + m)) := S.filter (fun v => v.val < n)
      let SR : Finset (Fin (n + m)) := S.filter (fun v => ¬ v.val < n)
      have hS_disj : Disjoint SL SR :=
        Finset.disjoint_left.mpr fun v h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hS_uni : SL ∪ SR = S := by
        ext v
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        exact ⟨fun h => h.elim (fun x => x.1) (fun x => x.1),
          fun hv => if hlt : v.val < n then Or.inl ⟨hv, hlt⟩ else Or.inr ⟨hv, hlt⟩⟩
      have hS_sum : SL.card + SR.card = S.card := by
        rw [← Finset.card_union_of_disjoint hS_disj, hS_uni]
      let ML : Finset (Fin n × Fin m) := M.filter (fun e => Fin.castAdd m e.1 ∈ S)
      let MR : Finset (Fin n × Fin m) := M.filter (fun e => Fin.castAdd m e.1 ∉ S)
      have hM_disj : Disjoint ML MR :=
        Finset.disjoint_left.mpr fun e h1 h2 => (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hM_uni : ML ∪ MR = M := by
        ext e
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        exact ⟨fun h => h.elim (fun x => x.1) (fun x => x.1),
          fun he => if hin : Fin.castAdd m e.1 ∈ S then Or.inl ⟨he, hin⟩ else Or.inr ⟨he, hin⟩⟩
      have hM_sum : ML.card + MR.card = M.card := by
        rw [← Finset.card_union_of_disjoint hM_disj, hM_uni]
      let fL : Fin n × Fin m → Fin (n + m) := fun e => Fin.castAdd m e.1
      let fR : Fin n × Fin m → Fin (n + m) := fun e => Fin.natAdd n e.2
      have hL_sub : ML.image fL ⊆ SL := by
        intro v hv
        exact Exists.elim (Finset.mem_image.mp hv) fun e he => by
          rw [← he.2]
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he.1).2, e.1.isLt⟩
      have hL_inj : Set.InjOn fL ↑ML := by
        intro e1 h1 e2 h2 heq
        exact hRow e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1 (hCastInj heq)
      have hL_card : ML.card ≤ SL.card := by
        rw [← Finset.card_image_of_injOn hL_inj]
        exact Finset.card_le_card hL_sub
      have hR_sub : MR.image fR ⊆ SR := by
        intro v hv
        exact Exists.elim (Finset.mem_image.mp hv) fun e he => by
          rw [← he.2]
          have hmM := (Finset.mem_filter.mp he.1).1
          have hnotL := (Finset.mem_filter.mp he.1).2
          have hadj : G.Adj (Fin.castAdd m e.1) (Fin.natAdd n e.2) := (hAdjPair e.1 e.2).mpr (hSub hmM)
          have hcovE : Fin.castAdd m e.1 ∈ S ∨ Fin.natAdd n e.2 ∈ S := hCov _ _ hadj
          have hinR : Fin.natAdd n e.2 ∈ S := hcovE.resolve_left hnotL
          exact Finset.mem_filter.mpr ⟨hinR, by change ¬ (Fin.natAdd n e.2).val < n; rw [Fin.val_natAdd]; omega⟩
      have hR_inj : Set.InjOn fR ↑MR := by
        intro e1 h1 e2 h2 heq
        exact hCol e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1 (hNatInj heq)
      have hR_card : MR.card ≤ SR.card := by
        rw [← Finset.card_image_of_injOn hR_inj]
        exact Finset.card_le_card hR_sub
      omega
    exact Exists.elim (norm (n + m) G hCol2 hNoFour hGNonempty C hAO hFun) fun D hD => by
      letI : DecidableEq GateOp := gateOpDecEq
      have hLeast := hD.1
      have hTop := hD.2.1
      have hSizeLe := hD.2.2
      by_cases hJ : (junk G D).Nonempty
      · exact Exists.elim (dirtyBip (n + m) G D hCol2 hNoFour hGNonempty hLeast hTop hJ) fun S hS => by
          have hMS := hMatchLeCover S hS.1
          have hB := hS.2
          omega
      · have hEmpty : junk G D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
        exact Exists.elim (cleanBip (n + m) G D hCol2 hNoFour hGNonempty hLeast hTop hEmpty) fun S hS => by
          have hMS := hMatchLeCover S hS.1
          have hB := hS.2
          omega
  · have hE0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    have hM0 : M = ∅ := Finset.subset_empty.mp (hE0 ▸ hSub)
    rw [hE0, hM0, Finset.card_empty]
    omega
