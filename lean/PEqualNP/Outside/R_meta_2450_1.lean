import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2450_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : Circuit),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      Monotone2 C →
      circuitFun n C = graphFun G ∅ →
      HasStarProfile n G C →
      let bad (D : Circuit) : Set ℕ :=
        {j | j < D.gates.length ∧ (gateAt D j).op = GateOp.and ∧
          ¬ ∃ u v : Fin n, G.Adj u v ∧ Owns n D j u v}
      0 < (bad C).ncard →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        HasStarProfile n G D ∧ (bad D).ncard < (bad C).ncard)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      Monotone2 C → circuitFun n C = graphFun G ∅ → HasStarProfile n G C →
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v) →
      ∃ C' : Circuit, Monotone2 C' ∧ circuitFun n C' = graphFun G ∅ ∧ C'.size ≤ C.size ∧
        HasStarProfile n G C' ∧ ∀ j < C'.gates.length, (gateAt C' j).op = GateOp.and →
          ∃ u v : Fin n, G.Adj u v ∧ Owns n C' j u v) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) → (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x9 → x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x4.size ≤ x9.size) → PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ PEqualNP.MetaComplexity.circuitFun x1 x11 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x11.size ≤ x4.size ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧ ∀ x12 < x11.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16 :=
  by
    intro n G _ hC htri hcyc hM hF hleast hstar
    classical
    let bad (D : Circuit) : Set ℕ :=
      {j | j < D.gates.length ∧ (gateAt D j).op = GateOp.and ∧
        ¬ ∃ u v : Fin n, G.Adj u v ∧ Owns n D j u v}
    have hExch : ∀ C' : Circuit, Monotone2 C' → circuitFun n C' = graphFun G ∅ →
        HasStarProfile n G C' → 0 < (bad C').ncard →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C'.size ∧
          HasStarProfile n G D ∧ (bad D).ncard < (bad C').ncard := by
      intro C' hM' hF' hS' hpos
      exact h1 n G C' htri hcyc hM' hF' hS' hpos
    let admissible (k : ℕ) : Prop :=
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ HasStarProfile n G D ∧
        D.size ≤ hC.size ∧ (bad D).ncard = k
    have hex : ∃ k, admissible k := ⟨(bad hC).ncard, hC, hM, hF, hstar, le_rfl, rfl⟩
    obtain ⟨C', hM', hF', hS', hsizeC', hbadC'⟩ := Nat.find_spec hex
    have hmin : ∀ k, admissible k → Nat.find hex ≤ k := fun k hk => Nat.find_min' hex hk
    have hk0 : Nat.find hex = 0 := by
      by_contra hne
      have hpos : 0 < Nat.find hex := Nat.pos_of_ne_zero hne
      have hC'pos : 0 < (bad C').ncard := hbadC'.symm ▸ hpos
      obtain ⟨D, hDM, hDF, hDsize, hDstar, hDlt⟩ := hExch C' hM' hF' hS' hC'pos
      have hDsizeC : D.size ≤ hC.size := hDsize.trans hsizeC'
      have hDadm : admissible (bad D).ncard := ⟨D, hDM, hDF, hDstar, hDsizeC, rfl⟩
      have hle := hmin _ hDadm
      have hlt : (bad D).ncard < Nat.find hex := by
        rw [← hbadC']
        exact hDlt
      exact Nat.lt_irrefl _ (hlt.trans_le hle)
    have hncard0 : (bad C').ncard = 0 := hbadC'.trans hk0
    have hfin : (bad C').Finite :=
      Set.Finite.subset (Set.finite_Iio C'.gates.length) (fun j hj => hj.1)
    have hbadempty : bad C' = ∅ := by
      by_contra hne
      have hne' : (bad C').Nonempty := Set.nonempty_iff_ne_empty.mpr hne
      have hpos : 0 < (bad C').ncard := (Set.ncard_pos hfin).mpr hne'
      rw [hncard0] at hpos
      exact Nat.lt_irrefl _ hpos
    have hown : ∀ j < C'.gates.length, (gateAt C' j).op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ Owns n C' j u v := by
      intro j hj hop
      by_contra hcon
      have hjb : j ∈ bad C' := ⟨hj, hop, hcon⟩
      rw [hbadempty] at hjb
      exact absurd hjb (Set.notMem_empty j)
    obtain ⟨C'', hM2, hF2, hsize2, hstar2, hown2⟩ := h2 n G C' hM' hF' hS' hown
    refine ⟨C'', hM2, hF2, ?_, hstar2, hown2⟩
    exact hsize2.trans hsizeC'
