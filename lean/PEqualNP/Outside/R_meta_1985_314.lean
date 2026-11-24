import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Normalize to a least top-form circuit, then charge uncovered edges against its gate count.
-- Only the low-budget regime needs a matching certificate in the surviving Heawood graph.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1985_314
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C'.size ≤ C.size)
    (topForm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧ PEqualNP.TopForm.TopForm G C')
    (account : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (packing : let G := edgeGraph 14 [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
      ∀ D : Circuit, IsLeastAO G D → PEqualNP.TopForm.TopForm G D → D.size ≤ 26 →
        let U := Ustar G D
        let b := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
        b < U.card + U.card / 3 →
          ∃ l r : Fin (7 + U.card - b) → Fin 14,
            Function.Injective l ∧ Function.Injective r ∧ (∀ i j, l i ≠ r j) ∧
            ∀ i, (G.deleteEdges ↑U).Adj (l i) (r i)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 x5) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (27 : ℕ) ≤ x1.size := by
  classical
  intro C hm _ _ hfun
  let E : List (ℕ × ℕ) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
  let G := edgeGraph 14 E
  have h4 : NoFourCycle G := by dsimp [G,E]; decide +kernel
  have h21 : G.edgeFinset.card = 21 := by dsimp [G,E]; decide +kernel
  have hne : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have loopfree : ∀ u v : Fin 14, (u.val,v.val) ∈ E → u ≠ v := by dsimp [E]; decide +kernel
  have computed (x : Fin 14 → Bool) :
      C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, G.Adj u v ∧ x u=true ∧ x v=true := by
    rw [hfun]
    constructor
    · rintro ⟨u,v,h,h1,h2⟩
      exact ⟨u,v,⟨loopfree u v h,Or.inl h⟩,h1,h2⟩
    · rintro ⟨u,v,⟨_,h|h⟩,h1,h2⟩
      · exact ⟨u,v,h,h1,h2⟩
      · exact ⟨v,u,h,h2,h1⟩
  obtain ⟨C₁,ha,hf,hsize⟩ := normalize 14 G inferInstance C hm computed
  let P := fun k : ℕ => ∃ D : Circuit, IsAO2 14 D ∧ circuitFun 14 D = graphFun G ∅ ∧ D.size = k
  have ex : ∃ k, P k := ⟨_,C₁,ha,hf,rfl⟩
  obtain ⟨C₂,h₁,h₂,hk⟩ := Nat.find_spec ex
  have hs : C₂.size ≤ C₁.size := hk.trans_le (Nat.find_min' ex ⟨C₁,ha,hf,rfl⟩)
  have least : IsLeastAO G C₂ := ⟨h₁,h₂,fun D hD hD' => hk.trans_le (Nat.find_min' ex ⟨D,hD,hD',rfl⟩)⟩
  obtain ⟨D,hL,hD,_,hTop⟩ := topForm 14 G C₂ hne least
  obtain ⟨hb,hkC⟩ := account 14 G D h4 hne hL hTop
  let U := Ustar G D
  let b := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
  rw [h21] at hb
  have budget : 21 + (tops G D \ centreless G D).card + b ≤ D.size + U.card + 1 := by
    dsimp only [b,U]
    omega
  let H := G.deleteEdges (↑U)
  let CoverSize := fun k : ℕ => ∃ K : Finset (Fin 14), H.IsVertexCover (K : Set (Fin 14)) ∧ K.card=k
  have hasCover : ∃ k, CoverSize k := ⟨_,Finset.univ,by simp,rfl⟩
  obtain ⟨K,cover,sizeK⟩ := Nat.find_spec hasCover
  have hmin : IsMinCover H K := ⟨cover,fun X hX => sizeK.trans_le (Nat.find_min' hasCover ⟨X,hX,rfl⟩)⟩
  have kt := hkC K hmin
  by_contra! short
  have small : D.size ≤ 26 := by omega
  by_cases cheap : U.card + U.card / 3 ≤ b
  · -- RESIDUAL_BOUND
    have degreeBound : 21 ≤ 3 * K.card + U.card := by
      -- Residual cover count contributed by LarkspurFold.
      let pairs : List (Fin 14 × Fin 14) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
      let edge := fun (p : Fin 14 × Fin 14) => s(p.1,p.2)
      let listed := (pairs.map edge).toFinset
      let star := fun (v : Fin 14) => listed.filter (fun e => v ∈ e)
      have listedAdj : ∀ p ∈ pairs, G.Adj p.1 p.2 := by dsimp [pairs,G,E]; decide +kernel
      have cardListed : listed.card = 21 := by dsimp [listed,pairs,edge]; decide +kernel
      have degree : ∀ v : Fin 14, (star v).card = 3 := by
        dsimp [star,listed,pairs,edge]; decide +kernel
      have total : listed ⊆ U ∪ K.biUnion star := by
        intro e he
        by_cases deleted : e ∈ U
        · exact Finset.mem_union_left _ deleted
        apply Finset.mem_union_right
        obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
        have adj : H.Adj p.1 p.2 := SimpleGraph.deleteEdges_adj.mpr ⟨listedAdj p hp,deleted⟩
        rcases cover adj with a | b
        · exact Finset.mem_biUnion.mpr ⟨p.1,a,Finset.mem_filter.mpr ⟨he,Sym2.mem_mk_left _ _⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨p.2,b,Finset.mem_filter.mpr ⟨he,Sym2.mem_mk_right _ _⟩⟩
      calc
        21 = listed.card := cardListed.symm
        _ ≤ (U ∪ K.biUnion star).card := Finset.card_le_card total
        _ ≤ U.card + (K.biUnion star).card := Finset.card_union_le _ _
        _ ≤ U.card + ∑ v ∈ K, (star v).card := Nat.add_le_add_left Finset.card_biUnion_le _
        _ = 3 * K.card + U.card := by simp [degree,Nat.mul_comm,Nat.add_comm]
    omega
  · obtain ⟨l,r,hl,hr,hd,he⟩ := packing D hL hTop small (Nat.lt_of_not_ge cheap)
    let pick (i : Fin (7+U.card-b)) : ↥K :=
      if hi : l i ∈ K then ⟨l i,hi⟩ else ⟨r i,(cover (he i)).resolve_left hi⟩
    have inj : Function.Injective pick := by
      intro i j h
      have eq := congrArg Subtype.val h
      by_cases hi : l i ∈ K <;> by_cases hj : l j ∈ K
      · exact hl (by simpa [pick,hi,hj] using eq)
      · exact (hd i j (by simpa [pick,hi,hj] using eq)).elim
      · exact (hd j i (by simpa [pick,hi,hj] using eq.symm)).elim
      · exact hr (by simpa [pick,hi,hj] using eq)
    have matching : 7 + U.card - b ≤ K.card := by simpa using Fintype.card_le_of_injective pick inj
    omega
