import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_5230_1
    (coverCost : ∀ (H : SimpleGraph (Fin (11 : ℕ))) [inst : DecidableRel H.Adj],
      let S : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};
      have M : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};
      (∀ (u v : Fin (11 : ℕ)), H.Adj u v → u ∈ S ∨ v ∈ S ∨ (u, v) ∈ M ∨ (v, u) ∈ M) →
      ∀ (K : Finset (Fin (11 : ℕ))),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover H K →
      ∃ B ⊆ S,
      (∀ v ∈ S \ B, ∀ w ∈ S \ B, ¬H.Adj v w) ∧
      let forced : Finset (Fin (11 : ℕ)) := {v ∈ Finset.univ \ S | ∃ a ∈ S \ B, H.Adj a v};
      have pairs : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {e ∈ M | H.Adj e.1 e.2 ∧ e.1 ∉ forced ∧ e.2 ∉ forced};
      K.card = B.card + forced.card + pairs.card)
    (profile : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj], G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      ∀ (U : Finset (Sym2 (Fin 11))), U ⊆ G.edgeFinset → ∀ T : Finset (Fin 11),
      (∀ u v, (G.deleteEdges ↑U).Adj u v → u ∈ T ∨ v ∈ T) →
      5 + U.card ≤ T.card + [0,0,2,4,5,7,8,9,11,12,13,14,16,17,18,19,21].getD U.card 0)
    (escape : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] → IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size < 22 →
      (∃ i j, junk G C = {i,j} ∧ InCone 11 C i j) →
      let r := (Ustar G C).card
      let k := 2 * (centreless G C).card + (orN G C \ lam G C).card
      k < [0,0,2,4,5,7,8,9,11,12,13,14,16,17,18,19,21].getD r 0 → ∀ T : Finset (Fin 11), T.card = min 11 (4+r-k) →
      ∃ u v : Fin 11, u ∉ T ∧ v ∉ T ∧ G.Adj u v ∧ s(u,v) ∈ starEdges G C) :
    ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (i j : ℕ),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map fun e => (e / 11, e % 11)) →
      IsLeastAO G C → TopForm G C → junk G C = {i,j} → InCone 11 C i j →
      let U := Ustar G C
      let V := centreless G C
      let R := orN G C \ lam G C
      let T := tops G C
      (∀ a ∈ T, let S : Fin 2 → Finset (Fin 11) := side C a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u,v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) h ∧
          gateVal 11 C h (pairInput u v) = true) →
      C.size ≤ 21 → 4 ≤ U.card →
      ∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K →
      7 ≤ K.card + U.card → K.card ≤ (T \ V).card →
      0 < 2 * V.card + R.card → (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card - 17 →
      False := by
  have gateCharge : ∀ (G : SimpleGraph (Fin (11 : ℕ))) [inst : DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      C.size < (22 : ℕ) →
      (∃ (i : ℕ) (j : ℕ), PEqualNP.TopForm.junk G C = {i, j} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) C i j) →
      let U : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar G C;
      let H : SimpleGraph (Fin (11 : ℕ)) := G.deleteEdges ↑U;
      let S : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};
      have M : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};
      ∀ B ⊆ S,
      (∀ u ∈ S \ B, ∀ w ∈ S \ B, ¬H.Adj u w) →
      let forced : Finset (Fin (11 : ℕ)) := {v ∈ Finset.univ \ S | ∃ w ∈ S \ B, H.Adj w v};
      have pairs : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {e ∈ M | H.Adj e.1 e.2 ∧ e.1 ∉ forced ∧ e.2 ∉ forced};
      (5 : ℕ) + U.card ≤ B.card + forced.card + pairs.card + (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card := by
    intro G inst C graph least top short nested U H S M B sub valid F P
    classical
    let K := (B ∪ F) ∪ P.image Prod.fst
    have shape0 : ∀ u v, (edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).Adj u v →
        u ∈ S ∨ v ∈ S ∨ (u,v) ∈ M ∨ (v,u) ∈ M := by decide +kernel
    have shape : ∀ u v, H.Adj u v → u ∈ S ∨ v ∈ S ∨ (u,v) ∈ M ∨ (v,u) ∈ M := by
      intro u v h
      apply shape0
      rw [← graph]
      exact (SimpleGraph.deleteEdges_adj.mp h).1
    have forced {u v : Fin 11} (adj : H.Adj u v) (us : u ∈ S) (ub : u ∉ B) (vb : v ∉ B) : v ∈ F := by
      have um := Finset.mem_sdiff.mpr ⟨us,ub⟩
      have vs : v ∉ S := fun vs => valid u um v (Finset.mem_sdiff.mpr ⟨vs,vb⟩) adj
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,vs⟩,u,um,adj⟩
    have covers : ∀ u v, H.Adj u v → u ∈ K ∨ v ∈ K := by
      intro u v adj
      by_contra! neither
      have ub : u ∉ B := fun hu => neither.1 (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
      have vb : v ∉ B := fun hv => neither.2 (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
      have uf : u ∉ F := fun hu => neither.1 (Finset.mem_union_left _ (Finset.mem_union_right _ hu))
      have vf : v ∉ F := fun hv => neither.2 (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
      rcases shape u v adj with us|vs|m|m
      · exact vf (forced adj us ub vb)
      · exact uf (forced adj.symm vs vb ub)
      · have h : (u,v) ∈ P := Finset.mem_filter.mpr ⟨m,adj,uf,vf⟩
        exact neither.1 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,h,rfl⟩))
      · have h : (v,u) ∈ P := Finset.mem_filter.mpr ⟨m,adj.symm,vf,uf⟩
        exact neither.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,h,rfl⟩))
    have size : K.card ≤ B.card + F.card + P.card :=
      (Finset.card_union_le ..).trans (Nat.add_le_add (Finset.card_union_le ..) Finset.card_image_le)
    let k := 2*(centreless G C).card+(orN G C \ lam G C).card
    let b := [0,0,2,4,5,7,8,9,11,12,13,14,16,17,18,19,21].getD U.card 0
    have enough := profile G graph U Finset.sdiff_subset K covers
    change 5+U.card ≤ K.card+b at enough
    by_contra fail
    have miss : B.card+F.card+P.card+k < 5+U.card := by dsimp [k]; omega
    have lo : k < b := by omega
    have upper : K.card ≤ min 11 (4+U.card-k) := by
      have bound := Finset.card_le_univ K
      simp at bound
      omega
    obtain ⟨T,hKT,_,ht⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ K) upper
      (show min 11 (4+U.card-k) ≤ (Finset.univ : Finset (Fin 11)).card by simp)
    obtain ⟨u,v,ut,vt,adj,star⟩ := escape G C graph least top short nested lo T ht
    have survives : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨adj,fun hu => (Finset.mem_sdiff.mp hu).2 star⟩
    exact (covers u v survives).elim (fun h => ut (hKT h)) (fun h => vt (hKT h))
  intro G inst C i j hG hLeast hTop hJunk hCone
  dsimp only
  intro hStars hTrace hSize hU4 K hKMin hKU hKT offCharge hBudget
  classical
  change G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] at hG
  let U := Ustar G C
  let H := G.deleteEdges (U : Set _)
  let S := ({3, 8, 9, 10} : Finset (Fin 11))
  let M := ({(1, 4), (2, 5), (6, 7)} : Finset (Fin 11 × Fin 11))
  let T := tops G C
  let V := centreless G C
  let R := orN G C \ lam G C
  have hSource : ∀ (u v : Fin 11), s(u,v) ∈ U → ∃ a ∈ T, ∃ (b : Fin 2) (h : ℕ),
      (h = i ∨ h = j) ∧ gateVal 11 C a (pairInput u v) = true ∧
      OrReaches 11 C (opnd C a b) h ∧ gateVal 11 C h (pairInput u v) = true := by
    intro u v huv
    obtain ⟨a, ha, b, h, hh, hval, hr, hhval⟩ := hTrace u v huv
    have hij : h = i ∨ h = j := by
      rw [hJunk] at hh
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    exact ⟨a, ha, b, h, hij, hval, hr, hhval⟩
  have graphShape : ∀ u v, (PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).Adj u v →
      u ∈ S ∨ v ∈ S ∨ (u,v) ∈ M ∨ (v,u) ∈ M := by decide +kernel
  have shape : ∀ u v, H.Adj u v → u ∈ S ∨ v ∈ S ∨ (u,v) ∈ M ∨ (v,u) ∈ M := by
    intro u v huv
    apply graphShape u v
    rw [← hG]
    exact (SimpleGraph.deleteEdges_adj.mp huv).1
  obtain ⟨B, hB, valid, cost⟩ := coverCost H shape K hKMin
  have small : C.size < 22 := by omega
  have charge := gateCharge G C hG hLeast hTop small ⟨i,j,hJunk,hCone⟩ B hB valid
  let F := (Finset.univ \ S).filter (fun v => ∃ a ∈ S \ B, H.Adj a v)
  let L := M.filter (fun e => H.Adj e.1 e.2 ∧ e.1 ∉ F ∧ e.2 ∉ F)
  change K.card = B.card + F.card + L.card at cost
  change (5 + U.card) ≤ B.card + F.card + L.card + 2 * V.card + R.card at charge
  change K.card ≤ (T \ V).card at hKT
  change 0 < 2 * V.card + R.card at offCharge
  change (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card - 17 at hBudget
  omega
