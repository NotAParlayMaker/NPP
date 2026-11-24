import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_5184_1
    (coverGap : ∀ (D : Finset (Sym2 (Fin (11 : ℕ)))) (K : Finset (Fin (11 : ℕ))),
      ((PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]).deleteEdges ↑D).IsVertexCover ↑K →
        (7 : ℕ) ≤ K.card + D.card)
    (pay : ∀ (G : SimpleGraph (Fin (11 : ℕ))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
        PEqualNP.TopForm.IsLeastAO G C →
          PEqualNP.TopForm.TopForm G C →
            C.size < (22 : ℕ) →
              (∃ (i j : ℕ), PEqualNP.TopForm.junk G C = {i, j} ∧
                  PEqualNP.EdgeOwnership.InCone (11 : ℕ) C i j) →
                (2 : ℕ) * (PEqualNP.TopForm.Ustar G C).card ≤
                  (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
                    (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card + (2 : ℕ)) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;             have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};             have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};             ∀ x13 ⊆ x11,               x13 ≠ ∅ →                 (∀ x16 ∈ x11 \ x13, ∀ x18 ∈ x11 \ x13, ¬x10.Adj x16 x18) →                   have x17 : Finset (Fin (11 : ℕ)) := {x17 ∈ Finset.univ \ x11 | ∃ x18 ∈ x11 \ x13, x10.Adj x18 x17};                   have x18 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x18 ∈ x12 | x10.Adj x18.1 x18.2 ∧ x18.1 ∉ x17 ∧ x18.2 ∉ x17};                   (5 : ℕ) + x9.card ≤ x13.card + x17.card + x18.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  classical
  intro G inst C hG hleast htop hsize hjunk
  intro U H S M B _hB _hne hindep forced pairs
  have hpay : (2 : ℕ) * U.card ≤
      (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card + 2 := by
    simpa [U] using pay G C hG hleast htop hsize hjunk
  let K : Finset (Fin 11) := B ∪ forced ∪ pairs.image Prod.fst
  have hKcard : K.card ≤ B.card + forced.card + pairs.card := by
    calc
      K.card ≤ (B ∪ forced).card + (pairs.image Prod.fst).card := Finset.card_union_le _ _
      _ ≤ B.card + forced.card + (pairs.image Prod.fst).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ B.card + forced.card + pairs.card := Nat.add_le_add_left Finset.card_image_le _
  have hshape : ∀ u v : Fin 11,
      (PEqualNP.EdgeOwnership.edgeGraph 11 [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]).Adj u v →
        u ∈ ({(3 : Fin 11), (8 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)) ∨
          v ∈ ({(3 : Fin 11), (8 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)) ∨
            (u, v) ∈ ({((1 : Fin 11), (4 : Fin 11)), ((2 : Fin 11), (5 : Fin 11)),
              ((6 : Fin 11), (7 : Fin 11))} : Finset (Fin 11 × Fin 11)) ∨
              (v, u) ∈ ({((1 : Fin 11), (4 : Fin 11)), ((2 : Fin 11), (5 : Fin 11)),
                ((6 : Fin 11), (7 : Fin 11))} : Finset (Fin 11 × Fin 11)) := by
    decide
  have hshapeH : ∀ u v, H.Adj u v → u ∈ S ∨ v ∈ S ∨ (u, v) ∈ M ∨ (v, u) ∈ M := by
    intro u v huv
    have hdel : G.Adj u v ∧ s(u, v) ∉ (↑U : Set (Sym2 (Fin 11))) := by
      simpa [H, SimpleGraph.deleteEdges_adj] using huv
    have hgraph : (PEqualNP.EdgeOwnership.edgeGraph 11 [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]).Adj u v := by
      simpa [hG] using hdel.1
    simpa [S, M] using hshape u v hgraph
  have hmemF : ∀ v, v ∈ forced ↔ v ∉ S ∧ ∃ u ∈ S \ B, H.Adj u v := by
    intro v
    simp [forced, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ]
  have hmemP : ∀ e, e ∈ pairs ↔ e ∈ M ∧ H.Adj e.1 e.2 ∧ e.1 ∉ forced ∧ e.2 ∉ forced := by
    intro e
    simp [pairs, Finset.mem_filter]
  have hcover : H.IsVertexCover (↑K : Set (Fin 11)) := by
    intro u v huv
    simp only [Finset.mem_coe]
    rcases hshapeH u v huv with hu | hv | huvM | hvuM
    · by_cases huB : u ∈ B
      · left
        exact Finset.mem_union_left _ (Finset.mem_union_left _ huB)
      · by_cases hvB : v ∈ B
        · right
          exact Finset.mem_union_left _ (Finset.mem_union_left _ hvB)
        · by_cases hvS : v ∈ S
          · exact False.elim (hindep u (Finset.mem_sdiff.mpr ⟨hu, huB⟩) v
              (Finset.mem_sdiff.mpr ⟨hvS, hvB⟩) huv)
          · right
            have hvF : v ∈ forced :=
              (hmemF v).2 ⟨hvS, u, Finset.mem_sdiff.mpr ⟨hu, huB⟩, huv⟩
            exact Finset.mem_union_left _ (Finset.mem_union_right _ hvF)
    · by_cases hvB : v ∈ B
      · right
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hvB)
      · by_cases huB : u ∈ B
        · left
          exact Finset.mem_union_left _ (Finset.mem_union_left _ huB)
        · by_cases huS : u ∈ S
          · exact False.elim (hindep u (Finset.mem_sdiff.mpr ⟨huS, huB⟩) v
              (Finset.mem_sdiff.mpr ⟨hv, hvB⟩) huv)
          · left
            have huF : u ∈ forced :=
              (hmemF u).2 ⟨huS, v, Finset.mem_sdiff.mpr ⟨hv, hvB⟩, huv.symm⟩
            exact Finset.mem_union_left _ (Finset.mem_union_right _ huF)
    · by_cases huF : u ∈ forced
      · left
        exact Finset.mem_union_left _ (Finset.mem_union_right _ huF)
      · by_cases hvF : v ∈ forced
        · right
          exact Finset.mem_union_left _ (Finset.mem_union_right _ hvF)
        · left
          have hp : (u, v) ∈ pairs := (hmemP (u, v)).2 ⟨huvM, huv, huF, hvF⟩
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(u, v), hp, rfl⟩)
    · by_cases hvF : v ∈ forced
      · right
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hvF)
      · by_cases huF : u ∈ forced
        · left
          exact Finset.mem_union_left _ (Finset.mem_union_right _ huF)
        · right
          have hp : (v, u) ∈ pairs := (hmemP (v, u)).2 ⟨hvuM, huv.symm, hvF, huF⟩
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(v, u), hp, rfl⟩)
  have h7 : (7 : ℕ) ≤ K.card + U.card :=
    coverGap U K (by simpa [H, hG] using hcover)
  omega

