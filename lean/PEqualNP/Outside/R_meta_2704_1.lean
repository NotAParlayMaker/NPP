import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_2704_1
    (h0 : ∀ (G : SimpleGraph (Fin (11 : ℕ))) [inst : DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
    G = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
    PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
    C.size < (22 : ℕ) →
    (∃ (i j : ℕ), PEqualNP.TopForm.junk G C = {i, j} ∧
      PEqualNP.EdgeOwnership.InCone (11 : ℕ) C i j) →
    let U : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar G C;
    U = ∅ →
    let H : SimpleGraph (Fin (11 : ℕ)) := G.deleteEdges ↑U;
    let S : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};
    have M : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};
    ∀ B ⊆ S,
      (∀ u ∈ S \ B, ∀ w ∈ S \ B, ¬H.Adj u w) →
      let forced : Finset (Fin (11 : ℕ)) := {v ∈ Finset.univ \ S | ∃ a ∈ S \ B, H.Adj a v};
      have pairs : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {e ∈ M | H.Adj e.1 e.2 ∧ e.1 ∉ forced ∧ e.2 ∉ forced};
      B.card ≤ (2 : ℕ) →
      (5 : ℕ) + U.card ≤ B.card + forced.card + pairs.card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)
    (h1 : ∀ (G : SimpleGraph (Fin (11 : ℕ))) [inst : DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
    G = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
    PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
    C.size < (22 : ℕ) →
    (∃ (i j : ℕ), PEqualNP.TopForm.junk G C = {i, j} ∧
      PEqualNP.EdgeOwnership.InCone (11 : ℕ) C i j) →
    let U : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar G C;
    U = ∅ →
    let H : SimpleGraph (Fin (11 : ℕ)) := G.deleteEdges ↑U;
    let S : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};
    have M : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};
    ∀ B ⊆ S,
      (∀ u ∈ S \ B, ∀ w ∈ S \ B, ¬H.Adj u w) →
      let forced : Finset (Fin (11 : ℕ)) := {v ∈ Finset.univ \ S | ∃ a ∈ S \ B, H.Adj a v};
      have pairs : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {e ∈ M | H.Adj e.1 e.2 ∧ e.1 ∉ forced ∧ e.2 ∉ forced};
      (3 : ℕ) ≤ B.card →
      (5 : ℕ) + U.card ≤ B.card + forced.card + pairs.card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)
    (h2 : ∀ (G : SimpleGraph (Fin (11 : ℕ))) [inst : DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
    G = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
    PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
    C.size < (22 : ℕ) →
    (∃ (i j : ℕ), PEqualNP.TopForm.junk G C = {i, j} ∧
      PEqualNP.EdgeOwnership.InCone (11 : ℕ) C i j) →
    let U : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar G C;
    U.Nonempty →
    let H : SimpleGraph (Fin (11 : ℕ)) := G.deleteEdges ↑U;
    let S : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};
    have M : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};
    ∀ B ⊆ S,
      (∀ u ∈ S \ B, ∀ w ∈ S \ B, ¬H.Adj u w) →
      let forced : Finset (Fin (11 : ℕ)) := {v ∈ Finset.univ \ S | ∃ a ∈ S \ B, H.Adj a v};
      have pairs : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {e ∈ M | H.Adj e.1 e.2 ∧ e.1 ∉ forced ∧ e.2 ∉ forced};
      B.card ≤ (2 : ℕ) →
      (5 : ℕ) + U.card ≤ B.card + forced.card + pairs.card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)
    (h3 : ∀ (G : SimpleGraph (Fin (11 : ℕ))) [inst : DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
    G = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
    PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
    C.size < (22 : ℕ) →
    (∃ (i j : ℕ), PEqualNP.TopForm.junk G C = {i, j} ∧
      PEqualNP.EdgeOwnership.InCone (11 : ℕ) C i j) →
    let U : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar G C;
    U.Nonempty →
    let H : SimpleGraph (Fin (11 : ℕ)) := G.deleteEdges ↑U;
    let S : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};
    have M : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};
    ∀ B ⊆ S,
      (∀ u ∈ S \ B, ∀ w ∈ S \ B, ¬H.Adj u w) →
      let forced : Finset (Fin (11 : ℕ)) := {v ∈ Finset.univ \ S | ∃ a ∈ S \ B, H.Adj a v};
      have pairs : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {e ∈ M | H.Adj e.1 e.2 ∧ e.1 ∉ forced ∧ e.2 ∉ forced};
      (3 : ℕ) ≤ B.card →
      (5 : ℕ) + U.card ≤ B.card + forced.card + pairs.card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)
    : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;             have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};             have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};             ∀ x13 ⊆ x11,               (∀ x15 ∈ x11 \ x13, ∀ x17 ∈ x11 \ x13, ¬x10.Adj x15 x17) →                 have x16 : Finset (Fin (11 : ℕ)) := {x16 ∈ Finset.univ \ x11 | ∃ x17 ∈ x11 \ x13, x10.Adj x17 x16};                 have x17 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x17 ∈ x12 | x10.Adj x17.1 x17.2 ∧ x17.1 ∉ x16 ∧ x17.2 ∉ x16};                 (5 : ℕ) + x9.card ≤ x13.card + x16.card + x17.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  intro G inst C hg hleast htop hsmall hj
  dsimp only
  intro B hB hind
  let U := Ustar G C
  let H := G.deleteEdges (U : Set _)
  let S : Finset (Fin 11) := {3, 8, 9, 10}
  let M : Finset (Fin 11 × Fin 11) := {(1, 4), (2, 5), (6, 7)}
  let F := (Finset.univ \ S).filter (fun v => ∃ a ∈ S \ B, H.Adj a v)
  let L := M.filter (fun e => H.Adj e.1 e.2 ∧ e.1 ∉ F ∧ e.2 ∉ F)
  change (5 + U.card) ≤ B.card + F.card + L.card + 2 * (centreless G C).card +
    (orN G C \ lam G C).card
  by_cases hu : U = ∅
  · by_cases hb : B.card ≤ 2
    · exact h0 G C hg hleast htop hsmall hj hu B hB hind hb
    · have hb3 : 3 ≤ B.card := by omega
      exact h1 G C hg hleast htop hsmall hj hu B hB hind hb3
  · have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hu
    by_cases hb : B.card ≤ 2
    · exact h2 G C hg hleast htop hsmall hj hUne B hB hind hb
    · have hb3 : 3 ≤ B.card := by omega
      exact h3 G C hg hleast htop hsmall hj hUne B hB hind hb3
