import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2260_1
    (smallCover : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ U : Finset (Sym2 (Fin 11)), U.card ≤ 1 →
        ∃ K, IsMinCover (G.deleteEdges (U : Set (Sym2 (Fin 11)))) K ∧ 6 ≤ K.card)
    (nested : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (i j : ℕ), G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] → IsLeastAO G C → TopForm G C →
        junk G C = {i,j} → InCone 11 C i j → 2 ≤ (Ustar G C).card → 22 ≤ C.size) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x12 ∈ x9,             have x14 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x12;             (∀ x15 ∈ x14 (0 : Fin (2 : ℕ)), ∀ x17 ∈ x14 (1 : Fin (2 : ℕ)), x1.Adj x15 x17) ∧ ((x14 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x14 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x13 x14 : Fin (11 : ℕ)), s(x13, x14) ∈ x11 → ∃ x16 ∈ x9, ∃ (x17 : Fin (2 : ℕ)) (x18 : ℕ), (x18 = x4 ∨ x18 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x16 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x16 x17) x18 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x18 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x15 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x15 → x15.card ≤ (x9 \ x10).card) → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 → (22 : ℕ) ≤ x3.size := by
  intro G inst C i j hg hleast htop
  subst G
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  dsimp only
  intro _ _ count cover junkEq cone
  by_cases small : (Ustar G C).card ≤ 1
  · obtain ⟨K, hK, six⟩ := smallCover _ small
    have lower := cover K hK
    change 17 + ((tops G C) \ (centreless G C)).card + 2 * (centreless G C).card +
      ((orN G C) \ (lam G C)).card ≤ C.size + (Ustar G C).card at count
    change K.card ≤ ((tops G C) \ (centreless G C)).card at lower
    omega
  · exact nested G C i j rfl hleast htop junkEq cone (by omega)
