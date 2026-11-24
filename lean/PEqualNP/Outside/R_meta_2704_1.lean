import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2704_1
    (coverBound : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 x4 : Finset (Fin (11 : ℕ))) (x5 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ))),   (∀ (x6 x7 : Fin (11 : ℕ)), x1.Adj x6 x7 → x6 ∈ x3 ∨ x7 ∈ x3 ∨ (x6, x7) ∈ x5 ∨ (x7, x6) ∈ x5) →     (∀ x7 ∈ x3 \ x4, ∀ x9 ∈ x3 \ x4, ¬x1.Adj x7 x9) →       let x8 : Finset (Fin (11 : ℕ)) := {x8 ∈ Finset.univ \ x3 | ∃ x9 ∈ x3 \ x4, x1.Adj x9 x8};       have x9 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x9 ∈ x5 | x1.Adj x9.1 x9.2 ∧ x9.1 ∉ x8 ∧ x9.2 ∉ x8};       (11 : ℕ) ≤ x4.card + x8.card + x9.card + x1.indepNum)
    (circuitBound : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = PEqualNP.EdgeOwnership.edgeGraph 11
        [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),
         (4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size < 22 →
      (∃ i j, PEqualNP.TopForm.junk G C = {i,j} ∧ PEqualNP.EdgeOwnership.InCone 11 C i j) →
      let U := PEqualNP.TopForm.Ustar G C
      let H := G.deleteEdges (U : Set _)
      U.card + H.indepNum ≤ 6 + 2 * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;             have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};             have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};             ∀ x13 ⊆ x11,               (∀ x15 ∈ x11 \ x13, ∀ x17 ∈ x11 \ x13, ¬x10.Adj x15 x17) →                 have x16 : Finset (Fin (11 : ℕ)) := {x16 ∈ Finset.univ \ x11 | ∃ x17 ∈ x11 \ x13, x10.Adj x17 x16};                 have x17 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x17 ∈ x12 | x10.Adj x17.1 x17.2 ∧ x17.1 ∉ x16 ∧ x17.2 ∉ x16};                 (5 : ℕ) + x9.card ≤ x13.card + x16.card + x17.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  classical
  intro G inst C graph least top small chain U H S M B _ valid F Q
  have shape : ∀ u v : Fin 11, H.Adj u v →
      u ∈ S ∨ v ∈ S ∨ (u,v) ∈ M ∨ (v,u) ∈ M := by
    intro u v edge
    have sub := (SimpleGraph.deleteEdges_adj.mp edge).1
    rw [graph] at sub
    have finiteShape : ∀ u v, (PEqualNP.EdgeOwnership.edgeGraph 11
        [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),
         (4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).Adj u v →
        u ∈ ({3,8,9,10} : Finset (Fin 11)) ∨ v ∈ ({3,8,9,10} : Finset (Fin 11)) ∨
        (u,v) ∈ ({(1,4),(2,5),(6,7)} : Finset (Fin 11 × Fin 11)) ∨
        (v,u) ∈ ({(1,4),(2,5),(6,7)} : Finset (Fin 11 × Fin 11)) := by decide
    exact finiteShape u v sub
  have h₁ := coverBound H S B M shape valid
  have h₂ := circuitBound G C graph least top small chain
  change 11 ≤ B.card + F.card + Q.card + H.indepNum at h₁
  change U.card + H.indepNum ≤ 6 + 2 * (PEqualNP.TopForm.centreless G C).card +
    (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card at h₂
  omega
