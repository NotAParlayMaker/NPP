import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Nested two junk gates g inside the cone of h. Either the charge p = 2 Z + R is at least two,
-- or there is no centreless top, g is read by h alone, h is read by one gate m, and m is the only
-- OR gate outside Lambda that is not below F, and every edge of U* makes g and h true
-- (the first statement, about any least top-form circuit).
-- The two cases are the last two statements; with p = 1 the charged count loses one.
theorem PEqualNP.Outside.R_meta_5182_617
    (dich : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g h : ℕ),
      G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C → junk G C = {g, h} →
      InCone n C g h →
      2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card ∨
      (centreless G C = ∅ ∧ readers n C g = {h} ∧
        (∃ m, readers n C h = {m} ∧ orN G C \ lam G C = {m}) ∧
        ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
          gateVal n C g (pairInput u v) = true ∧ gateVal n C h (pairInput u v) = true))
    (nf : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (g h m : ℕ),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
        fun e : ℕ => (e / 11, e % 11)) →
      IsLeastAO G C ∧ TopForm G C ∧ C.size < 22 ∧ junk G C = {g, h} ∧ InCone 11 C g h ∧
        centreless G C = ∅ ∧ readers 11 C g = {h} ∧ readers 11 C h = {m} ∧
        orN G C \ lam G C = {m} →
      (∀ u v : Fin 11, s(u, v) ∈ Ustar G C → gateVal 11 C h (pairInput u v) = true) →
      let U := Ustar G C
      let H := G.deleteEdges ↑U
      let S : Finset (Fin 11) := {3, 8, 9, 10}
      let M : Finset (Fin 11 × Fin 11) := {(1, 4), (2, 5), (6, 7)}
      (∀ a ∈ S, ∀ b ∈ S, ¬H.Adj a b) →
      let N := (Finset.univ \ S).filter fun v => ∃ a ∈ S, H.Adj a v
      let P := M.filter fun e => H.Adj e.1 e.2 ∧ e.1 ∉ N ∧ e.2 ∉ N
      4 + U.card ≤ N.card + P.card)
    (two : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
        fun e : ℕ => (e / 11, e % 11)) →
      IsLeastAO G C → TopForm G C → C.size < 22 →
      (∃ g h : ℕ, junk G C = {g, h} ∧ InCone 11 C g h) →
      2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card →
      let U := Ustar G C
      let H := G.deleteEdges ↑U
      let S : Finset (Fin 11) := {3, 8, 9, 10}
      let M : Finset (Fin 11 × Fin 11) := {(1, 4), (2, 5), (6, 7)}
      (∀ a ∈ S, ∀ b ∈ S, ¬H.Adj a b) →
      let N := (Finset.univ \ S).filter fun v => ∃ a ∈ S, H.Adj a v
      let P := M.filter fun e => H.Adj e.1 e.2 ∧ e.1 ∉ N ∧ e.2 ∉ N
      5 + U.card ≤ N.card + P.card + 2 * (centreless G C).card + (orN G C \ lam G C).card) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;             have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};             have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};             ∀ x13 ⊆ x11,               x13 = ∅ →                 (∀ x16 ∈ x11 \ x13, ∀ x18 ∈ x11 \ x13, ¬x10.Adj x16 x18) →                   have x17 : Finset (Fin (11 : ℕ)) := {x17 ∈ Finset.univ \ x11 | ∃ x18 ∈ x11 \ x13, x10.Adj x18 x17};                   have x18 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x18 ∈ x12 | x10.Adj x18.1 x18.2 ∧ x18.1 ∉ x17 ∧ x18.2 ∉ x17};                   (5 : ℕ) + x9.card ≤ x13.card + x17.card + x18.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  classical
  intro G inst C hG least form size nested U H S M T subset empty independent
  subst empty
  intro N P
  obtain ⟨g, h, hJ, hc⟩ := nested
  have hlist : ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
      fun e : ℕ => (e / 11, e % 11)) = [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] := by
    decide
  have hG' : G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
      fun e : ℕ => (e / 11, e % 11)) := by rw [hlist]; exact hG
  have adj89 : G.Adj (8 : Fin 11) 9 := by rw [hG]; decide +kernel
  have hE : G.edgeFinset.Nonempty := ⟨s(8, 9), SimpleGraph.mem_edgeFinset.mpr adj89⟩
  have indep : ∀ a ∈ S, ∀ b ∈ S, ¬H.Adj a b := by
    simpa only [Finset.sdiff_empty] using independent
  have eN : N = (Finset.univ \ S).filter (fun v => ∃ a ∈ S, H.Adj a v) := by
    simp only [N, Finset.sdiff_empty]
  have eP : P = M.filter (fun e => H.Adj e.1 e.2 ∧ e.1 ∉ N ∧ e.2 ∉ N) := rfl
  rw [Finset.card_empty, Nat.zero_add]
  rcases dich 11 G C g h hE least form hJ hc with hp | ⟨hZ, hrg, ⟨m, hrh, hR⟩, hU⟩
  · have key := two G C hG' least form size ⟨g, h, hJ, hc⟩ hp indep
    rw [eP, eN]
    exact key
  · have key : 4 + U.card ≤ N.card + P.card := by
      rw [eP, eN]
      exact nf G C g h m hG' ⟨least, form, size, hJ, hc, hZ, hrg, hrh, hR⟩
        (fun u v huv => (hU u v huv).2) indep
    rw [hZ, hR, Finset.card_empty, Finset.card_singleton]
    omega
