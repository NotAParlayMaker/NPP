import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

theorem PEqualNP.Outside.L_meta_746 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) s ↔ 3 ≤ s := by
  let G := SimpleGraph.starGraph (0 : Fin 4)
  have hfun : (fun x : Fin 4 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) =
      (fun x : Fin 4 → Bool => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x
    exact (by decide : ∀ y : Fin 4 → Bool,
      ((y 0 && y 1) || (y 0 && y 2) || (y 0 && y 3)) =
        decide (∃ i j, (SimpleGraph.starGraph (0 : Fin 4)).Adj i j ∧ y i = true ∧ y j = true)) x
  have ht : G.IsTree := SimpleGraph.isTree_starGraph _
  have hcard : G.edgeFinset.card = 3 := by
    have he := ht.card_edgeFinset
    simp only [Fintype.card_fin] at he
    omega
  have h01 : G.Adj 0 1 := by decide
  have hed : ∃ i j, G.Adj i j := ⟨0, 1, h01⟩
  rw [hfun]
  intro s
  constructor
  · intro hs
    have lb := PEqualNP.MetaComplexity.L104 4 1 s G ht.isAcyclic hed
      (fun T hT => Finset.card_pos.mpr ((hT 0 1 h01).elim
        (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩))) hs
    omega
  · intro hs
    have hc := PEqualNP.MetaComplexity.L105 4 G {0} hed (by
      intro i j hij
      simpa only [Finset.mem_singleton] using (SimpleGraph.starGraph_adj.mp hij).2)
    rw [hcard, Finset.card_singleton] at hc
    obtain ⟨C, hC, hsize, hval⟩ := hc
    exact ⟨C, hC, by omega, hval⟩

