import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

theorem PEqualNP.Outside.L_meta_747 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) s ↔ 4 ≤ s := by
  let G : SimpleGraph (Fin 5) := SimpleGraph.starGraph 0
  have hedge : ∃ i j : Fin 5, G.Adj i j := ⟨0, 1, by decide⟩
  have hcover : ∀ i j : Fin 5, G.Adj i j → i ∈ ({0} : Finset (Fin 5)) ∨ j ∈ ({0} : Finset (Fin 5)) := by
    intro i j hij
    rw [show G = SimpleGraph.starGraph 0 from rfl, SimpleGraph.starGraph_adj] at hij
    rcases hij.2 with rfl | rfl
    · exact Or.inl (Finset.mem_singleton_self 0)
    · exact Or.inr (Finset.mem_singleton_self 0)
  have hmin : ∀ T : Finset (Fin 5), (∀ i j : Fin 5, G.Adj i j → i ∈ T ∨ j ∈ T) → 1 ≤ T.card := by
    intro T hT
    rcases hT 0 1 (by decide) with h | h
    · exact Finset.card_pos.mpr ⟨0, h⟩
    · exact Finset.card_pos.mpr ⟨1, h⟩
  have hcard : G.edgeFinset.card = 4 := by
    have h := (SimpleGraph.isTree_starGraph (0 : Fin 5)).card_edgeFinset
    change G.edgeFinset.card + 1 = Fintype.card (Fin 5) at h
    simp only [Fintype.card_fin] at h
    omega
  have hfun : (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G.Adj i j ∧ x i = true ∧ x j = true)) = (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) := by
    decide
  have h4 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
    have h := PEqualNP.MetaComplexity.L105 5 G {0} hedge hcover
    have h4g : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G.Adj i j ∧ x i = true ∧ x j = true)) 4 := by
      simpa [hcard] using h
    rwa [hfun] at h4g
  intro s
  constructor
  · intro hs
    rw [← hfun] at hs
    have h := PEqualNP.MetaComplexity.L104 5 1 s G (SimpleGraph.isAcyclic_starGraph 0) hedge hmin hs
    rw [hcard] at h
    omega
  · intro hs
    rcases h4 with ⟨C, hC, hsize, heval⟩
    exact ⟨C, hC, hsize.trans hs, heval⟩
