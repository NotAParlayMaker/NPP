import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Tactic.FinCases
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside

open PEqualNP.MetaComplexity

private lemma edgeCount : (SimpleGraph.starGraph (0 : Fin 4)).edgeFinset.card = 3 := by
  have h := (SimpleGraph.isTree_starGraph (0 : Fin 4)).card_edgeFinset
  rw [Fintype.card_fin] at h
  omega

private lemma starFunction :
    (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4,
      (SimpleGraph.starGraph 0).Adj i j ∧ x i = true ∧ x j = true)) =
    (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i, j, hadj, hi, hj⟩
    fin_cases i <;> fin_cases j <;>
      simp_all [SimpleGraph.starGraph_adj]
  · rintro ((⟨h0, h1⟩ | ⟨h0, h2⟩) | ⟨h0, h3⟩)
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 2, by decide, h0, h2⟩
    · exact ⟨0, 3, by decide, h0, h3⟩

theorem L_meta_746 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) s ↔ 3 ≤ s := by
  intro s
  rw [← starFunction]
  have adj : (SimpleGraph.starGraph (0 : Fin 4)).Adj 0 1 := by decide
  have edge : ∃ i j : Fin 4, (SimpleGraph.starGraph 0).Adj i j := ⟨0, 1, adj⟩
  constructor
  · intro hc
    have coverLower (T : Finset (Fin 4))
        (hT : ∀ i j : Fin 4, (SimpleGraph.starGraph 0).Adj i j → i ∈ T ∨ j ∈ T) :
        1 ≤ T.card := by
      obtain h | h := hT 0 1 adj
      · exact Finset.card_pos.mpr ⟨0, h⟩
      · exact Finset.card_pos.mpr ⟨1, h⟩
    have h := L104 4 1 s (SimpleGraph.starGraph 0)
      (SimpleGraph.isAcyclic_starGraph 0) edge coverLower hc
    rw [edgeCount] at h
    omega
  · intro hs
    have cover (i j : Fin 4) (hij : (SimpleGraph.starGraph 0).Adj i j) :
        i ∈ ({0} : Finset (Fin 4)) ∨ j ∈ ({0} : Finset (Fin 4)) := by
      simpa only [Finset.mem_singleton] using (SimpleGraph.starGraph_adj.mp hij).2
    have h := L105 4 (SimpleGraph.starGraph 0) {0} edge cover
    rw [edgeCount, Finset.card_singleton] at h
    obtain ⟨C, hC, hsize, heval⟩ := h
    exact ⟨C, hC, le_trans hsize hs, heval⟩

end PEqualNP.Outside
