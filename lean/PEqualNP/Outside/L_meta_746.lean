import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L746

open PEqualNP.MetaComplexity

theorem fun_eq : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) =
    (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4,
      (SimpleGraph.starGraph (0 : Fin 4)).Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [SimpleGraph.starGraph_adj, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ((⟨h0, h1⟩ | ⟨h0, h2⟩) | ⟨h0, h3⟩)
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 2, by decide, h0, h2⟩
    · exact ⟨0, 3, by decide, h0, h3⟩
  · rintro ⟨i, j, ⟨hne, hij⟩, hi, hj⟩
    fin_cases i <;> fin_cases j <;> simp_all

theorem card_edges : (SimpleGraph.starGraph (0 : Fin 4)).edgeFinset.card = 3 := by
  decide

theorem main (s : ℕ) :
    HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) s ↔
      3 ≤ s := by
  rw [fun_eq]
  constructor
  · intro h
    have hb := PEqualNP.MetaComplexity.L104 4 1 s (SimpleGraph.starGraph (0 : Fin 4))
      (SimpleGraph.isAcyclic_starGraph 0) ⟨0, 1, by simp⟩
      (fun T hT => by
        rcases hT 0 1 (by simp) with h | h <;> exact Finset.card_pos.mpr ⟨_, h⟩) h
    rw [card_edges] at hb
    omega
  · intro hs
    obtain ⟨C, h1, h2, h3⟩ := PEqualNP.MetaComplexity.L105 4 (SimpleGraph.starGraph (0 : Fin 4))
      {0} ⟨0, 1, by simp⟩ (fun i j h => by
        simp only [SimpleGraph.starGraph_adj, Finset.mem_singleton] at h ⊢
        exact h.2)
    refine ⟨C, h1, ?_, h3⟩
    rw [card_edges, Finset.card_singleton] at h2
    omega

end PEqualNP.Outside.L746

theorem PEqualNP.Outside.L_meta_746 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) s ↔ 3 ≤ s := by
  intro s
  exact PEqualNP.Outside.L746.main s
