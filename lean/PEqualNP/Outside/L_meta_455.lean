import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_455
end PEqualNP.Outside.L_meta_455

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_455 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) →
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ u v : Fin n, G.Adj u v →
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b) ∧
      (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
        ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
              Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b) := by
  intro n G _ htri hc4 u v huv
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri v a b ⟨ha, hab, SimpleGraph.Adj.symm hb⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri u a b ⟨ha, hab, SimpleGraph.Adj.symm hb⟩
  · intro a ha b hb hab
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨hva, hane⟩ | ⟨hua, hav⟩ <;> rcases hb with ⟨hvb, hbne⟩ | ⟨hub, hbve⟩
    · exact htri v a b ⟨hva, hab, SimpleGraph.Adj.symm hvb⟩
    · exact hc4 u v a b (Ne.symm hane) (Ne.symm hbve) ⟨huv, hva, hab, SimpleGraph.Adj.symm hub⟩
    · exact hc4 u a b v (Ne.symm hbne) hav ⟨hua, hab, SimpleGraph.Adj.symm hvb, SimpleGraph.Adj.symm huv⟩
    · exact htri u a b ⟨hua, hab, SimpleGraph.Adj.symm hub⟩
