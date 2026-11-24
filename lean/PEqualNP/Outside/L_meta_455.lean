import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_455_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

end PEqualNP.Outside.L_meta_455_aux

open PEqualNP.Outside.L_meta_455_aux

theorem PEqualNP.Outside.L_meta_455 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)) →
      (∀ a b c d : Fin n, a ≠ c → b ≠ d →
        ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      ∀ u v : Fin n, G.Adj u v →
        (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w),
          ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w), ¬ G.Adj a b) ∧
        (∀ a ∈ Finset.univ.filter (fun w => G.Adj u w),
          ∀ b ∈ Finset.univ.filter (fun w => G.Adj u w), ¬ G.Adj a b) ∧
        (∀ a ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
                Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v),
          ∀ b ∈ Finset.univ.filter (fun w => G.Adj v w ∧ w ≠ u) ∪
                Finset.univ.filter (fun w => G.Adj u w ∧ w ≠ v), ¬ G.Adj a b) := by
  intro n G hdec htri hc4 u v huv
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri a b v ⟨hab, hb.symm, ha⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri a b u ⟨hab, hb.symm, ha⟩
  · intro a ha b hb hab
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha hb
    rcases ha with ⟨hva, hneau⟩ | ⟨hua, hneav⟩
    · rcases hb with ⟨hvb, hnebu⟩ | ⟨hub, hnebv⟩
      · exact htri a b v ⟨hab, hvb.symm, hva⟩
      · exact hc4 u v a b hneau.symm hnebv.symm
          ⟨huv, hva, hab, hub.symm⟩
    · rcases hb with ⟨hvb, hnebu⟩ | ⟨hub, hnebv⟩
      · exact hc4 u a b v hnebu.symm hneav
          ⟨hua, hab, hvb.symm, huv.symm⟩
      · exact htri a b u ⟨hab, hub.symm, hua⟩
