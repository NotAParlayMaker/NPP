import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_455

-- helpers go here

end PEqualNP.Outside.L_meta_455

theorem PEqualNP.Outside.L_meta_455 :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
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
  intro n G hdec htri hquad u v huv
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri v a b ⟨ha, hab, hb.symm⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri u a b ⟨ha, hab, hb.symm⟩
  · intro a ha b hb hab
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨hav, hau⟩ | ⟨hau, hav⟩
    · rcases hb with ⟨hbv, hbu⟩ | ⟨hbu, hbv⟩
      · exact htri v a b ⟨hav, hab, hbv.symm⟩
      · exact hquad u v a b hau.symm hbv.symm ⟨huv, hav, hab, hbu.symm⟩
    · rcases hb with ⟨hbv, hbu⟩ | ⟨hbu, hbv⟩
      · exact hquad u v b a hbu.symm hav.symm ⟨huv, hbv, hab.symm, hau.symm⟩
      · exact htri u a b ⟨hau, hab, hbu.symm⟩
