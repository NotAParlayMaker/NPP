import Mathlib
import PEqualNP.Defs

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
  intro n G _ htri hsq u v huv
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri v a b ⟨ha, hab, hb.symm⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact htri u a b ⟨ha, hab, hb.symm⟩
  · intro a ha b hb hab
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ⟨hva, hau⟩ | ⟨hua, hav⟩ <;> rcases hb with ⟨hvb, hbu⟩ | ⟨hub, hbv⟩
    · exact htri v a b ⟨hva, hab, hvb.symm⟩
    · exact hsq u v a b (Ne.symm hau) (Ne.symm hbv) ⟨huv, hva, hab, hub.symm⟩
    · exact hsq v u a b (Ne.symm hav) (Ne.symm hbu) ⟨huv.symm, hua, hab, hvb.symm⟩
    · exact htri u a b ⟨hua, hab, hub.symm⟩
