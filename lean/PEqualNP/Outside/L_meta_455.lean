import Mathlib.Combinatorics.SimpleGraph.Basic

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
  intro n G _ htri hquad u v huv
  have hnbr : ∀ z a b : Fin n, G.Adj z a → G.Adj z b → ¬ G.Adj a b := by
    intro z a b hza hzb hab
    exact htri z a b ⟨hza, hab, hzb.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    exact hnbr v a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  · intro a ha b hb
    exact hnbr u a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  · intro a ha b hb hab
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hnbr v a b ha.1 hb.1 hab
    · exact hquad u v a b (Ne.symm ha.2) (Ne.symm hb.2)
        ⟨huv, ha.1, hab, hb.1.symm⟩
    · exact hquad v u a b (Ne.symm ha.2) (Ne.symm hb.2)
        ⟨huv.symm, ha.1, hab, hb.1.symm⟩
    · exact hnbr u a b ha.1 hb.1 hab

