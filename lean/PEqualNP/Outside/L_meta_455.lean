import Mathlib.Combinatorics.SimpleGraph.Basic
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
  intro n G _ htri hquad u v huv
  have hind : ∀ w a b : Fin n, G.Adj w a → G.Adj w b → ¬ G.Adj a b := by
    intro w a b hwa hwb hab
    exact htri w a b ⟨hwa, hab, hwb.symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    exact hind v a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  · intro a ha b hb
    exact hind u a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  · intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact hind v a b (Finset.mem_filter.mp ha).2.1
        (Finset.mem_filter.mp hb).2.1 hab
    · obtain ⟨hva, hau⟩ := (Finset.mem_filter.mp ha).2
      obtain ⟨hub, hbv⟩ := (Finset.mem_filter.mp hb).2
      exact hquad v a b u hbv.symm hau ⟨hva, hab, hub.symm, huv⟩
    · obtain ⟨hua, hav⟩ := (Finset.mem_filter.mp ha).2
      obtain ⟨hvb, hbu⟩ := (Finset.mem_filter.mp hb).2
      exact hquad u a b v hbu.symm hav ⟨hua, hab, hvb.symm, huv.symm⟩
    · exact hind u a b (Finset.mem_filter.mp ha).2.1
        (Finset.mem_filter.mp hb).2.1 hab
