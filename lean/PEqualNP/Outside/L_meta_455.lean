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
    rw [Finset.mem_filter] at ha hb
    exact htri v a b ⟨ha.2, hab, hb.2.symm⟩
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    exact htri u a b ⟨ha.2, hab, hb.2.symm⟩
  · intro a ha b hb hab
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact htri v a b ⟨ha.2.1, hab, hb.2.1.symm⟩
    · exact hsq u v a b (Ne.symm ha.2.2) (Ne.symm hb.2.2) ⟨huv, ha.2.1, hab, hb.2.1.symm⟩
    · exact hsq v u a b (Ne.symm ha.2.2) (Ne.symm hb.2.2) ⟨huv.symm, ha.2.1, hab, hb.2.1.symm⟩
    · exact htri u a b ⟨ha.2.1, hab, hb.2.1.symm⟩
