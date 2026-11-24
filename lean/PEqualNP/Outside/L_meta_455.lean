import Mathlib
import PEqualNP.Defs

/-- Around an edge of a graph with no triangle and no 4-cycle, the neighbourhoods are independent. -/
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
  intro n G _ htri hfour u v huv
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha2 : G.Adj v a := (Finset.mem_filter.mp ha).2
    have hb2 : G.Adj v b := (Finset.mem_filter.mp hb).2
    exact htri a b v ⟨hab, hb2.symm, ha2⟩
  · intro a ha b hb hab
    have ha2 : G.Adj u a := (Finset.mem_filter.mp ha).2
    have hb2 : G.Adj u b := (Finset.mem_filter.mp hb).2
    exact htri a b u ⟨hab, hb2.symm, ha2⟩
  · intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp hb with hb | hb
      · have ha2 : G.Adj v a ∧ a ≠ u := (Finset.mem_filter.mp ha).2
        have hb2 : G.Adj v b ∧ b ≠ u := (Finset.mem_filter.mp hb).2
        exact htri a b v ⟨hab, hb2.1.symm, ha2.1⟩
      · have ha2 : G.Adj v a ∧ a ≠ u := (Finset.mem_filter.mp ha).2
        have hb2 : G.Adj u b ∧ b ≠ v := (Finset.mem_filter.mp hb).2
        exact hfour v a b u hb2.2.symm ha2.2 ⟨ha2.1, hab, hb2.1.symm, huv⟩
    · rcases Finset.mem_union.mp hb with hb | hb
      · have ha2 : G.Adj u a ∧ a ≠ v := (Finset.mem_filter.mp ha).2
        have hb2 : G.Adj v b ∧ b ≠ u := (Finset.mem_filter.mp hb).2
        exact hfour u a b v hb2.2.symm ha2.2 ⟨ha2.1, hab, hb2.1.symm, huv.symm⟩
      · have ha2 : G.Adj u a ∧ a ≠ v := (Finset.mem_filter.mp ha).2
        have hb2 : G.Adj u b ∧ b ≠ v := (Finset.mem_filter.mp hb).2
        exact htri a b u ⟨hab, hb2.1.symm, ha2.1⟩
