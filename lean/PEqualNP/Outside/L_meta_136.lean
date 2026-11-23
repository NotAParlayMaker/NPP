import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

theorem PEqualNP.Outside.L_meta_136 : ∃ (A : Fin 4 → Finset (Sym2 (Fin 4))) (B : Fin 4 → Finset (Finset (Fin 4))) (t : Fin 4 → Fin 4), (∀ i, ∀ e ∈ A i, e ∈ (SimpleGraph.cycleGraph 4).edgeFinset ∧ t i ∈ e) ∧ (∀ i, ∀ I ∈ B i, t i ∉ I) ∧ (∀ e ∈ (SimpleGraph.cycleGraph 4).edgeFinset, ∀ I : Finset (Fin 4), (∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.cycleGraph 4).Adj u w) → ∃! i : Fin 4, e ∈ A i ∧ I ∈ B i) := by
  -- Rectangle `i` is labelled by vertex `i`; it takes both edges at `i`. Even vertices take
  -- the independent sets avoiding `0` and `2`, odd vertices the nonempty ones avoiding `1`, `3`.
  refine ⟨fun i => (SimpleGraph.cycleGraph 4).edgeFinset.filter (fun e => i ∈ e),
    fun i => if i.val % 2 = 0 then {∅, {1}, {3}, {1, 3}} else {{0}, {2}, {0, 2}}, id,
    ?_, ?_, ?_⟩
  · intro i e he
    exact Finset.mem_filter.1 he
  · decide
  · unfold ExistsUnique
    decide
