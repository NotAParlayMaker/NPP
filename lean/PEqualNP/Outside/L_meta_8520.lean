import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8520

theorem key (b : Bool) (i j : ℕ) :
    ∃ g : Gate, (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      ∀ x : List Bool, g.op.eval (g.inputs.map fun k => x.getD k false)
        = (if i = (56 : ℕ) then b else if b = Bool.true then x.getD i Bool.false && x.getD j Bool.false
            else x.getD i Bool.false || x.getD j Bool.false) := by
  by_cases hi : i = 56
  · cases b with
    | true =>
      exact ⟨⟨GateOp.and, []⟩, ⟨Set.mem_insert _ _, by simp⟩,
        fun x => by simp [GateOp.eval, hi]⟩
    | false =>
      exact ⟨⟨GateOp.or, []⟩, ⟨Set.mem_insert_of_mem _ (Set.mem_singleton _), by simp⟩,
        fun x => by simp [GateOp.eval, hi]⟩
  · cases b with
    | true =>
      exact ⟨⟨GateOp.and, [i, j]⟩, ⟨Set.mem_insert _ _, by simp⟩,
        fun x => by simp [GateOp.eval, hi]⟩
    | false =>
      exact ⟨⟨GateOp.or, [i, j]⟩, ⟨Set.mem_insert_of_mem _ (Set.mem_singleton _), by simp⟩,
        fun x => by simp [GateOp.eval, hi]⟩

theorem main (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (b : Bool) (i j : ℕ) :
    ∃ (C6 : Circuit), PEqualNP.MetaComplexity.Monotone2 C6 ∧ C6.size ≤ C.size + (1 : ℕ) ∧
      ∀ (x : List Bool), C6.eval x = C.eval (x ++ [if i = (56 : ℕ) then b else
        if b = Bool.true then x.getD i Bool.false && x.getD j Bool.false
        else x.getD i Bool.false || x.getD j Bool.false]) := by
  obtain ⟨g, hg, hgv⟩ := key b i j
  refine ⟨⟨g :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g2 hg2
    rcases List.mem_cons.1 hg2 with h | h
    · rw [h]
      exact hg
    · exact hC g2 h
  · show (g :: C.gates).length ≤ C.gates.length + 1
    simp
  · intro x
    rw [← hgv x]
    rfl

end PEqualNP.Outside.L_meta_8520

theorem PEqualNP.Outside.L_meta_8520 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 : Bool) (x4 x5 : ℕ), ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x7 : List Bool), x6.eval x7 = x1.eval (x7 ++ [if x4 = (56 : ℕ) then x3 else if x3 = Bool.true then x7.getD x4 Bool.false && x7.getD x5 Bool.false else x7.getD x4 Bool.false || x7.getD x5 Bool.false]) := by
  intro x1 h x3 x4 x5
  exact PEqualNP.Outside.L_meta_8520.main x1 h x3 x4 x5
