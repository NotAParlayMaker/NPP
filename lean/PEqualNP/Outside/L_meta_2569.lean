import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_2569 :
    ∀ (n budget : ℕ) (i j : Fin n) (op : GateOp) (C : Circuit),
      op = GateOp.and ∨ op = GateOp.or → Monotone2 C → C.size ≤ budget →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ budget + 1 ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          C.eval (List.ofFn x ++ [op.eval [x i, x j]]) := by
  intro n budget i j op C hop hC hsize
  let first : Gate := ⟨op, [i.val, j.val]⟩
  refine ⟨⟨first :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | old
    · exact ⟨hop, le_rfl⟩
    · exact hC g old
  · exact Nat.succ_le_succ hsize
  · intro x
    simp [Circuit.eval, Circuit.wires, first, List.getD_eq_getElem?_getD]
