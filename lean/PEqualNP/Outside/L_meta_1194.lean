import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1194

open PEqualNP.CircuitLowerBounds

def ckt : Circuit :=
  { gates :=
      [ { op := GateOp.or,  inputs := [1, 2] }
      , { op := GateOp.or,  inputs := [8, 3] }
      , { op := GateOp.and, inputs := [0, 9] }
      , { op := GateOp.or,  inputs := [4, 5] }
      , { op := GateOp.and, inputs := [1, 11] }
      , { op := GateOp.or,  inputs := [2, 7] }
      , { op := GateOp.and, inputs := [6, 13] }
      , { op := GateOp.or,  inputs := [10, 12] }
      , { op := GateOp.or,  inputs := [15, 14] }
      ]
  , output := 16 }

def edgeFun (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) ||
  (x 1 && x 4) || (x 1 && x 5) ||
  (x 2 && x 6) || (x 6 && x 7)

-- Monotone2 ckt: all 9 gates are and/or with exactly 2 inputs.
lemma ckt_monotone2 : PEqualNP.MetaComplexity.Monotone2 ckt := by
  intro g hg
  simp only [ckt, Circuit.gates, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, false_or] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨by simp, by simp⟩

lemma ckt_size : ckt.size ≤ 9 := by
  simp [ckt, Circuit.size]

set_option maxRecDepth 200000 in
lemma ckt_eval : ∀ x : Fin 8 → Bool, ckt.eval (List.ofFn x) = edgeFun x := by
  decide

end PEqualNP.Outside.L_meta_1194

theorem PEqualNP.Outside.L_meta_1194 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1194.ckt, PEqualNP.Outside.L_meta_1194.ckt_monotone2, PEqualNP.Outside.L_meta_1194.ckt_size, ?_⟩
  intro x
  have h := PEqualNP.Outside.L_meta_1194.ckt_eval x
  exact h
