import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2403

open PEqualNP.CircuitLowerBounds

theorem ofFn_last (v : Bool) (x : Fin 26 → Bool) :
    List.ofFn (fun k : Fin (26 + 1) => Fin.lastCases v x k) = List.ofFn x ++ [v] := by
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem getD_ofFn (x : Fin 26 → Bool) (i : Fin 26) : (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem getD_ofFn0 (x : Fin 26 → Bool) : (List.ofFn x).getD 0 false = x 0 :=
  getD_ofFn x 0

end PEqualNP.Outside.L_meta_2403

theorem PEqualNP.Outside.L_meta_2403 : ∀ (x1 : Fin (26 : ℕ)) (x2 : Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x3 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x3.size + (1 : ℕ) ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x7 = PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x3 fun (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x2 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x1 else x7 (0 : Fin (26 : ℕ)) || x7 x1) x7 x8 := by
  intro i b C hC _
  refine ⟨⟨(⟨if b = true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, [0, i.val]⟩ : PEqualNP.CircuitLowerBounds.Gate) :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · refine ⟨?_, by simp⟩
      by_cases hb : b = true <;> simp [hb]
    · exact hC g hg
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons]
    rw [PEqualNP.Outside.L_meta_2403.ofFn_last]
    congr 3
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
        PEqualNP.Outside.L_meta_2403.getD_ofFn, PEqualNP.Outside.L_meta_2403.getD_ofFn0]
      simp
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
        PEqualNP.Outside.L_meta_2403.getD_ofFn, PEqualNP.Outside.L_meta_2403.getD_ofFn0]
      simp
