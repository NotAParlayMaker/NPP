import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2403
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem ofFn_last {n : ℕ} (x : Fin n → Bool) (a : Bool) :
    List.ofFn (Fin.lastCases a x) = List.ofFn x ++ [a] := by
  rw [List.ofFn_succ']
  simp

theorem ofFn_read {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp only [List.getElem_ofFn]

theorem extend (u : Fin 26) (b : Bool) (C : Circuit) (hm : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 1 ∧
      ∀ x : Fin 26 → Bool, circuitFun 26 D x =
        circuitFun 27 C (Fin.lastCases (if b = true then x 0 && x u else x 0 || x u) x) := by
  let g : Gate := ⟨if b = true then GateOp.and else GateOp.or, [0, u.val]⟩
  refine ⟨⟨g :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · cases b <;> simp [g]
    · exact hm h hh
  · simp [Circuit.size]
  · intro x
    have hl : List.ofFn (Fin.lastCases (if b = true then x 0 && x u else x 0 || x u) x)
        = List.ofFn x ++ [if b = true then x 0 && x u else x 0 || x u] := by
      exact ofFn_last x _
    have hv : g.op.eval (g.inputs.map (fun i => (List.ofFn x).getD i false))
        = if b = true then x 0 && x u else x 0 || x u := by
      have h0 : (List.ofFn x).getD 0 false = x 0 := ofFn_read x 0
      have hu : (List.ofFn x).getD u.val false = x u := ofFn_read x u
      simp only [g, List.map_cons, List.map_nil, h0, hu]
      cases b <;> simp [GateOp.eval]
    unfold circuitFun
    rw [hl]
    simp only [Circuit.eval, Circuit.wires, List.foldl_cons]
    rw [hv]

end PEqualNP.Outside.L_meta_2403

theorem PEqualNP.Outside.L_meta_2403 : ∀ (x1 : Fin (26 : ℕ)) (x2 : Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x3 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x3.size + (1 : ℕ) ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x7 = PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x3 fun (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x2 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x1 else x7 (0 : Fin (26 : ℕ)) || x7 x1) x7 x8 := by
  intro u b C hm _
  exact L_meta_2403.extend u b C hm
