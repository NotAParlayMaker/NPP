import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2438_aux

open PEqualNP.CircuitLowerBounds

theorem ofFn_last {n : ℕ} (x : Fin n → Bool) (v : Bool) :
    List.ofFn (fun (y : Fin (n + 1)) => Fin.lastCases v x y) = List.ofFn x ++ [v] := by
  rw [List.ofFn_succ']
  simp only [Fin.lastCases_castSucc, List.concat_eq_append, Fin.lastCases_last]

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp

end PEqualNP.Outside.L_meta_2438_aux

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2438 : ∀ (x1 : Fin (42 : ℕ)) (x2 x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x4 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 →       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x7 ∧           x7.size ≤ x4.size + (2 : ℕ) ∧             ∀ (x8 : Fin (42 : ℕ) → Bool),               have x9 : Fin (43 : ℕ) → Bool := fun (x9 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x8 (0 : Fin (42 : ℕ)) || x8 x1) x8 x9;               x7.eval (List.ofFn x8) = x4.eval (List.ofFn fun (x10 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x9 x2 || x9 x3) x9 x10) := by
  intro a b c C hC _
  refine ⟨⟨⟨GateOp.or, [0, a.val]⟩ :: ⟨GateOp.or, [b.val, c.val]⟩ :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with h | h
    · subst h; simp
    rcases List.mem_cons.mp h with h | h
    · subst h; simp
    · exact hC g h
  · simp [Circuit.size]
  · intro x
    simp only [Circuit.eval, Circuit.wires, List.foldl_cons]
    have h0 := PEqualNP.Outside.L_meta_2438_aux.getD_ofFn x 0
    have ha := PEqualNP.Outside.L_meta_2438_aux.getD_ofFn x a
    have e : List.ofFn x ++ [GateOp.or.eval ([0, a.val].map fun i => (List.ofFn x).getD i false)] = List.ofFn (fun (z : Fin (42 + 1)) => Fin.lastCases (x 0 || x a) x z) := by
      rw [PEqualNP.Outside.L_meta_2438_aux.ofFn_last]
      congr 2
      simp only [List.map_cons, List.map_nil]
      rw [show ((0 : ℕ)) = (0 : Fin 42).val from rfl, h0, ha]
      simp [GateOp.eval]
    rw [e]
    have hb := PEqualNP.Outside.L_meta_2438_aux.getD_ofFn (fun (z : Fin (42 + 1)) => Fin.lastCases (x 0 || x a) x z) b
    have hc := PEqualNP.Outside.L_meta_2438_aux.getD_ofFn (fun (z : Fin (42 + 1)) => Fin.lastCases (x 0 || x a) x z) c
    rw [PEqualNP.Outside.L_meta_2438_aux.ofFn_last (fun (z : Fin (42 + 1)) => Fin.lastCases (x 0 || x a) x z)]
    congr 3
    simp only [List.map_cons, List.map_nil]
    rw [hb, hc]
    simp [GateOp.eval]
