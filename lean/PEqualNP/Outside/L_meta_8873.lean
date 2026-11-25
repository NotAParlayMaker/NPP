import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8873

open PEqualNP.CircuitLowerBounds

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def stepN (w : List ℕ) (g : Gate) : List ℕ :=
  w ++ [if g.op.eval [true, false] then w.getD (g.inputs.getD 0 0) 0 ||| w.getD (g.inputs.getD 1 0) 0
    else w.getD (g.inputs.getD 0 0) 0 &&& w.getD (g.inputs.getD 1 0) 0]

theorem getD_map_testBit (ws : List ℕ) (a j : ℕ) :
    (ws.map fun n => n.testBit j).getD a false = (ws.getD a 0).testBit j := by
  by_cases h : a < ws.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp

theorem fold_sim (j : ℕ) : ∀ (gs : List Gate),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) → ∀ (ws : List ℕ),
    (gs.foldl stepN ws).map (fun n => n.testBit j) = gs.foldl stepW (ws.map fun n => n.testBit j)
  | [], _, ws => rfl
  | g :: gs, hg, ws => by
    rw [List.foldl_cons, List.foldl_cons, fold_sim j gs (fun g' h' => hg g' (List.mem_cons_of_mem g h'))]
    congr 1
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    unfold stepN stepW
    rw [List.map_append, hab]
    congr 1
    rcases hop with hop | hop <;> rw [hop] <;>
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons,
        List.all_nil, id_eq, Bool.or_false, Bool.and_true, Bool.true_and, Bool.false_and, Bool.true_or,
        Bool.false_or, Bool.and_false, getD_map_testBit, Nat.testBit_or, Nat.testBit_and, List.getD_cons_zero,
        List.getD_cons_succ, Bool.false_eq_true, if_false, if_true, ite_true, ite_false]

end PEqualNP.Outside.L_meta_8873

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.Outside.L_meta_8873 in
theorem PEqualNP.Outside.L_meta_8873 :
    ∀ (n : ℕ) (C : Circuit), IsAO2 n C → ∀ (initial : List ℕ) (r : ℕ),
    let step := fun (w : List ℕ) (g : Gate) =>
      let a := w.getD (g.inputs.getD 0 0) 0
      let b := w.getD (g.inputs.getD 1 0) 0
      w ++ [if g.op.eval [true, false] then a ||| b else a &&& b]
    ((C.gates.foldl step initial).getD C.output 0).testBit r =
      C.eval (initial.map fun a => a.testBit r) := by
  intro n C hC initial r step
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g h => ⟨hC.1 g h, hC.2.2 g h⟩
  have := fold_sim r C.gates hg initial
  show ((C.gates.foldl stepN initial).getD C.output 0).testBit r = _
  rw [← getD_map_testBit, this]
  rfl
