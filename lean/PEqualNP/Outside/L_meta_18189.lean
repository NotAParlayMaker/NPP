import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18189_aux

open PEqualNP.CircuitLowerBounds

theorem hget (acc : List ℕ) (k i : ℕ) :
    (acc.map (fun x => x.testBit k)).getD i false = (acc.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases acc[i]? <;> simp

theorem main (k : ℕ) (gs : List Gate) :
    ∀ (acc : List ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    List.map (fun (x : ℕ) => x.testBit k)
      (List.foldl (fun (x6 : List ℕ) (x7 : Gate) =>
                   have x8 : ℕ := x6.getD (x7.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
                   have x9 : ℕ := x6.getD (x7.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
                   x6 ++ [bif x7.op.eval [Bool.false, Bool.true] then x8 ||| x9 else x8 &&& x9]) acc gs)
    = List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.map (fun (x : ℕ) => x.testBit k) acc) gs := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g t ih =>
    intro acc h
    have hg := h g (by simp)
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun g' hg' => h g' (by simp [hg']))]
    congr 1
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, hl⟩ := hg
    match inputs, hl with
    | [a, b], _ =>
      rcases hop with hop | hop <;> simp only at hop <;> subst hop <;>
        simp [GateOp.eval, Nat.testBit_or, Nat.testBit_and] <;>
        cases acc[a]? <;> cases acc[b]? <;> simp

end PEqualNP.Outside.L_meta_18189_aux

theorem PEqualNP.Outside.L_meta_18189 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x2 ∈ x1.gates, (x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x4 : ℕ) (x5 : ℕ), x2.inputs = [x4, x5]) →     ∀ (x3 : List ℕ) (x4 : ℕ),       x1.eval (List.map (fun (x5 : ℕ) => x5.testBit x4) x3) =         ((List.foldl                   (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) =>                     have x7 : ℕ := x5.getD (x6.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                     have x8 : ℕ := x5.getD (x6.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                     x5 ++ [bif x6.op.eval [Bool.false, Bool.true] then x7 ||| x8 else x7 &&& x8])                   x3 x1.gates).getD               x1.output (0 : ℕ)).testBit           x4 := by
  intro C shape acc k
  rw [← PEqualNP.Outside.L_meta_18189_aux.hget]
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  symm
  apply congrArg (fun w => List.getD w C.output false)
  apply PEqualNP.Outside.L_meta_18189_aux.main
  intro g hg
  obtain ⟨op, a, b, hab⟩ := shape g hg
  exact ⟨op, by simp [hab]⟩
