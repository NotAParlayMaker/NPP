import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18189_aux

open PEqualNP.CircuitLowerBounds

private def step (w : List ℕ) (g : Gate) : List ℕ :=
  let a := w.getD (g.inputs.getD 0 0) 0
  let b := w.getD (g.inputs.getD 1 0) 0
  w ++ [bif g.op.eval [false, true] then a ||| b else a &&& b]

private theorem atBit (w : List ℕ) (k i : ℕ) :
    (w.map (fun x => x.testBit k)).getD i false = (w.getD i 0).testBit k := by
  simpa using (List.getD_map w 0 (fun x : ℕ => x.testBit k) (n := i))

private theorem optionBit (w : List ℕ) (k i : ℕ) :
    (w[i]?.map (fun x => x.testBit k)).getD false = (w[i]?.getD 0).testBit k := by
  cases w[i]? <;> simp

private theorem foldMap (gates : List Gate)
    (h : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧
      ∃ a b : ℕ, g.inputs = [a, b]) (w : List ℕ) (k : ℕ) :
    gates.foldl
      (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
      (w.map fun x => x.testBit k) =
      (gates.foldl step w).map (fun x => x.testBit k) := by
  induction gates generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hop, a, b, hab⟩ := h g List.mem_cons_self
    have hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] :=
      fun q hq => h q (List.mem_cons_of_mem g hq)
    simp only [List.foldl_cons]
    have hs :
        (w.map fun x => x.testBit k) ++
          [g.op.eval (g.inputs.map fun i => (w.map fun x => x.testBit k).getD i false)] =
        (step w g).map (fun x => x.testBit k) := by
      rcases hop with ho | ho <;>
        simp [step, hab, ho, GateOp.eval, optionBit]
    rw [hs]
    exact ih hgs _

theorem witness : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x2 ∈ x1.gates, (x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x4 : ℕ) (x5 : ℕ), x2.inputs = [x4, x5]) →     ∀ (x3 : List ℕ) (x4 : ℕ),       x1.eval (List.map (fun (x5 : ℕ) => x5.testBit x4) x3) =         ((List.foldl                   (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) =>                     have x7 : ℕ := x5.getD (x6.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                     have x8 : ℕ := x5.getD (x6.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                     x5 ++ [bif x6.op.eval [Bool.false, Bool.true] then x7 ||| x8 else x7 &&& x8])                   x3 x1.gates).getD               x1.output (0 : ℕ)).testBit           x4 := by
  intro C h w k
  change (C.wires (w.map fun x => x.testBit k)).getD C.output false =
    ((C.gates.foldl step w).getD C.output 0).testBit k
  rw [Circuit.wires, foldMap C.gates h]
  exact atBit _ _ _

end PEqualNP.Outside.L_meta_18189_aux

theorem PEqualNP.Outside.L_meta_18189 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x2 ∈ x1.gates, (x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x4 : ℕ) (x5 : ℕ), x2.inputs = [x4, x5]) →     ∀ (x3 : List ℕ) (x4 : ℕ),       x1.eval (List.map (fun (x5 : ℕ) => x5.testBit x4) x3) =         ((List.foldl                   (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) =>                     have x7 : ℕ := x5.getD (x6.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                     have x8 : ℕ := x5.getD (x6.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                     x5 ++ [bif x6.op.eval [Bool.false, Bool.true] then x7 ||| x8 else x7 &&& x8])                   x3 x1.gates).getD               x1.output (0 : ℕ)).testBit           x4 :=
  PEqualNP.Outside.L_meta_18189_aux.witness
