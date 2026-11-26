import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.ReadK

namespace PEqualNP.Outside.L_meta_18189
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem checked : ∀ (C : Circuit), (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) → ∀ (w : List ℕ) (k : ℕ),
      C.eval (w.map (fun z => z.testBit k)) = ((C.gates.foldl (fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [bif g.op.eval [false,true] then a ||| b else a &&& b]) w).getD C.output 0).testBit k := by
  intro C hC w k
  let packed (w : List ℕ) (g : Gate) : List ℕ :=
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [bif g.op.eval [false,true] then a ||| b else a &&& b]
  let stepB (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have get (w : List ℕ) (i : ℕ) : (w.map (fun z => z.testBit k)).getD i false = (w.getD i 0).testBit k := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[i]? <;> simp
  have step_eq (ws : List ℕ) (g : Gate) (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) :
      stepB (ws.map (fun z => z.testBit k)) g = (packed ws g).map (fun z => z.testBit k) := by
    obtain ⟨op,a,b,ab⟩ := h
    rcases op with op|op <;> simp [stepB,packed,op,ab,GateOp.eval,get,Nat.testBit_and,Nat.testBit_or]
    all_goals cases ws[a]? <;> cases ws[b]? <;> simp
  have run (gs : List Gate) (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) (ws : List ℕ) :
      gs.foldl stepB (ws.map (fun z => z.testBit k)) = (gs.foldl packed ws).map (fun z => z.testBit k) := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons,step_eq ws g (h g List.mem_cons_self)]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _
  change (C.gates.foldl stepB (w.map (fun z => z.testBit k))).getD C.output false = _
  rw [run C.gates hC w]
  exact get _ _
end PEqualNP.Outside.L_meta_18189

theorem PEqualNP.Outside.L_meta_18189 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x2 ∈ x1.gates, (x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x4 : ℕ) (x5 : ℕ), x2.inputs = [x4, x5]) →     ∀ (x3 : List ℕ) (x4 : ℕ),       x1.eval (List.map (fun (x5 : ℕ) => x5.testBit x4) x3) =         ((List.foldl                   (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) =>                     have x7 : ℕ := x5.getD (x6.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                     have x8 : ℕ := x5.getD (x6.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                     x5 ++ [bif x6.op.eval [Bool.false, Bool.true] then x7 ||| x8 else x7 &&& x8])                   x3 x1.gates).getD               x1.output (0 : ℕ)).testBit           x4 := @PEqualNP.Outside.L_meta_18189.checked
