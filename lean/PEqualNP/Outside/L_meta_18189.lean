import PEqualNP.Defs
import Mathlib.Data.List.GetD

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_18189 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x2 ∈ x1.gates, (x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x4 : ℕ) (x5 : ℕ), x2.inputs = [x4, x5]) →     ∀ (x3 : List ℕ) (x4 : ℕ),       x1.eval (List.map (fun (x5 : ℕ) => x5.testBit x4) x3) =         ((List.foldl                   (fun (x5 : List ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) =>                     have x7 : ℕ := x5.getD (x6.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                     have x8 : ℕ := x5.getD (x6.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                     x5 ++ [bif x6.op.eval [Bool.false, Bool.true] then x7 ||| x8 else x7 &&& x8])                   x3 x1.gates).getD               x1.output (0 : ℕ)).testBit           x4 := by
  intro C good inputs k
  let bit := fun (a : ℕ) => a.testBit k
  let packed := fun (w : List ℕ) (g : Gate) =>
    let a := w.getD (g.inputs.getD 0 0) 0
    let b := w.getD (g.inputs.getD 1 0) 0
    w ++ [bif g.op.eval [false, true] then a ||| b else a &&& b]
  let boolStep := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have readBit (w : List ℕ) (i : ℕ) : (w.map bit).getD i false = bit (w.getD i 0) := by
    simpa [bit] using (List.getD_map (l := w) (d := 0) (n := i) bit)
  have step (g : Gate) (hg : g ∈ C.gates) (w : List ℕ) :
      boolStep (w.map bit) g = (packed w g).map bit := by
    obtain ⟨hop, i, j, hinputs⟩ := good g hg
    rcases hop with h | h <;>
      simp [boolStep, packed, h, hinputs, GateOp.eval, bit, Nat.testBit_or, Nat.testBit_and] <;>
      cases w[i]? <;> cases w[j]? <;> simp
  have rows (gs : List Gate) (ht : ∀ g ∈ gs, g ∈ C.gates) (w : List ℕ) :
      gs.foldl boolStep (w.map bit) = (gs.foldl packed w).map bit := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [step g (ht g List.mem_cons_self) w]
      exact ih (fun h hh => ht h (List.mem_cons_of_mem _ hh)) _
  change (C.gates.foldl boolStep (inputs.map bit)).getD C.output false =
    bit ((C.gates.foldl packed inputs).getD C.output 0)
  rw [rows C.gates (fun _ h => h) inputs, readBit]
