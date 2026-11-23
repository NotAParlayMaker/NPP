import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta311

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = w.length + (g :: gs).length
    rw [ih]
    simp [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem run_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = w.getD i false
    have hle : w.length ≤ (step w g).length := by simp [step]
    rw [ih (step w g) (lt_of_lt_of_le hi hle)]
    exact List.getD_append _ _ _ _ hi

theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp only [run, List.foldl_append]

end PEqualNP.Outside.Meta311

theorem PEqualNP.Outside.L_meta_311 : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (o o' : ℕ) (x : List Bool) (i : ℕ), i < x.length + gs.length → (PEqualNP.CircuitLowerBounds.Circuit.wires (PEqualNP.CircuitLowerBounds.Circuit.mk (gs ++ hs) o) x).getD i false = (PEqualNP.CircuitLowerBounds.Circuit.wires (PEqualNP.CircuitLowerBounds.Circuit.mk gs o') x).getD i false := by
  intro gs hs o o' x i hi
  change (PEqualNP.Outside.Meta311.run (gs ++ hs) x).getD i false =
    (PEqualNP.Outside.Meta311.run gs x).getD i false
  rw [PEqualNP.Outside.Meta311.run_append]
  apply PEqualNP.Outside.Meta311.run_prefix
  simpa only [PEqualNP.Outside.Meta311.run_length] using hi
