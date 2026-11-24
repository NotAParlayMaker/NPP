import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4637_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def clamp (cap : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i cap)⟩

-- A clamped forward reference still reads the default value.
theorem step_clamp (cap : ℕ) (w : List Bool) (g : Gate) (h : w.length ≤ cap) :
    step w (clamp cap g) = step w g := by
  have read (i : ℕ) : w.getD (min i cap) false = w.getD i false := by
    by_cases hi : i ≤ cap
    · rw [min_eq_left hi]
    · rw [min_eq_right (by omega)]
      exact (List.getD_eq_default _ _ h).trans (List.getD_eq_default _ _ (by omega)).symm
  have vals : (g.inputs.map (fun i => min i cap)).map (fun i => w.getD i false)
      = g.inputs.map (fun i => w.getD i false) := by
    rw [List.map_map]
    exact List.map_congr_left (fun i _ => read i)
  simp only [step, clamp, vals]

-- The wire count grows by one as the remaining gate count drops by one.
theorem fold_clamp (cap : ℕ) (gs : List Gate) (w : List Bool)
    (h : w.length + gs.length ≤ cap) :
    (gs.map (clamp cap)).foldl step w = gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.length_cons] at h
    simp only [List.map_cons, List.foldl_cons]
    rw [step_clamp cap w g (by omega)]
    apply ih
    simp only [step, List.length_append, List.length_singleton]
    omega

end PEqualNP.Outside.L_meta_4637_aux

theorem PEqualNP.Outside.L_meta_4637 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List Bool), x3.length = x1 → { gates := List.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => { op := x5.op, inputs := List.map (fun (x6 : ℕ) => Min.min x6 (x1 + x2.size)) x5.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x3 = x2.wires x3 := by
  intro n C inputs length_inputs
  exact PEqualNP.Outside.L_meta_4637_aux.fold_clamp (n + C.size) C.gates inputs
    (by simp [length_inputs, PEqualNP.CircuitLowerBounds.Circuit.size])
