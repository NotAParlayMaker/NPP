import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4637

open PEqualNP.CircuitLowerBounds

def clampGate (bound : ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map fun i => min i bound }

lemma getD_min_of_length_le (w : List Bool) (i bound : ℕ) (h : w.length ≤ bound) :
    w.getD (min i bound) false = w.getD i false := by
  rcases le_or_gt i bound with hi | hi
  · rw [min_eq_left hi]
  · rw [min_eq_right (le_of_lt hi)]
    rw [List.getD_eq_default _ _ (le_of_lt (Nat.lt_of_le_of_lt h hi))]
    rw [List.getD_eq_default _ _ h]

lemma clampGate_eval (bound : ℕ) (g : Gate) (acc : List Bool) (hacc : acc.length ≤ bound) :
    (clampGate bound g).op.eval
        ((clampGate bound g).inputs.map fun j => acc.getD j false) =
      g.op.eval (g.inputs.map fun i => acc.getD i false) := by
  simp only [clampGate]
  refine congrArg (g.op.eval) ?_
  rw [List.map_map]
  refine List.map_congr_left ?_
  intro i _hi
  exact getD_min_of_length_le acc i bound hacc

lemma foldl_clamp (bound : ℕ) (acc : List Bool) (gs : List Gate)
    (h : acc.length + gs.length ≤ bound) :
    (gs.map (clampGate bound)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    have hlen : acc.length + (gs.length + 1) ≤ bound := by
      simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have hacc : acc.length ≤ bound :=
      Nat.le_trans (Nat.le_add_right acc.length (gs.length + 1)) hlen
    simp only [List.map_cons, List.foldl_cons]
    rw [clampGate_eval bound g acc hacc]
    refine ih (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) ?_
    have : (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]).length + gs.length =
        acc.length + (gs.length + 1) := by
      simp [List.length_append, Nat.add_comm, Nat.add_left_comm]
    exact this ▸ hlen

lemma clamp_map (bound : ℕ) (gs : List Gate) :
    gs.map (clampGate bound) =
      gs.map fun (g : Gate) =>
        ({ op := g.op, inputs := g.inputs.map fun i => Min.min i bound } : Gate) :=
  rfl

end PEqualNP.Outside.L_meta_4637

theorem PEqualNP.Outside.L_meta_4637 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List Bool), x3.length = x1 → { gates := List.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => { op := x5.op, inputs := List.map (fun (x6 : ℕ) => Min.min x6 (x1 + x2.size)) x5.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x3 = x2.wires x3 := by
  intro n C x hx
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [show (List.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => { op := x5.op, inputs := List.map (fun (x6 : ℕ) => Min.min x6 (n + C.size)) x5.inputs : PEqualNP.CircuitLowerBounds.Gate }) C.gates) = C.gates.map (PEqualNP.Outside.L_meta_4637.clampGate (n + C.size)) from (PEqualNP.Outside.L_meta_4637.clamp_map (n + C.size) C.gates).symm]
  refine PEqualNP.Outside.L_meta_4637.foldl_clamp (n + C.size) x C.gates ?_
  simp [PEqualNP.CircuitLowerBounds.Circuit.size, hx]
