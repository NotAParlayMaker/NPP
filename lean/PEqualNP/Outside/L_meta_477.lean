import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_477

open PEqualNP.CircuitLowerBounds

private lemma foldl_wires_length (gs : List Gate) (w0 : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  exact foldl_wires_length C.gates x

end PEqualNP.Outside.L_meta_477

theorem PEqualNP.Outside.L_meta_477 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool),
    (C.wires x).length = x.length + C.gates.length := by
  intro C x
  exact PEqualNP.Outside.L_meta_477.wires_length C x
