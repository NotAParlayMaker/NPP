import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_477_aux

open PEqualNP.CircuitLowerBounds

lemma go (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
      rw [List.foldl_cons]
      rw [ih]
      simp
      omega

end PEqualNP.Outside.L_meta_477_aux

open PEqualNP.Outside.L_meta_477_aux

theorem PEqualNP.Outside.L_meta_477 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool), (C.wires x).length = x.length + C.gates.length := by
  intro C x
  exact go C.gates x
