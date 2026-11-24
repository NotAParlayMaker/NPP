import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_477

open PEqualNP.CircuitLowerBounds

lemma wires_length_aux :
    ∀ (gs : List Gate) (x : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
        = x.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro x; simp
  | cons g gs ih =>
    intro x
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end PEqualNP.Outside.L_meta_477

theorem PEqualNP.Outside.L_meta_477 :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool),
      (C.wires x).length = x.length + C.gates.length := by
  intro C x
  exact PEqualNP.Outside.L_meta_477.wires_length_aux C.gates x
