import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_312_aux

private lemma foldl_wires_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [List.length_append, List.length_singleton]
      omega

end PEqualNP.Outside.L_meta_312_aux

theorem PEqualNP.Outside.L_meta_312 :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool),
      (C.wires x).length = x.length + C.gates.length :=
  fun C x => PEqualNP.Outside.L_meta_312_aux.foldl_wires_length C.gates x
