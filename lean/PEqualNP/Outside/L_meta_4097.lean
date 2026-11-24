import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_4097

private def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wireCount (gs : List Gate) (w : List Bool) :
    (gs.foldl appendGate w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [appendGate]
    omega

private theorem earlierWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl appendGate w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (appendGate w g) (by simp [appendGate]; omega)]
    simp [appendGate, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

end PEqualNP.Outside.L_meta_4097

open PEqualNP.Outside.L_meta_4097

theorem PEqualNP.Outside.L_meta_4097 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ) → Bool) (x3 : ℕ) => (x1.wires (List.ofFn x2)).getD x3 Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (26 : ℕ) → Bool) (x4 x5 x6 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → x2.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } → x1 x2 x3 ((26 : ℕ) + x4) = (x1 x2 x3 x5 && x1 x2 x3 x6) := by
  intro value C x j a b hAO hgate
  obtain ⟨hj, hlookup⟩ := List.getElem?_eq_some_iff.mp hgate
  let g : Gate := ⟨GateOp.and, [a, b]⟩
  have hAt : gateAt C j = g := by
    simp [gateAt, List.getD_eq_getElem?_getD, hgate, g]
  have ha : a < 26 + j := hAO.2.1 j hj a (by simp [hAt, g])
  have hb : b < 26 + j := hAO.2.1 j hj b (by simp [hAt, g])
  let w := (C.gates.take j).foldl appendGate (List.ofFn x)
  let tail := C.gates.drop (j + 1)
  have hw : w.length = 26 + j := by simp [w, wireCount, Nat.min_eq_left hj.le]
  have split : C.gates = C.gates.take j ++ g :: tail := by
    change C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1)
    rw [show g = C.gates[j] from hlookup.symm, List.cons_getElem_drop_succ, List.take_append_drop]
  have finalWires : C.wires (List.ofFn x) = (g :: tail).foldl appendGate w := by
    change C.gates.foldl appendGate _ = _
    conv_lhs => rw [split, List.foldl_append]
  change (C.wires (List.ofFn x)).getD (26 + j) false =
    ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false)
  rw [finalWires, earlierWire _ w a (by rwa [hw]), earlierWire _ w b (by rwa [hw])]
  rw [List.foldl_cons, earlierWire tail (appendGate w g) (26 + j) (by simp [appendGate, hw])]
  rw [← hw]
  simp [appendGate, g, GateOp.eval, List.getD_eq_getElem?_getD]
