import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_276_aux

private def step276 (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldLength276 (gs : List Gate) (w : List Bool) :
    (gs.foldl step276 w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step276]
    omega

private lemma foldKeepsWire276 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step276 w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step276]; omega)]
    simp [step276, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma twoInputGate276 (C : Circuit) (w : List Bool) (j a b : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hinputs : g.inputs = [a, b])
    (ha : a < w.length + j) (hb : b < w.length + j) :
    (C.wires w).getD (w.length + j) false =
      g.op.eval [(C.wires w).getD a false, (C.wires w).getD b false] := by
  obtain ⟨hj, heq⟩ := List.getElem?_eq_some_iff.mp hg
  have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    rw [← heq]
    simp [List.take_append_drop]
  let earlier := (C.gates.take j).foldl step276 w
  have hlen : earlier.length = w.length + j := by
    simp [earlier, foldLength276, Nat.min_eq_left hj.le]
  have hwires : C.wires w = (C.gates.drop (j + 1)).foldl step276 (step276 earlier g) := by
    change C.gates.foldl step276 w = _
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  have hbefore (i : ℕ) (hi : i < w.length + j) :
      (C.wires w).getD i false = earlier.getD i false := by
    rw [hwires, ← List.foldl_cons]
    exact foldKeepsWire276 _ _ _ (by simpa [hlen] using hi)
  rw [hbefore a ha, hbefore b hb, hwires, foldKeepsWire276 _ _ _
    (by simp [step276, hlen]), ← hlen]
  simp [step276, hinputs, List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_276_aux

theorem PEqualNP.Outside.L_meta_276 :
    ∀ (n j a b : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.inputs = [a, b] → a < n + j → b < n + j →
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) =
          (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∪
          (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) ∧
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) =
          (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∩
          (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) := by
  intro n j a b C g hg hinputs ha hb
  have hvalue (p : Fin n) := PEqualNP.Outside.L_meta_276_aux.twoInputGate276 C
    (List.ofFn (fun q : Fin n => decide (q = p))) j a b g hg hinputs
    (by simpa using ha) (by simpa using hb)
  simp only [List.length_ofFn] at hvalue
  constructor
  · intro hor
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hvalue p, hor]
    simp [GateOp.eval, Bool.or_eq_true]
  · intro hand
    ext p
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hvalue p, hand]
    simp [GateOp.eval, Bool.and_eq_true]
