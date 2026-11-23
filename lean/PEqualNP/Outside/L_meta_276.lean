import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta276

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_prefix (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (step w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t,
      by rw [List.foldl_cons, ht]; simp [step]⟩

theorem foldl_length (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp [List.foldl_cons, ih, step]
    omega

theorem key (C : Circuit) (x : List Bool) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) :
    ∃ W : List Bool, W.length = x.length + j ∧
      (∀ i, i < x.length + j → (C.wires x).getD i false = W.getD i false) ∧
      (C.wires x).getD (x.length + j) false
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj, hgj]
  have hw : C.wires x = C.gates.foldl step x := rfl
  set W := (C.gates.take j).foldl step x with hW
  have hWl : W.length = x.length + j := by
    rw [hW, foldl_length, List.length_take]
    omega
  obtain ⟨t, ht⟩ := foldl_prefix (C.gates.drop (j + 1)) (step W g)
  have hfin : C.wires x
      = W ++ ([g.op.eval (g.inputs.map fun i => W.getD i false)] ++ t) := by
    rw [hw, hsplit, List.foldl_append, List.foldl_cons, ← hW, ht, step, List.append_assoc]
  refine ⟨W, hWl, ?_, ?_⟩
  · intro i hi
    rw [hfin, List.getD_append _ _ _ _ (by omega)]
  · rw [hfin, ← hWl, List.getD_append_right _ _ _ _ (le_refl _)]
    simp

end PEqualNP.Outside.Meta276

theorem PEqualNP.Outside.L_meta_276 : ∀ (n j a b : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.inputs = [a, b] → a < n + j → b < n + j → (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) = (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∪ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) = (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∩ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) := by
  intro n j a b C g hg hin ha hb
  constructor
  · intro hop
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    obtain ⟨W, _, hpre, hval⟩ :=
      PEqualNP.Outside.Meta276.key C (List.ofFn (fun q : Fin n => decide (q = p))) j g hg
    simp only [List.length_ofFn] at hpre hval
    rw [hval, hpre a ha, hpre b hb, hin, hop]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · intro hop
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    obtain ⟨W, _, hpre, hval⟩ :=
      PEqualNP.Outside.Meta276.key C (List.ofFn (fun q : Fin n => decide (q = p))) j g hg
    simp only [List.length_ofFn] at hpre hval
    rw [hval, hpre a ha, hpre b hb, hin, hop]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
