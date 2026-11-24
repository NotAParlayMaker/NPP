import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2677

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def clipGate (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fun i => min i 24)⟩

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma clippedRead (w : List Bool) (hw : w.length ≤ 24) (i : ℕ) :
    w.getD (min i 24) false = w.getD i false := by
  by_cases hi : i ≤ 24
  · rw [min_eq_left hi]
  · have hLarge : 24 ≤ i := by omega
    rw [min_eq_right hLarge, List.getD_eq_default _ _ hw,
      List.getD_eq_default _ _ (hw.trans hLarge)]

lemma clippedRun (gs : List Gate) (w : List Bool) (h : w.length + gs.length ≤ 24) :
    (gs.map clipGate).foldl gateStep w = gs.foldl gateStep w ∧
      (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    have hLength : w.length + (gs.length + 1) ≤ 24 := h
    have hRead : w.length ≤ 24 := by omega
    have hStep : gateStep w (clipGate g) = gateStep w g := by
      simp only [gateStep, clipGate, List.map_map, Function.comp_def, clippedRead w hRead]
    have hNext : (gateStep w g).length = w.length + 1 := by simp [gateStep]
    have hTail : (gateStep w g).length + gs.length ≤ 24 := by omega
    obtain ⟨same, len⟩ := ih (gateStep w g) hTail
    simp only [List.map_cons, List.foldl_cons, List.length_cons]
    rw [hStep]
    exact ⟨same, by rw [len, hNext]; omega⟩

lemma clippedGateKinds (C : Circuit) (ops : Set GateOp)
    (h : ∀ g ∈ C.gates, g.op ∈ ops ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ C.gates.map clipGate, g.op ∈ ops ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨original, hOriginal, rfl⟩ := List.mem_map.mp hg
  simpa [clipGate] using h original hOriginal

end PEqualNP.Outside.L_meta_2677

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2677

theorem PEqualNP.Outside.L_meta_2677 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      x2.size = x1.size ∧ (PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x2) ∧
      (PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.FanInTwo x2) ∧ x2.output ≤ (24 : ℕ) ∧
      (∀ x3 ∈ x2.gates, ∀ x5 ∈ x3.inputs, x5 ≤ (24 : ℕ)) ∧
      ∀ (x3 : List Bool), x3.length + x1.size ≤ (24 : ℕ) →
        x2.wires x3 = x1.wires x3 ∧ x2.eval x3 = x1.eval x3 ∧
          (x1.wires x3).length = x3.length + x1.size := by
  intro C
  let D : Circuit := ⟨C.gates.map clipGate, min C.output 24⟩
  refine ⟨D, by simp [D, Circuit.size], clippedGateKinds C _, clippedGateKinds C _,
    min_le_right _ _, ?_, ?_⟩
  · intro g hg i hi
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp hg
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact min_le_right j 24
  · intro x hx
    obtain ⟨same, length⟩ := clippedRun C.gates x hx
    have wires : D.wires x = C.wires x := same
    have finalLength : (C.wires x).length = x.length + C.size := length
    refine ⟨wires, ?_, finalLength⟩
    change (D.wires x).getD (min C.output 24) false = (C.wires x).getD C.output false
    rw [wires]
    exact clippedRead _ (by rwa [finalLength]) C.output
