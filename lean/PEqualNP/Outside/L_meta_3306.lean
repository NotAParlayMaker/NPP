import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3306_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

/-- The gate placed at a position: an AND gate whose first input does not lie in `x4` or whose
second input does not lie in `x3` has its inputs reversed, so that afterwards its first input
lies in `x4` and its second one in `x3`. Every other gate is kept. -/
def fixGate (x3 x4 : Finset ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
    if g.inputs.getD 0 0 ∈ x4 ∧ g.inputs.getD 1 0 ∈ x3 then g
    else ⟨GateOp.and, g.inputs.reverse⟩
  | _ => g

theorem fixGate_of_and (x3 x4 : Finset ℕ) (g : Gate) (h : g.op = GateOp.and) :
    fixGate x3 x4 g
      = if g.inputs.getD 0 0 ∈ x4 ∧ g.inputs.getD 1 0 ∈ x3 then g
        else ⟨GateOp.and, g.inputs.reverse⟩ := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => rfl
  | or => exact absurd h (by simp)
  | not => exact absurd h (by simp)
  | mod m => exact absurd h (by simp)
  | maj => exact absurd h (by simp)

theorem fixGate_of_ne_and (x3 x4 : Finset ℕ) (g : Gate) (h : g.op ≠ GateOp.and) :
    fixGate x3 x4 g = g := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => exact absurd rfl h
  | or => rfl
  | not => rfl
  | mod m => rfl
  | maj => rfl

theorem fixGate_op (x3 x4 : Finset ℕ) (g : Gate) : (fixGate x3 x4 g).op = g.op := by
  by_cases h : g.op = GateOp.and
  · rw [fixGate_of_and x3 x4 g h]
    split_ifs with hc
    · rfl
    · exact h.symm
  · rw [fixGate_of_ne_and x3 x4 g h]

theorem fixGate_eval (x3 x4 : Finset ℕ) (g : Gate) (v : ℕ → Bool) :
    (fixGate x3 x4 g).op.eval ((fixGate x3 x4 g).inputs.map v) = g.op.eval (g.inputs.map v) := by
  by_cases h : g.op = GateOp.and
  · rw [fixGate_of_and x3 x4 g h]
    split_ifs with hc
    · rfl
    · rw [h]
      simp [GateOp.eval, List.map_reverse, List.all_reverse]
  · rw [fixGate_of_ne_and x3 x4 g h]

theorem fixGate_default (x3 x4 : Finset ℕ) : fixGate x3 x4 ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩ :=
  fixGate_of_ne_and x3 x4 _ (by simp)

theorem fixGate_inputs_subset (x3 x4 : Finset ℕ) (g : Gate) {i : ℕ}
    (hi : i ∈ (fixGate x3 x4 g).inputs) : i ∈ g.inputs := by
  by_cases h : g.op = GateOp.and
  · rw [fixGate_of_and x3 x4 g h] at hi
    split_ifs at hi with hc
    · exact hi
    · simpa using hi
  · rwa [fixGate_of_ne_and x3 x4 g h] at hi

theorem fixGate_inputs_length (x3 x4 : Finset ℕ) (g : Gate) :
    (fixGate x3 x4 g).inputs.length = g.inputs.length := by
  by_cases h : g.op = GateOp.and
  · rw [fixGate_of_and x3 x4 g h]
    split_ifs with hc
    · rfl
    · simp
  · rw [fixGate_of_ne_and x3 x4 g h]

theorem getD_map_fix (x3 x4 : Finset ℕ) (l : List Gate) (j : ℕ) :
    (l.map (fixGate x3 x4)).getD j ⟨GateOp.or, []⟩
      = fixGate x3 x4 (l.getD j ⟨GateOp.or, []⟩) := by
  induction l generalizing j with
  | nil =>
    cases j with
    | zero => exact (fixGate_default x3 x4).symm
    | succ j => exact (fixGate_default x3 x4).symm
  | cons g t ih =>
    cases j with
    | zero => rfl
    | succ j => simpa using ih j

theorem gateAt_map (x3 x4 : Finset ℕ) (C : Circuit) (j : ℕ) :
    gateAt (⟨C.gates.map (fixGate x3 x4), C.output⟩ : Circuit) j = fixGate x3 x4 (gateAt C j) :=
  getD_map_fix x3 x4 C.gates j

theorem foldl_gates (f : Gate → Gate)
    (h : ∀ (g : Gate) (v : ℕ → Bool),
      (f g).op.eval ((f g).inputs.map v) = g.op.eval (g.inputs.map v)) :
    ∀ (gs : List Gate) (w : List Bool),
      (gs.map f).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
        = gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g t ih =>
    intro w
    simp only [List.map_cons, List.foldl_cons]
    have hstep : w ++ [(f g).op.eval ((f g).inputs.map fun i => w.getD i false)]
        = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
      rw [h g (fun i => w.getD i false)]
    rw [hstep]
    exact ih _

theorem wires_fix (x3 x4 : Finset ℕ) (C : Circuit) (x : List Bool) :
    (⟨C.gates.map (fixGate x3 x4), C.output⟩ : Circuit).wires x = C.wires x :=
  foldl_gates (fixGate x3 x4) (fun g v => fixGate_eval x3 x4 g v) C.gates x

theorem circuitFun_fix (x1 : ℕ) (x3 x4 : Finset ℕ) (C : Circuit) :
    PEqualNP.MetaComplexity.circuitFun x1
        (⟨C.gates.map (fixGate x3 x4), C.output⟩ : Circuit)
      = PEqualNP.MetaComplexity.circuitFun x1 C := by
  funext x
  show (⟨C.gates.map (fixGate x3 x4), C.output⟩ : Circuit).eval (List.ofFn x)
      = C.eval (List.ofFn x)
  unfold Circuit.eval
  rw [wires_fix]

end PEqualNP.Outside.L_meta_3306_aux

open PEqualNP.Outside.L_meta_3306_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_3306 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro x1 x2 x3 x4 hAO hAnd
  obtain ⟨hAndOr, hReads, hLen⟩ := hAO
  refine ⟨⟨x2.gates.map (fixGate x3 x4), x2.output⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [fixGate_op]
      exact hAndOr g' hg'
    · intro j hj i hi
      have hj' : j < x2.gates.length := by simpa using hj
      rw [gateAt_map] at hi
      exact hReads j hj' i (fixGate_inputs_subset x3 x4 _ hi)
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [fixGate_inputs_length]
      exact hLen g' hg'
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · exact circuitFun_fix x1 x3 x4 x2
  · intro j
    rw [gateAt_map, fixGate_op]
  · intro j hj
    rw [gateAt_map, fixGate_of_ne_and x3 x4 _ (by rw [hj]; simp)]
  · intro j hj hop
    have hj' : j < x2.gates.length := by simpa using hj
    rw [gateAt_map, fixGate_op] at hop
    obtain ⟨x9, x10, hin, hmem⟩ := hAnd j hj' hop
    have h0 : (gateAt x2 j).inputs.getD 0 0 = x9 := by rw [hin]; rfl
    have h1 : (gateAt x2 j).inputs.getD 1 0 = x10 := by rw [hin]; rfl
    by_cases hcase : x9 ∈ x4 ∧ x10 ∈ x3
    · have hc : (gateAt x2 j).inputs.getD 0 0 ∈ x4 ∧ (gateAt x2 j).inputs.getD 1 0 ∈ x3 := by
        rw [h0, h1]; exact hcase
      refine ⟨x9, x10, ?_, hcase.1, hcase.2⟩
      rw [gateAt_map, fixGate_of_and x3 x4 _ hop, if_pos hc, hin]
    · have hmem' : x9 ∈ x3 ∧ x10 ∈ x4 := by
        rcases hmem with h | h
        · exact h
        · exact absurd h hcase
      have hc : ¬((gateAt x2 j).inputs.getD 0 0 ∈ x4 ∧ (gateAt x2 j).inputs.getD 1 0 ∈ x3) := by
        rw [h0, h1]; exact hcase
      refine ⟨x10, x9, ?_, hmem'.2, hmem'.1⟩
      rw [gateAt_map, fixGate_of_and x3 x4 _ hop, if_neg hc, hin]
      rfl
