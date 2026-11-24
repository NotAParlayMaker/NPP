import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2677
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

def clipg (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (fun i => min i 24) }

theorem clip_get (X : List Bool) (hX : X.length ≤ 24) (i : ℕ) :
    X.getD (min i 24) false = X.getD i false := by
  by_cases h : i ≤ 24
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ hX,
      List.getD_eq_default _ _ (by omega)]

theorem clipw : ∀ (gs : List Gate) (X : List Bool), X.length + gs.length ≤ 24 →
    wf (gs.map clipg) X = wf gs X := by
  intro gs
  induction gs with
  | nil => intro X _; rfl
  | cons g gs ih =>
    intro X hX
    rw [List.length_cons] at hX
    have hv : (clipg g).op.eval ((clipg g).inputs.map fun i => X.getD i false)
        = g.op.eval (g.inputs.map fun i => X.getD i false) := by
      show g.op.eval ((g.inputs.map (fun i => min i 24)).map fun i => X.getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact clip_get X (by omega) i
    show wf (gs.map clipg) (X ++ [(clipg g).op.eval ((clipg g).inputs.map fun i => X.getD i false)])
      = wf gs (X ++ [g.op.eval (g.inputs.map fun i => X.getD i false)])
    rw [hv]
    apply ih
    rw [List.length_append]
    simp
    omega

end PEqualNP.Outside.L_meta_2677

open PEqualNP.Outside.L_meta_2677 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2677 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size = x1.size ∧ (PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x2) ∧ (PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.FanInTwo x2) ∧ x2.output ≤ (24 : ℕ) ∧ (∀ x3 ∈ x2.gates, ∀ x5 ∈ x3.inputs, x5 ≤ (24 : ℕ)) ∧ ∀ (x3 : List Bool), x3.length + x1.size ≤ (24 : ℕ) → x2.wires x3 = x1.wires x3 ∧ x2.eval x3 = x1.eval x3 ∧ (x1.wires x3).length = x3.length + x1.size := by
  intro C
  refine ⟨⟨C.gates.map clipg, min C.output 24⟩, ?_, ?_, ?_, Nat.min_le_right _ _, ?_, ?_⟩
  · show (C.gates.map clipg).length = C.gates.length
    rw [List.length_map]
  · intro h g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    refine ⟨(h g0 hg0).1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]; exact (h g0 hg0).2
  · intro h g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    refine ⟨(h g0 hg0).1, ?_⟩
    show (g0.inputs.map _).length ≤ 2
    rw [List.length_map]; exact (h g0 hg0).2
  · intro g hg i hi
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨i0, _, rfl⟩ := List.mem_map.1 hi
    exact Nat.min_le_right _ _
  · intro X hX
    have hsz : X.length + C.gates.length ≤ 24 := hX
    have hw : wf (C.gates.map clipg) X = wf C.gates X := clipw C.gates X hsz
    have hl : (wf C.gates X).length = X.length + C.gates.length := wf_len C.gates X
    refine ⟨hw, ?_, hl⟩
    show (wf (C.gates.map clipg) X).getD (min C.output 24) false = (wf C.gates X).getD C.output false
    rw [hw]
    exact clip_get _ (by omega) _
