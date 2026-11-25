import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9043_aux

open PEqualNP.CircuitLowerBounds

theorem pre (gs : List Gate) : ∀ w : List Bool,
    w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons]
    exact (List.prefix_append _ _).trans (ih _)

theorem key (gs : List Gate) (g : Gate) : ∀ (j : ℕ) (w : List Bool), gs[j]? = some g →
    ∃ w0 t : List Bool, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
      = w0 ++ [g.op.eval (g.inputs.map fun i => w0.getD i false)] ++ t ∧ w0.length = w.length + j := by
  induction gs with
  | nil => intro j w h; simp at h
  | cons g' gs ih =>
    intro j w h
    cases j with
    | zero =>
      simp at h
      subst h
      obtain ⟨t, ht⟩ := pre gs (w ++ [g'.op.eval (g'.inputs.map fun i => w.getD i false)])
      exact ⟨w, t, by simp only [List.foldl_cons]; rw [← ht], by simp⟩
    | succ k =>
      simp at h
      obtain ⟨w0, t, h1, h2⟩ := ih k (w ++ [g'.op.eval (g'.inputs.map fun i => w.getD i false)]) h
      refine ⟨w0, t, by simp only [List.foldl_cons]; exact h1, ?_⟩
      simp at h2
      omega

end PEqualNP.Outside.L_meta_9043_aux

open PEqualNP.Outside.L_meta_9043_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9043 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x1 ≤ x2.output → x2.output < x1 + x2.size → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x2.output - x1]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ (x7 : ℕ) (x8 : ℕ), x7 < x2.output ∧ x8 < x2.output ∧ ∀ (x9 : List Bool), x9.length = x1 → x2.eval x9 = ((x2.wires x9).getD x7 Bool.false || (x2.wires x9).getD x8 Bool.false) := by
  intro n C h1 h2 _ ⟨g, hg, hop⟩
  obtain ⟨_, hRB, h2l⟩ := h1
  have hgm : g ∈ C.gates := List.mem_of_getElem? hg
  have hj : C.output - n < C.gates.length := (List.getElem?_eq_some_iff.1 hg).1
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C (C.output - n) = g := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]
  have hrb := hRB _ hj
  rw [hga] at hrb
  match hgi : g.inputs, h2l g hgm with
  | [a, b], _ =>
    have ha : a < n + (C.output - n) := hrb a (by simp [hgi])
    have hb : b < n + (C.output - n) := hrb b (by simp [hgi])
    refine ⟨a, b, by omega, by omega, ?_⟩
    intro x hx
    obtain ⟨w0, t, hw, hl⟩ := key C.gates g (C.output - n) x hg
    have hl' : w0.length = C.output := by omega
    have hga' : a < w0.length := by omega
    have hgb : b < w0.length := by omega
    simp only [Circuit.eval, Circuit.wires]
    rw [hw, ← hl']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hga', List.getElem?_append_left hgb, hop, hgi, GateOp.eval]
