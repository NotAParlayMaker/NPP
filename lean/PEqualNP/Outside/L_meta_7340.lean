import Mathlib
import PEqualNP.Defs

-- Clamp every wire index (gate inputs and the output) at N = x1 + x2. A clamped index that
-- changed was at least N, so it named a wire that did not exist yet and read false; the
-- index N does not exist yet either, so every gate value and the output are unchanged.

namespace PEqualNP.Outside.L_meta_7340

open PEqualNP.CircuitLowerBounds

def cg (N : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun i => min i N)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_min (N : ℕ) (w : List Bool) (hw : w.length ≤ N) (i : ℕ) :
    w.getD (min i N) false = w.getD i false := by
  rcases le_total i N with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.getD_eq_default _ _ hw, List.getD_eq_default _ _ (hw.trans h)]

theorem foldl_cg (N : ℕ) : ∀ (gs : List Gate) (w : List Bool), w.length + gs.length ≤ N →
    gs.foldl step w = (gs.map (cg N)).foldl step w := by
  intro gs
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hw
    simp only [List.foldl_cons, List.map_cons, List.length_cons] at hw ⊢
    have hs : step w g = step w (cg N g) := by
      unfold step cg
      simp only [List.map_map, Function.comp_def]
      congr 3
      apply List.map_congr_left
      intro i _
      exact (getD_min N w (by omega) i).symm
    rw [hs]
    apply ih
    unfold step
    simp only [List.length_append, List.length_singleton]
    omega

theorem length_foldl : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl step w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    unfold step
    simp only [List.length_append, List.length_singleton]
    omega

end PEqualNP.Outside.L_meta_7340

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_7340 in
theorem PEqualNP.Outside.L_meta_7340 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size ≤ x2 ∧ x6.output ≤ x1 + x2 ∧ (∀ x7 ∈ x6.gates, ∀ x9 ∈ x7.inputs, x9 ≤ x1 + x2) ∧ ∀ (x7 : List Bool), x7.length = x1 → x6.eval x7 = x3.eval x7 := by
  intro x1 x2 x3 hf hs
  refine ⟨⟨x3.gates.map (cg (x1 + x2)), min x3.output (x1 + x2)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2⟩ := hf g0 hg0
    exact ⟨h1, by simpa [cg] using h2⟩
  · simpa [Circuit.size] using hs
  · exact min_le_right _ _
  · intro g hg i hi
    obtain ⟨g0, _, rfl⟩ := List.mem_map.1 hg
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hi
    exact min_le_right _ _
  · intro x7 hx7
    have hsz : x3.gates.length ≤ x2 := hs
    have hw : Circuit.wires x3 x7 = x3.gates.foldl step x7 := rfl
    have hw2 : Circuit.wires ⟨x3.gates.map (cg (x1 + x2)), min x3.output (x1 + x2)⟩ x7 =
        (x3.gates.map (cg (x1 + x2))).foldl step x7 := rfl
    unfold Circuit.eval
    rw [hw, hw2, ← foldl_cg (x1 + x2) x3.gates x7 (by omega)]
    apply getD_min
    rw [length_foldl]
    omega
