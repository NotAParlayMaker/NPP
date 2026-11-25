import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7931_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

theorem wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires; exact foldl_len _ _

theorem wires_snoc (gs : List Gate) (g : Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ x =
      Circuit.wires ⟨gs, o'⟩ x ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o'⟩ x).getD i false)] := by
  unfold Circuit.wires; simp [List.foldl_append]

end PEqualNP.Outside.L_meta_7931_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_7931_aux in
theorem PEqualNP.Outside.L_meta_7931 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x2.gates, x6.inputs.Nodup) →       x3 ≠ x4 →         x3 < x1 + x2.size →           x4 < x1 + x2.size →             have x10 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate }], output := x1 + x2.size : PEqualNP.CircuitLowerBounds.Circuit };             PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : List Bool), x11.length = x1 → x10.eval x11 = ((x2.wires x11).getD x3 Bool.false && (x2.wires x11).getD x4 Bool.false) ∧ (x10.wires x11).getD x3 Bool.false = (x2.wires x11).getD x3 Bool.false ∧ (x10.wires x11).getD x4 Bool.false = (x2.wires x11).getD x4 Bool.false := by
  intro x1 x2 x3 x4 hA hN h34 h3 h4
  intro x10
  obtain ⟨hAO, hRB, hL⟩ := hA
  have hw : ∀ x11 : List Bool, x10.wires x11 = x2.wires x11 ++
      [GateOp.and.eval ([x3, x4].map fun i => (x2.wires x11).getD i false)] := by
    intro x11
    obtain ⟨gs, o⟩ := x2
    exact wires_snoc gs _ _ o x11
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [x10, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact Or.inl rfl
  · intro j hj i hi
    simp only [x10, List.length_append, List.length_singleton] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    simp only [x10] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hi
      exact hRB j hj i (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt; exact hi)
    · subst hj
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp [Circuit.size] at hi h3 h4
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    simp only [x10, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hL g hg
    · rfl
  · intro g hg
    simp only [x10, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hN g hg
    · simpa using h34
  · intro x11 hx
    have hlen := wires_len x2 x11
    have hs : x2.size = x2.gates.length := rfl
    refine ⟨?_, ?_, ?_⟩
    · unfold Circuit.eval
      rw [hw]
      have : x10.output = (x2.wires x11).length := by simp [x10]; omega
      rw [this, List.getD_append_right _ _ _ _ (le_refl _)]
      simp [GateOp.eval]
    · rw [hw, List.getD_append _ _ _ _ (by omega)]
    · rw [hw, List.getD_append _ _ _ _ (by omega)]
