import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1082_aux

open PEqualNP.CircuitLowerBounds

theorem gapp (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl

theorem step (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (W W' : List Bool)
    (hW : ∀ i, W.getD i false = true → W'.getD i false = true) :
    g.op.eval (g.inputs.map fun i => W.getD i false) = true →
    g.op.eval (g.inputs.map fun i => W'.getD i false) = true := by
  rcases hg with ho | ho
  · rw [ho]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map]
    rintro h _ ⟨b, hb, rfl⟩
    exact hW b (h _ ⟨b, hb, rfl⟩)
  · rw [ho]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map]
    rintro ⟨_, ⟨b, hb, rfl⟩, hv⟩
    exact ⟨_, ⟨b, hb, rfl⟩, hW b hv⟩

theorem fold (G : List Gate) (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, W.length = W'.length →
    (∀ i, W.getD i false = true → W'.getD i false = true) →
    ∀ i, (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD i false = true →
      (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W').getD i false = true := by
  induction G with
  | nil => intro W W' _ h; simpa using h
  | cons g G ih =>
    intro W W' hl hW
    simp only [List.foldl_cons]
    apply ih (fun e he => hG e (List.mem_cons_of_mem _ he))
    · simp [hl]
    · intro i hi
      rw [gapp] at hi ⊢
      rw [← hl]
      split_ifs at hi ⊢ with h1 h2
      · exact hW i hi
      · exact step g (hG g (by simp)) W W' hW hi

end PEqualNP.Outside.L_meta_1082_aux

open PEqualNP.Outside.L_meta_1082_aux in
theorem PEqualNP.Outside.L_meta_1082 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ x y : List Bool, x.length = n → y.length = n → (∀ i < n, x.getD i false = true → y.getD i false = true) → C.eval x = true → C.eval y = true := by
  intro n C hC x y hx hy hxy h
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires at *
  refine fold C.gates hC x y (by omega) ?_ _ h
  intro i hi
  by_cases hin : i < n
  · exact hxy i hin hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    cases hi
