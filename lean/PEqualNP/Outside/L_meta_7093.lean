import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7093

open PEqualNP.CircuitLowerBounds

theorem foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g t ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.size :=
  foldl_len C.gates x

theorem wires_snoc (C : Circuit) (g : Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires { gates := C.gates ++ [g], output := o } x)
      = C.wires x ++ [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

end PEqualNP.Outside.L_meta_7093

theorem PEqualNP.Outside.L_meta_7093 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.MetaComplexity.Monotone2 x2 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x2 → x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3.inputs.length ≤ (2 : ℕ) → (∀ x8 ∈ x3.inputs, x8 < x1 + x2.size) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x9 ∧ x9.size = x2.size + (1 : ℕ) ∧ ∀ (x10 : List Bool), x10.length = x1 → x9.eval x10 = x3.op.eval (List.map (fun (x12 : ℕ) => (x2.wires x10).getD x12 Bool.false) x3.inputs) := by
  intro n C g hM hR hop hlen hin
  refine ⟨{ gates := C.gates ++ [g], output := n + C.size }, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hM g' h
    · rw [List.mem_singleton] at h
      subst h
      refine ⟨?_, hlen⟩
      rcases hop with h | h
      · rw [h]; exact Or.inl rfl
      · rw [h]; exact Or.inr rfl
  · intro j hj i hi
    have hj' : j < C.gates.length + 1 := by simpa using hj
    by_cases hlt : j < C.gates.length
    · have e : PEqualNP.MetaComplexity.NestedCover.gateAt { gates := C.gates ++ [g], output := n + C.size } j
          = PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getElem?_append_left hlt]
      rw [e] at hi
      exact hR j hlt i hi
    · have hje : j = C.gates.length := by omega
      subst hje
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt { gates := C.gates ++ [g], output := n + C.size } C.gates.length
          = g := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [e] at hi
      exact hin i hi
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x hx
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_7093.wires_snoc]
    have hl := PEqualNP.Outside.L_meta_7093.wires_len C x
    rw [hx] at hl
    show (C.wires x ++ [g.op.eval (g.inputs.map fun i => (C.wires x).getD i false)]).getD (n + C.size) false = _
    rw [← hl]
    simp
