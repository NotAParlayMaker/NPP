import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2878_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len (gs : List Gate) : ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

end PEqualNP.Outside.L_meta_2878_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2878_aux in
theorem PEqualNP.Outside.L_meta_2878 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : PEqualNP.CircuitLowerBounds.GateOp), x4 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4 = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ (x6 x7 : ℕ), ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x2.size + (1 : ℕ) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x4.eval [(x2.wires (List.ofFn x9)).getD x6 Bool.false, (x2.wires (List.ofFn x9)).getD x7 Bool.false] := by
  intro n C hM op hop a b
  refine ⟨⟨C.gates ++ [Gate.mk op [a, b]], n + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hM g h
    · simp only [List.mem_singleton] at h
      subst h
      rcases hop with rfl | rfl <;> simp
  · simp [Circuit.size]
  · intro x
    have hl : (C.gates.foldl step (List.ofFn x)).length = n + C.gates.length := by
      rw [len]; simp
    have hw : C.wires (List.ofFn x) = C.gates.foldl step (List.ofFn x) := rfl
    have he : (Circuit.mk (C.gates ++ [Gate.mk op [a, b]]) (n + C.gates.length)).eval (List.ofFn x) =
        ((C.gates ++ [Gate.mk op [a, b]]).foldl step (List.ofFn x)).getD (n + C.gates.length) false := rfl
    rw [he, hw, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [step, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl]
