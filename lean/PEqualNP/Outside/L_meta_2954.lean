import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2954 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin (9 : ℕ) → Bool) (x4 : ℕ), ({ gates := x1.gates ++ List.replicate x2 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x1.output : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x3)).getD x4 Bool.false = (x1.wires (List.ofFn x3)).getD x4 Bool.false := by
  intro C k x i
  let step (W : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    W ++ [g.op.eval (g.inputs.map fun j => W.getD j false)]
  let dummy : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, []⟩
  have stable (W : List Bool) : (W ++ [false]).getD i false = W.getD i false := by
    by_cases h : i < W.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default _ _ (by omega : W.length ≤ i)]
      cases i - W.length <;> rfl
  have go (n : ℕ) (W : List Bool) : ((List.replicate n dummy).foldl step W).getD i false = W.getD i false := by
    induction n generalizing W with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons, ih]
      exact stable W
  change ((C.gates ++ List.replicate k dummy).foldl step (List.ofFn x)).getD i false = _
  rw [List.foldl_append,go]
  rfl
