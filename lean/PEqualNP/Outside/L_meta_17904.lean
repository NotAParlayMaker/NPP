import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17904_aux

open PEqualNP.CircuitLowerBounds

theorem len_foldl (gs : List Gate) (x : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

theorem key (x3 : Circuit) (W0 : List Bool) (hW0 : W0.length = 11) (a b : ℕ) :
    (x3.wires W0 ++ [GateOp.or.eval ([a, b].map fun i => (x3.wires W0).getD i false)]).getD
      (11 + x3.gates.length) false = ((x3.wires W0).getD a false || (x3.wires W0).getD b false) := by
  have hl : (x3.wires W0).length = 11 + x3.gates.length := by
    rw [Circuit.wires, len_foldl, hW0]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hl, GateOp.eval]

theorem split (g1 g3 : Gate) (x3 : Circuit) (x : List Bool) (o : ℕ) :
    Circuit.wires { gates := [g1] ++ x3.gates ++ [g3], output := o } x
      = x3.wires (Circuit.wires { gates := [g1], output := 0 } x) ++
        [g3.op.eval (g3.inputs.map fun i =>
          (x3.wires (Circuit.wires { gates := [g1], output := 0 } x)).getD i false)] := by
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]

end PEqualNP.Outside.L_meta_17904_aux

theorem PEqualNP.Outside.L_meta_17904 : ∀ (x1 : Fin (11 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin (18 : ℕ)) (x5 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ x5 →       have x8 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (10 : ℕ) → Bool) (x9 : ℕ) => (x2.wires ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [↑x1] : PEqualNP.CircuitLowerBounds.Gate }], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x8))).getD x9 Bool.false;       ∀ (x9 : (Fin (10 : ℕ) → Bool) → Bool), (∀ (x10 : Fin (10 : ℕ) → Bool), x9 x10 = (x8 x10 ((10 : ℕ) + ↑x3) || x8 x10 ((10 : ℕ) + ↑x4))) → PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) x9 (x5 + (2 : ℕ)) := by
  intro x1 x2 x3 x4 x5 hF hs x8 x9 hx
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [↑x1] }] ++ x2.gates ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(10 : ℕ) + ↑x3, (10 : ℕ) + ↑x4] }], output := 11 + x2.gates.length }, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (rfl | hg) | rfl
    · simp
    · exact hF g hg
    · simp
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, List.length_singleton] at hs ⊢
    omega
  · intro x
    rw [hx x, PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.Outside.L_meta_17904_aux.split]
    exact PEqualNP.Outside.L_meta_17904_aux.key x2 _
      (by simp [PEqualNP.CircuitLowerBounds.Circuit.wires]) _ _
