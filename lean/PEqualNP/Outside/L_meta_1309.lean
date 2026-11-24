import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1309

open PEqualNP.CircuitLowerBounds

theorem fold_length (gs : List Gate) (d : List ℕ) :
    (gs.foldl (fun d g => d ++ [g.lineDegree d]) d).length = d.length + gs.length := by
  induction gs generalizing d with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

theorem deg_length (gs : List Gate) (n : ℕ) (marked : Finset ℕ) :
    (Circuit.lineDegrees { gates := gs, output := 0 } n marked).length = n + gs.length := by
  unfold Circuit.lineDegrees
  rw [fold_length]
  simp

theorem step (gs : List Gate) (n : ℕ) (marked : Finset ℕ) (a b o : ℕ) :
    Circuit.lineDegrees { gates := gs ++ [Gate.mk GateOp.or [a, b]], output := o } n marked =
      Circuit.lineDegrees { gates := gs, output := 0 } n marked ++
        [max ((Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD a 0)
          ((Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD b 0)] := by
  unfold Circuit.lineDegrees
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp [Gate.lineDegree]

theorem last_getD (X : List ℕ) (m k : ℕ) (h : X.length = k) : (X ++ [m]).getD k 0 = m := by
  subst h
  simp

end PEqualNP.Outside.L_meta_1309

theorem PEqualNP.Outside.L_meta_1309 : ∀ (n : ℕ) (marked : Finset ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), (PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [a, b]], output := 0 } n marked = PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked ++ [max ((PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD a 0) ((PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD b 0)]) ∧ (PEqualNP.CircuitLowerBounds.Circuit.lineDeg { gates := gs ++ [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [a, b]], output := n + gs.length } n marked = max ((PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD a 0) ((PEqualNP.CircuitLowerBounds.Circuit.lineDegrees { gates := gs, output := 0 } n marked).getD b 0)) := by
  intro n marked gs a b
  refine ⟨PEqualNP.Outside.L_meta_1309.step gs n marked a b 0, ?_⟩
  unfold PEqualNP.CircuitLowerBounds.Circuit.lineDeg
  rw [PEqualNP.Outside.L_meta_1309.step gs n marked a b (n + gs.length)]
  exact PEqualNP.Outside.L_meta_1309.last_getD _ _ _
    (PEqualNP.Outside.L_meta_1309.deg_length gs n marked)
