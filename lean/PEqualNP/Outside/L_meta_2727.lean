import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2727

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma keepWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma absorb (gs : List Gate) (w : List Bool) (j u t : ℕ)
    (gate : gs[j]? = some ⟨.and, [u, t]⟩) (hu : u < w.length + j) (ht : t < w.length + j)
    (imp : (gs.foldl step w).getD u false = true → (gs.foldl step w).getD t false = true) :
    (gs.set j ⟨.or, [u]⟩).foldl step w = gs.foldl step w := by
  induction gs generalizing w j with
  | nil => simp at gate
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at gate
      subst g
      have lu : u < w.length := by simpa using hu
      have lt : t < w.length := by simpa using ht
      rw [keepWire _ w u lu, keepWire _ w t lt] at imp
      change gs.foldl step (step w ⟨.or, [u]⟩) = gs.foldl step (step w ⟨.and, [u, t]⟩)
      congr 1
      change w ++ [w.getD u false || false] = w ++ [w.getD u false && (w.getD t false && true)]
      cases hb : w.getD u false with
      | false => rfl
      | true => rw [imp hb]; rfl
    | succ j =>
      exact ih (step w g) j gate (by simp [step]; omega) (by simp [step]; omega) imp

end PEqualNP.Outside.L_meta_2727

theorem PEqualNP.Outside.L_meta_2727 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
  j < C.gates.length →
  C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u, t] } →
  u < n + j → t < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD u false = true →
      (C.wires (List.ofFn x)).getD t false = true) →
  ∀ x : Fin n → Bool,
    ({ gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] },
       output := C.output } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x) =
    C.wires (List.ofFn x) := by
  intro n C j u t _ gate hu ht imp x
  exact PEqualNP.Outside.L_meta_2727.absorb C.gates (List.ofFn x) j u t gate
    (by simpa using hu) (by simpa using ht) (imp x)
