import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside
namespace Wire196
open CircuitLowerBounds
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]; omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi


theorem removeInput (gs : List Gate) (w : List Bool) (j a h : ℕ)
    (gate : gs[j]? = some ⟨.or, [a,h]⟩) (prior : h < w.length + j) :
    let old := gs.foldl step w
    let new := (gs.set j ⟨.or,[a]⟩).foldl step w
    new.getD h false = old.getD h false ∧ (old.getD h false = false → new = old) := by
  induction gs generalizing j w with
  | nil => simp at gate
  | cons g gs ih =>
    cases j with
    | succ j =>
      apply ih (step w g) j (by simpa using gate)
      simp [step]
      omega
    | zero =>
      simp at gate
      subst g
      simp only [Nat.add_zero] at prior
      let w₁ := step w ⟨.or, [a,h]⟩
      let w₂ := step w ⟨.or, [a]⟩
      have get (g : Gate) : (gs.foldl step (step w g)).getD h false = w.getD h false := by
        rw [run_keep _ _ _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ prior
      change (gs.foldl step w₂).getD h false = (gs.foldl step w₁).getD h false ∧
        ((gs.foldl step w₁).getD h false = false → gs.foldl step w₂ = gs.foldl step w₁)
      dsimp only [w₂,w₁]
      rw [get, get]
      refine ⟨rfl, fun hh => ?_⟩
      change w[h]?.getD false = false at hh
      simp [step, GateOp.eval, hh]

end Wire196
open CircuitLowerBounds Wire196
theorem L_meta_196 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f gate prior x err
  let w := List.ofFn x
  let old := C.gates.foldl step w
  let new := (C.gates.set j ⟨.or,[a]⟩).foldl step w
  have facts := removeInput C.gates w j a h gate (by simpa [w] using prior)
  change new.getD h false = old.getD h false ∧ (old.getD h false = false → new = old) at facts
  have len : new.length = n + C.size := by simp [new, run_length, w, Circuit.size]
  change ((C.gates.set j ⟨.or,[a]⟩ ++ [⟨.or,[C.output,h]⟩] : List Gate).foldl step w).getD
    (n+C.size) false ≠ f x at err
  rw [List.foldl_append] at err
  change (step new ⟨.or,[C.output,h]⟩).getD (n+C.size) false ≠ f x at err
  rw [← len] at err
  simp [step, GateOp.eval] at err
  change old.getD C.output false ≠ f x ∨ (old.getD h false = true ∧ f x = false)
  cases hv : old.getD h false with
  | false =>
    left
    rw [facts.2 hv] at err
    change old[h]?.getD false = false at hv
    simpa [hv] using err
  | true =>
    right
    refine ⟨rfl, ?_⟩
    cases hf : f x <;> simp_all

end PEqualNP.Outside
