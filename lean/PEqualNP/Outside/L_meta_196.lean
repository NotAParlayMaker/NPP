import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Lift196

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma set_or_wires (gs : List Gate) : ∀ (w : List Bool) (j a h : ℕ),
    gs[j]? = some ⟨GateOp.or, [a, h]⟩ → h < w.length + j →
    ((wiresFrom (gs.set j ⟨GateOp.or, [a]⟩) w).getD h false =
      (wiresFrom gs w).getD h false) ∧
    ((wiresFrom gs w).getD h false = false →
      wiresFrom (gs.set j ⟨GateOp.or, [a]⟩) w = wiresFrom gs w) := by
  induction gs with
  | nil => intro w j a h hg _; simp at hg
  | cons g gs ih =>
    intro w j a h hg hh
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst g
      have hh' : h < w.length := by omega
      constructor
      · rw [getD_wiresFrom _ _ _ hh', getD_wiresFrom _ _ _ hh']
      · intro hzero
        rw [getD_wiresFrom _ _ _ hh'] at hzero
        simp only [List.set_cons_zero, wiresFrom_cons]
        congr 1
        simp only [List.getD] at hzero
        simp [GateOp.eval, hzero]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hg
      have hi := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) j a h hg
        (by simp only [List.length_append, List.length_singleton]; omega)
      simpa only [List.set_cons_succ, wiresFrom_cons] using hi

lemma final_or (w : List Bool) (a b : ℕ) :
    (wiresFrom [⟨GateOp.or, [a, b]⟩] w).getD w.length false =
      (w.getD a false || w.getD b false) := by
  simp [wiresFrom, GateOp.eval]

end PEqualNP.Outside.Lift196

open PEqualNP.Outside.Lift196 in
theorem PEqualNP.Outside.L_meta_196 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } x ≠ f x → PEqualNP.MetaComplexity.circuitFun n C x ≠ f x ∨ ((C.wires (List.ofFn x)).getD h false = true ∧ f x = false) := by
  intro n j a h C f hg hh x herr
  have hp := set_or_wires C.gates (List.ofFn x) j a h hg (by simpa using hh)
  let gs := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩
  let w := wiresFrom gs (List.ofFn x)
  have hl : n + C.size = w.length := by
    simp [w, length_wiresFrom, gs, PEqualNP.CircuitLowerBounds.Circuit.size]
  have hout : PEqualNP.MetaComplexity.circuitFun n
      { gates := gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩],
        output := n + C.size } x = (w.getD C.output false || w.getD h false) := by
    change (wiresFrom (gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩])
      (List.ofFn x)).getD (n + C.size) false = _
    rw [wiresFrom_append, hl]
    exact final_or w C.output h
  by_cases hc : PEqualNP.MetaComplexity.circuitFun n C x ≠ f x
  · exact Or.inl hc
  · have hc' : PEqualNP.MetaComplexity.circuitFun n C x = f x := by simpa using hc
    have hnf : (C.wires (List.ofFn x)).getD h false ≠ false := by
      intro hz
      apply herr
      rw [hout]
      have he := hp.2 hz
      change w = wiresFrom C.gates (List.ofFn x) at he
      rw [he]
      change ((C.wires (List.ofFn x)).getD C.output false ||
        (C.wires (List.ofFn x)).getD h false) = f x
      rw [hz, Bool.or_false]
      exact hc'
    have ht : (C.wires (List.ofFn x)).getD h false = true := by
      cases he : (C.wires (List.ofFn x)).getD h false <;> simp_all
    refine Or.inr ⟨ht, ?_⟩
    have hnew : PEqualNP.MetaComplexity.circuitFun n
        { gates := gs ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩],
          output := n + C.size } x = true := by
      rw [hout, hp.1]
      change (w.getD C.output false || (C.wires (List.ofFn x)).getD h false) = true
      rw [ht, Bool.or_true]
    apply Bool.eq_false_of_not_eq_true
    intro hfx
    exact herr (hnew.trans hfx.symm)
