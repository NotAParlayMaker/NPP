import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_202_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- One evaluation step: the gate adds one wire. -/
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem foldl_length (gs : List Gate) : ∀ W : List Bool,
    (gs.foldl stp W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [stp]
    omega

/-- Later gates do not change the wires that are already there. -/
theorem foldl_prefix (gs : List Gate) : ∀ (W : List Bool) (i : ℕ), i < W.length →
    (gs.foldl stp W).getD i false = W.getD i false := by
  induction gs with
  | nil => intro W i _; rfl
  | cons g gs ih =>
    intro W i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp [stp]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem split_at {α : Type} : ∀ (l : List α) (j : ℕ) (g : α), l[j]? = some g →
    ∃ pre post : List α, l = pre ++ g :: post ∧ pre.length = j ∧
      ∀ g' : α, l.set j g' = pre ++ g' :: post := by
  intro l
  induction l with
  | nil => intro j g h; simp at h
  | cons x xs ih =>
    intro j g h
    cases j with
    | zero =>
      simp at h
      exact ⟨[], xs, by simp [h], rfl, fun g' => by simp⟩
    | succ j =>
      simp at h
      obtain ⟨pre, post, h1, h2, h3⟩ := ih j g h
      exact ⟨x :: pre, post, by simp [h1], by simp [h2], fun g' => by simp [h3]⟩

end PEqualNP.Outside.L_meta_202_aux

open PEqualNP.Outside.L_meta_202_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_202 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.FanInTwo { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } ∧ PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } = PEqualNP.MetaComplexity.circuitFun n C := by
  intro n j a h C hF hj hh himp
  constructor
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_or_eq_of_mem_set hg with hg | rfl
      · exact hF g hg
      · simp
    · rw [List.mem_singleton] at hg
      subst hg
      simp
  · obtain ⟨pre, post, h1, h2, h3⟩ := split_at C.gates j _ hj
    funext x
    have hC : circuitFun n C x
        = (post.foldl stp (stp (pre.foldl stp (List.ofFn x)) ⟨GateOp.or, [a, h]⟩)).getD
            C.output false := by
      simp only [circuitFun, Circuit.eval, wires_eq, h1, List.foldl_append, List.foldl_cons]
    have hlen : (pre.foldl stp (List.ofFn x)).length = n + j := by
      rw [foldl_length, h2]
      simp
    have hwh : (C.wires (List.ofFn x)).getD h false
        = (pre.foldl stp (List.ofFn x)).getD h false := by
      rw [wires_eq, h1, List.foldl_append, List.foldl_cons]
      rw [foldl_prefix post _ h (by simp [stp, hlen]; omega)]
      exact List.getD_append _ _ _ _ (by omega)
    have himp' := himp x
    rw [hwh] at himp'
    have hsz : n + C.size
        = (post.foldl stp (stp (pre.foldl stp (List.ofFn x)) ⟨GateOp.or, [a]⟩)).length := by
      rw [foldl_length]
      simp only [stp, List.length_append, List.length_singleton, hlen]
      have : C.size = pre.length + (post.length + 1) := by
        show C.gates.length = _
        rw [h1]
        simp
      omega
    have hwh' : (post.foldl stp (stp (pre.foldl stp (List.ofFn x)) ⟨GateOp.or, [a]⟩)).getD h false
        = (pre.foldl stp (List.ofFn x)).getD h false := by
      rw [foldl_prefix post _ h (by simp [stp, hlen]; omega)]
      exact List.getD_append _ _ _ _ (by omega)
    have hC' : circuitFun n { gates := C.gates.set j ⟨GateOp.or, [a]⟩
          ++ [⟨GateOp.or, [C.output, h]⟩], output := n + C.size } x
        = ((post.foldl stp (stp (pre.foldl stp (List.ofFn x)) ⟨GateOp.or, [a]⟩)).getD
            C.output false
          || (pre.foldl stp (List.ofFn x)).getD h false) := by
      simp only [circuitFun, Circuit.eval, wires_eq, h3, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rw [hsz]
      generalize (post.foldl stp (stp (pre.foldl stp (List.ofFn x)) ⟨GateOp.or, [a]⟩)) = W
        at hwh' ⊢
      simp [stp, GateOp.eval, List.getD_eq_getElem?_getD] at hwh' ⊢
      rw [hwh']
    rw [hC', hC]
    cases hv : (pre.foldl stp (List.ofFn x)).getD h false with
    | true =>
      have := himp' hv
      rw [hC] at this
      rw [this]
      simp
    | false =>
      have e : stp (pre.foldl stp (List.ofFn x)) ⟨GateOp.or, [a, h]⟩
          = stp (pre.foldl stp (List.ofFn x)) ⟨GateOp.or, [a]⟩ := by
        have hv' := hv
        rw [List.getD_eq_getElem?_getD] at hv'
        simp [stp, GateOp.eval, hv']
      rw [e]
      simp
