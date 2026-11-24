import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2727

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp
    omega

theorem run_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

end PEqualNP.Outside.L_meta_2727

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2727 in
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
  intro n C j u t hj hg hu ht himp x
  obtain ⟨gates, out⟩ := C
  obtain ⟨hj', hgj⟩ := List.getElem?_eq_some_iff.mp hg
  obtain ⟨pre, post, hsplit, hpre⟩ : ∃ pre post : List Gate,
      gates = pre ++ (⟨GateOp.and, [u, t]⟩ : Gate) :: post ∧ pre.length = j := by
    refine ⟨gates.take j, gates.drop (j + 1), ?_, ?_⟩
    · rw [← hgj, ← List.drop_eq_getElem_cons hj', List.take_append_drop]
    · rw [List.length_take]
      exact Nat.min_eq_left (Nat.le_of_lt hj')
  subst hsplit
  subst hpre
  have hset : (pre ++ (⟨GateOp.and, [u, t]⟩ : Gate) :: post).set pre.length ⟨GateOp.or, [u]⟩
      = pre ++ (⟨GateOp.or, [u]⟩ : Gate) :: post := by
    simp
  have key : ∀ i, i < n + pre.length →
      (run (pre ++ (⟨GateOp.and, [u, t]⟩ : Gate) :: post) (List.ofFn x)).getD i false
        = (run pre (List.ofFn x)).getD i false := by
    intro i hi
    rw [run_append]
    apply run_getD
    rw [run_length]
    simpa using hi
  have himp' : (run (pre ++ (⟨GateOp.and, [u, t]⟩ : Gate) :: post) (List.ofFn x)).getD u false = true →
      (run (pre ++ (⟨GateOp.and, [u, t]⟩ : Gate) :: post) (List.ofFn x)).getD t false = true := himp x
  rw [key u hu, key t ht] at himp'
  change run (List.set _ _ _) (List.ofFn x) = run (pre ++ _ :: post) (List.ofFn x)
  rw [hset, run_append, run_append, run_cons, run_cons]
  have e : GateOp.or.eval (([u] : List ℕ).map fun i => (run pre (List.ofFn x)).getD i false)
      = GateOp.and.eval (([u, t] : List ℕ).map fun i => (run pre (List.ofFn x)).getD i false) := by
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false]
    cases hu' : (run pre (List.ofFn x)).getD u false
    · rfl
    · rw [himp' hu']
      rfl
  rw [e]
