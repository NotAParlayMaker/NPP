import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3655

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def circuit : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 38] }], output := 46 }

abbrev incident (p l : Fin 7) : Prop := p.val = l.val ∨ p.val = (l.val + 1) % 7 ∨ p.val = (l.val + 3) % 7

abbrev graph : SimpleGraph (Fin 14) := SimpleGraph.fromRel (fun u v =>
  ∃ p l : Fin 7, incident p l ∧ u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 l)

abbrev edgeSpec (z : Fin 14 → Bool) : Prop :=
  ∃ p l : Fin 7, incident p l ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_append (a b : List Gate) (x : List Bool) :
    run (a ++ b) x = run b (run a x) := by
  simp only [run, List.foldl_append]

theorem run_prefix (gs : List Gate) (x : List Bool) :
    ∃ tail, run gs x = x ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => x.getD i false)
    obtain ⟨tail, eq, length⟩ := ih (x ++ [b])
    refine ⟨b :: tail, ?_, by simp [length]⟩
    change run gs (x ++ [b]) = x ++ (b :: tail)
    rw [eq]
    simp

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  obtain ⟨tail, eq, length⟩ := run_prefix gs x
  simp [eq, length]

theorem run_keeps (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  obtain ⟨tail, eq, _⟩ := run_prefix gs x
  rw [eq, List.getD_append _ _ _ _ hi]

theorem gate_value (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (readsBack : ∀ i ∈ C.gates[j].inputs, i < x.length + j) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => (C.wires x).getD i false) := by
  let past := run (C.gates.take j) x
  let g := C.gates[j]
  let b := g.op.eval (g.inputs.map fun i => past.getD i false)
  have pastLen : past.length = x.length + j := by
    simp [past, run_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have whole : C.wires x = run (C.gates.drop (j + 1)) (past ++ [b]) := by
    change run C.gates x = _
    conv_lhs => rw [← List.take_append_drop (j + 1) C.gates,
       List.take_succ_eq_append_getElem hj, run_append, run_append]
    rfl
  have atJ : (C.wires x).getD (x.length + j) false = b := by
    rw [← pastLen, whole, run_keeps]
    · simp
    · simp
  rw [atJ]
  change g.op.eval (g.inputs.map fun i => past.getD i false) = _
  congr 1
  apply List.map_congr_left
  intro i hi
  have early : i < past.length := by
    rw [pastLen]
    exact readsBack i hi
  have extended : i < (past ++ [b]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rw [whole, run_keeps (C.gates.drop (j + 1)) (past ++ [b]) i extended,
    List.getD_append _ _ _ _ early]

def value (z : Fin 14 → Bool) (i : ℕ) : Bool :=
  (circuit.wires (List.ofFn z)).getD i false

theorem raw_value (z : Fin 14 → Bool) (i : Fin 14) : value z i = z i := by
  change (run circuit.gates (List.ofFn z)).getD i.val false = _
  rw [run_keeps _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem wire14 (z : Fin 14 → Bool) : value z 14 = (value z 7 || value z 8) := by
  have h := gate_value circuit (List.ofFn z) 0 (by decide) (by
    intro i hi
    change i ∈ [7, 8] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 14 = GateOp.or.eval [value z 7, value z 8] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire15 (z : Fin 14 → Bool) : value z 15 = (value z 14 || value z 12) := by
  have h := gate_value circuit (List.ofFn z) 1 (by decide) (by
    intro i hi
    change i ∈ [14, 12] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 15 = GateOp.or.eval [value z 14, value z 12] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire16 (z : Fin 14 → Bool) : value z 16 = (value z 1 && value z 15) := by
  have h := gate_value circuit (List.ofFn z) 2 (by decide) (by
    intro i hi
    change i ∈ [1, 15] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 16 = GateOp.and.eval [value z 1, value z 15] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire17 (z : Fin 14 → Bool) : value z 17 = (value z 8 || value z 9) := by
  have h := gate_value circuit (List.ofFn z) 3 (by decide) (by
    intro i hi
    change i ∈ [8, 9] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 17 = GateOp.or.eval [value z 8, value z 9] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire18 (z : Fin 14 → Bool) : value z 18 = (value z 17 || value z 13) := by
  have h := gate_value circuit (List.ofFn z) 4 (by decide) (by
    intro i hi
    change i ∈ [17, 13] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 18 = GateOp.or.eval [value z 17, value z 13] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire19 (z : Fin 14 → Bool) : value z 19 = (value z 2 && value z 18) := by
  have h := gate_value circuit (List.ofFn z) 5 (by decide) (by
    intro i hi
    change i ∈ [2, 18] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 19 = GateOp.and.eval [value z 2, value z 18] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire20 (z : Fin 14 → Bool) : value z 20 = (value z 7 || value z 9) := by
  have h := gate_value circuit (List.ofFn z) 6 (by decide) (by
    intro i hi
    change i ∈ [7, 9] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 20 = GateOp.or.eval [value z 7, value z 9] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire21 (z : Fin 14 → Bool) : value z 21 = (value z 20 || value z 10) := by
  have h := gate_value circuit (List.ofFn z) 7 (by decide) (by
    intro i hi
    change i ∈ [20, 10] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 21 = GateOp.or.eval [value z 20, value z 10] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire22 (z : Fin 14 → Bool) : value z 22 = (value z 3 && value z 21) := by
  have h := gate_value circuit (List.ofFn z) 8 (by decide) (by
    intro i hi
    change i ∈ [3, 21] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 22 = GateOp.and.eval [value z 3, value z 21] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire23 (z : Fin 14 → Bool) : value z 23 = (value z 8 || value z 10) := by
  have h := gate_value circuit (List.ofFn z) 9 (by decide) (by
    intro i hi
    change i ∈ [8, 10] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 23 = GateOp.or.eval [value z 8, value z 10] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire24 (z : Fin 14 → Bool) : value z 24 = (value z 23 || value z 11) := by
  have h := gate_value circuit (List.ofFn z) 10 (by decide) (by
    intro i hi
    change i ∈ [23, 11] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 24 = GateOp.or.eval [value z 23, value z 11] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire25 (z : Fin 14 → Bool) : value z 25 = (value z 4 && value z 24) := by
  have h := gate_value circuit (List.ofFn z) 11 (by decide) (by
    intro i hi
    change i ∈ [4, 24] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 25 = GateOp.and.eval [value z 4, value z 24] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire26 (z : Fin 14 → Bool) : value z 26 = (value z 9 || value z 11) := by
  have h := gate_value circuit (List.ofFn z) 12 (by decide) (by
    intro i hi
    change i ∈ [9, 11] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 26 = GateOp.or.eval [value z 9, value z 11] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire27 (z : Fin 14 → Bool) : value z 27 = (value z 26 || value z 12) := by
  have h := gate_value circuit (List.ofFn z) 13 (by decide) (by
    intro i hi
    change i ∈ [26, 12] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 27 = GateOp.or.eval [value z 26, value z 12] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire28 (z : Fin 14 → Bool) : value z 28 = (value z 5 && value z 27) := by
  have h := gate_value circuit (List.ofFn z) 14 (by decide) (by
    intro i hi
    change i ∈ [5, 27] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 28 = GateOp.and.eval [value z 5, value z 27] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire29 (z : Fin 14 → Bool) : value z 29 = (value z 10 || value z 12) := by
  have h := gate_value circuit (List.ofFn z) 15 (by decide) (by
    intro i hi
    change i ∈ [10, 12] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 29 = GateOp.or.eval [value z 10, value z 12] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire30 (z : Fin 14 → Bool) : value z 30 = (value z 29 || value z 13) := by
  have h := gate_value circuit (List.ofFn z) 16 (by decide) (by
    intro i hi
    change i ∈ [29, 13] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 30 = GateOp.or.eval [value z 29, value z 13] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire31 (z : Fin 14 → Bool) : value z 31 = (value z 6 && value z 30) := by
  have h := gate_value circuit (List.ofFn z) 17 (by decide) (by
    intro i hi
    change i ∈ [6, 30] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 31 = GateOp.and.eval [value z 6, value z 30] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire32 (z : Fin 14 → Bool) : value z 32 = (value z 0 && value z 7) := by
  have h := gate_value circuit (List.ofFn z) 18 (by decide) (by
    intro i hi
    change i ∈ [0, 7] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 32 = GateOp.and.eval [value z 0, value z 7] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire33 (z : Fin 14 → Bool) : value z 33 = (value z 0 && value z 13) := by
  have h := gate_value circuit (List.ofFn z) 19 (by decide) (by
    intro i hi
    change i ∈ [0, 13] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 33 = GateOp.and.eval [value z 0, value z 13] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire34 (z : Fin 14 → Bool) : value z 34 = (value z 7 || value z 11) := by
  have h := gate_value circuit (List.ofFn z) 20 (by decide) (by
    intro i hi
    change i ∈ [7, 11] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 34 = GateOp.or.eval [value z 7, value z 11] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire35 (z : Fin 14 → Bool) : value z 35 = (value z 0 && value z 34) := by
  have h := gate_value circuit (List.ofFn z) 21 (by decide) (by
    intro i hi
    change i ∈ [0, 34] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 35 = GateOp.and.eval [value z 0, value z 34] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire36 (z : Fin 14 → Bool) : value z 36 = (value z 11 || value z 13) := by
  have h := gate_value circuit (List.ofFn z) 22 (by decide) (by
    intro i hi
    change i ∈ [11, 13] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 36 = GateOp.or.eval [value z 11, value z 13] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire37 (z : Fin 14 → Bool) : value z 37 = (value z 0 && value z 36) := by
  have h := gate_value circuit (List.ofFn z) 23 (by decide) (by
    intro i hi
    change i ∈ [0, 36] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 37 = GateOp.and.eval [value z 0, value z 36] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire38 (z : Fin 14 → Bool) : value z 38 = (value z 35 && value z 37) := by
  have h := gate_value circuit (List.ofFn z) 24 (by decide) (by
    intro i hi
    change i ∈ [35, 37] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 38 = GateOp.and.eval [value z 35, value z 37] at h
  simpa only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] using h

theorem wire39 (z : Fin 14 → Bool) : value z 39 = (value z 16 || value z 19) := by
  have h := gate_value circuit (List.ofFn z) 25 (by decide) (by
    intro i hi
    change i ∈ [16, 19] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 39 = GateOp.or.eval [value z 16, value z 19] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire40 (z : Fin 14 → Bool) : value z 40 = (value z 39 || value z 22) := by
  have h := gate_value circuit (List.ofFn z) 26 (by decide) (by
    intro i hi
    change i ∈ [39, 22] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 40 = GateOp.or.eval [value z 39, value z 22] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire41 (z : Fin 14 → Bool) : value z 41 = (value z 40 || value z 25) := by
  have h := gate_value circuit (List.ofFn z) 27 (by decide) (by
    intro i hi
    change i ∈ [40, 25] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 41 = GateOp.or.eval [value z 40, value z 25] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire42 (z : Fin 14 → Bool) : value z 42 = (value z 41 || value z 28) := by
  have h := gate_value circuit (List.ofFn z) 28 (by decide) (by
    intro i hi
    change i ∈ [41, 28] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 42 = GateOp.or.eval [value z 41, value z 28] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire43 (z : Fin 14 → Bool) : value z 43 = (value z 42 || value z 31) := by
  have h := gate_value circuit (List.ofFn z) 29 (by decide) (by
    intro i hi
    change i ∈ [42, 31] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 43 = GateOp.or.eval [value z 42, value z 31] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire44 (z : Fin 14 → Bool) : value z 44 = (value z 43 || value z 32) := by
  have h := gate_value circuit (List.ofFn z) 30 (by decide) (by
    intro i hi
    change i ∈ [43, 32] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 44 = GateOp.or.eval [value z 43, value z 32] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire45 (z : Fin 14 → Bool) : value z 45 = (value z 44 || value z 33) := by
  have h := gate_value circuit (List.ofFn z) 31 (by decide) (by
    intro i hi
    change i ∈ [44, 33] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 45 = GateOp.or.eval [value z 44, value z 33] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem wire46 (z : Fin 14 → Bool) : value z 46 = (value z 45 || value z 38) := by
  have h := gate_value circuit (List.ofFn z) 32 (by decide) (by
    intro i hi
    change i ∈ [45, 38] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_ofFn]
    rcases hi with rfl | rfl <;> decide)
  change value z 46 = GateOp.or.eval [value z 45, value z 38] at h
  simpa only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] using h

theorem pointZero (earlier point line7 line11 line13 : Bool) :
    (((earlier || (point && line7)) || (point && line13)) ||
      ((point && (line7 || line11)) && (point && (line11 || line13)))) =
    (earlier || (point && ((line7 || line11) || line13))) := by
  cases earlier <;> cases point <;> cases line7 <;> cases line11 <;> cases line13 <;> rfl

theorem rowsExists (P : Fin 7 → Prop) :
    (∃ p, P p) ↔ ((((((P 1 ∨ P 2) ∨ P 3) ∨ P 4) ∨ P 5) ∨ P 6) ∨ P 0) := by
  constructor
  · rintro ⟨p, hp⟩
    fin_cases p <;> tauto
  · rintro (hp | hp)
    · rcases hp with (((((h1 | h2) | h3) | h4) | h5) | h6)
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
      · exact ⟨3, h3⟩
      · exact ⟨4, h4⟩
      · exact ⟨5, h5⟩
      · exact ⟨6, h6⟩
    · exact ⟨0, hp⟩

theorem rowTruth (z : Fin 14 → Bool) (p a b c : Fin 7)
    (row : ∀ l : Fin 7, incident p l ↔ l = a ∨ l = b ∨ l = c) :
    (∃ l : Fin 7, incident p l ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true) ↔
    (z (Fin.castAdd 7 p) && ((z (Fin.natAdd 7 a) || z (Fin.natAdd 7 b)) ||
      z (Fin.natAdd 7 c))) = true := by
  simp only [Bool.and_eq_true, Bool.or_eq_true]
  constructor
  · rintro ⟨l, inc, point, line⟩
    rcases (row l).mp inc with rfl | rfl | rfl
    · exact ⟨point, Or.inl (Or.inl line)⟩
    · exact ⟨point, Or.inl (Or.inr line)⟩
    · exact ⟨point, Or.inr line⟩
  · rintro ⟨point, (line | line) | line⟩
    · exact ⟨a, (row a).mpr (Or.inl rfl), point, line⟩
    · exact ⟨b, (row b).mpr (Or.inr (Or.inl rfl)), point, line⟩
    · exact ⟨c, (row c).mpr (Or.inr (Or.inr rfl)), point, line⟩

theorem row0 : ∀ l : Fin 7, incident 0 l ↔ l = 0 ∨ l = 4 ∨ l = 6 := by
  decide +kernel

theorem row1 : ∀ l : Fin 7, incident 1 l ↔ l = 0 ∨ l = 1 ∨ l = 5 := by
  decide +kernel

theorem row2 : ∀ l : Fin 7, incident 2 l ↔ l = 1 ∨ l = 2 ∨ l = 6 := by
  decide +kernel

theorem row3 : ∀ l : Fin 7, incident 3 l ↔ l = 0 ∨ l = 2 ∨ l = 3 := by
  decide +kernel

theorem row4 : ∀ l : Fin 7, incident 4 l ↔ l = 1 ∨ l = 3 ∨ l = 4 := by
  decide +kernel

theorem row5 : ∀ l : Fin 7, incident 5 l ↔ l = 2 ∨ l = 4 ∨ l = 5 := by
  decide +kernel

theorem row6 : ∀ l : Fin 7, incident 6 l ↔ l = 3 ∨ l = 5 ∨ l = 6 := by
  decide +kernel

def allStars (z : Fin 14 → Bool) : Bool :=
  (((((((z 1 && ((z 7 || z 8) || z 12)) ||
    (z 2 && ((z 8 || z 9) || z 13))) ||
    (z 3 && ((z 7 || z 9) || z 10))) ||
    (z 4 && ((z 8 || z 10) || z 11))) ||
    (z 5 && ((z 9 || z 11) || z 12))) ||
    (z 6 && ((z 10 || z 12) || z 13))) ||
    (z 0 && ((z 7 || z 11) || z 13)))

theorem starsSpec (z : Fin 14 → Bool) : allStars z = decide (edgeSpec z) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  unfold edgeSpec
  rw [rowsExists]
  rw [rowTruth z 0 0 4 6 row0,
    rowTruth z 1 0 1 5 row1,
    rowTruth z 2 1 2 6 row2,
    rowTruth z 3 0 2 3 row3,
    rowTruth z 4 1 3 4 row4,
    rowTruth z 5 2 4 5 row5,
    rowTruth z 6 3 5 6 row6]
  simp only [allStars, Bool.or_eq_true]
  rfl

set_option maxHeartbeats 2000000 in
theorem computes (z : Fin 14 → Bool) : circuitFun 14 circuit z = decide (edgeSpec z) := by
  change value z 46 = _
  simp only [wire46, wire45, wire44, wire43, wire42, wire41, wire40, wire39, wire38,
    wire37, wire36, wire35, wire34, wire33, wire32, wire31, wire30, wire29, wire28, wire27,
    wire26, wire25, wire24, wire23, wire22, wire21, wire20, wire19, wire18, wire17,
    wire16, wire15, wire14]
  rw [show value z 0 = z 0 from raw_value z 0, show value z 1 = z 1 from raw_value z 1,
    show value z 2 = z 2 from raw_value z 2, show value z 3 = z 3 from raw_value z 3,
    show value z 4 = z 4 from raw_value z 4, show value z 5 = z 5 from raw_value z 5,
    show value z 6 = z 6 from raw_value z 6, show value z 7 = z 7 from raw_value z 7,
    show value z 8 = z 8 from raw_value z 8, show value z 9 = z 9 from raw_value z 9,
    show value z 10 = z 10 from raw_value z 10, show value z 11 = z 11 from raw_value z 11,
    show value z 12 = z 12 from raw_value z 12, show value z 13 = z 13 from raw_value z 13]
  rw [pointZero, ← starsSpec]
  rfl

theorem point_ne_line (p l : Fin 7) : Fin.castAdd 7 p ≠ Fin.natAdd 7 l := by
  intro same
  have values := congrArg Fin.val same
  simp only [Fin.val_castAdd, Fin.val_natAdd] at values
  omega

theorem graphEval (z : Fin 14 → Bool) : graphFun graph ∅ z = decide (edgeSpec z) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, adj, hu, hv⟩
    rw [SimpleGraph.fromRel_adj] at adj
    rcases adj.2 with ⟨p, l, h, rfl, rfl⟩ | ⟨p, l, h, rfl, rfl⟩
    · exact ⟨p, l, h, hu, hv⟩
    · exact ⟨p, l, h, hv, hu⟩
  · rintro ⟨p, l, h, hp, hl⟩
    refine ⟨Fin.castAdd 7 p, Fin.natAdd 7 l, ?_, hp, hl⟩
    exact (SimpleGraph.fromRel_adj _ _ _).2
      ⟨point_ne_line p l, Or.inl ⟨p, l, h, rfl, rfl⟩⟩

theorem below21 : BelowF graph circuit 21 := by
  intro z h
  change value z 35 = true at h
  rw [wire35, wire34, show value z 0 = z 0 from raw_value z 0,
    show value z 7 = z 7 from raw_value z 7, show value z 11 = z 11 from raw_value z 11] at h
  rw [graphEval]
  apply decide_eq_true
  obtain ⟨point, line⟩ := Bool.and_eq_true_iff.mp h
  rcases Bool.or_eq_true_iff.mp line with h7 | h11
  · exact ⟨0, 0, by decide, point, h7⟩
  · exact ⟨0, 4, by decide, point, h11⟩

theorem below23 : BelowF graph circuit 23 := by
  intro z h
  change value z 37 = true at h
  rw [wire37, wire36, show value z 0 = z 0 from raw_value z 0,
    show value z 11 = z 11 from raw_value z 11, show value z 13 = z 13 from raw_value z 13] at h
  rw [graphEval]
  apply decide_eq_true
  obtain ⟨point, line⟩ := Bool.and_eq_true_iff.mp h
  rcases Bool.or_eq_true_iff.mp line with h11 | h13
  · exact ⟨0, 4, by decide, point, h11⟩
  · exact ⟨0, 6, by decide, point, h13⟩

theorem below24 : BelowF graph circuit 24 := by
  intro z h
  change value z 38 = true at h
  rw [wire38] at h
  exact below21 z (Bool.and_eq_true_iff.mp h).1

def edges : List (ℕ × ℕ) :=
  (List.finRange 7).flatMap (fun p => ((List.finRange 7).filter (fun l => decide (incident p l))).map
    (fun l => (p.val, 7 + l.val)))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem reread : PEqualNP.ReadK.doubleReread circuit 14 (fun w => decide (7 ≤ w)) edges = [(0, 11)] := by
  decide +kernel
private def liftOnlyLines (i : Fin 14) : Bool := decide (7 ≤ i.val)

private def liftIsOr : GateOp → Bool
  | .or => true
  | _ => false

set_option maxHeartbeats 2000000 in
private theorem liftEarlyWires :
    ∀ (j : Fin 25) (b : Fin 2), liftIsOr (gateAt circuit j.val).op = true →
      opnd circuit j.val b ∈ [7, 8, 9, 10, 11, 12, 13, 14, 17, 20, 23, 26, 29] := by
  decide +kernel

private theorem liftEarlyWitness (w : ℕ)
    (hw : w ∈ [7, 8, 9, 10, 11, 12, 13, 14, 17, 20, 23, 26, 29]) :
    PEqualNP.ReadTwo.wval circuit liftOnlyLines w = true := by
  change value liftOnlyLines w = true
  have h7 : value liftOnlyLines 7 = true := raw_value liftOnlyLines (7 : Fin 14)
  have h8 : value liftOnlyLines 8 = true := raw_value liftOnlyLines (8 : Fin 14)
  have h9 : value liftOnlyLines 9 = true := raw_value liftOnlyLines (9 : Fin 14)
  have h10 : value liftOnlyLines 10 = true := raw_value liftOnlyLines (10 : Fin 14)
  have h11 : value liftOnlyLines 11 = true := raw_value liftOnlyLines (11 : Fin 14)
  have h12 : value liftOnlyLines 12 = true := raw_value liftOnlyLines (12 : Fin 14)
  have h13 : value liftOnlyLines 13 = true := raw_value liftOnlyLines (13 : Fin 14)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · simp only [wire14, h7, Bool.true_or]
  · simp only [wire17, h8, Bool.true_or]
  · simp only [wire20, h7, Bool.true_or]
  · simp only [wire23, h8, Bool.true_or]
  · simp only [wire26, h9, Bool.true_or]
  · simp only [wire29, h10, Bool.true_or]

private theorem liftSpineStep (j : ℕ) (hlo : 25 ≤ j) (hhi : j < 32)
    (z : Fin 14 → Bool) (h : gateVal 14 circuit j z = true) :
    gateVal 14 circuit (j + 1) z = true := by
  have hj : j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change value z 39 = true at h
    change value z 40 = true
    simp only [wire40, h, Bool.true_or]
  · change value z 40 = true at h
    change value z 41 = true
    simp only [wire41, h, Bool.true_or]
  · change value z 41 = true at h
    change value z 42 = true
    simp only [wire42, h, Bool.true_or]
  · change value z 42 = true at h
    change value z 43 = true
    simp only [wire43, h, Bool.true_or]
  · change value z 43 = true at h
    change value z 44 = true
    simp only [wire44, h, Bool.true_or]
  · change value z 44 = true at h
    change value z 45 = true
    simp only [wire45, h, Bool.true_or]
  · change value z 45 = true at h
    change value z 46 = true
    simp only [wire46, h, Bool.true_or]

private theorem liftSpine (j : ℕ) (hlo : 25 ≤ j) (hhi : j ≤ 32)
    (z : Fin 14 → Bool) (h : gateVal 14 circuit j z = true) :
    circuitFun 14 circuit z = true := by
  change gateVal 14 circuit 32 z = true
  have reach : ∀ k : ℕ, j ≤ k → k ≤ 32 → gateVal 14 circuit k z = true := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro hjk hk
      by_cases he : j = k + 1
      · simpa only [he] using h
      · exact liftSpineStep k (by omega) (by omega) z (ih (by omega) (by omega))
  exact reach 32 hhi (Nat.le_refl 32)

private theorem liftFixed (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (hEval : ∀ z, circuitFun 14 circuit z = graphFun G ∅ z)
    (hfalse : graphFun G ∅ liftOnlyLines = false) :
    PEqualNP.Core.IsLiftFixedPoint G circuit := by
  change ¬ PEqualNP.Core.LiftApplies G circuit
  intro h
  obtain ⟨j, hj, b, hsite⟩ := h
  obtain ⟨_, hop, hnotBelow, hwire⟩ := hsite
  have hj33 : j < 33 := hj
  by_cases hj25 : j < 25
  · have hor : liftIsOr (gateAt circuit j).op = true := congrArg liftIsOr hop
    have hw := liftEarlyWitness _ (liftEarlyWires ⟨j, hj25⟩ b hor)
    have htrue := hwire.1 liftOnlyLines hw
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue
  · apply hnotBelow
    intro z hz
    rw [← hEval z]
    exact liftSpine j (by omega) (by omega) z hz

end PEqualNP.Outside.L_meta_3655

theorem PEqualNP.Outside.L_meta_3655 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [35, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 38] }], output := 46 } → (∀ z : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C z = decide (∃ p3 l3 : Fin 7, (p3.val = l3.val ∨ p3.val = (l3.val + 1) % 7 ∨ p3.val = (l3.val + 3) % 7) ∧ z (Fin.castAdd 7 p3) = true ∧ z (Fin.natAdd 7 l3) = true)) ∧ (PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ua va : Fin 14 => ∃ pa la : Fin 7, (pa.val = la.val ∨ pa.val = (la.val + 1) % 7 ∨ pa.val = (la.val + 3) % 7) ∧ ua = Fin.castAdd 7 pa ∧ va = Fin.natAdd 7 la)) C 21 ∧ PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun ub vb : Fin 14 => ∃ pb lb : Fin 7, (pb.val = lb.val ∨ pb.val = (lb.val + 1) % 7 ∨ pb.val = (lb.val + 3) % 7) ∧ ub = Fin.castAdd 7 pb ∧ vb = Fin.natAdd 7 lb)) C 23 ∧ PEqualNP.TopForm.BelowF (SimpleGraph.fromRel (fun uc vc : Fin 14 => ∃ pc lc : Fin 7, (pc.val = lc.val ∨ pc.val = (lc.val + 1) % 7 ∨ pc.val = (lc.val + 3) % 7) ∧ uc = Fin.castAdd 7 pc ∧ vc = Fin.natAdd 7 lc)) C 24) ∧ PEqualNP.Core.IsLiftFixedPoint (SimpleGraph.fromRel (fun ud vd : Fin 14 => ∃ pd ld : Fin 7, (pd.val = ld.val ∨ pd.val = (ld.val + 1) % 7 ∨ pd.val = (ld.val + 3) % 7) ∧ ud = Fin.castAdd 7 pd ∧ vd = Fin.natAdd 7 ld)) C ∧ PEqualNP.ReadK.doubleReread C 14 (fun w => decide (7 ≤ w)) ((List.finRange 7).flatMap (fun p5 => ((List.finRange 7).filter (fun l5 => decide (p5.val = l5.val ∨ p5.val = (l5.val + 1) % 7 ∨ p5.val = (l5.val + 3) % 7))).map (fun l6 => (p5.val, 7 + l6.val)))) = [(0, 11)] := by
  intro C same
  subst C
  refine ⟨PEqualNP.Outside.L_meta_3655.computes,
    ⟨PEqualNP.Outside.L_meta_3655.below21, PEqualNP.Outside.L_meta_3655.below23,
      PEqualNP.Outside.L_meta_3655.below24⟩, ?_, PEqualNP.Outside.L_meta_3655.reread⟩
  refine PEqualNP.Outside.L_meta_3655.liftFixed PEqualNP.Outside.L_meta_3655.graph (fun z =>
    (PEqualNP.Outside.L_meta_3655.computes z).trans (PEqualNP.Outside.L_meta_3655.graphEval z).symm) ?_
  rw [PEqualNP.Outside.L_meta_3655.graphEval]
  apply decide_eq_false
  rintro ⟨p, l, inc, hp, hl⟩
  have off : PEqualNP.Outside.L_meta_3655.liftOnlyLines (Fin.castAdd 7 p) = false := by
    apply decide_eq_false
    simpa only [Fin.val_castAdd] using Nat.not_le_of_gt p.isLt
  rw [off] at hp
  contradiction
