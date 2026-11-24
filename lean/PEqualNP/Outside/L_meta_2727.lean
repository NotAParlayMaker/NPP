import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2727_aux

open PEqualNP.CircuitLowerBounds

theorem pre (l : List Gate) : ∀ w : List Bool, ∃ s,
    l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ s := by
  induction l with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g l ih =>
    intro w
    obtain ⟨s, hs⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: s, by
      rw [List.foldl_cons, hs, List.append_assoc]; rfl⟩

theorem len (l : List Gate) : ∀ w : List Bool,
    (l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + l.length := by
  induction l with
  | nil => intro w; simp
  | cons g l ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp; omega

end PEqualNP.Outside.L_meta_2727_aux

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
  intro n C j u t hj hgj hu ht himp x
  have hget : C.gates[j] = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [u, t] } := by
    rw [List.getElem?_eq_getElem hj] at hgj
    exact Option.some.inj hgj
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j+1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hset : C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] }
      = C.gates.take j ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] }
        :: C.gates.drop (j+1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos hj]
  have himp' := himp x
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires at himp' ⊢
  simp only at himp' ⊢
  rw [hset]
  rw [hsplit] at himp'
  conv_rhs => rw [hsplit]
  rw [hget] at himp' ⊢
  simp only [List.foldl_append, List.foldl_cons] at himp' ⊢
  set w0 := List.foldl (fun w g => w ++
    [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x) (List.take j C.gates) with hw0
  have hlen : w0.length = n + j := by
    rw [hw0, PEqualNP.Outside.L_meta_2727_aux.len]
    simp; omega
  obtain ⟨s, hs⟩ := PEqualNP.Outside.L_meta_2727_aux.pre (List.drop (j+1) C.gates)
    (w0 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval ([u, t].map fun i => w0.getD i false)])
  rw [hs] at himp'
  rw [List.append_assoc, List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)] at himp'
  congr 3
  revert himp'
  simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil]
  cases w0.getD u false <;> cases w0.getD t false <;> simp
