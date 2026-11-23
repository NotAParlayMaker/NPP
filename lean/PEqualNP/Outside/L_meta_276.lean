import Mathlib
import PEqualNP.Defs

private theorem L276_stable (gs : List PEqualNP.CircuitLowerBounds.Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
        = w.getD i false := by
  induction gs with
  | nil =>
    intro w i _
    rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by rw [List.length_append]; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem L276_key (gs : List PEqualNP.CircuitLowerBounds.Gate) :
    ∀ (w : List Bool) (j a b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      gs[j]? = some g → g.inputs = [a, b] → a < w.length + j → b < w.length + j →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
          (w.length + j) false =
        g.op.eval
          [(gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
              a false,
           (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
              b false] := by
  induction gs with
  | nil =>
    intro w j a b g h
    simp at h
  | cons g0 gs ih =>
    intro w j a b g h hin ha hb
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [List.foldl_cons]
      rw [L276_stable gs _ (w.length + 0) (by rw [List.length_append]; simp),
        L276_stable gs _ a (by rw [List.length_append]; omega),
        L276_stable gs _ b (by rw [List.length_append]; omega)]
      have ha' : a < w.length := by omega
      have hb' : b < w.length := by omega
      simp [hin, List.getD_eq_getElem?_getD, List.getElem?_append_left ha',
        List.getElem?_append_left hb']
    | succ j =>
      rw [List.getElem?_cons_succ] at h
      rw [List.foldl_cons]
      have h2 := ih (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]) j a b g h hin
        (by rw [List.length_append]; simp; omega) (by rw [List.length_append]; simp; omega)
      have e : (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]).length + j
          = w.length + (j + 1) := by
        rw [List.length_append]
        simp
        omega
      rw [e] at h2
      exact h2

theorem PEqualNP.Outside.L_meta_276 : ∀ (n j a b : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.inputs = [a, b] → a < n + j → b < n + j → (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) = (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∪ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) = (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) ∩ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true))) := by
  intro n j a b C g hg hin ha hb
  have hw : ∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false
      = g.op.eval [(C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD a false,
          (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD b false] := by
    intro p
    have h := L276_key C.gates (List.ofFn (fun q : Fin n => decide (q = p))) j a b g hg hin
      (by rw [List.length_ofFn]; exact ha) (by rw [List.length_ofFn]; exact hb)
    rw [List.length_ofFn] at h
    exact h
  constructor
  · intro hop
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [hw p, hop]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · intro hop
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    rw [hw p, hop]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
