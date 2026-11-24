import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3460
open PEqualNP.CircuitLowerBounds

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_append (F : List Bool → Gate → Bool) (a b : List Gate) (w : List Bool) :
    fl F (a ++ b) w = fl F b (fl F a w) := by
  simp [fl, List.foldl_append]

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

theorem fl_len (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ w : List Bool, (fl F gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [fl_cons, ih]
    simp
    omega

theorem fl_keep (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (fl F gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [fl_cons, ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

def EV (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def shg (n m : ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + m) }

theorem ev_shift (n m : ℕ) (g : Gate) (w w' : List Bool)
    (h : ∀ i, w'.getD (if i < n then i else i + m) false = w.getD i false) :
    EV w' (shg n m g) = EV w g := by
  show g.op.eval ((g.inputs.map (fun w => if w < n then w else w + m)).map (fun i => w'.getD i false))
    = g.op.eval (g.inputs.map fun i => w.getD i false)
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact h i

theorem shift_sim (n m : ℕ) : ∀ (gs : List Gate) (w w' : List Bool), n ≤ w.length →
    w'.length = w.length + m →
    (∀ i, w'.getD (if i < n then i else i + m) false = w.getD i false) →
    ∀ i, (fl EV (gs.map (shg n m)) w').getD (if i < n then i else i + m) false
      = (fl EV gs w).getD i false := by
  intro gs
  induction gs with
  | nil => intro w w' _ _ h i; exact h i
  | cons g gs ih =>
    intro w w' hn hl h
    rw [List.map_cons, fl_cons, fl_cons]
    have hv := ev_shift n m g w w' h
    apply ih
    · rw [List.length_append]; exact Nat.le_succ_of_le hn
    · rw [List.length_append, List.length_append, hl]; simp; omega
    · intro i
      rcases Nat.lt_trichotomy i w.length with hi | hi | hi
      · have hj : (if i < n then i else i + m) < w'.length := by split <;> omega
        rw [getD_snoc_lt _ _ _ hj, getD_snoc_lt _ _ _ hi]
        exact h i
      · have hni : ¬ i < n := by omega
        rw [if_neg hni, hi, ← hl, getD_snoc_eq, getD_snoc_eq]
        exact hv
      · have hni : ¬ i < n := by omega
        rw [if_neg hni, getD_snoc_gt _ _ _ (by omega), getD_snoc_gt _ _ _ hi]

end PEqualNP.Outside.L_meta_3460

open PEqualNP.Outside.L_meta_3460 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3460 : ∀ (n : ℕ) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool), (∀ i < G0.length, ∀ w ∈ (G0.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w < n + i) → (∀ i : ℕ, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (if i < n then i else i + G0.length) false = (C.wires (List.ofFn x)).getD i false) ∧ (∀ i < G0.length, ((⟨G0 ++ C.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (fun w => if w < n then w else w + G0.length) } : PEqualNP.CircuitLowerBounds.Gate)), C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false = ((⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x)).getD (n + i) false) := by
  intro n G0 C x hG
  have hx : (List.ofFn x).length = n := by simp
  constructor
  · intro i
    show (fl EV (G0 ++ C.gates.map (shg n G0.length)) (List.ofFn x)).getD (if i < n then i else i + G0.length) false
      = (fl EV C.gates (List.ofFn x)).getD i false
    rw [fl_append]
    apply shift_sim n G0.length C.gates (List.ofFn x) (fl EV G0 (List.ofFn x)) (le_of_eq hx.symm)
      (fl_len _ _ _)
    intro j
    by_cases hj : j < n
    · rw [if_pos hj]
      exact fl_keep _ _ _ _ (by omega)
    · rw [if_neg hj]
      have h1 : (fl EV G0 (List.ofFn x)).length ≤ j + G0.length := by rw [fl_len]; omega
      have h2 : (List.ofFn x).length ≤ j := by omega
      rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
  · intro i hi
    show (fl EV (G0 ++ C.gates.map (shg n G0.length)) (List.ofFn x)).getD (n + i) false
      = (fl EV G0 (List.ofFn x)).getD (n + i) false
    rw [fl_append]
    exact fl_keep _ _ _ _ (by rw [fl_len]; omega)
