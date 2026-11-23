import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1322

-- The dual of one gate, where k wires exist before it.
-- A read of a wire that does not exist yet is false in both lists, so such reads are
-- removed (OR), or settle the gate to a constant (AND, NOT).
def dualGate (k : ℕ) : Gate → Gate
  | ⟨GateOp.and, l⟩ =>
      if l.all (fun i => decide (i < k)) then ⟨GateOp.or, l⟩ else ⟨GateOp.and, []⟩
  | ⟨GateOp.or, l⟩ => ⟨GateOp.and, l.filter (fun i => decide (i < k))⟩
  | ⟨GateOp.not, []⟩ => ⟨GateOp.or, []⟩
  | ⟨GateOp.not, i :: _⟩ => if i < k then ⟨GateOp.not, [i]⟩ else ⟨GateOp.or, []⟩
  | g => g

def dualList : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: t => dualGate k g :: dualList (k + 1) t

lemma getD_not (w : List Bool) (i : ℕ) (h : i < w.length) :
    (w.map not).getD i false = !(w.getD i false) := by
  simp [List.getD_eq_getElem?_getD, h]

lemma getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, h]

lemma any_dual (w : List Bool) (l : List ℕ) (h : l.all (fun i => decide (i < w.length)) = true) :
    (l.map fun i => (w.map not).getD i false).any id
      = !((l.map fun i => w.getD i false).all id) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have h2 := ih h.2
    simp only [List.map_cons, List.any_cons, List.all_cons, id, h2, getD_not w a h.1]
    cases w.getD a false <;> simp

lemma all_false (w : List Bool) (l : List ℕ) (h : ¬ l.all (fun i => decide (i < w.length)) = true) :
    (l.map fun i => w.getD i false).all id = false := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, not_and] at h
    simp only [List.map_cons, List.all_cons, id]
    by_cases ha : a < w.length
    · rw [ih (h ha)]; simp
    · rw [getD_ge w a (by omega)]; simp

lemma all_dual (w : List Bool) (l : List ℕ) :
    ((l.filter (fun i => decide (i < w.length))).map fun i => (w.map not).getD i false).all id
      = !((l.map fun i => w.getD i false).any id) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a < w.length
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, List.all_cons, id, ih, getD_not w a ha]
      cases w.getD a false <;> simp
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, id, ih, getD_ge w a (by omega)]
      simp

lemma gate_dual (w : List Bool) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (dualGate w.length g).op.eval
        ((dualGate w.length g).inputs.map fun i => (w.map not).getD i false)
      = !(g.op.eval (g.inputs.map fun i => w.getD i false)) := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and =>
    by_cases h : l.all (fun i => decide (i < w.length)) = true
    · simp only [dualGate, h, ite_true, GateOp.eval]
      exact any_dual w l h
    · simp only [dualGate, h, GateOp.eval]
      rw [all_false w l h]; simp
  | or =>
    simp only [dualGate, GateOp.eval]
    exact all_dual w l
  | not =>
    cases l with
    | nil => simp [dualGate, GateOp.eval]
    | cons a t =>
      by_cases ha : a < w.length
      · simp [dualGate, GateOp.eval, ha]
      · simp [dualGate, GateOp.eval, ha]
  | mod m => simp at hg
  | maj => simp at hg

lemma fold_dual (gates : List Gate) : ∀ w : List Bool,
    (∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    List.foldl (fun (w : List Bool) (g : Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map not)
        (dualList w.length gates)
      = (List.foldl (fun (w : List Bool) (g : Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w gates).map not := by
  induction gates with
  | nil => intro w _; simp [dualList]
  | cons g t ih =>
    intro w h
    have hg := h g (by simp)
    have ht := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (fun g' hg' => h g' (by simp [hg']))
    simp only [dualList, List.foldl_cons]
    rw [gate_dual w g hg]
    simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons,
      List.map_nil] at ht
    exact ht

lemma fold_length (gates : List Gate) : ∀ w : List Bool,
    (List.foldl (fun (w : List Bool) (g : Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w gates).length
      = w.length + gates.length := by
  induction gates with
  | nil => intro w; simp
  | cons g t ih =>
    intro w
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma dualList_length (gates : List Gate) : ∀ k, (dualList k gates).length = gates.length := by
  induction gates with
  | nil => intro k; simp [dualList]
  | cons g t ih => intro k; simp [dualList, ih]

lemma dualGate_ok (k : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((dualGate k g).op = GateOp.and ∨ (dualGate k g).op = GateOp.or ∨
      (dualGate k g).op = GateOp.not) ∧ (dualGate k g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hlen
  cases op with
  | and =>
    by_cases h : l.all (fun i => decide (i < k)) = true
    · simp [dualGate, h, hlen]
    · simp [dualGate, h]
  | or =>
    simp only [dualGate, true_or, true_and]
    exact le_trans (List.length_filter_le _ _) hlen
  | not =>
    cases l with
    | nil => simp [dualGate]
    | cons a t =>
      by_cases ha : a < k
      · simp [dualGate, ha]
      · simp [dualGate, ha]
  | mod m => simp at hop
  | maj => simp at hop

lemma dualGate_not (k : ℕ) (g : Gate) (h : (dualGate k g).op = GateOp.not) :
    g.op = GateOp.not := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and =>
    by_cases h' : l.all (fun i => decide (i < k)) = true
    · simp [dualGate, h'] at h
    · simp [dualGate, h'] at h
  | or => simp [dualGate] at h
  | not => rfl
  | mod m => simp [dualGate] at h
  | maj => simp [dualGate] at h

lemma dualList_ok (gates : List Gate) : ∀ k,
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    ∀ g ∈ dualList k gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 := by
  induction gates with
  | nil => intro k _ g hg; simp [dualList] at hg
  | cons a t ih =>
    intro k h g hg
    simp only [dualList, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact dualGate_ok k a (h a (by simp))
    · exact ih (k + 1) (fun g' hg' => h g' (by simp [hg'])) g hg

lemma dualList_not (gates : List Gate) : ∀ (k i : ℕ) (g' : Gate),
    (dualList k gates)[i]? = some g' → g'.op = GateOp.not →
    ∃ g : Gate, gates[i]? = some g ∧ g.op = GateOp.not := by
  induction gates with
  | nil => intro k i g' h; simp [dualList] at h
  | cons a t ih =>
    intro k i g' h hn
    cases i with
    | zero =>
      simp only [dualList, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨a, by simp, dualGate_not k a hn⟩
    | succ j =>
      simp only [dualList, List.getElem?_cons_succ] at h
      simpa using ih (k + 1) j g' h hn

end PEqualNP.Outside.L_meta_1322

theorem PEqualNP.Outside.L_meta_1322 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  intro n gates h
  refine ⟨PEqualNP.Outside.L_meta_1322.dualList n gates,
    PEqualNP.Outside.L_meta_1322.dualList_length gates n,
    PEqualNP.Outside.L_meta_1322.dualList_ok gates n h,
    PEqualNP.Outside.L_meta_1322.dualList_not gates n, ?_⟩
  intro w x hw
  have hx : List.ofFn x = (List.ofFn (fun p : Fin n => !x p)).map not := by
    rw [List.map_ofFn]
    congr 1
    funext p
    simp
  have hlen : (List.ofFn (fun p : Fin n => !x p)).length = n := by simp
  have key := PEqualNP.Outside.L_meta_1322.fold_dual gates (List.ofFn (fun p : Fin n => !x p))
    (fun g hg => (h g hg).1)
  rw [hlen, ← hx] at key
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [key]
  apply PEqualNP.Outside.L_meta_1322.getD_not
  rw [PEqualNP.Outside.L_meta_1322.fold_length, hlen]
  exact hw
