import Mathlib
import PEqualNP.Defs

/- A monotone fan-in-two AND/OR circuit over the fourteen Fano wires, and the finite checks
that identify the function it computes. -/

namespace PEqualNP.Outside.L_meta_3749_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- The circuit of the step. -/
def c : Circuit :=
  { gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [14, 3]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [16, 10]⟩,
    ⟨GateOp.and, [15, 17]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.and, [5, 19]⟩,
    ⟨GateOp.or, [18, 20]⟩,
    ⟨GateOp.or, [0, 10]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [23, 5]⟩,
    ⟨GateOp.or, [24, 7]⟩,
    ⟨GateOp.and, [22, 25]⟩,
    ⟨GateOp.and, [21, 26]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.and, [4, 28]⟩,
    ⟨GateOp.or, [18, 29]⟩,
    ⟨GateOp.or, [1, 8]⟩,
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.or, [32, 4]⟩,
    ⟨GateOp.or, [33, 7]⟩,
    ⟨GateOp.and, [31, 34]⟩,
    ⟨GateOp.and, [30, 35]⟩,
    ⟨GateOp.or, [27, 36]⟩,
    ⟨GateOp.and, [7, 2]⟩,
    ⟨GateOp.or, [37, 38]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [40, 6]⟩,
    ⟨GateOp.and, [41, 9]⟩,
    ⟨GateOp.or, [39, 42]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.or, [44, 6]⟩,
    ⟨GateOp.and, [45, 11]⟩,
    ⟨GateOp.or, [43, 46]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [48, 6]⟩,
    ⟨GateOp.and, [49, 12]⟩,
    ⟨GateOp.or, [47, 50]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [52, 5]⟩,
    ⟨GateOp.and, [53, 13]⟩,
    ⟨GateOp.or, [51, 54]⟩], output := 55 }

/-- One gate step of `Circuit.wires`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The gate list folded left with `step` is `Circuit.wires`. -/
theorem wires_eq (x : List Bool) : c.wires x = c.gates.foldl step x := rfl

/-- A `getD` that reads `true` reads inside the list. -/
theorem getD_true_lt (l : List Bool) (i : Nat) (h : l.getD i false = true) : i < l.length := by
  induction l generalizing i with
  | nil => simp [List.getD] at h
  | cons a t ih =>
      cases i with
      | zero => simp
      | succ k =>
          have h' : t.getD k false = true := by simpa [List.getD_cons_succ] using h
          have := ih k h'
          simp
          omega

/-- A `getD` past the end of the list reads `false`. -/
theorem getD_false_of_le (l : List Bool) (i : Nat) (h : l.length <= i) : l.getD i false = false := by
  induction l generalizing i with
  | nil => rfl
  | cons a t ih =>
      cases i with
      | zero => simp at h
      | succ k =>
          rw [List.getD_cons_succ]
          exact ih k (by simp at h; omega)

/-- `and` and `or` are monotone in each of two inputs. -/
theorem eval_pair {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ (p q p' q' : Bool), (p = true → p' = true) → (q = true → q' = true) →
      op.eval [p, q] = true → op.eval [p', q'] = true := by
  intro p q p' q' hp hq h
  rcases hop with rfl | rfl
  · cases p <;> cases q <;> cases p' <;> cases q' <;> simp_all [GateOp.eval]
  · cases p <;> cases q <;> cases p' <;> cases q' <;> simp_all [GateOp.eval]

/-- One gate step preserves the pointwise order of wire values. -/
theorem step_mono (w w' : List Bool) (g : Gate) (a b : Nat)
    (hins : g.inputs = [a, b]) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : w.length = w'.length)
    (hle : ∀ i, w.getD i false = true → w'.getD i false = true) :
    (step w g).length = (step w' g).length ∧
      ∀ i, (step w g).getD i false = true → (step w' g).getD i false = true := by
  refine ⟨by simp [step, hlen], ?_⟩
  intro i hi
  have hlen' : w'.length = w.length := hlen.symm
  by_cases hlt : i < w.length
  · rw [step, List.getD_append _ _ _ _ hlt] at hi
    rw [step, List.getD_append _ _ _ _ (by omega : i < w'.length)]
    exact hle i hi
  · have hge : w.length <= i := by omega
    have hge' : w'.length <= i := by omega
    rw [step, List.getD_append_right _ _ _ _ hge] at hi
    rw [step, List.getD_append_right _ _ _ _ hge']
    have hz : i - w.length = 0 := by
      by_contra hne
      have hle1 : (1 : Nat) <= i - w.length := by omega
      have h2 : [g.op.eval (g.inputs.map fun i => w.getD i false)].getD (i - w.length) false
          = false := by
        rw [getD_false_of_le]
        simp
        omega
      rw [h2] at hi
      exact Bool.false_ne_true hi
    have hz' : i - w'.length = 0 := by omega
    rw [hz] at hi
    rw [hz']
    simp only [List.getD_cons_zero] at hi ⊢
    have hmap : g.inputs.map (fun i => w.getD i false) = [w.getD a false, w.getD b false] := by
      rw [hins]
      rfl
    have hmap' : g.inputs.map (fun i => w'.getD i false) = [w'.getD a false, w'.getD b false] := by
      rw [hins]
      rfl
    rw [hmap] at hi
    rw [hmap']
    exact eval_pair hop (w.getD a false) (w.getD b false) (w'.getD a false) (w'.getD b false)
      (fun h => hle a h) (fun h => hle b h) hi

/-- Folding the gates preserves the pointwise order of wire values. -/
theorem foldl_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, ∃ a b, g.inputs = [a, b] ∧ (g.op = GateOp.and ∨ g.op = GateOp.or)) :
    ∀ w w', w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (gs.foldl step w).length = (gs.foldl step w').length ∧
        ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step w').getD i false = true := by
  induction gs with
  | nil => intro w w' h1 h2; exact ⟨by simpa using h1, h2⟩
  | cons g gs ih =>
      intro w w' h1 h2
      obtain ⟨a, b, hins, hop⟩ := hgs g (List.mem_cons_self ..)
      obtain ⟨h1', h2'⟩ := step_mono w w' g a b hins hop h1 h2
      exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step w g) (step w' g) h1' h2'

/-- Every gate of the circuit is a two-input `and` or `or`. -/
theorem gate_shapes :
    ∀ g ∈ c.gates, ∃ a b, g.inputs = [a, b] ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
  intro g hg
  simp only [c, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl, by simp⟩

/-- The fourteen wires of an input, spelled out. -/
theorem ofFn14 (x : Fin 14 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := by
  simp [List.ofFn_succ]

/-- The circuit computes a monotone function. -/
theorem mono (x y : Fin 14 → Bool) (h : ∀ i, x i = true → y i = true) :
    circuitFun 14 c x = true → circuitFun 14 c y = true := by
  intro hx
  have hlen : (List.ofFn x).length = (List.ofFn y).length := by simp
  have hle : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases hi14 : i < 14
    · rw [ofFn14 x, ofFn14 y] at *
      interval_cases i <;> simp_all
    · rw [getD_false_of_le (List.ofFn x) i (by rw [ofFn14]; simp; omega)] at hi
      exact (Bool.false_ne_true hi).elim
  obtain ⟨hlen', hle'⟩ := foldl_mono c.gates gate_shapes (List.ofFn x) (List.ofFn y) hlen hle
  have h1 : (c.gates.foldl step (List.ofFn x)).getD c.output false = true := hx
  exact hle' c.output h1

/-- The edges of the Fano plane, as point-line pairs. -/
def edgeList : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)]

/-- The incidence relation of the Fano plane, as point-line pairs. -/
def inc : List (Fin 7 × Fin 7) := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 3), (1, 4), (2, 0), (2, 5), (2, 6), (3, 1), (3, 3), (3, 5), (4, 1), (4, 4), (4, 6), (5, 2), (5, 3), (5, 6), (6, 2), (6, 4), (6, 5)]

/-- `l` is one of the lines through the point `p`. -/
def adj (p l : Fin 7) : Bool := decide ((p, l) ∈ inc)

/-- A line wire that is true exactly when none of its points is. -/
def freeWire (P : Fin 7 → Bool) (l : Fin 7) : Bool :=
  decide (∀ p : Fin 7, P p = true → adj p l = false)

/-- The point-free input determined by a set of true points. -/
def freeOf (P : Fin 7 → Bool) (i : Fin 14) : Bool :=
  if h : i.val < 7 then P ⟨i.val, h⟩
  else freeWire P ⟨i.val - 7, by have := i.isLt; have := h; omega⟩

/-- The point wires of a point-free input. -/
theorem freeOf_pt (P : Fin 7 → Bool) (i : Fin 14) (h : i.val < 7) :
    freeOf P i = P ⟨i.val, h⟩ := by
  simp [freeOf, h]

/-- The line wires of a point-free input. -/
theorem freeOf_line (P : Fin 7 → Bool) (i : Fin 14) (h : ¬ i.val < 7) :
    freeOf P i = freeWire P ⟨i.val - 7, by have := i.isLt; have := h; omega⟩ := by
  simp [freeOf, h]

set_option maxRecDepth 400000 in
/-- Every incidence of the Fano plane is an entry of `edgeList`. -/
theorem mem_edgeList : ∀ (p l : Fin 7), adj p l = true →
    ((⟨p.val, by omega⟩ : Fin 14), (⟨7 + l.val, by omega⟩ : Fin 14)) ∈ edgeList := by
  decide

set_option maxRecDepth 400000 in
/-- The circuit is true on the two wires of every edge. -/
theorem on_edges : ∀ e ∈ edgeList,
    circuitFun 14 c (fun i => decide (i = e.1) || decide (i = e.2)) = true := by
  decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- The circuit is false on every point-free input. -/
theorem freeOf_false : ∀ P : Fin 7 → Bool, circuitFun 14 c (freeOf P) = false := by
  decide

/-- An edge-free input lies below the point-free input of its true points. -/
theorem lift (x : Fin 14 → Bool) (hno : ∀ e ∈ edgeList, ¬ (x e.1 = true ∧ x e.2 = true)) :
    ∀ i, x i = true → freeOf (fun p : Fin 7 => x ⟨p.val, by omega⟩) i = true := by
  intro i hi
  by_cases h7 : i.val < 7
  · rw [freeOf_pt _ i h7]
    simpa using hi
  · rw [freeOf_line _ i h7]
    refine decide_eq_true ?_
    intro p hP
    by_contra hadj
    have hieq : (⟨7 + (i.val - 7), by omega⟩ : Fin 14) = i := by
      ext
      simp
      omega
    exact hno _ (mem_edgeList p ⟨i.val - 7, by omega⟩ (by simpa using hadj))
      ⟨hP, by rw [hieq]; exact hi⟩

end PEqualNP.Outside.L_meta_3749_aux

open PEqualNP.Outside.L_meta_3749_aux
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

set_option maxRecDepth 400000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_3749 :
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    C = ({ gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [14, 3]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [16, 10]⟩,
    ⟨GateOp.and, [15, 17]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.and, [5, 19]⟩,
    ⟨GateOp.or, [18, 20]⟩,
    ⟨GateOp.or, [0, 10]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [23, 5]⟩,
    ⟨GateOp.or, [24, 7]⟩,
    ⟨GateOp.and, [22, 25]⟩,
    ⟨GateOp.and, [21, 26]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.and, [4, 28]⟩,
    ⟨GateOp.or, [18, 29]⟩,
    ⟨GateOp.or, [1, 8]⟩,
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.or, [32, 4]⟩,
    ⟨GateOp.or, [33, 7]⟩,
    ⟨GateOp.and, [31, 34]⟩,
    ⟨GateOp.and, [30, 35]⟩,
    ⟨GateOp.or, [27, 36]⟩,
    ⟨GateOp.and, [7, 2]⟩,
    ⟨GateOp.or, [37, 38]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [40, 6]⟩,
    ⟨GateOp.and, [41, 9]⟩,
    ⟨GateOp.or, [39, 42]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.or, [44, 6]⟩,
    ⟨GateOp.and, [45, 11]⟩,
    ⟨GateOp.or, [43, 46]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [48, 6]⟩,
    ⟨GateOp.and, [49, 12]⟩,
    ⟨GateOp.or, [47, 50]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.or, [52, 5]⟩,
    ⟨GateOp.and, [53, 13]⟩,
    ⟨GateOp.or, [51, 54]⟩], output := 55 } : PEqualNP.CircuitLowerBounds.Circuit) →
 PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 42 ∧
 (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
 (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  rintro C rfl
  show PEqualNP.TopForm.IsAO2 14 c ∧ c.size = 42 ∧
    (∀ x : Fin 14 → Bool, circuitFun 14 c x = decide (∃ e ∈ edgeList, x e.1 = true ∧ x e.2 = true)) ∧
    (∀ e ∈ edgeList, PEqualNP.Core.ReadTwiceAt 14 c (c.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · rfl
  · intro x
    by_cases hx : ∃ e ∈ edgeList, x e.1 = true ∧ x e.2 = true
    · obtain ⟨e, he, h1, h2⟩ := hx
      have hf : circuitFun 14 c x = true := by
        refine mono (fun i => decide (i = e.1) || decide (i = e.2)) x ?_ (on_edges e he)
        intro i hi
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hi
        rcases hi with rfl | rfl
        · exact h1
        · exact h2
      have hdec : decide (∃ e ∈ edgeList, x e.1 = true ∧ x e.2 = true) = true := by
        rw [decide_eq_true_eq]
        exact ⟨e, he, h1, h2⟩
      rw [hf, hdec]
    · have hno : ∀ e ∈ edgeList, ¬ (x e.1 = true ∧ x e.2 = true) := by
        intro e he h; exact hx ⟨e, he, h⟩
      have hsub : ∀ i, x i = true → freeOf (fun p : Fin 7 => x ⟨p.val, by omega⟩) i = true :=
        lift x hno
      have hcontra : circuitFun 14 c x = true →
          circuitFun 14 c (freeOf (fun p : Fin 7 => x ⟨p.val, by omega⟩)) = true :=
        mono x (freeOf (fun p : Fin 7 => x ⟨p.val, by omega⟩)) hsub
      have hfalse : circuitFun 14 c (freeOf (fun p : Fin 7 => x ⟨p.val, by omega⟩)) = false :=
        freeOf_false _
      have hdec : decide (∃ e ∈ edgeList, x e.1 = true ∧ x e.2 = true) = false := by
        rw [decide_eq_false_iff_not]
        rintro ⟨e, he, h1, h2⟩
        exact hno e he ⟨h1, h2⟩
      cases hval : circuitFun 14 c x
      · rw [hdec]
      · rw [hdec]
        exact absurd (hcontra hval) (by rw [hfalse]; exact Bool.false_ne_true)
  · decide
