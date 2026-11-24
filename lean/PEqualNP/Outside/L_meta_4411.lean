import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4411

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The edge-existence function of the 9-vertex graph (Petersen minus a vertex). -/
def E (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

/-- The wires a gate's value depends on: a NOT gate reads only its first input. -/
def readset (g : Gate) : List ℕ :=
  if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs

/-- Flip one coordinate. -/
def flip (v : Fin 9) (x : Fin 9 → Bool) : Fin 9 → Bool :=
  fun i => if i = v then !x i else x i

/-- Candidate witness assignment: vertex `u` true, plus a stabilizer keeping the
precomputed OR wires fixed when `v` flips. -/
def W (v u x1 x2 : Fin 9) : Fin 9 → Bool := fun i =>
  (i = u) || (v = 0 && i = 4) || (v = 4 && i = 0) || (v = x1 && i = x2) || (v = x2 && i = x1)

/-- The flipped witness. -/
def Wf (v u x1 x2 : Fin 9) : Fin 9 → Bool := flip v (W v u x1 x2)

/-- getD of an `ofFn` list below its length. -/
theorem getD_ofFn' {n : ℕ} (y : Fin n → Bool) (v : ℕ) (hv : v < n) :
    (List.ofFn y).getD v false = y ⟨v, hv⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hv]; rfl

/-- getD of the extended 11-wire input list. -/
theorem getD_L_lt (y : Fin 9 → Bool) (x1 x2 : Fin 9) (i : ℕ) (hi : i < 9) :
    (List.ofFn y ++ [y 0 || y 4, y x1 || y x2]).getD i false = y ⟨i, hi⟩ := by
  rw [List.getD_append (List.ofFn y) _ false i (by simpa using hi), getD_ofFn']

theorem getD_L_9 (y : Fin 9 → Bool) (x1 x2 : Fin 9) :
    (List.ofFn y ++ [y 0 || y 4, y x1 || y x2]).getD 9 false = (y 0 || y 4) := by
  rw [List.getD_append_right (List.ofFn y) _ false 9 (by simp)]; simp

theorem getD_L_10 (y : Fin 9 → Bool) (x1 x2 : Fin 9) :
    (List.ofFn y ++ [y 0 || y 4, y x1 || y x2]).getD 10 false = (y x1 || y x2) := by
  rw [List.getD_append_right (List.ofFn y) _ false 10 (by simp)]; simp

theorem getD_L_ge (y : Fin 9 → Bool) (x1 x2 : Fin 9) (i : ℕ) (hi : 11 ≤ i) :
    (List.ofFn y ++ [y 0 || y 4, y x1 || y x2]).getD i false = false := by
  rw [List.getD_append_right (List.ofFn y) _ false i (by simp only [List.length_ofFn]; omega)]
  have hnone : [y 0 || y 4, y x1 || y x2][i - (List.ofFn y).length]? = none :=
    List.getElem?_eq_none (by simp only [List.length_ofFn, List.length_cons, List.length_nil]; omega)
  rw [List.getD_eq_getElem?_getD, hnone]; rfl

/-- A fan-in-two gate whose read-set misses `v` computes the same value on wire lists
that agree off `v`. -/
theorem gate_val_eq (g : Gate) (v : ℕ)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hv : v ∉ readset g) (w w' : List Bool)
    (h : ∀ i, i ≠ v → w.getD i false = w'.getD i false) :
    g.op.eval (g.inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rcases g with ⟨op, inputs⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · have hrs : readset ⟨GateOp.and, inputs⟩ = inputs := by
      unfold readset; simp [GateOp.eval]
    rw [hrs] at hv
    have hm : inputs.map (fun i => w.getD i false) = inputs.map (fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => h i (fun hc => hv (hc ▸ hi)))
    rw [hm]
  · have hrs : readset ⟨GateOp.or, inputs⟩ = inputs := by
      unfold readset; simp [GateOp.eval]
    rw [hrs] at hv
    have hm : inputs.map (fun i => w.getD i false) = inputs.map (fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => h i (fun hc => hv (hc ▸ hi)))
    rw [hm]
  · have hrs : readset ⟨GateOp.not, inputs⟩ = inputs.take 1 := by
      unfold readset; simp [GateOp.eval]
    rw [hrs] at hv
    cases inputs with
    | nil => simp [GateOp.eval]
    | cons a as =>
        have hne : v ≠ a := fun hc => hv (by simp [hc])
        simp only [GateOp.eval, List.map_cons]
        have e1 : ((w.getD a false) :: List.map (fun i => w.getD i false) as).headD false
            = w.getD a false := rfl
        have e2 : ((w'.getD a false) :: List.map (fun i => w'.getD i false) as).headD false
            = w'.getD a false := rfl
        rw [e1, e2, h a (Ne.symm hne)]

/-- getD of a list extended by one element. -/
theorem getD_snoc (l : List Bool) (c : Bool) (j : ℕ) :
    (l ++ [c]).getD j false
      = if j < l.length then l.getD j false else if j = l.length then c else false := by
  by_cases h : j < l.length
  · rw [List.getD_append l [c] false j h]; simp [h]
  · rw [List.getD_append_right l [c] false j (Nat.le_of_not_lt h)]
    by_cases hjeq : j = l.length
    · subst hjeq; simp
    · have h1 : [c].length ≤ j - l.length := by simp only [List.length_singleton]; omega
      rw [List.getD_eq_default _ false h1]
      simp [h, hjeq]

/-- Folding gates that never read `v` over two wire lists agreeing off `v` gives wire
lists agreeing off `v`. -/
theorem foldl_off (gs : List Gate) (v : ℕ) (A B : List Bool)
    (hlen : A.length = B.length)
    (hAB : ∀ i, i ≠ v → A.getD i false = B.getD i false)
    (hg : ∀ g ∈ gs, v ∉ readset g)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    ∀ i, i ≠ v →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) A).getD i false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) B).getD i false := by
  induction gs generalizing A B with
  | nil => exact hAB
  | cons g gs ih =>
      have hgmem : g ∈ g :: gs := List.mem_cons_self ..
      have hval : g.op.eval (g.inputs.map fun i => A.getD i false)
                = g.op.eval (g.inputs.map fun i => B.getD i false) :=
        gate_val_eq g v (hfan g hgmem) (hg g hgmem) A B hAB
      simp only [List.foldl_cons]
      have hlen' : (A ++ [g.op.eval (g.inputs.map fun i => A.getD i false)]).length
                 = (B ++ [g.op.eval (g.inputs.map fun i => B.getD i false)]).length := by
        simp [hlen]
      refine ih _ _ hlen' ?_ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
        (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      intro j hj
      rw [getD_snoc A _ j, getD_snoc B _ j]
      rw [show B.length = A.length from hlen.symm]
      by_cases hjlt : j < A.length
      · simp only [if_pos hjlt, hAB j hj]
      · simp only [if_neg hjlt]
        by_cases hjeq : j = A.length
        · simp only [if_pos hjeq, hval]
        · simp only [if_neg hjeq]

/-- Folding preserves the leading wire values. -/
theorem foldl_leading (gs : List Gate) (A : List Bool) (i : ℕ) (hi : i < A.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) A).getD i false
      = A.getD i false := by
  induction gs generalizing A with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (A ++ [g.op.eval (g.inputs.map fun i => A.getD i false)])
        (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append A [_] false i hi

/-- Finite witness: for every vertex `v` and allowed pair `x1 x2`, some vertex `u`
makes `E` change when `v` flips, while the two precomputed OR wires stay fixed. -/
theorem witness : ∀ (v x1 x2 : Fin 9), x1 ≠ 0 → x1 ≠ 4 → x2 ≠ 0 → x2 ≠ 4 → x1 ≠ x2 →
    ∃ u : Fin 9,
      E (W v u x1 x2) ≠ E (Wf v u x1 x2) ∧
      ((W v u x1 x2) 0 || (W v u x1 x2) 4) = ((Wf v u x1 x2) 0 || (Wf v u x1 x2) 4) ∧
      ((W v u x1 x2) x1 || (W v u x1 x2) x2) = ((Wf v u x1 x2) x1 || (Wf v u x1 x2) x2) ∧
      (∀ i : Fin 9, i ≠ v → (W v u x1 x2) i = (Wf v u x1 x2) i) := by
  decide

end PEqualNP.Outside.L_meta_4411

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_4411

theorem PEqualNP.Outside.L_meta_4411 : ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x10 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)), x10 x1 || x10 x2]) = (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)))) → ∀ (x11 : Fin (9 : ℕ)), ∃ x12 ∈ x3.gates, ↑x11 ∈ if x12.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x12.inputs else x12.inputs
 := by
  intro x1 x2 x3 h1 h2 h3 h4 h5 hfan hev x11
  by_contra hcon
  push_neg at hcon
  obtain ⟨u, hE, h9, h10, hdiff⟩ := witness x11 x1 x2 h1 h2 h3 h4 h5
  set x := W x11 u x1 x2 with hx
  set x' := Wf x11 u x1 x2 with hx'
  have hevE : ∀ y : Fin 9 → Bool,
      x3.eval (List.ofFn y ++ [y 0 || y 4, y x1 || y x2]) = E y := hev
  have hlen : (List.ofFn x ++ [x 0 || x 4, x x1 || x x2]).length
             = (List.ofFn x' ++ [x' 0 || x' 4, x' x1 || x' x2]).length := by simp
  have hAB : ∀ i, i ≠ (x11 : ℕ) →
      (List.ofFn x ++ [x 0 || x 4, x x1 || x x2]).getD i false
      = (List.ofFn x' ++ [x' 0 || x' 4, x' x1 || x' x2]).getD i false := by
    intro i hi
    by_cases hi9 : i < 9
    · rw [getD_L_lt x x1 x2 i hi9, getD_L_lt x' x1 x2 i hi9]
      exact hdiff ⟨i, hi9⟩ (fun h => hi (congrArg Fin.val h))
    · by_cases hi9' : i = 9
      · subst hi9'; rw [getD_L_9 x x1 x2, getD_L_9 x' x1 x2]; exact h9
      · by_cases hi10 : i = 10
        · subst hi10; rw [getD_L_10 x x1 x2, getD_L_10 x' x1 x2]; exact h10
        · rw [getD_L_ge x x1 x2 i (by omega), getD_L_ge x' x1 x2 i (by omega)]
  have hg : ∀ g ∈ x3.gates, (x11 : ℕ) ∉ readset g := by
    intro g hg
    simpa [readset] using hcon g hg
  have hfan' : ∀ g ∈ x3.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
    fun g hg => (hfan g hg).1
  have hwires := foldl_off x3.gates (x11 : ℕ)
      (List.ofFn x ++ [x 0 || x 4, x x1 || x x2])
      (List.ofFn x' ++ [x' 0 || x' 4, x' x1 || x' x2]) hlen hAB hg hfan'
  have houtv : x3.output ≠ (x11 : ℕ) := by
    intro heq
    have hproj : ∀ y : Fin 9 → Bool, E y = y x11 := by
      intro y
      have e := hevE y
      simp only [Circuit.eval, Circuit.wires] at e
      rw [heq] at e
      have hw : (x3.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
            (List.ofFn y ++ [y 0 || y 4, y x1 || y x2])).getD (x11 : ℕ) false
          = (List.ofFn y ++ [y 0 || y 4, y x1 || y x2]).getD (x11 : ℕ) false :=
        foldl_leading x3.gates _ (x11 : ℕ)
          (by simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_singleton]
              have := x11.isLt; omega)
      rw [hw, getD_L_lt y x1 x2 (x11 : ℕ) x11.isLt] at e
      exact e.symm
    have c := hproj (fun i => decide (i = x11))
    have hr : decide (x11 = x11) = true := by simp
    rw [hr] at c
    have hf : E (fun i : Fin 9 => decide (i = x11)) = false := by fin_cases x11 <;> decide
    rw [hf] at c
    exact Bool.false_ne_true c
  have heqv : x3.eval (List.ofFn x ++ [x 0 || x 4, x x1 || x x2])
            = x3.eval (List.ofFn x' ++ [x' 0 || x' 4, x' x1 || x' x2]) := by
    have h1 := hwires x3.output houtv
    simp only [Circuit.eval, Circuit.wires]
    exact h1
  rw [hevE x, hevE x'] at heqv
  exact hE heqv
