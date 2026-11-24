import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3749

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [0, 1]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [7, 8]⟩,
    ⟨.or, [16, 10]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [7, 10]⟩,
    ⟨.and, [5, 19]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [0, 10]⟩,
    ⟨.or, [1, 3]⟩, ⟨.or, [23, 5]⟩, ⟨.or, [24, 7]⟩,
    ⟨.and, [22, 25]⟩, ⟨.and, [21, 26]⟩, ⟨.or, [7, 8]⟩,
    ⟨.and, [4, 28]⟩, ⟨.or, [18, 29]⟩, ⟨.or, [1, 8]⟩,
    ⟨.or, [0, 3]⟩, ⟨.or, [32, 4]⟩, ⟨.or, [33, 7]⟩,
    ⟨.and, [31, 34]⟩, ⟨.and, [30, 35]⟩, ⟨.or, [27, 36]⟩,
    ⟨.and, [7, 2]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [0, 5]⟩,
    ⟨.or, [40, 6]⟩, ⟨.and, [41, 9]⟩, ⟨.or, [39, 42]⟩,
    ⟨.or, [1, 4]⟩, ⟨.or, [44, 6]⟩, ⟨.and, [45, 11]⟩,
    ⟨.or, [43, 46]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [48, 6]⟩,
    ⟨.and, [49, 12]⟩, ⟨.or, [47, 50]⟩, ⟨.or, [2, 4]⟩,
    ⟨.or, [52, 5]⟩, ⟨.and, [53, 13]⟩, ⟨.or, [51, 54]⟩], 55⟩

private def edges : List (Fin 14 × Fin 14) :=
  [(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)]

private def repeated : List (Fin 14 × Fin 14) :=
  [(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)]

private lemma legal : PEqualNP.TopForm.IsAO2 14 circuit := by
  decide +kernel

private def appendGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma snoc_getD (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  rcases lt_trichotomy i w.length with h | rfl | h
  · rw [ite_eq_right (ne_of_lt h), List.getD_append _ _ _ _ h]
  · simp
  · rw [ite_eq_right (ne_of_gt h), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

private lemma fold_mono (gs : List Gate) (u v : List Bool) (hlen : u.length = v.length)
    (legal : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (h : ∀ i, u.getD i false = true → v.getD i false = true) :
    ∀ i, (gs.foldl appendGate u).getD i false = true →
      (gs.foldl appendGate v).getD i false = true := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (appendGate u g) (appendGate v g) (by simp [appendGate, hlen])
      (fun g' hg' => legal g' (List.mem_cons_of_mem g hg'))
    intro i
    simp only [appendGate, snoc_getD, hlen]
    split_ifs
    · rcases legal g List.mem_cons_self with hg | hg
      · simp only [hg, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true]
        exact fun H j hj => h j (H j hj)
      · simp only [hg, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true]
        rintro ⟨j, hj, hv⟩
        exact ⟨j, hj, h j hv⟩
    · exact h i

private lemma cert_mono (x y : Fin 14 → Bool) (h : ∀ i, x i = true → y i = true)
    (hx : circuitFun 14 circuit x = true) : circuitFun 14 circuit y = true := by
  apply fold_mono circuit.gates (List.ofFn x) (List.ofFn y) (by simp) legal.1 ?_ circuit.output hx
  intro i hi
  by_cases hb : i < 14
  · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hb), List.getElem_ofFn] at hi ⊢
    exact h ⟨i, hb⟩ hi
  · rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hb)] at hi
    exact (Bool.false_ne_true hi).elim

private def pointBit (p : Fin 7 → Bool) (i : Fin 14) : Bool :=
  if hi : i.val < 7 then p ⟨i.val, hi⟩ else false

private def negativeRow (p : Fin 7 → Bool) (i : Fin 14) : Bool :=
  if hi : i.val < 7 then p ⟨i.val, hi⟩
  else !(edges.any fun e => decide (e.2 = i) && pointBit p e.1)

private lemma source_lt : ∀ e ∈ edges, e.1.val < 7 := by decide +kernel

set_option maxHeartbeats 500000 in
private lemma negativeCheck : ∀ p : Fin 7 → Bool, circuitFun 14 circuit (negativeRow p) = false := by
  decide +kernel

private lemma acceptsEdge : ∀ e ∈ edges,
    circuitFun 14 circuit (fun i => decide (i = e.1 ∨ i = e.2)) = true := by
  have h : edges.all (fun e => circuitFun 14 circuit (fun i => decide (i = e.1 ∨ i = e.2))) = true := by
    decide +kernel
  exact List.all_eq_true.mp h

-- With the points fixed, all lines disjoint from the chosen points can be set to true.
-- Every input containing no edge is bounded above by the corresponding negative row.
private lemma computes (x : Fin 14 → Bool) :
    circuitFun 14 circuit x = decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hx
    by_contra noEdge
    let p (i : Fin 7) : Bool := x ⟨i.val, by omega⟩
    have grows (i : Fin 14) (hxi : x i = true) : negativeRow p i = true := by
      unfold negativeRow
      split
      · exact hxi
      · rw [Bool.not_eq_true']
        cases hv : edges.any (fun e => decide (e.2 = i) && pointBit p e.1) with
        | false => rfl
        | true =>
          obtain ⟨e, he, hs⟩ := List.any_eq_true.mp hv
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
          have he1 : pointBit p e.1 = x e.1 := by simp [pointBit, source_lt e he, p]
          exact False.elim (noEdge ⟨e, he, he1 ▸ hs.2, hs.1.symm ▸ hxi⟩)
    exact Bool.false_ne_true ((negativeCheck p).symm.trans (cert_mono _ _ grows hx))
  · rintro ⟨e, he, ha, hb⟩
    apply cert_mono _ _ ?_ (acceptsEdge e he)
    intro i hi
    rcases of_decide_eq_true hi with rfl | rfl
    · exact ha
    · exact hb

-- The existing read-count recursion considers one proof tree for both endpoints jointly.
private lemma repetitions : ∀ e ∈ edges,
    PEqualNP.Core.ReadTwiceAt 14 circuit (circuit.output - 14) e.1 e.2 ↔ e ∈ repeated := by
  have h : edges.all (fun e => decide
      (PEqualNP.Core.ReadTwiceAt 14 circuit (circuit.output - 14) e.1 e.2 ↔ e ∈ repeated)) = true := by
    decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp h e he)

end PEqualNP.Outside.L_meta_3749

open PEqualNP.Outside.L_meta_3749 in
theorem PEqualNP.Outside.L_meta_3749 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 35] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [41, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [49, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 50] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 54] }], output := 55 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 42 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  intro C hC
  subst C
  exact ⟨legal, rfl, computes, repetitions⟩
