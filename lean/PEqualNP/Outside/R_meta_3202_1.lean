import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3202_1_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma preserved (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma headVal (g : Gate) (tail : List Gate) (o : ℕ) (x : Fin 9 → Bool) :
    (Circuit.wires ⟨g :: tail, o⟩ (List.ofFn x)).getD 9 false =
      g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
  let w := List.ofFn x
  have hl : w.length = 9 := by simp [w]
  change (tail.foldl step (step w g)).getD 9 false = _
  rw [preserved tail (step w g) 9 (by simp [step, hl])]
  simpa only [step, w, List.length_ofFn] using
    atEnd (List.ofFn x) (g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false))

end PEqualNP.Outside.R_meta_3202_1_aux

theorem PEqualNP.Outside.R_meta_3202_1
    (h1 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
      (∃ (x3 x4 : Fin D.gates.length), x3 < x4 ∧ (x3 : ℕ) = 6 ∧ (x4 : ℕ) ≤ 8 ∧
        (D.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (D.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        ∀ x5 : Fin D.gates.length, (D.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not →
          x5 = x3 ∨ x5 = x4) →
      ∃ y : Fin 9 → Bool,
        D.eval (List.ofFn y ++ [y 0 || y 2]) ≠
          (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
           y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
           y 6 && y 8 || y 8 && y 5))
    (h2 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
      (∃ (x3 x4 : Fin D.gates.length), x3 < x4 ∧ (x3 : ℕ) = 6 ∧ ((x4 : ℕ) = 9 ∨ (x4 : ℕ) = 10) ∧
        (D.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (D.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        ∀ x5 : Fin D.gates.length, (D.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not →
          x5 = x3 ∨ x5 = x4) →
      ∃ y : Fin 9 → Bool,
        D.eval (List.ofFn y ++ [y 0 || y 2]) ≠
          (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
           y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
           y 6 && y 8 || y 8 && y 5))
    (h3 : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 14 →
      (∃ (x3 x4 : Fin D.gates.length), x3 < x4 ∧ (x3 : ℕ) = 6 ∧ 11 ≤ (x4 : ℕ) ∧
        (D.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        (D.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
        ∀ x5 : Fin D.gates.length, (D.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not →
          x5 = x3 ∨ x5 = x4) →
      ∃ y : Fin 9 → Bool,
        D.eval (List.ofFn y ++ [y 0 || y 2]) ≠
          (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
           y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
           y 6 && y 8 || y 8 && y 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (7 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro x1 hfan hnots hhead hfun
  obtain ⟨gs, o⟩ := x1
  cases gs with
  | nil =>
    obtain ⟨x3, _⟩ := hnots
    exact Fin.elim0 x3
  | cons g tail =>
    by_contra hshort
    change ¬ 16 ≤ (g :: tail).length at hshort
    simp only [List.length_cons] at hshort
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨tail, o⟩
    have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
      intro a ha
      exact hfan a (List.mem_cons_of_mem g ha)
    have hDsize : D.size ≤ 14 := by
      change tail.length ≤ 14
      omega
    obtain ⟨x3, x4, hlt, hx3, hnot3, hnot4, huniq⟩ := hnots
    have hx3pos : 0 < (x3 : ℕ) := by omega
    have hx4pos : 0 < (x4 : ℕ) := by omega
    let x3' : Fin D.gates.length := ⟨(x3 : ℕ) - 1, by
      change (x3 : ℕ) - 1 < tail.length
      have := x3.isLt
      simp only [List.length_cons] at this
      omega⟩
    let x4' : Fin D.gates.length := ⟨(x4 : ℕ) - 1, by
      change (x4 : ℕ) - 1 < tail.length
      have := x4.isLt
      simp only [List.length_cons] at this
      omega⟩
    have hlt' : x3' < x4' := by
      change (x3 : ℕ) - 1 < (x4 : ℕ) - 1
      have : (x3 : ℕ) < (x4 : ℕ) := hlt
      omega
    have hx3' : (x3' : ℕ) = 6 := by
      change (x3 : ℕ) - 1 = 6
      omega
    have hget3 : (D.gates.get x3').op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      have hidx : (⟨g :: tail, o⟩ : PEqualNP.CircuitLowerBounds.Circuit).gates.get x3 =
          D.gates.get x3' := by
        simp only [List.get_eq_getElem, D]
        have heq : (x3 : ℕ) = (x3' : ℕ) + 1 := by change (x3 : ℕ) = (x3 : ℕ) - 1 + 1; omega
        simp_rw [heq]
        rfl
      rw [← hidx]
      exact hnot3
    have hget4 : (D.gates.get x4').op = PEqualNP.CircuitLowerBounds.GateOp.not := by
      have hidx : (⟨g :: tail, o⟩ : PEqualNP.CircuitLowerBounds.Circuit).gates.get x4 =
          D.gates.get x4' := by
        simp only [List.get_eq_getElem, D]
        have heq : (x4 : ℕ) = (x4' : ℕ) + 1 := by change (x4 : ℕ) = (x4 : ℕ) - 1 + 1; omega
        simp_rw [heq]
        rfl
      rw [← hidx]
      exact hnot4
    have huniq' : ∀ x5 : Fin D.gates.length,
        (D.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3' ∨ x5 = x4' := by
      intro x5 hx5
      let y5 : Fin (g :: tail).length := ⟨(x5 : ℕ) + 1, by
        have hlt5 : (x5 : ℕ) < tail.length := x5.isLt
        simp only [List.length_cons]
        omega⟩
      have hy5op : ((⟨g :: tail, o⟩ : PEqualNP.CircuitLowerBounds.Circuit).gates.get y5).op =
          PEqualNP.CircuitLowerBounds.GateOp.not := by
        simpa [List.get_eq_getElem, D, y5] using hx5
      rcases huniq y5 hy5op with h | h
      · left
        ext
        have hval : (y5 : ℕ) = (x3 : ℕ) := congrArg Fin.val h
        dsimp [y5] at hval
        dsimp [x3']
        omega
      · right
        ext
        have hval : (y5 : ℕ) = (x4 : ℕ) := congrArg Fin.val h
        dsimp [y5] at hval
        dsimp [x4']
        omega
    have hsplit : (x4' : ℕ) ≤ 8 ∨ ((x4' : ℕ) = 9 ∨ (x4' : ℕ) = 10) ∨ 11 ≤ (x4' : ℕ) := by omega
    have hbad : ∃ y : Fin 9 → Bool,
        D.eval (List.ofFn y ++ [y 0 || y 2]) ≠
          (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
           y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 ||
           y 6 && y 8 || y 8 && y 5) := by
      rcases hsplit with hle | heq | hge
      · exact h1 D hDfan hDsize ⟨x3', x4', hlt', hx3', hle, hget3, hget4, huniq'⟩
      · exact h2 D hDfan hDsize ⟨x3', x4', hlt', hx3', heq, hget3, hget4, huniq'⟩
      · exact h3 D hDfan hDsize ⟨x3', x4', hlt', hx3', hge, hget3, hget4, huniq'⟩
    obtain ⟨y, hy⟩ := hbad
    apply hy
    have hg := (PEqualNP.Outside.R_meta_3202_1_aux.headVal g tail o y).symm.trans (hhead y)
    have hh := congrFun hfun y
    change (tail.foldl PEqualNP.Outside.R_meta_3202_1_aux.step
      (List.ofFn y ++ [g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false)])).getD o false = _ at hh
    rw [hg] at hh
    exact hh
