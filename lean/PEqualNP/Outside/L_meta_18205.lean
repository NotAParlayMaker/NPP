import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18205

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

private def scan {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun a g => a ++ [f a g]) w

private theorem scan_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate)
    (w : List α) : scan f (g :: gs) w = scan f gs (w ++ [f w g]) := rfl

private theorem scan_append {α : Type} (f : List α → Gate → α) (xs ys : List Gate)
    (w : List α) : scan f (xs ++ ys) w = scan f ys (scan f xs w) := by
  simp only [scan, List.foldl_append]

private theorem scan_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan f gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [scan]
  | cons g gs ih => rw [scan_cons, ih]; simp; omega

private theorem scan_earlier {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (k : ℕ) (hk : k < w.length) :
    (scan f gs w).getD k d = w.getD k d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hk

private theorem scan_at_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length) (a b : ℕ)
    (ha : a < w.length + j) (hb : b < w.length + j) (op : α → α → α)
    (hf : ∀ z, f z gs[j] = op (z.getD a d) (z.getD b d)) :
    (scan f gs w).getD (w.length + j) d =
      op ((scan f gs w).getD a d) ((scan f gs w).getD b d) := by
  let pre := scan f (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan f gs w = scan f (gs[j] :: gs.drop (j + 1)) pre := by
    have ht := List.take_append_drop j gs
    conv_lhs => rw [← ht, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan f gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_earlier f _ pre d i (by omega)
  rw [hpre a ha, hpre b hb, hs, scan_cons, scan_earlier f _ _ d _ (by simp [hp]),
    List.getD_append_right _ _ _ _ (by omega)]
  simpa [hp] using hf pre

private def wval (N : ℕ) (D : Circuit) (z : Fin N → Bool) (w : ℕ) : Bool :=
  (D.wires (List.ofFn z)).getD w false

private theorem wval_input (N : ℕ) (D : Circuit) (z : Fin N → Bool) (i : ℕ) (hi : i < N) :
    wval N D z i = z ⟨i, hi⟩ := by
  change (scan (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
    D.gates (List.ofFn z)).getD i false = _
  rw [scan_earlier _ _ _ _ _ (by simpa using hi),
    List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private theorem wval_ge (N : ℕ) (D : Circuit) (z : Fin N → Bool) (w : ℕ)
    (hw : N + D.size ≤ w) : wval N D z w = false := by
  change (scan (fun a g => g.op.eval (g.inputs.map fun idx => a.getD idx false))
    D.gates (List.ofFn z)).getD w false = false
  apply List.getD_eq_default
  rw [scan_length, List.length_ofFn]
  exact hw

private theorem gateAt_eq (D : Circuit) (j : ℕ) (hj : j < D.size) :
    gateAt D j = D.gates[j] := by
  change D.gates.getD j ⟨GateOp.or, []⟩ = D.gates[j]
  exact List.getD_eq_getElem _ _ hj

private theorem ao2_gate_spec (N : ℕ) (D : Circuit) (hAO : IsAO2 N D)
    (j : ℕ) (hj : j < D.size) :
    ((gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or) ∧
    (gateAt D j).inputs = [opnd D j 0, opnd D j 1] ∧
    opnd D j 0 < N + j ∧ opnd D j 1 < N + j ∧
    ∀ z : Fin N → Bool,
      wval N D z (N + j) =
        (gateAt D j).op.eval [wval N D z (opnd D j 0), wval N D z (opnd D j 1)] := by
  have hmem : D.gates[j] ∈ D.gates := List.getElem_mem hj
  have hga : gateAt D j = D.gates[j] := gateAt_eq D j hj
  have hop : (gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or := by
    rw [hga]
    exact hAO.1 D.gates[j] hmem
  have hlen : (gateAt D j).inputs.length = 2 := by
    rw [hga]
    exact hAO.2.2 D.gates[j] hmem
  rcases hinp : (gateAt D j).inputs with _ | ⟨a, rest⟩
  · rw [hinp] at hlen; simp at hlen
  · rcases rest with _ | ⟨b, rest2⟩
    · rw [hinp] at hlen; simp at hlen
    · rcases rest2 with _ | ⟨c, rest3⟩
      · have ha0 : opnd D j 0 = a := by simp [opnd, hinp]
        have hb0 : opnd D j 1 = b := by simp [opnd, hinp]
        have ha_lt : a < N + j := hAO.2.1 j hj a (by rw [hinp]; simp)
        have hb_lt : b < N + j := hAO.2.1 j hj b (by rw [hinp]; simp)
        refine ⟨hop, by rw [ha0, hb0], by rwa [ha0], by rwa [hb0], fun z => ?_⟩
        rw [ha0, hb0]
        change (scan (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
          D.gates (List.ofFn z)).getD (N + j) false =
          (gateAt D j).op.eval
            [(scan (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
              D.gates (List.ofFn z)).getD a false,
             (scan (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
              D.gates (List.ofFn z)).getD b false]
        have hlen_in : (List.ofFn z).length = N := List.length_ofFn
        have hstep := scan_at_gate
          (fun w g => g.op.eval (g.inputs.map fun idx => w.getD idx false))
          D.gates (List.ofFn z) false j hj a b
          (by rw [hlen_in]; exact ha_lt) (by rw [hlen_in]; exact hb_lt)
          (fun x y => (gateAt D j).op.eval [x, y])
          (fun w => by rw [← hga, hinp]; rfl)
        simpa only [hlen_in] using hstep
      · rw [hinp] at hlen; simp at hlen

private theorem eval_and (x y : Bool) : GateOp.and.eval [x, y] = (x && y) := by
  cases x <;> cases y <;> rfl

private theorem eval_or (x y : Bool) : GateOp.or.eval [x, y] = (x || y) := by
  cases x <;> cases y <;> rfl

private theorem splitval {op : GateOp} (hop : op=.and ∨ op=.or)
    {a b c d : Bool} (ht : op.eval [a,b]=true) (hf : op.eval [c,d]=false) :
    (a=true ∧ c=false) ∨ (b=true ∧ d=false) := by
  rcases hop with rfl|rfl <;> cases a <;> cases b <;> cases c <;> cases d <;> simp_all [GateOp.eval]

theorem solve (n : Nat) (C : Circuit) (ao : IsAO2 n C) (s t : Fin n) (j : Nat)
    (hand : PEqualNP.ReadTwo.isAnd C j) :
    let W := fun k : Fin n => wval n C (PEqualNP.ReadTwo.indW n {k.val})
    let pure := fun w => W s w=true ∧ W t w=false
    let edge := fun a b => n≤b ∧ a ∈ (gateAt C (b-n)).inputs ∧ pure a ∧ pure b
    W s (n+j) = true → (∀ a ∈ (gateAt C j).inputs,W t a=false) →
    ∀ a ∈ (gateAt C j).inputs,pure a ∧ Relation.ReflTransGen edge s.val a := by
  let W := fun k : Fin n => wval n C (PEqualNP.ReadTwo.indW n {k.val})
  let pure := fun w => W s w=true ∧ W t w=false
  let edge := fun a b => n≤b ∧ a ∈ (gateAt C (b-n)).inputs ∧ pure a ∧ pure b
  have path (w : Nat) (hw : pure w) : Relation.ReflTransGen edge s.val w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases small : w<n
      · have start := hw.1
        change wval n C _ w = true at start
        rw [wval_input n C _ _ small] at start
        have eq : w = s.val := by simpa [PEqualNP.ReadTwo.indW] using start
        rw [eq]
      · have lt : w<n+C.size := by
          by_contra! big
          have h0 := wval_ge n C (PEqualNP.ReadTwo.indW n {s.val}) w big
          exact Bool.false_ne_true (h0.symm.trans hw.1)
        let k := w-n
        have rel : n+k=w := by dsimp [k];omega
        obtain ⟨hop,inputs,al,bl,eval⟩ := ao2_gate_spec n C ao k (by dsimp [k];omega)
        have evalW (z : Fin n) : W z w = (gateAt C k).op.eval [W z (opnd C k 0),W z (opnd C k 1)] := by
          rw [←rel];exact eval _
        have sa := hw.1
        have tb := hw.2
        rw [evalW] at sa tb
        rcases splitval hop sa tb with left|right
        · apply (ih (opnd C k 0) (by omega) left).tail
          exact ⟨by omega, by rw [←show k=w-n from rfl,inputs];simp,left,hw⟩
        · apply (ih (opnd C k 1) (by omega) right).tail
          exact ⟨by omega, by rw [←show k=w-n from rfl,inputs];simp,right,hw⟩
  change W s (n+j) = true → (∀ a ∈ (gateAt C j).inputs,W t a=false) → ∀ a ∈ (gateAt C j).inputs,pure a ∧ Relation.ReflTransGen edge s.val a
  intro yes inactive a ha
  obtain ⟨_,inputs,_,_,eval⟩ := ao2_gate_spec n C ao j hand.1
  have eq := eval (PEqualNP.ReadTwo.indW n {s.val})
  change W s (n+j) = _ at eq
  rw [eq,hand.2,eval_and] at yes
  have both := Bool.and_eq_true_iff.mp yes
  have hp : pure a := by
    refine ⟨?_,inactive a ha⟩
    rw [inputs] at ha
    rcases List.mem_cons.mp ha with h|h
    · exact h ▸ both.1
    · exact (List.mem_singleton.mp h) ▸ both.2
  exact ⟨hp,path a hp⟩

end PEqualNP.Outside.L_meta_18205

theorem PEqualNP.Outside.L_meta_18205 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 x1 x2 →     ∀ (x4 x5 : Fin x1) (x6 : ℕ),       PEqualNP.ReadTwo.isAnd x2 x6 →         have x8 : Fin x1 → ℕ → Bool := fun (x8 : Fin x1) => PEqualNP.ReadTwo.wval x2 (PEqualNP.ReadTwo.indW x1 {↑x8});         have x9 : ℕ → Prop := fun (x9 : ℕ) => x8 x4 x9 = Bool.true ∧ x8 x5 x9 = Bool.false;         have x10 : ℕ → ℕ → Prop := fun (x10 x11 : ℕ) => x1 ≤ x11 ∧ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x11 - x1)).inputs ∧ x9 x10 ∧ x9 x11;         x8 x4 (x1 + x6) = Bool.true → (∀ x12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x8 x5 x12 = Bool.false) → ∀ x13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs, x9 x13 ∧ Relation.ReflTransGen x10 (↑x4) x13 := PEqualNP.Outside.L_meta_18205.solve
