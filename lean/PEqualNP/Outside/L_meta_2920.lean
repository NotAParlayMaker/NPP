import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2920
namespace Mono

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

end Mono
open Mono PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j<C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt,List.getD_eq_getElem?_getD,hj]


lemma any_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    value C x (n+j) = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => if i < n+j then value C x i else false) := by
  have hv := gate_value C x (n+j) (by omega) (by unfold Circuit.size; omega)
  simpa only [Nat.add_sub_cancel_left,gateAt_eq hj] using hv

lemma gate_of_get {C : Circuit} {j : ℕ} {g : Gate} (hg : C.gates[j]?=some g) :
    gateAt C j=g := by simp [gateAt,List.getD_eq_getElem?_getD,hg]

lemma pair_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (op : GateOp) (a b : ℕ)
    (hg : gateAt C j=⟨op,[a,b]⟩) (ha : a < n+j) (hb : b < n+j) :
    value C x (n+j)=op.eval [value C x a,value C x b] := by
  rw [any_gate C x j hj,hg]
  simp only [List.map_cons,List.map_nil,if_pos ha,if_pos hb]

lemma pair_comm (op : GateOp) (hop : op=GateOp.and ∨ op=GateOp.or) (a b : Bool) :
    op.eval [a,b]=op.eval [b,a] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> rfl


end PEqualNP.Outside.L_meta_2920
open PEqualNP.Outside.L_meta_2920 PEqualNP.Outside.L_meta_2920.Mono PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_2920 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j is iv iw a b c z : ℕ)
    (op1 op2 : PEqualNP.CircuitLowerBounds.GateOp),
  ((op1 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.or) ∨
    (op1 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.and)) →
  C.gates[is]? = some { op := op2, inputs := [a, b] } →
  C.gates[iv]? = some { op := op2, inputs := [a, c] } →
  C.gates[iw]? = some { op := op1, inputs := [n + iv, z] } →
  (C.gates[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
    C.gates[j]? = some { op := op1, inputs := [n + iw, n + is] }) →
  is < j → iv < iw → iw < j →
  a < n + is → b < n + is → a < n + iv → b < n + iv → c < n + iv →
  z < n + iw → z ≠ n + iv →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ iw → n + iv ∉ g.inputs) →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ j → n + iw ∉ g.inputs) →
  C.output ≠ n + iv → C.output ≠ n + iw →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := ((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
            { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
      { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] }).length =
    C.gates.length := by
  intro n C j is iv iw a b c z op1 op2 hops hs hv hw hjg hsj hvw hwj
    has hbs hav hbv hcv hzw hzv hreadv hreadw houtv houtw
  have hj : j < C.gates.length := by
    rcases hjg with h | h <;> exact (List.getElem_of_getElem? h).1
  have hiv : iv < C.gates.length := by omega
  have hiw : iw < C.gates.length := by omega
  have his : is < C.gates.length := by omega
  have hop1 : op1=GateOp.and ∨ op1=GateOp.or := hops.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  let D : Circuit := ⟨((C.gates.set iv ⟨op1,[b,c]⟩).set iw ⟨op2,[a,n+iv]⟩).set j
    ⟨op1,[n+iw,z]⟩,C.output⟩
  have hlen : D.gates.length=C.gates.length := by simp [D]
  have dg (k : ℕ) (hk : k < C.gates.length) : gateAt D k =
      if j=k then ⟨op1,[n+iw,z]⟩ else if iw=k then ⟨op2,[a,n+iv]⟩ else
      if iv=k then ⟨op1,[b,c]⟩ else gateAt C k := by
    rw [gateAt_eq (by simpa only [hlen] using hk)]
    simp only [D,List.getElem_set]
    split_ifs <;> simp [gateAt_eq hk]
  refine ⟨?_,by simp⟩
  funext x
  have eqv : ∀ w, w≠n+iv → w≠n+iw → value D x w=value C x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hwv hww
      by_cases hwn : w < n
      · exact (input_value D x ⟨w,hwn⟩).trans (input_value C x ⟨w,hwn⟩).symm
      by_cases hwb : w < n+C.gates.length
      · let k := w-n
        have hk : k < C.gates.length := by dsimp [k]; omega
        have hwnk : w=n+k := by dsimp [k]; omega
        by_cases hkj : k=j
        · have hwj' : w=n+j := by omega
          have haEq := ih a (by omega) (by omega) (by omega)
          have hbEq := ih b (by omega) (by omega) (by omega)
          have hcEq := ih c (by omega) (by omega) (by omega)
          have hzEq := ih z (by omega) hzv (by omega)
          have oldS := pair_value C x is his op2 a b (gate_of_get hs) has hbs
          have oldV := pair_value C x iv hiv op2 a c (gate_of_get hv) hav hcv
          have oldW := pair_value C x iw hiw op1 (n+iv) z (gate_of_get hw) (by omega) hzw
          have oldJ : value C x (n+j)=op1.eval [value C x (n+is),value C x (n+iw)] := by
            rcases hjg with h | h
            · exact pair_value C x j hj op1 (n+is) (n+iw) (gate_of_get h) (by omega) (by omega)
            · exact (pair_value C x j hj op1 (n+iw) (n+is) (gate_of_get h) (by omega) (by omega)).trans
                (pair_comm op1 hop1 _ _)
          have newV : value D x (n+iv)=op1.eval [value C x b,value C x c] := by
            have hg : gateAt D iv=⟨op1,[b,c]⟩ := by
              rw [dg iv hiv]
              simp [show j≠iv by omega,show iw≠iv by omega]
            rw [pair_value D x iv (by omega) op1 b c hg hbv hcv,hbEq,hcEq]
          have newW : value D x (n+iw)=op2.eval [value C x a,value D x (n+iv)] := by
            have hg : gateAt D iw=⟨op2,[a,n+iv]⟩ := by
              rw [dg iw hiw]
              simp [show j≠iw by omega]
            rw [pair_value D x iw (by omega) op2 a (n+iv) hg (by omega) (by omega),haEq]
          have newJ : value D x (n+j)=op1.eval [value D x (n+iw),value C x z] := by
            have hg : gateAt D j=⟨op1,[n+iw,z]⟩ := by rw [dg j hj]; simp
            rw [pair_value D x j (by omega) op1 (n+iw) z hg (by omega) (by omega),hzEq]
          rw [hwj',newJ,oldJ,newW,newV,oldS,oldW,oldV]
          rcases hops with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
            cases value C x a <;> cases value C x b <;> cases value C x c <;>
            cases value C x z <;> rfl
        · have hkiw : k≠iw := by omega
          have hkiv : k≠iv := by omega
          rw [hwnk,any_gate D x k (by omega),any_gate C x k hk,dg k hk,
            if_neg (Ne.symm hkj),if_neg (Ne.symm hkiw),if_neg (Ne.symm hkiv)]
          congr 1
          apply List.map_congr_left
          intro i hi
          by_cases hir : i < n+k
          · rw [if_pos hir,if_pos hir]
            have hgk : C.gates[k]?=some (gateAt C k) := by simp [gateAt_eq hk]
            have hiv' : i≠n+iv := by intro heq; subst i; exact hreadv k _ hgk hkiw hi
            have hiw' : i≠n+iw := by intro heq; subst i; exact hreadw k _ hgk hkj hi
            exact ih i (by omega) hiv' hiw'
          · simp only [if_neg hir]
      · rw [missing_value D x w (by unfold Circuit.size; omega),
          missing_value C x w (by unfold Circuit.size; omega)]
  exact eqv C.output houtv houtw
