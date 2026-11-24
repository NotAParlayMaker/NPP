import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2860
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

lemma full_gate {n : ℕ} (C : Circuit) (hb : ReadsBack n C) (x : Fin n → Bool)
    (j : ℕ) (hj : j<C.gates.length) :
    value C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)) := by
  have hv := gate_value C x (n+j) (by omega) (by unfold Circuit.size; omega)
  simp only [Nat.add_sub_cancel_left] at hv
  rw [gateAt_eq hj]
  rw [hv]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt := hb j hj i (by simpa only [gateAt_eq hj] using hi)
  simp [hlt]


end PEqualNP.Outside.L_meta_2860
open PEqualNP.Outside.L_meta_2860 PEqualNP.Outside.L_meta_2860.Mono PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_2860 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m u v z a b : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → n ≤ u → u < v → v < n + m → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs = [u, v] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (u - n)).inputs = [z, a] → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt C (v - n)).inputs = [z, b] → (∀ j < C.gates.length, j ≠ m → v ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) → C.output ≠ v → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set (v - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩).set m ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [z, v]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m u v z a b hb hm hnu huv hvm hmo hmi huo hui hvo hvi hread hout
  let D : Circuit := ⟨(C.gates.set (v-n) ⟨GateOp.and,[a,b]⟩).set m ⟨GateOp.or,[z,v]⟩,C.output⟩
  have hlen : D.gates.length=C.gates.length := by simp [D]
  have huj : u-n < C.gates.length := by omega
  have hvj : v-n < C.gates.length := by omega
  have hun : n+(u-n)=u := by omega
  have hvn : n+(v-n)=v := by omega
  have hza : z < u ∧ a < u := by
    constructor
    · have h := hb (u-n) huj z (by simp [hui]); omega
    · have h := hb (u-n) huj a (by simp [hui]); omega
  have hzb : z < v ∧ b < v := by
    constructor
    · have h := hb (v-n) hvj z (by simp [hvi]); omega
    · have h := hb (v-n) hvj b (by simp [hvi]); omega
  have dg (j : ℕ) (hj : j < C.gates.length) : gateAt D j =
      if m=j then ⟨GateOp.or,[z,v]⟩ else
      if v-n=j then ⟨GateOp.and,[a,b]⟩ else gateAt C j := by
    rw [gateAt_eq (by simpa only [hlen] using hj)]
    simp only [D,List.getElem_set]
    split_ifs <;> simp [gateAt_eq hj]
  have hDb : ReadsBack n D := by
    intro j hj i hi
    have hjC : j < C.gates.length := by omega
    rw [dg j hjC] at hi
    split_ifs at hi with hjm hjv
    · subst j
      have hi' : i=z ∨ i=v := by simpa using hi
      rcases hi' with rfl | rfl <;> omega
    · have hi' : i=a ∨ i=b := by simpa using hi
      rcases hi' with rfl | rfl <;> omega
    · exact hb j hjC i hi
  change ReadsBack n D ∧ D.size=C.size ∧ _
  refine ⟨hDb,hlen,?_⟩
  intro x
  have eqv : ∀ w, w≠v → value D x w=value C x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hwv
      by_cases hwn : w < n
      · exact (input_value D x ⟨w,hwn⟩).trans (input_value C x ⟨w,hwn⟩).symm
      by_cases hwb : w < n+C.gates.length
      · let j := w-n
        have hj : j < C.gates.length := by dsimp [j]; omega
        have hwnj : w=n+j := by dsimp [j]; omega
        by_cases hjm : j=m
        · have hwm : w=n+m := by omega
          have hzEq := ih z (by omega) (by omega)
          have haEq := ih a (by omega) (by omega)
          have hbEq := ih b (by omega) (by omega)
          have holdU : value C x u=(value C x z || value C x a) := by
            rw [← hun,full_gate C hb x (u-n) huj,huo,hui]
            simp [GateOp.eval]
          have holdV : value C x v=(value C x z || value C x b) := by
            rw [← hvn,full_gate C hb x (v-n) hvj,hvo,hvi]
            simp [GateOp.eval]
          have hnewV : value D x v=(value C x a && value C x b) := by
            rw [← hvn,full_gate D hDb x (v-n) (by omega),dg (v-n) hvj]
            simp only [show m≠v-n by omega,if_false,if_pos rfl]
            simp [GateOp.eval,haEq,hbEq]
          rw [hwm,full_gate D hDb x m (by omega),full_gate C hb x m hm,dg m hm]
          simp only [ite_true,hmo,hmi]
          simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
            List.all_cons,List.all_nil,id_eq,Bool.or_false,Bool.and_true]
          rw [hzEq,hnewV,holdU,holdV]
          cases value C x z <;> cases value C x a <;> cases value C x b <;> rfl
        · have hjv : v-n≠j := by omega
          rw [hwnj,full_gate D hDb x j (by omega),full_gate C hb x j hj,dg j hj,
            if_neg (Ne.symm hjm),if_neg hjv]
          congr 1
          apply List.map_congr_left
          intro i hi
          have hlt := hb j hj i hi
          have hne : i≠v := by intro heq; subst i; exact hread j hj hjm hi
          exact ih i (by omega) hne
      · have hcsize : n+C.size ≤ w := by unfold Circuit.size; omega
        have hdsize : n+D.size ≤ w := by unfold Circuit.size; omega
        rw [missing_value D x w hdsize,missing_value C x w hcsize]
  exact eqv C.output hout
