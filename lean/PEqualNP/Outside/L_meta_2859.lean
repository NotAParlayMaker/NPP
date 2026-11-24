import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2859
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

lemma redirect_low (n m p i : ℕ) (hi : i<n+m) : eraseRedirect n m p i=i := by
  simp [eraseRedirect,show i≠n+m by omega,show ¬ (n + m < i) by omega]

lemma redirect_bound (n m p i j : ℕ) (hp : p<n+m) (hmj : m≤j)
    (hi : i<n+(j+1)) : eraseRedirect n m p i<n+j := by
  unfold eraseRedirect
  split_ifs <;> omega

lemma erased_length {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m<C.gates.length) :
    (eraseGate n C m p).gates.length+1=C.gates.length := by
  simp [eraseGate,hm,Nat.min_eq_left hm.le]
  omega

lemma erased_gate {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m<C.gates.length)
    (j : ℕ) (hj : j<(eraseGate n C m p).gates.length) :
    gateAt (eraseGate n C m p) j = if j < m then gateAt C j else
      ⟨(gateAt C (j+1)).op,(gateAt C (j+1)).inputs.map (eraseRedirect n m p)⟩ := by
  have hlen := erased_length (n:=n) (p:=p) hm
  rw [gateAt_eq hj]
  by_cases hjm : j < m
  · rw [if_pos hjm]
    have hjC : j<C.gates.length := by omega
    rw [gateAt_eq hjC]
    simp [eraseGate,hm,List.getElem_append,hjm,Nat.min_eq_left hm.le]
  · rw [if_neg hjm]
    have hjC : j+1<C.gates.length := by omega
    rw [gateAt_eq hjC]
    simp only [eraseGate,if_pos hm]
    rw [List.getElem_append_right (by simp [Nat.min_eq_left hm.le]; omega)]
    simp only [List.getElem_map,List.getElem_drop,List.length_take,Nat.min_eq_left hm.le]
    have heq : m+1+(j-m)=j+1 := by omega
    simp only [heq]


end PEqualNP.Outside.L_meta_2859
open PEqualNP.Outside.L_meta_2859 PEqualNP.Outside.L_meta_2859.Mono PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_2859 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → p < n + m → PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + m) false → (PEqualNP.CircuitMoves.eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  classical
  intro n C m p hC hb hm hp
  let D := eraseGate n C m p
  let r := eraseRedirect n m p
  have hlen : D.gates.length+1=C.gates.length := erased_length hm
  have hDC : PEqualNP.MetaComplexity.Monotone2 D := by
    intro g hg
    change g ∈ (eraseGate n C m p).gates at hg
    simp only [eraseGate,if_pos hm,List.mem_append,List.mem_map] at hg
    rcases hg with hpre | ⟨a,ha,rfl⟩
    · exact hC g (List.mem_of_mem_take hpre)
    · have h := hC a (List.mem_of_mem_drop ha)
      simpa using h
  have hDb : ReadsBack n D := by
    intro j hj i hi
    rw [erased_gate hm j hj] at hi
    split_ifs at hi with hjm
    · exact hb j (by omega) i hi
    · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
      exact redirect_bound n m p k j hp (by omega) (hb (j+1) (by omega) k hk)
  have rg (j : ℕ) (hj : j<C.gates.length) (hne : j≠m) :
      ∃ k, k<D.gates.length ∧ r (n+j)=n+k ∧
        gateAt D k = ⟨(gateAt C j).op,(gateAt C j).inputs.map r⟩ := by
    by_cases hjm : j < m
    · refine ⟨j,by omega,redirect_low n m p (n+j) (by omega),?_⟩
      rw [erased_gate hm j (by change j < D.gates.length; omega),if_pos hjm]
      have hmap : (gateAt C j).inputs.map r = (gateAt C j).inputs := by
        calc (gateAt C j).inputs.map r = (gateAt C j).inputs.map id := by
               apply List.map_congr_left
               intro i hi
               exact redirect_low n m p i (by have h := hb j hj i hi; omega)
             _ = _ := List.map_id _
      rw [hmap]
    · have hmj : m < j := by omega
      refine ⟨j-1,by omega,?_,?_⟩
      · dsimp [r,eraseRedirect]
        simp only [show n+j≠n+m by omega,if_false,show n+m<n+j by omega,if_true]
        omega
      · rw [erased_gate hm (j-1) (by change j-1 < D.gates.length; omega),if_neg (by omega)]
        simp only [show j-1+1=j by omega]
        rfl
  refine ⟨hDC,hDb,?_,?_⟩
  · exact hlen
  · intro x hsem
    have eqv : ∀ i, value D x (r i)=value C x i := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        by_cases hin : i<n
        · rw [show r i=i from redirect_low n m p i (by omega)]
          exact (input_value D x ⟨i,hin⟩).trans (input_value C x ⟨i,hin⟩).symm
        by_cases him : i=n+m
        · subst i
          have hpp := ih p hp
          rw [show r p=p from redirect_low n m p p hp] at hpp
          change value C x p=value C x (n+m) at hsem
          simpa [r,eraseRedirect] using hpp.trans hsem
        by_cases hib : i<n+C.gates.length
        · let j := i-n
          have hj : j<C.gates.length := by dsimp [j]; omega
          have hij : i=n+j := by dsimp [j]; omega
          have hjm : j≠m := by omega
          obtain ⟨k,hk,hr,hgate⟩ := rg j hj hjm
          rw [hij,hr,full_gate D hDb x k hk,full_gate C hb x j hj,hgate]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact ih a (by have h := hb j hj a ha; omega)
        · have hiold : n + C.size ≤ i := by unfold Circuit.size; omega
          have hinew : n + D.size ≤ r i := by
            dsimp [r,eraseRedirect]
            unfold Circuit.size
            split_ifs <;> omega
          rw [missing_value D x (r i) hinew,missing_value C x i hiold]
    change value D x D.output=value C x C.output
    have hout : D.output=r C.output := by simp [D,eraseGate,hm,r]
    rw [hout]
    exact eqv C.output
