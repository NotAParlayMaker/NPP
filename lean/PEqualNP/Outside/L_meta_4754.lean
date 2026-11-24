import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_4754

-- The new prefix writes wire 17. Old gate outputs start at 16 and now start at 18.
def route (i : Nat) : Nat :=
  if i = 10 then 17 else if i = 15 then 16 else if i < 16 then i else i + 2

def rename (g : Gate) : Gate := ⟨g.op,g.inputs.map route⟩
def mergeGate : Gate := ⟨.or,[10,15]⟩
def lifted (C : Circuit) : Circuit := ⟨mergeGate :: C.gates.map rename,route C.output⟩
def input (x : Fin 17 → Bool) (i : Fin 16) :=
  if i=10 then x 10 || x 15 else if i=15 then x 16 else x (Fin.ofNat 17 i.val)

private def value (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
private def run (gs : List Gate) (w : List Bool) := gs.foldl (fun s g => s++[value g s]) w

private theorem appended (w : List Bool) (b : Bool) (i : Nat) :
    (w++[b]).getD i false = if i=w.length then b else w.getD i false := by
  rcases lt_trichotomy i w.length with h|h|h
  · rw [List.getD_append _ _ _ _ h,ite_eq_right (ne_of_lt h)]
  · subst i;simp
  · rw [ite_eq_right (ne_of_gt h),List.getD_eq_default _ _ (by simp;omega),
      List.getD_eq_default _ _ (by omega)]

-- The invariant includes out-of-range wires, since an output may point past the end.
private theorem simulate (gs : List Gate) (old new : List Bool) (base : 16≤old.length)
    (size : new.length=old.length+2)
    (agree : ∀ i, new.getD (route i) false=old.getD i false) (i : Nat) :
    (run (gs.map rename) new).getD (route i) false=(run gs old).getD i false := by
  induction gs generalizing old new with
  | nil => exact agree i
  | cons g gs ih =>
    have same : value (rename g) new=value g old := by
      unfold value rename;simp only [List.map_map]
      apply congrArg g.op.eval
      apply List.map_congr_left;intro j _;exact agree j
    apply ih (old:=old++[value g old]) (new:=new++[value (rename g) new])
      (by simp;omega) (by simp [size])
    intro j
    have hit : route j=new.length ↔ j=old.length := by unfold route;split_ifs <;> omega
    rw [appended,appended]
    by_cases h : j=old.length
    · rw [ite_eq_left h,ite_eq_left (hit.mpr h),same]
    · rw [ite_eq_right h,ite_eq_right (fun e => h (hit.mp e)),agree]

theorem computes (C : Circuit) (x : Fin 17 → Bool) :
    circuitFun 17 (lifted C) x=circuitFun 16 C (input x) := by
  have mergedBit : value mergeGate (List.ofFn x)= (x 10 || x 15) := by
    simp [value,mergeGate,GateOp.eval,List.getD_eq_getElem?_getD]
  change (run (C.gates.map rename) (List.ofFn x++[value mergeGate (List.ofFn x)])).getD _ false=_
  rw [mergedBit]
  apply simulate _ (List.ofFn (input x)) _ (by simp) (by simp)
  intro i
  by_cases hi : i<16
  · let j : Fin 16 := ⟨i,hi⟩
    change _=(List.ofFn (input x)).getD j.val false
    change (List.ofFn x++[x 10 || x 15]).getD (route j.val) false=_
    generalize hj : j=t
    fin_cases t <;> rfl
  · have whereTo : route i=i+2 := by unfold route;split_ifs <;> omega
    rw [whereTo,List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

theorem monotone (C : Circuit) (valid : Monotone2 C) : Monotone2 (lifted C) := by
  intro g h
  rcases List.mem_cons.mp h with rfl|h
  · exact ⟨Or.inr rfl,by decide⟩
  · obtain ⟨old,mem,rfl⟩ := List.mem_map.mp h
    simpa [rename] using valid old mem

theorem reads (C : Circuit) (back : ReadsBack 16 C) : ReadsBack 17 (lifted C) := by
  intro i hi
  cases i with
  | zero =>
    change ∀ j∈([10,15] : List Nat), j<17+0
    decide
  | succ k =>
    have hk : k<C.gates.length := by simpa [lifted] using hi
    have atNew : gateAt (lifted C) (k+1)=rename C.gates[k] := by
      simp [gateAt,lifted,List.getD_eq_getElem?_getD,hk]
    have atOld : gateAt C k=C.gates[k] := by simp [gateAt,List.getD_eq_getElem?_getD,hk]
    rw [atNew];intro j hj
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hj
    have bound := back k hk u (by simpa [atOld] using hu)
    unfold route;split_ifs <;> omega

end PEqualNP.Outside.L_meta_4754

theorem PEqualNP.Outside.L_meta_4754 :
    ∀ C : Circuit, Monotone2 C → ReadsBack 16 C → ∃ D : Circuit,
      Monotone2 D ∧ ReadsBack 17 D ∧ D.size≤C.size+1 ∧ ∀ x : Fin 17 → Bool,
        circuitFun 17 D x=circuitFun 16 C (fun i => if i=10 then x 10 || x 15
          else if i=15 then x 16 else x (Fin.ofNat 17 i.val)) := by
  intro C m r
  exact ⟨L_meta_4754.lifted C,L_meta_4754.monotone C m,L_meta_4754.reads C r,
    by simp [L_meta_4754.lifted,Circuit.size],L_meta_4754.computes C⟩
