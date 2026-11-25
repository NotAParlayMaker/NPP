import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_9018

def run (gs : List Gate) (x : List Bool) :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) x

lemma length_run (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (x ++ [_])).length = _
    rw [ih]
    simp
    omega

def addr {L : ℕ} (w : Fin L → ℕ) (base limit i : ℕ) : ℕ :=
  if h : i < L then
    let j := w ⟨i,h⟩
    if j < base then j else base + limit
  else base + (i-L)

def gate {L : ℕ} (w : Fin L → ℕ) (base limit : ℕ) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (addr w base limit)⟩

def inputs {L : ℕ} (v : List Bool) (w : Fin L → ℕ) := List.ofFn (fun j => v.getD (w j) false)

lemma read {L : ℕ} (v e : List Bool) (w : Fin L → ℕ) (limit : ℕ) (he : e.length ≤ limit) (i : ℕ) :
    (v ++ e).getD (addr w v.length limit i) false = (inputs v w ++ e).getD i false := by
  by_cases h : i < L
  · rw [addr,dite_eq_left h,List.getD_append (inputs v w) e false i (by simpa [inputs] using h)]
    let j := w ⟨i,h⟩
    have val : (inputs v w).getD i false = v.getD j false := by
      simp [inputs,j,List.getD_eq_getElem?_getD,h]
    rw [val]
    change (v++e).getD (if j<v.length then j else v.length+limit) false = v.getD j false
    by_cases bound : j < v.length
    · rw [ite_eq_left bound,List.getD_append _ _ _ _ bound]
    · rw [ite_eq_right bound,List.getD_eq_default (v++e) false (by simp;omega),List.getD_eq_default v false (by omega)]
  · rw [addr,dite_eq_right h,List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by simp [inputs];omega)]
    simp [inputs]

lemma simulate {L : ℕ} (v : List Bool) (w : Fin L → ℕ) (limit : ℕ) (gs : List Gate) (e : List Bool)
    (bound : e.length + gs.length ≤ limit) :
    ∃u : List Bool,u.length ≤ limit ∧ run (gs.map (gate w v.length limit)) (v++e) = v++u ∧
      run gs (inputs v w++e) = inputs v w++u := by
  induction gs generalizing e with
  | nil => exact ⟨e,by simpa using bound,rfl,rfl⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => (inputs v w++e).getD i false)
    let e' := e++[b]
    have maps : (gate w v.length limit g).inputs.map (fun i=>(v++e).getD i false) =
        g.inputs.map (fun i=>(inputs v w++e).getD i false) := by
      simp only [gate,List.map_map,Function.comp_def,read v e w limit (by omega)]
    have left : (v++e)++[g.op.eval ((gate w v.length limit g).inputs.map (fun i=>(v++e).getD i false))]=v++e' := by
      rw [maps];simp [e',b,List.append_assoc]
    have right : (inputs v w++e)++[b]=inputs v w++e' := by simp [e',List.append_assoc]
    obtain ⟨u,ub,real,virt⟩:=ih e' (by simp [e'] at *;omega)
    refine ⟨u,ub,?_,?_⟩
    · change run _ ((v++e)++[g.op.eval _])=_
      rw [left];exact real
    · change run _ ((inputs v w++e)++[b])=_
      rw [right];exact virt

end PEqualNP.Outside.L_meta_9018

theorem PEqualNP.Outside.L_meta_9018 : ∀ (N L : ℕ) (D : Set (List Bool)) (P : List PEqualNP.CircuitLowerBounds.Gate) (w : Fin L → ℕ) (g : Fin L → List Bool → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ x ∈ D, x.length = N) → PEqualNP.MetaComplexity.Monotone2 (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x ∈ D, ∀ j, ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w j) false = g j x) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ P.length + C.size ∧ ∀ x ∈ D, C'.eval x = C.eval (List.ofFn fun j => g j x) := by
  intro N L D P w g C lens first second vals
  let base:=N+P.length
  let limit:=C.gates.length
  let R : Circuit:=⟨P++C.gates.map (PEqualNP.Outside.L_meta_9018.gate w base limit),PEqualNP.Outside.L_meta_9018.addr w base limit C.output⟩
  refine ⟨R,?_,?_,?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with left|right
    · exact first z left
    · obtain ⟨old,mem,rfl⟩:=List.mem_map.mp right
      simpa only [PEqualNP.Outside.L_meta_9018.gate,List.length_map] using second old mem
  · simp [R,Circuit.size]
  · intro x hx
    let v:=PEqualNP.Outside.L_meta_9018.run P x
    have vl : v.length=base:=by simp [v,base,PEqualNP.Outside.L_meta_9018.length_run,lens x hx]
    have input : PEqualNP.Outside.L_meta_9018.inputs v w=List.ofFn (fun j=>g j x):=by
      apply congrArg List.ofFn;funext j;exact vals x hx j
    obtain ⟨u,sz,real,virt⟩:=PEqualNP.Outside.L_meta_9018.simulate v w limit C.gates [] (by simp [limit])
    simp only [List.append_nil] at real virt
    change (PEqualNP.Outside.L_meta_9018.run (P++C.gates.map _) x).getD _ false = (PEqualNP.Outside.L_meta_9018.run C.gates _).getD _ false
    rw [show PEqualNP.Outside.L_meta_9018.run (P++C.gates.map (PEqualNP.Outside.L_meta_9018.gate w base limit)) x =
      PEqualNP.Outside.L_meta_9018.run (C.gates.map (PEqualNP.Outside.L_meta_9018.gate w base limit)) v from List.foldl_append ..,←vl,real,
      ←input,virt]
    simpa only [R,←vl] using PEqualNP.Outside.L_meta_9018.read v u w limit sz C.output
