import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1678_999
    (small : let F := fun (x : Fin 9→Bool) => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun n => x (Fin.ofNat 9 (n/9)) && x (Fin.ofNat 9 (n % 9)))
  ∀ D : Circuit, FanInTwo D → D.size≤14 → D.gates.countP (fun (g : Gate) => @GateOp.rec (fun _ => Bool) false false true (fun _ => false) false g.op)≤1 → (∀ x : Fin 9→Bool, (List.ofFn x).count true≤3 → D.eval (List.ofFn x++[x 4 || x 6])=F x) → False)
    (many : let F := fun (x : Fin 9→Bool) => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun n => x (Fin.ofNat 9 (n/9)) && x (Fin.ofNat 9 (n % 9)))
  ∀ D : Circuit, FanInTwo D → D.gates.countP (fun (g : Gate) => @GateOp.rec (fun _ => Bool) true true false (fun _ => true) true g.op)≤12 → (∀ x : Fin 9→Bool, D.eval (List.ofFn x++[x 4 || x 6])=F x) → False) :
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  dsimp only at small many
  intro C fan first eqF
  let nnot := fun (g : Gate) => @GateOp.rec (fun _ => Bool) false false true (fun _ => false) false g.op
  have fitted (x : Fin 9→Bool) : C.eval (List.ofFn x) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x := congrFun eqF x
  have agree : ∀ x : Fin 9→Bool, (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x = (fun (x : Fin 9→Bool) => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun n => x (Fin.ofNat 9 (n/9)) && x (Fin.ofNat 9 (n % 9)))) x := by decide +kernel
  by_contra! lt
  obtain ⟨l,o⟩ := C
  dsimp only at *
  cases l with
  | nil =>
    have fail := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at fail
    have hd : (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = false := by decide
    exact Bool.noConfusion (hd.symm.trans fail)
  | cons g gs =>
    let D : Circuit := ⟨gs,o⟩
    let step := fun (w : List Bool) (a : Gate) =>
      w ++ [a.op.eval (a.inputs.map (fun j => w.getD j false))]
    have pref (l : List Gate) (w : List Bool) : ∃ t, l.foldl step w = w ++ t := by
      induction l generalizing w with
      | nil => exact ⟨[],(List.append_nil w).symm⟩
      | cons a l ih =>
        obtain ⟨t,ht⟩ := ih (step w a)
        exact ⟨a.op.eval (a.inputs.map fun j => w.getD j false) :: t, by
          change l.foldl step (step w a) = _
          rw [ht]
          simp [step,List.append_assoc]⟩
    have dfit (x : Fin 9→Bool) : D.eval (List.ofFn x ++ [x 4 || x 6]) = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) x := by
      let w := List.ofFn x
      let v := g.op.eval (g.inputs.map fun j => w.getD j false)
      have hw : w.length = 9 := by simp [w]
      have h9 : 9 < (w ++ [v]).length := by simp [hw]
      obtain ⟨t,ht⟩ := pref gs (w ++ [v])
      have h := first x
      change (gs.foldl step (w ++ [v])).getD 9 false = _ at h
      rw [ht,List.getD_append _ _ _ _ h9] at h
      have hv : v = (x 4 || x 6) := by
        have hd : (w ++ [v]).getD w.length false = v := by simp
        rw [hw] at hd
        exact hd.symm.trans h
      have hit := fitted x
      change (gs.foldl step (w++[v])).getD o false = _ at hit
      change (gs.foldl step (w++[x 4 || x 6])).getD o false = _
      rwa [←hv]
    have gold : ∀ a∈gs, a.op∈({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ a.inputs.length≤2 := fun a h => fan a (List.mem_cons_of_mem _ h)
    have hsize : D.size≤14 := by
      change (g :: gs).length<16 at lt
      change gs.length≤14
      simp only [List.length_cons] at lt
      omega
    by_cases hcount : gs.countP nnot≤1
    · exact small D gold hsize hcount (fun x _ => (dfit x).trans (agree x))
    · let binary := fun (g : Gate) => @GateOp.rec (fun _ => Bool) true true false (fun _ => true) true g.op
      have addCounts (l : List Gate) : l.countP binary + l.countP nnot = l.length := by
        induction l with
        | nil => rfl
        | cons a l ih =>
          rw [List.countP_cons,List.countP_cons,List.length_cons]
          cases a with
          | mk op inp => cases op <;> simp [binary,nnot] at ih ⊢ <;> omega
      have sum := addCounts gs
      change gs.length≤14 at hsize
      exact many D gold (show gs.countP binary≤12 by omega) (fun x => (dfit x).trans (agree x))

