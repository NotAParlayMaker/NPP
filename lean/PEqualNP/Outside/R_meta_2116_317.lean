import Mathlib.Tactic
import PEqualNP.Defs

-- Three readers with one companion force a mixed signature at an early wire.
-- The other cases require at least two distinct companions.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2116_317
  (cut : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → PEqualNP.MetaComplexity.circuitFun 9 C=(fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun k => x (Fin.ofNat 9 (k/9)) && x (Fin.ofNat 9 (k%9)))) → (∀ j : Fin C.size, let g := C.gates.get j
        (∀ i∈g.inputs, i < 9+j.val) ∧ (g.op=PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length=1 ∨ g.op≠PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length=2)) →
    ∀ J : Fin 9 → Fin C.size, (∀ v∈([4,6,7] : List (Fin 9)), (∀ j : Fin C.size, v.val∈(C.gates.get j).inputs ↔ j=J v) ∧
        (C.gates.get (J v)).op=PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ w : Nat, (∀ v∈([4,6,7] : List (Fin 9)), w≠v.val ∧ w∈(C.gates.get (J v)).inputs) → let Y := fun r : Nat => (C.wires (List.ofFn (fun i : Fin 9 => r.testBit i.val))).getD w false
      w ≤ C.size ∧ Y 0=true ∧ (∀ i∈([0,1,2,3,5,8] : List Nat), Y (2^i)=false) ∧
        ∃ r : Fin 512, r.val &&& 303=r.val ∧ r.val≠0 ∧ Y r.val=true)
  (early : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ∀ w : Nat, w < 16 → let Y := fun r : Nat => (C.wires (List.ofFn (fun i : Fin 9 => r.testBit i.val))).getD w false
      ¬(Y 0=true ∧ (∀ i∈([0,1,2,3,5,8] : List Nat), Y (2^i)=false) ∧
        ∃ r : Fin 512, r.val &&& 303=r.val ∧ r.val≠0 ∧ Y r.val=true))
  (distinct : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size ≤ 15 → PEqualNP.MetaComplexity.circuitFun 9 C=(fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun k => x (Fin.ofNat 9 (k/9)) && x (Fin.ofNat 9 (k%9)))) → (∀ j : Fin C.size, let g := C.gates.get j
        (∀ i∈g.inputs, i < 9+j.val) ∧ (g.op=PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length=1 ∨ g.op≠PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length=2)) →
    ∀ J : Fin 9 → Fin C.size, (∀ v∈([4,6,7] : List (Fin 9)), (∀ j : Fin C.size, v.val∈(C.gates.get j).inputs ↔ j=J v) ∧
        (C.gates.get (J v)).op=PEqualNP.CircuitLowerBounds.GateOp.or) → (¬∃ w : Nat, (∀ v∈([4,6,7] : List (Fin 9)), w≠v.val ∧ w∈(C.gates.get (J v)).inputs)) → False) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  classical
  dsimp only
  intro C h singles
  obtain ⟨minC,sz,funC,norm,_⟩ := h
  let S : List (Fin 9) := [4,6,7]
  let readers (v : Fin 9) : Finset (Fin C.size) := {j | v.val∈(C.gates.get j).inputs}
  have marked : ∀ v∈S, ∃ j : Fin C.size, (∀ t : Fin C.size, v.val∈(C.gates.get t).inputs ↔ t=j) ∧
      (C.gates.get j).op=PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro v hv
    obtain ⟨one,ops⟩ := singles v hv
    change (readers v).card=1 at one
    obtain ⟨j,eq⟩ := Finset.card_eq_one.mp one
    have mem (t : Fin C.size) : t∈readers v ↔ v.val∈(C.gates.get t).inputs := by simp [readers]
    have iff (t : Fin C.size) : v.val∈(C.gates.get t).inputs ↔ t=j := by
      rw [←mem,eq];exact Finset.mem_singleton
    exact ⟨j,iff,ops j ((mem j).mpr ((iff j).mpr rfl))⟩
  have non := marked 4 (by decide)
  let J (v : Fin 9) : Fin C.size := if hv : v∈S then (marked v hv).choose else non.choose
  have ok : (∀ v∈([4,6,7] : List (Fin 9)), (∀ j : Fin C.size, v.val∈(C.gates.get j).inputs ↔ j=J v) ∧
        (C.gates.get (J v)).op=PEqualNP.CircuitLowerBounds.GateOp.or) := by
    intro v hv
    simpa only [J,dite_eq_left (show v∈S from hv)] using (marked v hv).choose_spec
  have normal : (∀ j : Fin C.size, let g := C.gates.get j
        (∀ i∈g.inputs, i < 9+j.val) ∧ (g.op=PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length=1 ∨ g.op≠PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length=2)) := by
    intro j
    exact ⟨(norm j).1,(norm j).2.2⟩
  have spec : PEqualNP.MetaComplexity.circuitFun 9 C=(fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any (fun k => x (Fin.ofNat 9 (k/9)) && x (Fin.ofNat 9 (k%9)))) := by
    rw [funC]
    funext x
    simp only [List.any_cons,List.any_nil,Bool.or_false]
    simp only [Bool.or_assoc]
    rfl
  by_cases existsCommon : ∃ w : Nat, (∀ v∈([4,6,7] : List (Fin 9)), w≠v.val ∧ w∈(C.gates.get (J v)).inputs)
  · obtain ⟨w,c⟩ := existsCommon
    obtain ⟨le,sign⟩ := cut C minC spec normal J ok w c
    exact early C minC.1 w (by omega) sign
  · exact distinct C minC sz spec normal J ok existsCommon
