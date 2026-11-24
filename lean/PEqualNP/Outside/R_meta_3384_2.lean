import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3384_2
    (lower : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (compile : ∀ (C D : Circuit) (k : Nat), FanInTwo C → List.Forall₂ (fun (g h : Gate) => g.op = h.op ∧ List.Forall₂ (fun i j => j=i+1 ∨ j=0 ∧ i=k) g.inputs h.inputs) C.gates D.gates →
      ∃ E : Circuit, FanInTwo E ∧ E.size ≤ C.size+1 ∧ ∀ (b : Bool) (x : Fin 7 → Bool),
        E.eval (b :: List.ofFn x) = if b then (D.wires (true :: List.ofFn x)).getD (C.output+1) false else C.eval (List.ofFn x))
    (essential : let F := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List Nat).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
    ∀ (C D : Circuit) (u v : Nat), FanInTwo C → C.size=11 → circuitFun 7 C = F →
      List.Forall₂ (fun (g h : Gate) => g.op = h.op ∧ List.Forall₂ (fun i j => j=i+1 ∨ j=0 ∧ (i=u ∨ i=v)) g.inputs h.inputs) C.gates D.gates → (∀ k : Nat, ¬ List.Forall₂ (fun (g h : Gate) => g.op = h.op ∧ List.Forall₂ (fun i j => j=i+1 ∨ j=0 ∧ i=k) g.inputs h.inputs) C.gates D.gates) →
      (∀ x : Fin 7 → Bool, (D.wires (true :: List.ofFn x)).getD (C.output+1) false = (F x || x 0 || x 3)) →
      2 ≤ (C.gates.filter (fun g => g.op.eval [true,false] && g.inputs.contains 2)).length) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (0 : Fin (7 : ℕ)) || x10 (3 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length ≥ (2 : ℕ) := by
  let F := fun x : Fin 7 → Bool => ([1,12,4,15,26,35,46,36] : List Nat).any fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10))
  dsimp only
  intro C D u v fan sz correct paired restored
  refine essential C D u v fan sz correct paired ?_ restored
  intro k one
  obtain ⟨E,efan,es,ev⟩ := compile C D k fan one
  apply lower
  refine ⟨E,efan,by omega,?_⟩
  intro y
  let x : Fin 7 → Bool := fun i => y i.succ
  have splitRow : List.ofFn y = y 0 :: List.ofFn x := List.ofFn_succ
  change E.eval (List.ofFn y) = _
  rw [splitRow,ev]
  have base : C.eval (List.ofFn x) = F x := congrFun correct x
  have lift := restored x
  change (D.wires _).getD _ false = (F x || x 0 || x 3) at lift
  rw [lift,base]
  exact (by decide +kernel : ∀ z : Fin 8 → Bool,
    (if z 0 then F (fun i => z i.succ) || z 1 || z 4 else F (fun i => z i.succ)) =
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) z) y
