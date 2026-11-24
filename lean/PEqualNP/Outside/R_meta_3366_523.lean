import Mathlib
import PEqualNP.Defs

-- The cofactor maps and the eight-input reconstruction are adapted from project PR 6449 by itsvari.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3366_523
    (pin : ∀ (n : ℕ) (C : Circuit) (bank : List (Option (Fin n))) (pins : List ℕ),
      FanInTwo C → (∀ i ∈ pins, bank[i]? = some none) →
      (∃ x y : Fin n → Bool, C.eval (bank.map (fun a => a.elim false x)) ≠ C.eval (bank.map (fun a => a.elim false y))) →
      let binary := fun (g : Gate) => GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op
      let read := fun (g : Gate) => pins.any fun i => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains i
      ∃ D : Circuit, FanInTwo D ∧ D.size + (C.gates.filter read).length ≤ C.size ∧
        D.gates.countP binary + (C.gates.filter (fun g => !binary g || read g)).length ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (bank.map (fun a => a.elim false x)))
    (thetaLower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates)
    (lowerFour : ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))) (12 : ℕ))
    (residual : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) →
      let charges (pins : List ℕ) (gate : Gate) := pins.any fun wire =>
        (if gate.op.eval [false] = true then gate.inputs.take 1 else gate.inputs).contains wire
      let binary := fun (g : Gate) => GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op
      (x2.gates.filter (fun g => !binary g || charges [0,3,4] g)).length ≤ 2 →
      (x2.gates.filter (charges [0,4])).length ≤ 1 → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (0 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))]) = x1 x5) → False := by
  dsimp only
  intro C fan size correct
  let graph9 (x : Fin 9 → Bool) : Bool :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2

  let theta7 (x : Fin 7 → Bool) : Bool :=
    ([(0,1),(1,2),(0,4),(1,5),(2,6),(3,5),(4,6),(6,3)] : List (Fin 7 × Fin 7)).any
      fun e => x e.1 && x e.2

  let embed (x : Fin 7 → Bool) : Fin 9 → Bool :=
    ![x 2, x 1, x 0, false, false, x 6, x 5, x 4, x 3]

  let row (x : Fin 9 → Bool) : List Bool :=
    List.ofFn (Function.update x 0 false) ++ [x 0 || x 4, x 0 || x 3]

  let bank : List (Option (Fin 7)) :=
    [none, some 1, some 0, none, none, some 6, some 5, some 4, some 3, some 2, some 2]

  have rows : ∀ y : Fin 7 → Bool, bank.map (fun a => a.elim false y) = row (embed y) := by
    decide +kernel

  have target : ∀ y : Fin 7 → Bool, graph9 (embed y) = theta7 y := by
    decide +kernel

  have noSource : ∀ i ∈ ([0,3,4] : List ℕ), bank[i]? = some none := by
    intro i mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> rfl

  let charges (gate : Gate) : Bool :=
    ([0,3,4] : List ℕ).any fun i =>
      (if gate.op.eval [false] = true then gate.inputs.take 1 else gate.inputs).contains i
  change ∀ x, C.eval (row x) = graph9 x at correct
  let binary := fun (g : Gate) => GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op
  have cap : (C.gates.filter (fun g => !binary g || charges g)).length ≤ 2 := by
    have cofactor (y : Fin 7 → Bool) : C.eval (bank.map (fun a => a.elim false y)) = theta7 y :=
      (congrArg C.eval (rows y)).trans ((correct (embed y)).trans (target y))
    have twoValues :
        ∃ x y : Fin 7 → Bool, C.eval (bank.map (fun a => a.elim false x)) ≠
          C.eval (bank.map (fun a => a.elim false y)) := by
      refine ⟨fun _ => false, fun _ => true, ?_⟩
      rw [cofactor (fun _ => false), cofactor (fun _ => true)]
      decide
    obtain ⟨D, fanD, _, saved, eval⟩ := pin 7 C bank [0,3,4] fan noSource twoValues
    have portable (y : Fin 7 → Bool) : D.eval (List.ofFn y) = theta7 y :=
      (eval y).trans (cofactor y)
    have lower := thetaLower D fanD (funext portable)
    change 11 ≤ D.gates.countP binary at lower
    change D.gates.countP binary + (C.gates.filter (fun g => !binary g || charges g)).length ≤ C.size at saved
    omega
  let fixedFour (x : Fin 8 → Bool) : Fin 9 → Bool :=
    ![x 0,x 1,x 2,x 3,false,x 4,x 5,x 6,x 7]

  let newPort (x : Fin 8 → Bool) : Fin 9 → Bool :=
    ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 0 || x 3]

  let fourBank : List (Option (Fin 9)) :=
    [none,some 1,some 2,some 3,none,some 4,some 5,some 6,some 7,some 0,some 8]

  let degreeTwo (x : Fin 8 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
    (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
    (x 5 && x 7) || (x 7 && x 4)

  have fourRows : ∀ y : Fin 8 → Bool,
      fourBank.map (fun a => a.elim false (newPort y)) = row (fixedFour y) := by
    decide +kernel

  have fourTarget : ∀ y : Fin 8 → Bool, graph9 (fixedFour y) = degreeTwo y := by
    decide +kernel

  have fourNoSource : ∀ i ∈ ([0,4] : List ℕ), fourBank[i]? = some none := by
    intro i mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> rfl

  let chargesFour (gate : Gate) : Bool :=
    ([0,4] : List ℕ).any fun i =>
      (if gate.op.eval [false] = true then gate.inputs.take 1 else gate.inputs).contains i

  have portValues : ∀ y : Fin 8 → Bool,
      List.ofFn (newPort y) = List.ofFn y ++ [GateOp.or.eval
        ([0,3].map fun i => (List.ofFn y).getD i false)] := by
    decide +kernel
  have capFour : (C.gates.filter chargesFour).length ≤ 1 := by
    have cofactor (y : Fin 8 → Bool) :
        C.eval (fourBank.map (fun a => a.elim false (newPort y))) = degreeTwo y :=
      (congrArg C.eval (fourRows y)).trans ((correct (fixedFour y)).trans (fourTarget y))
    have different :
        ∃ x y : Fin 9 → Bool, C.eval (fourBank.map (fun a => a.elim false x)) ≠
          C.eval (fourBank.map (fun a => a.elim false y)) := by
      refine ⟨newPort (fun _ => false), newPort (fun _ => true), ?_⟩
      rw [cofactor (fun _ => false), cofactor (fun _ => true)]
      decide
    obtain ⟨D, fanD, saved, _, evaluate⟩ := pin 9 C fourBank [0,4] fan fourNoSource different
    let orHead : Gate := ⟨.or,[0,3]⟩
    let rebuilt : Circuit := ⟨orHead::D.gates, D.output⟩
    have rebuiltFan : FanInTwo rebuilt := by
      intro gate member
      rcases List.mem_cons.mp member with first | rest
      · subst gate
        simp [orHead]
      · exact fanD gate rest
    have agreement (x : Fin 8 → Bool) : rebuilt.eval (List.ofFn x) = degreeTwo x := by
      have start : rebuilt.eval (List.ofFn x) = D.eval (List.ofFn (newPort x)) := by
        rw [portValues x]
        rfl
      exact start.trans ((evaluate (newPort x)).trans (cofactor x))
    by_contra! large
    apply lowerFour
    change D.size + (C.gates.filter chargesFour).length ≤ C.size at saved
    have rebuiltSize : rebuilt.size ≤ 12 := by
      change D.gates.length + 1 ≤ 12
      change D.gates.length + _ ≤ C.size at saved
      omega
    exact ⟨rebuilt, rebuiltFan, rebuiltSize, agreement⟩
  exact residual C fan size cap capFour correct
