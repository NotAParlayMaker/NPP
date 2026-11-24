import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_3271_813
    (binaryLower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → 14 ≤ x1.gates.countP (fun gate =>
      GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true gate.op))
    (monotone : ∀ C : Circuit, Monotone2 C → Monotone (circuitFun 9 C)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn fun (x6 : Fin (9 : ℕ)) => if x6 = (0 : Fin (9 : ℕ)) then !x5 (0 : Fin (9 : ℕ)) else x5 x6) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → False := by
  intro signedCircuit legal size _oneReader computes
  let signedRow (x : Fin 9 → Bool) (i : Fin 9) := if i = 0 then !x 0 else x i
  let edge (x : Fin 9 → Bool) :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let charged (gate : Gate) : Bool :=
    GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true gate.op
  let negation (gate : Gate) : Bool :=
    GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false gate.op
  have hasNot : ∃ gate ∈ signedCircuit.gates, gate.op = .not := by
    by_contra! missing
    have allMonotone : Monotone2 signedCircuit := by
      intro gate member
      have options : gate.op = .and ∨ gate.op = .or ∨ gate.op = .not := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (legal gate member).1
      rcases options with andGate | orGate | notGate
      · exact ⟨by simp [andGate], (legal gate member).2⟩
      · exact ⟨by simp [orGate], (legal gate member).2⟩
      · exact (missing gate member notGate).elim
    let absent : Fin 9 → Bool := fun index => decide (index = 1)
    let present : Fin 9 → Bool := fun index => decide (index = 0 ∨ index = 1)
    have ordering : signedRow present ≤ signedRow absent := by
      intro index
      fin_cases index <;> decide +kernel
    have presentEdge : edge present = true := by decide +kernel
    have absentEdge : edge absent = false := by decide +kernel
    have cannot := (monotone signedCircuit allMonotone) ordering
    change signedCircuit.eval (List.ofFn (signedRow present)) ≤
      signedCircuit.eval (List.ofFn (signedRow absent)) at cannot
    have presentCorrect : signedCircuit.eval (List.ofFn (signedRow present)) = edge present := computes present
    rw [presentCorrect, presentEdge] at cannot
    have absentCorrect : signedCircuit.eval (List.ofFn (signedRow absent)) = edge absent := computes absent
    rw [absentCorrect, absentEdge] at cannot
    exact (by decide : ¬ (true : Bool) ≤ false) cannot
  let rename (wire : ℕ) : ℕ := if wire = 0 then 9 else if wire < 9 then wire else wire + 1
  let remap (gate : Gate) : Gate := ⟨gate.op, gate.inputs.map rename⟩
  let inverter : Gate := ⟨.not, [0]⟩
  let full : Circuit := ⟨inverter :: signedCircuit.gates.map remap, rename signedCircuit.output⟩
  let step (wires : List Bool) (gate : Gate) :=
    wires ++ [gate.op.eval (gate.inputs.map fun wire => wires.getD wire false)]
  have readsSame (x : Fin 9 → Bool) (suffix : List Bool) (wire : ℕ) :
      ((List.ofFn x ++ [!x 0]) ++ suffix).getD (rename wire) false =
        (List.ofFn (signedRow x) ++ suffix).getD wire false := by
    by_cases isInput : wire < 9
    · have inputReads (index : Fin 9) :
          ((List.ofFn x ++ [!x 0]) ++ suffix).getD (rename index.val) false =
            (List.ofFn (signedRow x) ++ suffix).getD index.val false := by
        fin_cases index <;> simp [rename, signedRow, List.ofFn_succ]
      exact inputReads ⟨wire, isInput⟩
    · have nonzero : wire ≠ 0 := by omega
      have renameIndex : rename wire = wire + 1 := by simp [rename, nonzero, isInput]
      rw [renameIndex, List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      have offset : wire + 1 - (List.ofFn x ++ [!x 0]).length =
          wire - (List.ofFn (signedRow x)).length := by simp
      rw [offset]
  have runSame (gates : List Gate) (x : Fin 9 → Bool) (suffix : List Bool) :
      ∃ values : List Bool,
        gates.foldl step (List.ofFn (signedRow x) ++ suffix) = List.ofFn (signedRow x) ++ values ∧
        (gates.map remap).foldl step ((List.ofFn x ++ [!x 0]) ++ suffix) =
          (List.ofFn x ++ [!x 0]) ++ values := by
    induction gates generalizing suffix with
    | nil => exact ⟨suffix, rfl, rfl⟩
    | cons gate remaining inductionHypothesis =>
      let value := gate.op.eval (gate.inputs.map (fun wire => (List.ofFn (signedRow x) ++ suffix).getD wire false))
      have originalStep : step (List.ofFn (signedRow x) ++ suffix) gate =
          List.ofFn (signedRow x) ++ (suffix ++ [value]) := by
        simp [step, value]
      have sameValue :
          (remap gate).op.eval ((remap gate).inputs.map
            (fun wire => ((List.ofFn x ++ [!x 0]) ++ suffix).getD wire false)) = value := by
        simp only [remap, List.map_map, Function.comp_def, readsSame x suffix, value]
      have newStep : step ((List.ofFn x ++ [!x 0]) ++ suffix) (remap gate) =
          (List.ofFn x ++ [!x 0]) ++ (suffix ++ [value]) := by
        unfold step
        rw [sameValue]
        simp only [List.append_assoc]
      simpa only [List.foldl_cons, List.map_cons, originalStep, newStep] using
        inductionHypothesis (suffix ++ [value])
  have computesFull : circuitFun 9 full = edge := by
    funext x
    have firstBit : (List.ofFn x).getD 0 false = x 0 := by rw [List.ofFn_succ]; rfl
    have firstStep : step (List.ofFn x) inverter = List.ofFn x ++ [!x 0] := by
      change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = _
      rw [firstBit]
    obtain ⟨values, oldTrace, newTrace⟩ := runSame signedCircuit.gates x []
    simp only [List.append_nil] at oldTrace newTrace
    change ((signedCircuit.gates.map remap).foldl step (step (List.ofFn x) inverter)).getD
      (rename signedCircuit.output) false = _
    rw [firstStep, newTrace, readsSame, ← oldTrace]
    exact computes x
  have legalFull : FanInTwo full := by
    intro gate member
    change gate ∈ inverter :: signedCircuit.gates.map remap at member
    rcases List.mem_cons.mp member with rfl | tail
    · simp [inverter]
    · obtain ⟨original, present, rfl⟩ := List.mem_map.mp tail
      simpa [remap] using legal original present
  have sameCost : full.gates.countP charged = signedCircuit.gates.countP charged := by
    change (inverter :: signedCircuit.gates.map remap).countP charged = _
    rw [List.countP_cons_of_neg (by decide : ¬ charged inverter), List.countP_map]
    rfl
  have partition (gates : List Gate) : gates.countP charged + gates.countP negation = gates.length := by
    induction gates with
    | nil => rfl
    | cons gate remaining inductionHypothesis =>
      cases operation : gate.op <;>
        simp [charged, negation, operation] at inductionHypothesis ⊢ <;> omega
  obtain ⟨gate, member, negative⟩ := hasNot
  have positive : 0 < signedCircuit.gates.countP negation :=
    List.countP_pos_iff.mpr ⟨gate, member, by simp [negation, negative]⟩
  have lower := binaryLower full legalFull computesFull
  change 14 ≤ full.gates.countP charged at lower
  have total := partition signedCircuit.gates
  change signedCircuit.gates.length ≤ 14 at size
  omega
