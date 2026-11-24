import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Fixing vertex one removes its three edges and every effective reader of either polarity.
-- The restricted graph is a five-cycle with two pendant vertices.
-- Its bound appears as conj_82 in L-meta-927. L-meta-1007 gives the ordinary bound.
theorem PEqualNP.Outside.R_meta_2891_73
    (sevenVertices : ∀ t : ℕ, HasCircuitSize 7 (fun x : Fin 7 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) ||
      (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) t → 9 ≤ t)
    (ordinary : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
        (x 5 && x 7) || (x 7 && x 4))) 12)
    (projection : ∀ D : Circuit, FanInTwo D →
      4 ≤ D.gates.countP (fun g : Gate => (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun i => i == 1 || i == 8)) →
      (∃ y : Fin 7 → Bool, D.eval [y 3, false, y 6, y 4, y 0, y 5, y 2, y 1, true] = false) →
      ∃ E : Circuit, FanInTwo E ∧ E.size + 4 ≤ D.size ∧
        ∀ y : Fin 7 → Bool, E.eval (List.ofFn y) =
          D.eval [y 3, false, y 6, y 4, y 0, y 5, y 2, y 1, true])
    (fewReaders : ∀ C : Circuit, C.size = 12 →
      IsMinimalCircuit 8 ⟨⟨GateOp.not, [1]⟩ :: C.gates, C.output⟩ →
      C.gates.countP (fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any
          (fun i => i == 1 || i == 8)) ≤ 3 →
      ∃ x : Fin 8 → Bool, C.eval (List.ofFn x ++ [!x 1]) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4))) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 12 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x ++ [!x 1]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
         (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
         (x 5 && x 7) || (x 7 && x 4)) := by
  rintro ⟨C, fan, size, computes⟩
  let reads := fun g : Gate =>
    (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any
      (fun i => i == 1 || i == 8)
  by_cases few : C.gates.countP reads ≤ 3
  · let inverter : Gate := ⟨GateOp.not, [1]⟩
    let ordinaryCircuit : Circuit := ⟨inverter :: C.gates, C.output⟩
    have ordinaryFan : FanInTwo ordinaryCircuit := by
      intro g hg
      change g ∈ inverter :: C.gates at hg
      rcases List.mem_cons.mp hg with rfl | h
      · exact ⟨Or.inr (Or.inr rfl), by decide⟩
      · exact fan g h
    have cost : ordinaryCircuit.size = C.size + 1 := rfl
    have agrees (x : Fin 8 → Bool) :
        circuitFun 8 ordinaryCircuit x = C.eval (List.ofFn x ++ [!x 1]) := by
      change (C.gates.foldl _ (List.ofFn x ++ [GateOp.not.eval
        ([1].map (fun i => (List.ofFn x).getD i false))])).getD C.output false = _
      have readOne : (List.ofFn x).getD 1 false = x 1 := by simp [List.getD]
      rw [show GateOp.not.eval ([1].map (fun i => (List.ofFn x).getD i false)) =
        !((List.ofFn x).getD 1 false) from rfl, readOne]
      rfl
    have ordinaryBound (D : Circuit) (hD : FanInTwo D)
        (same : circuitFun 8 D = circuitFun 8 ordinaryCircuit) : 13 ≤ D.size := by
      by_contra! small
      apply ordinary
      exact ⟨D, hD, by omega, fun x => (congrFun same x).trans ((agrees x).trans (computes x))⟩
    have least : IsMinimalCircuit 8 ordinaryCircuit := by
      refine ⟨ordinaryFan, ?_⟩
      intro D hD same
      have bound := ordinaryBound D hD same
      omega
    have enough := ordinaryBound ordinaryCircuit ordinaryFan rfl
    obtain ⟨x, hx⟩ := fewReaders C (by omega) least few
    exact hx (computes x)
  have specializeInputs (y : Fin 7 → Bool) :
      C.eval [y 3, false, y 6, y 4, y 0, y 5, y 2, y 1, true] =
      ((y 0 && y 1) || (y 0 && y 2) || (y 0 && y 3) || (y 1 && y 4) ||
       (y 1 && y 5) || (y 2 && y 6) || (y 4 && y 6)) := by
    let x : Fin 8 → Bool := ![y 3, false, y 6, y 4, y 0, y 5, y 2, y 1]
    have h := computes x
    change C.eval [y 3, false, y 6, y 4, y 0, y 5, y 2, y 1, true] = _ at h
    simpa [x, Matrix.cons_val_succ, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, Bool.and_comm] using h
  obtain ⟨E, fanE, sizeE, evalE⟩ := projection C fan (by
    change 4 ≤ C.gates.countP reads
    omega)
    ⟨fun _ => false, specializeInputs (fun _ => false)⟩
  have lower := sevenVertices E.size ⟨E, fanE, le_rfl, fun y => (evalE y).trans (specializeInputs y)⟩
  omega
