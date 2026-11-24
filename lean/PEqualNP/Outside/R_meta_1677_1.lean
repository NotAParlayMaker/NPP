import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_1677_1
    (optimalBudget : ∀ C : Circuit, FanInTwo C → C.size ≤ 15 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) →
      C.size = 15 ∧ C.gates.countP (fun g => g.op.eval [false]) ≤ 2)
    (withoutNot : ∀ D : Circuit, FanInTwo D → D.size = 14 →
      D.gates.countP (fun g => g.op.eval [false]) = 0 →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 6]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5))
    (withNot : ∀ D : Circuit, FanInTwo D → D.size = 14 →
      1 ≤ D.gates.countP (fun g => g.op.eval [false]) →
      D.gates.countP (fun g => g.op.eval [false]) ≤ 2 →
      ∃ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 6]) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C fan first computes
  by_contra! small
  change C.gates.length < 16 at small
  let target (x : Fin 9 → Bool) := (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)
  have evalTarget (x : Fin 9 → Bool) : C.eval (List.ofFn x) = target x := congrFun computes x
  let tag (g : Gate) := g.op.eval [false]
  obtain ⟨optimal, notBound⟩ := optimalBudget C fan (by change C.gates.length ≤ 15; omega) evalTarget
  let step (bits : List Bool) (g : Gate) :=
    bits ++ [g.op.eval (g.inputs.map fun i => bits.getD i false)]
  have prefixRead (gs : List Gate) (bits : List Bool) (i : ℕ) (hi : i < bits.length) :
      (gs.foldl step bits).getD i false = bits.getD i false := by
    induction gs generalizing bits with
    | nil => rfl
    | cons g gs ih =>
      have hstep : i < (step bits g).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ih _ hstep]
      exact List.getD_append _ _ _ _ hi
  have nonempty : ∃ g gs, C.gates = g :: gs := by
    cases h : C.gates with
    | nil =>
      let x (i : Fin 9) := decide (i = 0)
      have wire := first x
      change (C.gates.foldl step (List.ofFn x)).getD 9 false = (x 0 || x 6) at wire
      rw [h] at wire
      exact False.elim (Bool.false_ne_true wire)
    | cons g gs => exact ⟨g, gs, rfl⟩
  obtain ⟨g, gs, gates⟩ := nonempty
  let D : Circuit := ⟨gs, C.output⟩
  have firstValue (x : Fin 9 → Bool) : step (List.ofFn x) g = List.ofFn x ++ [x 0 || x 6] := by
    have wire := first x
    change (C.gates.foldl step (List.ofFn x)).getD 9 false = (x 0 || x 6) at wire
    have rawLen : (List.ofFn x).length = 9 := List.length_ofFn
    rw [gates, List.foldl_cons, prefixRead] at wire
    · change (List.ofFn x ++ [g.op.eval (g.inputs.map fun i =>
        (List.ofFn x).getD i false)]).getD 9 false = (x 0 || x 6) at wire
      rw [List.getD_append_right _ _ _ _ (by omega), rawLen] at wire
      change g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 6) at wire
      change List.ofFn x ++ [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)] =
        List.ofFn x ++ [x 0 || x 6]
      rw [wire]
    · simp only [step, List.length_append, List.length_cons, List.length_nil, rawLen]
      omega
  have tailComputes (x : Fin 9 → Bool) :
      D.eval (List.ofFn x ++ [x 0 || x 6]) = target x := by
    have value := evalTarget x
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = target x at value
    rw [gates, List.foldl_cons, firstValue] at value
    exact value
  have tailFan : FanInTwo D := by
    intro q hq
    apply fan q
    rw [gates]
    exact List.mem_cons_of_mem _ hq
  have tailSize : D.size = 14 := by
    change gs.length = 14
    change C.gates.length = 15 at optimal
    rw [gates, List.length_cons] at optimal
    omega
  have tailNotBound : D.gates.countP tag ≤ 2 := by
    change gs.countP tag ≤ 2
    change C.gates.countP tag ≤ 2 at notBound
    rw [gates, List.countP_cons] at notBound
    split at notBound <;> omega
  by_cases h : D.gates.countP tag = 0
  · obtain ⟨x, hx⟩ := withoutNot D tailFan tailSize h
    exact hx (tailComputes x)
  · have positive : 1 ≤ D.gates.countP tag := by omega
    obtain ⟨x, hx⟩ := withNot D tailFan tailSize positive tailNotBound
    exact hx (tailComputes x)
