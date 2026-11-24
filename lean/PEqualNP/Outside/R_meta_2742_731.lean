import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.R_meta_2742_731
    (deletedLower : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (propagate : ∀ (C : Circuit), FanInTwo C →
      2 ≤ C.gates.countP (fun g =>
        (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).any
          (fun i => decide (i = 6 ∨ i = 9))) →
      (∃ x : Fin 8 → Bool, C.eval [x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3, false, false, true] = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
        ∀ x : Fin 8 → Bool, D.eval (List.ofFn x) =
          C.eval [x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3, false, false, true])
    (lowReaders : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length ≤ (13 : ℕ) →     x2 < (12 : ℕ) + x1.length →       x3 < (12 : ℕ) + x1.length →         PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →           (∀ (x8 : Fin x1.length),               have x9 : PEqualNP.CircuitLowerBounds.Gate := x1.get x8;               (∀ x10 ∈ x9.inputs, x10 < (12 : ℕ) + ↑x8) ∧ x9.inputs.Nodup ∧ (x9.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x9.inputs.length = (1 : ℕ) ∨ x9.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x9.inputs.length = (2 : ℕ))) →             (∃ x9 ∈ x1, x9.op = PEqualNP.CircuitLowerBounds.GateOp.not) → x1.countP (fun g => (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6 ∨ i = 9))) ≤ 1 →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)), Bool.false, Bool.true];                 ({ gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval x11 || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval x11) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x10 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x10 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ)))) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length ≤ (13 : ℕ) →     x2 < (12 : ℕ) + x1.length →       x3 < (12 : ℕ) + x1.length →         PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →           (∀ (x8 : Fin x1.length),               have x9 : PEqualNP.CircuitLowerBounds.Gate := x1.get x8;               (∀ x10 ∈ x9.inputs, x10 < (12 : ℕ) + ↑x8) ∧ x9.inputs.Nodup ∧ (x9.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x9.inputs.length = (1 : ℕ) ∨ x9.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x9.inputs.length = (2 : ℕ))) →             (∃ x9 ∈ x1, x9.op = PEqualNP.CircuitLowerBounds.GateOp.not) →               ∃ (x10 : Fin (9 : ℕ) → Bool),                 have x11 : List Bool := List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)), Bool.false, Bool.true];                 ({ gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval x11 || { gates := x1, output := x3 : PEqualNP.CircuitLowerBounds.Circuit }.eval x11) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x12 : ℕ) => x10 (Fin.ofNat (9 : ℕ) (x12 / (10 : ℕ))) && x10 (Fin.ofNat (9 : ℕ) (x12 % (10 : ℕ))) := by
  let extend (x : Fin 8 → Bool) (i : Fin 9) : Bool :=
    [x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3].getD i.val false
  have relabel (x : Fin 8 → Bool) :
      [(1 : ℕ), 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any
        (fun e => extend x (Fin.ofNat 9 (e / 10)) && extend x (Fin.ofNat 9 (e % 10))) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
       (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
       (x 5 && x 7) || (x 7 && x 4)) := by
    clear deletedLower lowReaders
    dsimp [extend]
    simp [List.getD, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm, Bool.and_comm]


  let fixedInput (x : Fin 8 → Bool) : List Bool :=
    [x 1, x 0, x 4, x 7, x 5, x 2, false, x 6, x 3, false, false, true]
  let effectiveTouches (g : Gate) : Bool :=
    (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).any
      (fun i => decide (i = 6 ∨ i = 9))
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wiresLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
  intro xs o₁ o₂ hlen ho₁ ho₂ hfan hshape hnot
  by_cases hlow : xs.countP effectiveTouches ≤ 1
  · exact lowReaders xs o₁ o₂ hlen ho₁ ho₂ hfan hshape hnot hlow
  by_contra hbad
  push Not at hbad
  let C : Circuit := ⟨xs ++ [⟨.or, [o₁, o₂]⟩], 12 + xs.length⟩
  have cFan : FanInTwo C := by
    intro g hg
    change g ∈ xs ++ [⟨.or, [o₁, o₂]⟩] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hfan g hg
    · obtain rfl := List.mem_singleton.mp hg
      exact ⟨Or.inr (Or.inl rfl), by simp⟩
  have cSize : C.size = xs.length + 1 := by
    change (xs ++ [(⟨.or, [o₁, o₂]⟩ : Gate)]).length = xs.length + 1
    simp only [List.length_append, List.length_singleton]
  have cCount : 2 ≤ C.gates.countP effectiveTouches := by
    change 2 ≤ (xs ++ [(⟨.or, [o₁, o₂]⟩ : Gate)]).countP effectiveTouches
    rw [List.countP_append]
    omega
  have combine (w : List Bool) (hw : w.length = 12) :
      C.eval w = ((⟨xs, o₁⟩ : Circuit).eval w || (⟨xs, o₂⟩ : Circuit).eval w) := by
    let ws := xs.foldl step w
    have atOutput : ws.length = 12 + xs.length := (wiresLen xs w).trans (by rw [hw])
    change ((xs ++ [(⟨.or, [o₁, o₂]⟩ : Gate)]).foldl step w).getD (12 + xs.length) false =
      (ws.getD o₁ false || ws.getD o₂ false)
    rw [List.foldl_append]
    change (ws ++ [ws.getD o₁ false || (ws.getD o₂ false || false)]).getD (12 + xs.length) false = _
    rw [Bool.or_false, ← atOutput]
    simp [List.getD]
  have input_eq (x : Fin 8 → Bool) :
      List.ofFn (extend x) ++ [extend x 0 && extend x 6, false, true] = fixedInput x := by
    simp [List.ofFn_succ, extend, fixedInput, List.getD]
  have agreement (x : Fin 8 → Bool) : C.eval (fixedInput x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) := by
    let pins := List.ofFn (extend x) ++ [extend x 0 && extend x 6, false, true]
    have refuted := hbad (extend x)
    change ¬ (((⟨xs, o₁⟩ : Circuit).eval pins || (⟨xs, o₂⟩ : Circuit).eval pins) ≠ _) at refuted
    have computes : ((⟨xs, o₁⟩ : Circuit).eval pins || (⟨xs, o₂⟩ : Circuit).eval pins) = _ :=
      Classical.byContradiction refuted
    rw [combine _ (by simp [fixedInput]), ← input_eq x, computes]
    exact relabel x
  have cFalse : ∃ x, C.eval (fixedInput x) = false := by
    exact ⟨fun _ => false, (agreement (fun _ => false)).trans rfl⟩
  obtain ⟨D, hd, hsize, heval⟩ := propagate C cFan cCount cFalse
  exact deletedLower ⟨D, hd, by omega, fun x => (heval x).trans (agreement x)⟩
