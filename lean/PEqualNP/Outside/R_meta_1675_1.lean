import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_1675_1
    (h0 : ∀ (C : Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      (∀ j : Fin C.gates.length, (C.gates.get j).op ≠ GateOp.not) →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size)
    (h1 : ∀ (C : Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      (∃ j : Fin C.gates.length, (j : ℕ) ≤ 7 ∧ (C.gates.get j).op = GateOp.not) →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size)
    (h2 : ∀ (C : Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      (∃ j : Fin C.gates.length, 8 ≤ (j : ℕ) ∧ (C.gates.get j).op = GateOp.not) →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size) :
    ∀ (C : Circuit), PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size := by
  intro C hfan hfirst hfun
  by_cases h : ∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not
  · obtain ⟨j, hnot⟩ := h
    by_cases h7 : (j : ℕ) ≤ 7
    · exact h1 C hfan hfirst ⟨j, h7, hnot⟩ hfun
    · exact h2 C hfan hfirst ⟨j, by omega, hnot⟩ hfun
  · push_neg at h
    exact h0 C hfan hfirst h hfun
