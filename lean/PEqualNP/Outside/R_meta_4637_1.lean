import Mathlib
import PEqualNP.Defs

set_option linter.unusedVariables false

theorem PEqualNP.Outside.R_meta_4637_1
  (h1 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List Bool), x3.length = x1 → x3 = [] → { gates := List.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => { op := x5.op, inputs := List.map (fun (x6 : ℕ) => Min.min x6 (x1 + x2.size)) x5.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x3 = x2.wires x3)
  (h2 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List Bool), x3.length = x1 → x3 ≠ [] → { gates := List.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => { op := x5.op, inputs := List.map (fun (x6 : ℕ) => Min.min x6 (x1 + x2.size)) x5.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x3 = x2.wires x3) :
  ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List Bool), x3.length = x1 → { gates := List.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => { op := x5.op, inputs := List.map (fun (x6 : ℕ) => Min.min x6 (x1 + x2.size)) x5.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x3 = x2.wires x3 := by
  intro x1 x2 x3 hlen
  by_cases h : x3 = []
  · exact h1 x1 x2 x3 hlen h
  · exact h2 x1 x2 x3 hlen h
