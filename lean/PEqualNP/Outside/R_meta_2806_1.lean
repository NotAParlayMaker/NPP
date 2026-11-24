import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2806_1
    (hAnd : have target : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      have seed : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (g : Gate),
        v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ k → k ≤ 10 + C.size →
        g.op = GateOp.and → g.inputs.length ≤ 2 → ↑v ∈ g.inputs →
        (∀ h ∈ List.take (k - 10) C.gates, ↑v ∉ h.inputs) →
        ∃ x : Fin 9 → Bool,
          let wires := seed x
          C.eval (wires.set ↑v (g.op.eval (List.map
            (fun i => if i < k then (C.wires wires).getD i false else false) g.inputs))) ≠ target x)
    (hOr : have target : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      have seed : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (g : Gate),
        v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ k → k ≤ 10 + C.size →
        g.op = GateOp.or → g.inputs.length ≤ 2 → ↑v ∈ g.inputs →
        (∀ h ∈ List.take (k - 10) C.gates, ↑v ∉ h.inputs) →
        ∃ x : Fin 9 → Bool,
          let wires := seed x
          C.eval (wires.set ↑v (g.op.eval (List.map
            (fun i => if i < k then (C.wires wires).getD i false else false) g.inputs))) ≠ target x)
    (hNot : have target : (Fin 9 → Bool) → Bool := fun x =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      have seed : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
      ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (g : Gate),
        v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ k → k ≤ 10 + C.size →
        g.op = GateOp.not → g.inputs.length ≤ 2 → ↑v ∈ g.inputs →
        (∀ h ∈ List.take (k - 10) C.gates, ↑v ∉ h.inputs) →
        ∃ x : Fin 9 → Bool,
          let wires := seed x
          C.eval (wires.set ↑v (g.op.eval (List.map
            (fun i => if i < k then (C.wires wires).getD i false else false) g.inputs))) ≠ target x) :
    have target : (Fin 9 → Bool) → Bool := fun x =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
    have seed : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
    ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (g : Gate),
      v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ k → k ≤ 10 + C.size →
      g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not →
      g.inputs.length ≤ 2 → ↑v ∈ g.inputs →
      (∀ h ∈ List.take (k - 10) C.gates, ↑v ∉ h.inputs) →
      ∃ x : Fin 9 → Bool,
        let wires := seed x
        C.eval (wires.set ↑v (g.op.eval (List.map
          (fun i => if i < k then (C.wires wires).getD i false else false) g.inputs))) ≠ target x := by
  intro target seed v C k g hv0 hv6 hfan hsize hklo hkhi hop hlen hread hfirst
  rcases hop with h | h | h
  · exact hAnd v C k g hv0 hv6 hfan hsize hklo hkhi h hlen hread hfirst
  · exact hOr v C k g hv0 hv6 hfan hsize hklo hkhi h hlen hread hfirst
  · exact hNot v C k g hv0 hv6 hfan hsize hklo hkhi h hlen hread hfirst
