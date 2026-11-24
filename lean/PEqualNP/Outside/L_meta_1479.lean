import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1479_aux

def C : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 15]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 18]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 8]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 21]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 24]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 8]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 27]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 30]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 33]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 25]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 31]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 36]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 34]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 39]⟩,
    ], output := 40 }

end PEqualNP.Outside.L_meta_1479_aux

open PEqualNP.Outside.L_meta_1479_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1479 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  refine ⟨C, by decide +kernel, by decide +kernel, by decide +kernel, 0, 0, by decide +kernel, ?_, ?_⟩
  · refine ⟨fun n => (C.wires (List.ofFn (fun my : Fin 14 => decide (my = Fin.castAdd 7 (0 : Fin 7))))).getD n false, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨fun n => (C.wires (List.ofFn (fun mx : Fin 14 => decide (mx = Fin.natAdd 7 (0 : Fin 7))))).getD n false, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
