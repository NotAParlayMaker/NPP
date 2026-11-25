import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11157_aux
def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [27, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [30, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [35, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 34]⟩], 40⟩

def wire (x : ℕ) : ℕ := if x = 0 then 0 else if x = 7 then 1 else if x = 14 then 1 else if x = 15 then 1 else if x = 40 then 5 else 2
end PEqualNP.Outside.L_meta_11157_aux

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
protected theorem PEqualNP.Outside.L_meta_11157_aux.ab : PEqualNP.Outside.L_meta_11157_aux.circuit.size ≤ 27 ∧
  (∀ n g, PEqualNP.Outside.L_meta_11157_aux.circuit.gates[n]? = some g →
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + n ∧ b < 14 + n) := by
  refine ⟨?_, ?_⟩
  · simp
  · decide +kernel

protected theorem PEqualNP.Outside.L_meta_11157_aux.eq (x : Fin 14 → Bool) :
  PEqualNP.Outside.L_meta_11157_aux.circuit.eval (List.ofFn x) = true ↔
  ∃ i j : Fin 7, (i = j ∨ i = j + 1 ∨ i = j + 3) ∧ x (Fin.castAdd 7 i) = true ∧ x (Fin.natAdd 7 j) = true := by
  decide +kernel

protected theorem PEqualNP.Outside.L_meta_11157_aux.wire (b : Bool) : ∃ w : ℕ → ℕ,
  w (if b then 0 else 7) = 0 ∧ w (if b then 7 else 0) ≤ 1 ∧ 2 ≤ w 40 ∧
  ∀ n g a b_, PEqualNP.Outside.L_meta_11157_aux.circuit.gates[n]? = some g → g.inputs = [a, b_] →
  (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + n) ≤ w a + w b_) ∧
  (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + n) ≤ min (w a) (w b_)) := by
  use PEqualNP.Outside.L_meta_11157_aux.wire
  constructor
  · decide
  · intro n g a b_ hg hgb
    dsimp only [PEqualNP.Outside.L_meta_11157_aux.circuit] at hg
    rcases hg with (r1|r2|r3|r4|r5|r6|r7|r8|r9|r10|r11|r12|r13|r14|r15|r16|r17|r18|r19|r20|r21|r22|r23|r24|r25|r26|r27)
    <;> (try contradiction) <;> (try split) <;> (try norm_num) <;> (try exact hgb) <;>
      (try decide)

theorem PEqualNP.Outside.L_meta_11157 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((14 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((14 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7)) := by
  refine ⟨PEqualNP.Outside.L_meta_11157_aux.circuit, ?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_11157_aux.ab.1
  · exact PEqualNP.Outside.L_meta_11157_aux.ab.2
  · intro x; exact PEqualNP.Outside.L_meta_11157_aux.eq x
  · intro b
    obtain ⟨w, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_meta_11157_aux.wire b
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · exact h1
    · exact h2
    · exact (h3 : 2 ≤ w 40)
    · intro n g a b_ hg hgb
      exact h4 n g a b_ hg hgb
