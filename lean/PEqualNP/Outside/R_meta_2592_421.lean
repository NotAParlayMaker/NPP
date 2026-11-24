import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A first inverter cannot be the output. If an output AND or OR reads it directly
from an earlier wire, the inverter takes a constant value. -/
theorem PEqualNP.Outside.R_meta_2592_421
    (extremes : ∀ (n : ℕ) (C : Circuit), FanInTwo C →
      C.eval (List.replicate n false) = false → C.eval (List.replicate n true) = true →
      ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → g.op = .not →
        (∀ h ∈ C.gates.take k, h.op ≠ .not) →
        C.output ≠ n+k ∧
        ∀ (j : ℕ) (o : Gate), k < j → C.output = n+j → C.gates[j]? = some o →
          (o.op = .and ∨ o.op = .or) → n+k ∈ o.inputs →
          ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+k) false =
            (C.wires (List.replicate n false)).getD (n+k) false)
    (remaining : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (19 : ℕ) → (∃ x4 ∈ x1.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ (k : ℕ) (g : Gate), x1.gates[k]? = some g → g.op = .not →
        (∀ h ∈ x1.gates.take k, h.op ≠ .not) →
        x1.output ≠ 10+k ∧
        ∀ (j : ℕ) (o : Gate), k < j → x1.output = 10+j → x1.gates[j]? = some o →
          (o.op = .and ∨ o.op = .or) → 10+k ∈ o.inputs →
          ∀ x : Fin 10 → Bool, (x1.wires (List.ofFn x)).getD (10+k) false =
            (x1.wires (List.replicate 10 false)).getD (10+k) false) →
      ¬∀ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (19 : ℕ) → (∃ x4 ∈ x1.gates, x4.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ¬∀ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C hf hsize hn heval
  have hz := heval (fun _ => false)
  have ho := heval (fun _ => true)
  change C.eval (List.replicate 10 false) = false at hz
  change C.eval (List.replicate 10 true) = true at ho
  exact remaining C hf hsize hn (extremes 10 C hf hz ho) heval
