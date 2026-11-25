import Mathlib
import PEqualNP.Defs

-- A cut of L-meta-6530 by the presence of an AND gate.  A circuit with no AND gate is a single
-- OR of the input wires, so the negative side is a genuinely restricted class and the
-- positive side is the case where the AND structure carries the argument.
theorem PEqualNP.Outside.R_meta_6530_733
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (∃ (j : Fin x1.gates.length), (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (¬ (∃ (j : Fin x1.gates.length), (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (63 : ℕ) ≤ x1.size := by
  intro x1 x2 hp1 hp2 hp3
  by_cases h : (∃ (j : Fin x1.gates.length), (x1.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  · exact h1 x1 x2 hp1 hp2 hp3 h
  · exact h2 x1 x2 hp1 hp2 hp3 h
