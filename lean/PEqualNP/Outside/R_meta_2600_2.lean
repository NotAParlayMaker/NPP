import Mathlib
import PEqualNP.Defs

-- Unfolding counts gate occurrences with multiplicity rather than physical gates.
-- When unfolding duplicates at least two gates, seek a vertex restriction
-- saving five physical gates. The minor bound is shared with the prior cut.
theorem PEqualNP.Outside.R_meta_2600_2
    (formulaSize : ∀ C, (fun (C : PEqualNP.CircuitLowerBounds.Circuit) => ∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j) C → (fun (C : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b : Fin 13, (a=b ∨ a=b+1 ∨ a=b+3 ∨ a=b+9) ∧ x (Fin.castAdd 13 a)=true ∧ x (Fin.natAdd 13 b)=true) C → 64 ≤ (fun (C : PEqualNP.CircuitLowerBounds.Circuit) => (C.gates.foldl (fun (w : List ℕ) g => w ++ [w.getD (g.inputs.getD 0 0) 0 + w.getD (g.inputs.getD 1 0) 0 + 1]) (List.replicate 26 0)).getD C.output 0) C)
    (minusVertex : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin 26), PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 26 → Bool, x v = false → (C.eval (List.ofFn x) = true ↔ ∃ a b : Fin 13, (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))) ∧ x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true)) → 58 ≤ C.size)
    (restrictShared : ∀ C, (fun (C : PEqualNP.CircuitLowerBounds.Circuit) => ∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j) C → (fun (C : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ a b : Fin 13, (a=b ∨ a=b+1 ∨ a=b+3 ∨ a=b+9) ∧ x (Fin.castAdd 13 a)=true ∧ x (Fin.natAdd 13 b)=true) C → C.size ≤ 62 → C.size + 2 ≤ (fun (C : PEqualNP.CircuitLowerBounds.Circuit) => (C.gates.foldl (fun (w : List ℕ) g => w ++ [w.getD (g.inputs.getD 0 0) 0 + w.getD (g.inputs.getD 1 0) 0 + 1]) (List.replicate 26 0)).getD C.output 0) C → ∃ (v : Fin 26) (D : PEqualNP.CircuitLowerBounds.Circuit), D.size + 5 ≤ C.size ∧ PEqualNP.MetaComplexity.Monotone2 D ∧ ∀ x : Fin 26 → Bool, x v = false → D.eval (List.ofFn x) = C.eval (List.ofFn x)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  intro C valid computes
  by_contra! small
  have lower := formulaSize C valid computes
  obtain ⟨v,D,save,mono,agrees⟩ := restrictShared C valid computes (by omega) (by omega)
  have minor := minusVertex D v mono (fun x hx => by rw [agrees x hx]; exact computes x)
  omega
