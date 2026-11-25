import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

-- The first step reconstructs the full edge function and pays for the two output taps.
-- The second step asks whether a minimum program can witness each flag without rereading an input.
-- The third step charges a read-once program for the fifty-two edges and a perfect matching.
theorem PEqualNP.Outside.R_meta_1990_619
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →
      ∃ D : Circuit, IsAO2 26 D ∧ D.size ≤ x1.size + 1 ∧ (∀ z : Fin 26 → Bool, circuitFun 26 D z = decide
        (∃ p l : Fin 13, (p.val + l.val) % 13 ∈ [0,1,3,9] ∧
          z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true)))
    (h2 : ∀ C : Circuit, IsAO2 26 C → (∀ z : Fin 26 → Bool, circuitFun 26 C z = decide
        (∃ p l : Fin 13, (p.val + l.val) % 13 ∈ [0,1,3,9] ∧
          z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true)) →
      ∃ D : Circuit, IsAO2 26 D ∧ (∀ z : Fin 26 → Bool, circuitFun 26 D z = decide
        (∃ p l : Fin 13, (p.val + l.val) % 13 ∈ [0,1,3,9] ∧
          z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true)) ∧ D.size ≤ C.size ∧ IsReadK 26 D 1)
    (h3 : ∀ D : Circuit, IsAO2 26 D → (∀ z : Fin 26 → Bool, circuitFun 26 D z = decide
        (∃ p l : Fin 13, (p.val + l.val) % 13 ∈ [0,1,3,9] ∧
          z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true)) →
      IsReadK 26 D 1 → 64 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by
  intro C outputs monotone taps tests
  obtain ⟨A, ha, budget, correctA⟩ := h1 C outputs monotone taps tests
  obtain ⟨B, hb, correctB, cost, read⟩ := h2 A ha correctA
  have lower := h3 B hb correctB read
  omega
