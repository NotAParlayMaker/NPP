import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The star forest case reaches the lower bound from the number of essential inputs.
-- The remaining graphs contain an edge whose endpoints both have degree at least two.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_5282_487
    (forest : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b, G.Adj a b → G.degree a = 1 ∨ G.degree b = 1) →
    let evalGraph (x : Fin n → Bool) := decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
    let on (S : Finset (Fin n)) (v : Fin n) := decide (v ∈ S)
    ∃ C : Circuit, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = evalGraph x) ∧
      (∀ D : Circuit, Monotone2 D → (∀ x, D.eval (List.ofFn x) = evalGraph x) → C.size ≤ D.size) ∧
      ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → ∀ S : Finset (Fin n), S.card ≤ 1 →
        (C.wires (List.ofFn (on S))).getD (n+j) false = false
    )
    (remaining : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∃ a b, G.Adj a b ∧ 2 ≤ G.degree a ∧ 2 ≤ G.degree b) →
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
    let evalGraph (x : Fin n → Bool) := decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
    let on (S : Finset (Fin n)) (v : Fin n) := decide (v ∈ S)
    ∃ C : Circuit, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = evalGraph x) ∧
      (∀ D : Circuit, Monotone2 D → (∀ x, D.eval (List.ofFn x) = evalGraph x) → C.size ≤ D.size) ∧
      ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → ∀ S : Finset (Fin n), S.card ≤ 1 →
        (C.wires (List.ofFn (on S))).getD (n+j) false = false) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 ∧ (∀ (x10 : Fin x1 → Bool), x9.eval (List.ofFn x10) = x4 x10) ∧ (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x12 : Fin x1 → Bool), x10.eval (List.ofFn x12) = x4 x12) → x9.size ≤ x10.size) ∧ x6 x9 := by
  intro n G decG
  dsimp only
  intro noTriangle noSquare
  by_cases branching : ∃ a b, G.Adj a b ∧ 2 ≤ G.degree a ∧ 2 ≤ G.degree b
  · exact remaining n G branching noTriangle noSquare
  · apply forest n G
    intro a b ab
    have positive {u v : Fin n} (uv : G.Adj u v) : 0 < G.degree u := by
      change 0 < (G.neighborFinset u).card
      exact Finset.card_pos.mpr ⟨v,(G.mem_neighborFinset _ _).mpr uv⟩
    have ha := positive ab
    have hb := positive ab.symm
    by_cases one : G.degree a = 1
    · exact Or.inl one
    · right
      by_contra! two
      exact branching ⟨a,b,ab,by omega,by omega⟩
