import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Close the two raw wires under OR gates. A certificate leaves an unmarked
-- operand at each AND gate, including those arbitrarily deep in the circuit.
theorem PEqualNP.Outside.R_meta_4061_827
    (sound : ∀ (n : Nat) (C : Circuit), AndOrOnly C → ∀ (marked : Nat → Prop) (x : Fin n → Bool),
      (∀ i, x i = true → marked i.val) → (∀ j < C.gates.length, let g := gateAt C j;
        (g.op = .or → ∀ w ∈ g.inputs, marked w → marked (n+j)) ∧
        (g.op = .and → ∃ w ∈ g.inputs, ¬ marked w)) →
      ∀ j < C.gates.length, (gateAt C j).op = .and → gateVal n C j x = false)
    (cert : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ y : Fin 26, y = 1 ∨ y = 14 → ∃ marked : Nat → Prop,
      marked 0 ∧ marked y.val ∧ (∀ j < x4.gates.length, let g := gateAt x4 j;
        (g.op = .or → ∀ w ∈ g.inputs, marked w → marked (26+j)) ∧
        (g.op = .and → ∃ w ∈ g.inputs, ¬ marked w))) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x9 : Fin (26 : ℕ)), x9 = (0 : Fin (26 : ℕ)) ∨ x9 = (1 : Fin (26 : ℕ)) ∨ x9 = (14 : Fin (26 : ℕ)) → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x9) = Bool.false := by
  intro G _ graph C least j hj hop y hy
  have choose (z : Fin 26) (hz : z = 1 ∨ z = 14) (hyz : y = 0 ∨ y = z) : gateVal 26 C j (pairInput 0 y) = false := by
    obtain ⟨marked,h0,hz',closed⟩ := cert G graph C least z hz
    apply sound 26 C least.1.1 marked (pairInput 0 y) _ closed j hj hop
    intro i hi
    have hit : i = 0 ∨ i = y := by exact of_decide_eq_true hi
    rcases hit with rfl | rfl
    · exact h0
    · rcases hyz with rfl | rfl
      · exact h0
      · exact hz'
  rcases hy with h | h | h
  · exact choose 1 (Or.inl rfl) (Or.inl h)
  · exact choose 1 (Or.inl rfl) (Or.inr h)
  · exact choose 14 (Or.inr rfl) (Or.inr h)
