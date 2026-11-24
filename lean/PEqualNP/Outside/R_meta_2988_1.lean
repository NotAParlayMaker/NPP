import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2988_1
  (h1 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (x5.output < x2 + x2 ∨ x2 + x2 + x5.size ≤ x5.output) → (∀ (x11 x12 : Fin (x2 + x2)), (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = x11 ∨ x13 = x12)) = Bool.true ↔ ∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ (Fin.castAdd x2 x13 = x11 ∨ Fin.castAdd x2 x13 = x12) ∧ (Fin.natAdd x2 x14 = x11 ∨ Fin.natAdd x2 x14 = x12)) → (3 : ℕ) * x2 ≤ x5.size + (1 : ℕ))
  (h2 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x5.gates[x5.output - (x2 + x2)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x11 x12 : Fin (x2 + x2)), (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = x11 ∨ x13 = x12)) = Bool.true ↔ ∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ (Fin.castAdd x2 x13 = x11 ∨ Fin.castAdd x2 x13 = x12) ∧ (Fin.natAdd x2 x14 = x11 ∨ Fin.natAdd x2 x14 = x12)) → (3 : ℕ) * x2 ≤ x5.size + (1 : ℕ))
  (h3 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x2 + x2 ≤ x5.output → x5.output < x2 + x2 + x5.size → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x5.gates[x5.output - (x2 + x2)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x11 x12 : Fin (x2 + x2)), (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = x11 ∨ x13 = x12)) = Bool.true ↔ ∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ (Fin.castAdd x2 x13 = x11 ∨ Fin.castAdd x2 x13 = x12) ∧ (Fin.natAdd x2 x14 = x11 ∨ Fin.natAdd x2 x14 = x12)) → (3 : ℕ) * x2 ≤ x5.size + (1 : ℕ)) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin (x2 + x2)), (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = x11 ∨ x13 = x12)) = Bool.true ↔ ∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ (Fin.castAdd x2 x13 = x11 ∨ Fin.castAdd x2 x13 = x12) ∧ (Fin.natAdd x2 x14 = x11 ∨ Fin.natAdd x2 x14 = x12)) → (3 : ℕ) * x2 ≤ x5.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hq hx2 hcard huniq hmon heval
  rcases lt_or_ge x5.output (x2 + x2) with hout_lt | hout_ge
  · exact h1 x1 x2 x3 x5 hq hx2 hcard huniq hmon (Or.inl hout_lt) heval
  · rcases lt_or_ge x5.output (x2 + x2 + x5.size) with hlt | hge
    · have hidx : x5.output - (x2 + x2) < x5.gates.length := by
        change x5.output - (x2 + x2) < x5.size
        omega
      obtain ⟨g, hg⟩ : ∃ g, x5.gates[x5.output - (x2 + x2)]? = Option.some g :=
        ⟨x5.gates[x5.output - (x2 + x2)], getElem?_pos x5.gates _ hidx⟩
      rcases (hmon g (List.mem_of_getElem? hg)).1 with hop | hop
      · exact h2 x1 x2 x3 x5 hq hx2 hcard huniq hmon hout_ge hlt ⟨g, hg, hop⟩ heval
      · exact h3 x1 x2 x3 x5 hq hx2 hcard huniq hmon hout_ge hlt ⟨g, hg, hop⟩ heval
    · exact h1 x1 x2 x3 x5 hq hx2 hcard huniq hmon (Or.inr hge) heval
