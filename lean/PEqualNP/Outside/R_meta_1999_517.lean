import Mathlib
import PEqualNP.Defs

-- Cut: clean the circuit on the light inputs, then count (a single-output Nechiporuk count).
-- Light inputs: at most two true bits in x ++ y. On the graph function
-- f = OR over edges ij of (x_i AND y_j), a gate is CLEAN when it is below f on the light
-- inputs: it is false on every single variable, on every pair of left (or of right)
-- variables, and on every non-edge pair x_i, y_j.
-- h1 (the open core, cleaning): a least monotone fan-in-two circuit for f gives, at linear
-- cost, a monotone fan-in-two circuit that agrees with f on the light inputs and whose AND
-- gates are all clean. It follows from the step (the circuit OR over i of x_i AND (OR of the
-- y_j over the neighbours of i) has at most 2 |E| gates and its AND gates are below f), and
-- with h2 it gives the step; so it is exactly as true as the step. Its content is the
-- removal of AND gates that fire on a single variable or on a non-edge pair (intersections of
-- big OR sets, killed later by correctness on heavy inputs). Correctness of the new circuit is
-- only asked on the light inputs; the heavy inputs are used only for the given circuit.
-- h2 (finishable, only light inputs): if every AND gate is clean and the circuit agrees with f
-- on the light inputs, then |E| is at most the number of gates. Proof sketch: since AND gates
-- are false on single variables, the variables that alone turn a wire on are exactly those
-- reached from it through OR gates. For an edge ij follow, from the output, wires true at
-- 1_ij and false at 1_i and at 1_j: it ends at an AND gate whose operands are turned on by x_i
-- and y_j alone. By cleanness and monotonicity all pairs between the operand sets are edges,
-- so (no 4-cycle) one operand set is one centre vertex c and the other lies in N(c). An OR gate
-- whose set has two vertices can serve one centre only (two common neighbours otherwise), and
-- expanding the OR gates under the leaf operands of the AND gates of centre c shows that the
-- edges at c number at most those AND gates plus those OR gates. Summing over c gives
-- |E| at most the size. The degree hypotheses are not needed there.
-- The proof below passes to a least circuit (Nat.find) and composes.

theorem PEqualNP.Outside.R_meta_1999_517 (h1 : ∃ (c : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → (∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → x9.size ≤ x10.size) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), List.count Bool.true (List.ofFn x11 ++ List.ofFn x12) ≤ (2 : ℕ) → x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) ∧ (∀ (x15 : ℕ), x15 < x10.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x15).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), List.count Bool.true (List.ofFn x11 ++ List.ofFn x12) ≤ (2 : ℕ) → (x10.wires (List.ofFn x11 ++ List.ofFn x12)).getD (x2 + x3 + x15) Bool.false = Bool.true → ∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) ∧ x10.size ≤ c * (x9.size + (1 : ℕ)))
    (h2 : ∃ (c : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), List.count Bool.true (List.ofFn x11 ++ List.ofFn x12) ≤ (2 : ℕ) → x10.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → (∀ (x15 : ℕ), x15 < x10.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x15).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), List.count Bool.true (List.ofFn x11 ++ List.ofFn x12) ≤ (2 : ℕ) → (x10.wires (List.ofFn x11 ++ List.ofFn x12)).getD (x2 + x3 + x15) Bool.false = Bool.true → ∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true) → ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ c * (x10.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ x1 * (x9.size + (1 : ℕ)) := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  refine ⟨c2 * (c1 + 1), ?_⟩
  intro x2 x3 x4 x5 hL hR hC4 C hmono hfun
  -- a circuit of least size computing the same function
  have hex : ∃ s : ℕ, ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧
      (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), D.eval (List.ofFn x11 ++ List.ofFn x12) =
        Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧
          x12 x14 = Bool.true)) ∧ D.size = s :=
    ⟨C.size, C, hmono, hfun, rfl⟩
  obtain ⟨D, hDm, hDf, hDs⟩ := @Nat.find_spec _ (Classical.decPred _) hex
  have hDmin : ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x10 →
      (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x10.eval (List.ofFn x11 ++ List.ofFn x12) =
        Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧
          x12 x14 = Bool.true)) → D.size ≤ x10.size := by
    intro D' h1' h2'
    rw [hDs]
    exact @Nat.find_min' _ (Classical.decPred _) hex _ ⟨D', h1', h2', rfl⟩
  have hDC : D.size ≤ C.size := hDmin C hmono hfun
  -- the cleaned circuit
  obtain ⟨E, hEm, hEf, hEclean, hEsize⟩ := hc1 x2 x3 x4 hL hR hC4 D hDm hDf hDmin
  -- the count on the cleaned circuit
  have key := hc2 x2 x3 x4 hL hR hC4 E hEm hEf hEclean
  have e1 : c1 * (D.size + 1) ≤ c1 * (C.size + 1) :=
    Nat.mul_le_mul_left c1 (Nat.add_le_add_right hDC 1)
  have e2 : E.size + 1 ≤ (c1 + 1) * (C.size + 1) := by
    have : (c1 + 1) * (C.size + 1) = c1 * (C.size + 1) + (C.size + 1) := by ring
    omega
  calc ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card
        ≤ c2 * (E.size + 1) := key
    _ ≤ c2 * ((c1 + 1) * (C.size + 1)) := Nat.mul_le_mul_left c2 e2
    _ = c2 * (c1 + 1) * (C.size + 1) := by ring
