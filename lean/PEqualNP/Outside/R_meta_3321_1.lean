import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Step one cleans every AND gate at no cost.
-- Step two, starting from a clean circuit, makes every AND gate false at one-hot inputs,
-- keeping the gates clean and the size no larger.
theorem PEqualNP.Outside.R_meta_3321_1
    (clean : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C → ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ z : Fin (N + N) → Bool,
          (D.wires (List.ofFn z)).getD (N + N + j) false = true →
          (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD
              (N + N + j) false = true ∨
          (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD
              (N + N + j) false = true ∨
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (oneHot : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C → ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ z : Fin (N + N) → Bool,
          (C.wires (List.ofFn z)).getD (N + N + j) false = true →
          (C.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD
              (N + N + j) false = true ∨
          (C.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD
              (N + N + j) false = true ∨
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → ∀ z : Fin (N + N) → Bool,
          (D.wires (List.ofFn z)).getD (N + N + j) false = true →
          (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD
              (N + N + j) false = true ∨
          (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD
              (N + N + j) false = true ∨
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) =>
            decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
          ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) =>
            decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin (N + N) → Bool, (D.wires (List.ofFn z)).getD (N + N + j) false = true → (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨ (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I _ C noCycle mono reads computes
  obtain ⟨D1, m1, r1, s1, c1, k1⟩ := clean N I C noCycle mono reads computes
  obtain ⟨D, m, r, s, c, k, h⟩ := oneHot N I D1 noCycle m1 r1 c1 k1
  exact ⟨D, m, r, s.trans s1, c, k, h⟩
