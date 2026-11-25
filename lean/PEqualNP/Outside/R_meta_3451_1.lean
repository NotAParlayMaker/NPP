import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- Reduction for L-meta-3451 (4-cycle-free incidence cleaning).

The desk statement splits in two, following its own sketch: first make every AND
false at single inputs, then make every AND false at one point with one
non-incident line. Each hypothesis below is a consequence of the desk statement
itself (apply the statement to the hypothesis input), so neither is stronger
than the goal. The assembly is pure chaining: apply `hSingle`, then `hPair`. -/
theorem PEqualNP.Outside.R_meta_3451_1
    (hSingle :
      ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
        (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        Monotone2 C → ReadsBack (N + N) C →
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
          (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
          (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
            (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
            ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false))
    (hPair :
      ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit),
        (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        Monotone2 D → ReadsBack (N + N) D →
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
          ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) →
        ∃ D' : Circuit, Monotone2 D' ∧ ReadsBack (N + N) D' ∧ D'.size ≤ D.size ∧
          (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D' z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
          (∀ j < D'.gates.length, (gateAt D' j).op = GateOp.and →
            ∀ p0 l0 : Fin N, ¬ I p0 l0 →
              (D'.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧
          (∀ j < D'.gates.length, (gateAt D' j).op = GateOp.and →
            (∀ p : Fin N, (D'.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
            ∀ l : Fin N, (D'.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I _ C hC4 hMono hRB hFun
  obtain ⟨D1, h1m, h1rb, h1size, h1fun, h1clean⟩ := hSingle N I C hC4 hMono hRB hFun
  obtain ⟨D2, h2m, h2rb, h2size, h2fun, h2pair, h2single⟩ := hPair N I D1 hC4 h1m h1rb h1fun h1clean
  exact ⟨D2, h2m, h2rb, h2size.trans h1size, h2fun, h2pair, h2single⟩
