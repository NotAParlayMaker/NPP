import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

-- Cut L-meta-2585 into three independent parts:
-- 1. Build a read-1 IsAO2 circuit from any star cover of cost edges + stars - 1.
-- 2. Normalize any IsAO2 circuit for f_I to a least-size one in strict top-OR block form.
-- 3. Show that for C4-free I, every least-size block-form circuit has size at least some star cover.
theorem PEqualNP.Outside.R_meta_2585_427
    (starCircuit :
      ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (assign : Fin P → Fin L → Bool),
        let f : (Fin (P + L) → Bool) → Bool := fun z =>
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)
        let edges : ℕ := (Finset.univ.filter fun pl : Fin P × Fin L => I pl.1 pl.2).card
        let stars : ℕ :=
          (Finset.univ.filter fun p : Fin P => ∃ l : Fin L, I p l ∧ assign p l = true).card +
          (Finset.univ.filter fun l : Fin L => ∃ p : Fin P, I p l ∧ assign p l = false).card
        ∃ D : Circuit, IsAO2 (P + L) D ∧ (∀ y, circuitFun (P + L) D y = f y) ∧
          D.size ≤ edges + stars - 1 ∧ IsReadK (P + L) D 1)
    (toBlockForm :
      ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit),
        let f : (Fin (P + L) → Bool) → Bool := fun z =>
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)
        IsAO2 (P + L) C → (∀ z, circuitFun (P + L) C z = f z) →
        ∃ C' : Circuit, IsAO2 (P + L) C' ∧ (∀ z, circuitFun (P + L) C' z = f z) ∧
          C'.size ≤ C.size ∧
          (∀ C'' : Circuit, IsAO2 (P + L) C'' → (∀ z, circuitFun (P + L) C'' z = f z) → C'.size ≤ C''.size) ∧
          (∀ j < C'.gates.length, ∀ g : Gate, C'.gates[j]? = some g →
            (∃ w ∈ g.inputs, ∀ z : Fin (P + L) → Bool, (C'.wires (List.ofFn z)).getD w false = true → f z = true) →
            g.op = GateOp.or ∧ ∀ z : Fin (P + L) → Bool, (C'.wires (List.ofFn z)).getD (P + L + j) false = true → f z = true))
    (blockCoverBound :
      ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C' : Circuit),
        let f : (Fin (P + L) → Bool) → Bool := fun z =>
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)
        (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        IsAO2 (P + L) C' → (∀ z, circuitFun (P + L) C' z = f z) →
        (∀ C'' : Circuit, IsAO2 (P + L) C'' → (∀ z, circuitFun (P + L) C'' z = f z) → C'.size ≤ C''.size) →
        (∀ j < C'.gates.length, ∀ g : Gate, C'.gates[j]? = some g →
          (∃ w ∈ g.inputs, ∀ z : Fin (P + L) → Bool, (C'.wires (List.ofFn z)).getD w false = true → f z = true) →
          g.op = GateOp.or ∧ ∀ z : Fin (P + L) → Bool, (C'.wires (List.ofFn z)).getD (P + L + j) false = true → f z = true) →
        ∃ assign : Fin P → Fin L → Bool,
          (Finset.univ.filter fun pl : Fin P × Fin L => I pl.1 pl.2).card +
          ((Finset.univ.filter fun p : Fin P => ∃ l : Fin L, I p l ∧ assign p l = true).card +
           (Finset.univ.filter fun l : Fin L => ∃ p : Fin P, I p l ∧ assign p l = false).card) - 1 ≤ C'.size) :
    ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  intro P L I _ C hNo4 hAO hFun
  obtain ⟨C', hAO', hFun', hLeC, hLeast, hBlock⟩ := toBlockForm P L I C hAO hFun
  obtain ⟨assign, hBound⟩ := blockCoverBound P L I C' hNo4 hAO' hFun' hLeast hBlock
  obtain ⟨D, hDAO, hDFun, hDSize, hDR1⟩ := starCircuit P L I assign
  exact ⟨D, hDAO, hDFun, (hDSize.trans hBound).trans hLeC, hDR1⟩
