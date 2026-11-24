import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4921_682
    (disjunctions : ∀ (q N : ℕ) (lines : Fin N → Finset (Fin N)),
      (∀ l, (lines l).card = q+1) →
      ∃ D : Circuit, D.size ≤ N*q ∧
        (∀ g ∈ D.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
        ∀ l, ∃ w : ℕ, ∀ p : Fin N,
          (D.wires (List.ofFn (fun i : Fin N => decide (i=p)))).getD w false =
            decide (p ∈ lines l))
    (mixedBudget : ∀ (q N : ℕ) (lines : Fin N → Finset (Fin N)),
      (∀ l, (lines l).card = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, p ∈ lines l ∧ r ∈ lines l) →
      ∀ D : Circuit, Monotone2 D → ReadsBack N D →
      (∀ l, ∃ w : ℕ,
        (D.wires (List.ofFn (fun i : Fin N => decide (i ∉ lines l)))).getD w false = false ∧
        ∀ p ∈ lines l, (D.wires (List.ofFn (fun i : Fin N => decide (i=p)))).getD w false = true) →
      N*q ≤ D.size)
    (extract : ∀ (q N : ℕ) (lines : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q^2+q+1 → (∀ l, (lines l).card = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, p ∈ lines l ∧ r ∈ lines l) → Monotone2 C →
      (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        circuitFun (N+N) C x = decide (∃ p l, p ∈ lines l ∧
          x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) →
      ∃ D : Circuit, D.size ≤ 100*C.size ∧ Monotone2 D ∧ ReadsBack N D ∧
        ∀ l, ∃ w : ℕ,
          (D.wires (List.ofFn (fun i : Fin N => decide (i ∉ lines l)))).getD w false = false ∧
          ∀ p ∈ lines l, (D.wires (List.ofFn (fun i : Fin N => decide (i=p)))).getD w false = true) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x10 : Fin (x2 + x2) → Bool), Fintype.card { x11 : Fin x2 // x10 (Fin.natAdd x2 x11) = Bool.true } ≤ x1 → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x10 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x12 ∈ x3 x13 ∧ x10 (Fin.castAdd x2 x12) = Bool.true ∧ x10 (Fin.natAdd x2 x13) = Bool.true)) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x11.size ≤ (100 : ℕ) * x4.size ∧ (∀ x12 ∈ x11.gates, x12.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x12.inputs.length ≤ (2 : ℕ)) ∧ ∀ (x12 : Fin x2), ∃ (x13 : ℕ), ∀ (x14 : Fin x2), (x11.wires (List.ofFn fun (x15 : Fin x2) => Decidable.decide (x15 = x14))).getD x13 Bool.false = Decidable.decide (x14 ∈ x3 x12) := by
  intro q N lines C hq hN hcard hunique hmono hfun
  obtain ⟨D, hsizeD, hmonoD, hbackD, houtputs⟩ := extract q N lines C hq hN hcard hunique hmono hfun
  have bound := (mixedBudget q N lines hcard hunique D hmonoD hbackD houtputs).trans hsizeD
  obtain ⟨E, hsizeE, horE, houtE⟩ := disjunctions q N lines hcard
  exact ⟨E,hsizeE.trans bound,horE,houtE⟩
