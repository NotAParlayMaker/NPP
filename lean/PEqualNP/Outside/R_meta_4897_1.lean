import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP

-- The empty incidence is charged by the empty cover. A circuit with no gates is a
-- separate case. A nonempty incidence with at least one gate is split on whether
-- the first gate is AND or OR.
theorem PEqualNP.Outside.R_meta_4897_1
    (hEmpty :
      ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ (a b : Fin n) (c d : Fin m), a ≠ b → c ≠ d →
        ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
      TopForm.IsAO2 (n + m) C →
      (∀ x : Fin (n + m) → Bool,
        circuitFun (n + m) C x =
          decide (∃ (p : Fin n) (l : Fin m),
            (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      ReadK.IsReadK (n + m) C 1 →
      E = ∅ →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card ≤ C.size + 1)
    (hNil :
      ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ (a b : Fin n) (c d : Fin m), a ≠ b → c ≠ d →
        ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
      TopForm.IsAO2 (n + m) C →
      (∀ x : Fin (n + m) → Bool,
        circuitFun (n + m) C x =
          decide (∃ (p : Fin n) (l : Fin m),
            (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      ReadK.IsReadK (n + m) C 1 →
      E.Nonempty → C.gates = [] →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card ≤ C.size + 1)
    (hAND :
      ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ (a b : Fin n) (c d : Fin m), a ≠ b → c ≠ d →
        ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
      TopForm.IsAO2 (n + m) C →
      (∀ x : Fin (n + m) → Bool,
        circuitFun (n + m) C x =
          decide (∃ (p : Fin n) (l : Fin m),
            (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      ReadK.IsReadK (n + m) C 1 →
      E.Nonempty →
      (∀ g M, C.gates = g :: M → g.op = GateOp.and) →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card ≤ C.size + 1)
    (hOR :
      ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ (a b : Fin n) (c d : Fin m), a ≠ b → c ≠ d →
        ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
      TopForm.IsAO2 (n + m) C →
      (∀ x : Fin (n + m) → Bool,
        circuitFun (n + m) C x =
          decide (∃ (p : Fin n) (l : Fin m),
            (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      ReadK.IsReadK (n + m) C 1 →
      E.Nonempty →
      (∀ g M, C.gates = g :: M → g.op = GateOp.or) →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → PEqualNP.ReadK.IsReadK (x1 + x2) x4 (1 : ℕ) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C hC4 hAO hfun hread
  refine Or.elim (Classical.em (E = ∅)) ?empty ?ne
  · intro hE
    exact hEmpty n m E C hC4 hAO hfun hread hE
  · intro hEne
    have hne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEne
    refine Or.elim (Classical.em (C.gates = [])) ?nil ?cons
    · intro hgs
      exact hNil n m E C hC4 hAO hfun hread hne hgs
    · intro hnn
      refine Exists.elim (List.exists_cons_of_ne_nil hnn) (fun g hg =>
        Exists.elim hg (fun M hgs => ?split))
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or :=
        hAO.1 g (hgs ▸ List.mem_cons_self)
      have hall (op : GateOp) (hopg : g.op = op) :
          ∀ g' M', C.gates = g' :: M' → g'.op = op :=
        fun g' M' heq =>
          (List.cons.inj (heq.symm.trans hgs)).1 ▸ hopg
      exact Or.elim hop
        (fun ha => hAND n m E C hC4 hAO hfun hread hne (hall GateOp.and ha))
        (fun hor => hOR n m E C hC4 hAO hfun hread hne (hall GateOp.or hor))
