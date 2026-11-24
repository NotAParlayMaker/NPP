import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP

-- The empty incidence is charged by the empty cover. A nonempty incidence needs at least
-- one gate, and that case is split on whether the first gate is AND or OR.
theorem PEqualNP.Outside.R_meta_4897_1
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
  by_cases hE : E = ∅
  · refine ⟨∅, ∅, ?_, ?_⟩
    · intro e he
      exact (Finset.notMem_empty e (hE ▸ he)).elim
    · simp [hE, Finset.card_empty]
  have hne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
  have hsz : 0 < C.size := by
    by_contra hnon
    have hz : C.size = 0 := by omega
    have hgs : C.gates = [] := List.length_eq_zero_iff.mp hz
    have hw (x : Fin (n + m) → Bool) :
        circuitFun (n + m) C x = (List.ofFn x).getD C.output false := by
      simp [circuitFun, Circuit.eval, Circuit.wires, hgs]
    obtain ⟨⟨p, l⟩, hp⟩ := hne
    let xEdge : Fin (n + m) → Bool :=
      fun i => decide (i = Fin.castAdd m p ∨ i = Fin.natAdd n l)
    have hp_edge : xEdge (Fin.castAdd m p) = true := by
      simp [xEdge]
    have hl_edge : xEdge (Fin.natAdd n l) = true := by
      simp [xEdge]
    have htrue : circuitFun (n + m) C xEdge = true := by
      rw [hfun xEdge, decide_eq_true_eq]
      exact ⟨p, l, hp, hp_edge, hl_edge⟩
    by_cases ho : C.output < n + m
    · let i : Fin (n + m) := ⟨C.output, ho⟩
      let y : Fin (n + m) → Bool := fun j => decide (j = i)
      have hy : circuitFun (n + m) C y = true := by
        rw [hw]
        have hlen : C.output < (List.ofFn y).length := by
          simpa [List.length_ofFn] using ho
        rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn hlen]
        simp [y, i]
      have hF : circuitFun (n + m) C y = false := by
        rw [hfun y, decide_eq_false_iff_not]
        intro ⟨q, r, hq, hqy, hry⟩
        have hq' : Fin.castAdd m q = i := by
          have : decide (Fin.castAdd m q = i) = true := by
            simpa [y] using hqy
          exact of_decide_eq_true this
        have hr' : Fin.natAdd n r = i := by
          have : decide (Fin.natAdd n r = i) = true := by
            simpa [y] using hry
          exact of_decide_eq_true this
        have hlt : (Fin.castAdd m q).val < n := by
          rw [Fin.val_castAdd]
          exact q.isLt
        have hge : n ≤ (Fin.natAdd n r).val := by
          rw [Fin.val_natAdd]
          exact Nat.le_add_right _ _
        have : (Fin.castAdd m q).val = (Fin.natAdd n r).val := by
          rw [hq', hr']
        omega
      exact Bool.false_ne_true (hF.symm.trans hy)
    · have hfalse : circuitFun (n + m) C xEdge = false := by
        rw [hw]
        apply List.getD_eq_default
        simpa [List.length_ofFn] using Nat.not_lt.mp ho
      exact Bool.false_ne_true (hfalse.symm.trans htrue)
  cases hgs : C.gates with
  | nil =>
    have : C.size = 0 := by simp [Circuit.size, hgs]
    omega
  | cons g M =>
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or :=
      (hAO.1 g (by simp [hgs]))
    have hall (op : GateOp) (hopg : g.op = op) :
        ∀ g' M', C.gates = g' :: M' → g'.op = op := by
      intro g' M' heq
      have : g' = g := by
        rw [hgs] at heq
        exact (List.cons.inj heq).1.symm
      exact this ▸ hopg
    rcases hop with ha | hor
    · exact hAND n m E C hC4 hAO hfun hread hne (hall GateOp.and ha)
    · exact hOR n m E C hC4 hAO hfun hread hne (hall GateOp.or hor)
