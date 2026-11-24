import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.TopForm

-- A finite bank need only store a sound rectangle for each edge. Outputs of
-- unselected gates and the Boolean function of the bank can be arbitrary.
-- The cover construction is the checked child L_meta_4320 of PR #4612.
theorem PEqualNP.Outside.R_meta_1904_314
    (count : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    let bank (D : Circuit) :=
      IsAO2 n D ∧
      (∀ k < D.size, D.output = n+k ∨ ∃ j < D.size, n+k ∈ (gateAt D j).inputs) ∧
      ∀ u v, G.Adj u v → ∃ j < D.size, (gateAt D j).op = GateOp.and ∧
        let R (w : ℕ) (i : Fin n) := readsAtMost (⟨D.gates,w⟩ : Circuit) n [i.val] 1 = true
        let P (a b : Fin n) := R (opnd D j 0) a ∧ R (opnd D j 1) b
        (P u v ∨ P v u) ∧ ∀ a b, P a b → G.Adj a b
    (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
    G.edgeFinset.Nonempty → ∀ D, bank D → ∃ T : Finset (Fin n),
      (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card ≤ D.size + 1)
    (compact : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    let bank (D : Circuit) :=
      IsAO2 n D ∧
      (∀ k < D.size, D.output = n+k ∨ ∃ j < D.size, n+k ∈ (gateAt D j).inputs) ∧
      ∀ u v, G.Adj u v → ∃ j < D.size, (gateAt D j).op = GateOp.and ∧
        let R (w : ℕ) (i : Fin n) := readsAtMost (⟨D.gates,w⟩ : Circuit) n [i.val] 1 = true
        let P (a b : Fin n) := R (opnd D j 0) a ∧ R (opnd D j 1) b
        (P u v ∨ P v u) ∧ ∀ a b, P a b → G.Adj a b
    (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬G.Adj c a) →
    (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
    G.edgeFinset.Nonempty → ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, D.size ≤ C.size ∧ bank D)
    (coverBuilder : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)),
  (∀ a b, G.Adj a b → a ∈ U ∨ b ∈ U) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
      decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true)) ∧
    D.size ≤ G.edgeFinset.card + U.card - 1 ∧
    ∀ j g, D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
        ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x1 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x6.size ≤ x7.size) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  classical
  intro n G inst tri square
  let covers (T : Finset (Fin n)) := ∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T
  let possible (k : ℕ) := ∃ T : Finset (Fin n), covers T ∧ T.card = k
  have feasible : ∃ k, possible k :=
    ⟨_, Finset.univ, fun a _ _ => Or.inl (Finset.mem_univ a), rfl⟩
  obtain ⟨K, hK, szK⟩ := Nat.find_spec feasible
  obtain ⟨D, model, correct, size, clean⟩ := coverBuilder n G K hK
  refine ⟨D, model, correct, ?_, clean⟩
  intro C mono computes
  have target : circuitFun n C = graphFun G ∅ := by
    funext x
    have h := computes x
    change C.eval (List.ofFn x) = (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    simpa using h
  by_cases any : G.edgeFinset.Nonempty
  · obtain ⟨B, small, hB⟩ := compact n G tri square any C mono target
    obtain ⟨T, ht, budget⟩ := count n G square any B hB
    have minK := Nat.find_min' feasible (show possible T.card from ⟨T, ht, rfl⟩)
    omega
  · have zero := Finset.not_nonempty_iff_eq_empty.mp any
    have emptyCover : covers ∅ := by
      intro a b edge
      exact (any ⟨s(a,b), by simpa using edge⟩).elim
    have minK := Nat.find_min' feasible (show possible 0 from ⟨∅, emptyCover, rfl⟩)
    rw [zero, Finset.card_empty] at size
    omega
