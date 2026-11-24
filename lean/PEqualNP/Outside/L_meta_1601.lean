import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro bound m H inst D mono computes girth clean
  have square : ∀ a b c d : Fin m, a ≠ c → b ≠ d →
      ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
    rintro a b c d ac bd ⟨ab, bc, cd, da⟩
    let p : H.Walk a a := .cons ab (.cons bc (.cons cd (.cons da .nil)))
    have cycle : p.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
      simp [p, SimpleGraph.Walk.isPath_def, ab.ne, bc.ne, cd.ne, da.ne,
        ac, bd, ab.ne.symm, bc.ne.symm, cd.ne.symm, da.ne.symm, ac.symm, bd.symm]
    have length := girth a p cycle
    change 5 ≤ 4 at length
    omega
  have eval (x : Fin m → Bool) : D.eval (List.ofFn x) =
      decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
    simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun]
      using congrFun computes x
  apply Exists.elim (bound m H square D.gates D.output (fun g hg => mono g hg) eval ?_)
  · rintro S ⟨cover, cost⟩
    refine ⟨S, cover, cost, ?_⟩
    change H.edgeFinset.card ≤ D.gates.length + 1
    omega
  · intro i x op on
    have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt D i.val).op =
        PEqualNP.CircuitLowerBounds.GateOp.and := by
      simpa [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ i.isLt]
        using op
    have hit := clean i.val i.isLt hop x on
    simpa [PEqualNP.MetaComplexity.NestedCover.graphFun] using hit
