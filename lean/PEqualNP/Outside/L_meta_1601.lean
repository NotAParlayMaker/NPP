import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro hyp m H inst D hmono hfun hgirth hclean
  have h4 : ∀ a b c d : Fin m, a ≠ c → b ≠ d →
      ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
    rintro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
    have hab' : a ≠ b := hab.ne
    have hbc' : b ≠ c := hbc.ne
    have hcd' : c ≠ d := hcd.ne
    have hda' : d ≠ a := hda.ne
    have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.cons_isPath_iff, hbc', hcd', hda', hbd, hab'.symm, hac.symm]
      · simp [hab', hbc', hac, hbd, hab'.symm, hda'.symm]
    have h5 := hgirth a _ hcyc
    simp at h5
  obtain ⟨T, hT, hcard⟩ := hyp m H h4 D.gates D.output
    (by
      intro g hg
      have h1 := hmono g hg
      refine ⟨?_, h1.2⟩
      have h2 := h1.1
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h2)
    (by
      intro x
      have h1 := congrFun hfun x
      simpa [PEqualNP.MetaComplexity.circuitFun,
        PEqualNP.MetaComplexity.NestedCover.graphFun] using h1)
    (by
      intro i x hop hval
      have h1 := hclean i.val i.isLt
        (by
          rw [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ i.isLt]
          exact hop) x hval
      simpa [PEqualNP.MetaComplexity.NestedCover.graphFun] using h1)
  have hsz : D.size = D.gates.length := rfl
  refine ⟨T, hT, ?_, ?_⟩
  · rw [hsz]; exact hcard
  · rw [hsz]; omega
