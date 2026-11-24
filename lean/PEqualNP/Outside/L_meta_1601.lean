import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1601

theorem no4 {m : ℕ} (H : SimpleGraph (Fin m))
    (hg : ∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) :
    ∀ a b c d : Fin m, a ≠ c → b ≠ d → ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
  intro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def]
    have h1 := hab.ne
    have h2 := hbc.ne
    have h3 := hcd.ne
    have h4 := hda.ne
    refine ⟨?_, ?_⟩
    · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, List.nodup_nil]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro (h | h | h | h) <;> simp_all
      · rintro (h | h | h) <;> simp_all
      · rintro (h | h) <;> simp_all
      · simp_all
    · simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
      intro h
      rcases h with (⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩) | h <;> simp_all
  have := hg a _ hcyc
  simp at this

end PEqualNP.Outside.L_meta_1601

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro hyp m H _ D hmono hfun hgirth hclean
  have hlegal : ∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  have heval : ∀ x : Fin m → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) = decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    have := congrFun hfun x
    simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun] using this
  have hcl : ∀ (i : Fin D.gates.length) (x : Fin m → Bool), (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩ (List.ofFn x)).getD (m + (i : ℕ)) false = true → ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hop hw
    have hat : PEqualNP.MetaComplexity.NestedCover.gateAt D i = D.gates.get i := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD]
    have h := hclean i i.isLt (hat ▸ hop) x hw
    simpa [PEqualNP.MetaComplexity.NestedCover.graphFun] using h
  obtain ⟨T, hT, hcard⟩ := hyp m H (PEqualNP.Outside.L_meta_1601.no4 H hgirth) D.gates D.output hlegal heval hcl
  refine ⟨T, hT, ?_, ?_⟩
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hcard
  · have : H.edgeFinset.card + T.card ≤ D.size + 1 := by
      simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hcard
    omega
