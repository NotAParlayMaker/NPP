import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1601

theorem no4 {m : ℕ} (H : SimpleGraph (Fin m))
    (hgirth : ∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) :
    ∀ a b c d : Fin m, a ≠ c → b ≠ d → ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
  rintro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
  have h := hgirth a (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
    (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))) (by
    rw [SimpleGraph.Walk.isCycle_def]
    have h1 := hab.ne
    have h2 := hbc.ne
    have h3 := hcd.ne
    have h4 := hda.ne
    refine ⟨?_, ?_, ?_⟩
    · rw [SimpleGraph.Walk.isTrail_def]
      simp [Sym2.eq_iff]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> (try intro h) <;> (try intro h') <;> (try subst h) <;> simp_all <;> tauto
    · simp
    · simp
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> (try intro h) <;> (try subst h) <;> simp_all <;> tauto)
  simp at h

end PEqualNP.Outside.L_meta_1601

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro hyp m H _ D hmono hfun hgirth hclean
  obtain ⟨S, hS, hcard⟩ := hyp m H (PEqualNP.Outside.L_meta_1601.no4 H hgirth) D.gates D.output
    (by
      intro g hg
      have h := hmono g hg
      simpa using h)
    (by
      intro x
      have h := congrFun hfun x
      simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun] using h)
    (by
      intro i x hop hw
      have h := hclean i.1 i.2 (by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hop) x hw
      simpa [PEqualNP.MetaComplexity.NestedCover.graphFun] using h)
  refine ⟨S, hS, ?_, ?_⟩
  · simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hcard
  · have : H.edgeFinset.card + S.card ≤ D.gates.length + 1 := hcard
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
