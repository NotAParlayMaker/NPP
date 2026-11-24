import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1601_aux

lemma noFourCycle_of_girth {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) :
    ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  intro a b c d hac hbd h
  obtain ⟨hab, hbc, hcd, hda⟩ := h
  let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hcyc : p.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    refine ⟨?_, by simp [p]⟩
    have h1 : b ≠ c := G.ne_of_adj hbc
    have h2 : b ≠ d := hbd
    have h3 : b ≠ a := (G.ne_of_adj hab).symm
    have h4 : c ≠ d := G.ne_of_adj hcd
    have h5 : c ≠ a := hac.symm
    have h6 : d ≠ a := G.ne_of_adj hda
    simp only [p, SimpleGraph.Walk.tail_cons]
    simp [h1, h2, h3, h4, h5, h6]
  have hl := h a p hcyc
  simp [p] at hl

end PEqualNP.Outside.L_meta_1601_aux

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  intro H1 m H _ D hMono hFun hGirth hSound
  have hNo4 := PEqualNP.Outside.L_meta_1601_aux.noFourCycle_of_girth H hGirth
  obtain ⟨T, hcov, hb⟩ := H1 m H hNo4 D.gates D.output
    (fun g hg => ⟨(hMono g hg).1, (hMono g hg).2⟩)
    (by
      intro x
      have hx := congrFun hFun x
      simp only [PEqualNP.MetaComplexity.circuitFun] at hx
      simpa [PEqualNP.MetaComplexity.NestedCover.graphFun] using hx)
    (by
      intro i x hi hw
      have hval : PEqualNP.EdgeOwnership.gateVal m D i.val x = true := hw
      have hi' : (PEqualNP.MetaComplexity.NestedCover.gateAt D i.val).op
          = PEqualNP.CircuitLowerBounds.GateOp.and := by
        simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hi
      have h := hSound i.val i.isLt hi' x hval
      simpa [PEqualNP.MetaComplexity.NestedCover.gateAt,
        PEqualNP.MetaComplexity.NestedCover.graphFun] using h)
  have hb' : H.edgeFinset.card + T.card ≤ D.size + 1 := by
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hb
  refine ⟨T, hcov, hb', ?_⟩
  omega
