import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1601

private lemma no_four_cycle_of_girth_five {m : ℕ} (H : SimpleGraph (Fin m))
    (hGirth : ∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) :
    ∀ a b c d : Fin m, a ≠ c → b ≠ d → ¬ (H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a) := by
  intro a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
  have hab_ne : a ≠ b := H.ne_of_adj hab
  have hbc_ne : b ≠ c := H.ne_of_adj hbc
  have hcd_ne : c ≠ d := H.ne_of_adj hcd
  have hda_ne : d ≠ a := H.ne_of_adj hda
  let q : H.Walk a a :=
    SimpleGraph.Walk.cons hab
      (SimpleGraph.Walk.cons hbc
        (SimpleGraph.Walk.cons hcd
          (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))
  have hEdges : q.edges.Nodup := by
    simp only [q, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.nodup_cons, List.mem_cons, List.not_mem_nil, List.mem_nil_iff, or_false, List.nodup_nil,
      not_false_eq_true, and_true, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    · intro h
      rw [Sym2.eq_iff] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      first
      | exact hab_ne h1
      | exact hab_ne h1.symm
      | exact hab_ne h2
      | exact hab_ne h2.symm
      | exact hbc_ne h1
      | exact hbc_ne h1.symm
      | exact hbc_ne h2
      | exact hbc_ne h2.symm
      | exact hcd_ne h1
      | exact hcd_ne h1.symm
      | exact hcd_ne h2
      | exact hcd_ne h2.symm
      | exact hda_ne h1
      | exact hda_ne h1.symm
      | exact hda_ne h2
      | exact hda_ne h2.symm
      | exact hac h1
      | exact hac h1.symm
      | exact hac h2
      | exact hac h2.symm
      | exact hbd h1
      | exact hbd h1.symm
      | exact hbd h2
      | exact hbd h2.symm
  have hSupport : q.support.tail.Nodup := by
    simp only [q, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.mem_nil_iff, or_false,
      List.nodup_nil, not_false_eq_true, and_true, not_or]
    exact ⟨⟨hbc_ne, hbd, hab_ne.symm⟩, ⟨hcd_ne, hac.symm⟩, hda_ne⟩
  have hCyc : q.IsCycle :=
    { edges_nodup := hEdges
      ne_nil := by simp [q]
      support_nodup := hSupport }
  have hLen : 5 ≤ q.length := hGirth a q hCyc
  simp [q] at hLen

private lemma graphFun_empty {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (x : Fin m → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ x =
      decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
  simp [PEqualNP.MetaComplexity.NestedCover.graphFun]

private lemma main
    (hClean : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
      ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ),
      (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1)
    (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hMono : PEqualNP.MetaComplexity.Monotone2 D)
    (hFun : PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅)
    (hGirth : ∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length)
    (hAnd : ∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) :
    ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  have hNoC4 := no_four_cycle_of_girth_five H hGirth
  have hOps : ∀ g ∈ D.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    rcases hMono g hg with ⟨hop, hlen⟩
    exact ⟨by simpa using hop, hlen⟩
  have hEval : ∀ x : Fin m → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, D.output⟩ (List.ofFn x) =
        decide (∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    have hx := congrFun hFun x
    rw [graphFun_empty] at hx
    exact hx
  have hAndClean : ∀ (i : Fin D.gates.length) (x : Fin m → Bool),
      (D.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩ (List.ofFn x)).getD (m + (i : ℕ)) false = true →
      ∃ u v : Fin m, H.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hop hval
    have hgateAt : PEqualNP.MetaComplexity.NestedCover.gateAt D i.val = D.gates.get i := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      simp [List.getD_eq_getElem?_getD, i.isLt]
    have hres := hAnd i.val i.isLt (by rw [hgateAt]; exact hop) x hval
    rw [graphFun_empty] at hres
    exact of_decide_eq_true hres
  obtain ⟨S, hCov, hCard⟩ := hClean m H hNoC4 D.gates D.output hOps hEval hAndClean
  exact ⟨S, hCov, hCard, Nat.le_trans (Nat.le_add_right _ _) hCard⟩

end PEqualNP.Outside.L_meta_1601

theorem PEqualNP.Outside.L_meta_1601 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ (p : Fin m) (q : H.Walk p p), q.IsCycle → 5 ≤ q.length) → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ y : Fin m → Bool, PEqualNP.EdgeOwnership.gateVal m D k y = true → PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ y = true) → ∃ S : Finset (Fin m), (∀ e w : Fin m, H.Adj e w → e ∈ S ∨ w ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 ∧ H.edgeFinset.card ≤ D.size + 1 := by
  exact PEqualNP.Outside.L_meta_1601.main
