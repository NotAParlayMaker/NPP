import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

theorem PEqualNP.Outside.R_meta_4111_1
    (deletions : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      ¬ G.Colorable 2 →
      (∀ z, (∃ w, G.Adj z w) → (G.neighborSet z).ncard = 3) →
      (∀ z (w : G.Walk z z), w.IsCycle → 7 ≤ w.length) →
      (∃ u v, G.Adj u v) → PEqualNP.MetaComplexity.IsMinimalCircuit n C →
      (∀ x, C.eval (List.ofFn x) = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
        C.size+1 < G.edgeSet.ncard+T.card) →
      ∃ u v : Fin n, G.Adj u v ∧ ∃ K : ℕ → PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo (K 0) ∧ (K 0).size ≤ C.size ∧
        PEqualNP.MetaComplexity.circuitFun n (K 0) = PEqualNP.MetaComplexity.circuitFun n C ∧
        ∀ i < 7, ∃ j p : ℕ, j < (K i).size ∧ (p < n+j ∨ n+(K i).size ≤ p) ∧
          K (i+1) = PEqualNP.CircuitMoves.eraseGate n (K i) j p ∧
          ((∀ x : Fin n → Bool,
            let w := (K i).wires (List.ofFn (Function.update (Function.update x u false) v false))
            w.getD (n+j) false = w.getD p false) ∨
          ((K i).output ≠ n+j ∧ ∀ g ∈ (K i).gates.drop (j+1), n+j ∉ g.inputs)))
    (collapse : ∀ (n k : ℕ) (u v : Fin n) (K : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo (K 0) →
      (∀ i < k, ∃ j p : ℕ, j < (K i).size ∧ (p < n+j ∨ n+(K i).size ≤ p) ∧
        K (i+1) = PEqualNP.CircuitMoves.eraseGate n (K i) j p ∧
        ((∀ x : Fin n → Bool,
          let w := (K i).wires (List.ofFn (Function.update (Function.update x u false) v false))
          w.getD (n+j) false = w.getD p false) ∨
        ((K i).output ≠ n+j ∧ ∀ g ∈ (K i).gates.drop (j+1), n+j ∉ g.inputs))) →
      ∃ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo E ∧
        E.size+k = (K 0).size ∧ ∀ x : Fin n → Bool,
          E.eval (List.ofFn x) =
            (K 0).eval (List.ofFn (Function.update (Function.update x u false) v false))) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x9 + (1 : ℕ) < x2.edgeSet.ncard + x10.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ ∃ (x14 : ℕ), x14 + (7 : ℕ) ≤ x9 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x15 : Fin x1 → Bool) => x3 (Function.update (Function.update x15 x12 Bool.false) x13 Bool.false)) x14 := by
  intro n G f hcolor hdegree hgirth hedge hsem s hsparse hs
  classical
  have hex : ∃ t, PEqualNP.MetaComplexity.HasCircuitSize n f t := ⟨s, hs⟩
  obtain ⟨C, hfan, hbound, hval⟩ := Nat.find_spec hex
  have hCs : C.size ≤ s := hbound.trans (Nat.find_min' hex hs)
  have hmin : PEqualNP.MetaComplexity.IsMinimalCircuit n C := by
    refine ⟨hfan, ?_⟩
    intro E hE heq
    have hEs : PEqualNP.MetaComplexity.HasCircuitSize n f E.size := by
      refine ⟨E, hE, le_rfl, ?_⟩
      intro x
      have hx := congrFun heq x
      change E.eval (List.ofFn x) = C.eval (List.ofFn x) at hx
      exact hx.trans (hval x)
    exact hbound.trans (Nat.find_min' hex hEs)
  have hCsem (x : Fin n → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    rw [hval x]
    exact hsem x
  have hCsmall (T : Finset (Fin n))
      (ht : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) :
      C.size+1 < G.edgeSet.ncard+T.card := by
    have := hsparse T ht
    omega
  obtain ⟨u, v, huv, K, hzeroFan, hzeroSize, hzeroFun, hsteps⟩ :=
    deletions n G C hcolor hdegree hgirth hedge hmin hCsem hCsmall
  obtain ⟨E, hE, hcount, heval⟩ := collapse n 7 u v K hzeroFan hsteps
  refine ⟨u, v, huv, E.size, hcount.le.trans (hzeroSize.trans hCs), E, hE, le_rfl, ?_⟩
  intro x
  have hz := congrFun hzeroFun (Function.update (Function.update x u false) v false)
  exact (heval x).trans (hz.trans (hval _))

