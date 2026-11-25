import Mathlib
import PEqualNP.Defs

-- Reduction of L-meta-4318. Count the AND gates and the OR gates separately.
-- hOwned: every edge is owned by some AND gate (the statement of L-meta-1599, already proved).
-- hStar: under the hypotheses of the step, the owned edges of every AND gate form a star.
-- hOr: under the hypotheses of the step, the circuit has at least one OR gate less than edges.
-- The centers of the stars form a vertex cover with at most one vertex per AND gate, and a
-- gate of a monotone circuit is an AND gate or an OR gate, which gives the bound.
theorem PEqualNP.Outside.R_meta_4318_1
    (hOwned : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.EdgeOwnership.EveryEdgeOwned n G C)
    (hStar : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n,
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput z z) = false) →
      PEqualNP.EdgeOwnership.HasStarProfile n G C)
    (hOr : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      (∀ j < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n,
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput z z) = false) →
      G.edgeFinset.card ≤ {j : ℕ | j < C.size ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + 1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → x2.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ x10 < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput x13 x13) = Bool.false) → ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x2.edgeFinset.card + x11.card ≤ x7.size + (1 : ℕ) := by
  classical
  intro n G _ hTri hC4 hNe C hMin hFun hSing
  have hAO : PEqualNP.EdgeOwnership.AndOrOnly C := by
    intro g hg
    have h := (hMin.1 g hg).1
    simpa using h
  have hOwn := hOwned n G C hAO hFun
  have hSt := hStar n G hTri hC4 C hMin hFun hSing
  have hO := hOr n G hTri hC4 C hMin hFun hSing
  obtain ⟨e0, _⟩ := hNe
  let v0 : Fin n := (Quot.out e0).1
  let P : ℕ → Fin n → Prop := fun j c => ∀ u v : Fin n, G.Adj u v →
    PEqualNP.EdgeOwnership.Owns n C j u v → u = c ∨ v = c
  let cen : ℕ → Fin n := fun j => if h : ∃ c, P j c then Classical.choose h else v0
  let A := (Finset.range C.size).filter (fun j =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  let O := (Finset.range C.size).filter (fun j =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or)
  refine ⟨A.image cen, ?_, ?_⟩
  · intro u v huv
    obtain ⟨j, hj, hown⟩ := hOwn u v huv
    have hjand := hown.2.1
    have hjA : j ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, hjand⟩
    rcases hSt j hj hjand with hno | hc
    · exact absurd hown (hno u v huv)
    · have hcen : cen j = Classical.choose hc := dif_pos hc
      have hspec := Classical.choose_spec hc u v huv hown
      rw [← hcen] at hspec
      rcases hspec with h | h
      · left
        rw [h]
        exact Finset.mem_image_of_mem cen hjA
      · right
        rw [h]
        exact Finset.mem_image_of_mem cen hjA
  · have h1 : (A.image cen).card ≤ A.card := Finset.card_image_le
    have h2 : A.card + ((Finset.range C.size).filter (fun j =>
        ¬ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and)).card = (Finset.range C.size).card :=
      Finset.card_filter_add_card_filter_not _
    have h3 : O.card ≤ ((Finset.range C.size).filter (fun j =>
        ¬ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and)).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [O, Finset.mem_filter] at hj
      simp only [Finset.mem_filter]
      refine ⟨hj.1, ?_⟩
      rw [hj.2]
      exact fun h => PEqualNP.CircuitLowerBounds.GateOp.noConfusion h
    rw [Finset.card_range] at h2
    have hOset : {j : ℕ | j < C.size ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.or} = (O : Set ℕ) := by
      ext j
      simp [O]
    have h4 : G.edgeFinset.card ≤ O.card + 1 := by
      rw [hOset, Set.ncard_coe_finset] at hO
      exact hO
    omega
