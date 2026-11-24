import Mathlib
import PEqualNP.Defs

-- The 64-gate bound for the point-line graph of the projective plane of order 3
-- follows from the general no-4-cycle counting lemmas (as in R_meta_612_7): every
-- AND/OR circuit for the edge function of a graph with no 4-cycle has at least
-- |E| - 1 OR gates, and its AND gates cover a vertex cover. Here |E| = 52 and the
-- vertex cover number is 13, since the graph is the incidence graph of PG(2,3)
-- (13 points, 13 lines, 52 incidences, no 4-cycle). The step hypothesis is about
-- the AND of the output wires x2, so one extra AND gate is appended to make a
-- circuit whose eval is exactly that AND; the count then gives
-- 52 + 13 <= #OR + #AND + 2 = size + 2, i.e. 63 <= size.
-- The concrete graph facts (52 edges, cover number 13, no 4-cycle) and the bridge
-- (the step hypothesis makes the appended circuit compute the edge function) are
-- finite checks / counting arguments over the difference set {0, 1, 3, 9} mod 13.
theorem PEqualNP.Outside.R_meta_1988_1
    (hOr : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.edgeSet.ncard ≤
        {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + 1)
    (hAnd : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧
        S.card ≤
          {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard)
    (hGraph :
      let G := PEqualNP.EdgeOwnership.edgeGraph 26 [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
      G.edgeSet.ncard = 52 ∧
        (∀ S : Finset (Fin 26), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S →
          13 ≤ S.card) ∧
        (∀ a b c d : Fin 26, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
          G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a))
    (hBridge : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),
      PEqualNP.MetaComplexity.Monotone2 C → x2.length ≤ 2 →
      (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => (C.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →
      ∀ x : Fin 26 → Bool,
        (({ gates := C.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, x2⟩],
            output := 26 + C.gates.length } : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = true ↔
          ∃ u v : Fin 26, (PEqualNP.EdgeOwnership.edgeGraph 26 [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]).Adj u v ∧ x u = true ∧ x v = true))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);         have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};         have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn (x6 x8 x9))).getD x10 Bool.false) x2);         (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false) →         (63 : ℕ) ≤ x1.size := by
  intro C x2 hMono hLen hHyp
  obtain ⟨hE, hMin, hC4⟩ := hGraph
  set C' : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := C.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, x2⟩],
      output := 26 + C.gates.length } with hC'def
  have hCgates : C'.gates = C.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.and, x2⟩] := rfl
  have hMono' : PEqualNP.MetaComplexity.Monotone2 C' := by
    intro g hg
    rw [hCgates] at hg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hMono g hg
    · rw [List.mem_singleton] at hg
      subst hg
      constructor
      · exact Set.mem_insert _ _
      · exact hLen
  have hEval : ∀ x : Fin 26 → Bool,
      (C'.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, (PEqualNP.EdgeOwnership.edgeGraph 26 [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]).Adj u v ∧ x u = true ∧ x v = true) :=
    hBridge C x2 hMono hLen hHyp
  have h1 := hOr 26 (PEqualNP.EdgeOwnership.edgeGraph 26 [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]) C' hC4 hMono' hEval
  obtain ⟨S, hS, hSc⟩ := hAnd 26 (PEqualNP.EdgeOwnership.edgeGraph 26 [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]) C' hC4 hMono' hEval
  have h13 : 13 ≤
      {i : Fin C'.gates.length | (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
    le_trans (hMin S hS) hSc
  have hdisj : Disjoint
      {i : Fin C'.gates.length | (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}
      {i : Fin C'.gates.length | (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
    rw [Set.disjoint_left]
    intro i h1 h2
    rw [Set.mem_ofPred_eq] at h1 h2
    rw [h1] at h2
    exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion h2
  have hsum := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : ({i : Fin C'.gates.length | (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or} ∪
      {i : Fin C'.gates.length | (C'.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}).ncard ≤
      C'.gates.length := by
    calc _ ≤ (Set.univ : Set (Fin C'.gates.length)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = C'.gates.length := by
          rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hlen : C'.gates.length = C.size + 1 := by
    have h1 : C'.gates.length = C.gates.length + 1 := by
      rw [hCgates, List.length_append]
      rfl
    have h2 : C.size = C.gates.length := rfl
    omega
  omega
