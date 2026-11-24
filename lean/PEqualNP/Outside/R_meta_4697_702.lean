import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4697_702
    (build : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
      (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
    ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
      (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (D : List (Finset (Fin n))),
        B = P ++ a :: D → ∃ (b c : Finset (Fin n)), a = b ∪ c ∧
          (b.card ≤ 1 ∨ b ∈ D) ∧ (c.card ≤ 1 ∨ c ∈ D)) ∧
      (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
      (∀ x : Fin n → Bool, (∃ i, (∃ u ∈ X i, x u = true) ∧ ∃ v ∈ Y i, x v = true) ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧
      B.length + 2 * m ≤ G.edgeSet.ncard + T.card)
    (flat : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsAO2 n C → (∀ i < C.size, ∀ j < C.size,
        (gateAt C i).op = .and → (gateAt C j).op = .and → ¬ InCone n C i j) →
      circuitFun n C = graphFun G ∅ →
    ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
      (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (D : List (Finset (Fin n))),
        B = P ++ a :: D → ∃ (b c : Finset (Fin n)), a = b ∪ c ∧
          (b.card ≤ 1 ∨ b ∈ D) ∧ (c.card ≤ 1 ∨ c ∈ D)) ∧
      (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
      (∀ x : Fin n → Bool, (∃ i, (∃ u ∈ X i, x u = true) ∧ ∃ v ∈ Y i, x v = true) ↔
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧
      B.length + 2 * m ≤ C.size + 1)
    (normalize : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      circuitFun n C (fun _ => false) = false →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C)
    (hard : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ →
      ((∃ g ∈ C.gates, g.op = .not) ∨ (IsAO2 n C ∧ ∃ i < C.size, ∃ j < C.size,
        (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone n C i j)) →
      C.size + 1 < G.edgeSet.ncard + (Finset.univ \ A).card →
      ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        G.edgeSet.ncard + T.card ≤ C.size + 1) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 : Fin x12 → Finset (Fin x1)) (x14 : Fin x12 → Finset (Fin x1)), (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 : Finset (Fin x1)) (x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ (1 : ℕ) ∨ x19 ∈ x17) ∧ (x20.card ≤ (1 : ℕ) ∨ x20 ∈ x17)) ∧ (∀ (x15 : Fin x12), ((x13 x15).card ≤ (1 : ℕ) ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ (1 : ℕ) ∨ x14 x15 ∈ x11)) ∧ (∀ (x15 : Fin x1 → Bool), (∃ (x16 : Fin x12), (∃ x17 ∈ x13 x16, x15 x17 = Bool.true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = Bool.true) ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧ x11.length + (2 : ℕ) * x12 ≤ x9 + (1 : ℕ) := by
  classical
  intro n G _ A cubic girth separated edge s admissible
  obtain ⟨C, fan, bound, good⟩ := admissible
  let admissibleSize (k : ℕ) := ∃ D : Circuit, FanInTwo D ∧
    circuitFun n D = graphFun G ∅ ∧ D.size = k
  have sizes : ∃ k, admissibleSize k := ⟨C.size, C, fan, funext good, rfl⟩
  obtain ⟨D, fanD, evalD, hsize⟩ := Nat.find_spec sizes
  have minimal : IsMinimalCircuit n D := by
    refine ⟨fanD, ?_⟩
    intro Q fanQ evalQ
    rw [hsize]
    exact Nat.find_min' sizes ⟨Q, fanQ, evalQ.trans evalD, rfl⟩
  have ds := (minimal.2 C fan ((funext good).trans evalD.symm)).trans bound
  suffices data :
      (∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
        (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (U : List (Finset (Fin n))),
          B = P ++ a :: U → ∃ (b c : Finset (Fin n)), a = b ∪ c ∧
            (b.card ≤ 1 ∨ b ∈ U) ∧ (c.card ≤ 1 ∨ c ∈ U)) ∧
        (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
        (∀ x : Fin n → Bool, (∃ i, (∃ u ∈ X i, x u = true) ∧ ∃ v ∈ Y i, x v = true) ↔
          ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧ B.length + 2 * m ≤ D.size + 1) ∨
      ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeSet.ncard + T.card ≤ D.size + 1 by
    rcases data with ⟨B, m, X, Y, hB, hXY, truth, cost⟩ | ⟨T, covered, paid⟩
    · exact ⟨B, m, X, Y, hB, hXY, truth, by omega⟩
    · obtain ⟨B, m, X, Y, hB, hXY, truth, cost⟩ := build n G T covered
      exact ⟨B, m, X, Y, hB, hXY, truth, by omega⟩
  by_cases cheap : G.edgeSet.ncard + (Finset.univ \ A).card ≤ D.size + 1
  · refine Or.inr ⟨Finset.univ \ A, ?_, cheap⟩
    intro u v edge
    exact Or.inl (by simp [separated u v edge])
  by_cases mon : Monotone2 D
  · have hzero : circuitFun n D (fun _ => false) = false := by
      rw [evalD]
      unfold graphFun
      simp
    obtain ⟨E, form, es, evalE⟩ := normalize n D mon hzero
    have fanE : FanInTwo E := by
      intro g h
      refine ⟨?_, by rw [form.2.2 g h]⟩
      rcases form.1 g h with hop | hop <;> simp [hop]
    have minE : IsMinimalCircuit n E := by
      refine ⟨fanE, fun Q fQ eQ => es.trans ?_⟩
      exact minimal.2 Q fQ (eQ.trans evalE)
    have evalG := evalE.trans evalD
    by_cases nested : ∃ i < E.size, ∃ j < E.size,
        (gateAt E i).op = .and ∧ (gateAt E j).op = .and ∧ InCone n E i j
    · obtain ⟨T, hc, hp⟩ := hard n G A E cubic girth separated edge minE evalG
        (Or.inr ⟨form, nested⟩) (by omega)
      exact Or.inr ⟨T, hc, by omega⟩
    · obtain ⟨B, m, X, Y, hb, hxy, hx, hbnd⟩ := flat n G E form
        (fun i hi j hj hA hB before => nested ⟨i, hi, j, hj, hA, hB, before⟩) evalG
      exact Or.inl ⟨B, m, X, Y, hb, hxy, hx, by omega⟩
  · have usesNot : ∃ g ∈ D.gates, g.op = .not := by
      by_contra lacks
      apply mon
      intro g h
      obtain ⟨hop, hlen⟩ := fanD g h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
      refine ⟨?_, hlen⟩
      rcases hop with ha | ho | hn
      · exact Or.inl ha
      · exact Or.inr ho
      · exact False.elim (lacks ⟨g, h, hn⟩)
    exact Or.inr (hard n G A D cubic girth separated edge minimal evalD (Or.inl usesNot) (by omega))
