import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_972_1 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ x u = true ∧ x v = true) →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C' ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C' ∧
        C'.size ≤ C.size ∧
        ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ x u = true ∧ x v = true) →
      (¬ ∃ g1 g2 : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 26 C g1 g2) →
      64 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧ x u = true ∧ x v = true) →
      (∃ g1 g2 : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 26 C g1 g2) →
      64 ≤ C.size) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  intro h1 h2 h3 C hM2 hEval
  have hEdge : ∀ u v : Fin 26,
      (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ↔
      u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
    decide
  have hEval' : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 26, u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
        x u = true ∧ x v = true := by
    intro x
    exact Iff.trans (hEval x)
      ⟨fun h => Exists.elim h fun u hu => Exists.elim hu fun v hv =>
          ⟨u, v, ((hEdge u v).mp hv.1).1, ((hEdge u v).mp hv.1).2.1, ((hEdge u v).mp hv.1).2.2, hv.2.1, hv.2.2⟩,
       fun h => Exists.elim h fun u hu => Exists.elim hu fun v hv =>
          ⟨u, v, (hEdge u v).mpr ⟨hv.1, hv.2.1, hv.2.2.1⟩, hv.2.2.2.1, hv.2.2.2.2⟩⟩
  exact Exists.elim (h1 C hM2 hEval') fun C' hC' =>
    have hEval'' : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) ∧
          x u = true ∧ x v = true :=
      fun x => Eq.subst (motive := fun b => b = true ↔ _) (hC'.2.2.2 x).symm (hEval' x)
    Or.elim (Classical.em (∃ g1 g2 : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C' g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C' g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone 26 C' g1 g2))
      (fun hNest => Nat.le_trans (h3 C' hC'.1 hC'.2.1 hEval'' hNest) hC'.2.2.1)
      (fun hNoNest => Nat.le_trans (h2 C' hC'.1 hC'.2.1 hEval'' hNoNest) hC'.2.2.1)
