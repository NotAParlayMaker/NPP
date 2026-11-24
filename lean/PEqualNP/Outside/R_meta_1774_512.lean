import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

/-- Reduction of L-meta-1774:
    Internally proves:
    1. `0 < badCount C` yields a minimum-index bad AND gate `j0 < C.gates.length` owning two
       disjoint edges `(a, b)` and `(c, d)` of `G`.
    2. Using `allOwn C` and triangle-freeness of `G`, every earlier AND gate `i < j0` owns a
       star of edges (`∃ v0, ∀ u w, G.Adj u w → Owns n C i u w → u = v0 ∨ w = v0`).
    Splits by whether the minimum-index bad AND gate `j0` is `BelowF G C j0` or dirty (`¬ BelowF G C j0`). -/
theorem PEqualNP.Outside.R_meta_1774_512
    (min_bad_belowF :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ u v w : Fin n, G.Adj u v → G.Adj v w → ¬ G.Adj w u) →
        NoFourCycle G →
        let allOwn (C : Circuit) : Prop :=
          ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
            ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v
        let badCount (C : Circuit) : ℕ :=
          {j : ℕ | ∃ a b c d : Fin n,
            G.Adj a b ∧ G.Adj c d ∧ Owns n C j a b ∧ Owns n C j c d ∧
            a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d}.ncard
        ∀ (C : Circuit) (j0 : ℕ) (a b c d : Fin n),
          IsMinimalMonoCircuit n C →
          circuitFun n C = graphFun G ∅ →
          allOwn C →
          0 < badCount C →
          j0 < C.gates.length →
          (gateAt C j0).op = GateOp.and →
          G.Adj a b → G.Adj c d →
          Owns n C j0 a b → Owns n C j0 c d →
          a ≠ c → a ≠ d → b ≠ c → b ≠ d →
          (∀ i < j0, (gateAt C i).op = GateOp.and →
            ∃ v0 : Fin n, ∀ u w : Fin n, G.Adj u w → Owns n C i u w → u = v0 ∨ w = v0) →
          BelowF G C j0 →
          ∃ C' : Circuit, Monotone2 C' ∧ circuitFun n C' = graphFun G ∅ ∧
            C'.size ≤ C.size ∧ allOwn C' ∧ badCount C' < badCount C)
    (min_bad_dirty :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ u v w : Fin n, G.Adj u v → G.Adj v w → ¬ G.Adj w u) →
        NoFourCycle G →
        let allOwn (C : Circuit) : Prop :=
          ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
            ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v
        let badCount (C : Circuit) : ℕ :=
          {j : ℕ | ∃ a b c d : Fin n,
            G.Adj a b ∧ G.Adj c d ∧ Owns n C j a b ∧ Owns n C j c d ∧
            a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d}.ncard
        ∀ (C : Circuit) (j0 : ℕ) (a b c d : Fin n),
          IsMinimalMonoCircuit n C →
          circuitFun n C = graphFun G ∅ →
          allOwn C →
          0 < badCount C →
          j0 < C.gates.length →
          (gateAt C j0).op = GateOp.and →
          G.Adj a b → G.Adj c d →
          Owns n C j0 a b → Owns n C j0 c d →
          a ≠ c → a ≠ d → b ≠ c → b ≠ d →
          (∀ i < j0, (gateAt C i).op = GateOp.and →
            ∃ v0 : Fin n, ∀ u w : Fin n, G.Adj u w → Owns n C i u w → u = v0 ∨ w = v0) →
          ¬ BelowF G C j0 →
          ∃ C' : Circuit, Monotone2 C' ∧ circuitFun n C' = graphFun G ∅ ∧
            C'.size ≤ C.size ∧ allOwn C' ∧ badCount C' < badCount C) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],
      (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →
      PEqualNP.TopForm.NoFourCycle x2 →
      have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) =>
        ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;
      have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) =>
        {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1),
          x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧
          PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧
          x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;
      ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 →
        PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        x6 x8 →
        (0 : ℕ) < x7 x8 →
        ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 x13 ∧
          PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
          x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8 := by
  classical
  intro n G _ htri hno4 allOwn badCount C hmin hfun hallOwn hpos
  -- Step 1: Extract the minimum-index bad AND gate j0
  let B : Set ℕ := {j : ℕ | ∃ a b c d : Fin n,
    G.Adj a b ∧ G.Adj c d ∧ Owns n C j a b ∧ Owns n C j c d ∧
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d}
  have hB_ne : ∃ j : ℕ, j ∈ B := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hpos)
  let j0 := Nat.find hB_ne
  have hj0_mem : j0 ∈ B := Nat.find_spec hB_ne
  have hj0_min : ∀ i < j0, i ∉ B := fun i hi => Nat.find_min hB_ne hi
  rcases hj0_mem with ⟨a, b, c, d, hab, hcd, hOab, hOcd, hac, had, hbc, hbd⟩
  have hj0_lt : j0 < C.gates.length := hOab.1
  have hj0_and : (gateAt C j0).op = GateOp.and := hOab.2.1
  -- Step 2: Every AND gate i < j0 owns a star of edges (using triangle-freeness)
  have hstar_before : ∀ i < j0, (gateAt C i).op = GateOp.and →
      ∃ v0 : Fin n, ∀ u w : Fin n, G.Adj u w → Owns n C i u w → u = v0 ∨ w = v0 := by
    intro i hi hior
    have hi_lt : i < C.gates.length := by omega
    rcases hallOwn i hi_lt hior with ⟨u1, v1, huv1, hO1⟩
    by_cases h1 : ∀ u w : Fin n, G.Adj u w → Owns n C i u w → u = u1 ∨ w = u1
    · exact ⟨u1, h1⟩
    · push Not at h1
      rcases h1 with ⟨u2, v2, huv2, hO2, hu2ne, hv2ne⟩
      -- Since i ∉ B, {u1, v1} and {u2, v2} must intersect; since u2 ≠ u1 and v2 ≠ u1, v1 ∈ {u2, v2}
      have hnotB := hj0_min i hi
      have hv1_in : u2 = v1 ∨ v2 = v1 := by
        by_contra hnone
        push Not at hnone
        exact hnotB ⟨u1, v1, u2, v2, huv1, huv2, hO1, hO2,
          hu2ne.symm, hv2ne.symm, hnone.1.symm, hnone.2.symm⟩
      -- Show every edge owned by i touches v1
      refine ⟨v1, ?_⟩
      intro u3 v3 huv3 hO3
      by_contra hnotv1
      push Not at hnotv1
      -- Edge (u3, v3) must touch {u1, v1} -> u1 ∈ {u3, v3}
      have hu1_in : u3 = u1 ∨ v3 = u1 := by
        by_contra hnone
        push Not at hnone
        exact hnotB ⟨u1, v1, u3, v3, huv1, huv3, hO1, hO3,
          hnone.1.symm, hnone.2.symm, hnotv1.1.symm, hnotv1.2.symm⟩
      -- Edge (u3, v3) must touch {u2, v2}
      rcases hv1_in with rfl | rfl
      · -- u2 = v1, so other endpoint of (u2, v2) is v2 (≠ u1, ≠ v1)
        have hv2_in : u3 = v2 ∨ v3 = v2 := by
          by_contra hnone
          push Not at hnone
          exact hnotB ⟨u2, v2, u3, v3, huv2, huv3, hO2, hO3,
            hnotv1.1.symm, hnotv1.2.symm, hnone.1.symm, hnone.2.symm⟩
        rcases hu1_in with rfl | rfl <;> rcases hv2_in with hEq | hEq
        · exact hv2ne hEq.symm
        · subst hEq; exact htri u3 u2 v3 huv1 huv2 huv3.symm
        · subst hEq; exact htri v3 u2 u3 huv1 huv2 huv3
        · exact hv2ne hEq.symm
      · -- v2 = v1, so other endpoint of (u2, v2) is u2 (≠ u1, ≠ v1)
        have hu2_in : u3 = u2 ∨ v3 = u2 := by
          by_contra hnone
          push Not at hnone
          exact hnotB ⟨u2, v2, u3, v3, huv2, huv3, hO2, hO3,
            hnone.1.symm, hnone.2.symm, hnotv1.1.symm, hnotv1.2.symm⟩
        rcases hu1_in with rfl | rfl <;> rcases hu2_in with hEq | hEq
        · exact hu2ne hEq.symm
        · subst hEq; exact htri u3 v2 v3 huv1 huv2.symm huv3.symm
        · subst hEq; exact htri v3 v2 u3 huv1 huv2.symm huv3
        · exact hu2ne hEq.symm
  -- Step 3: Split by BelowF G C j0 vs ¬ BelowF G C j0
  by_cases hbel : BelowF G C j0
  · exact min_bad_belowF n G htri hno4 C j0 a b c d hmin hfun hallOwn hpos
      hj0_lt hj0_and hab hcd hOab hOcd hac had hbc hbd hstar_before hbel
  · exact min_bad_dirty n G htri hno4 C j0 a b c d hmin hfun hallOwn hpos
      hj0_lt hj0_and hab hcd hOab hOcd hac had hbc hbd hstar_before hbel
