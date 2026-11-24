import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Core PEqualNP.FactorSubst PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_3722_481
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ D : Circuit, IsLeastAO G D ∧ IsLiftFixedPoint G D ∧
        (∀ k < D.gates.length, (gateAt D k).op = GateOp.and →
          ∀ t ∈ (gateAt D k).inputs,
            ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true →
              graphFun G ∅ x = true)) ∧
        liveSize n D = D.size)
    (core_drop : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj],
      (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧
        ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨
          (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) →
      NoFourCycle G →
      ∀ C : Circuit, IsLeastAO G C → IsLiftFixedPoint G C →
        (∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
          ∀ t ∈ (gateAt C k).inputs,
            ¬ (∀ x : Fin (N + N) → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
              graphFun G ∅ x = true)) →
        liveSize (N + N) C = C.size →
        ∀ c ∈ maximalCores G C, ∃ a b : ℕ, ∃ sigma : ℕ → ℕ,
          (gateAt C c).inputs = [a, b] ∧
          liveSize (N + N) (substReads C (N + N) c sigma) + 1 ≤ liveSize (N + N) C)
    (finish : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (isLine : ℕ → Bool) (E : List (ℕ × ℕ)),
      IsLeastAO G C → IsLiftFixedPoint G C →
        (∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
          ∀ t ∈ (gateAt C k).inputs,
            ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true →
              graphFun G ∅ x = true)) →
        liveSize n C = C.size →
        (∀ c ∈ maximalCores G C, ∃ a b : ℕ, ∃ sigma : ℕ → ℕ,
          (gateAt C c).inputs = [a, b] ∧
          liveSize n (substReads C n c sigma) + 1 ≤ liveSize n C) →
        (∀ e ∈ E, ∃ u v : Fin n, e = (u.val, v.val) ∧ G.Adj u v) →
        doubleReread C n isLine E = []) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj], (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.Core.IsLiftFixedPoint G D ∧ (∀ k < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D k).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) ∧ PEqualNP.FactorSubst.liveSize (N + N) D = D.size ∧ PEqualNP.ReadK.doubleReread D (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val)))) = [] := by
  classical
  intro N I _ G _ hAdj h4 C hAO hF
  obtain ⟨D, hLeast, hLift, hClean, hLive⟩ := normalize (N + N) G C hAO hF
  let E : List (ℕ × ℕ) :=
    (List.finRange N).flatMap fun p =>
      ((List.finRange N).filter fun l => decide (I p l)).map fun l =>
        (p.val, N + l.val)
  have hEdges : ∀ e ∈ E, ∃ u v : Fin (N + N), e = (u.val, v.val) ∧ G.Adj u v := by
    intro e he
    simp only [E, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and, decide_eq_true_eq] at he
    obtain ⟨p, l, hI, rfl⟩ := he
    refine ⟨Fin.castAdd N p, Fin.natAdd N l, rfl, ?_⟩
    exact (hAdj _ _).2 ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩
  have hDrop := core_drop N I G hAdj h4 D hLeast hLift hClean hLive
  have hSingle := finish (N + N) G D (fun w => decide (N ≤ w)) E
    hLeast hLift hClean hLive hDrop hEdges
  exact ⟨D, hLeast, hLift, hClean, hLive, hSingle⟩
