import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8181_1
    (hA :
      ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n + m))),
        (∀ u v : Fin (n + m), G.Adj u v ↔ ∃ e ∈ E,
          (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
          (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2)) →
        ¬ G.IsAcyclic → M ⊆ E →
        (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) →
        (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) →
        ∃ e ∈ E, e ∉ M ∧
          2 ≤ (G.neighborSet (Fin.castAdd m e.1)).ncard ∧
          2 ≤ (G.neighborSet (Fin.natAdd n e.2)).ncard)
    (hB :
      ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (G : SimpleGraph (Fin (n + m))) (e : Fin n × Fin m),
        (∀ u v : Fin (n + m), G.Adj u v ↔ ∃ f ∈ E,
          (u = Fin.castAdd m f.1 ∧ v = Fin.natAdd n f.2) ∨
          (v = Fin.castAdd m f.1 ∧ u = Fin.natAdd n f.2)) →
        ¬ G.IsAcyclic → e ∈ E →
        2 ≤ (G.neighborSet (Fin.castAdd m e.1)).ncard →
        2 ≤ (G.neighborSet (Fin.natAdd n e.2)).ncard →
        PEqualNP.TopForm.IsAO2 (n + m) C →
        (∀ x : Fin (n + m) → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) C x =
          Decidable.decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = Bool.true ∧
            x (Fin.natAdd n l) = Bool.true)) →
        (∀ p q l s, p ≠ q → l ≠ s →
          ¬ ((p, l) ∈ E ∧ (p, s) ∈ E ∧ (q, l) ∈ E ∧ (q, s) ∈ E)) →
        ¬ (∃ v : Fin (n + m),
          have d : ℕ := (G.neighborSet v).ncard
          have r : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) C ↑v
          2 ≤ d ∧ (d < r.card ∨ d = r.card ∧ ∃ k ∈ r,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
              PEqualNP.CircuitLowerBounds.GateOp.and ∧
            ¬ PEqualNP.TopForm.readers (n + m) C k ⊆ r)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size < C.size ∧
          PEqualNP.TopForm.IsAO2 (n + m) D ∧
          ∀ x : Fin (n + m) → Bool, PEqualNP.MetaComplexity.circuitFun (n + m) D x =
            Decidable.decide (∃ p l, (p, l) ∈ E.erase e ∧ x (Fin.castAdd m p) = Bool.true ∧
              x (Fin.natAdd n l) = Bool.true)) :
  ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),   have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 → x12 = x14) → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.2 = x15.2 → x13 = x15) → x4 ⊆ x3 → (∀ (x15 x16 : Fin x1) (x17 x18 : Fin x2), x15 ≠ x16 → x17 ≠ x18 → ¬((x15, x17) ∈ x3 ∧ (x15, x18) ∈ x3 ∧ (x16, x17) ∈ x3 ∧ (x16, x18) ∈ x3)) → (∀ x16 ∈ x3, ((∀ x18 ∈ x3, x18.1 = x16.1 → x18 = x16) ∨ ∀ x18 ∈ x3, x18.2 = x16.2 → x18 = x16) → (x3.erase x16).Nonempty → x16 ∈ x4) → ¬x8 → ∃ x18 ∈ x3, x18 ∉ x4 ∧ ∃ (x19 : PEqualNP.CircuitLowerBounds.Circuit), x19.size < x5.size ∧ x7 (x3.erase x18) x19 := by
  classical
  intro x1 x2 x3 x4 x5 x6
  dsimp only
  intro hAdj hNotAcyc hAO hRow hCol hSub hSquare hForce hNotBad
  rcases hA x1 x2 x3 x4 x6 hAdj hNotAcyc hSub hRow hCol with
    ⟨e, he, heNot, hdegr, hdegc⟩
  rcases hB x1 x2 x3 x5 x6 e hAdj hNotAcyc he hdegr hdegc hAO.1 hAO.2 hSquare hNotBad with
    ⟨D, hDlt, hDAO, hDEval⟩
  refine ⟨e, he, heNot, D, hDlt, ?_⟩
  exact ⟨hDAO, hDEval⟩
