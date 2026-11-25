import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open scoped Classical

-- Removing a star must save enough gates to restore all but one of its edges.
-- The two edges need not be specified by the matching.
theorem PEqualNP.Outside.R_meta_5373_327
    (saveStar : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit)
      (G : SimpleGraph (Fin (n+m))),
      let fit := fun (F : Finset (Fin n × Fin m)) (D : Circuit) =>
        IsAO2 (n+m) D ∧ ∀ x, circuitFun (n+m) D x = decide
          (∃ a b, (a,b) ∈ F ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)
      (∀ u v, G.Adj u v ↔ ∃ e ∈ E, (u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2) ∨
        (v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2)) →
      ¬ G.IsAcyclic →
      (∀ a a' b b', a ≠ a' → b ≠ b' → ¬((a,b) ∈ E ∧ (a,b') ∈ E ∧
        (a',b) ∈ E ∧ (a',b') ∈ E)) →
      fit E C → ∃ S ⊆ E, 2 ≤ S.card ∧
        ((∃ a, ∀ e ∈ S, e.1 = a) ∨ (∃ b, ∀ e ∈ S, e.2 = b)) ∧
        (E \ S).Nonempty ∧ ∃ D : Circuit, fit (E \ S) D ∧ D.size + S.card < C.size)
    (restoreStar : ∀ (n m : ℕ) (E S : Finset (Fin n × Fin m)) (e : Fin n × Fin m) (D : Circuit),
      let fit := fun (F : Finset (Fin n × Fin m)) (K : Circuit) =>
        IsAO2 (n+m) K ∧ ∀ x, circuitFun (n+m) K x = decide
          (∃ a b, (a,b) ∈ F ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)
      S ⊆ E → 2 ≤ S.card → ((∃ a, ∀ f ∈ S, f.1 = a) ∨ (∃ b, ∀ f ∈ S, f.2 = b)) →
      (E \ S).Nonempty → e ∈ S → fit (E \ S) D →
      ∃ H : Circuit, fit (E.erase e) H ∧ H.size ≤ D.size + S.card) :
  ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) → ∃ x16 ∈ x3, x16 ∉ x4 ∧ ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), x17.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x17 ∧ ∀ (x18 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x17 x18 = Decidable.decide (∃ (x19 : Fin x1) (x20 : Fin x2), (x19, x20) ∈ x3.erase x16 ∧ x18 (Fin.castAdd x2 x19) = Bool.true ∧ x18 (Fin.natAdd x1 x20) = Bool.true) := by
  classical
  intro n m E M C G graph cycle four well computes _ point line _
  obtain ⟨S, sub, two, star, nonempty, D, good, saves⟩ :=
    saveStar n m E C G graph cycle four ⟨well, computes⟩
  have missing : ∃ e ∈ S, e ∉ M := by
    by_contra! all
    have small : S.card ≤ 1 := Finset.card_le_one_iff.mpr (by
      intro u v hu hv
      rcases star with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact point u (all u hu) v (all v hv) ((ha u hu).trans (ha v hv).symm)
      · exact line u (all u hu) v (all v hv) ((hb u hu).trans (hb v hv).symm))
    omega
  obtain ⟨e, he, outside⟩ := missing
  obtain ⟨H, hH, cost⟩ := restoreStar n m E S e D sub two star nonempty he good
  exact ⟨e, sub he, outside, H, by omega, hH⟩
