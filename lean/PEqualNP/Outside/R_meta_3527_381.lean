import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- The vertex-cover construction handles circuits at or above the cover cost.
-- The remaining case asks for a saving only when every cover construction is larger.
theorem PEqualNP.Outside.R_meta_3527_381
    (outside : ∀ (p l : ℕ) (E M : Finset (Fin p × Fin l)) (G : SimpleGraph (Fin (p+l))),
      (∀ a b, G.Adj a b ↔ ∃ e ∈ E,
        a = Fin.castAdd l e.1 ∧ b = Fin.natAdd p e.2 ∨
        b = Fin.castAdd l e.1 ∧ a = Fin.natAdd p e.2) →
      ¬ G.IsAcyclic → (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') →
      (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e') → ∃ e ∈ E, e ∉ M)
    (construct : ∀ (p l : ℕ) (E : Finset (Fin p × Fin l)),
      let covers := fun (T : Finset (Fin (p+l))) =>
        ∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ T ∨ Fin.natAdd p b ∈ T
      let f := fun (K : Finset (Fin p × Fin l)) (z : Fin (p+l) → Bool) =>
        decide (∃ a b, (a,b) ∈ K ∧ z (Fin.castAdd l a) = true ∧ z (Fin.natAdd p b) = true)
      ∀ T, covers T →
      ∃ D : Circuit, IsAO2 (p+l) D ∧ circuitFun (p+l) D = f E ∧
        D.size ≤ E.card + T.card - 1)
    (below : ∀ (p l : ℕ) (E M : Finset (Fin p × Fin l))
      (C : Circuit) (G : SimpleGraph (Fin (p+l))),
      let covers := fun (T : Finset (Fin (p+l))) =>
        ∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ T ∨ Fin.natAdd p b ∈ T
      let f := fun (K : Finset (Fin p × Fin l)) (z : Fin (p+l) → Bool) =>
        decide (∃ a b, (a,b) ∈ K ∧ z (Fin.castAdd l a) = true ∧ z (Fin.natAdd p b) = true)
      (∀ a b, G.Adj a b ↔ ∃ e ∈ E,
        a = Fin.castAdd l e.1 ∧ b = Fin.natAdd p e.2 ∨
        b = Fin.castAdd l e.1 ∧ a = Fin.natAdd p e.2) →
      ¬ G.IsAcyclic →
      (∀ a a' b b', a ≠ a' → b ≠ b' → ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E)) →
      IsAO2 (p+l) C → circuitFun (p+l) C = f E → M ⊆ E →
      (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') →
      (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e') →
      (∀ T, covers T → C.size + 1 < E.card + T.card) →
      ∃ e ∈ E, e ∉ M ∧ ∃ D : Circuit, D.size < C.size ∧ IsAO2 (p+l) D ∧
        circuitFun (p+l) D = f (E.erase e)) :
∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → ∃ x15 ∈ x3, x15 ∉ x4 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), x16.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x16 ∧ ∀ (x17 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x16 x17 = Decidable.decide (∃ (x18 : Fin x1) (x19 : Fin x2), (x18, x19) ∈ x3.erase x15 ∧ x17 (Fin.castAdd x2 x18) = Bool.true ∧ x17 (Fin.natAdd x1 x19) = Bool.true) := by

  intro p l E M C G adj cycle four ao computes subset injP injL
  let covers (T : Finset (Fin (p+l))) :=
    ∀ a b, (a,b) ∈ E → Fin.castAdd l a ∈ T ∨ Fin.natAdd p b ∈ T
  by_cases budget : ∃ T, covers T ∧ E.card + T.card ≤ C.size + 1
  · obtain ⟨T,hT,budgetT⟩ := budget
    obtain ⟨e,he,hM⟩ := outside p l E M G adj cycle injP injL
    obtain ⟨D,hd,hc,hs⟩ := construct p l (E.erase e) T (fun a b hab =>
      hT a b (Finset.mem_of_mem_erase hab))
    have less : (E.erase e).card + 1 = E.card := Finset.card_erase_add_one he
    have nonempty : 1 ≤ E.card := Finset.card_pos.mpr ⟨e,he⟩
    have nonemptyT : 1 ≤ T.card := by
      apply Finset.card_pos.mpr
      rcases hT e.1 e.2 (by simpa using he) with h | h
      · exact ⟨_,h⟩
      · exact ⟨_,h⟩
    exact ⟨e,he,hM,D,by omega,hd,congrFun hc⟩
  · obtain ⟨e,he,hM,D,hs,hd,hc⟩ := below p l E M C G adj cycle four ao (funext computes) subset injP injL
      (fun T hT => Nat.lt_of_not_ge fun h => budget ⟨T,hT,h⟩)
    exact ⟨e,he,hM,D,hs,hd,congrFun hc⟩
