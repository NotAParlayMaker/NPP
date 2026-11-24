import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_1735_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∀ e ∈ PEqualNP.TopForm.Ustar G C,
      (∃ g ∈ PEqualNP.TopForm.junk G C, e ∈ PEqualNP.TopForm.gammaE G C g ∧ ∃ p ∈ e, p ∈ PEqualNP.TopForm.wmax G C g) ∨ (∃ g ∈ PEqualNP.TopForm.junk G C, ∃ h ∈ PEqualNP.TopForm.junk G C, g ≠ h ∧ e ∈ PEqualNP.TopForm.gammaE G C g ∧ e ∈ PEqualNP.TopForm.gammaE G C h ∧ ∀ x, PEqualNP.EdgeOwnership.gateVal n C g x = true → PEqualNP.EdgeOwnership.gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true))
    (h2 : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) → G.edgeFinset.Nonempty → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ((PEqualNP.TopForm.Ustar G C).filter (fun e => (∃ g ∈ PEqualNP.TopForm.junk G C, e ∈ PEqualNP.TopForm.gammaE G C g ∧ ∃ p ∈ e, p ∈ PEqualNP.TopForm.wmax G C g))).card ≤ c * (C.size + 1))
    (h3 : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) → G.edgeFinset.Nonempty → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ((PEqualNP.TopForm.Ustar G C).filter (fun e => (∃ g ∈ PEqualNP.TopForm.junk G C, ∃ h ∈ PEqualNP.TopForm.junk G C, g ≠ h ∧ e ∈ PEqualNP.TopForm.gammaE G C g ∧ e ∈ PEqualNP.TopForm.gammaE G C h ∧ ∀ x, PEqualNP.EdgeOwnership.gateVal n C g x = true → PEqualNP.EdgeOwnership.gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true))).card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨s,hs⟩ := h2
  obtain ⟨t,ht⟩ := h3
  refine ⟨s+t,?_⟩
  intro n G inst cycles edges C least form
  classical
  let A := (PEqualNP.TopForm.Ustar G C).filter (fun e => (∃ g ∈ PEqualNP.TopForm.junk G C, e ∈ PEqualNP.TopForm.gammaE G C g ∧ ∃ p ∈ e, p ∈ PEqualNP.TopForm.wmax G C g))
  let B := (PEqualNP.TopForm.Ustar G C).filter (fun e => (∃ g ∈ PEqualNP.TopForm.junk G C, ∃ h ∈ PEqualNP.TopForm.junk G C, g ≠ h ∧ e ∈ PEqualNP.TopForm.gammaE G C g ∧ e ∈ PEqualNP.TopForm.gammaE G C h ∧ ∀ x, PEqualNP.EdgeOwnership.gateVal n C g x = true → PEqualNP.EdgeOwnership.gateVal n C h x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true))
  have inc : PEqualNP.TopForm.Ustar G C ⊆ A ∪ B := by
    intro e he
    rcases h1 n G C least.1 least.2.1 e he with ha|hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he,ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he,hb⟩)
  have a : A.card ≤ s * (C.size+1) := hs n G cycles edges C least form
  have b : B.card ≤ t * (C.size+1) := ht n G cycles edges C least form
  rw [Nat.add_mul]
  exact (Finset.card_le_card inc).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add a b))
