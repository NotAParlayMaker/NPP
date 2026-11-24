import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1593_1
    (hcore : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ v : Fin n, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) → (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) → (∃ i1 j1 : Fin n, G.Adj i1 j1) → ∃ z : Fin n, (∃ u, G.Adj z u) ∧ ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide (∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) s → ∃ t : ℕ, t + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x' : Fin n → Bool => @decide (∃ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i3 j3 ∧ x' i3 = true ∧ x' j3 = true) (Classical.propDecidable _)) t)
    (hstrip : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i1 j1 : Fin n, G.Adj i1 j1) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) s → ∃ b : ℕ, b + A.card ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide (∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) b)
    (hattach : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide (∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) s → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) (s + A.card)) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ v : Fin n, v ∉ A → (G.neighborSet v).ncard = 3) → (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (∃ i1 j1 : Fin n, G.Adj i1 j1) → ∃ z : Fin n, z ∉ A ∧ ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i2 j2 : Fin n, G.Adj i2 j2 ∧ x i2 = true ∧ x j2 = true) (Classical.propDecidable _)) s → ∃ t : ℕ, t + 4 ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x' : Fin n → Bool => @decide ((∃ a' ∈ A, x' a' = true) ∨ ∃ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj i3 j3 ∧ x' i3 = true ∧ x' j3 = true) (Classical.propDecidable _)) t := by
  classical
  intro n G A hd hg ha he
  have degrees (v : Fin n) : (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3 := by
    by_cases hv : v ∈ A
    · left
      have empty : G.neighborSet v = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun u hu => ha v u hu hv
      simp [empty]
    · exact Or.inr (hd v hv)
  obtain ⟨z, ⟨u, hzu⟩, hz⟩ := hcore n G degrees hg he
  refine ⟨z, ha z u hzu, ?_⟩
  intro s hs
  obtain ⟨b, hb, hbase⟩ := hstrip n G A ha he s hs
  obtain ⟨t, ht, hsmall⟩ := hz b hbase
  exact ⟨t + A.card, by omega, hattach n _ A t hsmall⟩
