import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_156 : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  intro k m r hr ⟨j, hred⟩
  let E : Set (Fin k) := {i | r i ∉ Submodule.span ℚ (r '' {l | l ≠ i})}
  have hjE : j ∉ E := by
    simpa [E] using hred
  have hjind : LinearIndepOn ℚ r ({j} : Set (Fin k)) :=
    LinearIndepOn.singleton (hr j)
  obtain ⟨b, hbsub, hjsub, hspan, hlin⟩ :=
    exists_linearIndepOn_extension hjind (Set.subset_univ _)
  have hjb : j ∈ b := hjsub (by simp)
  have hEsub : E ⊆ b := by
    intro i hi
    by_contra hnot
    have hs : b ⊆ {l : Fin k | l ≠ i} := by
      intro l hl
      change l ≠ i
      intro heq
      apply hnot
      simpa [heq] using hl
    have hw : r i ∈ Submodule.span ℚ (r '' b) :=
      hspan ⟨i, Set.mem_univ i, rfl⟩
    have hspanmon : Submodule.span ℚ (r '' b) ≤
        Submodule.span ℚ (r '' {l : Fin k | l ≠ i}) :=
      Submodule.span_mono (Set.image_mono hs)
    exact hi (hspanmon hw)
  have hspanEq : Submodule.span ℚ (r '' b) =
      Submodule.span ℚ (Set.range r) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro v ⟨i, hi, rfl⟩
      exact ⟨i, rfl⟩
    · apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      exact hspan ⟨i, Set.mem_univ i, rfl⟩
  have hrange : Set.range (fun i : b => r i) = r '' b := by
    ext x
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hdim : Module.finrank ℚ (Submodule.span ℚ (r '' b)) = b.toFinset.card := by
    rw [← hrange, finrank_span_eq_card hlin]
    simp only [← Nat.card_eq_fintype_card, ← Set.ncard_eq_toFinset_card']
    exact Nat.card_coe_set_eq b
  have hjbF : j ∈ b.toFinset := Set.mem_toFinset.mpr hjb
  have hjnotF : j ∉ E.toFinset := by
    simpa using hjE
  have hEB : E.toFinset ⊆ b.toFinset := by
    intro i hi
    exact Set.mem_toFinset.mpr (hEsub (Set.mem_toFinset.mp hi))
  have hcard : E.toFinset.card + 1 ≤ b.toFinset.card := by
    have h := Finset.card_le_card
      (Finset.insert_subset_iff.mpr ⟨hjbF, hEB⟩)
    simpa [hjnotF] using h
  change E.ncard + 1 ≤ _
  rw [Set.ncard_eq_toFinset_card' E]
  calc
    E.toFinset.card + 1 ≤ b.toFinset.card := hcard
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
      rw [← hspanEq, hdim]
