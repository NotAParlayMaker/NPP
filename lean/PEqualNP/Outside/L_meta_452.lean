import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_452

theorem j0_not {k m : ℕ} (r : Fin k → (Fin m → ℚ)) (hne : ∀ i, r i ≠ 0) (j0 : Fin k)
    (E : Finset (Fin k)) (hE : ∀ i ∈ E, r i ∉ Submodule.span ℚ (r '' {j | j ≠ i}))
    (hj0 : j0 ∉ E) : r j0 ∉ Submodule.span ℚ (r '' (E : Set (Fin k))) := by
  intro h
  obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination ℚ).mp h
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hlc
    exact hne j0 hlc.symm
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hl0
  have hiE : i ∈ E := hl hi
  have hli : l i ≠ 0 := Finsupp.mem_support_iff.mp hi
  apply hE i hiE
  have hsplit : l = l.erase i + Finsupp.single i (l i) := (Finsupp.erase_add_single i l).symm
  have hlc2 : r j0 = Finsupp.linearCombination ℚ r (l.erase i) + l i • r i := by
    rw [← hlc]
    conv_lhs => rw [hsplit]
    rw [map_add, Finsupp.linearCombination_single]
  have hA : Finsupp.linearCombination ℚ r (l.erase i) ∈ Submodule.span ℚ (r '' {j | j ≠ i}) := by
    apply (Finsupp.mem_span_image_iff_linearCombination ℚ).mpr
    refine ⟨l.erase i, ?_, rfl⟩
    intro j hj
    simp only [Set.mem_ofPred_eq]
    intro hji
    subst hji
    simp at hj
  have hB : r j0 ∈ Submodule.span ℚ (r '' {j | j ≠ i}) := by
    apply Submodule.subset_span
    refine ⟨j0, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq]
    rintro rfl
    exact hj0 hiE
  have hC : l i • r i ∈ Submodule.span ℚ (r '' {j | j ≠ i}) := by
    have : l i • r i = r j0 - Finsupp.linearCombination ℚ r (l.erase i) := by
      rw [hlc2]; abel
    rw [this]
    exact Submodule.sub_mem _ hB hA
  have := Submodule.smul_mem _ (l i)⁻¹ hC
  rwa [smul_smul, inv_mul_cancel₀ hli, one_smul] at this

theorem key {k m : ℕ} (r : Fin k → (Fin m → ℚ)) (hne : ∀ i, r i ≠ 0) (j0 : Fin k)
    (E : Finset (Fin k)) (hE : ∀ i ∈ E, r i ∉ Submodule.span ℚ (r '' {j | j ≠ i}))
    (hj0 : j0 ∉ E) :
    LinearIndependent ℚ (fun t : (insert j0 E : Finset (Fin k)) => r t) := by
  rw [linearIndependent_iff_notMem_span]
  intro t
  by_cases ht : (t : Fin k) = j0
  · intro hmem
    apply j0_not r hne j0 E hE hj0
    rw [← ht]
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u, ?_, rfl⟩
    have hu' : u ≠ t := hu.2
    have hmemu := u.2
    simp only [Finset.mem_insert] at hmemu
    rcases hmemu with h | h
    · exact absurd (Subtype.ext (h.trans ht.symm)) hu'
    · exact h
  · have htE : (t : Fin k) ∈ E := by
      have := t.2
      simp only [Finset.mem_insert] at this
      exact this.resolve_left ht
    intro hmem
    apply hE t htE
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq]
    intro hut
    exact hu.2 (Subtype.ext hut)

end PEqualNP.Outside.L_meta_452

open PEqualNP.Outside.L_meta_452 in
theorem PEqualNP.Outside.L_meta_452 : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  intro k m r hne hred
  obtain ⟨j0, hj0⟩ := hred
  set E : Finset (Fin k) := Finset.univ.filter (fun i => r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})) with hEdef
  have hE : ∀ i ∈ E, r i ∉ Submodule.span ℚ (r '' {j | j ≠ i}) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hj0E : j0 ∉ E := by
    intro h
    exact (Finset.mem_filter.mp h).2 hj0
  have hli := key r hne j0 E hE hj0E
  have hcard := finrank_span_eq_card hli
  have hsub : Submodule.span ℚ (Set.range (fun t : (insert j0 E : Finset (Fin k)) => r t)) ≤
      Submodule.span ℚ (Set.range r) := by
    apply Submodule.span_mono
    rintro _ ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  have hmono := Submodule.finrank_mono hsub
  have hT : Fintype.card (insert j0 E : Finset (Fin k)) = E.card + 1 := by
    rw [Fintype.card_coe, Finset.card_insert_of_notMem hj0E]
  have hN : Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} = E.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hN]
  rw [hT] at hcard
  omega
