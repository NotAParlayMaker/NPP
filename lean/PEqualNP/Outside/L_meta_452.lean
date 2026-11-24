import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_452 : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  intro k m r hne hred
  obtain ⟨j, hj⟩ := hred
  let v : {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} → (Fin m → ℚ) :=
    fun i => r i.1
  have hli : LinearIndependent ℚ v := by
    rw [linearIndependent_iff_notMem_span]
    intro i hi
    apply i.2
    refine Submodule.span_mono ?_ hi
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a.1, ?_, rfl⟩
    show a.1 ≠ i.1
    intro h
    exact ha.2 (Set.mem_singleton_iff.2 (Subtype.ext h))
  have hnot : r j ∉ Submodule.span ℚ (Set.range v) := by
    intro hmem
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hex : ∃ i, c i ≠ 0 := by
      by_contra hall
      apply hne j
      rw [← hc]
      refine Finset.sum_eq_zero ?_
      intro i _
      have hci : c i = 0 := by
        by_contra hci
        exact hall ⟨i, hci⟩
      rw [hci, zero_smul]
    obtain ⟨i0, hi0⟩ := hex
    have hji : j ≠ i0.1 := by
      intro h
      apply i0.2
      rw [← h]
      exact hj
    have hsum := Finset.add_sum_erase Finset.univ (fun i => c i • v i) (Finset.mem_univ i0)
    have hsplit : c i0 • v i0 = r j - ∑ i ∈ Finset.univ.erase i0, c i • v i := by
      rw [← hc]
      exact eq_sub_of_add_eq hsum
    have hrep : (c i0)⁻¹ • (r j - ∑ i ∈ Finset.univ.erase i0, c i • v i) = r i0.1 := by
      rw [← hsplit]
      exact inv_smul_smul₀ hi0 _
    have hmem2 : (c i0)⁻¹ • (r j - ∑ i ∈ Finset.univ.erase i0, c i • v i) ∈
        Submodule.span ℚ (r '' {l | l ≠ i0.1}) := by
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
      · exact Submodule.subset_span ⟨j, hji, rfl⟩
      · refine Submodule.sum_mem _ ?_
        intro i hi
        refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.1, ?_, rfl⟩)
        show i.1 ≠ i0.1
        intro h
        exact Finset.ne_of_mem_erase hi (Subtype.ext h)
    rw [hrep] at hmem2
    exact i0.2 hmem2
  have hlt : Submodule.span ℚ (Set.range v) < Submodule.span ℚ (Set.range r) := by
    refine lt_of_le_of_ne (Submodule.span_mono ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
    · intro heq
      apply hnot
      rw [heq]
      exact Submodule.subset_span ⟨j, rfl⟩
  have h1 : Module.finrank ℚ (Submodule.span ℚ (Set.range v)) = Fintype.card _ :=
    finrank_span_eq_card hli
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [Nat.card_eq_fintype_card]
  omega
