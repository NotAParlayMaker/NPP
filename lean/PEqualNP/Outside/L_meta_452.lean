import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_452

/-- The essential vectors of a finite family are linearly independent. -/
theorem essential_linearIndependent {k m : ℕ} (r : Fin k → (Fin m → ℚ)) :
    LinearIndependent ℚ
      (fun i : {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} => r i.1) := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have hmem : r i.1 ∈ Submodule.span ℚ (r '' {j | j ≠ i.1}) := by
    have hsplit : (∑ j ∈ s.erase i, g j • r j.1) + g i • r i.1 = 0 := by
      rw [Finset.sum_erase_add s (fun j => g j • r j.1) hi]
      exact hsum
    have hneg : g i • r i.1 = - ∑ j ∈ s.erase i, g j • r j.1 :=
      eq_neg_of_add_eq_zero_right hsplit
    have hri : r i.1 = (g i)⁻¹ • (- ∑ j ∈ s.erase i, g j • r j.1) := by
      calc r i.1 = (g i)⁻¹ • (g i • r i.1) := by
            rw [smul_smul, inv_mul_cancel₀ hgi, one_smul]
        _ = (g i)⁻¹ • (- ∑ j ∈ s.erase i, g j • r j.1) := by
            rw [hneg]
    rw [hri]
    refine Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sum_mem _ ?_))
    intro j hj
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨j.1, ?_, rfl⟩
    rw [Finset.mem_erase] at hj
    exact fun h => hj.1 (Subtype.ext h)
  exact i.2 hmem

/-- The number of essential vectors is at most the rank of the span. -/
theorem essential_card_le_finrank {k m : ℕ} (r : Fin k → (Fin m → ℚ)) :
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  let S := {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})}
  change Nat.card S ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range r))
  haveI : Fintype S := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card]
  have hli : LinearIndependent ℚ (fun i : S => r i.1) := essential_linearIndependent r
  have h1 : Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : S => r i.1))) =
      Fintype.card S :=
    finrank_span_eq_card hli
  have h2 : Submodule.span ℚ (Set.range (fun i : S => r i.1)) ≤
      Submodule.span ℚ (Set.range r) := by
    refine Submodule.span_mono ?_
    rintro x ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  have h3 : Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : S => r i.1))) ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) :=
    Submodule.finrank_mono h2
  calc Fintype.card S =
        Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : S => r i.1))) := h1.symm
    _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := h3

/-- A redundant vector forces the dimension to exceed the number of essentials. -/
theorem essential_card_succ_le_finrank {k m : ℕ} (r : Fin k → (Fin m → ℚ))
    (hne : ∀ i, r i ≠ 0)
    (hred : ∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) :
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  let S := {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})}
  change Nat.card S + 1 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range r))
  haveI : Fintype S := Fintype.ofFinite S
  have hle : Nat.card S ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range r)) :=
    essential_card_le_finrank r
  by_contra hcon
  have hge : Module.finrank ℚ (Submodule.span ℚ (Set.range r)) ≤ Nat.card S := by
    omega
  have heq : Module.finrank ℚ (Submodule.span ℚ (Set.range r)) = Nat.card S :=
    le_antisymm hge hle
  have hli : LinearIndependent ℚ (fun i : S => r i.1) := essential_linearIndependent r
  have hWfin : Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : S => r i.1))) =
      Nat.card S := by
    rw [finrank_span_eq_card hli, Nat.card_eq_fintype_card]
  have hWV : Submodule.span ℚ (Set.range (fun i : S => r i.1)) ≤
      Submodule.span ℚ (Set.range r) := by
    refine Submodule.span_mono ?_
    rintro x ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  have hVeq : Submodule.span ℚ (Set.range r) =
      Submodule.span ℚ (Set.range (fun i : S => r i.1)) := by
    have heqfin : Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : S => r i.1))) =
        Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
      rw [hWfin]
      exact heq.symm
    exact (Submodule.eq_of_le_of_finrank_eq hWV heqfin).symm
  obtain ⟨j, hj⟩ := hred
  by_cases hEss : r j ∉ Submodule.span ℚ (r '' {l | l ≠ j})
  · exact hEss hj
  · have hjnot : r j ∈ Submodule.span ℚ (r '' {l | l ≠ j}) := not_not.mp hEss
    have hjW : r j ∈ Submodule.span ℚ (Set.range (fun i : S => r i.1)) := by
      rw [← hVeq]
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hjW
    have hex : ∃ i : S, a i ≠ 0 := by
      by_contra h
      push_neg at h
      have hzero : ∑ t : S, a t • r t.1 = 0 := by
        simp [h]
      rw [hzero] at ha
      exact hne j ha.symm
    obtain ⟨i, hai⟩ := hex
    have hmem : r i.1 ∈ Submodule.span ℚ (r '' {l | l ≠ i.1}) := by
      have hsplit : (∑ t ∈ Finset.univ.erase i, a t • r t.1) + a i • r i.1 = r j := by
        rw [Finset.sum_erase_add (Finset.univ : Finset S) (fun t => a t • r t.1)
          (Finset.mem_univ i)]
        exact ha
      have hsub : a i • r i.1 = r j - ∑ t ∈ Finset.univ.erase i, a t • r t.1 := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact hsplit
      have hri : r i.1 = (a i)⁻¹ • (r j - ∑ t ∈ Finset.univ.erase i, a t • r t.1) := by
        calc r i.1 = (a i)⁻¹ • (a i • r i.1) := by
              rw [smul_smul, inv_mul_cancel₀ hai, one_smul]
          _ = (a i)⁻¹ • (r j - ∑ t ∈ Finset.univ.erase i, a t • r t.1) := by
              rw [hsub]
      rw [hri]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
      · refine Submodule.subset_span ?_
        refine ⟨j, ?_, rfl⟩
        intro h
        rw [h] at hjnot
        exact i.2 hjnot
      · refine Submodule.sum_mem _ ?_
        intro t ht
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        rw [Finset.mem_erase] at ht
        exact ⟨t.1, fun h => ht.1 (Subtype.ext h), rfl⟩
    exact i.2 hmem

end PEqualNP.Outside.L_meta_452

theorem PEqualNP.Outside.L_meta_452 : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  intro k m r hne hred
  exact PEqualNP.Outside.L_meta_452.essential_card_succ_le_finrank r hne hred
