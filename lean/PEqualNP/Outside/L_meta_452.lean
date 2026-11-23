import Mathlib
import PEqualNP.Defs

open Submodule Set

theorem PEqualNP.Outside.L_meta_452 : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  intro k m r hne hred
  obtain ⟨jr, hjr⟩ := hred
  set T := {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} with hTdef
  let g : T → (Fin m → ℚ) := fun t => r t.1
  have hLI : LinearIndependent ℚ g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t0
    by_contra hct0
    refine t0.2 ?_
    have h1 : c t0 • g t0 + ∑ t ∈ Finset.univ.erase t0, c t • g t = 0 := by
      rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ t0)] at hc
      simpa [add_comm] using hc
    have hsolve : g t0 = - (c t0)⁻¹ • ∑ t ∈ Finset.univ.erase t0, c t • g t := by
      have h2 : c t0 • g t0 = - ∑ t ∈ Finset.univ.erase t0, c t • g t := by
        rw [eq_neg_iff_add_eq_zero]; exact h1
      rw [show g t0 = (c t0)⁻¹ • (c t0 • g t0) by
            rw [smul_smul, inv_mul_cancel₀ hct0, one_smul], h2, smul_neg, neg_smul]
    have key : g t0 ∈ Submodule.span ℚ (r '' {j | j ≠ t0.1}) := by
      rw [hsolve]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro t ht
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨t.1, fun hEq => (Finset.mem_erase.mp ht).1 (Subtype.ext hEq), rfl⟩
    exact key
  set V := Submodule.span ℚ (Set.range r) with hVdef
  have hle : Submodule.span ℚ (Set.range g) ≤ V := by
    apply Submodule.span_mono
    rintro x ⟨t, rfl⟩
    exact ⟨t.1, rfl⟩
  have hjr_not : r jr ∉ Submodule.span ℚ (Set.range g) := by
    intro hmem
    rw [mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    by_cases hall : ∀ t, c t = 0
    · exact hne jr (by rw [← hc]; simp [hall])
    · rw [not_forall] at hall
      obtain ⟨t0, hct0⟩ := hall
      refine t0.2 ?_
      have h1 : c t0 • g t0 + ∑ t ∈ Finset.univ.erase t0, c t • g t = r jr := by
        rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ t0)] at hc
        simpa [add_comm] using hc
      have hsolve : g t0 = (c t0)⁻¹ • (r jr - ∑ t ∈ Finset.univ.erase t0, c t • g t) := by
        have h2 : c t0 • g t0 = r jr - ∑ t ∈ Finset.univ.erase t0, c t • g t := by
          rw [eq_sub_iff_add_eq]; exact h1
        rw [← h2, smul_smul, inv_mul_cancel₀ hct0, one_smul]
      have key : g t0 ∈ Submodule.span ℚ (r '' {j | j ≠ t0.1}) := by
        rw [hsolve]
        apply Submodule.smul_mem
        apply Submodule.sub_mem
        · by_cases hEq : jr = t0.1
          · exact absurd hjr (by rw [hEq]; exact t0.2)
          · exact Submodule.subset_span ⟨jr, hEq, rfl⟩
        · apply Submodule.sum_mem
          intro t ht
          apply Submodule.smul_mem
          apply Submodule.subset_span
          exact ⟨t.1, fun hEq => (Finset.mem_erase.mp ht).1 (Subtype.ext hEq), rfl⟩
      exact key
  have hlt : Submodule.span ℚ (Set.range g) < V := by
    refine lt_of_le_of_ne hle ?_
    intro hEqSub
    exact hjr_not (by rw [hEqSub]; exact Submodule.subset_span ⟨jr, rfl⟩)
  have hcard : Module.finrank ℚ (Submodule.span ℚ (Set.range g)) = Fintype.card T :=
    finrank_span_eq_card hLI
  have hfin_lt : Module.finrank ℚ (Submodule.span ℚ (Set.range g)) < Module.finrank ℚ V :=
    Submodule.finrank_lt_finrank_of_lt hlt
  rw [hcard] at hfin_lt
  rw [Nat.card_eq_fintype_card]
  omega
