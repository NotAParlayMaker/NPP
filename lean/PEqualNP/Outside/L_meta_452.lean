import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_452 : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  intro k m r hne ⟨j₀, hj₀⟩
  let E : Set (Fin k) := {i : Fin k | r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})}
  let T : Set (Fin k) := insert j₀ E
  have hj₀_not_E : j₀ ∉ E := by
    simp [E, hj₀]
  have hli : LinearIndependent ℚ (fun x : T => r x.1) := by
    rw [linearIndependent_iff']
    intro s g hsum x₀ hx₀
    by_contra hgx₀
    by_cases hE : ∃ y ∈ s, y.1 ∈ E ∧ g y ≠ 0
    · obtain ⟨y, hys, hyE, hgy⟩ := hE
      have hadd : g y • r y.1 + ∑ z ∈ s.erase y, g z • r z.1 = 0 := by
        rw [Finset.add_sum_erase s (fun z => g z • r z.1) hys]
        exact hsum
      have hry : r y.1 = ∑ z ∈ s.erase y, (-(g y)⁻¹ * g z) • r z.1 := by
        have h1 : g y • r y.1 = -(∑ z ∈ s.erase y, g z • r z.1) := eq_neg_of_add_eq_zero_left hadd
        have h2 : r y.1 = (g y)⁻¹ • (g y • r y.1) := by
          rw [inv_smul_smul₀ hgy]
        rw [h2, h1, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [smul_smul, ← neg_smul, neg_mul]
      have hmem : r y.1 ∈ Submodule.span ℚ (r '' {l | l ≠ y.1}) := by
        rw [hry]
        refine Submodule.sum_mem _ fun z hz => ?_
        refine Submodule.smul_mem _ _ ?_
        refine Submodule.subset_span ?_
        refine ⟨z.1, ?_, rfl⟩
        intro hzy
        exact (Finset.mem_erase.mp hz).1 (Subtype.ext hzy)
      exact hyE hmem
    · push Not at hE
      have hx₀_eq : x₀.1 = j₀ := by
        rcases x₀.2 with h | h
        · exact h
        · exact absurd (hE x₀ hx₀ h) hgx₀
      have herase : ∑ z ∈ s.erase x₀, g z • r z.1 = 0 := by
        refine Finset.sum_eq_zero fun z hz => ?_
        have hzne : z.1 ≠ j₀ := by
          intro hzj
          exact (Finset.mem_erase.mp hz).1 (Subtype.ext (hzj.trans hx₀_eq.symm))
        have hzE : z.1 ∈ E := by
          rcases z.2 with h | h
          · exact absurd h hzne
          · exact h
        rw [hE z (Finset.mem_erase.mp hz).2 hzE, zero_smul]
      have hzero : g x₀ • r x₀.1 = 0 := by
        have hadd := Finset.add_sum_erase s (fun z => g z • r z.1) hx₀
        rw [herase, add_zero] at hadd
        exact hadd.trans hsum
      rcases smul_eq_zero.mp hzero with h | h
      · exact hgx₀ h
      · exact hne x₀.1 h
  let V := Submodule.span ℚ (Set.range r)
  let v : T → V := fun x => ⟨r x.1, Submodule.subset_span (Set.mem_range_self x.1)⟩
  have hliV : LinearIndependent ℚ v := hli.of_comp V.subtype
  have hcard_le : Fintype.card T ≤ Module.finrank ℚ V := hliV.fintype_card_le_finrank
  have hcard_eq : Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 = Fintype.card T := by
    rw [Nat.card_eq_fintype_card]
    have hE_eq : Fintype.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} = E.toFinset.card :=
      (Set.toFinset_card E).symm
    have hT_eq : Fintype.card T = T.toFinset.card := (Set.toFinset_card T).symm
    rw [hE_eq, hT_eq]
    have hins : T.toFinset = insert j₀ E.toFinset := by
      ext x
      simp [T]
    rw [hins, Finset.card_insert_of_notMem]
    simp [hj₀_not_E]
  rw [hcard_eq]
  exact hcard_le
