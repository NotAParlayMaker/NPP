import Mathlib
import PEqualNP.Defs

open scoped BigOperators

theorem PEqualNP.Outside.L_meta_452 :
    ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
      (∀ i, r i ≠ 0) →
      (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
      Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
        Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  intro k m r hne hred
  classical
  let ι := {i : Fin k // r i ∉ Submodule.span ℚ (r '' {l : Fin k | l ≠ i})}
  haveI : Fintype ι := by
    change Fintype {i : Fin k // r i ∉ Submodule.span ℚ (r '' {l : Fin k | l ≠ i})}
    infer_instance
  have hLI : LinearIndependent ℚ (fun i : ι => r i.1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum i0
    by_contra hg
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
      (fun i => g i • r i.1) (Finset.mem_univ i0)
    rw [hsum] at hsplit
    have hgs : g i0 • r i0.1 = -(∑ x ∈ Finset.univ.erase i0, g x • r x.1) :=
      eq_neg_of_add_eq_zero_right hsplit
    have hri : r i0.1 = (g i0)⁻¹ • (g i0 • r i0.1) := by
      rw [smul_smul, inv_mul_cancel₀ hg, one_smul]
    have hS : (∑ x ∈ Finset.univ.erase i0, g x • r x.1) ∈
        Submodule.span ℚ (r '' {l : Fin k | l ≠ i0.1}) := by
      apply Submodule.sum_mem
      intro x hx
      rw [Finset.mem_erase] at hx
      exact Submodule.smul_mem _ (g x)
        (Submodule.subset_span ⟨x.1, fun h => hx.1 (Subtype.ext h), rfl⟩)
    have hmem : r i0.1 ∈ Submodule.span ℚ (r '' {l : Fin k | l ≠ i0.1}) := by
      rw [hri, hgs]
      exact Submodule.smul_mem _ (g i0)⁻¹ (Submodule.neg_mem _ hS)
    exact i0.2 hmem
  have hfin : Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : ι => r i.1))) =
      Nat.card ι := by
    rw [finrank_span_eq_card hLI, Nat.card_eq_fintype_card]
  have hUW : Submodule.span ℚ (Set.range (fun i : ι => r i.1)) ≤
      Submodule.span ℚ (Set.range r) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  obtain ⟨j, hj⟩ := hred
  have hspanE : ∀ i : ι, i.1 ≠ j := by
    intro i hid
    exact i.2 (by rw [hid]; exact hj)
  have hrj_notU : r j ∉ Submodule.span ℚ (Set.range (fun i : ι => r i.1)) := by
    intro hmem
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hsum_eq : (c.sum fun i a => a • r i.1) = ∑ i ∈ c.support, c i • r i.1 :=
      Finsupp.sum_of_support_subset c (Finset.Subset.refl _) (fun i a => a • r i.1)
        (fun i _ => zero_smul ℚ _)
    have hcne : c ≠ 0 := by
      intro h0
      rw [h0, Finsupp.sum_zero_index] at hc
      exact hne j hc.symm
    obtain ⟨e, he⟩ := Finsupp.support_nonempty_iff.mpr hcne
    have hec : c e ≠ 0 := Finsupp.mem_support_iff.mp he
    have hsplit := Finset.sum_erase_add c.support (fun i => c i • r i.1) he
    have hcomb : (∑ x ∈ c.support.erase e, c x • r x.1) + c e • r e.1 = r j := by
      rw [hsplit, ← hsum_eq]
      exact hc
    have hterm : (∑ x ∈ c.support.erase e, c x • r x.1) ∈
        Submodule.span ℚ (r '' {l : Fin k | l ≠ e.1}) := by
      apply Submodule.sum_mem
      intro x hx
      rw [Finset.mem_erase] at hx
      exact Submodule.smul_mem _ (c x)
        (Submodule.subset_span ⟨x.1, fun h => hx.1 (Subtype.ext h), rfl⟩)
    have hrj_mem : r j ∈ Submodule.span ℚ (r '' {l : Fin k | l ≠ e.1}) :=
      Submodule.subset_span ⟨j, (hspanE e).symm, rfl⟩
    have hce_mem : c e • r e.1 ∈ Submodule.span ℚ (r '' {l : Fin k | l ≠ e.1}) := by
      rw [eq_sub_of_add_eq' hcomb]
      exact Submodule.sub_mem _ hrj_mem hterm
    have hre_mem : r e.1 ∈ Submodule.span ℚ (r '' {l : Fin k | l ≠ e.1}) := by
      rw [show r e.1 = (c e)⁻¹ • (c e • r e.1) by
            rw [smul_smul, inv_mul_cancel₀ hec, one_smul]]
      exact Submodule.smul_mem _ (c e)⁻¹ hce_mem
    exact e.2 hre_mem
  have hUj : r j ∈ Submodule.span ℚ (Set.range r) := Submodule.subset_span ⟨j, rfl⟩
  have hneUW : Submodule.span ℚ (Set.range (fun i : ι => r i.1)) ≠
      Submodule.span ℚ (Set.range r) := by
    intro heq
    rw [← heq] at hUj
    exact hrj_notU hUj
  have hfinlt : Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : ι => r i.1))) <
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hUW hneUW)
  change Nat.card ι + 1 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range r))
  omega
