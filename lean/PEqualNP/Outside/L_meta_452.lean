import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_452

theorem submodule_sum_mem {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [DecidableEq ι] (p : Submodule R M) (s : Finset ι) (f : ι → M) (hf : ∀ i ∈ s, f i ∈ p) :
    ∑ i ∈ s, f i ∈ p := by
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact p.zero_mem
  · intro a s ha ih hfs
    rw [Finset.sum_insert ha]
    exact p.add_mem (hfs a (by simp)) (ih fun i hi => hfs i (by simp [hi]))

def witnessVec {k m : ℕ} (r : Fin k → (Fin m → ℚ)) (j₀ : Fin k) :
    Option {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} →
      Submodule.span ℚ (Set.range r)
  | none => ⟨r j₀, Submodule.subset_span ⟨j₀, rfl⟩⟩
  | some i => ⟨r i.1, Submodule.subset_span ⟨i.1, rfl⟩⟩

theorem witnessVec_linearIndependent {k m : ℕ} (r : Fin k → (Fin m → ℚ))
    (hr : ∀ i, r i ≠ 0) (j₀ : Fin k)
    (hj₀ : r j₀ ∈ Submodule.span ℚ (r '' {l | l ≠ j₀}))
    [Fintype {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})}] :
    LinearIndependent ℚ (witnessVec r j₀) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_option] at hg
  have hg' : g none • r j₀ + ∑ i, g (some i) • r i.1 = 0 := by
    simpa [witnessVec] using
      congr_arg (fun y : Submodule.span ℚ (Set.range r) => (y : Fin m → ℚ)) hg
  have h_some : ∀ i, g (some i) = 0 := by
    intro i₀
    by_contra hi₀
    rw [← Finset.add_sum_erase Finset.univ (fun i => g (some i) • r i.1)
      (Finset.mem_univ i₀)] at hg'
    have h_eq : g (some i₀) • r i₀.1 =
        -(g none • r j₀ + ∑ i ∈ Finset.univ.erase i₀, g (some i) • r i.1) := by
      rw [eq_neg_iff_add_eq_zero, ← hg']
      exact add_left_comm _ _ _
    have h_ri₀ : r i₀.1 = (g (some i₀))⁻¹ •
        -(g none • r j₀ + ∑ i ∈ Finset.univ.erase i₀, g (some i) • r i.1) := by
      rw [← h_eq, inv_smul_smul₀ hi₀]
    have hj₀_ne : j₀ ≠ i₀.1 := by
      intro heq
      apply i₀.2
      rw [← heq]
      exact hj₀
    have h_sum_mem : ∑ i ∈ Finset.univ.erase i₀, g (some i) • r i.1 ∈
        Submodule.span ℚ (r '' {j | j ≠ i₀.1}) := by
      refine submodule_sum_mem _ _ _ fun i hi => ?_
      have hi_ne : i.1 ≠ i₀.1 := fun h => (Finset.mem_erase.mp hi).1 (Subtype.ext h)
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.1, hi_ne, rfl⟩)
    have h_mem : r i₀.1 ∈ Submodule.span ℚ (r '' {j | j ≠ i₀.1}) := by
      rw [h_ri₀]
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _
        (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j₀, hj₀_ne, rfl⟩))
          h_sum_mem))
    exact i₀.2 h_mem
  have h_none : g none = 0 := by
    have h_zero : ∑ i, g (some i) • r i.1 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [h_some i, zero_smul]
    rw [h_zero, add_zero] at hg'
    by_contra hgn
    apply hr j₀
    calc
      r j₀ = (g none)⁻¹ • (g none • r j₀) := (inv_smul_smul₀ hgn _).symm
      _ = (g none)⁻¹ • 0 := by rw [hg']
      _ = 0 := smul_zero _
  intro x
  cases x with
  | none => exact h_none
  | some i => exact h_some i

end PEqualNP.Outside.L_meta_452

theorem PEqualNP.Outside.L_meta_452 :
    ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  intro k m r hr ⟨j₀, hj₀⟩
  classical
  have h_indep : LinearIndependent ℚ (PEqualNP.Outside.L_meta_452.witnessVec r j₀) :=
    PEqualNP.Outside.L_meta_452.witnessVec_linearIndependent r hr j₀ hj₀
  have h_le := h_indep.fintype_card_le_finrank
  rw [Fintype.card_option] at h_le
  rw [Nat.card_eq_fintype_card]
  exact h_le
