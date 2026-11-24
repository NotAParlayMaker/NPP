import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_452

open Submodule

lemma ess_indep {k m : ℕ} (r : Fin k → (Fin m → ℚ)) :
    LinearIndepOn ℚ r {i | r i ∉ span ℚ (r '' {j | j ≠ i})} := by
  rw [LinearIndepOn, linearIndependent_iff_notMem_span]
  intro i hi
  apply i.2
  refine span_mono ?_ hi
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x.1, fun h => ?_, rfl⟩
  exact hx.2 (Subtype.ext h)

lemma red_notMem {k m : ℕ} (r : Fin k → (Fin m → ℚ)) (hr : ∀ i, r i ≠ 0) (j : Fin k)
    (hj : r j ∈ span ℚ (r '' {l | l ≠ j})) :
    r j ∉ span ℚ (r '' {i | r i ∉ span ℚ (r '' {j | j ≠ i})}) := by
  classical
  intro hin
  obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination ℚ).mp hin
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hr j (by simpa using hlc.symm)
  obtain ⟨i0, hi0⟩ := Finsupp.support_nonempty_iff.mpr hl0
  have hiE : r i0 ∉ span ℚ (r '' {x | x ≠ i0}) := (Finsupp.mem_supported ℚ l).mp hl hi0
  have hji : j ≠ i0 := by
    rintro rfl
    exact hiE hj
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hlc
  have hsplit := Finset.add_sum_erase l.support (fun i => l i • r i) hi0
  rw [hlc] at hsplit
  have hkey : l i0 • r i0 = r j - ∑ i ∈ l.support.erase i0, l i • r i :=
    eq_sub_of_add_eq hsplit
  have hmem : l i0 • r i0 ∈ span ℚ (r '' {x | x ≠ i0}) := by
    rw [hkey]
    refine sub_mem (subset_span ⟨j, hji, rfl⟩) (sum_mem fun i hi => smul_mem _ _ ?_)
    exact subset_span ⟨i, Finset.ne_of_mem_erase hi, rfl⟩
  exact hiE ((smul_mem_iff _ (Finsupp.mem_support_iff.mp hi0)).mp hmem)

lemma main {k m : ℕ} (r : Fin k → (Fin m → ℚ)) (hr : ∀ i, r i ≠ 0)
    (hj : ∃ j : Fin k, r j ∈ span ℚ (r '' {l | l ≠ j})) :
    Nat.card {i : Fin k // r i ∉ span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (span ℚ (Set.range r)) := by
  classical
  obtain ⟨j, hj⟩ := hj
  set E : Set (Fin k) := {i | r i ∉ span ℚ (r '' {j | j ≠ i})} with hEdef
  have hjE : j ∉ E := fun h => h hj
  have hS : LinearIndepOn ℚ r (insert j E) := (ess_indep r).insert (red_notMem r hr j hj)
  have hfr := finrank_span_eq_card hS.linearIndependent
  have hle : span ℚ (Set.range fun x : ↥(insert j E) => r x) ≤ span ℚ (Set.range r) := by
    apply span_mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩
  have hmono := Submodule.finrank_mono hle
  have hcard : Fintype.card ↥(insert j E) = Nat.card ↥E + 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_insert_of_notMem hjE]
  have hE : Nat.card {i : Fin k // r i ∉ span ℚ (r '' {j | j ≠ i})} = Nat.card ↥E := rfl
  omega

end PEqualNP.Outside.L_meta_452

theorem PEqualNP.Outside.L_meta_452 : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  intro k m r hr hj
  exact PEqualNP.Outside.L_meta_452.main r hr hj
