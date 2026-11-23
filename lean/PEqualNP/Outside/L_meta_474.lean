import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity.CoverPromise in
theorem PEqualNP.Outside.L_meta_474 :
    ∀ φ : PEqualNP.Search.CNF, ∀ u ∈ cvcCover φ, ∃ v, (cvcGraph φ).Adj u v := by
  intro φ u hu
  let ψ := cvcFormula φ
  change u ∈ coverOf ψ (fun _ => true) at hu
  change ∃ v, satAdj ψ u v
  cases u with
  | inl lit =>
    rw [coverOf, Finset.inl_mem_disjSum, Finset.mem_image] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨.inl (x, false), rfl, Ne.symm Bool.false_ne_true, hx⟩
  | inr occ =>
    rw [coverOf, Finset.inr_mem_disjSum, Finset.mem_biUnion] at hu
    obtain ⟨i, _, hi⟩ := hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hbound := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    refine ⟨.inl ((clauseAt ψ i)[j]'hbound), ?_⟩
    exact List.getElem?_eq_getElem hbound
