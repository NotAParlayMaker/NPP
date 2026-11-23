import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_452 :
    ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
        (∀ i, r i ≠ 0) →
        (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
        Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
          Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  intro k m r hn hred
  obtain ⟨j, hj⟩ := hred
  let E := {i : Fin k // r i ∉ Submodule.span ℚ (r '' {l | l ≠ i})}
  let v : Option E → (Fin m → ℚ) := fun x =>
    match x with
    | none => r j
    | some i => r i.val
  have hli : LinearIndependent ℚ v := by
    apply Fintype.linearIndependent_iff.mpr
    intro g hg
    have he : ∀ e : E, g (some e) = 0 := by
      intro e
      by_contra hge
      let S := Submodule.span ℚ (r '' {l | l ≠ e.val})
      have hv : ∀ x : Option E, x ≠ some e → v x ∈ S := by
        intro x hx
        apply Submodule.subset_span
        cases x with
        | none =>
          refine ⟨j, ?_, rfl⟩
          intro hje
          apply e.property
          simpa [hje] using hj
        | some a =>
          refine ⟨a.val, ?_, rfl⟩
          intro hae
          apply hx
          exact congrArg some (Subtype.ext hae)
      have hrest : (∑ x ∈ Finset.univ.erase (some e), g x • v x) ∈ S := by
        apply S.sum_mem
        intro x hx
        exact S.smul_mem (g x) (hv x (Finset.mem_erase.mp hx).1)
      have hsum : (∑ x ∈ Finset.univ.erase (some e), g x • v x) +
          g (some e) • v (some e) = 0 := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ _)]
        exact hg
      have hmem : g (some e) • v (some e) ∈ S := by
        rw [eq_neg_of_add_eq_zero_right hsum]
        exact S.neg_mem hrest
      exact e.property ((Submodule.smul_mem_iff S hge).mp hmem)
    intro x
    cases x with
    | none =>
      have hz : g none • r j = 0 := by
        simpa [Fintype.sum_option, v, he] using hg
      exact (smul_eq_zero.mp hz).resolve_right (hn j)
    | some e => exact he e
  calc
    Nat.card E + 1 = Fintype.card (Option E) := by
      simp [Nat.card_eq_fintype_card]
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range v)) :=
      (finrank_span_eq_card hli).symm
    _ ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
      apply Submodule.finrank_mono
      apply Submodule.span_mono
      rintro _ ⟨x, rfl⟩
      cases x with
      | none => exact ⟨j, rfl⟩
      | some e => exact ⟨e.val, rfl⟩
