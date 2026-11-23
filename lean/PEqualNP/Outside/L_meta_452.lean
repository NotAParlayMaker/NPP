import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_452 : ∀ (k m : ℕ) (r : Fin k → (Fin m → ℚ)),
    (∀ i, r i ≠ 0) →
    (∃ j : Fin k, r j ∈ Submodule.span ℚ (r '' {l | l ≠ j})) →
    Nat.card {i : Fin k // r i ∉ Submodule.span ℚ (r '' {j | j ≠ i})} + 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range r)) := by
  classical
  intro k m r hne ⟨j, hj⟩
  -- (b) the redundant vector is not in the span of any finset of essential vectors
  have hb : ∀ T : Finset (Fin k),
      (∀ i ∈ T, r i ∉ Submodule.span ℚ (r '' {l | l ≠ i})) →
      r j ∉ Submodule.span ℚ (r '' (T : Set (Fin k))) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ h
      simp at h
      exact hne j h
    | insert a T ha ih =>
      intro hT h
      have h1 : r j ∉ Submodule.span ℚ (r '' (T : Set (Fin k))) :=
        ih (fun i hi => hT i (Finset.mem_insert_of_mem hi))
      rw [Finset.coe_insert, Set.image_insert_eq] at h
      have h2 := mem_span_insert_exchange h h1
      have hja : j ≠ a := by
        rintro rfl
        exact hT j (Finset.mem_insert_self _ _) hj
      apply hT a (Finset.mem_insert_self _ _)
      refine Submodule.span_mono ?_ h2
      rintro x (rfl | ⟨l, hl, rfl⟩)
      · exact ⟨j, hja, rfl⟩
      · refine ⟨l, ?_, rfl⟩
        rintro rfl
        exact ha (by exact_mod_cast hl)
  set P : Fin k → Prop := fun i => r i ∉ Submodule.span ℚ (r '' {j | j ≠ i}) with hP
  let f : Option {i : Fin k // P i} → (Fin m → ℚ) := fun o => o.elim (r j) (fun i => r i)
  have hf : LinearIndependent ℚ f := by
    rw [linearIndependent_iff_notMem_span]
    intro o ho
    cases o with
    | none =>
      apply hb (Finset.univ.filter P) (fun i hi => (Finset.mem_filter.mp hi).2)
      refine Submodule.span_mono ?_ ho
      rintro x ⟨o, ho', rfl⟩
      cases o with
      | none => simp at ho'
      | some i => exact ⟨i.1, by simp [i.2], rfl⟩
    | some i =>
      apply i.2
      refine Submodule.span_mono ?_ ho
      rintro x ⟨o, ho', rfl⟩
      cases o with
      | none =>
        refine ⟨j, ?_, rfl⟩
        rintro h
        exact i.2 (h ▸ hj)
      | some i' =>
        refine ⟨i'.1, ?_, rfl⟩
        intro h
        apply ho'.2
        simp [Subtype.ext_iff, h]
  have hcard := finrank_span_eq_card hf
  have hle : Submodule.span ℚ (Set.range f) ≤ Submodule.span ℚ (Set.range r) := by
    apply Submodule.span_mono
    rintro x ⟨o, rfl⟩
    cases o with
    | none => exact ⟨j, rfl⟩
    | some i => exact ⟨i.1, rfl⟩
  have := Submodule.finrank_mono hle
  rw [hcard, Fintype.card_option] at this
  rw [Nat.card_eq_fintype_card]
  exact this
