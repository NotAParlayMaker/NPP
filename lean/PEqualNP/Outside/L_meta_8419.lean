import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8419 : let x1 : Type := Fin (21 : ℕ); have x2 : x1 → Finset x1 := fun (x2 : x1) => {x3 : x1 | (↑x2 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]}; have x3 : (Fin (42 : ℕ) → Bool) → Prop := fun (x3 : Fin (42 : ℕ) → Bool) => ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true; ∀ (x4 : Fin (42 : ℕ) → Bool), x3 x4 → (∀ (x6 : Fin (42 : ℕ) → Bool), (∀ (x7 : Fin (42 : ℕ)), x6 x7 = Bool.true → x4 x7 = Bool.true) → x3 x6 → x6 = x4) → ∃ (x7 : x1) (x8 : x1), x7 ∈ x2 x8 ∧ List.ofFn x4 = PEqualNP.GenericRejection.incidenceInput {x7} {x8} := by
  intro x1 x2 x3 x4 hx4 hmin
  obtain ⟨a, b, ⟨ha, hb, hk⟩, h4a, h4b⟩ := hx4
  have he := hmin (fun i => (i == a || i == b)) (by
    intro i hi
    simp only [Bool.or_eq_true, beq_iff_eq] at hi
    rcases hi with h | h <;> subst h <;> assumption) ⟨a, b, ⟨ha, hb, hk⟩, by simp, by simp⟩
  subst he
  refine ⟨⟨a, by omega⟩, ⟨b - 21, by omega⟩, ?_, ?_⟩
  · simp only [x2, Finset.mem_filter, Finset.mem_univ, true_and]
    have e : ((b : ℕ) - 21 + 21 - (a : ℕ)) % 21 = ((b : ℕ) + 21 - (a : ℕ)) % 21 := by omega
    simpa [e] using hk
  · unfold PEqualNP.GenericRejection.incidenceInput
    refine (List.ofFn_add (n := 21) (m := 21) (f := fun i => (i == a || i == b))).trans ?_
    congr 1
    · congr 1
      funext i
      simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_castLE, Finset.mem_singleton]
      by_cases h : (i : ℕ) = a <;> simp [h, Fin.ext_iff, Fin.val_castLE, Fin.val_addNat, Fin.val_castAdd, Fin.val_natAdd] <;> omega
    · congr 1
      funext i
      simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_addNat, Finset.mem_singleton]
      by_cases h : (i : ℕ) = b - 21 <;> simp [h, Fin.ext_iff, Fin.val_castLE, Fin.val_addNat, Fin.val_castAdd, Fin.val_natAdd] <;> omega
