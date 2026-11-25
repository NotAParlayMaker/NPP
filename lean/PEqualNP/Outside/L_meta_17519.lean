import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17519 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → x1.size = (0 : ℕ) → (59 : ℕ) ≤ x1.size := by
  intro C hout _ hfun hzero
  obtain ⟨gs, out⟩ := C
  have hg : gs = [] := List.length_eq_zero_iff.mp hzero
  subst gs
  have h := (hfun (fun _ => true)).2 ⟨1, 1, Or.inl rfl, by decide, rfl, rfl⟩
  change (List.ofFn (fun _ : Fin 26 => true)).getD out false = true at h
  have bound : (List.ofFn (fun _ : Fin 26 => true)).length ≤ out := by simpa using hout
  rw [List.getD_eq_default _ _ bound] at h
  contradiction
