import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7814 : have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (4292497062759936 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (11 : ℕ) ∧ (∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5) ∧ (3647 : ℕ) ∈ x1 ++ x2 := by
  intro x1
  refine ⟨[191866593364673099, 193001360500003407, 7, 264171595797922329, 288167337562522425, 56, 63, 265911111072622089, 283937879088049801, 3584, 3647], by decide, ?_, by simp [x1]⟩
  intro x3
  fin_cases x3
  · exact ⟨189297016294081033, by simp [x1], 155696362464477250, by simp [x1], Or.inr (by decide)⟩
  · exact ⟨183565875465490436, by simp [x1], 191866593364673099, by simp [x1], Or.inr (by decide)⟩
  · exact ⟨95229015649943559, by simp [x1], 193001360500003407, by simp [x1], Or.inl (by decide)⟩
  · exact ⟨189297016294081033, by simp [x1], 218994303132270608, by simp [x1], Or.inr (by decide)⟩
  · exact ⟨288160007407550752, by simp [x1], 264171595797922329, by simp [x1], Or.inr (by decide)⟩
  · exact ⟨63038587666488, by simp [x1], 288167337562522425, by simp [x1], Or.inl (by decide)⟩
  · exact ⟨7, by simp [x1], 56, by simp [x1], Or.inr (by decide)⟩
  · exact ⟨189297016294081033, by simp [x1], 229736628138025984, by simp [x1], Or.inr (by decide)⟩
  · exact ⟨270286071508633728, by simp [x1], 265911111072622089, by simp [x1], Or.inr (by decide)⟩
  · exact ⟨4292497062759936, by simp [x1], 283937879088049801, by simp [x1], Or.inl (by decide)⟩
  · exact ⟨63, by simp [x1], 3584, by simp [x1], Or.inr (by decide)⟩
