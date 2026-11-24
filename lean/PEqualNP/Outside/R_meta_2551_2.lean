import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2551_2
    (encode :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) → let seeds : List (BitVec 24) := [0, 16777215, 4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888, 16646144, 13339321]; ∃ values : List (BitVec 24), values.length ≤ x1.size ∧ (∀ j (hj : j < values.length), values[j] ∉ seeds ++ values.take j ∧ ∃ a ∈ seeds ++ values.take j, ∃ b ∈ seeds ++ values.take j, values[j] = a &&& b ∨ values[j] = a ||| b) ∧ 3428671 ∈ seeds ++ values)
    (exclude :
      let seeds : List (BitVec 24) := [0, 16777215, 4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888, 16646144, 13339321]; ∀ values : List (BitVec 24), values.length ≤ 14 → (∀ j (hj : j < values.length), values[j] ∉ seeds ++ values.take j ∧ ∃ a ∈ seeds ++ values.take j, ∃ b ∈ seeds ++ values.take j, values[j] = a &&& b ∨ values[j] = a ||| b) → 3428671 ∉ seeds ++ values) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ))]) = (fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) x3) → (15 : ℕ) ≤ x1.size := by
  intro C hm hfull
  by_contra hsmall
  have hrows : ∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)], have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5; C.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)]) := by
    intro n hn
    let x : Fin (9 : ℕ) → Bool := fun i => n.testBit ↑i
    change C.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ))]) = Decidable.decide (n ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])
    rw [hfull x]
    simp only [List.mem_cons] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hn
    all_goals first | decide | cases hn
  obtain ⟨values, hsize, hreach, houtput⟩ := encode C hm hrows
  exact exclude values (Nat.le_trans hsize (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hsmall))) hreach houtput

