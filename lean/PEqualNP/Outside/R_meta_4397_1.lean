import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Split the five residual vertices. Each hypothesis is the 29-row monotone
-- size-13 bound for one fixed vertex on the extra OR wire.
theorem PEqualNP.Outside.R_meta_4397_1
    (h1 :
      ∀ (C : Circuit), Monotone2 C → C.size ≤ 13 →
      ∃ (x6 : Fin 29),
        have x7 : ℕ := [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (133 : ℕ), (160 : ℕ), (264 : ℕ), (265 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (200 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x6 0
        have x8 : Fin 9 → Bool := fun i => x7.testBit ↑i
        C.eval (List.ofFn x8 ++ [!x8 0] ++ [x8 4 || x8 (1 : Fin 9)]) ≠
          Decidable.decide (↑x6 < 16))
    (h2 :
      ∀ (C : Circuit), Monotone2 C → C.size ≤ 13 →
      ∃ (x6 : Fin 29),
        have x7 : ℕ := [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (133 : ℕ), (160 : ℕ), (264 : ℕ), (265 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (200 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x6 0
        have x8 : Fin 9 → Bool := fun i => x7.testBit ↑i
        C.eval (List.ofFn x8 ++ [!x8 0] ++ [x8 4 || x8 (2 : Fin 9)]) ≠
          Decidable.decide (↑x6 < 16))
    (h3 :
      ∀ (C : Circuit), Monotone2 C → C.size ≤ 13 →
      ∃ (x6 : Fin 29),
        have x7 : ℕ := [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (133 : ℕ), (160 : ℕ), (264 : ℕ), (265 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (200 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x6 0
        have x8 : Fin 9 → Bool := fun i => x7.testBit ↑i
        C.eval (List.ofFn x8 ++ [!x8 0] ++ [x8 4 || x8 (3 : Fin 9)]) ≠
          Decidable.decide (↑x6 < 16))
    (h4 :
      ∀ (C : Circuit), Monotone2 C → C.size ≤ 13 →
      ∃ (x6 : Fin 29),
        have x7 : ℕ := [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (133 : ℕ), (160 : ℕ), (264 : ℕ), (265 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (200 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x6 0
        have x8 : Fin 9 → Bool := fun i => x7.testBit ↑i
        C.eval (List.ofFn x8 ++ [!x8 0] ++ [x8 4 || x8 (4 : Fin 9)]) ≠
          Decidable.decide (↑x6 < 16))
    (h6 :
      ∀ (C : Circuit), Monotone2 C → C.size ≤ 13 →
      ∃ (x6 : Fin 29),
        have x7 : ℕ := [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (133 : ℕ), (160 : ℕ), (264 : ℕ), (265 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (200 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x6 0
        have x8 : Fin 9 → Bool := fun i => x7.testBit ↑i
        C.eval (List.ofFn x8 ++ [!x8 0] ++ [x8 4 || x8 (6 : Fin 9)]) ≠
          Decidable.decide (↑x6 < 16)) :
    ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.Monotone2 x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (29 : ℕ)),           have x7 : ℕ := [(3 : ℕ), (6 : ℕ), (12 : ℕ), (13 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (133 : ℕ), (160 : ℕ), (264 : ℕ), (265 : ℕ), (288 : ℕ), (320 : ℕ), (321 : ℕ), (42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (200 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)].getD ↑x6 (0 : ℕ);           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.testBit ↑x8;           x3.eval (List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))] ++ [x8 (4 : Fin (9 : ℕ)) || x8 x1]) ≠ Decidable.decide (↑x6 < (16 : ℕ)) := by
  intro v hv C hm hs
  dsimp only
  have hv' : v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 6 := by
    simpa [List.mem_cons] using hv
  rcases hv' with rfl | rfl | rfl | rfl | rfl
  · exact h1 C hm hs
  · exact h2 C hm hs
  · exact h3 C hm hs
  · exact h4 C hm hs
  · exact h6 C hm hs
