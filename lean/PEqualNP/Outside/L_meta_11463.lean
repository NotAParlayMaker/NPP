import PEqualNP.Defs

-- The low seven bits select points and the high seven bits select lines.
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.L_meta_11463 :
    ∀ points : Fin 7 → Bool,
      ∃ mask ∈ ([127, 244, 480, 720, 1188, 3008, 16256] : List ℕ), ∃ shift : Fin 7,
        (∀ p : Fin 7, points p = true → mask.testBit (p + shift).val = true) ∧
        (∀ l : Fin 7, points l = false → points (l + 1) = false → points (l + 3) = false →
          mask.testBit (7 + (l + shift).val) = true) := by
  decide +kernel
