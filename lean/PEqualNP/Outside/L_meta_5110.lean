import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5110 : ∃ (x1 : List (Bool × ℕ × ℕ)), (1 : ℕ) ≤ x1.length ∧ x1.length ≤ (8 : ℕ) ∧ (List.foldl (fun (x2 : List ℕ) (x3 : Bool × ℕ × ℕ) => x2 ++ [if x3.1 = Bool.true then x2.getD x3.2.1 (0 : ℕ) ||| x2.getD x3.2.2 (0 : ℕ) else x2.getD x3.2.1 (0 : ℕ) &&& x2.getD x3.2.2 (0 : ℕ)]) [(95229015649944073 : ℕ), (63038587928642 : ℕ), (4292497062825988 : ℕ), (189297016294080519 : ℕ), (192860064594267704 : ℕ), (288166778660192704 : ℕ), (283797140973809664 : ℕ)] x1).getD ((7 : ℕ) + x1.length - (1 : ℕ)) (0 : ℕ) = (332367 : ℕ) :=
  ⟨[(true, 3, 6), (true, 3, 4), (true, 3, 5), (false, 1, 9), (false, 0, 8), (true, 10, 11), (false, 2, 7), (true, 12, 13)], by decide +kernel⟩
