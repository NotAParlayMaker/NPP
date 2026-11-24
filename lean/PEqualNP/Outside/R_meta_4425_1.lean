import PEqualNP.Defs

-- Membership in `seed ++ xs` splits: the concrete seed carries the decidable part (`base`),
-- the carried spine carries the content (`spine`).
theorem PEqualNP.Outside.R_meta_4425_1
    (base :
      BitVec.ofNat (512 : ℕ)
        ((18446744060824649720 : ℕ) * (2 : ℕ) ^ (64 : ℕ) + (18441958779708426440 : ℕ)) ∉
        List.map (fun (x1 : ℕ) =>
          BitVec.ofNat (512 : ℕ)
            (((2 : ℕ) ^ (128 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x1 + (1 : ℕ)) *
              (2 : ℕ) ^ (2 : ℕ) ^ x1)) (List.range (7 : ℕ)))
    (spine : ∀ (x3 : List (BitVec (512 : ℕ))),
        x3.length ≤ (10 : ℕ) →
        (∀ (x5 : Fin x3.length),
          ∃ x7 ∈
              (List.map (fun (x1 : ℕ) =>
                BitVec.ofNat (512 : ℕ)
                  (((2 : ℕ) ^ (128 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x1 + (1 : ℕ)) *
                    (2 : ℕ) ^ (2 : ℕ) ^ x1)) (List.range (7 : ℕ)) ++ List.take (↑x5) x3),
          ∃ x8 ∈
              (List.map (fun (x1 : ℕ) =>
                BitVec.ofNat (512 : ℕ)
                  (((2 : ℕ) ^ (128 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x1 + (1 : ℕ)) *
                    (2 : ℕ) ^ (2 : ℕ) ^ x1)) (List.range (7 : ℕ)) ++ List.take (↑x5) x3),
          ∃ (x9 : Bool) (x10 : Bool),
            x3.get x5 =
              (fun (x2 x3 : Bool) (x4 x5 : BitVec (512 : ℕ)) =>
                have x6 : BitVec (512 : ℕ) :=
                  (if x2 = Bool.true then x4 else ~~~x4) &&& if x3 = Bool.true then x5 else ~~~x5
                if x6.getLsbD (0 : ℕ) = Bool.true then ~~~x6 else x6) x9 x10 x7 x8) →
        BitVec.ofNat (512 : ℕ)
          ((18446744060824649720 : ℕ) * (2 : ℕ) ^ (64 : ℕ) + (18441958779708426440 : ℕ)) ∉ x3) :
    have x1 : List (BitVec (512 : ℕ)) := List.map (fun (x1 : ℕ) => BitVec.ofNat (512 : ℕ) (((2 : ℕ) ^ (128 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x1 + (1 : ℕ)) * (2 : ℕ) ^ (2 : ℕ) ^ x1)) (List.range (7 : ℕ)); have x2 : Bool → Bool → BitVec (512 : ℕ) → BitVec (512 : ℕ) → BitVec (512 : ℕ) := fun (x2 x3 : Bool) (x4 x5 : BitVec (512 : ℕ)) =>   have x6 : BitVec (512 : ℕ) := (if x2 = Bool.true then x4 else ~~~x4) &&& if x3 = Bool.true then x5 else ~~~x5;   if x6.getLsbD (0 : ℕ) = Bool.true then ~~~x6 else x6; ∀ (x3 : List (BitVec (512 : ℕ))),   x3.length ≤ (10 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (BitVec (512 : ℕ)) := x1 ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool) (x10 : Bool), x3.get x5 = x2 x9 x10 x7 x8) →       BitVec.ofNat (512 : ℕ) ((18446744060824649720 : ℕ) * (2 : ℕ) ^ (64 : ℕ) + (18441958779708426440 : ℕ)) ∉ x1 ++ x3 := by
  intro x1 x2 x3 hlen hclos hmem
  exact (List.mem_append.mp hmem).elim base (spine x3 hlen hclos)
