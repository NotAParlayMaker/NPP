import PEqualNP.Defs

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3672_421
    (normalize :
      ∀ (A T : Type) (step : List A → T → List A) (canonical : T → Prop),
      (∀ s t, step s t = s ∨ ∃ a, step s t = a :: s) →
      (∀ s t a, step s t = a :: s → ∃ t', canonical t' ∧ step s t' = a :: s) →
      ∀ (seed : List A) (ops : List T) (target : A),
        target ∉ seed → target ∈ ops.foldl step seed →
        ∃ effective : List T, effective.length ≤ ops.length ∧
          (∀ t ∈ effective, canonical t) ∧
          let result := effective.foldl step seed
          result.length = seed.length + effective.length ∧ result.head? = some target)
    (remaining :
      have x1 : ℕ → BitVec (512 : ℕ) := fun (x1 : ℕ) => BitVec.ofNat (512 : ℕ) (((2 : ℕ) ^ (512 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x1 + (1 : ℕ)) * (2 : ℕ) ^ (2 : ℕ) ^ x1); have x2 : List (BitVec (512 : ℕ)) := List.map x1 (List.range (9 : ℕ)) ++ [~~~x1 (0 : ℕ), (0 : BitVec (512 : ℕ)), ~~~(0 : BitVec (512 : ℕ))]; have x3 : BitVec (512 : ℕ) := List.foldl (fun (x3 : BitVec (512 : ℕ)) (x4 : ℕ) => x3 ||| x1 (x4 / (10 : ℕ)) &&& x1 (x4 % (10 : ℕ))) (0 : BitVec (512 : ℕ)) [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)]; have x4 : List (BitVec (512 : ℕ)) → Fin (3 : ℕ) × BitVec (512 : ℕ) × BitVec (512 : ℕ) → List (BitVec (512 : ℕ)) := fun (x4 : List (BitVec (512 : ℕ))) (x5 : Fin (3 : ℕ) × BitVec (512 : ℕ) × BitVec (512 : ℕ)) =>   have x6 : BitVec (512 : ℕ) := x5.2.1;   have x7 : BitVec (512 : ℕ) := x5.2.2;   have x8 : BitVec (512 : ℕ) := if x5.1 = (0 : Fin (3 : ℕ)) then x6 &&& x7 else if x5.1 = (1 : Fin (3 : ℕ)) then x6 ||| x7 else ~~~x6;   if x6 ∈ x4 ∧ x7 ∈ x4 ∧ x8 ∉ x4 then x8 :: x4 else x4;
      let canonical := fun op : Fin 3 × BitVec 512 × BitVec 512 => if op.1 = 2 then op.2.1 = op.2.2 else op.2.1.toNat ≤ op.2.2.toNat
      ∀ k ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (29 : ℕ), (30 : ℕ), (31 : ℕ), (37 : ℕ), (39 : ℕ), (42 : ℕ), (50 : ℕ), (53 : ℕ), (73 : ℕ), (75 : ℕ)],
        let seed := (x2.getD (k / 11) 0 ||| x2.getD (k % 11) 0) :: x2
        x3 ∉ seed ∧ ∀ ops : List (Fin 3 × BitVec 512 × BitVec 512), ops.length ≤ 13 →
          (∀ op ∈ ops, canonical op) →
          let result := ops.foldl x4 seed
          result.length = seed.length + ops.length → result.head? ≠ some x3) :
    have x1 : ℕ → BitVec (512 : ℕ) := fun (x1 : ℕ) => BitVec.ofNat (512 : ℕ) (((2 : ℕ) ^ (512 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x1 + (1 : ℕ)) * (2 : ℕ) ^ (2 : ℕ) ^ x1); have x2 : List (BitVec (512 : ℕ)) := List.map x1 (List.range (9 : ℕ)) ++ [~~~x1 (0 : ℕ), (0 : BitVec (512 : ℕ)), ~~~(0 : BitVec (512 : ℕ))]; have x3 : BitVec (512 : ℕ) := List.foldl (fun (x3 : BitVec (512 : ℕ)) (x4 : ℕ) => x3 ||| x1 (x4 / (10 : ℕ)) &&& x1 (x4 % (10 : ℕ))) (0 : BitVec (512 : ℕ)) [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)]; have x4 : List (BitVec (512 : ℕ)) → Fin (3 : ℕ) × BitVec (512 : ℕ) × BitVec (512 : ℕ) → List (BitVec (512 : ℕ)) := fun (x4 : List (BitVec (512 : ℕ))) (x5 : Fin (3 : ℕ) × BitVec (512 : ℕ) × BitVec (512 : ℕ)) =>   have x6 : BitVec (512 : ℕ) := x5.2.1;   have x7 : BitVec (512 : ℕ) := x5.2.2;   have x8 : BitVec (512 : ℕ) := if x5.1 = (0 : Fin (3 : ℕ)) then x6 &&& x7 else if x5.1 = (1 : Fin (3 : ℕ)) then x6 ||| x7 else ~~~x6;   if x6 ∈ x4 ∧ x7 ∈ x4 ∧ x8 ∉ x4 then x8 :: x4 else x4; ∀ x5 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (29 : ℕ), (30 : ℕ), (31 : ℕ), (37 : ℕ), (39 : ℕ), (42 : ℕ), (50 : ℕ), (53 : ℕ), (73 : ℕ), (75 : ℕ)], ∀ (x7 : List (Fin (3 : ℕ) × BitVec (512 : ℕ) × BitVec (512 : ℕ))), x7.length ≤ (13 : ℕ) → x3 ∉ List.foldl x4 ((x2.getD (x5 / (11 : ℕ)) (0 : BitVec (512 : ℕ)) ||| x2.getD (x5 % (11 : ℕ)) (0 : BitVec (512 : ℕ))) :: x2) x7 := by
  classical
  let x1 : ℕ → BitVec (512 : ℕ) := fun (x1 : ℕ) => BitVec.ofNat (512 : ℕ) (((2 : ℕ) ^ (512 : ℕ) - (1 : ℕ)) / ((2 : ℕ) ^ (2 : ℕ) ^ x1 + (1 : ℕ)) * (2 : ℕ) ^ (2 : ℕ) ^ x1)
  let x2 : List (BitVec (512 : ℕ)) := List.map x1 (List.range (9 : ℕ)) ++ [~~~x1 (0 : ℕ), (0 : BitVec (512 : ℕ)), ~~~(0 : BitVec (512 : ℕ))]
  let x3 : BitVec (512 : ℕ) := List.foldl (fun (x3 : BitVec (512 : ℕ)) (x4 : ℕ) => x3 ||| x1 (x4 / (10 : ℕ)) &&& x1 (x4 % (10 : ℕ))) (0 : BitVec (512 : ℕ)) [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)]
  let x4 : List (BitVec (512 : ℕ)) → Fin (3 : ℕ) × BitVec (512 : ℕ) × BitVec (512 : ℕ) → List (BitVec (512 : ℕ)) := fun (x4 : List (BitVec (512 : ℕ))) (x5 : Fin (3 : ℕ) × BitVec (512 : ℕ) × BitVec (512 : ℕ)) =>   have x6 : BitVec (512 : ℕ) := x5.2.1;   have x7 : BitVec (512 : ℕ) := x5.2.2;   have x8 : BitVec (512 : ℕ) := if x5.1 = (0 : Fin (3 : ℕ)) then x6 &&& x7 else if x5.1 = (1 : Fin (3 : ℕ)) then x6 ||| x7 else ~~~x6;   if x6 ∈ x4 ∧ x7 ∈ x4 ∧ x8 ∉ x4 then x8 :: x4 else x4
  let canonical := fun op : Fin 3 × BitVec 512 × BitVec 512 => if op.1 = 2 then op.2.1 = op.2.2 else op.2.1.toNat ≤ op.2.2.toNat
  have steps : ∀ s op, x4 s op = s ∨ ∃ value, x4 s op = value :: s := by
    intro s op
    dsimp [x4]
    split_ifs <;> first | exact Or.inr ⟨_, rfl⟩ | exact Or.inl rfl
  have replacement : ∀ s op value, x4 s op = value :: s →
      ∃ op', canonical op' ∧ x4 s op' = value :: s := by
    intro s op value hAdd
    rcases op with ⟨kind, a, b⟩
    by_cases hNot : kind = 2
    · subst kind
      have h0 : (2 : Fin 3) ≠ 0 := by decide
      have h1 : (2 : Fin 3) ≠ 1 := by decide
      have tested : a ∈ s ∧ b ∈ s ∧ ~~~a ∉ s := by
        by_contra failed
        simp [x4, h0, h1, failed] at hAdd
      refine ⟨(2, a, a), by simp [canonical], ?_⟩
      simpa [x4, h0, h1, tested.1, tested.2.1, tested.2.2] using hAdd
    · by_cases ordered : a.toNat ≤ b.toNat
      · exact ⟨(kind, a, b), by simpa [canonical, hNot] using ordered, hAdd⟩
      · have hba : b.toNat ≤ a.toNat := by omega
        refine ⟨(kind, b, a), by simpa [canonical, hNot] using hba, ?_⟩
        have swapped : x4 s (kind, b, a) = x4 s (kind, a, b) := by
          by_cases h0 : kind = 0
          · simp [x4, h0, BitVec.and_comm, and_left_comm]
          · by_cases h1 : kind = 1
            · simp [x4, h1, BitVec.or_comm, and_left_comm]
            · have hv := kind.isLt
              have hv0 : kind.val ≠ 0 := fun e => h0 (Fin.ext e)
              have hv1 : kind.val ≠ 1 := fun e => h1 (Fin.ext e)
              have hk2 : kind = 2 := Fin.ext (by change kind.val = 2; omega)
              exact (hNot hk2).elim
        exact swapped.trans hAdd
  change ∀ k ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (29 : ℕ), (30 : ℕ), (31 : ℕ), (37 : ℕ), (39 : ℕ), (42 : ℕ), (50 : ℕ), (53 : ℕ), (73 : ℕ), (75 : ℕ)], ∀ ops : List (Fin 3 × BitVec 512 × BitVec 512),
    ops.length ≤ 13 → x3 ∉ ops.foldl x4 ((x2.getD (k / 11) 0 ||| x2.getD (k % 11) 0) :: x2)
  intro k hk ops hlen hTarget
  let seed := (x2.getD (k / 11) 0 ||| x2.getD (k % 11) 0) :: x2
  have hRemaining := remaining k hk
  obtain ⟨eff, hEff, hCanonical, hSize, hHead⟩ :=
    normalize _ _ x4 canonical steps replacement seed ops x3 hRemaining.1 hTarget
  exact hRemaining.2 eff (hEff.trans hlen) hCanonical hSize hHead

