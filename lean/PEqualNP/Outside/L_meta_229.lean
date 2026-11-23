import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_229 : ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) n ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank n (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) := by
  intro n hn
  let f : (Fin n → Bool) → Bool := fun x => decide (∃ i : Fin n, x i = true)
  change HasTypedRank n f n ∧ ¬ HasTypedRank n f (n - 1)
  classical
  let z : Fin n → Bool := fun _ => false
  have hz : f z = false := by simp [f, z]
  have hz_unique (y : Fin n → Bool) (hy : f y = false) : y = z := by
    funext j
    change y j = false
    by_contra h
    have htrue : f y = true := by
      apply decide_eq_true
      exact ⟨j, by cases hbit : y j <;> simp_all⟩
    simp_all
  constructor
  · let τ := fun (x _y : Fin n → Bool) =>
      if h : ∃ i : Fin n, x i = true then (h.choose : ℕ) else 0
    have htype : IsTyping n f τ := by
      intro x y hx hy
      have hex : ∃ i : Fin n, x i = true := of_decide_eq_true hx
      refine ⟨hex.choose, by simp [τ, hex], ?_⟩
      rw [hz_unique y hy, hex.choose_spec]
      decide
    refine ⟨τ, htype, ?_⟩
    have hb (i : Fin n) : typedMatrix n f τ i false = 0 := by
      ext x y
      have hno : ¬ (f x = true ∧ f y = false ∧ τ x y = (i : ℕ) ∧ x i = false) := by
        rintro ⟨hx, hy, hi, hbit⟩
        obtain ⟨j, hj, hd⟩ := htype x y hx hy
        have hji : j = i := Fin.ext (hj.symm.trans hi)
        subst j
        exact hd (by simpa [hz_unique y hy, z] using hbit)
      simp [typedMatrix, hno]
    have hr (i : Fin n) : (typedMatrix n f τ i true).rank ≤ 1 := by
      let M := typedMatrix n f τ i true
      let A : Matrix (Fin n → Bool) Unit ℚ := fun x _ => M x z
      let B : Matrix Unit (Fin n → Bool) ℚ := fun _ y => if y = z then 1 else 0
      have hprod : M = A * B := by
        ext x y
        change M x y = ∑ k : Unit, A x k * B k y
        by_cases hy : y = z
        · subst y
          simp [A, B]
        · have hf : f y ≠ false := fun h => hy (hz_unique y h)
          simp [M, typedMatrix, A, B, hy, hf]
      change M.rank ≤ 1
      rw [hprod]
      apply (Matrix.rank_mul_le_left A B).trans
      simpa using A.rank_le_card_width
    calc
      _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by
        simpa [Fintype.sum_bool, hb] using hr i
      _ = n := by simp
  · rintro ⟨τ, htype, hsum⟩
    have hr (i : Fin n) : 1 ≤ (typedMatrix n f τ i true).rank := by
      let x : Fin n → Bool := fun j => decide (j = i)
      have hxi : x i = true := by simp [x]
      have hx : f x = true := by
        apply decide_eq_true
        exact ⟨i, hxi⟩
      obtain ⟨j, hj, hd⟩ := htype x z hx hz
      have hji : j = i := by
        by_contra h
        exact hd (by simp [x, z, h])
      subst j
      have hentry : typedMatrix n f τ i true x z = 1 := by
        simp [typedMatrix, hx, hz, hj, hxi]
      let M := typedMatrix n f τ i true
      have hsub : M.submatrix (fun _ : Unit => x) (fun _ : Unit => z) = 1 := by
        ext a b
        cases a
        cases b
        simpa [M, Matrix.one_apply] using hentry
      have hle := M.rank_submatrix_le (fun _ : Unit => x) (fun _ : Unit => z)
      simpa only [hsub, Matrix.rank_one, Fintype.card_unit] using hle
    have hle : n ≤ ∑ i : Fin n, ∑ b : Bool, (typedMatrix n f τ i b).rank := by
      calc
        n = ∑ _i : Fin n, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum fun i _ => by
          rw [Fintype.sum_bool]
          have := hr i
          omega
    omega
