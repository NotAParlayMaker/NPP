import PEqualNP.Defs

namespace ParityFourBound

open PEqualNP.MetaComplexity

private theorem minorBound (A : Matrix (Fin 4) (Fin 4) ℚ) {k : ℕ}
    (r : Fin k → Fin 4) (h : (A.submatrix r r).det ≠ 0) : k ≤ A.rank := by
  have hr := A.rank_submatrix_le r r
  simpa [(Matrix.rank_of_det_ne_zero h)] using hr

-- A diagonal-one matrix with rank at most two must have at least two
-- off-diagonal entries counted with multiplicity in each principal triple.
-- Summing over the four triples counts every off-diagonal entry twice.
private theorem weightRank (w : Fin 4 → Fin 4 → ℕ) (hd : ∀ i, w i i = 1) :
    let A : Matrix (Fin 4) (Fin 4) ℚ := fun i j => w i j
    16 ≤ 4 * A.rank + ∑ i, ∑ j, w i j := by
  classical
  let A : Matrix (Fin 4) (Fin 4) ℚ := fun i j => w i j
  change 16 ≤ 4 * A.rank + _
  have h1 : 1 ≤ A.rank := by
    apply minorBound A (fun _ => 0)
    simp [Matrix.submatrix, A, hd]
  have pair (i j : Fin 4) (hz : w i j = 0) : 2 ≤ A.rank := by
    apply minorBound A ![i,j]
    simp [Matrix.det_fin_two, Matrix.submatrix, A, hd, hz]
  have triple (i j k : Fin 4)
      (small : w i j + w i k + w j i + w j k + w k i + w k j < 2) : 3 ≤ A.rank := by
    apply minorBound A ![i,j,k]
    have few :
        (w i k = 0 ∧ w j i = 0 ∧ w j k = 0 ∧ w k i = 0 ∧ w k j = 0) ∨
        (w i j = 0 ∧ w j i = 0 ∧ w j k = 0 ∧ w k i = 0 ∧ w k j = 0) ∨
        (w i j = 0 ∧ w i k = 0 ∧ w j k = 0 ∧ w k i = 0 ∧ w k j = 0) ∨
        (w i j = 0 ∧ w i k = 0 ∧ w j i = 0 ∧ w k i = 0 ∧ w k j = 0) ∨
        (w i j = 0 ∧ w i k = 0 ∧ w j i = 0 ∧ w j k = 0 ∧ w k j = 0) ∨
        (w i j = 0 ∧ w i k = 0 ∧ w j i = 0 ∧ w j k = 0 ∧ w k i = 0) := by omega
    rcases few with h | h | h | h | h | h <;>
      obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := h <;>
      simp [Matrix.det_fin_three, Matrix.submatrix, A, hd, h₁, h₂, h₃, h₄, h₅]
  by_cases r2 : A.rank < 2
  · have pos (i j : Fin 4) : 1 ≤ w i j := by
      by_contra! h
      have := pair i j (by omega)
      omega
    have total : (∑ i : Fin 4, ∑ j : Fin 4, 1) ≤ ∑ i, ∑ j, w i j :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pos i j
    simp at total
    omega
  · by_cases r3 : A.rank < 3
    · have two (i j k : Fin 4) : 2 ≤ w i j + w i k + w j i + w j k + w k i + w k j := by
        by_contra! h
        have := triple i j k h
        omega
      have t₀ := two 1 2 3
      have t₁ := two 0 2 3
      have t₂ := two 0 1 3
      have t₃ := two 0 1 2
      simp [Fin.sum_univ_four, hd]
      omega
    · simp [Fin.sum_univ_four, hd]
      omega

private def parity (x : Fin 4 → Bool) := xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)
private def oddX (a : Fin 8) (i : Fin 4) : Bool := (![1, 2, 4, 7, 8, 11, 13, 14] a : ℕ).testBit i
private def evenX (a : Fin 8) (i : Fin 4) : Bool := (![0, 3, 5, 6, 9, 10, 12, 15] a : ℕ).testBit i

-- Each row lists the four odd inputs of one literal. Its matched columns
-- are their even neighbours obtained by flipping that literal's bit.
private def rowId (i : Fin 4) (b : Bool) : Fin 4 → Fin 8 :=
  if b then ![![0, 3, 5, 6], ![1, 3, 5, 7], ![2, 3, 6, 7], ![4, 5, 6, 7]] i else ![![1, 2, 4, 7], ![0, 2, 4, 6], ![0, 1, 4, 5], ![0, 1, 2, 3]] i
private def colId (i : Fin 4) (b : Bool) : Fin 4 → Fin 8 :=
  if b then ![![0, 3, 5, 6], ![0, 2, 4, 6], ![0, 1, 4, 5], ![0, 1, 2, 3]] i else ![![1, 2, 4, 7], ![1, 3, 5, 7], ![2, 3, 6, 7], ![4, 5, 6, 7]] i

private theorem oddValue : ∀ a, parity (oddX a) = true := by decide
private theorem evenValue : ∀ a, parity (evenX a) = false := by decide
private theorem bitValue : ∀ i b r, oddX (rowId i b r) i = b := by decide
private theorem flipOnly : ∀ i b r d,
    oddX (rowId i b r) d ≠ evenX (colId i b r) d → d = i := by decide
private theorem rowInj : ∀ i b, Function.Injective (rowId i b) := by decide
private theorem colInj : ∀ i b, Function.Injective (colId i b) := by decide

end ParityFourBound

open PEqualNP.MetaComplexity ParityFourBound

theorem PEqualNP.Outside.L_meta_232 : ¬ PEqualNP.MetaComplexity.HasTypedRank 4 (fun x : Fin 4 → Bool => xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)) 15 := by
  classical
  change ¬ HasTypedRank 4 parity 15
  rintro ⟨τ, ht, budget⟩
  let cost (l : Fin 4 × Bool) (z : Fin 8 × Fin 8) : ℕ :=
    if τ (oddX z.1) (evenX z.2) = l.1.val ∧ oddX z.1 l.1 = l.2 then 1 else 0
  let mat (l : Fin 4 × Bool) := typedMatrix 4 parity τ l.1 l.2
  have bound (l : Fin 4 × Bool) : 16 ≤ 4 * (mat l).rank + ∑ z, cost l z := by
    let r := rowId l.1 l.2
    let c := colId l.1 l.2
    let w (a b : Fin 4) := cost l (r a, c b)
    have diag (a : Fin 4) : w a a = 1 := by
      obtain ⟨d, eq, diff⟩ := ht (oddX (r a)) (evenX (c a)) (oddValue _) (evenValue _)
      have same := flipOnly l.1 l.2 a d diff
      subst d
      simp [w, cost, eq, r, bitValue]
    have rankBound := (mat l).rank_submatrix_le (fun a => oddX (r a)) (fun b => evenX (c b))
    have sub : (mat l).submatrix (fun a => oddX (r a)) (fun b => evenX (c b)) =
        (fun a b => (w a b : ℚ) : Matrix (Fin 4) (Fin 4) ℚ) := by
      ext a b
      simp [mat, typedMatrix, Matrix.submatrix, oddValue, evenValue, w, cost]
    rw [sub] at rankBound
    have embed : Function.Injective (fun z : Fin 4 × Fin 4 => (r z.1, c z.2)) :=
      (rowInj l.1 l.2).prodMap (colInj l.1 l.2)
    have countBound : (∑ z : Fin 4 × Fin 4, w z.1 z.2) ≤ ∑ z, cost l z :=
      Finset.sum_le_sum_of_injOn _ embed.injOn (Finset.subset_univ _)
        (fun _ _ => le_rfl) (fun _ _ _ => Nat.zero_le _)
    rw [Fintype.sum_prod_type] at countBound
    change (∑ i, ∑ j, w i j) ≤ ∑ z, cost l z at countBound
    have h := weightRank w diag
    dsimp only at h
    omega
  -- Every odd/even input pair contributes to exactly one of the eight literals.
  have one (z : Fin 8 × Fin 8) : ∑ l, cost l z = 1 := by
    obtain ⟨d, eq, _⟩ := ht (oddX z.1) (evenX z.2) (oddValue _) (evenValue _)
    have entry (l : Fin 4 × Bool) :
        cost l z = if l = (d, oddX z.1 d) then 1 else 0 := by
      rcases l with ⟨j, b⟩
      by_cases same : d = j
      · subst j
        simp [cost, eq, eq_comm]
      · have ne : d.val ≠ j.val := fun h => same (Fin.ext h)
        simp [cost, eq, ne, Ne.symm same]
    simp [entry]
  have total := Finset.sum_le_sum (s := Finset.univ) (fun l _ => bound l)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at total
  have allCosts : (∑ l, ∑ z, cost l z) = 64 := by
    rw [Finset.sum_comm]
    simp [one]
  rw [allCosts] at total
  have ranks : (∑ l, (mat l).rank) ≤ 15 := by
    simpa [Fintype.sum_prod_type, mat] using budget
  norm_num at total
  omega
