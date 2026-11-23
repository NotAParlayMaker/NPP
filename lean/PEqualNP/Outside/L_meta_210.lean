import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_210_aux

open PEqualNP.MetaComplexity

def parity : (Fin 2 → Bool) → Bool := fun x => xor (x 0) (x 1)

def typing (x y : Fin 2 → Bool) : ℕ := if x 0 ≠ y 0 then 0 else 1

def row (i : Fin 2) (b : Bool) : Fin 2 → Bool := fun j => if j = i then b else !b

lemma row_unique : ∀ (i : Fin 2) (b : Bool) (x : Fin 2 → Bool),
    parity x = true → x i = b → x = row i b := by
  decide +kernel

lemma typing_valid : IsTyping 2 parity typing := by
  unfold IsTyping
  decide +kernel

lemma matrix_outer (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ) (i : Fin 2) (b : Bool) :
    typedMatrix 2 parity τ i b =
      Matrix.vecMulVec (fun x => if x = row i b then (1 : ℚ) else 0)
        (typedMatrix 2 parity τ i b (row i b)) := by
  ext x y
  by_cases hx : x = row i b
  · subst x
    simp [Matrix.vecMulVec]
  · have hz : typedMatrix 2 parity τ i b x y = 0 := by
      unfold typedMatrix
      split_ifs with h
      · exact (hx (row_unique i b x h.1 h.2.2.2)).elim
      · rfl
    simp [Matrix.vecMulVec, hx, hz]

lemma rank_le_one (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ) (i : Fin 2) (b : Bool) :
    (typedMatrix 2 parity τ i b).rank ≤ 1 := by
  rw [matrix_outer]
  exact Matrix.rank_vecMulVec_le _ _

lemma upper : HasTypedRank 2 parity 4 := by
  refine ⟨typing, typing_valid, ?_⟩
  calc
    (∑ i : Fin 2, ∑ b : Bool, (typedMatrix 2 parity typing i b).rank) ≤
        ∑ i : Fin 2, ∑ b : Bool, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro b hb
      exact rank_le_one typing i b
    _ = 4 := by simp

def lowerPos (i : Fin 2) (b : Bool) : Fin 2 → Bool :=
  fun j => if j = i then b else !b

def lowerNeg (b : Bool) : Fin 2 → Bool := fun _ => !b

theorem lowerPos_parity (i : Fin 2) (b : Bool) :
    xor (lowerPos i b 0) (lowerPos i b 1) = true := by
  fin_cases i <;> cases b <;> decide

theorem lowerNeg_parity (b : Bool) :
    xor (lowerNeg b 0) (lowerNeg b 1) = false := by
  cases b <;> decide

theorem lowerTyping
    (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ)
    (hτ : IsTyping 2 (fun x => xor (x 0) (x 1)) τ)
    (i : Fin 2) (b : Bool) : τ (lowerPos i b) (lowerNeg b) = i.val := by
  obtain ⟨j, hj, hd⟩ := hτ (lowerPos i b) (lowerNeg b)
    (lowerPos_parity i b) (lowerNeg_parity b)
  have hji : j = i := by
    by_contra hn
    exact hd (by simp [lowerPos, lowerNeg, hn])
  simpa [hji] using hj

theorem lowerEntry
    (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ)
    (hτ : IsTyping 2 (fun x => xor (x 0) (x 1)) τ)
    (i : Fin 2) (b : Bool) :
    typedMatrix 2 (fun x => xor (x 0) (x 1)) τ i b
      (lowerPos i b) (lowerNeg b) = 1 := by
  unfold typedMatrix
  exact if_pos ⟨lowerPos_parity i b, lowerNeg_parity b,
    lowerTyping τ hτ i b, by simp [lowerPos]⟩

theorem rank_at_least_one_of_entry {m n : Type} [Fintype n]
    (A : Matrix m n ℚ) (x : m) (y : n) (h : A x y = 1) :
    1 ≤ A.rank := by
  have hs : A.submatrix (fun _ : Fin 1 => x) (fun _ : Fin 1 => y)
      = (1 : Matrix (Fin 1) (Fin 1) ℚ) := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.submatrix] using h
  have hb := Matrix.rank_submatrix_le A (fun _ : Fin 1 => x) (fun _ : Fin 1 => y)
  simpa [hs] using hb

theorem lowerRank
    (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ)
    (hτ : IsTyping 2 (fun x => xor (x 0) (x 1)) τ)
    (i : Fin 2) (b : Bool) :
    1 ≤ (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ i b).rank := by
  exact rank_at_least_one_of_entry _ _ _ (lowerEntry τ hτ i b)

theorem lower_sum
    (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ)
    (hτ : IsTyping 2 (fun x => xor (x 0) (x 1)) τ) :
    4 ≤ ∑ i : Fin 2, ∑ b : Bool,
      (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ i b).rank := by
  calc
    4 = ∑ _i : Fin 2, ∑ _b : Bool, (1 : ℕ) := by decide
    _ ≤ ∑ i : Fin 2, ∑ b : Bool,
        (typedMatrix 2 (fun x => xor (x 0) (x 1)) τ i b).rank := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro b _
      exact lowerRank τ hτ i b

theorem no_rank_three :
    ¬ HasTypedRank 2 (fun x => xor (x 0) (x 1)) 3 := by
  rintro ⟨τ, hτ, hs⟩
  have hl := lower_sum τ hτ
  omega

end PEqualNP.Outside.L_meta_210_aux

theorem PEqualNP.Outside.L_meta_210 :
    PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 4 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 3 := by
  exact ⟨PEqualNP.Outside.L_meta_210_aux.upper, PEqualNP.Outside.L_meta_210_aux.no_rank_three⟩
