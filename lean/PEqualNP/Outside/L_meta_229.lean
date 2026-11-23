import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_229
open PEqualNP.MetaComplexity

def orFun (n : ℕ) (x : Fin n → Bool) : Bool := decide (∃ i : Fin n, x i = true)

def zeroInput (n : ℕ) : Fin n → Bool := fun _ => false

def unitInput {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

theorem false_eq_zero {n : ℕ} (y : Fin n → Bool) (hy : orFun n y = false) :
    y = zeroInput n := by
  funext i
  cases hi : y i with
  | false => rfl
  | true =>
    have ht : orFun n y = true := by
      unfold orFun
      exact decide_eq_true ⟨i, hi⟩
    rw [hy] at ht
    exact False.elim (Bool.false_ne_true ht)

theorem rank_le_one {n : ℕ} (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (i : Fin n) (b : Bool) : (typedMatrix n (orFun n) τ i b).rank ≤ 1 := by
  classical
  let M := typedMatrix n (orFun n) τ i b
  have heq : M = Matrix.vecMulVec (fun x => M x (zeroInput n))
      (fun y => if y = zeroInput n then (1 : ℚ) else 0) := by
    ext x y
    by_cases hy : y = zeroInput n
    · subst y
      simp [Matrix.vecMulVec]
    · have hf : orFun n y ≠ false := fun h => hy (false_eq_zero y h)
      simp [M, typedMatrix, Matrix.vecMulVec, hy, hf]
  change M.rank ≤ 1
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

theorem false_matrix {n : ℕ} (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (hτ : IsTyping n (orFun n) τ) (i : Fin n) : typedMatrix n (orFun n) τ i false = 0 := by
  classical
  ext x y
  simp only [typedMatrix, Matrix.zero_apply]
  split_ifs with h
  · obtain ⟨hfx, hfy, htype, hxi⟩ := h
    obtain ⟨j, hj, hdiff⟩ := hτ x y hfx hfy
    have hji : j = i := Fin.ext (hj.symm.trans htype)
    subst j
    have hy := false_eq_zero y hfy
    have hsame : x i = y i := by rw [hxi, hy]; rfl
    exact False.elim (hdiff hsame)
  · rfl

theorem true_entry {n : ℕ} (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (hτ : IsTyping n (orFun n) τ) (i : Fin n) :
    typedMatrix n (orFun n) τ i true (unitInput i) (zeroInput n) = 1 := by
  classical
  have hx : orFun n (unitInput i) = true := by simp [orFun, unitInput]
  have hy : orFun n (zeroInput n) = false := by simp [orFun, zeroInput]
  obtain ⟨j, hj, hdiff⟩ := hτ (unitInput i) (zeroInput n) hx hy
  have hji : j = i := by
    by_contra hn
    exact hdiff (by simp [unitInput, zeroInput, hn])
  subst j
  simp [typedMatrix, hx, hy, hj, unitInput]

theorem rank_true {n : ℕ} (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (hτ : IsTyping n (orFun n) τ) (i : Fin n) :
    (typedMatrix n (orFun n) τ i true).rank = 1 := by
  classical
  let M := typedMatrix n (orFun n) τ i true
  have heq : M.submatrix (fun _ : Unit => unitInput i) (fun _ : Unit => zeroInput n) =
      (1 : Matrix Unit Unit ℚ) := by
    ext a b
    cases a
    cases b
    simp [M, Matrix.submatrix_apply, true_entry τ hτ i]
  have h := Matrix.rank_submatrix_le M (fun _ : Unit => unitInput i)
    (fun _ : Unit => zeroInput n)
  rw [heq, Matrix.rank_one] at h
  exact le_antisymm (rank_le_one τ i true) (by simpa using h)

theorem rank_sum {n : ℕ} (τ : (Fin n → Bool) → (Fin n → Bool) → ℕ)
    (hτ : IsTyping n (orFun n) τ) :
    (∑ i : Fin n, ∑ b : Bool, (typedMatrix n (orFun n) τ i b).rank) = n := by
  simp [false_matrix τ hτ, rank_true τ hτ]

noncomputable def typing (n : ℕ) : (Fin n → Bool) → (Fin n → Bool) → ℕ :=
  fun x _ => if h : ∃ i : Fin n, x i = true then (Classical.choose h).val else 0

theorem typing_valid (n : ℕ) : IsTyping n (orFun n) (typing n) := by
  classical
  intro x y hx hy
  have hex : ∃ i : Fin n, x i = true := of_decide_eq_true hx
  refine ⟨Classical.choose hex, ?_, ?_⟩
  · simp [typing, hex]
  · have hxi := Classical.choose_spec hex
    have hyz := false_eq_zero y hy
    rw [hxi, hyz]
    simp [zeroInput]

end PEqualNP.Outside.L_meta_229

theorem PEqualNP.Outside.L_meta_229 :
    ∀ n : ℕ, 1 ≤ n → PEqualNP.MetaComplexity.HasTypedRank n
      (fun x => decide (∃ i : Fin n, x i = true)) n ∧
      ¬ PEqualNP.MetaComplexity.HasTypedRank n
        (fun x => decide (∃ i : Fin n, x i = true)) (n - 1) := by
  intro n hn
  constructor
  · refine ⟨PEqualNP.Outside.L_meta_229.typing n,
      PEqualNP.Outside.L_meta_229.typing_valid n, ?_⟩
    change (∑ i : Fin n, ∑ b : Bool,
      (PEqualNP.MetaComplexity.typedMatrix n (PEqualNP.Outside.L_meta_229.orFun n)
        (PEqualNP.Outside.L_meta_229.typing n) i b).rank) ≤ n
    rw [PEqualNP.Outside.L_meta_229.rank_sum _ (PEqualNP.Outside.L_meta_229.typing_valid n)]
  · rintro ⟨τ, hτ, hs⟩
    have heq := PEqualNP.Outside.L_meta_229.rank_sum τ hτ
    change (∑ i : Fin n, ∑ b : Bool,
      (PEqualNP.MetaComplexity.typedMatrix n (PEqualNP.Outside.L_meta_229.orFun n) τ i b).rank) ≤ n - 1 at hs
    rw [heq] at hs
    omega
