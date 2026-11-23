import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_230

open PEqualNP.MetaComplexity

def maj : (Fin 3 → Bool) → Bool :=
  fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

lemma one_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (M : Matrix α β ℚ)
    (a : α) (c : β) (h : M a c = 1) : 1 ≤ M.rank := by
  have h1 := Matrix.rank_submatrix_le M ![a] ![c]
  have hdet : (M.submatrix ![a] ![c]).det ≠ 0 := by
    rw [Matrix.det_fin_one]; simp [h]
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h1
  exact h1

lemma two_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (M : Matrix α β ℚ)
    (a b : α) (c d : β) (h1 : M a c = 1) (h2 : M b d = 1) (h3 : M a d = 0 ∨ M b c = 0) :
    2 ≤ M.rank := by
  have h := Matrix.rank_submatrix_le M ![a, b] ![c, d]
  have hdet : (M.submatrix ![a, b] ![c, d]).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    rcases h3 with h3 | h3 <;> simp [h1, h2, h3]
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h
  exact h

lemma entry (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (i : Fin 3) (x y : Fin 3 → Bool)
    (hx : maj x = true) (hy : maj y = false) (hxi : x i = true) :
    typedMatrix 3 maj τ i true x y = if τ x y = (i : ℕ) then 1 else 0 := by
  simp [typedMatrix, hx, hy, hxi]

def p01 : Fin 3 → Bool := ![true, true, false]
def p02 : Fin 3 → Bool := ![true, false, true]
def p12 : Fin 3 → Bool := ![false, true, true]
def s0 : Fin 3 → Bool := ![true, false, false]
def s1 : Fin 3 → Bool := ![false, true, false]
def s2 : Fin 3 → Bool := ![false, false, true]

lemma lower (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (hτ : IsTyping 3 maj τ) :
    5 ≤ ∑ i : Fin 3, ∑ b : Bool, (typedMatrix 3 maj τ i b).rank := by
  have f01 : τ p01 s1 = 0 := by
    obtain ⟨i, hi, hne⟩ := hτ p01 s1 (by decide) (by decide)
    fin_cases i <;> simp_all [p01, s1]
  have f02 : τ p02 s2 = 0 := by
    obtain ⟨i, hi, hne⟩ := hτ p02 s2 (by decide) (by decide)
    fin_cases i <;> simp_all [p02, s2]
  have f10 : τ p01 s0 = 1 := by
    obtain ⟨i, hi, hne⟩ := hτ p01 s0 (by decide) (by decide)
    fin_cases i <;> simp_all [p01, s0]
  have f12 : τ p12 s2 = 1 := by
    obtain ⟨i, hi, hne⟩ := hτ p12 s2 (by decide) (by decide)
    fin_cases i <;> simp_all [p12, s2]
  have f20 : τ p02 s0 = 2 := by
    obtain ⟨i, hi, hne⟩ := hτ p02 s0 (by decide) (by decide)
    fin_cases i <;> simp_all [p02, s0]
  have f21 : τ p12 s1 = 2 := by
    obtain ⟨i, hi, hne⟩ := hτ p12 s1 (by decide) (by decide)
    fin_cases i <;> simp_all [p12, s1]
  have e0a := entry τ 0 p01 s1 (by decide) (by decide) (by decide)
  have e0b := entry τ 0 p02 s2 (by decide) (by decide) (by decide)
  have e0c := entry τ 0 p01 s2 (by decide) (by decide) (by decide)
  have e0d := entry τ 0 p02 s1 (by decide) (by decide) (by decide)
  have e1a := entry τ 1 p01 s0 (by decide) (by decide) (by decide)
  have e1b := entry τ 1 p12 s2 (by decide) (by decide) (by decide)
  have e1c := entry τ 1 p01 s2 (by decide) (by decide) (by decide)
  have e1d := entry τ 1 p12 s0 (by decide) (by decide) (by decide)
  have e2a : typedMatrix 3 maj τ 2 true p02 s0 = if τ p02 s0 = 2 then 1 else 0 :=
    entry τ 2 p02 s0 (by decide) (by decide) (by decide)
  have e2b : typedMatrix 3 maj τ 2 true p12 s1 = if τ p12 s1 = 2 then 1 else 0 :=
    entry τ 2 p12 s1 (by decide) (by decide) (by decide)
  have e2c : typedMatrix 3 maj τ 2 true p02 s1 = if τ p02 s1 = 2 then 1 else 0 :=
    entry τ 2 p02 s1 (by decide) (by decide) (by decide)
  have e2d : typedMatrix 3 maj τ 2 true p12 s0 = if τ p12 s0 = 2 then 1 else 0 :=
    entry τ 2 p12 s0 (by decide) (by decide) (by decide)
  simp only [Fin.val_zero, Fin.val_one] at e0a e0b e0c e0d e1a e1b e1c e1d
  have r0 : 1 ≤ (typedMatrix 3 maj τ 0 true).rank :=
    one_le _ p01 s1 (by rw [e0a, f01]; simp)
  have r1 : 1 ≤ (typedMatrix 3 maj τ 1 true).rank :=
    one_le _ p01 s0 (by rw [e1a, f10]; simp)
  have r2 : 1 ≤ (typedMatrix 3 maj τ 2 true).rank :=
    one_le _ p02 s0 (by rw [e2a, f20]; simp)
  have q0 : (τ p01 s2 = 0 ∧ τ p02 s1 = 0) ∨ 2 ≤ (typedMatrix 3 maj τ 0 true).rank := by
    by_cases hc : τ p01 s2 = 0
    · by_cases hd : τ p02 s1 = 0
      · exact Or.inl ⟨hc, hd⟩
      · right
        exact two_le _ p01 p02 s1 s2 (by rw [e0a, f01]; simp) (by rw [e0b, f02]; simp)
          (Or.inr (by rw [e0d]; simp [hd]))
    · right
      exact two_le _ p01 p02 s1 s2 (by rw [e0a, f01]; simp) (by rw [e0b, f02]; simp)
        (Or.inl (by rw [e0c]; simp [hc]))
  have q1 : (τ p01 s2 = 1 ∧ τ p12 s0 = 1) ∨ 2 ≤ (typedMatrix 3 maj τ 1 true).rank := by
    by_cases hc : τ p01 s2 = 1
    · by_cases hd : τ p12 s0 = 1
      · exact Or.inl ⟨hc, hd⟩
      · right
        exact two_le _ p01 p12 s0 s2 (by rw [e1a, f10]; simp) (by rw [e1b, f12]; simp)
          (Or.inr (by rw [e1d]; simp [hd]))
    · right
      exact two_le _ p01 p12 s0 s2 (by rw [e1a, f10]; simp) (by rw [e1b, f12]; simp)
        (Or.inl (by rw [e1c]; simp [hc]))
  have q2 : (τ p02 s1 = 2 ∧ τ p12 s0 = 2) ∨ 2 ≤ (typedMatrix 3 maj τ 2 true).rank := by
    by_cases hc : τ p02 s1 = 2
    · by_cases hd : τ p12 s0 = 2
      · exact Or.inl ⟨hc, hd⟩
      · right
        exact two_le _ p02 p12 s0 s1 (by rw [e2a, f20]; simp) (by rw [e2b, f21]; simp)
          (Or.inr (by rw [e2d]; simp [hd]))
    · right
      exact two_le _ p02 p12 s0 s1 (by rw [e2a, f20]; simp) (by rw [e2b, f21]; simp)
        (Or.inl (by rw [e2c]; simp [hc]))
  simp only [Fin.sum_univ_three, Fintype.sum_bool]
  omega

def tau0 (x y : Fin 3 → Bool) : ℕ :=
  if x 0 = true ∧ y 0 = false then 0 else if x 1 = true ∧ y 1 = false then 1 else 2

lemma typing_aux : ∀ a b c d e g : Bool,
    maj ![a, b, c] = true → maj ![d, e, g] = false →
      ∃ i : Fin 3, tau0 ![a, b, c] ![d, e, g] = (i : ℕ) ∧ (![a, b, c] : Fin 3 → Bool) i ≠ ![d, e, g] i := by
  decide

lemma eta3 (x : Fin 3 → Bool) : x = ![x 0, x 1, x 2] := by
  ext i; fin_cases i <;> rfl

lemma typing : IsTyping 3 maj tau0 := by
  intro x y hx hy
  have h := typing_aux (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
  rw [← eta3 x, ← eta3 y] at h
  exact h hx hy

lemma all3 {P : (Fin 3 → Bool) → Prop} (h : ∀ a b c : Bool, P ![a, b, c])
    (x : Fin 3 → Bool) : P x := by
  rw [eta3 x]; exact h _ _ _

lemma zero_mat (i : Fin 3) : typedMatrix 3 maj tau0 i false = 0 := by
  ext x y
  simp only [typedMatrix, Matrix.zero_apply, maj, tau0]
  revert y; revert x; apply all3; intro a b c; beta_reduce; apply all3; intro d e g
  fin_cases i <;>
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases g <;> simp

lemma mat0 : typedMatrix 3 maj tau0 0 true =
    Matrix.vecMulVec (fun x => if maj x = true ∧ x 0 = true then (1 : ℚ) else 0)
      (fun y => if maj y = false ∧ y 0 = false then (1 : ℚ) else 0) := by
  ext x y
  simp only [typedMatrix, Matrix.vecMulVec_apply, maj, tau0]
  revert y; revert x; apply all3; intro a b c; beta_reduce; apply all3; intro d e g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases g <;> simp

def A1 : Matrix (Fin 3 → Bool) (Fin 2) ℚ :=
  fun x k => if k = 0 then (if x 0 = true ∧ x 1 = true then 1 else 0)
    else (if x 0 = false ∧ x 1 = true ∧ x 2 = true then 1 else 0)

def B1 : Matrix (Fin 2) (Fin 3 → Bool) ℚ :=
  fun k y => if k = 0 then (if y 0 = true ∧ y 1 = false ∧ y 2 = false then 1 else 0)
    else (if y 1 = false ∧ (y 0 = false ∨ y 2 = false) then 1 else 0)

lemma mat1 : typedMatrix 3 maj tau0 1 true = A1 * B1 := by
  ext x y
  simp only [typedMatrix, Matrix.mul_apply, Fin.sum_univ_two, A1, B1, maj, tau0]
  revert y; revert x; apply all3; intro a b c; beta_reduce; apply all3; intro d e g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases g <;> simp

def A2 : Matrix (Fin 3 → Bool) (Fin 2) ℚ :=
  fun x k => if k = 0 then (if x 0 = true ∧ x 1 = false ∧ x 2 = true then 1 else 0)
    else (if x 0 = false ∧ x 1 = true ∧ x 2 = true then 1 else 0)

def B2 : Matrix (Fin 2) (Fin 3 → Bool) ℚ :=
  fun k y => if k = 0 then (if y 0 = true ∧ y 1 = false ∧ y 2 = false then 1 else 0)
    else (if y 0 = false ∧ y 1 = true ∧ y 2 = false then 1 else 0)

lemma mat2 : typedMatrix 3 maj tau0 2 true = A2 * B2 := by
  ext x y
  simp only [typedMatrix, Matrix.mul_apply, Fin.sum_univ_two, A2, B2, maj, tau0]
  revert y; revert x; apply all3; intro a b c; beta_reduce; apply all3; intro d e g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases g <;> simp

lemma upper : HasTypedRank 3 maj 5 := by
  refine ⟨tau0, typing, ?_⟩
  simp only [Fin.sum_univ_three, Fintype.sum_bool, zero_mat, Matrix.rank_zero]
  have r0 : (typedMatrix 3 maj tau0 0 true).rank ≤ 1 := by
    rw [mat0]; exact Matrix.rank_vecMulVec_le _ _
  have r1 : (typedMatrix 3 maj tau0 1 true).rank ≤ 2 := by
    rw [mat1]
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width A1)
  have r2 : (typedMatrix 3 maj tau0 2 true).rank ≤ 2 := by
    rw [mat2]
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width A2)
  omega

end PEqualNP.Outside.L_meta_230

theorem PEqualNP.Outside.L_meta_230 : PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 5 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  refine ⟨PEqualNP.Outside.L_meta_230.upper, ?_⟩
  rintro ⟨τ, hτ, hs⟩
  have := PEqualNP.Outside.L_meta_230.lower τ hτ
  exact absurd (this.trans hs) (by norm_num)
