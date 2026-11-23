import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_210

open PEqualNP.MetaComplexity

def px : (Fin 2 → Bool) → Bool := fun x => xor (x 0) (x 1)

lemma one_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (M : Matrix α β ℚ)
    (a : α) (c : β) (h : M a c = 1) : 1 ≤ M.rank := by
  have h1 := Matrix.rank_submatrix_le M ![a] ![c]
  have hdet : (M.submatrix ![a] ![c]).det ≠ 0 := by
    rw [Matrix.det_fin_one]; simp [h]
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at h1
  exact h1

lemma eta2 (x : Fin 2 → Bool) : x = ![x 0, x 1] := by
  ext i; fin_cases i <;> rfl

lemma all2 {P : (Fin 2 → Bool) → Prop} (h : ∀ a b : Bool, P ![a, b])
    (x : Fin 2 → Bool) : P x := by
  rw [eta2 x]; exact h _ _

def tau0 (x y : Fin 2 → Bool) : ℕ := if x 0 = y 0 then 1 else 0

lemma typing_aux : ∀ a b c d : Bool, px ![a, b] = true → px ![c, d] = false →
    ∃ i : Fin 2, tau0 ![a, b] ![c, d] = (i : ℕ) ∧ (![a, b] : Fin 2 → Bool) i ≠ ![c, d] i := by
  decide

lemma typing : IsTyping 2 px tau0 := by
  intro x y hx hy
  have h := typing_aux (x 0) (x 1) (y 0) (y 1)
  rw [← eta2 x, ← eta2 y] at h
  exact h hx hy

lemma rank_le (i : Fin 2) (b : Bool) : (typedMatrix 2 px tau0 i b).rank ≤ 1 := by
  have e : typedMatrix 2 px tau0 i b = Matrix.vecMulVec
      (fun x => if px x = true ∧ x i = b ∧ x (1 - i) = !b then (1 : ℚ) else 0)
      (fun y => if px y = false ∧ y i = !b then (1 : ℚ) else 0) := by
    ext x y
    simp only [typedMatrix, Matrix.vecMulVec_apply, px, tau0]
    revert y; revert x; apply all2; intro a1 a2; beta_reduce; apply all2; intro c1 c2
    fin_cases i <;> cases b <;> cases a1 <;> cases a2 <;> cases c1 <;> cases c2 <;> simp
  rw [e]; exact Matrix.rank_vecMulVec_le _ _

lemma upper : HasTypedRank 2 px 4 := by
  refine ⟨tau0, typing, ?_⟩
  have h00 := rank_le 0 false
  have h01 := rank_le 0 true
  have h10 := rank_le 1 false
  have h11 := rank_le 1 true
  simp only [Fin.sum_univ_two, Fintype.sum_bool]
  omega

lemma forced (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ) (hτ : IsTyping 2 px τ)
    (x y : Fin 2 → Bool) (k : Fin 2) (hx : px x = true) (hy : px y = false)
    (hk : ∀ j : Fin 2, x j ≠ y j → j = k) : τ x y = (k : ℕ) := by
  obtain ⟨j, hj, hne⟩ := hτ x y hx hy
  rw [hj, hk j hne]

lemma lower (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ) (hτ : IsTyping 2 px τ) :
    4 ≤ ∑ i : Fin 2, ∑ b : Bool, (typedMatrix 2 px τ i b).rank := by
  have r0t : 1 ≤ (typedMatrix 2 px τ 0 true).rank := by
    apply one_le _ ![true, false] ![false, false]
    have := forced τ hτ ![true, false] ![false, false] 0 (by decide) (by decide)
      (by intro j hj; fin_cases j <;> simp_all)
    simp [typedMatrix, px, this]
  have r0f : 1 ≤ (typedMatrix 2 px τ 0 false).rank := by
    apply one_le _ ![false, true] ![true, true]
    have := forced τ hτ ![false, true] ![true, true] 0 (by decide) (by decide)
      (by intro j hj; fin_cases j <;> simp_all)
    simp [typedMatrix, px, this]
  have r1t : 1 ≤ (typedMatrix 2 px τ 1 true).rank := by
    apply one_le _ ![false, true] ![false, false]
    have := forced τ hτ ![false, true] ![false, false] 1 (by decide) (by decide)
      (by intro j hj; fin_cases j <;> simp_all)
    simp [typedMatrix, px, this]
  have r1f : 1 ≤ (typedMatrix 2 px τ 1 false).rank := by
    apply one_le _ ![true, false] ![true, true]
    have := forced τ hτ ![true, false] ![true, true] 1 (by decide) (by decide)
      (by intro j hj; fin_cases j <;> simp_all)
    simp [typedMatrix, px, this]
  simp only [Fin.sum_univ_two, Fintype.sum_bool]
  omega

end PEqualNP.Outside.L_meta_210

theorem PEqualNP.Outside.L_meta_210 : PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 4 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => xor (x 0) (x 1)) 3 := by
  refine ⟨PEqualNP.Outside.L_meta_210.upper, ?_⟩
  rintro ⟨τ, hτ, hs⟩
  have := PEqualNP.Outside.L_meta_210.lower τ hτ
  exact absurd (this.trans hs) (by norm_num)
