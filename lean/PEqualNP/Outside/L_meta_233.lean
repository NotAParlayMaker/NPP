import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_233

private abbrev Input := Fin 3 → Bool

private def accepts (x : Input) : Bool :=
  decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)

private def position (x y : Input) : ℕ :=
  if y 0 && y 1 then
    if x 0 then 1 else 0
  else if !x 2 then 2
  else if y 0 then 0 else 1

private def bit (b : Bool) : ℚ := if b then 1 else 0

private def rowColProduct {k : ℕ} (rows cols : Fin k → Input → Bool) :
    Matrix Input Input ℚ :=
  (Matrix.of fun x i => bit (rows i x)) * (Matrix.of fun i y => bit (cols i y))

private lemma rank_product {k : ℕ} (rows cols : Fin k → Input → Bool) :
    (rowColProduct rows cols).rank ≤ k := by
  unfold rowColProduct
  refine (Matrix.rank_mul_le_left _ _).trans (le_trans (Matrix.rank_le_card_width _) ?_)
  simp

private lemma valid : IsTyping 3 accepts position := by
  change ∀ x y : Input, accepts x = true → accepts y = false →
    ∃ i : Fin 3, position x y = (i : ℕ) ∧ x i ≠ y i
  decide

private lemma rank_zero_true (i : Fin 3) :
    (typedMatrix 3 accepts position i true).rank = 0 := by
  have entries : ∀ (j : Fin 3) (x y : Input),
      typedMatrix 3 accepts position j true x y = 0 := by
    unfold typedMatrix
    decide
  have h : typedMatrix 3 accepts position i true = 0 := by
    ext x y
    exact entries i x y
  rw [h, Matrix.rank_zero]

private lemma rank_first : (typedMatrix 3 accepts position 0 false).rank ≤ 2 := by
  let rows : Fin 2 → Input → Bool :=
    ![fun x => accepts x && !x 0, fun x => accepts x && x 2]
  let cols : Fin 2 → Input → Bool :=
    ![fun y => !accepts y && (y 0 && y 1), fun y => !accepts y && (y 0 && !y 1)]
  have entries : ∀ x y : Input,
      typedMatrix 3 accepts position 0 false x y = rowColProduct rows cols x y := by
    simp only [typedMatrix, rowColProduct, Matrix.mul_apply, Matrix.of_apply]
    decide +kernel
  have h : typedMatrix 3 accepts position 0 false = rowColProduct rows cols := Matrix.ext entries
  rw [h]
  exact rank_product rows cols

private lemma rank_second : (typedMatrix 3 accepts position 1 false).rank ≤ 2 := by
  let rows : Fin 2 → Input → Bool :=
    ![fun x => accepts x && x 0, fun x => accepts x && x 2]
  let cols : Fin 2 → Input → Bool :=
    ![fun y => !accepts y && (y 0 && y 1), fun y => !accepts y && !y 0]
  have entries : ∀ x y : Input,
      typedMatrix 3 accepts position 1 false x y = rowColProduct rows cols x y := by
    simp only [typedMatrix, rowColProduct, Matrix.mul_apply, Matrix.of_apply]
    decide +kernel
  have h : typedMatrix 3 accepts position 1 false = rowColProduct rows cols := Matrix.ext entries
  rw [h]
  exact rank_product rows cols

private lemma rank_third : (typedMatrix 3 accepts position 2 false).rank ≤ 1 := by
  let rows : Fin 1 → Input → Bool := fun _ x => accepts x && !x 2
  let cols : Fin 1 → Input → Bool := fun _ y => !accepts y && !(y 0 && y 1)
  have entries : ∀ x y : Input,
      typedMatrix 3 accepts position 2 false x y = rowColProduct rows cols x y := by
    simp only [typedMatrix, rowColProduct, Matrix.mul_apply, Matrix.of_apply]
    decide +kernel
  have h : typedMatrix 3 accepts position 2 false = rowColProduct rows cols := Matrix.ext entries
  rw [h]
  exact rank_product rows cols

end PEqualNP.Outside.L_meta_233

theorem PEqualNP.Outside.L_meta_233 :
    PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)) 5 := by
  open PEqualNP.Outside.L_meta_233 in
  change HasTypedRank 3 accepts 5
  refine ⟨position, valid, ?_⟩
  simp only [Fin.sum_univ_three, Fintype.sum_bool, rank_zero_true, Nat.zero_add]
  have h₀ := rank_first
  have h₁ := rank_second
  have h₂ := rank_third
  omega
