import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_234

def F : (Fin 3 → Bool) → Bool := fun x => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)

def e0 : Fin 3 → Bool := ![true, false, false]
def e1 : Fin 3 → Bool := ![false, true, false]
def e2 : Fin 3 → Bool := ![false, false, true]
def y01 : Fin 3 → Bool := ![true, true, false]
def y02 : Fin 3 → Bool := ![true, false, true]
def y12 : Fin 3 → Bool := ![false, true, true]

lemma rank_ge {ι κ : Type} [Fintype κ] (M : Matrix ι κ ℚ) {k : ℕ} (r : Fin k → ι)
    (c : Fin k → κ) (h : (M.submatrix r c).det ≠ 0) : k ≤ M.rank := by
  have h1 := Matrix.rank_submatrix_le M r c
  have h2 := Matrix.rank_of_isUnit (M.submatrix r c)
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
  rw [Fintype.card_fin] at h2
  omega

lemma entry (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (i : Fin 3) (x y : Fin 3 → Bool)
    (hx : F x = true) (hy : F y = false) (hxi : x i = false) :
    typedMatrix 3 F τ i false x y = if τ x y = (i : ℕ) then 1 else 0 := by
  unfold typedMatrix
  simp [hx, hy, hxi]

lemma forced (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (hτ : IsTyping 3 F τ)
    (x y : Fin 3 → Bool) (hx : F x = true) (hy : F y = false) (i : Fin 3)
    (h : ∀ j : Fin 3, j ≠ i → x j = y j) : τ x y = (i : ℕ) := by
  obtain ⟨j, hj, hne⟩ := hτ x y hx hy
  by_cases hji : j = i
  · rw [hj, hji]
  · exact absurd (h j hji) hne

lemma one_le (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (b : Fin 3) (x y : Fin 3 → Bool)
    (hx : F x = true) (hy : F y = false) (hxb : x b = false) (h : τ x y = (b : ℕ)) :
    1 ≤ (typedMatrix 3 F τ b false).rank := by
  apply rank_ge _ ![x] ![y]
  rw [Matrix.det_fin_one]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero]
  rw [entry τ b x y hx hy hxb, if_pos h]
  norm_num

lemma key (τ : (Fin 3 → Bool) → (Fin 3 → Bool) → ℕ) (b : Fin 3) (xa xc ya yc : Fin 3 → Bool)
    (hxa : F xa = true) (hxc : F xc = true) (hya : F ya = false) (hyc : F yc = false)
    (hab : xa b = false) (hcb : xc b = false) (h1 : τ xa ya = (b : ℕ)) (h2 : τ xc yc = (b : ℕ)) :
    2 ≤ (typedMatrix 3 F τ b false).rank ∨ (τ xa yc = (b : ℕ) ∧ τ xc ya = (b : ℕ)) := by
  by_cases hc : τ xa yc = (b : ℕ) ∧ τ xc ya = (b : ℕ)
  · exact Or.inr hc
  · left
    apply rank_ge _ ![xa, xc] ![ya, yc]
    rw [Matrix.det_fin_two]
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [entry τ b xa ya hxa hya hab, entry τ b xc yc hxc hyc hcb, entry τ b xa yc hxa hyc hab,
      entry τ b xc ya hxc hya hcb, if_pos h1, if_pos h2]
    split_ifs with h3 h4 <;> simp_all

end PEqualNP.Outside.L_meta_234

theorem PEqualNP.Outside.L_meta_234 : ¬ PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)) 4 := by
  change ¬ HasTypedRank 3 PEqualNP.Outside.L_meta_234.F 4
  rintro ⟨τ, hτ, hsum⟩
  simp only [Fin.sum_univ_three, Fintype.sum_bool] at hsum
  have tE0 : PEqualNP.Outside.L_meta_234.F PEqualNP.Outside.L_meta_234.e0 = true := by decide
  have tE1 : PEqualNP.Outside.L_meta_234.F PEqualNP.Outside.L_meta_234.e1 = true := by decide
  have tE2 : PEqualNP.Outside.L_meta_234.F PEqualNP.Outside.L_meta_234.e2 = true := by decide
  have fY01 : PEqualNP.Outside.L_meta_234.F PEqualNP.Outside.L_meta_234.y01 = false := by decide
  have fY02 : PEqualNP.Outside.L_meta_234.F PEqualNP.Outside.L_meta_234.y02 = false := by decide
  have fY12 : PEqualNP.Outside.L_meta_234.F PEqualNP.Outside.L_meta_234.y12 = false := by decide
  have p1 := PEqualNP.Outside.L_meta_234.forced τ hτ _ _ tE1 fY01 0 (by decide)
  have p2 := PEqualNP.Outside.L_meta_234.forced τ hτ _ _ tE2 fY02 0 (by decide)
  have p3 := PEqualNP.Outside.L_meta_234.forced τ hτ _ _ tE0 fY01 1 (by decide)
  have p4 := PEqualNP.Outside.L_meta_234.forced τ hτ _ _ tE2 fY12 1 (by decide)
  have p5 := PEqualNP.Outside.L_meta_234.forced τ hτ _ _ tE0 fY02 2 (by decide)
  have p6 := PEqualNP.Outside.L_meta_234.forced τ hτ _ _ tE1 fY12 2 (by decide)
  have o0 := PEqualNP.Outside.L_meta_234.one_le τ 0 _ _ tE1 fY01 (by decide) p1
  have o1 := PEqualNP.Outside.L_meta_234.one_le τ 1 _ _ tE0 fY01 (by decide) p3
  have o2 := PEqualNP.Outside.L_meta_234.one_le τ 2 _ _ tE0 fY02 (by decide) p5
  have k0 := PEqualNP.Outside.L_meta_234.key τ 0 _ _ _ _ tE1 tE2 fY01 fY02
    (by decide) (by decide) p1 p2
  have k1 := PEqualNP.Outside.L_meta_234.key τ 1 _ _ _ _ tE0 tE2 fY01 fY12
    (by decide) (by decide) p3 p4
  have k2 := PEqualNP.Outside.L_meta_234.key τ 2 _ _ _ _ tE0 tE1 fY02 fY12
    (by decide) (by decide) p5 p6
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at k0 k1 k2
  rcases k0 with k0 | ⟨a0, b0⟩ <;> rcases k1 with k1 | ⟨a1, b1⟩ <;>
    rcases k2 with k2 | ⟨a2, b2⟩ <;> omega
