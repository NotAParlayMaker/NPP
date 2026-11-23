import Mathlib
import PEqualNP.Defs

namespace PQ201
abbrev Mat := Fin 4 × Fin 4 → ℂ
abbrev Vec := Fin 4 → ℂ
abbrev Lev (L : Submodule ℂ Mat) :=
  ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24
def RC (x : Mat) := ∀ i : Fin 4, (∑ j, x (i,j)) = 0
def B (x y : Mat) := ∑ i : Fin 4, ∑ j : Fin 4,
  (x (i,j) - ∑ k : Fin 4, x (k,j)) * y (i,j)
def d (j k : Fin 4) : ℂ := if k = j then 3 else -1
def atom (j : Fin 4) (v : Vec) : Mat := fun p => v p.1 * d j p.2
end PQ201

namespace Gap183
open Finset
theorem sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

/-- The permanent of a `4 x 4` matrix as a sum over permutations, written out. -/
theorem sum_perm_four (z : Fin 4 × Fin 4 → ℂ) :
    ∑ σ : Equiv.Perm (Fin 4), ∏ i, z (σ i, i) =
      z (0, 0) * z (1, 1) * z (2, 2) * z (3, 3) +
      z (0, 0) * z (1, 1) * z (3, 2) * z (2, 3) +
      z (0, 0) * z (2, 1) * z (1, 2) * z (3, 3) +
      z (0, 0) * z (2, 1) * z (3, 2) * z (1, 3) +
      z (0, 0) * z (3, 1) * z (1, 2) * z (2, 3) +
      z (0, 0) * z (3, 1) * z (2, 2) * z (1, 3) +
      z (1, 0) * z (0, 1) * z (2, 2) * z (3, 3) +
      z (1, 0) * z (0, 1) * z (3, 2) * z (2, 3) +
      z (1, 0) * z (2, 1) * z (0, 2) * z (3, 3) +
      z (1, 0) * z (2, 1) * z (3, 2) * z (0, 3) +
      z (1, 0) * z (3, 1) * z (0, 2) * z (2, 3) +
      z (1, 0) * z (3, 1) * z (2, 2) * z (0, 3) +
      z (2, 0) * z (0, 1) * z (1, 2) * z (3, 3) +
      z (2, 0) * z (0, 1) * z (3, 2) * z (1, 3) +
      z (2, 0) * z (1, 1) * z (0, 2) * z (3, 3) +
      z (2, 0) * z (1, 1) * z (3, 2) * z (0, 3) +
      z (2, 0) * z (3, 1) * z (0, 2) * z (1, 3) +
      z (2, 0) * z (3, 1) * z (1, 2) * z (0, 3) +
      z (3, 0) * z (0, 1) * z (1, 2) * z (2, 3) +
      z (3, 0) * z (0, 1) * z (2, 2) * z (1, 3) +
      z (3, 0) * z (1, 1) * z (0, 2) * z (2, 3) +
      z (3, 0) * z (1, 1) * z (2, 2) * z (0, 3) +
      z (3, 0) * z (2, 1) * z (0, 2) * z (1, 3) +
      z (3, 0) * z (2, 1) * z (1, 2) * z (0, 3)
 := by
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp (config := { decide := true }) [Equiv.swap_apply_def]
  ring

/-- The same for `MvPolynomial.eval` of `permPoly`. -/
theorem eval_perm_four (z : Fin 4 × Fin 4 → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ 4) =
      z (0, 0) * z (1, 1) * z (2, 2) * z (3, 3) +
      z (0, 0) * z (1, 1) * z (3, 2) * z (2, 3) +
      z (0, 0) * z (2, 1) * z (1, 2) * z (3, 3) +
      z (0, 0) * z (2, 1) * z (3, 2) * z (1, 3) +
      z (0, 0) * z (3, 1) * z (1, 2) * z (2, 3) +
      z (0, 0) * z (3, 1) * z (2, 2) * z (1, 3) +
      z (1, 0) * z (0, 1) * z (2, 2) * z (3, 3) +
      z (1, 0) * z (0, 1) * z (3, 2) * z (2, 3) +
      z (1, 0) * z (2, 1) * z (0, 2) * z (3, 3) +
      z (1, 0) * z (2, 1) * z (3, 2) * z (0, 3) +
      z (1, 0) * z (3, 1) * z (0, 2) * z (2, 3) +
      z (1, 0) * z (3, 1) * z (2, 2) * z (0, 3) +
      z (2, 0) * z (0, 1) * z (1, 2) * z (3, 3) +
      z (2, 0) * z (0, 1) * z (3, 2) * z (1, 3) +
      z (2, 0) * z (1, 1) * z (0, 2) * z (3, 3) +
      z (2, 0) * z (1, 1) * z (3, 2) * z (0, 3) +
      z (2, 0) * z (3, 1) * z (0, 2) * z (1, 3) +
      z (2, 0) * z (3, 1) * z (1, 2) * z (0, 3) +
      z (3, 0) * z (0, 1) * z (1, 2) * z (2, 3) +
      z (3, 0) * z (0, 1) * z (2, 2) * z (1, 3) +
      z (3, 0) * z (1, 1) * z (0, 2) * z (2, 3) +
      z (3, 0) * z (1, 1) * z (2, 2) * z (0, 3) +
      z (3, 0) * z (2, 1) * z (0, 2) * z (1, 3) +
      z (3, 0) * z (2, 1) * z (1, 2) * z (0, 3)
 := by
  rw [← sum_perm_four]
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

/-- Bridge: the four explicit sums of the gap statement vanish, so the permanent of `J + t` is 24.
(Pointwise identity `perm (J + t) = 24 + 6 s1 + 2 s2 + s3 + s4`.) -/
theorem level_of_sums (t : Fin 4 × Fin 4 → ℂ)
    (h : (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [eval_perm_four]
  simp only [Fin.sum_univ_four] at h1 h2 h3 h4
  simp (config := { decide := true }) only [ite_true, ite_false, add_zero, zero_add] at h2 h3 h4
  linear_combination 6 * h1 + 2 * h2 + h3 + h4

end Gap183

namespace PQ183Core

abbrev Mat := Fin 4 × Fin 4 → ℂ
abbrev Lev (L : Submodule ℂ Mat) :=
  ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24
def dot (F T : Mat) : ℂ := ∑ i : Fin 4, ∑ j : Fin 4, F (i,j) * T (i,j)
def total (F : Mat) : ℂ := ∑ i : Fin 4, ∑ j : Fin 4, F (i,j)

namespace LevelPolarProof
open Finset

private abbrev Perm := Equiv.Perm (Fin 4)

private theorem sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

-- List the columns of each permutation, before specifying the summand.
private theorem permTuples (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℂ) :
    (∑ σ : Perm, f (σ 0) (σ 1) (σ 2) (σ 3)) =
      f 0 1 2 3 + f 0 1 3 2 + f 0 2 1 3 + f 0 2 3 1 + f 0 3 1 2 + f 0 3 2 1 +
      f 1 0 2 3 + f 1 0 3 2 + f 1 2 0 3 + f 1 2 3 0 + f 1 3 0 2 + f 1 3 2 0 +
      f 2 0 1 3 + f 2 0 3 1 + f 2 1 0 3 + f 2 1 3 0 + f 2 3 0 1 + f 2 3 1 0 +
      f 3 0 1 2 + f 3 0 2 1 + f 3 1 0 2 + f 3 1 2 0 + f 3 2 0 1 + f 3 2 1 0 := by
  change (∑ σ : Perm, f (σ 0) (σ (0 : Fin 3).succ)
    (σ (0 : Fin 2).succ.succ) (σ (0 : Fin 1).succ.succ.succ)) = _
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fintype.sum_unique,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp (config := { decide := true }) [Equiv.swap_apply_def]
  ring

private def e₁ (a b c d : ℂ) := a + b + c + d
private def e₂ (a b c d : ℂ) := a*b + a*c + a*d + b*c + b*d + c*d
private def e₃ (a b c d : ℂ) := a*b*c + a*b*d + a*c*d + b*c*d
private def e₄ (a b c d : ℂ) := a*b*c*d

private def coeff (e : ℂ → ℂ → ℂ → ℂ → ℂ) (x : Mat) : ℂ :=
  ∑ σ : Perm, e (x (σ 0,0)) (x (σ 1,1)) (x (σ 2,2)) (x (σ 3,3))

private theorem lineExpansion (x : Mat) (s : ℂ) :
    MvPolynomial.eval (fun p => 1 + s * x p) (PEqualNP.Gct.permPoly ℂ 4) =
      24 + s * coeff e₁ x + s^2 * coeff e₂ x + s^3 * coeff e₃ x + s^4 * coeff e₄ x := by
  have hcard : (∑ _ : Perm, (1 : ℂ)) = 24 := by
    simp [Perm, Fintype.card_perm, Nat.factorial]
  rw [← hcard]
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, map_sum, map_mul,
    Matrix.mvPolynomialX_apply, MvPolynomial.eval_X, Fin.prod_univ_four, coeff,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  unfold e₁ e₂ e₃ e₄
  ring

-- Odd and even parts at ±1 and ±2 isolate degrees one and two.
theorem vanish {L : Submodule ℂ Mat} (hL : Lev L) (x : Mat) (hx : x ∈ L) :
    coeff e₁ x = 0 ∧ coeff e₂ x = 0 := by
  have h (s : ℂ) :
      24 + s * coeff e₁ x + s^2 * coeff e₂ x + s^3 * coeff e₃ x + s^4 * coeff e₄ x = 24 := by
    rw [← lineExpansion]
    exact hL (s • x) (L.smul_mem s hx)
  constructor
  · linear_combination (8 * (h 1 - h (-1)) - (h 2 - h (-2))) / 12
  · linear_combination (16 * (h 1 + h (-1)) - (h 2 + h (-2))) / 24

private def B (x y : Mat) : ℂ :=
  dot x y - (∑ i : Fin 4, (∑ j : Fin 4, x (i,j)) * (∑ j : Fin 4, y (i,j))) -
    (∑ j : Fin 4, (∑ i : Fin 4, x (i,j)) * (∑ i : Fin 4, y (i,j))) +
    total x * total y

private theorem B_symm (x y : Mat) : B x y = B y x := by
  simp [B, dot, mul_comm]

private theorem B_add_left (x y z : Mat) : B (x+y) z = B x z + B y z := by
  simp only [B, dot, total, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private theorem B_add_right (x y z : Mat) : B x (y+z) = B x y + B x z := by
  rw [B_symm x, B_add_left, B_symm y, B_symm z]

theorem first (x : Mat) : coeff e₁ x = 6 * total x := by
  unfold coeff
  rw [permTuples (fun a b c d => e₁ (x (a,0)) (x (b,1)) (x (c,2)) (x (d,3)))]
  simp only [e₁, total, Fin.sum_univ_four]
  ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem second (x : Mat) : coeff e₂ x = B x x := by
  unfold coeff
  rw [permTuples (fun a b c d => e₂ (x (a,0)) (x (b,1)) (x (c,2)) (x (d,3)))]
  simp only [e₂, B, dot, total, Fin.sum_univ_four]
  ring

private theorem B_eq (x y : Mat) :
    dot (fun p => x p - (∑ j : Fin 4, x (p.1,j)) -
      (∑ i : Fin 4, x (i,p.2)) + total x) y = B x y := by
  simp only [dot, B, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j : Fin 4 => (∑ k : Fin 4, x (k,j)) * y (i,j))]
  simp only [← Finset.mul_sum, total]

theorem polarization {L : Submodule ℂ Mat} (hL : Lev L) (x y : Mat)
    (hx : x ∈ L) (hy : y ∈ L) : B x y = 0 := by
  have q (v : Mat) (hv : v ∈ L) : B v v = 0 := second v ▸ (vanish hL v hv).2
  have h := q _ (L.add_mem hx hy)
  rw [B_add_left, B_add_right, B_add_right, q x hx, q y hy, B_symm y x] at h
  linear_combination h / 2

end LevelPolarProof

open LevelPolarProof in
theorem levelPolar (L : Submodule ℂ Mat) (hL : Lev L) :
    (∀ x ∈ L, total x = 0) ∧
      (∀ x ∈ L, ∀ y ∈ L,
        dot (fun p => x p - (∑ j : Fin 4, x (p.1,j)) -
          (∑ i : Fin 4, x (i,p.2)) + total x) y = 0) := by
  constructor
  · intro x hx
    have h := (vanish hL x hx).1
    rw [first] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  · intro x hx y hy
    rw [B_eq]
    exact polarization hL x y hx hy

end PQ183Core

/-!
# A special case of L-gct-091

A complex level space for the permanent at the all-ones 4 by 4 matrix has
dimension at most five if it contains all zero-sum perturbations on its last
row or column. This extra hypothesis is essential to the proof here. The
general L-gct-091 statement is not proved in this file.

First use the free row to equate four cofactors. Fourier coordinates on each
remaining centred column turn their three-variable permanent equations into
elementary product equations. These reduce the image to at most two dimensions;
at most three further independent coordinates occur in the last row.
-/

namespace PQFullRow

def topBlock (t : Fin 4 × Fin 4 → ℂ) : Fin 3 × Fin 4 → ℂ :=
  fun p => t (p.1.castSucc, p.2)

def bottom (w : Fin 4 → ℂ) : Fin 4 × Fin 4 → ℂ :=
  fun p => if p.1 = (3 : Fin 4) then w p.2 else 0

private noncomputable def cofactor (t : Fin 4 × Fin 4 → ℂ) (j : Fin 4) : ℂ :=
  (Matrix.of fun i k : Fin 3 => 1 + topBlock t (i, j.succAbove k)).permanent

private theorem expandFirstCol (A : Matrix (Fin 4) (Fin 4) ℂ) :
    A.permanent = ∑ j : Fin 4, A j 0 * (A.submatrix j.succAbove Fin.succ).permanent := by
  classical
  unfold Matrix.permanent
  rw [← (Equiv.Perm.decomposeFin' (n := 2)).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Fin.prod_univ_succ]
  rfl

private theorem expandBottom (t : Fin 4 × Fin 4 → ℂ) :
    MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) =
      ∑ j, (1 + t (3, j)) * cofactor t j := by
  let A := Matrix.of fun i j : Fin 4 => 1 + t (i, j)
  have heval : MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) =
      A.permanent := by
    simp [A, PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]
  let r := (finRotate 4).symm
  have hr0 : r 0 = 3 := by decide
  have hrs : ∀ i : Fin 3, r i.succ = i.castSucc := by decide
  rw [heval, ← Matrix.permanent_transpose A, ← Matrix.permanent_permute_rows r,
    expandFirstCol]
  apply Finset.sum_congr rfl
  intro j _
  change (1 + t (r 0, j)) * _ = _
  rw [hr0]
  congr 1
  unfold cofactor
  rw [← Matrix.permanent_transpose (Matrix.of _)]
  congr 1
  ext i k
  change 1 + t (r k.succ, j.succAbove i) = 1 + t (k.castSucc, j.succAbove i)
  rw [hrs]

/-- A full zero-sum bottom row forces zero bottom-row sum on `L` and fixes
all four complementary permanents at their value at the origin. -/
theorem topMinors (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hlevel : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (hrow : ∀ w : Fin 4 → ℂ, (∑ j, w j) = 0 → bottom w ∈ L)
    (t : Fin 4 × Fin 4 → ℂ) (ht : t ∈ L) :
    (∑ j, t (3,j)) = 0 ∧ ∀ j : Fin 4,
      (Matrix.of fun i k : Fin 3 => 1 + topBlock t (i,j.succAbove k)).permanent = 6 := by
  classical
  -- Concentrate the whole last row of `J+u` at column `j` without changing its sum.
  have hprod (u : Fin 4 × Fin 4 → ℂ) (hu : u ∈ L) (j : Fin 4) :
      (4 + ∑ k, u (3,k)) * cofactor u j = 24 := by
    let s := ∑ k : Fin 4, (1 + u (3,k))
    let w := fun k : Fin 4 => (if k = j then s else 0) - (1 + u (3,k))
    have hw : (∑ k, w k) = 0 := by simp [w, Finset.sum_sub_distrib, s]
    have hb (k : Fin 4) : 1 + (u + bottom w) (3,k) = if k = j then s else 0 := by
      simp [Pi.add_apply, bottom, w]
      ring
    have hc (k : Fin 4) : cofactor (u + bottom w) k = cofactor u k := by
      have hne (i : Fin 3) : i.castSucc ≠ (3 : Fin 4) := Fin.castSucc_ne_last i
      simp [cofactor, topBlock, bottom, hne]
    have h := hlevel _ (L.add_mem hu (hrow w hw))
    rw [expandBottom] at h
    simp only [hb, hc, ite_mul, zero_mul] at h
    simpa [s, Finset.sum_add_distrib] using h
  have hz : (∑ j, t (3,j)) = 0 := by
    by_contra hn
    let z : ℂ := -4 / (∑ j, t (3,j))
    have he : 4 + z * (∑ j, t (3,j)) = 0 := by
      dsimp [z]
      field_simp
      ring
    have h := hprod _ (L.smul_mem z ht) 0
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, he, zero_mul] at h
    norm_num at h
  refine ⟨hz, fun j => ?_⟩
  change cofactor t j = 6
  have h := hprod t ht j
  rw [hz, add_zero] at h
  linear_combination h / 4

end PQFullRow

namespace PQFullRow
open Finset

private theorem permanentThree (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.permanent = A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 1 2 * A 2 1 + A 0 1 * A 1 0 * A 2 2 +
      A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 + A 0 2 * A 1 1 * A 2 0 := by
  have hu : (univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
        Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by decide
  unfold Matrix.permanent
  rw [hu, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [Fin.prod_univ_three, Equiv.Perm.mul_apply, Equiv.swap_apply_def, Equiv.Perm.one_apply]
  simp
  ring

private theorem fourierRoot : ∃ w : ℂ, w ^ 2 + w + 1 = 0 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  exact ⟨(-1 + Complex.I * (Real.sqrt 3 : ℝ)) / 2, by
    linear_combination (((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * hI - h3) / 4⟩

set_option maxHeartbeats 1200000 in
private theorem tripleOrder :
    ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      ∃ (d : Fin 4) (σ : Equiv.Perm (Fin 3)),
        d.succAbove (σ 0) = i ∧ d.succAbove (σ 1) = j ∧ d.succAbove (σ 2) = k := by decide

variable {U : Submodule ℂ (Fin 3 × Fin 4 → ℂ)}

private theorem tripleMinor
    (hU : ∀ x ∈ U, ∀ j : Fin 4,
      (Matrix.of fun i k : Fin 3 => 1 + x (i,j.succAbove k)).permanent = 6)
    (x : U) (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Matrix.of fun r s : Fin 3 => 1 + x.val (r,![i,j,k] s)).permanent = 6 := by
  obtain ⟨d, σ, h0, h1, h2⟩ := tripleOrder i j k hij hik hjk
  have he : ∀ s : Fin 3, ![i,j,k] s = d.succAbove (σ s) := by
    intro s; fin_cases s
    exacts [h0.symm, h1.symm, h2.symm]
  simp_rw [he]
  exact (Matrix.permanent_permute_rows σ
    (Matrix.of fun r s : Fin 3 => 1 + x.val (r,d.succAbove s))).trans (hU _ x.2 d)

-- Extract the linear term of the permanent at the ones matrix.
private theorem minorLinear (M : Matrix (Fin 3) (Fin 3) ℂ)
    (h : ∀ t : ℂ, (Matrix.of fun r s => 1 + t * M r s).permanent = 6) :
    M 0 0 + M 1 0 + M 2 0 + (M 0 1 + M 1 1 + M 2 1) + (M 0 2 + M 1 2 + M 2 2) = 0 := by
  have h1 := h 1; have hm := h (-1); have h2 := h 2
  simp only [permanentThree, Matrix.of_apply] at h1 hm h2
  linear_combination (6*h1 - 2*hm - h2)/12

private theorem columnSum
    (hU : ∀ x ∈ U, ∀ j : Fin 4,
      (Matrix.of fun i k : Fin 3 => 1 + x (i,j.succAbove k)).permanent = 6)
    (x : U) (c : Fin 4) : x.val (0,c) + x.val (1,c) + x.val (2,c) = 0 := by
  let f (j : Fin 4) := x.val (0,j) + x.val (1,j) + x.val (2,j)
  have h (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      f i + f j + f k = 0 :=
    minorLinear (Matrix.of fun r s => x.val (r, ![i,j,k] s))
      (fun t => tripleMinor hU (t • x) i j k hij hik hjk)
  have e0 := h 1 2 3 (by decide) (by decide) (by decide)
  have e1 := h 0 2 3 (by decide) (by decide) (by decide)
  have e2 := h 0 1 3 (by decide) (by decide) (by decide)
  have e3 := h 0 1 2 (by decide) (by decide) (by decide)
  change f c = 0
  fin_cases c
  · change f 0 = 0
    linear_combination (e1 + e2 + e3 - 2*e0)/3
  · change f 1 = 0
    linear_combination (e0 + e2 + e3 - 2*e1)/3
  · change f 2 = 0
    linear_combination (e0 + e1 + e3 - 2*e2)/3
  · change f 3 = 0
    linear_combination (e0 + e1 + e2 - 2*e3)/3

-- The constant, quadratic and cubic parts of the permanent in the two nontrivial
-- Fourier modes. Here `-w-1` is `w²`.
private theorem fourierEval {w : ℂ} (hw : w ^ 2 + w + 1 = 0) (a b c d e f : ℂ) :
    (1 + (a+b)) * (1 + (w*c + (-w-1)*d)) * (1 + ((-w-1)*e + w*f)) +
    (1 + (a+b)) * (1 + (w*e + (-w-1)*f)) * (1 + ((-w-1)*c + w*d)) +
    (1 + (c+d)) * (1 + (w*a + (-w-1)*b)) * (1 + ((-w-1)*e + w*f)) +
    (1 + (c+d)) * (1 + (w*e + (-w-1)*f)) * (1 + ((-w-1)*a + w*b)) +
    (1 + (e+f)) * (1 + (w*a + (-w-1)*b)) * (1 + ((-w-1)*c + w*d)) +
    (1 + (e+f)) * (1 + (w*c + (-w-1)*d)) * (1 + ((-w-1)*a + w*b)) =
      6 + 6*(a*c*e + b*d*f) - 3*(a*d+b*c + a*f+b*e + c*f+d*e) := by
  linear_combination
    (2*(a*c*f+a*d*e+b*c*e+a*d*f+b*c*f+b*d*e) - 6*(a*c*e+b*d*f) -
      2*((a-b)*(c-d)+(a-b)*(e-f)+(c-d)*(e-f))) * hw

/-- The four columns admit jointly faithful pairs of Fourier coordinates. On every
triple the pure cubic and the mixed quadratic vanish. -/
theorem existsCoords
    (hU : ∀ x ∈ U, ∀ j : Fin 4,
      (Matrix.of fun i k : Fin 3 => 1 + x (i,j.succAbove k)).permanent = 6) :
    ∃ a b : Fin 4 → Module.Dual ℂ U,
      (∀ (x : U) (i j k : Fin 4), i ≠ j → i ≠ k → j ≠ k →
        a i x * a j x * a k x + b i x * b j x * b k x = 0) ∧
      (∀ (x : U) (i j k : Fin 4), i ≠ j → i ≠ k → j ≠ k →
        a i x * b j x + b i x * a j x + a i x * b k x + b i x * a k x +
          a j x * b k x + b j x * a k x = 0) ∧
      (∀ x : U, (∀ j, a j x = 0) → (∀ j, b j x = 0) → x = 0) := by
  obtain ⟨w, hw⟩ := fourierRoot
  let E (r : Fin 3) (j : Fin 4) : Module.Dual ℂ U := (LinearMap.proj (r,j)).domRestrict U
  let a (j : Fin 4) := ((1-w)/3) • E 0 j + ((-2*w-1)/3) • E 1 j
  let b (j : Fin 4) := ((w+2)/3) • E 0 j + ((2*w+1)/3) • E 1 j
  have reconstruct (x : U) (j : Fin 4) :
      x.val (0,j) = a j x + b j x ∧
      x.val (1,j) = w*a j x + (-w-1)*b j x ∧
      x.val (2,j) = (-w-1)*a j x + w*b j x := by
    have r0 : x.val (0,j) = a j x + b j x := by
      change x.val (0,j) = ((1-w)/3 * x.val (0,j) + (-2*w-1)/3 * x.val (1,j)) +
        ((w+2)/3 * x.val (0,j) + (2*w+1)/3 * x.val (1,j))
      ring
    have r1 : x.val (1,j) = w*a j x + (-w-1)*b j x := by
      change x.val (1,j) = w * ((1-w)/3 * x.val (0,j) + (-2*w-1)/3 * x.val (1,j)) +
        (-w-1) * ((w+2)/3 * x.val (0,j) + (2*w+1)/3 * x.val (1,j))
      linear_combination ((2*x.val (0,j) + 4*x.val (1,j))/3) * hw
    refine ⟨r0, r1, ?_⟩
    linear_combination columnSum hU x j - r0 - r1
  have expansion (x : U) (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      6 + 6 * (a i x * a j x * a k x + b i x * b j x * b k x) -
        3 * (a i x * b j x + b i x * a j x + a i x * b k x + b i x * a k x +
          a j x * b k x + b j x * a k x) = 6 := by
    have h := tripleMinor hU x i j k hij hik hjk
    simp only [permanentThree, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
    obtain ⟨hi0,hi1,hi2⟩ := reconstruct x i
    obtain ⟨hj0,hj1,hj2⟩ := reconstruct x j
    obtain ⟨hk0,hk1,hk2⟩ := reconstruct x k
    rw [hi0,hi1,hi2,hj0,hj1,hj2,hk0,hk1,hk2, fourierEval hw] at h
    exact h
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro x i j k hij hik hjk
    have h := expansion x i j k hij hik hjk
    have h' := expansion (-x) i j k hij hik hjk
    simp only [map_neg] at h'
    linear_combination (h - h')/12
  · intro x i j k hij hik hjk
    have h := expansion x i j k hij hik hjk
    have h' := expansion (-x) i j k hij hik hjk
    simp only [map_neg] at h'
    linear_combination -(h + h')/6
  · intro x ha hb
    apply Subtype.ext
    funext ⟨r,j⟩
    change x.val (r,j) = 0
    obtain ⟨r0,r1,r2⟩ := reconstruct x j
    simp only [ha j, hb j, mul_zero, add_zero] at r0 r1 r2
    fin_cases r
    exacts [r0,r1,r2]

end PQFullRow

namespace PQFullRow.Quadratic

/-- The polar form of `x 0 * x 3 + x 1 * x 2`, as a map into the dual space. -/
noncomputable def polar : (Fin 4 → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin 4 → ℂ) :=
  LinearMap.mk₂ ℂ (fun x y => x 3 * y 0 + x 0 * y 3 + x 2 * y 1 + x 1 * y 2)
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem polar_apply (x y : Fin 4 → ℂ) :
    polar x y = x 3 * y 0 + x 0 * y 3 + x 2 * y 1 + x 1 * y 2 := rfl

theorem polar_injective : Function.Injective polar := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h : ∀ k, polar x (Pi.single k 1) = 0 := fun k => by rw [hx]; rfl
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [polar_apply, Pi.single_apply] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  funext k
  fin_cases k <;> simp [h0, h1, h2, h3]

/-- A subspace on which `x 0 * x 3 + x 1 * x 2` vanishes has dimension at most two. -/
theorem finrank_le_two (R : Submodule ℂ (Fin 4 → ℂ))
    (hR : ∀ x ∈ R, x 0 * x 3 + x 1 * x 2 = 0) : Module.finrank ℂ R ≤ 2 := by
  have hiso : ∀ x ∈ R, ∀ y ∈ R, polar x y = 0 := by
    intro x hx y hy
    have e1 := hR _ (R.add_mem hx hy)
    have e2 := hR x hx
    have e3 := hR y hy
    simp only [Pi.add_apply] at e1
    rw [polar_apply]
    linear_combination e1 - e2 - e3
  have hr : ∀ x : R, polar.domRestrict R x ∈ R.dualAnnihilator := fun x =>
    (Submodule.mem_dualAnnihilator _).2 fun y hy => hiso x x.2 y hy
  have hinj : Function.Injective ((polar.domRestrict R).codRestrict R.dualAnnihilator hr) :=
    fun a b hab => Subtype.ext (polar_injective (congrArg Subtype.val hab))
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq R
  have h3 : Module.finrank ℂ (Fin 4 → ℂ) = 4 := Module.finrank_fin_fun ℂ
  omega


end PQFullRow.Quadratic

namespace PQFullRow

theorem twoColumnBound {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    (α β γ δ : Module.Dual ℂ U)
    (hzero : ∀ x, α x = 0 → β x = 0 → γ x = 0 → δ x = 0 → x = 0)
    (hquad : ∀ x, α x * δ x + β x * γ x = 0) : Module.finrank ℂ U ≤ 2 := by
  let f : U →ₗ[ℂ] (Fin 4 → ℂ) := LinearMap.pi ![α, β, γ, δ]
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact hzero x (congrFun hx 0) (congrFun hx 1) (congrFun hx 2) (congrFun hx 3)
  have h := Quadratic.finrank_le_two (LinearMap.range f) (by
    rintro _ ⟨x, rfl⟩
    exact hquad x)
  rwa [LinearMap.finrank_range_of_inj hf] at h

end PQFullRow

namespace PQFullRow

private abbrev MaskLaw (A B : Fin 4 → Prop) :=
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k → A i → A j → A k → False) →
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k → B i → B j → B k → False) →
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ A k → ¬ B k → A i → ¬ B i → B j → False) →
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ B k → ¬ A k → B i → ¬ A i → A j → False) →
  (∃ i j, i ≠ j ∧ ∀ k, k ≠ i → k ≠ j → ¬ A k ∧ ¬ B k) ∨
  (∃ i j k l : Fin 4, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
    (∀ t : Fin 4, t=i ∨ t=j ∨ t=k ∨ t=l) ∧ ¬ B i ∧ ¬ B j ∧ ¬ A k ∧ ¬ A l ∧ A i ∧ B k)

private def maskFn (a b c d : Bool) : Fin 4 → Prop :=
  fun i => ![a, b, c, d] i = true

-- Once nonzero triples and cross terms through a zero column have been
-- excluded, the remaining question concerns only two four-bit supports.
set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem boolMaskLaw : ∀ a b c d e f g h : Bool,
    MaskLaw (maskFn a b c d) (maskFn e f g h) := by
  unfold MaskLaw maskFn
  decide +kernel

private theorem masks (A B : Fin 4 → Prop) : MaskLaw A B := by
  classical
  have repr (P : Fin 4 → Prop) :
      maskFn (decide (P 0)) (decide (P 1)) (decide (P 2)) (decide (P 3)) = P := by
    funext i
    fin_cases i <;> simp [maskFn]
  have law := boolMaskLaw (decide (A 0)) (decide (A 1)) (decide (A 2)) (decide (A 3))
    (decide (B 0)) (decide (B 1)) (decide (B 2)) (decide (B 3))
  rwa [repr A, repr B] at law

private theorem not_dense (a b : Fin 4 → ℂ)
    (hc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      a i*a j*a k+b i*b j*b k=0)
    (hq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (a i*b j+b i*a j)+(a i*b k+b i*a k)+(a j*b k+b j*a k)=0)
    (ha : ∀ i, a i ≠ 0) : False := by
  let r := fun i => b i / a i
  have prodR (i j k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      r i * r j * r k = -1 := by
    dsimp [r]
    field_simp [ha]
    linear_combination hc i j k hij hik hjk
  have same (x y z w : ℂ) (h : x*y*z = -1) (h' : x*y*w = -1) : z = w := by
    apply mul_left_cancel₀ (a := x*y)
    · intro e
      rw [e, zero_mul] at h
      norm_num at h
    · exact h.trans h'.symm
  have hr (i : Fin 4) : r i = r 0 := by
    fin_cases i
    · rfl
    · exact same _ _ _ _ (prodR 2 3 1 (by decide) (by decide) (by decide))
        (prodR 2 3 0 (by decide) (by decide) (by decide))
    · exact same _ _ _ _ (prodR 1 3 2 (by decide) (by decide) (by decide))
        (prodR 1 3 0 (by decide) (by decide) (by decide))
    · exact same _ _ _ _ (prodR 1 2 3 (by decide) (by decide) (by decide))
        (prodR 1 2 0 (by decide) (by decide) (by decide))
  have hn : r 0 ≠ 0 := by
    intro h
    have e := prodR 0 1 2 (by decide) (by decide) (by decide)
    simp [h] at e
  have hb (i) : b i = r 0 * a i := (div_eq_iff (ha i)).mp (hr i)
  have invSum (i j k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (a i)⁻¹ + (a j)⁻¹ + (a k)⁻¹ = 0 := by
    have e := hq i j k hij hik hjk
    simp only [hb] at e
    field_simp [ha]
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ) ≠ 0) hn)
    linear_combination e
  have h₀ := invSum 1 2 3 (by decide) (by decide) (by decide)
  have h₁ := invSum 0 2 3 (by decide) (by decide) (by decide)
  have h₂ := invSum 0 1 3 (by decide) (by decide) (by decide)
  have h₃ := invSum 0 1 2 (by decide) (by decide) (by decide)
  apply inv_ne_zero (ha 0)
  linear_combination (h₁ + h₂ + h₃ - 2*h₀)/3

private theorem not_mixed3 {a A b B c C : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a*b*c + A*B*C = 0) (h1 : a*B + A*b = 0) (h2 : a*C + A*c = 0)
    (h3 : b*C + B*c = 0) : False := by
  have h : (2 : ℂ) * A * (b*c) = 0 := by
    linear_combination c*h1 + b*h2 - a*h3
  have hA : A = 0 := (mul_eq_zero.mp
    ((mul_eq_zero.mp h).resolve_right (mul_ne_zero hb hc))).resolve_left (by norm_num)
  simp [hA, ha, hb, hc] at he

private theorem no_three (a b : Fin 4 → ℂ)
    (hc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      a i * a j * a k + b i * b j * b k = 0)
    (hq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (a i*b j+b i*a j)+(a i*b k+b i*a k)+(a j*b k+b j*a k)=0)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : a i ≠ 0) (hj : a j ≠ 0) (hk : a k ≠ 0) : False := by
  classical
  have hmiss : ¬ ∀ l, a l ≠ 0 := not_dense a b hc hq
  push Not at hmiss
  obtain ⟨l, hl⟩ := hmiss
  have hil : i ≠ l := fun h => hi (h ▸ hl)
  have hjl : j ≠ l := fun h => hj (h ▸ hl)
  have hkl : k ≠ l := fun h => hk (h ▸ hl)
  have he := hc i j k hij hik hjk
  have hn : b i * b j ≠ 0 := by
    intro h
    apply mul_ne_zero (mul_ne_zero hi hj) hk
    simpa [h] using he
  have hbl : b l = 0 := by
    have h := hc i j l hij hil hjl
    exact (mul_eq_zero.mp (by simpa [hl] using h : b i * b j * b l = 0)).resolve_left hn
  exact not_mixed3 hi hj hk he (by simpa [hl, hbl] using hq i j l hij hil hjl)
    (by simpa [hl, hbl] using hq i k l hik hil hkl)
    (by simpa [hl, hbl] using hq j k l hjk hjl hkl)

private theorem no_cross (a b : Fin 4 → ℂ)
    (hq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (a i*b j+b i*a j)+(a i*b k+b i*a k)+(a j*b k+b j*a k)=0)
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hak : ¬ a k ≠ 0) (hbk : ¬ b k ≠ 0)
    (hai : a i ≠ 0) (hbi : ¬ b i ≠ 0) (hbj : b j ≠ 0) : False := by
  apply mul_ne_zero hai hbj
  simpa [not_not.mp hak, not_not.mp hbk, not_not.mp hbi] using hq i j k hij hik hjk

/-- Four scalar pairs obeying the Fourier cubic and quadratic identities are
concentrated in two columns, or split as two opposite pairs along the axes. -/
theorem pointwise (a b : Fin 4 → ℂ)
    (hc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      a i * a j * a k + b i * b j * b k = 0)
    (hq : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (a i*b j+b i*a j)+(a i*b k+b i*a k)+(a j*b k+b j*a k)=0) :
    (∃ i j, i ≠ j ∧ ∀ k, k ≠ i → k ≠ j → a k = 0 ∧ b k = 0) ∨
    (∃ i j k l : Fin 4, (∀ t : Fin 4, t=i ∨ t=j ∨ t=k ∨ t=l) ∧
      b i = 0 ∧ b j = 0 ∧ a k = 0 ∧ a l = 0 ∧ a j = -a i ∧ b l = -b k) := by
  have hc' (i j k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      b i*b j*b k + a i*a j*a k = 0 := by
    simpa only [add_comm] using hc i j k hij hik hjk
  have hq' (i j k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      (b i*a j+a i*b j)+(b i*a k+a i*b k)+(b j*a k+a j*b k)=0 := by
    linear_combination hq i j k hij hik hjk
  rcases masks (fun i => a i ≠ 0) (fun i => b i ≠ 0) (no_three a b hc hq)
      (no_three b a hc' hq') (no_cross a b hq) (no_cross b a hq') with
      ⟨i,j,hij,ho⟩ | ⟨i,j,k,l,hij,hik,hil,hjk,_,hkl,cover,hbi,hbj,hak,hal,hai,hbk⟩
  · exact Or.inl ⟨i, j, hij, fun k hki hkj => by simpa using ho k hki hkj⟩
  · replace hbi : b i = 0 := not_not.mp hbi
    replace hbj : b j = 0 := not_not.mp hbj
    replace hak : a k = 0 := not_not.mp hak
    replace hal : a l = 0 := not_not.mp hal
    refine Or.inr ⟨i,j,k,l,cover,hbi,hbj,hak,hal,?_,?_⟩
    · have he := hq i j k hij hik hjk
      simp only [hbi, hbj, hak, mul_zero, zero_mul, zero_add, add_zero] at he
      apply eq_neg_of_add_eq_zero_left
      apply (mul_eq_zero.mp ?_).resolve_right hbk
      linear_combination he
    · have he := hq i k l hik hil hkl
      simp only [hbi, hak, hal, mul_zero, zero_mul, add_zero] at he
      apply eq_neg_of_add_eq_zero_left
      apply (mul_eq_zero.mp ?_).resolve_left hai
      linear_combination he

end PQFullRow


namespace PQFullRow

variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-- Simultaneous detection of vanishing in a finite family of linear forms. -/
private theorem genericEvaluation {ι : Type*} [Finite ι] (f : ι → Module.Dual ℂ U) :
    ∃ x, ∀ i, f i x = 0 → f i = 0 := by
  classical
  let S := {i : ι // f i ≠ 0}
  obtain ⟨x, hx⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun i : S => f i.val) (by
      intro i
      by_contra! h
      exact i.property (LinearMap.ext h))
  exact ⟨x, fun i hi => by
    by_contra hn
    exact hx ⟨i, hn⟩ hi⟩

/-- Test both the coordinates and the pair sums that occur in the
complementary-pair alternative. -/
private theorem genericFour (a b : Fin 4 → Module.Dual ℂ U) :
    ∃ x : U, (∀ i, a i x = 0 → a i = 0) ∧ (∀ i, b i x = 0 → b i = 0) ∧
      (∀ i j, a i x + a j x = 0 → a i + a j = 0) ∧
      (∀ i j, b i x + b j x = 0 → b i + b j = 0) := by
  let forms : Bool × Fin 4 × Option (Fin 4) → Module.Dual ℂ U
    | (false, i, none) => a i
    | (true, i, none) => b i
    | (false, i, some j) => a i + a j
    | (true, i, some j) => b i + b j
  obtain ⟨x, hx⟩ := genericEvaluation forms
  exact ⟨x, fun i => hx (false, i, none), fun i => hx (true, i, none),
    fun i j => hx (false, i, some j), fun i j => hx (true, i, some j)⟩

private theorem boundByTwoSeparating (f g : Module.Dual ℂ U)
    (h : ∀ x, f x = 0 → g x = 0 → x = 0) : Module.finrank ℂ U ≤ 2 := by
  let m := f.prod g
  have hinj : Function.Injective m := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply h
    · simpa [m] using sub_eq_zero.mpr (congrArg Prod.fst hxy)
    · simpa [m] using sub_eq_zero.mpr (congrArg Prod.snd hxy)
  simpa [Module.finrank_prod] using LinearMap.finrank_le_finrank_of_injective hinj

private theorem twoSupportedBound
    (twoColumnBound : ∀ α β γ δ : Module.Dual ℂ U,
      (∀ x, α x = 0 → β x = 0 → γ x = 0 → δ x = 0 → x = 0) →
      (∀ x, α x * δ x + β x * γ x = 0) → Module.finrank ℂ U ≤ 2)
    (a b : Fin 4 → Module.Dual ℂ U)
    (hq : ∀ x i j k, i ≠ j → i ≠ k → j ≠ k →
      a i x * b j x + b i x * a j x + a i x * b k x +
        b i x * a k x + a j x * b k x + b j x * a k x = 0)
    (hz : ∀ x : U, (∀ t, a t x = 0) → (∀ t, b t x = 0) → x = 0)
    (i j : Fin 4) (hij : i ≠ j)
    (ho : ∀ k, k ≠ i → k ≠ j → a k = 0 ∧ b k = 0) : Module.finrank ℂ U ≤ 2 := by
  apply twoColumnBound (a i) (b i) (a j) (b j)
  · intro x hai hbi haj hbj
    apply hz <;> intro t
    · by_cases hi : t = i
      · simpa [hi] using hai
      by_cases hj : t = j
      · simpa [hj] using haj
      simp [(ho t hi hj).1]
    · by_cases hi : t = i
      · simpa [hi] using hbi
      by_cases hj : t = j
      · simpa [hj] using hbj
      simp [(ho t hi hj).2]
  · have havail : ∀ r s : Fin 4, ∃ t, t ≠ r ∧ t ≠ s := by decide
    obtain ⟨k, hki, hkj⟩ := havail i j
    obtain ⟨ha, hb⟩ := ho k hki hkj
    intro x
    simpa [ha, hb] using hq x i j k hij hki.symm hkj.symm

/-- Two opposite pairs are determined by one entry of each pair. -/
private theorem oppositePairsBound
    (a b : Fin 4 → Module.Dual ℂ U)
    (hz : ∀ x : U, (∀ t, a t x = 0) → (∀ t, b t x = 0) → x = 0)
    (i j k l : Fin 4) (cover : ∀ t : Fin 4, t = i ∨ t = j ∨ t = k ∨ t = l)
    (hbi : b i = 0) (hbj : b j = 0) (hak : a k = 0) (hal : a l = 0)
    (haij : a j + a i = 0) (hbkl : b l + b k = 0) : Module.finrank ℂ U ≤ 2 := by
  apply boundByTwoSeparating (a i) (b k)
  intro x hai hbk
  have haj : a j x = 0 := by simpa [hai] using LinearMap.congr_fun haij x
  have hbl : b l x = 0 := by simpa [hbk] using LinearMap.congr_fun hbkl x
  apply hz <;> intro t <;> rcases cover t with rfl | rfl | rfl | rfl <;> simp_all

/-- The cubic and quadratic Fourier identities for the four triples bound a
separating family by dimension two. `twoColumnBound` handles the residual
quadric when at most two columns survive. -/
theorem fourierFamilyBound [FiniteDimensional ℂ U]
    (twoColumnBound : ∀ α β γ δ : Module.Dual ℂ U,
      (∀ x, α x = 0 → β x = 0 → γ x = 0 → δ x = 0 → x = 0) →
      (∀ x, α x * δ x + β x * γ x = 0) → Module.finrank ℂ U ≤ 2)
    (a b : Fin 4 → Module.Dual ℂ U)
    (hc : ∀ x i j k, i ≠ j → i ≠ k → j ≠ k →
      a i x * a j x * a k x + b i x * b j x * b k x = 0)
    (hq : ∀ x i j k, i ≠ j → i ≠ k → j ≠ k →
      a i x * b j x + b i x * a j x + a i x * b k x +
        b i x * a k x + a j x * b k x + b j x * a k x = 0)
    (hz : ∀ x : U, (∀ t, a t x = 0) → (∀ t, b t x = 0) → x = 0) :
    Module.finrank ℂ U ≤ 2 := by
  obtain ⟨x, ha, hb, hsa, hsb⟩ := genericFour a b
  rcases pointwise (fun i => a i x) (fun i => b i x) (hc x)
      (fun i j k hij hik hjk => by simpa only [add_assoc] using hq x i j k hij hik hjk) with
      ⟨i, j, hij, ho⟩ | ⟨i, j, k, l, cover, hbi, hbj, hak, hal, haij, hbkl⟩
  · apply twoSupportedBound twoColumnBound a b hq hz i j hij
    intro t hti htj
    obtain ⟨hat, hbt⟩ := ho t hti htj
    exact ⟨ha t hat, hb t hbt⟩
  · apply oppositePairsBound a b hz i j k l cover (hb i hbi) (hb j hbj) (ha k hak) (ha l hal)
    · exact hsa j i (by simp [haij])
    · exact hsb l k (by simp [hbkl])

end PQFullRow

namespace PQFullRow

theorem fullRowBound (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hlevel : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (hrow : ∀ w : Fin 4 → ℂ, (∑ j, w j) = 0 → bottom w ∈ L) :
    Module.finrank ℂ L ≤ 5 := by
  let T : L →ₗ[ℂ] (Fin 3 × Fin 4 → ℂ) :=
    LinearMap.pi fun p => (LinearMap.proj (p.1.castSucc, p.2)).comp L.subtype
  let U := LinearMap.range T
  have hU : ∀ x ∈ U, ∀ j : Fin 4,
      (Matrix.of fun i k : Fin 3 => 1 + x (i, j.succAbove k)).permanent = 6 := by
    rintro _ ⟨x, rfl⟩
    exact (topMinors L hlevel hrow x.1 x.2).2
  obtain ⟨a, b, hc, hq, hz⟩ := existsCoords hU
  have hd : Module.finrank ℂ U ≤ 2 :=
    fourierFamilyBound twoColumnBound a b hc hq hz
  let f : L →ₗ[ℂ] U × (Fin 3 → ℂ) := T.rangeRestrict.prod
    (LinearMap.pi fun j : Fin 3 => (LinearMap.proj ((3 : Fin 4), j.castSucc)).comp L.subtype)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have ht : T x = 0 := congrArg Subtype.val (congrArg Prod.fst hx)
    have hr : ∀ j : Fin 3, x.1 (3,j.castSucc) = 0 := fun j =>
      congrFun (congrArg Prod.snd hx) j
    have hs := (topMinors L hlevel hrow x.1 x.2).1
    rw [Fin.sum_univ_castSucc] at hs
    simp only [hr, Finset.sum_const_zero, zero_add] at hs
    apply Subtype.ext
    funext ⟨i,j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact Fin.lastCases hs hr j
    · exact congrFun ht (i,j)
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  change Module.finrank ℂ L ≤ Module.finrank ℂ (U × (Fin 3 → ℂ)) at h
  rw [Module.finrank_prod, Module.finrank_fin_fun] at h
  omega

end PQFullRow

namespace PQFullRow

def rightCol (w : Fin 4 → ℂ) (p : Fin 4 × Fin 4) : ℂ := if p.2 = 3 then w p.1 else 0

theorem fullColBound (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hlevel : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (hcol : ∀ w : Fin 4 → ℂ, (∑ j, w j) = 0 → rightCol w ∈ L) :
    Module.finrank ℂ L ≤ 5 := by
  let f := LinearMap.funLeft ℂ ℂ (Prod.swap : Fin 4 × Fin 4 → Fin 4 × Fin 4)
  have hf : Function.Injective f := by
    intro a b h
    funext p
    exact congrFun h p.swap
  have ev (a : Fin 4 × Fin 4 → ℂ) : MvPolynomial.eval a (PEqualNP.Gct.permPoly ℂ 4) =
      (Matrix.of fun i j => a (i,j)).permanent := by
    simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]
  have hl : ∀ t ∈ L.map f,
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24 := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hlevel x hx
    rw [ev] at h ⊢
    exact (Matrix.permanent_transpose (Matrix.of fun i j => 1 + x (i,j))).trans h
  have hh := fullRowBound (L.map f) hl (fun w hw => ⟨rightCol w, hcol w hw, rfl⟩)
  exact (Submodule.equivMapOfInjective f hf L).finrank_eq.le.trans hh

end PQFullRow

namespace PQFullRow

private def reindex4 (σ τ : Equiv.Perm (Fin 4)) :
    (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 4 → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun p : Fin 4 × Fin 4 => (σ p.1, τ p.2))

private theorem reindex4_injective (σ τ : Equiv.Perm (Fin 4)) :
    Function.Injective (reindex4 σ τ) := by
  intro a b h
  funext p
  have h' := congrFun h (σ.symm p.1, τ.symm p.2)
  change a (σ (σ.symm p.1), τ (τ.symm p.2)) = b (σ (σ.symm p.1), τ (τ.symm p.2)) at h'
  simpa using h'

private theorem reindex4_level (σ τ : Equiv.Perm (Fin 4)) (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (h : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24) :
    ∀ t ∈ L.map (reindex4 σ τ),
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24 := by
  rintro _ ⟨x, hx, rfl⟩
  let M : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun i j => 1 + x (i,j)
  have eqP (a : Fin 4 × Fin 4 → ℂ) : MvPolynomial.eval a (PEqualNP.Gct.permPoly ℂ 4) =
      (Matrix.of fun i j => a (i,j)).permanent := by
    simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]
  calc
    _ = ((M.submatrix σ id).submatrix id τ).permanent :=
      eqP (fun p => 1 + reindex4 σ τ x p)
    _ = (M.submatrix σ id).permanent := Matrix.permanent_permute_rows τ _
    _ = M.permanent := Matrix.permanent_permute_cols σ M
    _ = 24 := (eqP (fun p => 1 + x p)).symm.trans (h x hx)

private theorem swap_eq_iff_last (i k : Fin 4) : Equiv.swap i (3 : Fin 4) k = i ↔ k = 3 := by
  calc Equiv.swap i (3 : Fin 4) k = i ↔ Equiv.swap i 3 k = Equiv.swap i 3 3 := by simp
       _ ↔ k = 3 := (Equiv.swap i (3 : Fin 4)).injective.eq_iff

/-- The choice of the distinguished row does not affect the bound. -/
theorem fullRowBound' (i : Fin 4) (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hlevel : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (hrow : ∀ w : Fin 4 → ℂ, (∑ j, w j) = 0 →
      (fun p : Fin 4 × Fin 4 => if p.1 = i then w p.2 else 0) ∈ L) :
    Module.finrank ℂ L ≤ 5 := by
  let σ := Equiv.swap i (3 : Fin 4)
  let f := reindex4 σ (Equiv.refl _)
  have hm := fullRowBound (L.map f) (reindex4_level _ _ _ hlevel) (by
    intro w hw
    refine ⟨_, hrow w hw, ?_⟩
    funext p
    change (if Equiv.swap i 3 p.1 = i then w p.2 else 0) = (if p.1 = 3 then w p.2 else 0)
    simp only [swap_eq_iff_last])
  exact (Submodule.equivMapOfInjective f (reindex4_injective _ _) L).finrank_eq.le.trans hm

/-- The choice of the distinguished column does not affect the bound. -/
theorem fullColBound' (j : Fin 4) (L : Submodule ℂ (Fin 4 × Fin 4 → ℂ))
    (hlevel : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 4) = 24)
    (hcol : ∀ w : Fin 4 → ℂ, (∑ i, w i) = 0 →
      (fun p : Fin 4 × Fin 4 => if p.2 = j then w p.1 else 0) ∈ L) :
    Module.finrank ℂ L ≤ 5 := by
  let τ := Equiv.swap j (3 : Fin 4)
  let f := reindex4 (Equiv.refl _) τ
  have hm := fullColBound (L.map f) (reindex4_level _ _ _ hlevel) (by
    intro w hw
    refine ⟨_, hcol w hw, ?_⟩
    funext p
    change (if Equiv.swap j 3 p.2 = j then w p.1 else 0) = (if p.2 = 3 then w p.1 else 0)
    simp only [swap_eq_iff_last])
  exact (Submodule.equivMapOfInjective f (reindex4_injective _ _) L).finrank_eq.le.trans hm

end PQFullRow

namespace PQ201

private noncomputable def lagRow : Vec →ₗ[ℂ] Mat where
  toFun a := fun p => a p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def lagQ (x : Mat) : Mat := fun p => x p - ∑ i, x (i,p.2)

private noncomputable def lagInv : Mat →ₗ[ℂ] Mat where
  toFun x := fun p => x p - (∑ i, x (i,p.2)) / 3
  map_add' x y := by
    funext p
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' a x := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, RingHom.id_apply]
    ring

private theorem lagInv_Q (x : Mat) : lagInv (lagQ x) = x := by
  funext p
  change _ - (∑ i, lagQ x (i,p.2)) / 3 = _
  simp [lagQ, Finset.sum_sub_distrib]
  ring

private noncomputable abbrev lagDual := dotProductEquiv ℂ (Fin 4 × Fin 4)

private theorem lagDual_eval (x y : Mat) : lagDual (lagQ x) y = B x y := by
  change ∑ p, lagQ x p * y p = _
  rw [Fintype.sum_prod_type]
  rfl

theorem lagr (L : Submodule ℂ Mat) (hR : ∀ x ∈ L, RC x)
    (hB : ∀ x ∈ L, ∀ y ∈ L, B x y = 0) (hd : 6 ≤ Module.finrank ℂ L)
    (x : Mat) (hx : RC x) (ho : ∀ y ∈ L, B x y = 0) : x ∈ L := by
  classical
  let V := L ⊔ LinearMap.range lagRow
  have hr : Module.finrank ℂ (LinearMap.range lagRow) = 4 := by
    rw [LinearMap.finrank_range_of_inj]
    · simp [Vec, Module.finrank_fintype_fun_eq_card]
    · intro v w he
      funext i
      exact congrFun he (i,0)
  have hi : L ⊓ LinearMap.range lagRow = ⊥ := by
    apply le_antisymm _ bot_le
    rintro _ ⟨hy, v, rfl⟩
    change lagRow v = 0
    funext p
    have h := hR _ hy p.1
    change v p.1 = 0
    simpa [lagRow] using h
  have hV : Module.finrank ℂ V = Module.finrank ℂ L + 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq L (LinearMap.range lagRow)
    rw [hi, finrank_bot, add_zero, hr] at h
    exact h
  let A := lagInv.comp lagDual.symm.toLinearMap
  let S := V.dualAnnihilator.map A
  have hS : Module.finrank ℂ S ≤ 6 := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq V
    have hM : Module.finrank ℂ Mat = 16 := by simp [Mat, Module.finrank_fintype_fun_eq_card]
    rw [hV, hM] at h
    have hm := Submodule.finrank_map_le A V.dualAnnihilator
    change Module.finrank ℂ S ≤ _ at hm
    have num (a b : ℕ) (ha : 6 ≤ a) (hb : a + 4 + b = 16) : b ≤ 6 := by omega
    exact hm.trans (num _ _ hd h)
  have memS (z : Mat) (hz : RC z) (ha : ∀ y ∈ L, B z y = 0) : z ∈ S := by
    refine ⟨lagDual (lagQ z), ?_, ?_⟩
    · apply (Submodule.mem_dualAnnihilator _).mpr
      change V ≤ LinearMap.ker (lagDual (lagQ z))
      apply sup_le
      · intro y hy
        exact (lagDual_eval _ _).trans (ha _ hy)
      · rintro _ ⟨v, rfl⟩
        change lagDual (lagQ z) (lagRow v) = 0
        rw [lagDual_eval]
        have hh (i : Fin 4) : (∑ j : Fin 4, (z (i,j) - ∑ k, z (k,j))) = 0 := by
          rw [Finset.sum_sub_distrib, hz, Finset.sum_comm (f := fun j k => z (k,j))]
          simp only [hz _, Finset.sum_const_zero, sub_zero]
        simp only [B, lagRow, LinearMap.coe_mk, AddHom.coe_mk, ← Finset.sum_mul, hh,
          zero_mul, Finset.sum_const_zero]
    · change lagInv (lagDual.symm (lagDual (lagQ z))) = _
      rw [LinearEquiv.symm_apply_apply, lagInv_Q]
  have he : L = S := Submodule.eq_of_le_of_finrank_le (fun y hy => memS y (hR y hy) (hB y hy))
    (hS.trans hd)
  exact he ▸ memS _ hx ho

end PQ201

namespace PQ201

private def sym₂ (v : Vec) : ℂ :=
  v 0*v 1 + v 0*v 2 + v 0*v 3 + v 1*v 2 + v 1*v 3 + v 2*v 3
private def sym₃ (v : Vec) : ℂ :=
  v 0*v 1*v 2 + v 0*v 1*v 3 + v 0*v 2*v 3 + v 1*v 2*v 3
private def sym₄ (v : Vec) : ℂ := v 0*v 1*v 2*v 3

-- Along a rank-one line, the degree-r coefficient is
-- r! (4-r)! times the product of the two elementary symmetric functions.
set_option maxHeartbeats 2000000 in
private theorem atom_eval (j : Fin 4) (v : Vec) (s : ℂ) :
    MvPolynomial.eval (fun p => 1 + s * atom j v p) (PEqualNP.Gct.permPoly ℂ 4) =
      24 - 24*s^2*sym₂ v + 48*s^3*sym₃ v - 72*s^4*sym₄ v := by
  rw [Gap183.eval_perm_four]
  fin_cases j <;> simp (config := { decide := true }) only
      [atom, d, ite_true, ite_false, sym₂, sym₃, sym₄] <;> ring

theorem atom_single (L : Submodule ℂ Mat) (hL : Lev L) (j : Fin 4) (v : Vec)
    (hs : (∑ i, v i) = -1) (ha : atom j v ∈ L) :
    ∃ i : Fin 4, v = fun k => if k = i then -1 else 0 := by
  have h (s : ℂ) : 24 - 24*s^2*sym₂ v + 48*s^3*sym₃ v - 72*s^4*sym₄ v = 24 := by
    rw [← atom_eval j]
    exact hL _ (L.smul_mem s ha)
  have h₂ : sym₂ v = 0 := by
    linear_combination ((h 2 + h (-2)) - 16*(h 1 + h (-1))) / 576
  have h₃ : sym₃ v = 0 := by linear_combination (h 1 - h (-1)) / 96
  have h₄ : sym₄ v = 0 := by
    linear_combination (4*(h 1 + h (-1)) - (h 2 + h (-2))) / 1728
  rw [Fin.sum_univ_four] at hs
  have poly (z : ℂ) :
      (z-v 0)*(z-v 1)*(z-v 2)*(z-v 3) = z^3*(z+1) := by
    simp only [sym₂, sym₃, sym₄] at h₂ h₃ h₄
    linear_combination -z^3 * hs + z^2 * h₂ - z * h₃ + h₄
  have root (i : Fin 4) : v i = 0 ∨ v i = -1 := by
    have hroot : (v i)^3 * (v i + 1) = 0 := by
      rw [← poly]
      fin_cases i <;> simp
    rcases mul_eq_zero.mp hroot with h0|hm
    · exact Or.inl (by simpa using h0)
    · exact Or.inr (by linear_combination hm)
  rcases root 0 with h0|h0 <;> rcases root 1 with h1|h1 <;>
    rcases root 2 with h2|h2 <;> rcases root 3 with h3|h3 <;>
    norm_num [h0,h1,h2,h3] at hs
  · refine ⟨3, ?_⟩
    funext k; fin_cases k <;> simp [h0,h1,h2,h3]
  · refine ⟨2, ?_⟩
    funext k; fin_cases k <;> simp [h0,h1,h2,h3]
  · refine ⟨1, ?_⟩
    funext k; fin_cases k <;> simp [h0,h1,h2,h3]
  · refine ⟨0, ?_⟩
    funext k; fin_cases k <;> simp [h0,h1,h2,h3]

end PQ201

-- ==== APPEND BOUNDARY: lem_colNormal ====
namespace PQ201
namespace ColNormal

noncomputable def col (j : Fin 4) : Mat →ₗ[ℂ] Vec :=
  LinearMap.funLeft ℂ ℂ fun i => (i,j)

private theorem eval_perm (w : Mat) :
    MvPolynomial.eval w (PEqualNP.Gct.permPoly ℂ 4) = ∑ σ : Equiv.Perm (Fin 4), ∏ i, w (σ i, i) := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

theorem misses_one (L : Submodule ℂ Mat) (hL : Lev L) (j : Fin 4) :
    (1 : Vec) ∉ L.map (col j) := by
  rintro ⟨t, ht, hj⟩
  have e := hL _ (L.neg_mem ht)
  rw [eval_perm] at e
  have hzero (σ : Equiv.Perm (Fin 4)) : (∏ i, (1 + (-t) (σ i, i))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have h := congrFun hj (σ j)
    change t (σ j, j) = 1 at h
    simp [h]
  rw [Finset.sum_eq_zero (fun σ _ => hzero σ)] at e
  norm_num at e

end ColNormal

theorem colNormal (L : Submodule ℂ Mat) (hL : Lev L) (j : Fin 4) :
    ∃ u : Vec, (∑ i, u i) = 1 ∧ ∀ t ∈ L, (∑ i, u i * t (i,j)) = 0 := by
  obtain ⟨f, hf, hbot⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (ColNormal.misses_one L hL j) inferInstance
  obtain ⟨u, hu⟩ := (dotProductEquiv ℂ (Fin 4)).surjective ((f 1)⁻¹ • f)
  refine ⟨u, ?_, ?_⟩
  · have h := LinearMap.congr_fun hu (1 : Vec)
    change (∑ i, u i * 1) = (f 1)⁻¹ * f 1 at h
    simpa only [mul_one, inv_mul_cancel₀ hf] using h
  · intro t ht
    have hm : f (ColNormal.col j t) ∈ (L.map (ColNormal.col j)).map f := ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    rw [hbot] at hm
    change f (ColNormal.col j t) = 0 at hm
    have h := LinearMap.congr_fun hu (ColNormal.col j t)
    change (∑ i, u i * t (i,j)) = (f 1)⁻¹ * f (ColNormal.col j t) at h
    simpa only [hm, mul_zero] using h

end PQ201

-- ==== APPEND BOUNDARY: lem_forceAtom ====

namespace PQ201

namespace ForceAtom

theorem d_sum (j : Fin 4) : (∑ k, d j k) = 0 := by
  fin_cases j <;> simp [d, Fin.sum_univ_four] <;> norm_num

/-- `d j k = 4·[k = j] − 1`, so a `d`-weighted sum of a centred row is 4 times its `j` entry. -/
theorem d_weight (j : Fin 4) (r : Fin 4 → ℂ) (hr : (∑ k, r k) = 0) :
    (∑ k, d j k * r k) = 4 * r j := by
  rw [Fin.sum_univ_four] at hr
  fin_cases j <;> simp [d, Fin.sum_univ_four] <;> linear_combination (-1 : ℂ) * hr

/-- The column-centred atom: entry minus column sum is `3 u_i d_j(k)`. -/
theorem atom_centre (j : Fin 4) (u : Vec) (hs : (∑ i, u i) = 1) (i k : Fin 4) :
    atom j (fun i => 3 * u i - 1) (i,k) - ∑ l : Fin 4, atom j (fun i => 3 * u i - 1) (l,k)
      = 3 * u i * d j k := by
  rw [Fin.sum_univ_four] at hs
  simp only [atom, Fin.sum_univ_four]
  linear_combination (-3 * d j k) * hs

/-- `B = 12 ×` the evaluation of the normal on column `j`, for row-centred `y`. -/
theorem B_atom (j : Fin 4) (u : Vec) (hs : (∑ i, u i) = 1) (y : Mat) (hy : RC y) :
    B (atom j (fun i => 3 * u i - 1)) y = 12 * ∑ i, u i * y (i,j) := by
  unfold B
  simp only [atom_centre j u hs]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := d_weight j (fun k => y (i,k)) (hy i)
  calc (∑ k, 3 * u i * d j k * y (i,k)) = 3 * u i * ∑ k, d j k * y (i,k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = 12 * (u i * y (i,j)) := by rw [h]; ring

end ForceAtom

theorem forceAtom (L : Submodule ℂ Mat) (hR : ∀ x ∈ L, RC x)
    (j : Fin 4) (u : Vec) (hs : (∑ i, u i) = 1)
    (hu : ∀ t ∈ L, (∑ i, u i * t (i,j)) = 0) :
    let v : Vec := fun i => 3 * u i - 1
    (∑ i, v i) = -1 ∧ RC (atom j v) ∧ ∀ y ∈ L, B (atom j v) y = 0 := by
  intro v
  refine ⟨?_, ?_, ?_⟩
  · have hs' := hs
    rw [Fin.sum_univ_four] at hs'
    simp only [v, Fin.sum_univ_four]
    linear_combination 3 * hs'
  · intro i
    simp only [atom]
    rw [← Finset.mul_sum, ForceAtom.d_sum, mul_zero]
  · intro y hy
    rw [ForceAtom.B_atom j u hs y (hR y hy), hu y hy, mul_zero]

end PQ201

-- ==== APPEND BOUNDARY: lem_commonRow ====

namespace PQ201

namespace CommonRowProof

private def negUnit (i : Fin 4) : Vec := fun k => if k = i then -1 else 0

private lemma sum_negUnit (i : Fin 4) : (∑ k : Fin 4, negUnit i k) = -1 := by
  simp [negUnit]

private lemma d_eq (j c : Fin 4) : d j c = (if c = j then (4 : ℂ) else 0) - 1 := by
  unfold d
  split_ifs <;> norm_num

private lemma sum_d_mul {j₁ j₂ : Fin 4} (hj : j₁ ≠ j₂) :
    (∑ c : Fin 4, d j₁ c * d j₂ c) = -4 := by
  have hterm : ∀ c : Fin 4, d j₁ c * d j₂ c =
      -(if c = j₁ then (4 : ℂ) else 0) - (if c = j₂ then (4 : ℂ) else 0) + 1 := by
    intro c
    rw [d_eq, d_eq]
    by_cases h1 : c = j₁
    · subst h1
      simp [hj]
      ring
    · simp [h1]
      ring
  simp [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]

private lemma B_atom_negUnit {i₁ i₂ j₁ j₂ : Fin 4} (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) :
    B (atom j₁ (negUnit i₁)) (atom j₂ (negUnit i₂)) = 4 := by
  unfold B
  rw [Finset.sum_eq_single i₂]
  · have hcol : ∀ c : Fin 4,
        (∑ k : Fin 4, atom j₁ (negUnit i₁) (k, c)) = -d j₁ c := by
      intro c
      simp only [atom, ← Finset.sum_mul, sum_negUnit, neg_one_mul]
    have hinner : ∀ c : Fin 4,
        (atom j₁ (negUnit i₁) (i₂, c) - ∑ k : Fin 4, atom j₁ (negUnit i₁) (k, c)) *
          atom j₂ (negUnit i₂) (i₂, c) = -(d j₁ c * d j₂ c) := by
      intro c
      rw [hcol c]
      simp [atom, negUnit, Ne.symm hi]
    simp only [hinner, Finset.sum_neg_distrib, sum_d_mul hj]
    norm_num
  · intro r _ hri₂
    simp [atom, negUnit, hri₂]
  · intro hmem
    exact (hmem (Finset.mem_univ i₂)).elim

private lemma row_eq_sum_atoms (i : Fin 4) (w : Vec) (hw : (∑ j : Fin 4, w j) = 0) :
    (fun p : Fin 4 × Fin 4 => if p.1 = i then w p.2 else 0) =
      ∑ j : Fin 4, (-w j / 4) • atom j (negUnit i) := by
  funext ⟨r, c⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, atom, negUnit]
  by_cases hr : r = i
  · subst hr
    simp only [↓reduceIte]
    have hterm : ∀ j : Fin 4,
        (-w j / 4) * (-1 * d j c) = (if j = c then w j else 0) - w j / 4 := by
      intro j
      rw [d_eq]
      by_cases hcj : c = j
      · subst hcj
        simp
        ring
      · have hjc : j ≠ c := Ne.symm hcj
        simp [hcj, hjc]
        ring
    simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      ← Finset.sum_div, hw, zero_div, sub_zero]
  · simp [hr]

end CommonRowProof

theorem commonRow (L : Submodule ℂ Mat) (hB : ∀ x ∈ L, ∀ y ∈ L, B x y = 0)
    (h : ∀ j : Fin 4, ∃ i : Fin 4, atom j (fun k => if k = i then -1 else 0) ∈ L) :
    ∃ i : Fin 4, ∀ w : Vec, (∑ j, w j) = 0 →
      (fun p : Fin 4 × Fin 4 => if p.1 = i then w p.2 else 0) ∈ L := by
  obtain ⟨i₀, hi₀⟩ := h 0
  refine ⟨i₀, ?_⟩
  have hall : ∀ j : Fin 4, atom j (CommonRowProof.negUnit i₀) ∈ L := by
    intro j
    by_cases hj : j = 0
    · subst hj
      exact hi₀
    · obtain ⟨i_j, hi_j⟩ := h j
      have heq : i₀ = i_j := by
        by_contra hne
        have hzero : B (atom 0 (CommonRowProof.negUnit i₀))
            (atom j (CommonRowProof.negUnit i_j)) = 0 := hB _ hi₀ _ hi_j
        have hfour : B (atom 0 (CommonRowProof.negUnit i₀))
            (atom j (CommonRowProof.negUnit i_j)) = 4 :=
          CommonRowProof.B_atom_negUnit hne (Ne.symm hj)
        rw [hfour] at hzero
        norm_num at hzero
      subst heq
      exact hi_j
  intro w hw
  rw [CommonRowProof.row_eq_sum_atoms i₀ w hw]
  exact Submodule.sum_mem L (fun j _ => Submodule.smul_mem L _ (hall j))

end PQ201

namespace PQ201

theorem polar (L : Submodule ℂ Mat) (hL : Lev L) (hR : ∀ x ∈ L, RC x) :
    ∀ x ∈ L, ∀ y ∈ L, B x y = 0 := by
  obtain ⟨ht, hb⟩ := PQ183Core.levelPolar L hL
  intro x hx y hy
  have h := hb x hx y hy
  have hr : ∀ i : Fin 4, (∑ j, x (i,j)) = 0 := hR x hx
  simpa only [PQ183Core.dot, hr, sub_zero, ht x hx, add_zero, B] using h

theorem bound (L : Submodule ℂ Mat) (hL : Lev L) (hR : ∀ x ∈ L, RC x) :
    Module.finrank ℂ L ≤ 5 := by
  by_contra! hd
  have h6 := Nat.succ_le_of_lt hd
  have hB := polar L hL hR
  obtain ⟨i, hi⟩ := commonRow L hB (by
    intro j
    obtain ⟨u, hu, ht⟩ := colNormal L hL j
    let v : Vec := fun i => 3 * u i - 1
    obtain ⟨hs, hrc, hv⟩ := forceAtom L hR j u hu ht
    have ha : atom j v ∈ L := lagr L hR hB h6 _ hrc hv
    obtain ⟨i, hi⟩ := atom_single L hL j v hs ha
    exact ⟨i, hi ▸ ha⟩)
  exact (Nat.not_lt_of_ge (PQFullRow.fullRowBound' i L hL hi)) hd

end PQ201


theorem PEqualNP.Outside.L_gct_217 : ∀ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), (∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) → Module.finrank ℂ L ≤ 5 := by
  intro L hm
  have hR : ∀ x ∈ L, PQ201.RC x := fun x hx => (hm x hx).1
  apply PQ201.bound L _ hR
  intro x hx
  apply Gap183.level_of_sums
  have hr : ∀ i : Fin 4, (∑ j, x (i,j)) = 0 := hR x hx
  exact ⟨by simp [hr], (hm x hx).2⟩
