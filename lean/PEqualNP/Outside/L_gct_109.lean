import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private noncomputable def ω : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private lemma ω_sq_add : ω ^ 2 + ω + 1 = 0 := by
  apply Complex.ext
  · simp only [ω, sq, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.zero_re]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  · simp only [ω, sq, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.zero_im]
    ring

private lemma ω_cube : ω ^ 3 = 1 := by
  linear_combination (ω - 1) * ω_sq_add

private lemma prod_cyc (A B C : ℂ) :
    (A + B + C) * (A * ω ^ 2 + B * ω + C) * (A * ω + B * ω ^ 2 + C) =
      A ^ 3 + B ^ 3 + C ^ 3 - 3 * A * B * C := by
  have h1 : (A * ω ^ 2 + B * ω + C) * (A * ω + B * ω ^ 2 + C) =
      A ^ 2 + B ^ 2 + C ^ 2 - A * B - A * C - B * C := by
    linear_combination
      (A ^ 2 * (ω - 1) + B ^ 2 * (ω - 1) + A * B * (ω ^ 2 - ω + 1) + A * C + B * C) * ω_sq_add
  rw [mul_assoc, h1]
  ring

private lemma sum_cube_cyc (a b : ℂ) :
    (1 + a + b) ^ 3 + (1 + a * ω ^ 2 + b * ω) ^ 3 + (1 + a * ω + b * ω ^ 2) ^ 3 =
      3 + 3 * a ^ 3 + 3 * b ^ 3 + 18 * a * b := by
  have hω2 : ω ^ 2 = -ω - 1 := by linear_combination ω_sq_add
  have hω3 : ω ^ 3 = 1 := ω_cube
  have hω4 : ω ^ 4 = ω := by linear_combination ω * hω3
  have hω5 : ω ^ 5 = -ω - 1 := by linear_combination ω ^ 2 * hω3 + hω2
  have hω6 : ω ^ 6 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
  ring_nf
  simp only [hω6, hω5, hω4, hω3, hω2]
  ring

private noncomputable def psi (x y z w : ℂ) : Fin 3 × Fin 3 → ℂ
  | (0, 0) => x + y + z + w
  | (0, 1) => x * ω + y * ω ^ 2 + z * ω ^ 2 + w * ω
  | (0, 2) => x * ω ^ 2 + y * ω + z * ω + w * ω ^ 2
  | (1, 0) => x * ω + y * ω ^ 2 + z * ω + w * ω ^ 2
  | (1, 1) => x * ω ^ 2 + y * ω + z + w
  | (1, 2) => x + y + z * ω ^ 2 + w * ω
  | (2, 0) => x * ω ^ 2 + y * ω + z * ω ^ 2 + w * ω
  | (2, 1) => x + y + z * ω + w * ω ^ 2
  | (2, 2) => x * ω + y * ω ^ 2 + z + w

private noncomputable def dftX (t : Fin 3 × Fin 3 → ℂ) : ℂ :=
  (1 / 9 : ℂ) * (
    t (0, 0) + t (0, 1) * ω ^ 2 + t (0, 2) * ω +
    t (1, 0) * ω ^ 2 + t (1, 1) * ω + t (1, 2) +
    t (2, 0) * ω + t (2, 1) + t (2, 2) * ω ^ 2)

private noncomputable def dftY (t : Fin 3 × Fin 3 → ℂ) : ℂ :=
  (1 / 9 : ℂ) * (
    t (0, 0) + t (0, 1) * ω + t (0, 2) * ω ^ 2 +
    t (1, 0) * ω + t (1, 1) * ω ^ 2 + t (1, 2) +
    t (2, 0) * ω ^ 2 + t (2, 1) + t (2, 2) * ω)

private noncomputable def dftZ (t : Fin 3 × Fin 3 → ℂ) : ℂ :=
  (1 / 9 : ℂ) * (
    t (0, 0) + t (0, 1) * ω + t (0, 2) * ω ^ 2 +
    t (1, 0) * ω ^ 2 + t (1, 1) + t (1, 2) * ω +
    t (2, 0) * ω + t (2, 1) * ω ^ 2 + t (2, 2))

private noncomputable def dftW (t : Fin 3 × Fin 3 → ℂ) : ℂ :=
  (1 / 9 : ℂ) * (
    t (0, 0) + t (0, 1) * ω ^ 2 + t (0, 2) * ω +
    t (1, 0) * ω + t (1, 1) + t (1, 2) * ω ^ 2 +
    t (2, 0) * ω ^ 2 + t (2, 1) * ω + t (2, 2))

private noncomputable def dft (t : Fin 3 × Fin 3 → ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (dftX t, dftY t, dftZ t, dftW t)

private lemma dft_linear (a b : ℂ) (t₁ t₂ : Fin 3 × Fin 3 → ℂ) :
    dft (a • t₁ + b • t₂) = a • dft t₁ + b • dft t₂ := by
  simp only [dft, dftX, dftY, dftZ, dftW, Prod.smul_mk, Prod.mk_add_mk, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Prod.ext (by ring) (Prod.ext (by ring) (Prod.ext (by ring) (by ring)))

private lemma psi_zero : psi 0 0 0 0 = 0 := by
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [psi]

private lemma dft_reconstruct (t : Fin 3 × Fin 3 → ℂ)
    (hrow : ∀ i, ∑ j, t (i, j) = 0)
    (hcol : ∀ j, ∑ i, t (i, j) = 0) :
    psi (dftX t) (dftY t) (dftZ t) (dftW t) = t := by
  have hr0 : t (0, 0) + t (0, 1) + t (0, 2) = 0 := by simpa [Fin.sum_univ_three] using hrow 0
  have hr1 : t (1, 0) + t (1, 1) + t (1, 2) = 0 := by simpa [Fin.sum_univ_three] using hrow 1
  have hr2 : t (2, 0) + t (2, 1) + t (2, 2) = 0 := by simpa [Fin.sum_univ_three] using hrow 2
  have hc0 : t (0, 0) + t (1, 0) + t (2, 0) = 0 := by simpa [Fin.sum_univ_three] using hcol 0
  have hc1 : t (0, 1) + t (1, 1) + t (2, 1) = 0 := by simpa [Fin.sum_univ_three] using hcol 1
  have ht02 : t (0, 2) = -t (0, 0) - t (0, 1) := by linear_combination hr0
  have ht12 : t (1, 2) = -t (1, 0) - t (1, 1) := by linear_combination hr1
  have ht20 : t (2, 0) = -t (0, 0) - t (1, 0) := by linear_combination hc0
  have ht21 : t (2, 1) = -t (0, 1) - t (1, 1) := by linear_combination hc1
  have ht22 : t (2, 2) = t (0, 0) + t (0, 1) + t (1, 0) + t (1, 1) := by
    linear_combination hr2 - hc0 - hc1
  have hω2 : ω ^ 2 = -ω - 1 := by linear_combination ω_sq_add
  have hω3 : ω ^ 3 = 1 := ω_cube
  have hω4 : ω ^ 4 = ω := by linear_combination ω * hω3
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, psi, dftX, dftY, dftZ, dftW,
      ht02, ht12, ht20, ht21, ht22] <;>
    (ring_nf; simp only [hω4, hω3, hω2]; ring)

private lemma eval_permPoly_three (f : Fin 3 × Fin 3 → ℂ) :
    MvPolynomial.eval f (PEqualNP.Gct.permPoly ℂ 3) =
      f (0, 0) * f (1, 1) * f (2, 2) +
      f (0, 1) * f (1, 2) * f (2, 0) +
      f (0, 2) * f (1, 0) * f (2, 1) +
      f (0, 0) * f (1, 2) * f (2, 1) +
      f (0, 1) * f (1, 0) * f (2, 2) +
      f (0, 2) * f (1, 1) * f (2, 0) := by
  unfold PEqualNP.Gct.permPoly Matrix.permanent
  rw [map_sum]
  simp only [map_prod, Matrix.mvPolynomialX_apply, MvPolynomial.eval_X]
  let σ0 : Equiv.Perm (Fin 3) := 1
  let σ1 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  let σ2 : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1
  let σ3 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let σ4 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let σ5 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 3))) = {σ0, σ1, σ2, σ3, σ4, σ5} := by
    decide
  rw [huniv]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  have h01_2 : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
  have h12_0 : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  have h02_1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide
  simp [Fin.prod_univ_three, σ0, σ1, σ2, σ3, σ4, σ5, h01_2, h12_0, h02_1]
  ring

private lemma perm_one_add_psi (x y z w : ℂ) :
    MvPolynomial.eval (fun p => 1 + psi x y z w p) (PEqualNP.Gct.permPoly ℂ 3) =
      6 + 9 * (x * y + z * w) + 6 * (x ^ 3 + y ^ 3 + z ^ 3 + w ^ 3) := by
  rw [eval_permPoly_three]
  dsimp only [psi]
  have hω3 := ω_cube
  have hω4 : ω ^ 4 = ω := by linear_combination ω * hω3
  have he0 :
      (1 + (x + y + z + w)) *
      (1 + (x * ω ^ 2 + y * ω + z + w)) *
      (1 + (x * ω + y * ω ^ 2 + z + w)) =
      x ^ 3 + y ^ 3 + (1 + z + w) ^ 3 - 3 * x * y * (1 + z + w) := by
    convert prod_cyc x y (1 + z + w) using 1; ring
  have he1 :
      (1 + (x * ω + y * ω ^ 2 + z * ω ^ 2 + w * ω)) *
      (1 + (x + y + z * ω ^ 2 + w * ω)) *
      (1 + (x * ω ^ 2 + y * ω + z * ω ^ 2 + w * ω)) =
      x ^ 3 + y ^ 3 + (1 + z * ω ^ 2 + w * ω) ^ 3 - 3 * x * y * (1 + z * ω ^ 2 + w * ω) := by
    have h := prod_cyc (x * ω) (y * ω ^ 2) (1 + z * ω ^ 2 + w * ω)
    have hL :
        (1 + (x * ω + y * ω ^ 2 + z * ω ^ 2 + w * ω)) *
        (1 + (x + y + z * ω ^ 2 + w * ω)) *
        (1 + (x * ω ^ 2 + y * ω + z * ω ^ 2 + w * ω)) =
        (x * ω + y * ω ^ 2 + (1 + z * ω ^ 2 + w * ω)) *
        (x * ω * ω ^ 2 + y * ω ^ 2 * ω + (1 + z * ω ^ 2 + w * ω)) *
        (x * ω * ω + y * ω ^ 2 * ω ^ 2 + (1 + z * ω ^ 2 + w * ω)) := by
      have ha : x * ω * ω ^ 2 = x := by linear_combination x * hω3
      have hb : y * ω ^ 2 * ω = y := by linear_combination y * hω3
      have hc : y * ω ^ 2 * ω ^ 2 = y * ω := by linear_combination y * hω4
      rw [ha, hb, hc]; ring
    have hR : (x * ω) ^ 3 + (y * ω ^ 2) ^ 3 + (1 + z * ω ^ 2 + w * ω) ^ 3 -
        3 * (x * ω) * (y * ω ^ 2) * (1 + z * ω ^ 2 + w * ω) =
        x ^ 3 + y ^ 3 + (1 + z * ω ^ 2 + w * ω) ^ 3 - 3 * x * y * (1 + z * ω ^ 2 + w * ω) := by
      have h6 : ω ^ 6 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
      linear_combination x ^ 3 * hω3 + y ^ 3 * h6 - 3 * x * y * (1 + z * ω ^ 2 + w * ω) * hω3
    rw [hL, h, hR]
  have he2 :
      (1 + (x * ω ^ 2 + y * ω + z * ω + w * ω ^ 2)) *
      (1 + (x * ω + y * ω ^ 2 + z * ω + w * ω ^ 2)) *
      (1 + (x + y + z * ω + w * ω ^ 2)) =
      x ^ 3 + y ^ 3 + (1 + z * ω + w * ω ^ 2) ^ 3 - 3 * x * y * (1 + z * ω + w * ω ^ 2) := by
    have h := prod_cyc (x * ω ^ 2) (y * ω) (1 + z * ω + w * ω ^ 2)
    have hL :
        (1 + (x * ω ^ 2 + y * ω + z * ω + w * ω ^ 2)) *
        (1 + (x * ω + y * ω ^ 2 + z * ω + w * ω ^ 2)) *
        (1 + (x + y + z * ω + w * ω ^ 2)) =
        (x * ω ^ 2 + y * ω + (1 + z * ω + w * ω ^ 2)) *
        (x * ω ^ 2 * ω ^ 2 + y * ω * ω + (1 + z * ω + w * ω ^ 2)) *
        (x * ω ^ 2 * ω + y * ω * ω ^ 2 + (1 + z * ω + w * ω ^ 2)) := by
      have ha : x * ω ^ 2 * ω ^ 2 = x * ω := by linear_combination x * hω4
      have hb : x * ω ^ 2 * ω = x := by linear_combination x * hω3
      have hc : y * ω * ω ^ 2 = y := by linear_combination y * hω3
      rw [ha, hb, hc]; ring
    have hR : (x * ω ^ 2) ^ 3 + (y * ω) ^ 3 + (1 + z * ω + w * ω ^ 2) ^ 3 -
        3 * (x * ω ^ 2) * (y * ω) * (1 + z * ω + w * ω ^ 2) =
        x ^ 3 + y ^ 3 + (1 + z * ω + w * ω ^ 2) ^ 3 - 3 * x * y * (1 + z * ω + w * ω ^ 2) := by
      have h6 : ω ^ 6 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
      linear_combination x ^ 3 * h6 + y ^ 3 * hω3 - 3 * x * y * (1 + z * ω + w * ω ^ 2) * hω3
    rw [hL, h, hR]
  have ho0 :
      (1 + (x + y + z + w)) *
      (1 + (x + y + z * ω ^ 2 + w * ω)) *
      (1 + (x + y + z * ω + w * ω ^ 2)) =
      z ^ 3 + w ^ 3 + (1 + x + y) ^ 3 - 3 * z * w * (1 + x + y) := by
    convert prod_cyc z w (1 + x + y) using 1; ring
  have ho1 :
      (1 + (x * ω + y * ω ^ 2 + z * ω ^ 2 + w * ω)) *
      (1 + (x * ω + y * ω ^ 2 + z * ω + w * ω ^ 2)) *
      (1 + (x * ω + y * ω ^ 2 + z + w)) =
      z ^ 3 + w ^ 3 + (1 + x * ω + y * ω ^ 2) ^ 3 - 3 * z * w * (1 + x * ω + y * ω ^ 2) := by
    have h := prod_cyc (z * ω ^ 2) (w * ω) (1 + x * ω + y * ω ^ 2)
    have hL :
        (1 + (x * ω + y * ω ^ 2 + z * ω ^ 2 + w * ω)) *
        (1 + (x * ω + y * ω ^ 2 + z * ω + w * ω ^ 2)) *
        (1 + (x * ω + y * ω ^ 2 + z + w)) =
        (z * ω ^ 2 + w * ω + (1 + x * ω + y * ω ^ 2)) *
        (z * ω ^ 2 * ω ^ 2 + w * ω * ω + (1 + x * ω + y * ω ^ 2)) *
        (z * ω ^ 2 * ω + w * ω * ω ^ 2 + (1 + x * ω + y * ω ^ 2)) := by
      have ha : z * ω ^ 2 * ω ^ 2 = z * ω := by linear_combination z * hω4
      have hb : z * ω ^ 2 * ω = z := by linear_combination z * hω3
      have hc : w * ω * ω ^ 2 = w := by linear_combination w * hω3
      rw [ha, hb, hc]; ring
    have hR : (z * ω ^ 2) ^ 3 + (w * ω) ^ 3 + (1 + x * ω + y * ω ^ 2) ^ 3 -
        3 * (z * ω ^ 2) * (w * ω) * (1 + x * ω + y * ω ^ 2) =
        z ^ 3 + w ^ 3 + (1 + x * ω + y * ω ^ 2) ^ 3 - 3 * z * w * (1 + x * ω + y * ω ^ 2) := by
      have h6 : ω ^ 6 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
      linear_combination z ^ 3 * h6 + w ^ 3 * hω3 - 3 * z * w * (1 + x * ω + y * ω ^ 2) * hω3
    rw [hL, h, hR]
  have ho2 :
      (1 + (x * ω ^ 2 + y * ω + z * ω + w * ω ^ 2)) *
      (1 + (x * ω ^ 2 + y * ω + z + w)) *
      (1 + (x * ω ^ 2 + y * ω + z * ω ^ 2 + w * ω)) =
      z ^ 3 + w ^ 3 + (1 + x * ω ^ 2 + y * ω) ^ 3 - 3 * z * w * (1 + x * ω ^ 2 + y * ω) := by
    have h := prod_cyc (z * ω) (w * ω ^ 2) (1 + x * ω ^ 2 + y * ω)
    have hL :
        (1 + (x * ω ^ 2 + y * ω + z * ω + w * ω ^ 2)) *
        (1 + (x * ω ^ 2 + y * ω + z + w)) *
        (1 + (x * ω ^ 2 + y * ω + z * ω ^ 2 + w * ω)) =
        (z * ω + w * ω ^ 2 + (1 + x * ω ^ 2 + y * ω)) *
        (z * ω * ω ^ 2 + w * ω ^ 2 * ω + (1 + x * ω ^ 2 + y * ω)) *
        (z * ω * ω + w * ω ^ 2 * ω ^ 2 + (1 + x * ω ^ 2 + y * ω)) := by
      have ha : z * ω * ω ^ 2 = z := by linear_combination z * hω3
      have hb : w * ω ^ 2 * ω = w := by linear_combination w * hω3
      have hc : w * ω ^ 2 * ω ^ 2 = w * ω := by linear_combination w * hω4
      rw [ha, hb, hc]; ring
    have hR : (z * ω) ^ 3 + (w * ω ^ 2) ^ 3 + (1 + x * ω ^ 2 + y * ω) ^ 3 -
        3 * (z * ω) * (w * ω ^ 2) * (1 + x * ω ^ 2 + y * ω) =
        z ^ 3 + w ^ 3 + (1 + x * ω ^ 2 + y * ω) ^ 3 - 3 * z * w * (1 + x * ω ^ 2 + y * ω) := by
      have h6 : ω ^ 6 = 1 := by linear_combination (ω ^ 3 + 1) * hω3
      linear_combination z ^ 3 * hω3 + w ^ 3 * h6 - 3 * z * w * (1 + x * ω ^ 2 + y * ω) * hω3
    rw [hL, h, hR]
  rw [he0, he1, he2, ho0, ho1, ho2]
  have hcz := sum_cube_cyc z w
  have hcx := sum_cube_cyc x y
  linear_combination hcz + hcx - 3 * (x * y * (z + w) + z * w * (x + y)) * ω_sq_add

private lemma cube_eq_zero {z : ℂ} (h : z ^ 3 = 0) : z = 0 := by
  have h1 : z * (z * z) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with hz | h2
  · exact hz
  · rcases mul_eq_zero.mp h2 with hz | hz <;> exact hz

private lemma no_two_indep (v₁ v₂ : ℂ × ℂ × ℂ × ℂ)
    (hind : ∀ a b : ℂ, a • v₁ + b • v₂ = 0 → a = 0 ∧ b = 0)
    (hQ : ∀ a b : ℂ,
      let v := a • v₁ + b • v₂
      v.1 * v.2.1 + v.2.2.1 * v.2.2.2 = 0)
    (hC : ∀ a b : ℂ,
      let v := a • v₁ + b • v₂
      v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = 0) : False := by
  rcases v₁ with ⟨x₁, y₁, z₁, w₁⟩
  rcases v₂ with ⟨x₂, y₂, z₂, w₂⟩
  have hQ' : ∀ a b : ℂ,
      (a * x₁ + b * x₂) * (a * y₁ + b * y₂) + (a * z₁ + b * z₂) * (a * w₁ + b * w₂) = 0 := by
    intro a b; simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hQ a b
  have hC' : ∀ a b : ℂ,
      (a * x₁ + b * x₂) ^ 3 + (a * y₁ + b * y₂) ^ 3 +
      (a * z₁ + b * z₂) ^ 3 + (a * w₁ + b * w₂) ^ 3 = 0 := by
    intro a b; simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using hC a b
  by_cases hD : x₁ * z₂ - z₁ * x₂ ≠ 0
  · set D := x₁ * z₂ - z₁ * x₂
    have hQ1 := hQ' (z₂ / D) (-z₁ / D)
    have hQ2 := hQ' (-x₂ / D) (x₁ / D)
    have hQ12 := hQ' ((z₂ - x₂) / D) ((x₁ - z₁) / D)
    have hC1 := hC' (z₂ / D) (-z₁ / D)
    have hC2 := hC' (-x₂ / D) (x₁ / D)
    set y1' := (z₂ / D) * y₁ + (-z₁ / D) * y₂
    set w1' := (z₂ / D) * w₁ + (-z₁ / D) * w₂
    set y2' := (-x₂ / D) * y₁ + (x₁ / D) * y₂
    set w2' := (-x₂ / D) * w₁ + (x₁ / D) * w₂
    have hx1' : (z₂ / D) * x₁ + (-z₁ / D) * x₂ = 1 := by
      calc (z₂ / D) * x₁ + (-z₁ / D) * x₂ = D / D := by dsimp only [D]; ring
        _ = 1 := div_self hD
    have hz1' : (z₂ / D) * z₁ + (-z₁ / D) * z₂ = 0 := by ring
    have hx2' : (-x₂ / D) * x₁ + (x₁ / D) * x₂ = 0 := by ring
    have hz2' : (-x₂ / D) * z₁ + (x₁ / D) * z₂ = 1 := by
      calc (-x₂ / D) * z₁ + (x₁ / D) * z₂ = D / D := by dsimp only [D]; ring
        _ = 1 := div_self hD
    have hx12 : ((z₂ - x₂) / D) * x₁ + ((x₁ - z₁) / D) * x₂ = 1 := by
      calc ((z₂ - x₂) / D) * x₁ + ((x₁ - z₁) / D) * x₂ = D / D := by dsimp only [D]; ring
        _ = 1 := div_self hD
    have hz12 : ((z₂ - x₂) / D) * z₁ + ((x₁ - z₁) / D) * z₂ = 1 := by
      calc ((z₂ - x₂) / D) * z₁ + ((x₁ - z₁) / D) * z₂ = D / D := by dsimp only [D]; ring
        _ = 1 := div_self hD
    have hy12 : ((z₂ - x₂) / D) * y₁ + ((x₁ - z₁) / D) * y₂ = y1' + y2' := by
      dsimp only [y1', y2']; ring
    have hw12 : ((z₂ - x₂) / D) * w₁ + ((x₁ - z₁) / D) * w₂ = w1' + w2' := by
      dsimp only [w1', w2']; ring
    have hy1_zero : y1' = 0 := by
      rw [hx1', hz1'] at hQ1; linear_combination hQ1
    have hw2_zero : w2' = 0 := by
      rw [hx2', hz2'] at hQ2; linear_combination hQ2
    have hrel : y2' + w1' = 0 := by
      rw [hx12, hz12, hy12, hw12, hy1_zero, hw2_zero] at hQ12
      linear_combination hQ12
    have hc1' : 1 + w1' ^ 3 = 0 := by
      rw [hx1', hz1'] at hC1
      change 1 ^ 3 + y1' ^ 3 + 0 ^ 3 + w1' ^ 3 = 0 at hC1
      rw [hy1_zero] at hC1
      linear_combination hC1
    have hc2' : y2' ^ 3 + 1 = 0 := by
      rw [hx2', hz2'] at hC2
      change 0 ^ 3 + y2' ^ 3 + 1 ^ 3 + w2' ^ 3 = 0 at hC2
      rw [hw2_zero] at hC2
      linear_combination hC2
    have htwo : (2 : ℂ) = 0 := by
      linear_combination hc1' + hc2' - (y2' ^ 2 - y2' * w1' + w1' ^ 2) * hrel
    norm_num at htwo
  · push Not at hD
    have hstep : ∀ (u₁ u₂ : ℂ × ℂ × ℂ × ℂ),
        (∀ a b : ℂ, a • u₁ + b • u₂ = 0 → a = 0 ∧ b = 0) →
        (∀ a b : ℂ, let v := a • u₁ + b • u₂; v.1 * v.2.1 + v.2.2.1 * v.2.2.2 = 0) →
        (∀ a b : ℂ, let v := a • u₁ + b • u₂;
          v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = 0) →
        u₂.1 = 0 → u₂.2.2.1 = 0 → False := by
      rintro ⟨a1, b1, c1, d1⟩ ⟨a2, b2, c2, d2⟩ hu_ind huQ huC ha2 hc2
      dsimp only at ha2 hc2
      subst ha2; subst hc2
      have huQ' : ∀ a b : ℂ,
          (a * a1) * (a * b1 + b * b2) + (a * c1) * (a * d1 + b * d2) = 0 := by
        intro a b; simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using huQ a b
      have huC' : ∀ a b : ℂ,
          (a * a1) ^ 3 + (a * b1 + b * b2) ^ 3 + (a * c1) ^ 3 + (a * d1 + b * d2) ^ 3 = 0 := by
        intro a b; simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using huC a b
      have hu2_ne : b2 ≠ 0 ∨ d2 ≠ 0 := by
        by_contra h
        push Not at h
        have h0 : (0 : ℂ) • (a1, b1, c1, d1) + (1 : ℂ) • ((0 : ℂ), b2, (0 : ℂ), d2) = 0 := by
          simp [h.1, h.2]
        exact one_ne_zero (hu_ind 0 1 h0).2
      have hC_u2 : b2 ^ 3 + d2 ^ 3 = 0 := by
        have h := huC' 0 1; linear_combination h
      have hb2_ne : b2 ≠ 0 := by
        intro hb2
        rw [hb2] at hC_u2
        have hd2 : d2 = 0 := cube_eq_zero (by linear_combination hC_u2)
        rcases hu2_ne with h | h <;> exact h (by assumption)
      by_cases hac : a1 = 0 ∧ c1 = 0
      · rcases hac with ⟨ha1, hc1⟩
        subst ha1; subst hc1
        have hdet : b1 * d2 - d1 * b2 ≠ 0 := by
          intro hdet
          have h0 : b2 • ((0 : ℂ), b1, (0 : ℂ), d1) + (-b1) • ((0 : ℂ), b2, (0 : ℂ), d2) = 0 := by
            simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk_eq_zero,
              mul_zero, add_zero, true_and]
            exact ⟨by ring, by linear_combination -hdet⟩
          exact hb2_ne (hu_ind b2 (-b1) h0).1
        set E := b1 * d2 - d1 * b2
        have h := huC' (d2 / E) (-d1 / E)
        have h1 : (d2 / E) * b1 + (-d1 / E) * b2 = 1 := by
          calc (d2 / E) * b1 + (-d1 / E) * b2 = E / E := by dsimp only [E]; ring
            _ = 1 := div_self hdet
        have h2 : (d2 / E) * d1 + (-d1 / E) * d2 = 0 := by ring
        rw [h1, h2] at h
        have : (1 : ℂ) = 0 := by linear_combination h
        norm_num at this
      · have hQ1 : a1 * b1 + c1 * d1 = 0 := by
          have h := huQ' 1 0; linear_combination h
        have hQ12 : a1 * b2 + c1 * d2 = 0 := by
          have h := huQ' 1 1; linear_combination h - hQ1
        have hdet : b1 * d2 - d1 * b2 = 0 := by
          have ha : a1 * (b1 * d2 - d1 * b2) = 0 := by linear_combination d2 * hQ1 - d1 * hQ12
          have hc : c1 * (b1 * d2 - d1 * b2) = 0 := by linear_combination -b2 * hQ1 + b1 * hQ12
          by_cases ha1 : a1 = 0
          · have hc1 : c1 ≠ 0 := fun h => hac ⟨ha1, h⟩
            exact (mul_eq_zero.mp hc).resolve_left hc1
          · exact (mul_eq_zero.mp ha).resolve_left ha1
        have hC_u1' := huC' 1 (-b1 / b2)
        have hb0 : 1 * b1 + (-b1 / b2) * b2 = 0 := by field_simp [hb2_ne]; ring
        have hd0 : 1 * d1 + (-b1 / b2) * d2 = 0 := by
          field_simp [hb2_ne]; linear_combination -hdet
        rw [hb0, hd0] at hC_u1'
        have hC1 : a1 ^ 3 + c1 ^ 3 = 0 := by linear_combination hC_u1'
        have hprod : 2 * a1 ^ 3 * b2 ^ 3 = 0 := by
          linear_combination
            (a1 ^ 2 * b2 ^ 2 - a1 * b2 * c1 * d2 + c1 ^ 2 * d2 ^ 2) * hQ12
            + a1 ^ 3 * hC_u2 - d2 ^ 3 * hC1
        have ha1 : a1 = 0 := by
          rcases mul_eq_zero.mp hprod with h | h
          · rcases mul_eq_zero.mp h with h2 | ha3
            · norm_num at h2
            · exact cube_eq_zero ha3
          · exact absurd (cube_eq_zero h) hb2_ne
        rw [ha1] at hC1
        have hc1 : c1 = 0 := cube_eq_zero (by linear_combination hC1)
        exact hac ⟨ha1, hc1⟩
    by_cases hx1 : x₁ = 0 ∧ z₁ = 0
    · exact hstep (x₂, y₂, z₂, w₂) (x₁, y₁, z₁, w₁)
        (fun a b h => by
          have := hind b a (by simpa [add_comm] using h)
          exact ⟨this.2, this.1⟩)
        (fun a b => by simpa [add_comm] using hQ b a)
        (fun a b => by simpa [add_comm] using hC b a)
        hx1.1 hx1.2
    · by_cases hx10 : x₁ ≠ 0
      · let u₂ := (-x₂) • (x₁, y₁, z₁, w₁) + x₁ • (x₂, y₂, z₂, w₂)
        have hlin : ∀ a b : ℂ, a • (x₁, y₁, z₁, w₁) + b • u₂ =
            (a - b * x₂) • (x₁, y₁, z₁, w₁) + (b * x₁) • (x₂, y₂, z₂, w₂) := by
          intro a b; dsimp only [u₂]; simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
          refine Prod.ext (by ring) (Prod.ext (by ring) (Prod.ext (by ring) (by ring)))
        exact hstep (x₁, y₁, z₁, w₁) u₂
          (fun a b h => by
            rw [hlin] at h
            have ⟨h1, h2⟩ := hind _ _ h
            have hb : b = 0 := (mul_eq_zero.mp h2).resolve_right hx10
            exact ⟨by rw [hb] at h1; linear_combination h1, hb⟩)
          (fun a b => by rw [hlin]; exact hQ _ _)
          (fun a b => by rw [hlin]; exact hC _ _)
          (by dsimp only [u₂]; simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; ring)
          (by dsimp only [u₂]; simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; linear_combination hD)
      · push Not at hx10
        have hz10 : z₁ ≠ 0 := fun hz => hx1 ⟨hx10, hz⟩
        let u₂ := (-z₂) • (x₁, y₁, z₁, w₁) + z₁ • (x₂, y₂, z₂, w₂)
        have hlin : ∀ a b : ℂ, a • (x₁, y₁, z₁, w₁) + b • u₂ =
            (a - b * z₂) • (x₁, y₁, z₁, w₁) + (b * z₁) • (x₂, y₂, z₂, w₂) := by
          intro a b; dsimp only [u₂]; simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
          refine Prod.ext (by ring) (Prod.ext (by ring) (Prod.ext (by ring) (by ring)))
        exact hstep (x₁, y₁, z₁, w₁) u₂
          (fun a b h => by
            rw [hlin] at h
            have ⟨h1, h2⟩ := hind _ _ h
            have hb : b = 0 := (mul_eq_zero.mp h2).resolve_right hz10
            exact ⟨by rw [hb] at h1; linear_combination h1, hb⟩)
          (fun a b => by rw [hlin]; exact hQ _ _)
          (fun a b => by rw [hlin]; exact hC _ _)
          (by dsimp only [u₂]; simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; linear_combination -hD)
          (by dsimp only [u₂]; simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; ring)

theorem L_gct_109 : ∀ K : Submodule ℂ (Fin 3 × Fin 3 → ℂ), (∀ t ∈ K, (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0)) → (∀ t ∈ K, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 3) = 6) → Module.finrank ℂ K ≤ 1 := by
  intro K hcent hperm
  by_contra hdim
  have hgt : 1 < Module.finrank ℂ K := Nat.lt_of_not_ge hdim
  let b := Module.finBasis ℂ K
  let i0 : Fin (Module.finrank ℂ K) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank ℂ K) := ⟨1, hgt⟩
  let k₁ : K := b i0
  let k₂ : K := b i1
  have hk_ind : ∀ a c : ℂ, a • (k₁ : Fin 3 × Fin 3 → ℂ) + c • (k₂ : Fin 3 × Fin 3 → ℂ) = 0 →
      a = 0 ∧ c = 0 := by
    intro a c h
    have hK : a • k₁ + c • k₂ = 0 := Subtype.ext h
    have h0 := congrArg (fun x => b.repr x i0) hK
    have h1 := congrArg (fun x => b.repr x i1) hK
    have hne : i0 ≠ i1 := by
      intro heq
      have hval := congrArg Fin.val heq
      exact Nat.zero_ne_one hval
    simp only [k₁, k₂, map_add, map_smul, map_zero, Module.Basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.zero_apply, Finsupp.single_apply, smul_eq_mul,
      ↓reduceIte, hne, hne.symm, mul_one, mul_zero, add_zero, zero_add] at h0 h1
    exact ⟨h0, h1⟩
  have hdft_QC : ∀ t ∈ K,
      let v := dft t
      (v.1 * v.2.1 + v.2.2.1 * v.2.2.2 = 0) ∧
      (v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = 0) := by
    intro t ht
    have hrec : psi (dftX t) (dftY t) (dftZ t) (dftW t) = t :=
      dft_reconstruct t (hcent t ht).1 (hcent t ht).2
    have hpos : 6 + 9 * (dftX t * dftY t + dftZ t * dftW t) +
        6 * (dftX t ^ 3 + dftY t ^ 3 + dftZ t ^ 3 + dftW t ^ 3) = 6 := by
      rw [← perm_one_add_psi, hrec]
      exact hperm t ht
    have hneg_mem : (-t) ∈ K := K.neg_mem ht
    have hneg_dft : dft (-t) = (-1 : ℂ) • dft t := by
      have h := dft_linear (-1 : ℂ) 0 t 0
      simpa using h
    have hneg_rec : psi (-dftX t) (-dftY t) (-dftZ t) (-dftW t) = -t := by
      have h := dft_reconstruct (-t) (hcent (-t) hneg_mem).1 (hcent (-t) hneg_mem).2
      have hx : dftX (-t) = -dftX t := by
        simpa [dft, Prod.smul_mk] using congrArg Prod.fst hneg_dft
      have hy : dftY (-t) = -dftY t := by
        simpa [dft, Prod.smul_mk] using congrArg (fun p => p.2.1) hneg_dft
      have hz : dftZ (-t) = -dftZ t := by
        simpa [dft, Prod.smul_mk] using congrArg (fun p => p.2.2.1) hneg_dft
      have hw : dftW (-t) = -dftW t := by
        simpa [dft, Prod.smul_mk] using congrArg (fun p => p.2.2.2) hneg_dft
      rw [← hx, ← hy, ← hz, ← hw]
      exact h
    have hneg : 6 + 9 * ((-dftX t) * (-dftY t) + (-dftZ t) * (-dftW t)) +
        6 * ((-dftX t) ^ 3 + (-dftY t) ^ 3 + (-dftZ t) ^ 3 + (-dftW t) ^ 3) = 6 := by
      rw [← perm_one_add_psi, hneg_rec]
      exact hperm (-t) hneg_mem
    dsimp only [dft]
    exact ⟨by linear_combination (1 / 18 : ℂ) * (hpos + hneg),
           by linear_combination (1 / 12 : ℂ) * (hpos - hneg)⟩
  refine no_two_indep (dft k₁.1) (dft k₂.1) ?_ ?_ ?_
  · intro a c h
    rw [← dft_linear] at h
    have hmem : a • k₁.1 + c • k₂.1 ∈ K := K.add_mem (K.smul_mem a k₁.2) (K.smul_mem c k₂.2)
    have hrec := dft_reconstruct (a • k₁.1 + c • k₂.1) (hcent _ hmem).1 (hcent _ hmem).2
    have hx : dftX (a • k₁.1 + c • k₂.1) = 0 := congrArg Prod.fst h
    have hy : dftY (a • k₁.1 + c • k₂.1) = 0 := congrArg (fun p => p.2.1) h
    have hz : dftZ (a • k₁.1 + c • k₂.1) = 0 := congrArg (fun p => p.2.2.1) h
    have hw : dftW (a • k₁.1 + c • k₂.1) = 0 := congrArg (fun p => p.2.2.2) h
    rw [hx, hy, hz, hw, psi_zero] at hrec
    exact hk_ind a c hrec.symm
  · intro a c
    have hmem : a • k₁.1 + c • k₂.1 ∈ K := K.add_mem (K.smul_mem a k₁.2) (K.smul_mem c k₂.2)
    have h := (hdft_QC _ hmem).1
    rw [dft_linear] at h
    exact h
  · intro a c
    have hmem : a • k₁.1 + c • k₂.1 ∈ K := K.add_mem (K.smul_mem a k₁.2) (K.smul_mem c k₂.2)
    have h := (hdft_QC _ hmem).2
    rw [dft_linear] at h
    exact h

end PEqualNP.Outside
