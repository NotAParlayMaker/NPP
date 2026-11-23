import Mathlib
import PEqualNP.Defs

open Finset

private abbrev Mat3 := Fin 3 × Fin 3 → ℂ

private lemma permanent_three (A : Matrix (Fin 3) (Fin 3) ℂ) :
    A.permanent =
      A 0 0 * A 1 1 * A 2 2 + A 0 0 * A 1 2 * A 2 1 + A 0 1 * A 1 0 * A 2 2 +
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

private def fourierMatrix (w a b c d : ℂ) : Mat3 := fun p =>
  ![![a + b + c + d, (a + c) * w + (b + d) * (-w - 1), (a + c) * (-w - 1) + (b + d) * w],
    ![(a + b) * w + (c + d) * (-w - 1), a * (-w - 1) + d * w + b + c,
      a + d + b * (-w - 1) + c * w],
    ![(a + b) * (-w - 1) + (c + d) * w, a + d + b * w + c * (-w - 1),
      a * w + d * (-w - 1) + b + c]] p.1 p.2

/-- On the four Fourier modes with nonzero row and column frequency, the quadratic part
pairs opposite modes and the cubic part is a sum of cubes. -/
private lemma eval_fourier (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (a b c d : ℂ) :
    MvPolynomial.eval (fun p => 1 + fourierMatrix w a b c d p) (PEqualNP.Gct.permPoly ℂ 3) =
      6 + 9 * (a * d + b * c) + 6 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) := by
  have heval (z : Mat3) :
      MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ 3) =
        (Matrix.of fun i j => z (i, j)).permanent := by
    simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]
  rw [heval, permanent_three]
  simp only [Matrix.of_apply, fourierMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination
    (-6*a^3 + 6*a^2*d + 3*a^2 + 6*a*d^2 - 6*a*d - 6*d^3 + 3*d^2
      - 6*b^3 + 6*b^2*c + 3*b^2 + 6*b*c^2 - 6*b*c - 6*c^3 + 3*c^2) * hw

private def modePlus (w : ℂ) : Fin 3 → ℂ := ![1, w, -w - 1]
private def modeMinus (w : ℂ) : Fin 3 → ℂ := ![1, -w - 1, w]

private lemma fourier_modes (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (a b c d : ℂ) (i j : Fin 3) :
    fourierMatrix w a b c d (i, j) =
      (a * modePlus w i + c * modeMinus w i) * modePlus w j +
      (b * modePlus w i + d * modeMinus w i) * modeMinus w j := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, fourierMatrix, modePlus, modeMinus,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  · ring
  · ring
  · ring
  · ring
  · linear_combination (-a + b + c - d) * hw
  · linear_combination (a - b - c + d) * hw
  · ring
  · linear_combination (a - b - c + d) * hw
  · linear_combination (-a + b + c - d) * hw

private noncomputable def coefficient (r : Fin 3 → ℂ) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun u := (∑ i, r i * u i) / 3
  map_add' u v := by
    simp only [Pi.add_apply, mul_add, sum_add_distrib, add_div]
  map_smul' c u := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm (r _) c,
      ← mul_sum, mul_div_assoc]

private lemma coefficient_apply (r u : Fin 3 → ℂ) :
    coefficient r u = (∑ i, r i * u i) / 3 := rfl

private lemma reconstruct_vector (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (u : Fin 3 → ℂ) (hu : ∑ i, u i = 0) (i : Fin 3) :
    u i = coefficient (modeMinus w) u * modePlus w i +
      coefficient (modePlus w) u * modeMinus w i := by
  simp only [Fin.sum_univ_three] at hu
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, coefficient_apply, Fin.sum_univ_three,
      modePlus, modeMinus, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  · linear_combination hu / 3
  · linear_combination hu / 3 + (2 * (u 1 - u 2) / 3) * hw
  · linear_combination hu / 3 + (2 * (u 2 - u 1) / 3) * hw

private noncomputable def coordinate (r s : Fin 3 → ℂ) : Mat3 →ₗ[ℂ] ℂ where
  toFun t := coefficient r (fun i => coefficient s fun j => t (i, j))
  map_add' t u := by
    rw [← map_add]
    apply congrArg (coefficient r)
    funext i
    exact map_add (coefficient s) (fun j => t (i, j)) (fun j => u (i, j))
  map_smul' k t := by
    rw [← map_smul]
    apply congrArg (coefficient r)
    funext i
    exact map_smul (coefficient s) k (fun j => t (i, j))

private lemma coordinate_apply (r s : Fin 3 → ℂ) (t : Mat3) :
    coordinate r s t = coefficient r (fun i => coefficient s fun j => t (i, j)) := rfl

private lemma reconstruct_matrix (w : ℂ) (hw : w ^ 2 + w + 1 = 0) (t : Mat3)
    (hrow : ∀ i, ∑ j, t (i, j) = 0) (hcol : ∀ j, ∑ i, t (i, j) = 0) :
    fourierMatrix w (coordinate (modeMinus w) (modeMinus w) t)
      (coordinate (modeMinus w) (modePlus w) t) (coordinate (modePlus w) (modeMinus w) t)
      (coordinate (modePlus w) (modePlus w) t) = t := by
  have center (s : Fin 3 → ℂ) : ∑ i, coefficient s (fun j => t (i, j)) = 0 := by
    simp only [coefficient_apply, ← sum_div]
    rw [sum_comm]
    simp [← mul_sum, hcol]
  funext ⟨i, j⟩
  rw [fourier_modes w hw]
  simp only [coordinate_apply]
  calc
    _ = coefficient (modeMinus w) (fun j => t (i, j)) * modePlus w j +
        coefficient (modePlus w) (fun j => t (i, j)) * modeMinus w j := by
      rw [← reconstruct_vector w hw _ (center (modeMinus w)) i,
        ← reconstruct_vector w hw _ (center (modePlus w)) i]
    _ = t (i, j) := (reconstruct_vector w hw _ (hrow i) j).symm

/-- The mixed quadratic equation for two points with coordinates `(a,b,c,d)` and
`(0,y,0,z)` is incompatible with both cubic equations when `a` and `y` are nonzero. -/
private lemma incompatible (a b c d y z : ℂ) (ha : a ≠ 0) (hy : y ≠ 0)
    (hquad : a * d + b * c = 0) (hcub : a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = 0)
    (hmix : a * z + c * y = 0) (hcub' : y ^ 3 + z ^ 3 = 0) : False := by
  have h₁ : (a ^ 3 - c ^ 3) * y ^ 3 = 0 := by
    linear_combination a ^ 3 * hcub' -
      ((a * z) ^ 2 - (a * z) * (c * y) + (c * y) ^ 2) * hmix
  have hdiff : a ^ 3 - c ^ 3 = 0 := (mul_eq_zero.mp h₁).resolve_right (pow_ne_zero 3 hy)
  have h₂ : a ^ 3 * (a ^ 3 + c ^ 3) = 0 := by
    linear_combination a ^ 3 * hcub -
      ((a * d) ^ 2 - (a * d) * (b * c) + (b * c) ^ 2) * hquad - b ^ 3 * hdiff
  have hsum : a ^ 3 + c ^ 3 = 0 := (mul_eq_zero.mp h₂).resolve_left (pow_ne_zero 3 ha)
  exact pow_ne_zero 3 ha (by linear_combination (hdiff + hsum) / 2)

section
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (a b c d : V →ₗ[ℂ] ℂ)

private lemma zero_of_first_zero
    (hquad : ∀ x, a x * d x + b x * c x = 0)
    (hcub : ∀ x, a x ^ 3 + b x ^ 3 + c x ^ 3 + d x ^ 3 = 0)
    {u v : V} (hu : a u ≠ 0) (hv : a v = 0) :
    b v = 0 ∧ c v = 0 ∧ d v = 0 := by
  have hmul : b v * c v = 0 := by simpa [hv] using hquad v
  have hlin : a u * d v + b u * c v + c u * b v = 0 := by
    have hadd := hquad (u + v)
    simp only [map_add] at hadd
    linear_combination hadd - hquad u - hquad v - d u * hv
  have hb : b v = 0 := by
    by_contra hn
    have hc : c v = 0 := (mul_eq_zero.mp hmul).resolve_left hn
    exact incompatible (a u) (b u) (c u) (d u) (b v) (d v) hu hn
      (hquad u) (hcub u) (by simpa [hc] using hlin) (by simpa [hv, hc] using hcub v)
  have hc : c v = 0 := by
    by_contra hn
    exact incompatible (a u) (c u) (b u) (d u) (c v) (d v) hu hn
      (by linear_combination hquad u) (by linear_combination hcub u)
      (by simpa [hb] using hlin) (by simpa [hv, hb] using hcub v)
  have hd : a u * d v = 0 := by simpa [hb, hc] using hlin
  exact ⟨hb, hc, (mul_eq_zero.mp hd).resolve_left hu⟩

private lemma dimension_from_first
    (hquad : ∀ x, a x * d x + b x * c x = 0)
    (hcub : ∀ x, a x ^ 3 + b x ^ 3 + c x ^ 3 + d x ^ 3 = 0)
    (hzero : ∀ x, a x = 0 → b x = 0 → c x = 0 → d x = 0 → x = 0)
    {u : V} (hu : a u ≠ 0) : Module.finrank ℂ V ≤ 1 := by
  refine finrank_le_one u fun v => ⟨a v / a u, ?_⟩
  let z := v - (a v / a u) • u
  have hz : a z = 0 := by
    simp only [z, map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hu, sub_self]
  obtain ⟨hb, hc, hd⟩ := zero_of_first_zero a b c d hquad hcub hu hz
  exact (sub_eq_zero.mp (hzero z hz hb hc hd)).symm

private lemma dimension_of_quadric_and_cubic
    (hquad : ∀ x, a x * d x + b x * c x = 0)
    (hcub : ∀ x, a x ^ 3 + b x ^ 3 + c x ^ 3 + d x ^ 3 = 0)
    (hzero : ∀ x, a x = 0 → b x = 0 → c x = 0 → d x = 0 → x = 0) :
    Module.finrank ℂ V ≤ 1 := by
  by_cases ha : ∃ u, a u ≠ 0
  · obtain ⟨u, hu⟩ := ha
    exact dimension_from_first a b c d hquad hcub hzero hu
  by_cases hb : ∃ u, b u ≠ 0
  · obtain ⟨u, hu⟩ := hb
    exact dimension_from_first b a d c (fun x => by linear_combination hquad x)
      (fun x => by linear_combination hcub x) (fun x hb ha hd hc => hzero x ha hb hc hd) hu
  by_cases hc : ∃ u, c u ≠ 0
  · obtain ⟨u, hu⟩ := hc
    exact dimension_from_first c d a b (fun x => by linear_combination hquad x)
      (fun x => by linear_combination hcub x) (fun x hc hd ha hb => hzero x ha hb hc hd) hu
  by_cases hd : ∃ u, d u ≠ 0
  · obtain ⟨u, hu⟩ := hd
    exact dimension_from_first d c b a (fun x => by linear_combination hquad x)
      (fun x => by linear_combination hcub x) (fun x hd hc hb ha => hzero x ha hb hc hd) hu
  push Not at ha hb hc hd
  exact finrank_le_one 0 (fun x => ⟨0, by simp [hzero x (ha x) (hb x) (hc x) (hd x)]⟩)

end

theorem PEqualNP.Outside.L_gct_109 : ∀ K : Submodule ℂ (Fin 3 × Fin 3 → ℂ), (∀ t ∈ K, (∀ i, ∑ j, t (i, j) = 0) ∧ (∀ j, ∑ i, t (i, j) = 0)) → (∀ t ∈ K, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ 3) = 6) → Module.finrank ℂ K ≤ 1 := by
  intro K hcenter hperm
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w ^ 2 + w + 1 = 0 := by
    let w := Complex.exp (2 * Real.pi * Complex.I / 3)
    have hprim : IsPrimitiveRoot w 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
    have hroot := hprim.isRoot_cyclotomic (by decide)
    refine ⟨w, ?_⟩
    simpa [Polynomial.cyclotomic_three, Polynomial.IsRoot.def] using hroot
  let a := (coordinate (modeMinus w) (modeMinus w)).comp K.subtype
  let b := (coordinate (modeMinus w) (modePlus w)).comp K.subtype
  let c := (coordinate (modePlus w) (modeMinus w)).comp K.subtype
  let d := (coordinate (modePlus w) (modePlus w)).comp K.subtype
  have hrec (x : K) : fourierMatrix w (a x) (b x) (c x) (d x) = x.val :=
    reconstruct_matrix w hw x.val (hcenter x.val x.property).1 (hcenter x.val x.property).2
  have hval (x : K) : 6 + 9 * (a x * d x + b x * c x) +
        6 * (a x ^ 3 + b x ^ 3 + c x ^ 3 + d x ^ 3) = 6 := by
    rw [← eval_fourier w hw, hrec x]
    exact hperm x.val x.property
  have hparts (x : K) : a x * d x + b x * c x = 0 ∧
      a x ^ 3 + b x ^ 3 + c x ^ 3 + d x ^ 3 = 0 := by
    have hp := hval x
    have hn := hval (-x)
    simp only [map_neg] at hn
    constructor
    · linear_combination (hp + hn) / 18
    · linear_combination (hp - hn) / 12
  refine dimension_of_quadric_and_cubic a b c d (fun x => (hparts x).1)
    (fun x => (hparts x).2) ?_
  intro x ha hb hc hd
  apply Subtype.ext
  rw [← hrec x, ha, hb, hc, hd]
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> simp [fourierMatrix]
