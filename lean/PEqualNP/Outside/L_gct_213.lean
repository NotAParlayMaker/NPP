import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_213_aux

lemma finrank_le_of_inj {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (k : ℕ)
    (g : V →ₗ[ℂ] (Fin k → ℂ)) (h : ∀ v ∈ S, g v = 0 → v = 0) : Module.finrank ℂ S ≤ k := by
  have hinj : Function.Injective (g.domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (h v.1 v.2 hv)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

lemma single {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (g : V →ₗ[ℂ] ℂ)
    (hg : ∀ t ∈ S, g t = 0 → t = 0) : Module.finrank ℂ S ≤ 1 := by
  refine finrank_le_of_inj S 1 (LinearMap.pi (fun _ : Fin 1 => g)) ?_
  intro t ht h
  have h0 := congrFun h 0
  exact hg t ht (by simpa using h0)

lemma zero_dim {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V)
    (h : ∀ v ∈ S, v = 0) : Module.finrank ℂ S = 0 := by
  rw [(Submodule.eq_bot_iff S).mpr h]
  simp

lemma dim_le_one4 {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V)
    (f1 f2 f3 f4 : V →ₗ[ℂ] ℂ)
    (hsep : ∀ t ∈ S, f1 t = 0 → f2 t = 0 → f3 t = 0 → f4 t = 0 → t = 0)
    (hmin : ∀ t ∈ S, ∀ s ∈ S, f1 t * f2 s = f2 t * f1 s ∧ f1 t * f3 s = f3 t * f1 s ∧
      f1 t * f4 s = f4 t * f1 s ∧ f2 t * f3 s = f3 t * f2 s ∧ f2 t * f4 s = f4 t * f2 s ∧
      f3 t * f4 s = f4 t * f3 s) : Module.finrank ℂ S ≤ 1 := by
  by_cases h1 : ∃ t0 ∈ S, f1 t0 ≠ 0
  · obtain ⟨t0, ht0, hne⟩ := h1
    refine single S f1 ?_
    intro t ht hz
    obtain ⟨m12, m13, m14, -, -, -⟩ := hmin t0 ht0 t ht
    rw [hz, mul_zero] at m12 m13 m14
    exact hsep t ht hz ((mul_eq_zero.mp m12).resolve_left hne)
      ((mul_eq_zero.mp m13).resolve_left hne) ((mul_eq_zero.mp m14).resolve_left hne)
  · push Not at h1
    by_cases h2 : ∃ t0 ∈ S, f2 t0 ≠ 0
    · obtain ⟨t0, ht0, hne⟩ := h2
      refine single S f2 ?_
      intro t ht hz
      obtain ⟨-, -, -, m23, m24, -⟩ := hmin t0 ht0 t ht
      rw [hz, mul_zero] at m23 m24
      exact hsep t ht (h1 t ht) hz ((mul_eq_zero.mp m23).resolve_left hne)
        ((mul_eq_zero.mp m24).resolve_left hne)
    · push Not at h2
      by_cases h3 : ∃ t0 ∈ S, f3 t0 ≠ 0
      · obtain ⟨t0, ht0, hne⟩ := h3
        refine single S f3 ?_
        intro t ht hz
        obtain ⟨-, -, -, -, -, m34⟩ := hmin t0 ht0 t ht
        rw [hz, mul_zero] at m34
        exact hsep t ht (h1 t ht) (h2 t ht) hz ((mul_eq_zero.mp m34).resolve_left hne)
      · push Not at h3
        refine single S f4 ?_
        intro t ht hz
        exact hsep t ht (h1 t ht) (h2 t ht) (h3 t ht) hz

lemma sumA (t : Fin 2 × Fin 3 → ℂ) :
    (∑ j, (t (0, j) + t (1, j))) =
      t (0, 0) + t (1, 0) + (t (0, 1) + t (1, 1)) + (t (0, 2) + t (1, 2)) :=
  Fin.sum_univ_three _

lemma sumR0 (t : Fin 2 × Fin 3 → ℂ) : (∑ j, t (0, j)) = t (0, 0) + t (0, 1) + t (0, 2) :=
  Fin.sum_univ_three _

lemma sumR1 (t : Fin 2 × Fin 3 → ℂ) : (∑ j, t (1, j)) = t (1, 0) + t (1, 1) + t (1, 2) :=
  Fin.sum_univ_three _

lemma sumP2 (t : Fin 2 × Fin 3 → ℂ) :
    (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) =
      t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2)
        + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) := by
  simp [Fin.sum_univ_three]
  ring

lemma sumAx (t : Fin 2 × Fin 3 → ℂ) (x : Fin 3 → ℂ) :
    (∑ j, (t (0, j) + t (1, j) + x j)) =
      t (0, 0) + t (1, 0) + x 0 + (t (0, 1) + t (1, 1) + x 1) + (t (0, 2) + t (1, 2) + x 2) :=
  Fin.sum_univ_three _

lemma sumG2 (t : Fin 2 × Fin 3 → ℂ) (x : Fin 3 → ℂ) :
    (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l) + t (0, j) * x l + t (1, j) * x l) =
      (t (0, 0) * t (1, 1) + t (0, 0) * x 1 + t (1, 0) * x 1)
      + (t (0, 0) * t (1, 2) + t (0, 0) * x 2 + t (1, 0) * x 2)
      + (t (0, 1) * t (1, 0) + t (0, 1) * x 0 + t (1, 1) * x 0)
      + (t (0, 1) * t (1, 2) + t (0, 1) * x 2 + t (1, 1) * x 2)
      + (t (0, 2) * t (1, 0) + t (0, 2) * x 0 + t (1, 2) * x 0)
      + (t (0, 2) * t (1, 1) + t (0, 2) * x 1 + t (1, 2) * x 1) := by
  simp [Fin.sum_univ_three]
  ring

lemma sumG3 (t : Fin 2 × Fin 3 → ℂ) (x : Fin 3 → ℂ) :
    (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * x m) =
      t (0, 0) * t (1, 1) * x 2 + t (0, 0) * t (1, 2) * x 1 + t (0, 1) * t (1, 0) * x 2
        + t (0, 1) * t (1, 2) * x 0 + t (0, 2) * t (1, 0) * x 1 + t (0, 2) * t (1, 1) * x 0 := by
  simp [Fin.sum_univ_three]
  ring

noncomputable def Bf : LinearMap.BilinForm ℂ (Fin 2 × Fin 3 → ℂ) :=
  LinearMap.mk₂ ℂ (fun t s =>
      (t (0, 0) + t (0, 1) + t (0, 2)) * (s (1, 0) + s (1, 1) + s (1, 2))
      + (s (0, 0) + s (0, 1) + s (0, 2)) * (t (1, 0) + t (1, 1) + t (1, 2))
      - (t (0, 0) * s (1, 0) + t (0, 1) * s (1, 1) + t (0, 2) * s (1, 2))
      - (s (0, 0) * t (1, 0) + s (0, 1) * t (1, 1) + s (0, 2) * t (1, 2)))
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [Pi.add_apply]; ring)
    (by intros; simp only [Pi.smul_apply, smul_eq_mul]; ring)

lemma Bf_apply (t s : Fin 2 × Fin 3 → ℂ) : Bf t s =
      (t (0, 0) + t (0, 1) + t (0, 2)) * (s (1, 0) + s (1, 1) + s (1, 2))
      + (s (0, 0) + s (0, 1) + s (0, 2)) * (t (1, 0) + t (1, 1) + t (1, 2))
      - (t (0, 0) * s (1, 0) + t (0, 1) * s (1, 1) + t (0, 2) * s (1, 2))
      - (s (0, 0) * t (1, 0) + s (0, 1) * t (1, 1) + s (0, 2) * t (1, 2)) := rfl

lemma Bf_symm (t s : Fin 2 × Fin 3 → ℂ) : Bf t s = Bf s t := by
  rw [Bf_apply, Bf_apply]
  ring

lemma Bf_sep (t : Fin 2 × Fin 3 → ℂ) (h : ∀ s, Bf t s = 0) : t = 0 := by
  have e (p : Fin 2 × Fin 3) := h (Pi.single p 1)
  have e00 := e (0, 0)
  have e01 := e (0, 1)
  have e02 := e (0, 2)
  have e10 := e (1, 0)
  have e11 := e (1, 1)
  have e12 := e (1, 2)
  simp [Bf_apply] at e00 e01 e02 e10 e11 e12
  have z00 : t (0, 0) = 0 := by linear_combination (e10 + e11 + e12) / 2 - e10
  have z01 : t (0, 1) = 0 := by linear_combination (e10 + e11 + e12) / 2 - e11
  have z02 : t (0, 2) = 0 := by linear_combination (e10 + e11 + e12) / 2 - e12
  have z10 : t (1, 0) = 0 := by linear_combination (e00 + e01 + e02) / 2 - e00
  have z11 : t (1, 1) = 0 := by linear_combination (e00 + e01 + e02) / 2 - e01
  have z12 : t (1, 2) = 0 := by linear_combination (e00 + e01 + e02) / 2 - e02
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · exact z00
  · exact z01
  · exact z02
  · exact z10
  · exact z11
  · exact z12

lemma Bf_nondeg : Bf.Nondegenerate :=
  ⟨Bf_sep, fun t h => Bf_sep t (fun s => by rw [Bf_symm]; exact h s)⟩

noncomputable def phiSum : (Fin 2 × Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun t := t (0, 0) + t (1, 0) + (t (0, 1) + t (1, 1)) + (t (0, 2) + t (1, 2))
  map_add' := by
    intros
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intros
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma dimA (L : Submodule ℂ (Fin 2 × Fin 3 → ℂ))
    (hE1 : ∀ t ∈ L, t (0, 0) + t (1, 0) + (t (0, 1) + t (1, 1)) + (t (0, 2) + t (1, 2)) = 0)
    (hE2 : ∀ t ∈ L, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0)
      + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) = 0) :
    Module.finrank ℂ L ≤ 2 := by
  have hpol : ∀ t ∈ L, ∀ s ∈ L, Bf t s = 0 := by
    intro t ht s hs
    have e1 := hE2 t ht
    have e2 := hE2 s hs
    have e3 := hE2 (t + s) (L.add_mem ht hs)
    simp only [Pi.add_apply] at e3
    rw [Bf_apply]
    linear_combination e3 - e1 - e2
  have hle : L ≤ Bf.orthogonal L ⊓ LinearMap.ker phiSum := by
    intro t ht
    refine ⟨?_, ?_⟩
    · intro s hs
      exact hpol s hs t ht
    · exact hE1 t ht
  have hlt : Bf.orthogonal L ⊓ LinearMap.ker phiSum < Bf.orthogonal L := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hw : (fun _ => 1 : Fin 2 × Fin 3 → ℂ) ∈ Bf.orthogonal L := by
      intro s hs
      have := hE1 s hs
      show Bf s (fun _ => 1) = 0
      rw [Bf_apply]
      linear_combination 2 * this
    rw [← heq] at hw
    have hk : (1 : ℂ) + 1 + (1 + 1) + (1 + 1) = 0 := hw.2
    norm_num at hk
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  have h3 := LinearMap.BilinForm.finrank_orthogonal Bf_nondeg L
  have h4 : Module.finrank ℂ (Fin 2 × Fin 3 → ℂ) = 6 := by
    simp
  omega

lemma core_01 (a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 : ℂ) (h1 : -2*a0*b0 - a0*b1 - a1*b0 - 2*a1*b1 = 0) (h2 : -2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h3 : -2*a0*b0 - a0*b1 - 2*a0*d0 - a0*d1 - a1*b0 - 2*a1*b1 - a1*d0 - 2*a1*d1 - 2*b0*c0 - b0*c1 - b1*c0 - 2*b1*c1 - 2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h4 : -2*a0*b0 - a0*b1 - 2*a0*x0 - a0*x1 - a1*b0 - 2*a1*b1 - a1*x0 - 2*a1*x1 - 2*b0*x0 - b0*x1 - b1*x0 - 2*b1*x1 = 0) (h5 : -2*c0*d0 - c0*d1 - 2*c0*x0 - c0*x1 - c1*d0 - 2*c1*d1 - c1*x0 - 2*c1*x1 - 2*d0*x0 - d0*x1 - d1*x0 - 2*d1*x1 = 0) (h6 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 = 0) (h7 : -2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0) (h8 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a0*d0*x1 - 2*a0*d1*x0 - 2*a0*d1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 - 2*a1*d0*x0 - 2*a1*d0*x1 - 2*a1*d1*x0 - 2*b0*c0*x1 - 2*b0*c1*x0 - 2*b0*c1*x1 - 2*b1*c0*x0 - 2*b1*c0*x1 - 2*b1*c1*x0 - 2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0)
    (hx : x0 ≠ 0 ∨ x1 ≠ 0) : a0 * c1 = a1 * c0 := by
  have key : (a0 * c1 - a1 * c0) ^ 2 = 0 := by
    rcases hx with hx | hx
    · have e : x0 * (a0 * c1 - a1 * c0) ^ 2 = 0 := by
        linear_combination (a0*c0*c1/3 + a0*c0*x0/3 - 2*a0*c0*x1/3 + 2*a0*c1^2/3 - 2*a0*c1*x1/3 - a1*c0^2/3 - 2*a1*c0*c1/3 - 2*a1*c0*x1/3 + 2*a1*c1*x0/3 + c0^2*x0/3 - 2*c0^2*x1/3 - 4*c0*c1*x1/3 + 2*c1^2*x0/3) * h1 + (-a0^2*c1/3 + a0^2*x0/3 - 2*a0^2*x1/3 + a0*a1*c0/3 - 2*a0*a1*c1/3 - 4*a0*a1*x1/3 + a0*c0*x0/3 - 2*a0*c0*x1/3 - 2*a0*c1*x1/3 + 2*a1^2*c0/3 + 2*a1^2*x0/3 - 2*a1*c0*x1/3 + 2*a1*c1*x0/3) * h2 + (-a0*c0*x0/3 + 2*a0*c0*x1/3 + 2*a0*c1*x1/3 + 2*a1*c0*x1/3 - 2*a1*c1*x0/3) * h3 + (-a0*c0*c1/3 - 2*a0*c1^2/3 + a1*c0^2/3 + 2*a1*c0*c1/3) * h4 + (a0^2*c1/3 - a0*a1*c0/3 + 2*a0*a1*c1/3 - 2*a1^2*c0/3) * h5 + (-a0*c0/2 - c0^2/2) * h6 + (-a0^2/2 - a0*c0/2) * h7 + (a0*c0/2) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
    · have e : x1 * (a0 * c1 - a1 * c0) ^ 2 = 0 := by
        linear_combination (-2*a0*c0*c1/3 + 7*a0*c0*x1/6 - a0*c1^2/3 - a0*c1*x0/6 + a0*c1*x1/2 + 2*a1*c0^2/3 + a1*c0*c1/3 - a1*c0*x0/6 + a1*c0*x1/2 - a1*c1*x0/6 + a1*c1*x1/3 + 7*c0^2*x1/6 - c0*c1*x0/3 + c0*c1*x1 - c1^2*x0/6 + c1^2*x1/3) * h1 + (2*a0^2*c1/3 + 7*a0^2*x1/6 - 2*a0*a1*c0/3 + a0*a1*c1/3 - a0*a1*x0/3 + a0*a1*x1 + 7*a0*c0*x1/6 - a0*c1*x0/6 + a0*c1*x1/2 - a1^2*c0/3 - a1^2*x0/6 + a1^2*x1/3 - a1*c0*x0/6 + a1*c0*x1/2 - a1*c1*x0/6 + a1*c1*x1/3) * h2 + (-7*a0*c0*x1/6 + a0*c1*x0/6 - a0*c1*x1/2 + a1*c0*x0/6 - a1*c0*x1/2 + a1*c1*x0/6 - a1*c1*x1/3) * h3 + (2*a0*c0*c1/3 + a0*c1^2/3 - 2*a1*c0^2/3 - a1*c0*c1/3) * h4 + (-2*a0^2*c1/3 + 2*a0*a1*c0/3 - a0*a1*c1/3 + a1^2*c0/3) * h5 + (a0*c0/2 + a0*c1/4 + a1*c0/4 + c0^2/2 + c0*c1/2) * h6 + (a0^2/2 + a0*a1/2 + a0*c0/2 + a0*c1/4 + a1*c0/4) * h7 + (-a0*c0/2 - a0*c1/4 - a1*c0/4) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
  have key2 := pow_eq_zero_iff (two_ne_zero) |>.mp key
  linear_combination key2

lemma core_02 (a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 : ℂ) (h1 : -2*a0*b0 - a0*b1 - a1*b0 - 2*a1*b1 = 0) (h2 : -2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h3 : -2*a0*b0 - a0*b1 - 2*a0*d0 - a0*d1 - a1*b0 - 2*a1*b1 - a1*d0 - 2*a1*d1 - 2*b0*c0 - b0*c1 - b1*c0 - 2*b1*c1 - 2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h4 : -2*a0*b0 - a0*b1 - 2*a0*x0 - a0*x1 - a1*b0 - 2*a1*b1 - a1*x0 - 2*a1*x1 - 2*b0*x0 - b0*x1 - b1*x0 - 2*b1*x1 = 0) (h5 : -2*c0*d0 - c0*d1 - 2*c0*x0 - c0*x1 - c1*d0 - 2*c1*d1 - c1*x0 - 2*c1*x1 - 2*d0*x0 - d0*x1 - d1*x0 - 2*d1*x1 = 0) (h6 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 = 0) (h7 : -2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0) (h8 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a0*d0*x1 - 2*a0*d1*x0 - 2*a0*d1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 - 2*a1*d0*x0 - 2*a1*d0*x1 - 2*a1*d1*x0 - 2*b0*c0*x1 - 2*b0*c1*x0 - 2*b0*c1*x1 - 2*b1*c0*x0 - 2*b1*c0*x1 - 2*b1*c1*x0 - 2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0)
    (hx : x0 ≠ 0 ∨ x1 ≠ 0) : a0 * d0 = b0 * c0 := by
  have key : (a0 * d0 - b0 * c0) ^ 2 = 0 := by
    rcases hx with hx | hx
    · have e : x0 * (a0 * d0 - b0 * c0) ^ 2 = 0 := by
        linear_combination (-7*a0*c0*d0/18 - a0*c0*d1/9 - 5*a0*c0*x0/18 + a0*c0*x1/9 - a0*d0^2/18 - a0*d0*d1/9 + a0*d0*x0/6 - a0*d1*x0/9 - 2*a0*d1*x1/9 - a1*c0*d0/9 - 2*a1*c0*d1/9 + a1*c0*x0/9 + 2*a1*c0*x1/9 - a1*d0^2/9 - 2*a1*d0*d1/9 + a1*d0*x0/9 + 2*a1*d0*x1/9 + b0*c0^2/6 - b0*c0*d0/6 + b0*c0*x0/6 - b0*d0*x0/18 - b0*d0*x1/9 - b0*d1*x0/9 - 2*b0*d1*x1/9 - 5*c0^2*x0/18 + c0^2*x1/9 + c0*c1*x0/9 + 2*c0*c1*x1/9 + c0*d0*x0/3 - c0*d1*x0/9 - 2*c0*d1*x1/9 + c1*d0*x0/9 + 2*c1*d0*x1/9 - d0^2*x0/18 - d0^2*x1/9 - d0*d1*x0/9 - 2*d0*d1*x1/9) * h1 + (7*a0^2*d0/18 + a0^2*d1/9 - 5*a0^2*x0/18 + a0^2*x1/9 + a0*a1*d0/9 + 2*a0*a1*d1/9 + a0*a1*x0/9 + 2*a0*a1*x1/9 - a0*b0*c0/6 + a0*b0*d0/18 + a0*b0*d1/9 + a0*b0*x0/3 - a0*b1*x0/9 - 2*a0*b1*x1/9 - 5*a0*c0*x0/18 + a0*c0*x1/9 + a0*d0*x0/6 - a0*d1*x0/9 - 2*a0*d1*x1/9 + a1*b0*d0/9 + 2*a1*b0*d1/9 + a1*b0*x0/9 + 2*a1*b0*x1/9 + a1*c0*x0/9 + 2*a1*c0*x1/9 + a1*d0*x0/9 + 2*a1*d0*x1/9 + b0^2*c0/6 - b0^2*x0/18 - b0^2*x1/9 - b0*b1*x0/9 - 2*b0*b1*x1/9 + b0*c0*x0/6 - b0*d0*x0/18 - b0*d0*x1/9 - b0*d1*x0/9 - 2*b0*d1*x1/9) * h2 + (5*a0*c0*x0/18 - a0*c0*x1/9 - a0*d0*x0/6 + a0*d1*x0/9 + 2*a0*d1*x1/9 - a1*c0*x0/9 - 2*a1*c0*x1/9 - a1*d0*x0/9 - 2*a1*d0*x1/9 - b0*c0*x0/6 + b0*d0*x0/18 + b0*d0*x1/9 + b0*d1*x0/9 + 2*b0*d1*x1/9) * h3 + (7*a0*c0*d0/18 + a0*c0*d1/9 + a0*d0^2/18 + a0*d0*d1/9 + a1*c0*d0/9 + 2*a1*c0*d1/9 + a1*d0^2/9 + 2*a1*d0*d1/9 - b0*c0^2/6 + b0*c0*d0/6) * h4 + (-7*a0^2*d0/18 - a0^2*d1/9 - a0*a1*d0/9 - 2*a0*a1*d1/9 + a0*b0*c0/6 - a0*b0*d0/18 - a0*b0*d1/9 - a1*b0*d0/9 - 2*a1*b0*d1/9 - b0^2*c0/6) * h5 + (a0*c0/3 - a0*d0/6 - b0*c0/6 + c0^2/3 - c0*d0/3) * h6 + (a0^2/3 - a0*b0/3 + a0*c0/3 - a0*d0/6 - b0*c0/6) * h7 + (-a0*c0/3 + a0*d0/6 + b0*c0/6) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
    · have e : x1 * (a0 * d0 - b0 * c0) ^ 2 = 0 := by
        linear_combination (4*a0*c0*d0/9 + a0*c0*d1/18 - a0*c0*x0/9 - 5*a0*c0*x1/9 - a0*c1*d0 + a0*c1*x0/2 + a0*d0^2/9 + a0*d0*d1/18 - a0*d0*x0/3 + a0*d0*x1/3 - 5*a0*d1*x0/18 - 5*a0*d1*x1/9 + 14*a1*c0*d0/9 + a1*c0*d1/9 - 5*a1*c0*x0/9 - a1*c0*x1/9 + 2*a1*d0^2/9 + a1*d0*d1/9 - 11*a1*d0*x0/9 - 7*a1*d0*x1/9 - 2*a1*d1*x0/3 - 4*a1*d1*x1/3 - b0*c0^2/3 - b0*c0*c1/2 + b0*c0*x0/3 + 2*b0*c0*x1/3 - b0*c1*d0/6 + b0*c1*x0/6 + b0*d0*x0/9 + 2*b0*d0*x1/9 + b0*d1*x0/18 + b0*d1*x1/9 - c0^2*x0/9 - 5*c0^2*x1/9 - c0*c1*x0/18 - c0*c1*x1/9 + c0*d0*x1 - 5*c0*d1*x0/18 - 5*c0*d1*x1/9 - 19*c1*d0*x0/18 - 7*c1*d0*x1/9 - 2*c1*d1*x0/3 - 4*c1*d1*x1/3 + d0^2*x0/9 + 2*d0^2*x1/9 + d0*d1*x0/18 + d0*d1*x1/9) * h1 + (2*a0^2*d0/9 + 5*a0^2*d1/18 + 5*a0^2*x0/9 - 2*a0^2*x1/9 + 10*a0*a1*d0/9 + 11*a0*a1*d1/9 + 29*a0*a1*x0/18 + 11*a0*a1*x1/9 + a0*b0*c0/3 + a0*b0*c1/2 - a0*b0*d0/9 - a0*b0*d1/18 + 2*a0*b0*x0/3 + 4*a0*b0*x1/3 + a0*b1*x0/18 + a0*b1*x1/9 - a0*c0*x0/9 - 5*a0*c0*x1/9 + a0*c1*x0/2 - a0*d0*x0/3 + a0*d0*x1/3 - 5*a0*d1*x0/18 - 5*a0*d1*x1/9 + 2*a1^2*d0/3 + 4*a1^2*d1/3 + 2*a1^2*x0/3 + 4*a1^2*x1/3 - 2*a1*b0*d0/9 - a1*b0*d1/9 + 5*a1*b0*x0/18 - a1*b0*x1/9 - 5*a1*c0*x0/9 - a1*c0*x1/9 - 11*a1*d0*x0/9 - 7*a1*d0*x1/9 - 2*a1*d1*x0/3 - 4*a1*d1*x1/3 + b0^2*c1/6 + b0^2*x0/9 + 2*b0^2*x1/9 + b0*b1*x0/18 + b0*b1*x1/9 + b0*c0*x0/3 + 2*b0*c0*x1/3 + b0*c1*x0/6 + b0*d0*x0/9 + 2*b0*d0*x1/9 + b0*d1*x0/18 + b0*d1*x1/9) * h2 + (a0*c0*x0/9 + 5*a0*c0*x1/9 - a0*c1*x0/2 + a0*d0*x0/3 - a0*d0*x1/3 + 5*a0*d1*x0/18 + 5*a0*d1*x1/9 + 5*a1*c0*x0/9 + a1*c0*x1/9 + 11*a1*d0*x0/9 + 7*a1*d0*x1/9 + 2*a1*d1*x0/3 + 4*a1*d1*x1/3 - b0*c0*x0/3 - 2*b0*c0*x1/3 - b0*c1*x0/6 - b0*d0*x0/9 - 2*b0*d0*x1/9 - b0*d1*x0/18 - b0*d1*x1/9) * h3 + (-4*a0*c0*d0/9 - a0*c0*d1/18 + a0*c1*d0 - a0*d0^2/9 - a0*d0*d1/18 - 14*a1*c0*d0/9 - a1*c0*d1/9 - 2*a1*d0^2/9 - a1*d0*d1/9 + b0*c0^2/3 + b0*c0*c1/2 + b0*c1*d0/6) * h4 + (-2*a0^2*d0/9 - 5*a0^2*d1/18 - 10*a0*a1*d0/9 - 11*a0*a1*d1/9 - a0*b0*c0/3 - a0*b0*c1/2 + a0*b0*d0/9 + a0*b0*d1/18 - 2*a1^2*d0/3 - 4*a1^2*d1/3 + 2*a1*b0*d0/9 + a1*b0*d1/9 - b0^2*c1/6) * h5 + (-2*a0*c0/3 - a0*c1/2 - a1*c0/2 - a1*d0/6 - b0*c1/6 - 2*c0^2/3 - c0*c1 - c1*d0/3) * h6 + (-2*a0^2/3 - a0*a1 - 2*a0*c0/3 - a0*c1/2 - a1*b0/3 - a1*c0/2 - a1*d0/6 - b0*c1/6) * h7 + (2*a0*c0/3 + a0*c1/2 + a1*c0/2 + a1*d0/6 + b0*c1/6) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
  have key2 := pow_eq_zero_iff (two_ne_zero) |>.mp key
  linear_combination key2

lemma core_03 (a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 : ℂ) (h1 : -2*a0*b0 - a0*b1 - a1*b0 - 2*a1*b1 = 0) (h2 : -2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h3 : -2*a0*b0 - a0*b1 - 2*a0*d0 - a0*d1 - a1*b0 - 2*a1*b1 - a1*d0 - 2*a1*d1 - 2*b0*c0 - b0*c1 - b1*c0 - 2*b1*c1 - 2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h4 : -2*a0*b0 - a0*b1 - 2*a0*x0 - a0*x1 - a1*b0 - 2*a1*b1 - a1*x0 - 2*a1*x1 - 2*b0*x0 - b0*x1 - b1*x0 - 2*b1*x1 = 0) (h5 : -2*c0*d0 - c0*d1 - 2*c0*x0 - c0*x1 - c1*d0 - 2*c1*d1 - c1*x0 - 2*c1*x1 - 2*d0*x0 - d0*x1 - d1*x0 - 2*d1*x1 = 0) (h6 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 = 0) (h7 : -2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0) (h8 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a0*d0*x1 - 2*a0*d1*x0 - 2*a0*d1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 - 2*a1*d0*x0 - 2*a1*d0*x1 - 2*a1*d1*x0 - 2*b0*c0*x1 - 2*b0*c1*x0 - 2*b0*c1*x1 - 2*b1*c0*x0 - 2*b1*c0*x1 - 2*b1*c1*x0 - 2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0)
    (hx : x0 ≠ 0 ∨ x1 ≠ 0) : a0 * d1 = b1 * c0 := by
  have key : (a0 * d1 - b1 * c0) ^ 2 = 0 := by
    rcases hx with hx | hx
    · have e : x0 * (a0 * d1 - b1 * c0) ^ 2 = 0 := by
        linear_combination (-5*a0*c0*d0/9 + a0*c0*d1/18 - a0*c0*x0/3 + a0*c1*d0/3 - 5*a0*c1*x0/18 - 2*a0*c1*x1/9 + 11*a0*d0*d1/18 - a0*d0*x0/3 - a0*d0*x1/3 + 8*a0*d1^2/9 - 11*a0*d1*x0/18 - 5*a0*d1*x1/9 - 7*a1*c0*d0/9 + a1*c0*d1/9 - a1*c0*x1/3 - 2*a1*c1*x0/9 - 4*a1*c1*x1/9 + 5*a1*d0*d1/9 + a1*d0*x0/9 - a1*d0*x1/9 + 4*a1*d1^2/9 + 2*b0*c0^2/3 + b0*c0*c1/2 + b0*c0*d0/3 - b0*c0*x0/3 - b0*c0*x1/3 + b0*c1*d0/6 - b0*c1*x0/6 + b0*d1*x0/6 + b0*d1*x1/3 - 2*b1*c0*d1/3 - b1*c0*x0/3 - 2*b1*c0*x1/3 + 4*b1*d0*x0/9 + 2*b1*d0*x1/9 + 8*b1*d1*x0/9 + 4*b1*d1*x1/9 - c0^2*x0/3 - 5*c0*c1*x0/18 - 5*c0*c1*x1/9 - 2*c0*d0*x0/3 - c0*d0*x1 - 11*c0*d1*x0/18 - 11*c0*d1*x1/9 - 2*c1^2*x0/9 - 4*c1^2*x1/9 - c1*d0*x0/18 - c1*d0*x1/9 + 2*d0^2*x0/9 + d0^2*x1/9 + 7*d0*d1*x0/6 + d0*d1*x1 + 10*d1^2*x0/9 + 8*d1^2*x1/9) * h1 + (a0^2*d0/3 - a0^2*d1/6 - 5*a0^2*x0/9 - a0^2*x1/9 - a0*a1*d0/9 - 5*a0*a1*d1/9 - 5*a0*a1*x0/6 - a0*a1*x1 - 2*a0*b0*c0/3 - a0*b0*c1/2 + 2*a0*b0*d0/9 + 5*a0*b0*d1/18 - 2*a0*b0*x0/3 - a0*b0*x1/3 - a0*b1*d0/3 - 2*a0*b1*d1/3 - 17*a0*b1*x0/18 - 11*a0*b1*x1/9 - a0*c0*x0/3 - 5*a0*c1*x0/18 - 2*a0*c1*x1/9 - a0*d0*x0/3 - a0*d0*x1/3 - 11*a0*d1*x0/18 - 5*a0*d1*x1/9 - 2*a1^2*d0/9 - 4*a1^2*d1/9 - 4*a1^2*x0/9 - 8*a1^2*x1/9 + a1*b0*d0/9 - a1*b0*d1/9 - 7*a1*b0*x0/18 - a1*b0*x1/9 - a1*c0*x1/3 - 2*a1*c1*x0/9 - 4*a1*c1*x1/9 + a1*d0*x0/9 - a1*d0*x1/9 - b0^2*c0/3 - b0^2*c1/6 + 11*b0*b1*x0/18 + 5*b0*b1*x1/9 - b0*c0*x0/3 - b0*c0*x1/3 - b0*c1*x0/6 + b0*d1*x0/6 + b0*d1*x1/3 + 2*b1^2*c0/3 + 8*b1^2*x0/9 + 4*b1^2*x1/9 - b1*c0*x0/3 - 2*b1*c0*x1/3 + 4*b1*d0*x0/9 + 2*b1*d0*x1/9 + 8*b1*d1*x0/9 + 4*b1*d1*x1/9) * h2 + (a0*c0*x0/3 + 5*a0*c1*x0/18 + 2*a0*c1*x1/9 + a0*d0*x0/3 + a0*d0*x1/3 + 11*a0*d1*x0/18 + 5*a0*d1*x1/9 + a1*c0*x1/3 + 2*a1*c1*x0/9 + 4*a1*c1*x1/9 - a1*d0*x0/9 + a1*d0*x1/9 + b0*c0*x0/3 + b0*c0*x1/3 + b0*c1*x0/6 - b0*d1*x0/6 - b0*d1*x1/3 + b1*c0*x0/3 + 2*b1*c0*x1/3 - 4*b1*d0*x0/9 - 2*b1*d0*x1/9 - 8*b1*d1*x0/9 - 4*b1*d1*x1/9) * h3 + (5*a0*c0*d0/9 - a0*c0*d1/18 - a0*c1*d0/3 - 11*a0*d0*d1/18 - 8*a0*d1^2/9 + 7*a1*c0*d0/9 - a1*c0*d1/9 - 5*a1*d0*d1/9 - 4*a1*d1^2/9 - 2*b0*c0^2/3 - b0*c0*c1/2 - b0*c0*d0/3 - b0*c1*d0/6 + 2*b1*c0*d1/3) * h4 + (-a0^2*d0/3 + a0^2*d1/6 + a0*a1*d0/9 + 5*a0*a1*d1/9 + 2*a0*b0*c0/3 + a0*b0*c1/2 - 2*a0*b0*d0/9 - 5*a0*b0*d1/18 + a0*b1*d0/3 + 2*a0*b1*d1/3 + 2*a1^2*d0/9 + 4*a1^2*d1/9 - a1*b0*d0/9 + a1*b0*d1/9 + b0^2*c0/3 + b0^2*c1/6 - 2*b1^2*c0/3) * h5 + (a0*c0/2 + a0*c1/6 + a0*d0/6 + a1*c0/6 + a1*d0/6 + b0*c0/6 + b0*c1/6 + c0^2/2 + c0*c1/3 + c0*d0/3 + c1*d0/3) * h6 + (a0^2/2 + a0*a1/3 + a0*b0/3 + a0*c0/2 + a0*c1/6 + a0*d0/6 + a1*b0/3 + a1*c0/6 + a1*d0/6 + b0*c0/6 + b0*c1/6) * h7 + (-a0*c0/2 - a0*c1/6 - a0*d0/6 - a1*c0/6 - a1*d0/6 - b0*c0/6 - b0*c1/6) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
    · have e : x1 * (a0 * d1 - b1 * c0) ^ 2 = 0 := by
        linear_combination (a0*c0*d0/9 - 11*a0*c0*d1/18 + 2*a0*c0*x0/3 + a0*c0*x1/2 - a0*c1*d0/6 + a0*c1*x0/18 - a0*c1*x1/18 - a0*d0*d1/18 + a0*d0*x1/6 - a0*d1^2/9 - 4*a0*d1*x0/9 - 2*a0*d1*x1/9 + a1*c0*d0/18 - 2*a1*c0*d1/9 + a1*c0*x1/6 - a1*c1*x0/18 - a1*c1*x1/9 + 2*a1*d0*d1/9 - 2*a1*d0*x0/9 - a1*d0*x1/9 + 4*a1*d1^2/9 - a1*d1*x0/3 - 2*a1*d1*x1/3 - b0*c0^2/3 + b0*c0*d1/2 + b0*c0*x0/3 + b0*c0*x1/3 - b0*d0*x0/3 - b0*d0*x1/6 - 2*b0*d1*x0/3 - b0*d1*x1/3 + b1*c0^2/2 + b1*c0*d1/3 + b1*c0*x0/6 + b1*c0*x1/3 - 2*b1*d0*x0/9 - b1*d0*x1/9 - 4*b1*d1*x0/9 - 2*b1*d1*x1/9 + 2*c0^2*x0/3 + c0^2*x1/2 + c0*c1*x0/18 + c0*c1*x1/9 + c0*d0*x0/3 + c0*d0*x1/6 + c0*d1*x0/18 + c0*d1*x1/9 - c1^2*x0/18 - c1^2*x1/9 - 2*c1*d0*x0/9 - c1*d0*x1/9 - c1*d1*x0/3 - 2*c1*d1*x1/3 - d0^2*x0/9 - d0^2*x1/18 - d0*d1*x0/3 - 2*d1^2*x0/9 + 2*d1^2*x1/9) * h1 + (2*a0^2*d1/3 + 7*a0^2*x0/9 + 5*a0^2*x1/9 + 7*a0*a1*d0/18 + 4*a0*a1*d1/9 + a0*a1*x0/3 + a0*a1*x1/3 + a0*b0*c0/3 + 2*a0*b0*d0/9 + 4*a0*b0*d1/9 + 2*a0*b0*x0/3 + a0*b0*x1 - a0*b1*c0/2 + a0*b1*d0/6 + a0*b1*d1/3 - a0*b1*x0/9 + 4*a0*b1*x1/9 + 2*a0*c0*x0/3 + a0*c0*x1/2 + a0*c1*x0/18 - a0*c1*x1/18 + a0*d0*x1/6 - 4*a0*d1*x0/9 - 2*a0*d1*x1/9 + a1^2*d0/9 + 2*a1^2*d1/9 + a1^2*x0/18 + a1^2*x1/9 + a1*b0*d0/9 + 2*a1*b0*d1/9 + a1*b0*x0/9 + 2*a1*b0*x1/9 + a1*c0*x1/6 - a1*c1*x0/18 - a1*c1*x1/9 - 2*a1*d0*x0/9 - a1*d0*x1/9 - a1*d1*x0/3 - 2*a1*d1*x1/3 - b0^2*x0/3 - b0^2*x1/6 - b0*b1*c0/2 - 8*b0*b1*x0/9 - 4*b0*b1*x1/9 + b0*c0*x0/3 + b0*c0*x1/3 - b0*d0*x0/3 - b0*d0*x1/6 - 2*b0*d1*x0/3 - b0*d1*x1/3 - b1^2*c0/3 - 4*b1^2*x0/9 - 2*b1^2*x1/9 + b1*c0*x0/6 + b1*c0*x1/3 - 2*b1*d0*x0/9 - b1*d0*x1/9 - 4*b1*d1*x0/9 - 2*b1*d1*x1/9) * h2 + (-2*a0*c0*x0/3 - a0*c0*x1/2 - a0*c1*x0/18 + a0*c1*x1/18 - a0*d0*x1/6 + 4*a0*d1*x0/9 + 2*a0*d1*x1/9 - a1*c0*x1/6 + a1*c1*x0/18 + a1*c1*x1/9 + 2*a1*d0*x0/9 + a1*d0*x1/9 + a1*d1*x0/3 + 2*a1*d1*x1/3 - b0*c0*x0/3 - b0*c0*x1/3 + b0*d0*x0/3 + b0*d0*x1/6 + 2*b0*d1*x0/3 + b0*d1*x1/3 - b1*c0*x0/6 - b1*c0*x1/3 + 2*b1*d0*x0/9 + b1*d0*x1/9 + 4*b1*d1*x0/9 + 2*b1*d1*x1/9) * h3 + (-a0*c0*d0/9 + 11*a0*c0*d1/18 + a0*c1*d0/6 + a0*d0*d1/18 + a0*d1^2/9 - a1*c0*d0/18 + 2*a1*c0*d1/9 - 2*a1*d0*d1/9 - 4*a1*d1^2/9 + b0*c0^2/3 - b0*c0*d1/2 - b1*c0^2/2 - b1*c0*d1/3) * h4 + (-2*a0^2*d1/3 - 7*a0*a1*d0/18 - 4*a0*a1*d1/9 - a0*b0*c0/3 - 2*a0*b0*d0/9 - 4*a0*b0*d1/9 + a0*b1*c0/2 - a0*b1*d0/6 - a0*b1*d1/3 - a1^2*d0/9 - 2*a1^2*d1/9 - a1*b0*d0/9 - 2*a1*b0*d1/9 + b0*b1*c0/2 + b1^2*c0/3) * h5 + (-a0*c0/2 - a0*c1/12 - a0*d0/6 - a1*c0/12 - b0*c0/6 - c0^2/2 - c0*c1/6 - c0*d0/3) * h6 + (-a0^2/2 - a0*a1/6 - a0*b0/3 - a0*c0/2 - a0*c1/12 - a0*d0/6 - a1*c0/12 - b0*c0/6) * h7 + (a0*c0/2 + a0*c1/12 + a0*d0/6 + a1*c0/12 + b0*c0/6) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
  have key2 := pow_eq_zero_iff (two_ne_zero) |>.mp key
  linear_combination key2

lemma core_12 (a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 : ℂ) (h1 : -2*a0*b0 - a0*b1 - a1*b0 - 2*a1*b1 = 0) (h2 : -2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h3 : -2*a0*b0 - a0*b1 - 2*a0*d0 - a0*d1 - a1*b0 - 2*a1*b1 - a1*d0 - 2*a1*d1 - 2*b0*c0 - b0*c1 - b1*c0 - 2*b1*c1 - 2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h4 : -2*a0*b0 - a0*b1 - 2*a0*x0 - a0*x1 - a1*b0 - 2*a1*b1 - a1*x0 - 2*a1*x1 - 2*b0*x0 - b0*x1 - b1*x0 - 2*b1*x1 = 0) (h5 : -2*c0*d0 - c0*d1 - 2*c0*x0 - c0*x1 - c1*d0 - 2*c1*d1 - c1*x0 - 2*c1*x1 - 2*d0*x0 - d0*x1 - d1*x0 - 2*d1*x1 = 0) (h6 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 = 0) (h7 : -2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0) (h8 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a0*d0*x1 - 2*a0*d1*x0 - 2*a0*d1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 - 2*a1*d0*x0 - 2*a1*d0*x1 - 2*a1*d1*x0 - 2*b0*c0*x1 - 2*b0*c1*x0 - 2*b0*c1*x1 - 2*b1*c0*x0 - 2*b1*c0*x1 - 2*b1*c1*x0 - 2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0)
    (hx : x0 ≠ 0 ∨ x1 ≠ 0) : a1 * d0 = b0 * c1 := by
  have key : (a1 * d0 - b0 * c1) ^ 2 = 0 := by
    rcases hx with hx | hx
    · have e : x0 * (a1 * d0 - b0 * c1) ^ 2 = 0 := by
        linear_combination (-5*a0*c0*d0/9 - 5*a0*c0*d1/18 - a0*c0*x0/9 + 4*a0*c0*x1/9 + a0*c1*x0/6 - 2*a0*d0^2/9 - 5*a0*d0*d1/18 - a0*d0*x0/3 - a0*d0*x1/3 - 5*a0*d1*x0/18 - 5*a0*d1*x1/9 - 7*a1*c0*d0/9 - 5*a1*c0*d1/9 + 4*a1*c0*x0/9 + 5*a1*c0*x1/9 - 2*a1*c1*d0/3 + 2*a1*c1*x0/3 - 4*a1*d0^2/9 - 5*a1*d0*d1/9 - 2*a1*d0*x0/9 - a1*d0*x1/9 + b0*c0*c1/2 - b0*c0*d0/3 - b0*c0*x0/3 - b0*c0*x1/3 + 2*b0*c1^2/3 + b0*c1*d0/6 - b0*c1*x0/2 - 2*b0*c1*x1/3 - 2*b0*d0*x0/9 - 4*b0*d0*x1/9 - 5*b0*d1*x0/18 - 5*b0*d1*x1/9 - c0^2*x0/9 + 4*c0^2*x1/9 + 11*c0*c1*x0/18 + 5*c0*c1*x1/9 - 2*c0*d0*x0/3 - 2*c0*d0*x1/3 - 5*c0*d1*x0/18 - 5*c0*d1*x1/9 + 2*c1^2*x0/3 - 13*c1*d0*x0/18 - 7*c1*d0*x1/9 - 2*d0^2*x0/9 - 4*d0^2*x1/9 - 5*d0*d1*x0/18 - 5*d0*d1*x1/9) * h1 + (5*a0^2*d0/9 + 5*a0^2*d1/18 - a0^2*x0/9 + 4*a0^2*x1/9 + 7*a0*a1*d0/9 + 5*a0*a1*d1/9 + 11*a0*a1*x0/18 + 5*a0*a1*x1/9 - a0*b0*c1/2 + 2*a0*b0*d0/9 + 5*a0*b0*d1/18 - 2*a0*b0*x0/3 - 2*a0*b0*x1/3 - 5*a0*b1*x0/18 - 5*a0*b1*x1/9 - a0*c0*x0/9 + 4*a0*c0*x1/9 + a0*c1*x0/6 - a0*d0*x0/3 - a0*d0*x1/3 - 5*a0*d1*x0/18 - 5*a0*d1*x1/9 + 2*a1^2*d0/3 + 2*a1^2*x0/3 - 2*a1*b0*c1/3 + 4*a1*b0*d0/9 + 5*a1*b0*d1/9 - 13*a1*b0*x0/18 - 7*a1*b0*x1/9 + 4*a1*c0*x0/9 + 5*a1*c0*x1/9 + 2*a1*c1*x0/3 - 2*a1*d0*x0/9 - a1*d0*x1/9 + b0^2*c0/3 - b0^2*c1/6 - 2*b0^2*x0/9 - 4*b0^2*x1/9 - 5*b0*b1*x0/18 - 5*b0*b1*x1/9 - b0*c0*x0/3 - b0*c0*x1/3 - b0*c1*x0/2 - 2*b0*c1*x1/3 - 2*b0*d0*x0/9 - 4*b0*d0*x1/9 - 5*b0*d1*x0/18 - 5*b0*d1*x1/9) * h2 + (a0*c0*x0/9 - 4*a0*c0*x1/9 - a0*c1*x0/6 + a0*d0*x0/3 + a0*d0*x1/3 + 5*a0*d1*x0/18 + 5*a0*d1*x1/9 - 4*a1*c0*x0/9 - 5*a1*c0*x1/9 - 2*a1*c1*x0/3 + 2*a1*d0*x0/9 + a1*d0*x1/9 + b0*c0*x0/3 + b0*c0*x1/3 + b0*c1*x0/2 + 2*b0*c1*x1/3 + 2*b0*d0*x0/9 + 4*b0*d0*x1/9 + 5*b0*d1*x0/18 + 5*b0*d1*x1/9) * h3 + (5*a0*c0*d0/9 + 5*a0*c0*d1/18 + 2*a0*d0^2/9 + 5*a0*d0*d1/18 + 7*a1*c0*d0/9 + 5*a1*c0*d1/9 + 2*a1*c1*d0/3 + 4*a1*d0^2/9 + 5*a1*d0*d1/9 - b0*c0*c1/2 + b0*c0*d0/3 - 2*b0*c1^2/3 - b0*c1*d0/6) * h4 + (-5*a0^2*d0/9 - 5*a0^2*d1/18 - 7*a0*a1*d0/9 - 5*a0*a1*d1/9 + a0*b0*c1/2 - 2*a0*b0*d0/9 - 5*a0*b0*d1/18 - 2*a1^2*d0/3 + 2*a1*b0*c1/3 - 4*a1*b0*d0/9 - 5*a1*b0*d1/9 - b0^2*c0/3 + b0^2*c1/6) * h5 + (a0*c0/2 + a0*c1/6 + a0*d0/6 + a1*c0/6 + a1*d0/6 + b0*c0/6 + b0*c1/6 + c0^2/2 + c0*c1/3 + c0*d0/3 + c1*d0/3) * h6 + (a0^2/2 + a0*a1/3 + a0*b0/3 + a0*c0/2 + a0*c1/6 + a0*d0/6 + a1*b0/3 + a1*c0/6 + a1*d0/6 + b0*c0/6 + b0*c1/6) * h7 + (-a0*c0/2 - a0*c1/6 - a0*d0/6 - a1*c0/6 - a1*d0/6 - b0*c0/6 - b0*c1/6) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
    · have e : x1 * (a1 * d0 - b0 * c1) ^ 2 = 0 := by
        linear_combination (7*a0*c0*d0/9 + 7*a0*c0*d1/18 + 2*a0*c0*x0/9 - 7*a0*c0*x1/18 + a0*c1*x1/6 + 4*a0*d0^2/9 + 7*a0*d0*d1/18 + a0*d0*x0/3 + a0*d0*x1/3 + 7*a0*d1*x0/18 + 7*a0*d1*x1/9 + 8*a1*c0*d0/9 + 7*a1*c0*d1/9 - 7*a1*c0*x0/18 - 11*a1*c0*x1/18 + a1*c1*d0/3 - a1*c1*x0/6 + a1*c1*x1/3 + 8*a1*d0^2/9 + 7*a1*d0*d1/9 - 2*a1*d0*x0/9 - 4*a1*d0*x1/9 - b0*c0*c1/2 + b0*c0*d0/3 + b0*c0*x0/3 + b0*c0*x1/3 - b0*c1^2/3 - b0*c1*d0/2 + b0*c1*x0/6 + b0*c1*x1/3 + 4*b0*d0*x0/9 + 8*b0*d0*x1/9 + 7*b0*d1*x0/18 + 7*b0*d1*x1/9 + 2*c0^2*x0/9 - 7*c0^2*x1/18 - 7*c0*c1*x0/18 - 4*c0*c1*x1/9 + 2*c0*d0*x0/3 + 2*c0*d0*x1/3 + 7*c0*d1*x0/18 + 7*c0*d1*x1/9 - c1^2*x0/6 + c1^2*x1/3 - c1*d0*x0/18 - c1*d0*x1/9 + 4*d0^2*x0/9 + 8*d0^2*x1/9 + 7*d0*d1*x0/18 + 7*d0*d1*x1/9) * h1 + (-7*a0^2*d0/9 - 7*a0^2*d1/18 + 2*a0^2*x0/9 - 7*a0^2*x1/18 - 8*a0*a1*d0/9 - 7*a0*a1*d1/9 - 7*a0*a1*x0/18 - 4*a0*a1*x1/9 + a0*b0*c1/2 - 4*a0*b0*d0/9 - 7*a0*b0*d1/18 + 2*a0*b0*x0/3 + 2*a0*b0*x1/3 + 7*a0*b1*x0/18 + 7*a0*b1*x1/9 + 2*a0*c0*x0/9 - 7*a0*c0*x1/18 + a0*c1*x1/6 + a0*d0*x0/3 + a0*d0*x1/3 + 7*a0*d1*x0/18 + 7*a0*d1*x1/9 - a1^2*d0/3 - a1^2*x0/6 + a1^2*x1/3 + a1*b0*c1/3 - 8*a1*b0*d0/9 - 7*a1*b0*d1/9 - a1*b0*x0/18 - a1*b0*x1/9 - 7*a1*c0*x0/18 - 11*a1*c0*x1/18 - a1*c1*x0/6 + a1*c1*x1/3 - 2*a1*d0*x0/9 - 4*a1*d0*x1/9 - b0^2*c0/3 + b0^2*c1/2 + 4*b0^2*x0/9 + 8*b0^2*x1/9 + 7*b0*b1*x0/18 + 7*b0*b1*x1/9 + b0*c0*x0/3 + b0*c0*x1/3 + b0*c1*x0/6 + b0*c1*x1/3 + 4*b0*d0*x0/9 + 8*b0*d0*x1/9 + 7*b0*d1*x0/18 + 7*b0*d1*x1/9) * h2 + (-2*a0*c0*x0/9 + 7*a0*c0*x1/18 - a0*c1*x1/6 - a0*d0*x0/3 - a0*d0*x1/3 - 7*a0*d1*x0/18 - 7*a0*d1*x1/9 + 7*a1*c0*x0/18 + 11*a1*c0*x1/18 + a1*c1*x0/6 - a1*c1*x1/3 + 2*a1*d0*x0/9 + 4*a1*d0*x1/9 - b0*c0*x0/3 - b0*c0*x1/3 - b0*c1*x0/6 - b0*c1*x1/3 - 4*b0*d0*x0/9 - 8*b0*d0*x1/9 - 7*b0*d1*x0/18 - 7*b0*d1*x1/9) * h3 + (-7*a0*c0*d0/9 - 7*a0*c0*d1/18 - 4*a0*d0^2/9 - 7*a0*d0*d1/18 - 8*a1*c0*d0/9 - 7*a1*c0*d1/9 - a1*c1*d0/3 - 8*a1*d0^2/9 - 7*a1*d0*d1/9 + b0*c0*c1/2 - b0*c0*d0/3 + b0*c1^2/3 + b0*c1*d0/2) * h4 + (7*a0^2*d0/9 + 7*a0^2*d1/18 + 8*a0*a1*d0/9 + 7*a0*a1*d1/9 - a0*b0*c1/2 + 4*a0*b0*d0/9 + 7*a0*b0*d1/18 + a1^2*d0/3 - a1*b0*c1/3 + 8*a1*b0*d0/9 + 7*a1*b0*d1/9 + b0^2*c0/3 - b0^2*c1/2) * h5 + (-a0*c0/2 - a0*c1/12 - a0*d0/6 - a1*c0/12 - b0*c0/6 - c0^2/2 - c0*c1/6 - c0*d0/3) * h6 + (-a0^2/2 - a0*a1/6 - a0*b0/3 - a0*c0/2 - a0*c1/12 - a0*d0/6 - a1*c0/12 - b0*c0/6) * h7 + (a0*c0/2 + a0*c1/12 + a0*d0/6 + a1*c0/12 + b0*c0/6) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
  have key2 := pow_eq_zero_iff (two_ne_zero) |>.mp key
  linear_combination key2

lemma core_13 (a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 : ℂ) (h1 : -2*a0*b0 - a0*b1 - a1*b0 - 2*a1*b1 = 0) (h2 : -2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h3 : -2*a0*b0 - a0*b1 - 2*a0*d0 - a0*d1 - a1*b0 - 2*a1*b1 - a1*d0 - 2*a1*d1 - 2*b0*c0 - b0*c1 - b1*c0 - 2*b1*c1 - 2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h4 : -2*a0*b0 - a0*b1 - 2*a0*x0 - a0*x1 - a1*b0 - 2*a1*b1 - a1*x0 - 2*a1*x1 - 2*b0*x0 - b0*x1 - b1*x0 - 2*b1*x1 = 0) (h5 : -2*c0*d0 - c0*d1 - 2*c0*x0 - c0*x1 - c1*d0 - 2*c1*d1 - c1*x0 - 2*c1*x1 - 2*d0*x0 - d0*x1 - d1*x0 - 2*d1*x1 = 0) (h6 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 = 0) (h7 : -2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0) (h8 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a0*d0*x1 - 2*a0*d1*x0 - 2*a0*d1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 - 2*a1*d0*x0 - 2*a1*d0*x1 - 2*a1*d1*x0 - 2*b0*c0*x1 - 2*b0*c1*x0 - 2*b0*c1*x1 - 2*b1*c0*x0 - 2*b1*c0*x1 - 2*b1*c1*x0 - 2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0)
    (hx : x0 ≠ 0 ∨ x1 ≠ 0) : a1 * d1 = b1 * c1 := by
  have key : (a1 * d1 - b1 * c1) ^ 2 = 0 := by
    rcases hx with hx | hx
    · have e : x0 * (a1 * d1 - b1 * c1) ^ 2 = 0 := by
        linear_combination (-19*a0*c0*d0/18 - 19*a0*c0*d1/36 - 2*a0*c0*x0/3 + a0*c0*x1/3 - 5*a0*c1*d0/12 + 2*a0*c1*x0/9 - a0*c1*x1/18 - 2*a0*d0*d1/9 - 4*a0*d0*x0/3 - 2*a0*d0*x1/3 - a0*d1^2/9 - 4*a0*d1*x0/9 - 11*a0*d1*x1/9 - a1*c0*d0/9 - 19*a1*c0*d1/18 + a1*c0*x0/3 + a1*c0*x1 - a1*c1*d0/6 + a1*c1*x0/9 - a1*c1*x1/9 - 11*a1*d0*d1/18 - 5*a1*d0*x0/9 - a1*d0*x1/9 - 5*a1*d1^2/9 + a1*d1*x0/2 - b0*c0*d0/3 - b0*c0*d1/2 - b0*c0*x0/3 - b0*c0*x1/6 + b0*c1^2/6 - b0*c1*d0/6 - b0*c1*x0/6 - b0*c1*x1/6 + b0*d0*x0/3 + b0*d0*x1/6 + b0*d1*x0/2 - b1*c0*d1/6 - b1*c0*x0/3 - b1*c0*x1/6 + b1*c1*x0/2 + b1*d0*x0/9 + b1*d0*x1/18 + 2*b1*d1*x0/9 + b1*d1*x1/9 - 2*c0^2*x0/3 + c0^2*x1/3 + 5*c0*c1*x0/9 + 17*c0*c1*x1/18 - 2*c0*d0*x0/3 - 5*c0*d0*x1/12 - 25*c0*d1*x0/36 - 25*c0*d1*x1/18 + c1^2*x0/9 - c1^2*x1/9 - 2*c1*d0*x0/9 - 5*c1*d0*x1/18 + 2*c1*d1*x0 + d0^2*x0/18 + d0^2*x1/36 - d0*d1*x0/12 - d0*d1*x1/2 - d1^2*x0/18 - 4*d1^2*x1/9) * h1 + (4*a0^2*d0/3 + 2*a0^2*d1/3 - 7*a0^2*x0/18 + 17*a0^2*x1/36 + 11*a0*a1*d0/9 + 29*a0*a1*d1/18 + 5*a0*a1*x0/4 + 3*a0*a1*x1/2 - 5*a0*b0*d0/18 - 7*a0*b0*d1/18 - 8*a0*b0*x0/3 - 5*a0*b0*x1/4 - a0*b1*d0/12 - a0*b1*d1/6 - 23*a0*b1*x0/18 - 25*a0*b1*x1/18 - 2*a0*c0*x0/3 + a0*c0*x1/3 + 2*a0*c1*x0/9 - a0*c1*x1/18 - 4*a0*d0*x0/3 - 2*a0*d0*x1/3 - 4*a0*d1*x0/9 - 11*a0*d1*x1/9 + 4*a1^2*d0/9 + 5*a1^2*d1/9 + 7*a1^2*x0/18 + 4*a1^2*x1/9 - a1*b0*c1/6 - 5*a1*b0*d0/36 + a1*b0*d1/18 - 29*a1*b0*x0/36 - 5*a1*b0*x1/18 + a1*c0*x0/3 + a1*c0*x1 + a1*c1*x0/9 - a1*c1*x1/9 - 5*a1*d0*x0/9 - a1*d0*x1/9 + a1*d1*x0/2 + b0^2*c0/3 + b0^2*c1/6 + b0^2*x0/3 + b0^2*x1/6 + b0*b1*c0/2 + 11*b0*b1*x0/18 + b0*b1*x1/18 - b0*c0*x0/3 - b0*c0*x1/6 - b0*c1*x0/6 - b0*c1*x1/6 + b0*d0*x0/3 + b0*d0*x1/6 + b0*d1*x0/2 + b1^2*c0/6 + 2*b1^2*x0/9 + b1^2*x1/9 - b1*c0*x0/3 - b1*c0*x1/6 + b1*c1*x0/2 + b1*d0*x0/9 + b1*d0*x1/18 + 2*b1*d1*x0/9 + b1*d1*x1/9) * h2 + (2*a0*c0*x0/3 - a0*c0*x1/3 - 2*a0*c1*x0/9 + a0*c1*x1/18 + 4*a0*d0*x0/3 + 2*a0*d0*x1/3 + 4*a0*d1*x0/9 + 11*a0*d1*x1/9 - a1*c0*x0/3 - a1*c0*x1 - a1*c1*x0/9 + a1*c1*x1/9 + 5*a1*d0*x0/9 + a1*d0*x1/9 - a1*d1*x0/2 + b0*c0*x0/3 + b0*c0*x1/6 + b0*c1*x0/6 + b0*c1*x1/6 - b0*d0*x0/3 - b0*d0*x1/6 - b0*d1*x0/2 + b1*c0*x0/3 + b1*c0*x1/6 - b1*c1*x0/2 - b1*d0*x0/9 - b1*d0*x1/18 - 2*b1*d1*x0/9 - b1*d1*x1/9) * h3 + (19*a0*c0*d0/18 + 19*a0*c0*d1/36 + 5*a0*c1*d0/12 + 2*a0*d0*d1/9 + a0*d1^2/9 + a1*c0*d0/9 + 19*a1*c0*d1/18 + a1*c1*d0/6 + 11*a1*d0*d1/18 + 5*a1*d1^2/9 + b0*c0*d0/3 + b0*c0*d1/2 - b0*c1^2/6 + b0*c1*d0/6 + b1*c0*d1/6) * h4 + (-4*a0^2*d0/3 - 2*a0^2*d1/3 - 11*a0*a1*d0/9 - 29*a0*a1*d1/18 + 5*a0*b0*d0/18 + 7*a0*b0*d1/18 + a0*b1*d0/12 + a0*b1*d1/6 - 4*a1^2*d0/9 - 5*a1^2*d1/9 + a1*b0*c1/6 + 5*a1*b0*d0/36 - a1*b0*d1/18 - b0^2*c0/3 - b0^2*c1/6 - b0*b1*c0/2 - b1^2*c0/6) * h5 + (2*a0*c0/3 - a0*c1/6 - a1*c0/6 - a1*d0/6 - b0*c1/6 + 2*c0^2/3 - c0*c1/3 - c1*d0/3) * h6 + (2*a0^2/3 - a0*a1/3 + 2*a0*c0/3 - a0*c1/6 - a1*b0/3 - a1*c0/6 - a1*d0/6 - b0*c1/6) * h7 + (-2*a0*c0/3 + a0*c1/6 + a1*c0/6 + a1*d0/6 + b0*c1/6) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
    · have e : x1 * (a1 * d1 - b1 * c1) ^ 2 = 0 := by
        linear_combination (a0*c0*d0/9 + a0*c0*d1/18 - a0*c0*x1/3 - 7*a0*c1*d0/24 + a0*c1*x0/72 - 2*a0*c1*x1/9 + a0*d0*d1/9 - a0*d0*x0/12 - 5*a0*d0*x1/24 + 5*a0*d1^2/36 - 23*a0*d1*x0/72 - 2*a0*d1*x1/9 + 25*a1*c0*d0/72 + 13*a1*c0*d1/36 - 11*a1*c0*x0/24 - 7*a1*c0*x1/12 + a1*c1*d0/12 - 11*a1*c1*x0/36 - 4*a1*c1*x1/9 + 11*a1*d0*d1/36 - 5*a1*d0*x0/9 - 4*a1*d0*x1/9 + 4*a1*d1^2/9 - 5*a1*d1*x0/12 - a1*d1*x1/3 + b0*c0^2/4 + b0*c0*c1/8 + b0*c0*d0/12 + 3*b0*c0*d1/8 - b0*c0*x0/6 - b0*c0*x1/4 - b0*c1^2/12 + b0*c1*d0/24 - b0*c1*x0/8 - b0*c1*x1/6 - b0*d0*x0/4 - b0*d0*x1/8 - 11*b0*d1*x0/24 - b0*d1*x1/6 + b1*c0^2/8 + b1*c0*d1/12 + b1*c0*x0/24 - b1*c0*x1/6 + b1*c1*x1/2 - b1*d0*x0/18 - b1*d0*x1/36 - b1*d1*x0/9 - b1*d1*x1/18 - c0^2*x1/3 - 4*c0*c1*x0/9 - 29*c0*c1*x1/36 - c0*d0*x0/4 + 5*c0*d0*x1/24 + c0*d1*x0/18 + c0*d1*x1/9 - 11*c1^2*x0/36 - 4*c1^2*x1/9 - 49*c1*d0*x0/72 - c1*d0*x1/9 - 5*c1*d1*x0/12 + 7*c1*d1*x1/6 - d0^2*x0/36 - d0^2*x1/72 + d0*d1*x0/24 + d0*d1*x1/4 + d1^2*x0/9 + 7*d1^2*x1/18) * h1 + (a0^2*d0/12 + a0^2*d1/24 + 7*a0^2*x0/36 - 17*a0^2*x1/72 + 31*a0*a1*d0/72 + a0*a1*d1/36 + a0*a1*x0/24 - 5*a0*a1*x1/12 - a0*b0*c0/4 - a0*b0*c1/8 + 2*a0*b0*d0/9 + 29*a0*b0*d1/72 + a0*b0*x0/6 - 11*a0*b0*x1/12 - a0*b1*c0/8 + a0*b1*d0/24 + a0*b1*d1/12 - 5*a0*b1*x0/72 - 17*a0*b1*x1/36 - a0*c0*x1/3 + a0*c1*x0/72 - 2*a0*c1*x1/9 - a0*d0*x0/12 - 5*a0*d0*x1/24 - 23*a0*d1*x0/72 - 2*a0*d1*x1/9 + a1^2*d0/9 + 7*a1^2*d1/18 - a1^2*x0/9 - a1^2*x1/18 + a1*b0*c1/12 + a1*b0*d0/9 + 5*a1*b0*d1/36 - 13*a1*b0*x0/72 - 25*a1*b0*x1/36 - 11*a1*c0*x0/24 - 7*a1*c0*x1/12 - 11*a1*c1*x0/36 - 4*a1*c1*x1/9 - 5*a1*d0*x0/9 - 4*a1*d0*x1/9 - 5*a1*d1*x0/12 - a1*d1*x1/3 - b0^2*c0/12 - b0^2*c1/24 - b0^2*x0/4 - b0^2*x1/8 - 3*b0*b1*c0/8 - 37*b0*b1*x0/72 - 7*b0*b1*x1/36 - b0*c0*x0/6 - b0*c0*x1/4 - b0*c1*x0/8 - b0*c1*x1/6 - b0*d0*x0/4 - b0*d0*x1/8 - 11*b0*d1*x0/24 - b0*d1*x1/6 - b1^2*c0/12 - b1^2*x0/9 - b1^2*x1/18 + b1*c0*x0/24 - b1*c0*x1/6 + b1*c1*x1/2 - b1*d0*x0/18 - b1*d0*x1/36 - b1*d1*x0/9 - b1*d1*x1/18) * h2 + (a0*c0*x1/3 - a0*c1*x0/72 + 2*a0*c1*x1/9 + a0*d0*x0/12 + 5*a0*d0*x1/24 + 23*a0*d1*x0/72 + 2*a0*d1*x1/9 + 11*a1*c0*x0/24 + 7*a1*c0*x1/12 + 11*a1*c1*x0/36 + 4*a1*c1*x1/9 + 5*a1*d0*x0/9 + 4*a1*d0*x1/9 + 5*a1*d1*x0/12 + a1*d1*x1/3 + b0*c0*x0/6 + b0*c0*x1/4 + b0*c1*x0/8 + b0*c1*x1/6 + b0*d0*x0/4 + b0*d0*x1/8 + 11*b0*d1*x0/24 + b0*d1*x1/6 - b1*c0*x0/24 + b1*c0*x1/6 - b1*c1*x1/2 + b1*d0*x0/18 + b1*d0*x1/36 + b1*d1*x0/9 + b1*d1*x1/18) * h3 + (-a0*c0*d0/9 - a0*c0*d1/18 + 7*a0*c1*d0/24 - a0*d0*d1/9 - 5*a0*d1^2/36 - 25*a1*c0*d0/72 - 13*a1*c0*d1/36 - a1*c1*d0/12 - 11*a1*d0*d1/36 - 4*a1*d1^2/9 - b0*c0^2/4 - b0*c0*c1/8 - b0*c0*d0/12 - 3*b0*c0*d1/8 + b0*c1^2/12 - b0*c1*d0/24 - b1*c0^2/8 - b1*c0*d1/12) * h4 + (-a0^2*d0/12 - a0^2*d1/24 - 31*a0*a1*d0/72 - a0*a1*d1/36 + a0*b0*c0/4 + a0*b0*c1/8 - 2*a0*b0*d0/9 - 29*a0*b0*d1/72 + a0*b1*c0/8 - a0*b1*d0/24 - a0*b1*d1/12 - a1^2*d0/9 - 7*a1^2*d1/18 - a1*b0*c1/12 - a1*b0*d0/9 - 5*a1*b0*d1/36 + b0^2*c0/12 + b0^2*c1/24 + 3*b0*b1*c0/8 + b1^2*c0/12) * h5 + (-a0*c0/3 - a0*c1/6 + a0*d0/6 - a1*c0/6 + a1*d0/6 + b0*c0/6 + b0*c1/6 - c0^2/3 - c0*c1/3 + c0*d0/3 + c1*d0/3) * h6 + (-a0^2/3 - a0*a1/3 + a0*b0/3 - a0*c0/3 - a0*c1/6 + a0*d0/6 + a1*b0/3 - a1*c0/6 + a1*d0/6 + b0*c0/6 + b0*c1/6) * h7 + (a0*c0/3 + a0*c1/6 - a0*d0/6 + a1*c0/6 - a1*d0/6 - b0*c0/6 - b0*c1/6) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
  have key2 := pow_eq_zero_iff (two_ne_zero) |>.mp key
  linear_combination key2

lemma core_23 (a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 : ℂ) (h1 : -2*a0*b0 - a0*b1 - a1*b0 - 2*a1*b1 = 0) (h2 : -2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h3 : -2*a0*b0 - a0*b1 - 2*a0*d0 - a0*d1 - a1*b0 - 2*a1*b1 - a1*d0 - 2*a1*d1 - 2*b0*c0 - b0*c1 - b1*c0 - 2*b1*c1 - 2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h4 : -2*a0*b0 - a0*b1 - 2*a0*x0 - a0*x1 - a1*b0 - 2*a1*b1 - a1*x0 - 2*a1*x1 - 2*b0*x0 - b0*x1 - b1*x0 - 2*b1*x1 = 0) (h5 : -2*c0*d0 - c0*d1 - 2*c0*x0 - c0*x1 - c1*d0 - 2*c1*d1 - c1*x0 - 2*c1*x1 - 2*d0*x0 - d0*x1 - d1*x0 - 2*d1*x1 = 0) (h6 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 = 0) (h7 : -2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0) (h8 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a0*d0*x1 - 2*a0*d1*x0 - 2*a0*d1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 - 2*a1*d0*x0 - 2*a1*d0*x1 - 2*a1*d1*x0 - 2*b0*c0*x1 - 2*b0*c1*x0 - 2*b0*c1*x1 - 2*b1*c0*x0 - 2*b1*c0*x1 - 2*b1*c1*x0 - 2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0)
    (hx : x0 ≠ 0 ∨ x1 ≠ 0) : b0 * d1 = b1 * d0 := by
  have key : (b0 * d1 - b1 * d0) ^ 2 = 0 := by
    rcases hx with hx | hx
    · have e : x0 * (b0 * d1 - b1 * d0) ^ 2 = 0 := by
        linear_combination (2*a0*c0*d0/3 + a0*c0*d1/3 + a0*c0*x0/3 - a0*c0*x1/3 + 2*a0*d0^2/3 + a0*d0*d1/3 + a0*d1*x0/3 + 2*a0*d1*x1/3 + a1*c0*d0/3 + 2*a1*c0*d1/3 - a1*c0*x0/3 - 2*a1*c0*x1/3 + a1*d0^2/3 + 2*a1*d0*d1/3 - a1*d0*x0/3 - 2*a1*d0*x1/3 + b0*d0*d1/3 - b0*d0*x1/3 + 2*b0*d1^2/3 + b0*d1*x0/3 - b1*d0^2/3 - 2*b1*d0*d1/3 - 2*b1*d0*x1/3 + 2*b1*d1*x0/3 + c0^2*x0/3 - c0^2*x1/3 - c0*c1*x0/3 - 2*c0*c1*x1/3 + c0*d1*x0/3 + 2*c0*d1*x1/3 - c1*d0*x0/3 - 2*c1*d0*x1/3 - d0^2*x1/3 + d0*d1*x0/3 - 2*d0*d1*x1/3 + 2*d1^2*x0/3) * h1 + (-2*a0^2*d0/3 - a0^2*d1/3 + a0^2*x0/3 - a0^2*x1/3 - a0*a1*d0/3 - 2*a0*a1*d1/3 - a0*a1*x0/3 - 2*a0*a1*x1/3 - 2*a0*b0*d0/3 - a0*b0*d1/3 + a0*b1*x0/3 + 2*a0*b1*x1/3 + a0*c0*x0/3 - a0*c0*x1/3 + a0*d1*x0/3 + 2*a0*d1*x1/3 - a1*b0*d0/3 - 2*a1*b0*d1/3 - a1*b0*x0/3 - 2*a1*b0*x1/3 - a1*c0*x0/3 - 2*a1*c0*x1/3 - a1*d0*x0/3 - 2*a1*d0*x1/3 - b0^2*d1/3 - b0^2*x1/3 + b0*b1*d0/3 - 2*b0*b1*d1/3 + b0*b1*x0/3 - 2*b0*b1*x1/3 - b0*d0*x1/3 + b0*d1*x0/3 + 2*b1^2*d0/3 + 2*b1^2*x0/3 - 2*b1*d0*x1/3 + 2*b1*d1*x0/3) * h2 + (-a0*c0*x0/3 + a0*c0*x1/3 - a0*d1*x0/3 - 2*a0*d1*x1/3 + a1*c0*x0/3 + 2*a1*c0*x1/3 + a1*d0*x0/3 + 2*a1*d0*x1/3 + b0*d0*x1/3 - b0*d1*x0/3 + 2*b1*d0*x1/3 - 2*b1*d1*x0/3) * h3 + (-2*a0*c0*d0/3 - a0*c0*d1/3 - 2*a0*d0^2/3 - a0*d0*d1/3 - a1*c0*d0/3 - 2*a1*c0*d1/3 - a1*d0^2/3 - 2*a1*d0*d1/3 - b0*d0*d1/3 - 2*b0*d1^2/3 + b1*d0^2/3 + 2*b1*d0*d1/3) * h4 + (2*a0^2*d0/3 + a0^2*d1/3 + a0*a1*d0/3 + 2*a0*a1*d1/3 + 2*a0*b0*d0/3 + a0*b0*d1/3 + a1*b0*d0/3 + 2*a1*b0*d1/3 + b0^2*d1/3 - b0*b1*d0/3 + 2*b0*b1*d1/3 - 2*b1^2*d0/3) * h5 + (-a0*c0/2 - c0^2/2) * h6 + (-a0^2/2 - a0*c0/2) * h7 + (a0*c0/2) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
    · have e : x1 * (b0 * d1 - b1 * d0) ^ 2 = 0 := by
        linear_combination (-a0*c0*d0/3 - a0*c0*d1/6 + a0*c0*x1/2 + a0*c1*d0/2 - a0*c1*x0/6 + a0*c1*x1/6 + 2*a0*d0*d1/3 + a0*d1^2/3 - 2*a0*d1*x0/3 - a0*d1*x1/3 - 2*a1*c0*d0/3 - a1*c0*d1/3 + a1*c0*x0/2 + a1*c0*x1/2 + a1*c1*x0/6 + a1*c1*x1/3 + a1*d0*d1/3 + 2*a1*d0*x0/3 + a1*d0*x1/3 + 2*a1*d1^2/3 - 2*b0*d0*d1/3 + 2*b0*d0*x1/3 - b0*d1^2/3 - 2*b0*d1*x0/3 + 2*b1*d0^2/3 + b1*d0*d1/3 + b1*d0*x1/3 - b1*d1*x0/3 + c0^2*x1/2 + c0*c1*x0/3 + 2*c0*c1*x1/3 - c0*d0*x1/2 - c0*d1*x0/6 - c0*d1*x1/3 + c1^2*x0/6 + c1^2*x1/3 + 2*c1*d0*x0/3 + c1*d0*x1/3 + d0^2*x0/3 + 5*d0^2*x1/6 + d0*d1*x0/6 + d0*d1*x1 + 2*d1^2*x1/3) * h1 + (-a0^2*x0/3 + a0^2*x1/3 - 2*a0*a1*d0/3 - a0*a1*d1/3 - a0*a1*x0/2 + a0*b0*d0/3 + 2*a0*b0*d1/3 + a0*b0*x1/2 - a0*b1*d0/2 - 2*a0*b1*x0/3 - a0*b1*x1/3 + a0*c0*x1/2 - a0*c1*x0/6 + a0*c1*x1/6 - 2*a0*d1*x0/3 - a0*d1*x1/3 - a1^2*d0/3 - 2*a1^2*d1/3 - a1^2*x0/6 - a1^2*x1/3 + a1*b0*d0/6 + a1*b0*d1/3 + a1*b0*x0/6 + a1*b0*x1/3 + a1*c0*x0/2 + a1*c0*x1/2 + a1*c1*x0/6 + a1*c1*x1/3 + 2*a1*d0*x0/3 + a1*d0*x1/3 + 2*b0^2*d1/3 + 2*b0^2*x1/3 - 2*b0*b1*d0/3 + b0*b1*d1/3 - 2*b0*b1*x0/3 + b0*b1*x1/3 + 2*b0*d0*x1/3 - 2*b0*d1*x0/3 - b1^2*d0/3 - b1^2*x0/3 + b1*d0*x1/3 - b1*d1*x0/3) * h2 + (-a0*c0*x1/2 + a0*c1*x0/6 - a0*c1*x1/6 + 2*a0*d1*x0/3 + a0*d1*x1/3 - a1*c0*x0/2 - a1*c0*x1/2 - a1*c1*x0/6 - a1*c1*x1/3 - 2*a1*d0*x0/3 - a1*d0*x1/3 - 2*b0*d0*x1/3 + 2*b0*d1*x0/3 - b1*d0*x1/3 + b1*d1*x0/3) * h3 + (a0*c0*d0/3 + a0*c0*d1/6 - a0*c1*d0/2 - 2*a0*d0*d1/3 - a0*d1^2/3 + 2*a1*c0*d0/3 + a1*c0*d1/3 - a1*d0*d1/3 - 2*a1*d1^2/3 + 2*b0*d0*d1/3 + b0*d1^2/3 - 2*b1*d0^2/3 - b1*d0*d1/3) * h4 + (2*a0*a1*d0/3 + a0*a1*d1/3 - a0*b0*d0/3 - 2*a0*b0*d1/3 + a0*b1*d0/2 + a1^2*d0/3 + 2*a1^2*d1/3 - a1*b0*d0/6 - a1*b0*d1/3 - 2*b0^2*d1/3 + 2*b0*b1*d0/3 - b0*b1*d1/3 + b1^2*d0/3) * h5 + (a0*c0/2 + a0*c1/4 + a1*c0/4 + c0^2/2 + c0*c1/2) * h6 + (a0^2/2 + a0*a1/2 + a0*c0/2 + a0*c1/4 + a1*c0/4) * h7 + (-a0*c0/2 - a0*c1/4 - a1*c0/4) * h8
      exact (mul_eq_zero.mp e).resolve_left hx
  have key2 := pow_eq_zero_iff (two_ne_zero) |>.mp key
  linear_combination key2

lemma core_all (a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 : ℂ) (h1 : -2*a0*b0 - a0*b1 - a1*b0 - 2*a1*b1 = 0) (h2 : -2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h3 : -2*a0*b0 - a0*b1 - 2*a0*d0 - a0*d1 - a1*b0 - 2*a1*b1 - a1*d0 - 2*a1*d1 - 2*b0*c0 - b0*c1 - b1*c0 - 2*b1*c1 - 2*c0*d0 - c0*d1 - c1*d0 - 2*c1*d1 = 0) (h4 : -2*a0*b0 - a0*b1 - 2*a0*x0 - a0*x1 - a1*b0 - 2*a1*b1 - a1*x0 - 2*a1*x1 - 2*b0*x0 - b0*x1 - b1*x0 - 2*b1*x1 = 0) (h5 : -2*c0*d0 - c0*d1 - 2*c0*x0 - c0*x1 - c1*d0 - 2*c1*d1 - c1*x0 - 2*c1*x1 - 2*d0*x0 - d0*x1 - d1*x0 - 2*d1*x1 = 0) (h6 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 = 0) (h7 : -2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0) (h8 : -2*a0*b0*x1 - 2*a0*b1*x0 - 2*a0*b1*x1 - 2*a0*d0*x1 - 2*a0*d1*x0 - 2*a0*d1*x1 - 2*a1*b0*x0 - 2*a1*b0*x1 - 2*a1*b1*x0 - 2*a1*d0*x0 - 2*a1*d0*x1 - 2*a1*d1*x0 - 2*b0*c0*x1 - 2*b0*c1*x0 - 2*b0*c1*x1 - 2*b1*c0*x0 - 2*b1*c0*x1 - 2*b1*c1*x0 - 2*c0*d0*x1 - 2*c0*d1*x0 - 2*c0*d1*x1 - 2*c1*d0*x0 - 2*c1*d0*x1 - 2*c1*d1*x0 = 0)
    (hx : x0 ≠ 0 ∨ x1 ≠ 0) : a0 * c1 = a1 * c0 ∧ a0 * d0 = b0 * c0 ∧ a0 * d1 = b1 * c0 ∧ a1 * d0 = b0 * c1 ∧ a1 * d1 = b1 * c1 ∧ b0 * d1 = b1 * d0 :=
  ⟨core_01 a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 h1 h2 h3 h4 h5 h6 h7 h8 hx, core_02 a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 h1 h2 h3 h4 h5 h6 h7 h8 hx, core_03 a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 h1 h2 h3 h4 h5 h6 h7 h8 hx, core_12 a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 h1 h2 h3 h4 h5 h6 h7 h8 hx, core_13 a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 h1 h2 h3 h4 h5 h6 h7 h8 hx, core_23 a0 a1 b0 b1 c0 c1 d0 d1 x0 x1 h1 h2 h3 h4 h5 h6 h7 h8 hx⟩

noncomputable def ev {ι : Type} (p : ι) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun t := t p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def zsum : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun x := x 0 + x 1 + x 2
  map_add' := by
    intros
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intros
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma dimX (X : Submodule ℂ (Fin 3 → ℂ)) (hXs : ∀ x ∈ X, x 0 + x 1 + x 2 = 0) : Module.finrank ℂ X ≤ 2 := by
  refine finrank_le_of_inj X 2 (LinearMap.pi (fun i : Fin 2 => ev (Fin.castSucc i))) ?_
  intro x hx hg
  have h0 : x 0 = 0 := congrFun hg 0
  have h1 : x 1 = 0 := congrFun hg 1
  have h2 := hXs x hx
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · show x 2 = 0
    linear_combination h2 - h0 - h1

lemma dimY (Y : Submodule ℂ (Fin 2 → ℂ)) (hYs : ∀ y ∈ Y, y 0 + y 1 = 0) : Module.finrank ℂ Y ≤ 1 := by
  refine single Y (ev 0) ?_
  intro y hy hz
  have h0 : y 0 = 0 := hz
  have h2 := hYs y hy
  funext i
  fin_cases i
  · exact h0
  · show y 1 = 0
    linear_combination h2 - h0

def u1 : Fin 3 → ℂ := fun j => if j = 0 then 1 else if j = 1 then -1 else 0

def u2 : Fin 3 → ℂ := fun j => if j = 0 then 0 else if j = 1 then 1 else -1

lemma u1_0 : u1 0 = 1 := by simp [u1]

lemma u1_1 : u1 1 = -1 := by simp [u1]

lemma u1_2 : u1 2 = 0 := by simp [u1]

lemma u2_0 : u2 0 = 0 := by simp [u2]

lemma u2_1 : u2 1 = 1 := by simp [u2]

lemma u2_2 : u2 2 = -1 := by simp [u2]

lemma full_X (X : Submodule ℂ (Fin 3 → ℂ)) (hXs : ∀ x ∈ X, x 0 + x 1 + x 2 = 0) (hd : 2 ≤ Module.finrank ℂ X) : u1 ∈ X ∧ u2 ∈ X := by
  have hle : X ≤ LinearMap.ker zsum := fun x hx => hXs x hx
  have hk : Module.finrank ℂ (LinearMap.ker zsum) ≤ 2 := dimX _ (fun x hx => hx)
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [heq]
  constructor
  · show u1 0 + u1 1 + u1 2 = 0
    rw [u1_0, u1_1, u1_2]
    ring
  · show u2 0 + u2 1 + u2 2 = 0
    rw [u2_0, u2_1, u2_2]
    ring

lemma P1 (L : Submodule ℂ (Fin 2 × Fin 3 → ℂ)) (X : Submodule ℂ (Fin 3 → ℂ)) (Y : Submodule ℂ (Fin 2 → ℂ)) (E1 : ∀ t ∈ L, t (0, 0) + t (1, 0) + (t (0, 1) + t (1, 1)) + (t (0, 2) + t (1, 2)) = 0) (E2 : ∀ t ∈ L, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) = 0) (G2 : ∀ t ∈ L, ∀ x ∈ X, (t (0, 0) * t (1, 1) + t (0, 0) * x 1 + t (1, 0) * x 1) + (t (0, 0) * t (1, 2) + t (0, 0) * x 2 + t (1, 0) * x 2) + (t (0, 1) * t (1, 0) + t (0, 1) * x 0 + t (1, 1) * x 0) + (t (0, 1) * t (1, 2) + t (0, 1) * x 2 + t (1, 1) * x 2) + (t (0, 2) * t (1, 0) + t (0, 2) * x 0 + t (1, 2) * x 0) + (t (0, 2) * t (1, 1) + t (0, 2) * x 1 + t (1, 2) * x 1) = 0) (G3 : ∀ t ∈ L, ∀ x ∈ X, t (0, 0) * t (1, 1) * x 2 + t (0, 0) * t (1, 2) * x 1 + t (0, 1) * t (1, 0) * x 2 + t (0, 1) * t (1, 2) * x 0 + t (0, 2) * t (1, 0) * x 1 + t (0, 2) * t (1, 1) * x 0 = 0) (K2 : ∀ t ∈ L, ∀ y ∈ Y, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) + (t (0, 0) + t (0, 1) + t (0, 2)) * y 1 + y 0 * (t (1, 0) + t (1, 1) + t (1, 2)) = 0) (hXs : ∀ x ∈ X, x 0 + x 1 + x 2 = 0) (hYs : ∀ y ∈ Y, y 0 + y 1 = 0)
    (x : Fin 3 → ℂ) (hx : x ∈ X) (hx0 : x ≠ 0) (y : Fin 2 → ℂ) (hy : y ∈ Y) (hy0 : y ≠ 0) :
    Module.finrank ℂ L ≤ 1 := by
  have ys := hYs y hy
  have xs := hXs x hx
  have hy00 : y 0 ≠ 0 := by
    intro h
    apply hy0
    funext i
    fin_cases i
    · exact h
    · show y 1 = 0
      linear_combination ys - h
  have hx01 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    apply hx0
    funext i
    fin_cases i
    · exact hc.1
    · exact hc.2
    · show x 2 = 0
      linear_combination xs - hc.1 - hc.2
  have hx2 : x 2 = -x 0 - x 1 := by linear_combination xs
  have hR : ∀ t ∈ L, t (0, 2) = -t (0, 0) - t (0, 1) ∧ t (1, 2) = -t (1, 0) - t (1, 1) := by
    intro t ht
    have k := K2 t ht y hy
    have e1 := E1 t ht
    have e2 := E2 t ht
    have hd : y 0 * ((t (1, 0) + t (1, 1) + t (1, 2)) - (t (0, 0) + t (0, 1) + t (0, 2))) = 0 := by
      linear_combination k - e2 - (t (0, 0) + t (0, 1) + t (0, 2)) * ys
    have hd' := (mul_eq_zero.mp hd).resolve_left hy00
    constructor
    · linear_combination (e1 - hd') / 2
    · linear_combination (e1 + hd') / 2
  refine dim_le_one4 L (ev (0, 0)) (ev (0, 1)) (ev (1, 0)) (ev (1, 1)) ?_ ?_
  · intro t ht h1 h2 h3 h4
    obtain ⟨ha, hb⟩ := hR t ht
    have z1 : t (0, 0) = 0 := h1
    have z2 : t (0, 1) = 0 := h2
    have z3 : t (1, 0) = 0 := h3
    have z4 : t (1, 1) = 0 := h4
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j
    · exact z1
    · exact z2
    · show t (0, 2) = 0
      rw [ha, z1, z2]
      ring
    · exact z3
    · exact z4
    · show t (1, 2) = 0
      rw [hb, z3, z4]
      ring
  · intro t ht s hs
    obtain ⟨ha, hb⟩ := hR t ht
    obtain ⟨hc, hd⟩ := hR s hs
    have f1 := E2 t ht
    have f2 := E2 s hs
    have f3 := E2 (t + s) (L.add_mem ht hs)
    have f4 := G2 t ht x hx
    have f5 := G2 s hs x hx
    have f6 := G3 t ht x hx
    have f7 := G3 s hs x hx
    have f8 := G3 (t + s) (L.add_mem ht hs) x hx
    simp only [Pi.add_apply] at f3 f8
    rw [ha, hb] at f1 f4 f6
    rw [hc, hd] at f2 f5 f7
    rw [ha, hb, hc, hd] at f3 f8
    rw [hx2] at f4 f5 f6 f7 f8
    exact core_all (t (0, 0)) (t (0, 1)) (t (1, 0)) (t (1, 1)) (s (0, 0)) (s (0, 1)) (s (1, 0))
      (s (1, 1)) (x 0) (x 1) (by linear_combination f1) (by linear_combination f2)
      (by linear_combination f3) (by linear_combination f4) (by linear_combination f5)
      (by linear_combination f6) (by linear_combination f7) (by linear_combination f8) hx01

lemma P2f (L : Submodule ℂ (Fin 2 × Fin 3 → ℂ)) (X : Submodule ℂ (Fin 3 → ℂ)) (E1 : ∀ t ∈ L, t (0, 0) + t (1, 0) + (t (0, 1) + t (1, 1)) + (t (0, 2) + t (1, 2)) = 0) (E2 : ∀ t ∈ L, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) = 0) (G2 : ∀ t ∈ L, ∀ x ∈ X, (t (0, 0) * t (1, 1) + t (0, 0) * x 1 + t (1, 0) * x 1) + (t (0, 0) * t (1, 2) + t (0, 0) * x 2 + t (1, 0) * x 2) + (t (0, 1) * t (1, 0) + t (0, 1) * x 0 + t (1, 1) * x 0) + (t (0, 1) * t (1, 2) + t (0, 1) * x 2 + t (1, 1) * x 2) + (t (0, 2) * t (1, 0) + t (0, 2) * x 0 + t (1, 2) * x 0) + (t (0, 2) * t (1, 1) + t (0, 2) * x 1 + t (1, 2) * x 1) = 0) (G3 : ∀ t ∈ L, ∀ x ∈ X, t (0, 0) * t (1, 1) * x 2 + t (0, 0) * t (1, 2) * x 1 + t (0, 1) * t (1, 0) * x 2 + t (0, 1) * t (1, 2) * x 0 + t (0, 2) * t (1, 0) * x 1 + t (0, 2) * t (1, 1) * x 0 = 0)
    (h1 : u1 ∈ X) (h2 : u2 ∈ X) (t : Fin 2 × Fin 3 → ℂ) (ht : t ∈ L) :
    t (1, 0) = -t (0, 0) ∧ t (1, 1) = -t (0, 1) ∧ t (1, 2) = -t (0, 2) ∧
      t (0, 0) * t (0, 1) = 0 ∧ t (0, 0) * t (0, 2) = 0 ∧ t (0, 1) * t (0, 2) = 0 := by
  have e1 := E1 t ht
  have e2 := E2 t ht
  have g1 := G2 t ht u1 h1
  have g2 := G2 t ht u2 h2
  have q1 := G3 t ht u1 h1
  have q2 := G3 t ht u2 h2
  rw [u1_0, u1_1, u1_2] at g1 q1
  rw [u2_0, u2_1, u2_2] at g2 q2
  have hb0 : t (1, 0) = -t (0, 0) := by linear_combination (e1 - 2 * (g1 - e2) - (g2 - e2)) / 3
  have hb1 : t (1, 1) = -t (0, 1) := by linear_combination (e1 + (g1 - e2) - (g2 - e2)) / 3
  have hb2 : t (1, 2) = -t (0, 2) := by linear_combination (e1 + (g1 - e2) + 2 * (g2 - e2)) / 3
  rw [hb0, hb1, hb2] at e2 q1 q2
  refine ⟨hb0, hb1, hb2, ?_, ?_, ?_⟩
  · linear_combination (-e2 + q1 + 2 * q2) / 6
  · linear_combination (-e2 + q1 - q2) / 6
  · linear_combination (-e2 - 2 * q1 - q2) / 6

lemma crossz (p q p' q' : ℂ) (h1 : p * q = 0) (h2 : p' * q' = 0) (h3 : (p + p') * (q + q') = 0) :
    p * q' = q * p' := by
  have k1 : (p * q') ^ 2 = 0 := by
    linear_combination (p * q') * (h3 - h1 - h2) - (p' * q') * h1
  have k2 : (q * p') ^ 2 = 0 := by
    linear_combination (q * p') * (h3 - h1 - h2) - (p' * q') * h1
  rw [pow_eq_zero_iff two_ne_zero |>.mp k1, pow_eq_zero_iff two_ne_zero |>.mp k2]

lemma P2 (L : Submodule ℂ (Fin 2 × Fin 3 → ℂ))
    (hF : ∀ t ∈ L, t (1, 0) = -t (0, 0) ∧ t (1, 1) = -t (0, 1) ∧ t (1, 2) = -t (0, 2) ∧
      t (0, 0) * t (0, 1) = 0 ∧ t (0, 0) * t (0, 2) = 0 ∧ t (0, 1) * t (0, 2) = 0) :
    Module.finrank ℂ L ≤ 1 := by
  refine dim_le_one4 L (ev (0, 0)) (ev (0, 1)) (ev (0, 2)) (ev (0, 2)) ?_ ?_
  · intro t ht h1 h2 h3 _
    obtain ⟨hb0, hb1, hb2, -, -, -⟩ := hF t ht
    have z1 : t (0, 0) = 0 := h1
    have z2 : t (0, 1) = 0 := h2
    have z3 : t (0, 2) = 0 := h3
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j
    · exact z1
    · exact z2
    · exact z3
    · show t (1, 0) = 0
      rw [hb0, z1, neg_zero]
    · show t (1, 1) = 0
      rw [hb1, z2, neg_zero]
    · show t (1, 2) = 0
      rw [hb2, z3, neg_zero]
  · intro t ht s hs
    obtain ⟨-, -, -, p01, p02, p12⟩ := hF t ht
    obtain ⟨-, -, -, r01, r02, r12⟩ := hF s hs
    obtain ⟨-, -, -, w01, w02, w12⟩ := hF (t + s) (L.add_mem ht hs)
    simp only [Pi.add_apply] at w01 w02 w12
    have m01 := crossz _ _ _ _ p01 r01 w01
    have m02 := crossz _ _ _ _ p02 r02 w02
    have m12 := crossz _ _ _ _ p12 r12 w12
    exact ⟨m01, m02, m02, m12, m12, rfl⟩

lemma P3 (L : Submodule ℂ (Fin 2 × Fin 3 → ℂ)) (Y : Submodule ℂ (Fin 2 → ℂ)) (E2 : ∀ t ∈ L, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) = 0) (K2 : ∀ t ∈ L, ∀ y ∈ Y, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) + (t (0, 0) + t (0, 1) + t (0, 2)) * y 1 + y 0 * (t (1, 0) + t (1, 1) + t (1, 2)) = 0) (hYs : ∀ y ∈ Y, y 0 + y 1 = 0)
    (hF : ∀ t ∈ L, t (1, 0) = -t (0, 0) ∧ t (1, 1) = -t (0, 1) ∧ t (1, 2) = -t (0, 2) ∧
      t (0, 0) * t (0, 1) = 0 ∧ t (0, 0) * t (0, 2) = 0 ∧ t (0, 1) * t (0, 2) = 0)
    (y : Fin 2 → ℂ) (hy : y ∈ Y) (hy0 : y ≠ 0) : Module.finrank ℂ L = 0 := by
  have ys := hYs y hy
  have hy00 : y 0 ≠ 0 := by
    intro h
    apply hy0
    funext i
    fin_cases i
    · exact h
    · show y 1 = 0
      linear_combination ys - h
  refine zero_dim L ?_
  intro t ht
  obtain ⟨hb0, hb1, hb2, p01, p02, p12⟩ := hF t ht
  have k := K2 t ht y hy
  have e2 := E2 t ht
  rw [hb0, hb1, hb2] at k e2
  have hR' : y 0 * (t (0, 0) + t (0, 1) + t (0, 2)) = 0 := by
    linear_combination (-(k - e2) + (t (0, 0) + t (0, 1) + t (0, 2)) * ys) / 2
  have hR := (mul_eq_zero.mp hR').resolve_left hy00
  have s0 : t (0, 0) ^ 2 = 0 := by linear_combination t (0, 0) * hR - p01 - p02
  have s1 : t (0, 1) ^ 2 = 0 := by linear_combination t (0, 1) * hR - p01 - p12
  have s2 : t (0, 2) ^ 2 = 0 := by linear_combination t (0, 2) * hR - p02 - p12
  have z0 := pow_eq_zero_iff two_ne_zero |>.mp s0
  have z1 := pow_eq_zero_iff two_ne_zero |>.mp s1
  have z2 := pow_eq_zero_iff two_ne_zero |>.mp s2
  funext ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · exact z0
  · exact z1
  · exact z2
  · show t (1, 0) = 0
    rw [hb0, z0, neg_zero]
  · show t (1, 1) = 0
    rw [hb1, z1, neg_zero]
  · show t (1, 2) = 0
    rw [hb2, z2, neg_zero]

lemma main_aux (L : Submodule ℂ (Fin 2 × Fin 3 → ℂ)) (X : Submodule ℂ (Fin 3 → ℂ)) (Y : Submodule ℂ (Fin 2 → ℂ)) (E1 : ∀ t ∈ L, t (0, 0) + t (1, 0) + (t (0, 1) + t (1, 1)) + (t (0, 2) + t (1, 2)) = 0) (E2 : ∀ t ∈ L, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) = 0) (G2 : ∀ t ∈ L, ∀ x ∈ X, (t (0, 0) * t (1, 1) + t (0, 0) * x 1 + t (1, 0) * x 1) + (t (0, 0) * t (1, 2) + t (0, 0) * x 2 + t (1, 0) * x 2) + (t (0, 1) * t (1, 0) + t (0, 1) * x 0 + t (1, 1) * x 0) + (t (0, 1) * t (1, 2) + t (0, 1) * x 2 + t (1, 1) * x 2) + (t (0, 2) * t (1, 0) + t (0, 2) * x 0 + t (1, 2) * x 0) + (t (0, 2) * t (1, 1) + t (0, 2) * x 1 + t (1, 2) * x 1) = 0) (G3 : ∀ t ∈ L, ∀ x ∈ X, t (0, 0) * t (1, 1) * x 2 + t (0, 0) * t (1, 2) * x 1 + t (0, 1) * t (1, 0) * x 2 + t (0, 1) * t (1, 2) * x 0 + t (0, 2) * t (1, 0) * x 1 + t (0, 2) * t (1, 1) * x 0 = 0) (K2 : ∀ t ∈ L, ∀ y ∈ Y, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) + (t (0, 0) + t (0, 1) + t (0, 2)) * y 1 + y 0 * (t (1, 0) + t (1, 1) + t (1, 2)) = 0) (hXs : ∀ x ∈ X, x 0 + x 1 + x 2 = 0) (hYs : ∀ y ∈ Y, y 0 + y 1 = 0) :
    Module.finrank ℂ L + Module.finrank ℂ X + Module.finrank ℂ Y ≤ 3 := by
  have dA := dimA L E1 E2
  have dX := dimX X hXs
  have dY := dimY Y hYs
  by_cases hY : ∀ y ∈ Y, y = 0
  · have dY0 := zero_dim Y hY
    by_cases hX2 : Module.finrank ℂ X ≤ 1
    · omega
    · obtain ⟨m1, m2⟩ := full_X X hXs (by omega)
      have := P2 L (P2f L X E1 E2 G2 G3 m1 m2)
      omega
  · rw [not_forall] at hY
    obtain ⟨y, hy⟩ := hY
    rw [Classical.not_imp] at hy
    obtain ⟨hy, hy0⟩ := hy
    by_cases hX : ∀ x ∈ X, x = 0
    · have dX0 := zero_dim X hX
      omega
    · rw [not_forall] at hX
      obtain ⟨x, hx⟩ := hX
      rw [Classical.not_imp] at hx
      obtain ⟨hx, hx0⟩ := hx
      by_cases hX2 : Module.finrank ℂ X ≤ 1
      · have := P1 L X Y E1 E2 G2 G3 K2 hXs hYs x hx hx0 y hy hy0
        omega
      · obtain ⟨m1, m2⟩ := full_X X hXs (by omega)
        have := P3 L Y E2 K2 hYs (P2f L X E1 E2 G2 G3 m1 m2) y hy hy0
        omega

end PEqualNP.Outside.L_gct_213_aux

open PEqualNP.Outside.L_gct_213_aux in
theorem PEqualNP.Outside.L_gct_213 : ∀ (L : Submodule ℂ (Fin 2 × Fin 3 → ℂ)) (X : Submodule ℂ (Fin 3 → ℂ)) (Y : Submodule ℂ (Fin 2 → ℂ)), (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) → (∀ t ∈ L, ∀ x ∈ X, (∑ j, (t (0, j) + t (1, j) + x j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l) + t (0, j) * x l + t (1, j) * x l) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * x m) = 0) → (∀ t ∈ L, ∀ y ∈ Y, (∑ j, (t (0, j) + t (1, j))) + y 0 + y 1 = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) + (∑ j, t (0, j)) * y 1 + y 0 * (∑ j, t (1, j)) = 0) → Module.finrank ℂ L + Module.finrank ℂ X + Module.finrank ℂ Y ≤ 3 := by
  intro L X Y hL hLX hLY
  have E1 : ∀ t ∈ L, t (0, 0) + t (1, 0) + (t (0, 1) + t (1, 1)) + (t (0, 2) + t (1, 2)) = 0 := by
    intro t ht
    have h := (hL t ht).1
    rw [sumA] at h
    exact h
  have E2 : ∀ t ∈ L, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) = 0 := by
    intro t ht
    have h := (hL t ht).2
    rw [sumP2] at h
    exact h
  have hXs : ∀ x ∈ X, x 0 + x 1 + x 2 = 0 := by
    intro x hx
    have h := (hLX 0 L.zero_mem x hx).1
    rw [sumAx] at h
    simp only [Pi.zero_apply] at h
    linear_combination h
  have hYs : ∀ y ∈ Y, y 0 + y 1 = 0 := by
    intro y hy
    have h := (hLY 0 L.zero_mem y hy).1
    rw [sumA] at h
    simp only [Pi.zero_apply] at h
    linear_combination h
  have G2 : ∀ t ∈ L, ∀ x ∈ X, (t (0, 0) * t (1, 1) + t (0, 0) * x 1 + t (1, 0) * x 1) + (t (0, 0) * t (1, 2) + t (0, 0) * x 2 + t (1, 0) * x 2) + (t (0, 1) * t (1, 0) + t (0, 1) * x 0 + t (1, 1) * x 0) + (t (0, 1) * t (1, 2) + t (0, 1) * x 2 + t (1, 1) * x 2) + (t (0, 2) * t (1, 0) + t (0, 2) * x 0 + t (1, 2) * x 0) + (t (0, 2) * t (1, 1) + t (0, 2) * x 1 + t (1, 2) * x 1) = 0 := by
    intro t ht x hx
    have h := (hLX t ht x hx).2.1
    rw [sumG2] at h
    exact h
  have G3 : ∀ t ∈ L, ∀ x ∈ X, t (0, 0) * t (1, 1) * x 2 + t (0, 0) * t (1, 2) * x 1 + t (0, 1) * t (1, 0) * x 2 + t (0, 1) * t (1, 2) * x 0 + t (0, 2) * t (1, 0) * x 1 + t (0, 2) * t (1, 1) * x 0 = 0 := by
    intro t ht x hx
    have h := (hLX t ht x hx).2.2
    rw [sumG3] at h
    exact h
  have K2 : ∀ t ∈ L, ∀ y ∈ Y, t (0, 0) * t (1, 1) + t (0, 0) * t (1, 2) + t (0, 1) * t (1, 0) + t (0, 1) * t (1, 2) + t (0, 2) * t (1, 0) + t (0, 2) * t (1, 1) + (t (0, 0) + t (0, 1) + t (0, 2)) * y 1 + y 0 * (t (1, 0) + t (1, 1) + t (1, 2)) = 0 := by
    intro t ht y hy
    have h := (hLY t ht y hy).2
    rw [sumP2, sumR0, sumR1] at h
    exact h
  exact main_aux L X Y E1 E2 G2 G3 K2 hXs hYs
