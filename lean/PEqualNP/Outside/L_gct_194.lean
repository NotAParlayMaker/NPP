import PEqualNP.Defs
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem PEqualNP.Outside.L_gct_194 :
    ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  have sumPerm4 : ∀ (f : Equiv.Perm (Fin 4) → ℂ), ∑ σ, f σ =
      ∑ a : Fin 4, ∑ b : Fin 3, ∑ x : Fin 2, ∑ y : Fin 1,
        f (Equiv.Perm.decomposeFin.symm (a, Equiv.Perm.decomposeFin.symm (b,
          Equiv.Perm.decomposeFin.symm (x, Equiv.Perm.decomposeFin.symm (y, 1))))) := by
    intro f
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Fintype.sum_unique]
    rfl
  have key : ∀ F : ℕ → ℕ → ℕ → ℕ → ℂ,
      ∑ σ : Equiv.Perm (Fin 4), F (σ 0).val (σ 1).val (σ 2).val (σ 3).val =
      (((F 0 1 2 3 + F 0 1 3 2) + ((F 0 2 1 3 + F 0 2 3 1) + (F 0 3 2 1 + F 0 3 1 2))) +
      (((F 1 0 2 3 + F 1 0 3 2) + ((F 1 2 0 3 + F 1 2 3 0) + (F 1 3 2 0 + F 1 3 0 2))) +
      (((F 2 1 0 3 + F 2 1 3 0) + ((F 2 0 1 3 + F 2 0 3 1) + (F 2 3 0 1 + F 2 3 1 0))) +
      ((F 3 1 2 0 + F 3 1 0 2) + ((F 3 2 1 0 + F 3 2 0 1) + (F 3 0 2 1 + F 3 0 1 2)))))) := by
    intro F
    rw [sumPerm4]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rfl
  have perm4_eq : ∀ M : ℕ → ℕ → ℂ,
      (∑ σ : Equiv.Perm (Fin 4), M (σ 0).val 0 * M (σ 1).val 1 * M (σ 2).val 2 * M (σ 3).val 3) =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 + M 3 2 * M 2 3) +
               M 2 1 * (M 1 2 * M 3 3 + M 3 2 * M 1 3) +
               M 3 1 * (M 1 2 * M 2 3 + M 2 2 * M 1 3)) +
      M 1 0 * (M 0 1 * (M 2 2 * M 3 3 + M 3 2 * M 2 3) +
               M 2 1 * (M 0 2 * M 3 3 + M 3 2 * M 0 3) +
               M 3 1 * (M 0 2 * M 2 3 + M 2 2 * M 0 3)) +
      M 2 0 * (M 1 1 * (M 0 2 * M 3 3 + M 3 2 * M 0 3) +
               M 0 1 * (M 1 2 * M 3 3 + M 3 2 * M 1 3) +
               M 3 1 * (M 0 2 * M 1 3 + M 1 2 * M 0 3)) +
      M 3 0 * (M 1 1 * (M 0 2 * M 2 3 + M 2 2 * M 0 3) +
               M 2 1 * (M 0 2 * M 1 3 + M 1 2 * M 0 3) +
               M 0 1 * (M 1 2 * M 2 3 + M 2 2 * M 1 3)) := by
    intro M
    rw [key (fun a b x y => M a 0 * M b 1 * M x 2 * M y 3)]
    ring
  let eFun : Fin 5 × Equiv.Perm (Fin 4) → (Fin 4 ↪ Fin 5) :=
    fun p => p.2.toEmbedding.trans (Fin.succAboveEmb p.1)
  have heInj : Function.Injective eFun := by
    rintro ⟨k₁, σ₁⟩ ⟨k₂, σ₂⟩ h
    have hk : k₁ = k₂ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne
      have h1 : eFun (k₁, σ₁) (σ₂.symm i) = eFun (k₂, σ₂) (σ₂.symm i) := by rw [h]
      simp only [eFun, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
        Fin.succAboveEmb_apply, Equiv.apply_symm_apply, hi] at h1
      exact Fin.succAbove_ne k₁ (σ₁ (σ₂.symm i)) h1
    subst hk
    have hσ : σ₁ = σ₂ := by
      ext j
      have h1 : eFun (k₁, σ₁) j = eFun (k₁, σ₂) j := by rw [h]
      simp only [eFun, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
        Fin.succAboveEmb_apply] at h1
      exact congrArg Fin.val (Fin.succAbove_right_injective h1)
    rw [hσ]
  have heBij : Function.Bijective eFun := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨heInj, ?_⟩
    simp only [Fintype.card_prod, Fintype.card_perm, Fintype.card_embedding_eq, Fintype.card_fin]
    decide
  let embEquiv : Fin 5 × Equiv.Perm (Fin 4) ≃ (Fin 4 ↪ Fin 5) := Equiv.ofBijective eFun heBij
  intro c d
  let T : ℕ → ℕ → ℂ := fun r j =>
    1 + (if r = 4 then d * (if j = 0 then (1 : ℂ) else if j = 1 then -1 else 0)
      else c * (if j = r then (1 : ℂ) else if j = (r + 1) % 4 then Complex.I
        else if j = (r + 2) % 4 then -Complex.I else -1))
  change (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, T (f j).val j.val) = 120
  rw [← Equiv.sum_comp embEquiv, Fintype.sum_prod_type]
  have hval : ∀ k : Fin 5, ∀ σ : Equiv.Perm (Fin 4),
      (∏ j : Fin 4, T (embEquiv (k, σ) j).val j.val) =
        T (k.succAbove (σ 0)).val 0 * T (k.succAbove (σ 1)).val 1 *
        T (k.succAbove (σ 2)).val 2 * T (k.succAbove (σ 3)).val 3 := by
    intro k σ
    simp only [Fin.prod_univ_four, embEquiv, Equiv.ofBijective_apply, eFun,
      Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Fin.succAboveEmb_apply]
    rfl
  simp_rw [hval]
  rw [Fin.sum_univ_five]
  have t00 : T 0 0 = 1 + c := by simp only [T]; norm_num
  have t01 : T 0 1 = 1 + c * Complex.I := by simp only [T]; norm_num
  have t02 : T 0 2 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t03 : T 0 3 = 1 + c * (-1) := by simp only [T]; norm_num
  have t10 : T 1 0 = 1 + c * (-1) := by simp only [T]; norm_num
  have t11 : T 1 1 = 1 + c := by simp only [T]; norm_num
  have t12 : T 1 2 = 1 + c * Complex.I := by simp only [T]; norm_num
  have t13 : T 1 3 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t20 : T 2 0 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t21 : T 2 1 = 1 + c * (-1) := by simp only [T]; norm_num
  have t22 : T 2 2 = 1 + c := by simp only [T]; norm_num
  have t23 : T 2 3 = 1 + c * Complex.I := by simp only [T]; norm_num
  have t30 : T 3 0 = 1 + c * Complex.I := by simp only [T]; norm_num
  have t31 : T 3 1 = 1 + c * (-Complex.I) := by simp only [T]; norm_num
  have t32 : T 3 2 = 1 + c * (-1) := by simp only [T]; norm_num
  have t33 : T 3 3 = 1 + c := by simp only [T]; norm_num
  have t40 : T 4 0 = 1 + d := by simp only [T]; norm_num
  have t41 : T 4 1 = 1 - d := by simp only [T]; norm_num; ring
  have t42 : T 4 2 = 1 := by simp only [T]; norm_num
  have t43 : T 4 3 = 1 := by simp only [T]; norm_num
  have p01 : T 0 2 * T 1 3 + T 1 2 * T 0 3 = 2 - c - c * Complex.I - c ^ 2 - c ^ 2 * Complex.I := by
    rw [t02, t13, t12, t03]; linear_combination c ^ 2 * Complex.I_sq
  have p02 : T 0 2 * T 2 3 + T 2 2 * T 0 3 = 2 := by
    rw [t02, t23, t22, t03]; linear_combination (-c ^ 2) * Complex.I_sq
  have p03 : T 0 2 * T 3 3 + T 3 2 * T 0 3 = 2 - c - c * Complex.I + c ^ 2 - c ^ 2 * Complex.I := by
    rw [t02, t33, t32, t03]; ring
  have p04 : T 0 2 * T 4 3 + T 4 2 * T 0 3 = 2 - c - c * Complex.I := by
    rw [t02, t43, t42, t03]; ring
  have p12 : T 1 2 * T 2 3 + T 2 2 * T 1 3 = 2 + c + c * Complex.I - c ^ 2 - c ^ 2 * Complex.I := by
    rw [t12, t23, t22, t13]; linear_combination c ^ 2 * Complex.I_sq
  have p13 : T 1 2 * T 3 3 + T 3 2 * T 1 3 = 2 + 2 * c ^ 2 * Complex.I := by
    rw [t12, t33, t32, t13]; ring
  have p14 : T 1 2 * T 4 3 + T 4 2 * T 1 3 = 2 := by
    rw [t12, t43, t42, t13]; ring
  have p23 : T 2 2 * T 3 3 + T 3 2 * T 2 3 = 2 + c + c * Complex.I + c ^ 2 - c ^ 2 * Complex.I := by
    rw [t22, t33, t32, t23]; ring
  have p24 : T 2 2 * T 4 3 + T 4 2 * T 2 3 = 2 + c + c * Complex.I := by
    rw [t22, t43, t42, t23]; ring
  have p34 : T 3 2 * T 4 3 + T 4 2 * T 3 3 = 2 := by
    rw [t32, t43, t42, t33]; ring
  let m0 : ℕ → ℕ := fun | 0 => 1 | 1 => 2 | 2 => 3 | _ => 4
  let m1 : ℕ → ℕ := fun | 0 => 0 | 1 => 2 | 2 => 3 | _ => 4
  let m2 : ℕ → ℕ := fun | 0 => 0 | 1 => 1 | 2 => 3 | _ => 4
  let m3 : ℕ → ℕ := fun | 0 => 0 | 1 => 1 | 2 => 2 | _ => 4
  let m4 : ℕ → ℕ := fun | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3
  have hm0 : ∀ a : Fin 4, ((0 : Fin 5).succAbove a).val = m0 a.val := by
    intro a; fin_cases a <;> rfl
  have hm1 : ∀ a : Fin 4, ((1 : Fin 5).succAbove a).val = m1 a.val := by
    intro a; fin_cases a <;> rfl
  have hm2 : ∀ a : Fin 4, ((2 : Fin 5).succAbove a).val = m2 a.val := by
    intro a; fin_cases a <;> rfl
  have hm3 : ∀ a : Fin 4, ((3 : Fin 5).succAbove a).val = m3 a.val := by
    intro a; fin_cases a <;> rfl
  have hm4 : ∀ a : Fin 4, ((4 : Fin 5).succAbove a).val = m4 a.val := by
    intro a; fin_cases a <;> rfl
  have h0 : ∑ σ : Equiv.Perm (Fin 4),
      T ((0 : Fin 5).succAbove (σ 0)).val 0 * T ((0 : Fin 5).succAbove (σ 1)).val 1 *
      T ((0 : Fin 5).succAbove (σ 2)).val 2 * T ((0 : Fin 5).succAbove (σ 3)).val 3 =
      24 + 2 * c * d - 2 * c * d * Complex.I + 4 * c ^ 2 * d - 2 * c ^ 3 * d -
      2 * c ^ 3 * d * Complex.I := by
    simp_rw [hm0]
    rw [perm4_eq (fun r j => T (m0 r) j)]
    simp only [m0, p12, p13, p14, p23, p24, p34, t10, t11, t20, t21, t30, t31, t40, t41]
    linear_combination (2 * c ^ 2 - 2 * c ^ 2 * d + 4 * c ^ 3 * d) * Complex.I_sq
  have h1 : ∑ σ : Equiv.Perm (Fin 4),
      T ((1 : Fin 5).succAbove (σ 0)).val 0 * T ((1 : Fin 5).succAbove (σ 1)).val 1 *
      T ((1 : Fin 5).succAbove (σ 2)).val 2 * T ((1 : Fin 5).succAbove (σ 3)).val 3 =
      24 - 4 * c * d + 4 * c ^ 3 * d * Complex.I := by
    simp_rw [hm1]
    rw [perm4_eq (fun r j => T (m1 r) j)]
    simp only [m1, p02, p03, p04, p23, p24, p34, t00, t01, t20, t21, t30, t31, t40, t41]
    linear_combination (6 * c ^ 2 - 2 * c ^ 3 * d) * Complex.I_sq
  have h2 : ∑ σ : Equiv.Perm (Fin 4),
      T ((2 : Fin 5).succAbove (σ 0)).val 0 * T ((2 : Fin 5).succAbove (σ 1)).val 1 *
      T ((2 : Fin 5).succAbove (σ 2)).val 2 * T ((2 : Fin 5).succAbove (σ 3)).val 3 =
      24 + 2 * c * d - 2 * c * d * Complex.I - 4 * c ^ 2 * d - 2 * c ^ 3 * d -
      2 * c ^ 3 * d * Complex.I := by
    simp_rw [hm2]
    rw [perm4_eq (fun r j => T (m2 r) j)]
    simp only [m2, p01, p03, p04, p13, p14, p34, t00, t01, t10, t11, t30, t31, t40, t41]
    linear_combination (2 * c ^ 2 + 2 * c ^ 2 * d + 4 * c ^ 3 * d) * Complex.I_sq
  have h3 : ∑ σ : Equiv.Perm (Fin 4),
      T ((3 : Fin 5).succAbove (σ 0)).val 0 * T ((3 : Fin 5).succAbove (σ 1)).val 1 *
      T ((3 : Fin 5).succAbove (σ 2)).val 2 * T ((3 : Fin 5).succAbove (σ 3)).val 3 =
      24 + 4 * c * d * Complex.I + 4 * c ^ 3 * d := by
    simp_rw [hm3]
    rw [perm4_eq (fun r j => T (m3 r) j)]
    simp only [m3, p01, p02, p04, p12, p14, p24, t00, t01, t10, t11, t20, t21, t40, t41]
    linear_combination (2 * c ^ 2 - 2 * c ^ 3 * d) * Complex.I_sq
  have h4 : ∑ σ : Equiv.Perm (Fin 4),
      T ((4 : Fin 5).succAbove (σ 0)).val 0 * T ((4 : Fin 5).succAbove (σ 1)).val 1 *
      T ((4 : Fin 5).succAbove (σ 2)).val 2 * T ((4 : Fin 5).succAbove (σ 3)).val 3 = 24 := by
    simp_rw [hm4]
    rw [perm4_eq (fun r j => T (m4 r) j)]
    simp only [m4, p01, p02, p03, p12, p13, p23, t00, t01, t10, t11, t20, t21, t30, t31]
    linear_combination (6 * c ^ 2 + 2 * c ^ 4 - 4 * c ^ 4 * Complex.I) * Complex.I_sq
  rw [h0, h1, h2, h3, h4]
  ring
