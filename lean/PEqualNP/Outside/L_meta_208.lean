import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_208_aux

open PEqualNP.MetaComplexity

private def f2 : (Fin 2 → Bool) → Bool := fun x => x 0 && x 1

private def tt : Fin 2 → Bool := ![true, true]
private def ft : Fin 2 → Bool := ![false, true]
private def tf : Fin 2 → Bool := ![true, false]

private lemma f2_tt : f2 tt = true := by decide
private lemma f2_ft : f2 ft = false := by decide
private lemma f2_tf : f2 tf = false := by decide

private lemma f2_true (x : Fin 2 → Bool) (h : f2 x = true) : x 0 = true ∧ x 1 = true := by
  simp [f2] at h; exact h

private lemma rank_single_row {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (M : Matrix α β ℚ) (r : α) (hM : ∀ x y, M x y ≠ 0 → x = r) : M.rank ≤ 1 := by
  have hpq : (Matrix.of fun x (_ : Unit) => if x = r then (1:ℚ) else 0) *
      (Matrix.of fun (_ : Unit) (y : β) => M r y) = M := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.univ_unique, Finset.sum_singleton]
    by_cases hx : x = r
    · simp [hx]
    · have h0 : M x y = 0 := by
        by_contra hne
        exact hx (hM x y hne)
      simp [hx, h0]
  calc M.rank = ((Matrix.of fun x (_ : Unit) => if x = r then (1:ℚ) else 0) *
      (Matrix.of fun (_ : Unit) (y : β) => M r y)).rank := by rw [hpq]
    _ ≤ (Matrix.of fun (_ : Unit) (y : β) => M r y).rank :=
        Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card Unit := Matrix.rank_le_card_height _
    _ = 1 := by decide

private def smulC {α : Type} (c : α → ℚ) : (Fin 1 → ℚ) →ₗ[ℚ] (α → ℚ) where
  toFun w := w 0 • c
  map_add' u v := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul]
    ring
  map_smul' a u := by
    funext z
    simp only [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_smul, RingHom.id_apply]
    ring

private lemma rank_pos_of_entry {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix α β ℚ) (x₀ : α) (y₀ : β) (h : M x₀ y₀ ≠ 0) : 1 ≤ M.rank := by
  have hcx : M.mulVec (Pi.single y₀ (1 : ℚ)) x₀ = M x₀ y₀ := by
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [Finset.sum_eq_single y₀]
    · rw [if_pos rfl, mul_one]
    · intro y _ hy
      rw [if_neg hy, mul_zero]
    · intro hy
      exact absurd (Finset.mem_univ y₀) hy
  have hcne : M.mulVec (Pi.single y₀ (1 : ℚ)) ≠ 0 := by
    intro hz
    apply h
    have hxz := congrFun hz x₀
    rw [hcx] at hxz
    exact hxz
  have hinj : Function.Injective (smulC (M.mulVec (Pi.single y₀ (1 : ℚ)))) := by
    rintro u v hv
    funext k
    fin_cases k
    have hx₀ : u 0 * M.mulVec (Pi.single y₀ (1 : ℚ)) x₀ =
        v 0 * M.mulVec (Pi.single y₀ (1 : ℚ)) x₀ := by
      have hz := congrFun hv x₀
      simp only [smulC, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul] at hz
      exact hz
    rw [hcx] at hx₀
    have huv : u 0 = v 0 := by
      have e : (u 0 - v 0) * M x₀ y₀ = 0 := by
        linear_combination hx₀
      rcases mul_eq_zero.mp e with hs | hr
      · exact sub_eq_zero.mp hs
      · exact absurd hr h
    exact huv
  have hrng : LinearMap.range (smulC (M.mulVec (Pi.single y₀ (1 : ℚ)))) ≤
      LinearMap.range M.mulVecLin := by
    rintro w ⟨u, rfl⟩
    refine ⟨u 0 • Pi.single y₀ (1 : ℚ), ?_⟩
    have h1 : M.mulVecLin (u 0 • Pi.single y₀ (1 : ℚ)) =
        u 0 • M.mulVecLin (Pi.single y₀ (1 : ℚ)) := map_smul _ _ _
    rw [h1]
    simp only [Matrix.mulVecLin_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rfl
  have h1 : Module.finrank ℚ (LinearMap.range (smulC (M.mulVec (Pi.single y₀ (1 : ℚ))))) = 1 := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  have h2 : Module.finrank ℚ (LinearMap.range (smulC (M.mulVec (Pi.single y₀ (1 : ℚ))))) ≤
      Module.finrank ℚ (LinearMap.range M.mulVecLin) := Submodule.finrank_mono hrng
  show 1 ≤ Module.finrank ℚ (LinearMap.range M.mulVecLin)
  omega

private def tau : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ := fun x y => if x 0 = y 0 then 1 else 0

private lemma tau_is_typing : IsTyping 2 f2 tau := by
  intro x y hx hy
  have hxt := f2_true x hx
  rcases hb0 : y 0 <;> rcases hb1 : y 1
  · exact ⟨0, by simp [tau, hxt.1, hb0], by simp [hxt.1, hb0]⟩
  · exact ⟨0, by simp [tau, hxt.1, hb0], by simp [hxt.1, hb0]⟩
  · exact ⟨1, by simp [tau, hxt.1, hb0], by simp [hxt.2, hb1]⟩
  · exact absurd hy (by simp [f2, hb0, hb1])

private lemma mat_bfalse_zero (i : Fin 2) : typedMatrix 2 f2 tau i false = 0 := by
  ext x y
  by_cases hf : f2 x = true
  · have h2 := f2_true x hf
    have hxi : x i = true := by
      fin_cases i <;> simp [h2.1, h2.2]
    show (if f2 x = true ∧ f2 y = false ∧ tau x y = ((i : Fin 2) : ℕ) ∧ x i = false then (1:ℚ) else 0) = 0
    rw [if_neg]
    intro hc
    rw [hxi] at hc
    exact absurd hc.2.2.2 (by simp)
  · show (if f2 x = true ∧ f2 y = false ∧ tau x y = ((i : Fin 2) : ℕ) ∧ x i = false then (1:ℚ) else 0) = 0
    rw [if_neg]
    intro hc
    exact absurd hc.1 hf

private lemma mat_btrue_row (i : Fin 2) (x y : Fin 2 → Bool)
    (h : typedMatrix 2 f2 tau i true x y ≠ 0) : x = tt := by
  simp only [typedMatrix, Matrix.of_apply] at h
  by_cases hc : f2 x = true ∧ f2 y = false ∧ tau x y = ((i : Fin 2) : ℕ) ∧ x i = true
  · have h2 := f2_true x hc.1
    funext k
    fin_cases k <;> simp [tt, h2.1, h2.2]
  · rw [if_neg hc] at h
    exact absurd rfl h

private lemma upper_sum :
    (∑ i : Fin 2, ∑ b : Bool, (typedMatrix 2 f2 tau i b).rank) ≤ 2 := by
  have h00 : (typedMatrix 2 f2 tau 0 false).rank = 0 := by
    rw [mat_bfalse_zero 0, Matrix.rank_zero]
  have h10 : (typedMatrix 2 f2 tau 1 false).rank = 0 := by
    rw [mat_bfalse_zero 1, Matrix.rank_zero]
  have h01 : (typedMatrix 2 f2 tau 0 true).rank ≤ 1 :=
    rank_single_row _ tt (mat_btrue_row 0)
  have h11 : (typedMatrix 2 f2 tau 1 true).rank ≤ 1 :=
    rank_single_row _ tt (mat_btrue_row 1)
  simp only [Fin.sum_univ_two, Fintype.sum_bool]
  omega

private lemma pair_ft_forces (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ) (hτ : IsTyping 2 f2 τ) :
    typedMatrix 2 f2 τ 0 true tt ft = 1 ∧ τ tt ft = 0 := by
  obtain ⟨i, hi, hne⟩ := hτ tt ft f2_tt f2_ft
  fin_cases i
  · refine ⟨?_, hi⟩
    show (if f2 tt = true ∧ f2 ft = false ∧ τ tt ft = ((0 : Fin 2) : ℕ) ∧ tt 0 = true then (1:ℚ) else 0) = 1
    rw [if_pos ⟨f2_tt, f2_ft, hi, by simp [tt]⟩]
  · simp [tt, ft] at hne

private lemma pair_tf_forces (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ) (hτ : IsTyping 2 f2 τ) :
    typedMatrix 2 f2 τ 1 true tt tf = 1 ∧ τ tt tf = 1 := by
  obtain ⟨i, hi, hne⟩ := hτ tt tf f2_tt f2_tf
  fin_cases i
  · simp [tt, tf] at hne
  · refine ⟨?_, hi⟩
    show (if f2 tt = true ∧ f2 tf = false ∧ τ tt tf = ((1 : Fin 2) : ℕ) ∧ tt 1 = true then (1:ℚ) else 0) = 1
    rw [if_pos ⟨f2_tt, f2_tf, hi, by simp [tt]⟩]

private lemma lower_absurd (τ : (Fin 2 → Bool) → (Fin 2 → Bool) → ℕ) (hτ : IsTyping 2 f2 τ)
    (hsum : (∑ i : Fin 2, ∑ b : Bool, (typedMatrix 2 f2 τ i b).rank) ≤ 1) : False := by
  have e1 := (pair_ft_forces τ hτ).1
  have r1 : 1 ≤ (typedMatrix 2 f2 τ 0 true).rank := by
    refine rank_pos_of_entry _ tt ft ?_
    rw [e1]; norm_num
  have e2 := (pair_tf_forces τ hτ).1
  have r2 : 1 ≤ (typedMatrix 2 f2 τ 1 true).rank := by
    refine rank_pos_of_entry _ tt tf ?_
    rw [e2]; norm_num
  simp only [Fin.sum_univ_two, Fintype.sum_bool] at hsum
  omega

theorem witness :
    PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 2 ∧
      ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 1 := by
  constructor
  · exact ⟨tau, tau_is_typing, upper_sum⟩
  · rintro ⟨τ, hτ, hsum⟩
    exact lower_absurd τ hτ hsum

end PEqualNP.Outside.L_meta_208_aux

theorem PEqualNP.Outside.L_meta_208 : PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 2 ∧
    ¬ PEqualNP.MetaComplexity.HasTypedRank 2 (fun x => x 0 && x 1) 1 :=
  PEqualNP.Outside.L_meta_208_aux.witness
