import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatFromKneser

namespace PEqualNP.Outside.Gct122

open Module Finset PEqualNP.Gct.Helpers

section General

variable {ι : Type} [Fintype ι]

/-- The polarized hypotheses: `W` is isotropic for the dot product and for the quadrilinear
form `∑ u_i v_i z_i w_i`. -/
def QIso (W : Submodule ℂ (ι → ℂ)) : Prop :=
  (∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0) ∧
    (∀ u ∈ W, ∀ v ∈ W, ∀ z ∈ W, ∀ w ∈ W, ∑ i, u i * v i * z i * w i = 0)

theorem sq_perp_one {W : Submodule ℂ (ι → ℂ)} (hW : QIso W) :
    ∀ q ∈ W * W, ∑ i, q i = 0 := by
  intro q hq
  refine Submodule.mul_induction_on hq ?_ ?_
  · intro u hu v hv
    simpa only [Pi.mul_apply] using hW.1 u hu v hv
  · intro a b ha hb
    simp only [Pi.add_apply, sum_add_distrib, ha, hb, add_zero]

theorem sq_perp_sq {W : Submodule ℂ (ι → ℂ)} (hW : QIso W) :
    ∀ q ∈ W * W, ∀ r ∈ W * W, ∑ i, q i * r i = 0 := by
  intro q hq
  refine Submodule.mul_induction_on hq ?_ ?_
  · intro u hu v hv r hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro z hz w hw
      have := hW.2 u hu v hv z hz w hw
      simpa only [Pi.mul_apply, mul_assoc] using this
    · intro a b ha hb
      simp only [Pi.add_apply, mul_add, sum_add_distrib, ha, hb, add_zero]
  · intro a b ha hb r hr
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha r hr, hb r hr, add_zero]

/-- The restriction of `W` along a 0/1 element of the stabilizer of `W * W` is again
isotropic. -/
theorem restr_qiso {W : Submodule ℂ (ι → ℂ)} (hW : QIso W) {p : ι → ℂ}
    (hp : p ∈ stab (W * W)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    QIso (W.map (restr p)) := by
  constructor
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k)]
    have := sq_perp_one hW _ (hp _ (Submodule.mul_mem_mul hu hv))
    simpa only [Pi.mul_apply] using this
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k * z k * w k)]
    have := sq_perp_sq hW _ (hp _ (Submodule.mul_mem_mul hu hv)) _
      (Submodule.mul_mem_mul hz hw)
    simpa only [Pi.mul_apply, mul_assoc] using this

end General

theorem quartic_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ W : Submodule ℂ (ι → ℂ), QIso W → 3 * finrank ℂ W ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard W hW
  classical
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]; omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  have hdpos : 0 < finrank ℂ W := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    exact hW0 (Submodule.finrank_eq_zero.1 h)
  set V := W * W with hVdef
  have hone : (1 : ι → ℂ) ∉ V := by
    intro h
    have := sq_perp_one hW 1 h
    simp only [Pi.one_apply, sum_const, card_univ, nsmul_eq_mul, mul_one] at this
    exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
  by_cases hconst : ∀ x ∈ stab V, ∀ j k, x j = x k
  · have hSt : finrank ℂ (stab V) ≤ 1 := by
      have : stab V ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x hx i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hU : finrank ℂ ↥(V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) = finrank ℂ V + 1 := by
      have hinf : V ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxW, hx1⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
        rw [Submodule.mem_bot]
        by_contra hc
        have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
        apply hone
        have := V.smul_mem c⁻¹ hxW
        rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span ℂ {(1 : ι → ℂ)})
      rw [hinf, finrank_bot, add_zero,
        finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
      exact h
    have hk := hK ι W W (stab V) hW0 hW0 (fun x => Iff.rfl)
    have hp := perp_bound V (V ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) (by
      intro q hq z hz
      obtain ⟨r, hr, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have h1 := sq_perp_sq hW q hq r hr
      have h2 := sq_perp_one hW q hq
      calc ∑ i, q i * (r + c • (1 : ι → ℂ)) i
          = ∑ i, q i * r i + c * ∑ i, q i := by
            rw [mul_sum, ← sum_add_distrib]
            refine sum_congr rfl fun i _ => ?_
            simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
            ring
        _ = 0 := by rw [h1, h2, mul_zero, add_zero])
    change _ + _ ≤ finrank ℂ V + _ at hk
    omega
  · push Not at hconst
    obtain ⟨x, hx, j, k, hjk⟩ := hconst
    obtain ⟨e, he, hev⟩ := exists_indicator hx j
    have he01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by
      rw [hev l]; split_ifs <;> simp
    set f : ι → ℂ := 1 - e with hf
    have hfS : f ∈ stab V := (stab V).sub_mem (one_mem_stab V) he
    have hf01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases he01 l with h | h <;> simp [hf, h]
    have hej : e j = 1 := by rw [hev]; simp
    have hek : e k = 0 := by rw [hev]; simp [Ne.symm hjk]
    have hcB : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have hcB' : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hf, hej])
    have hsum : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← hcard,
        ← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2
        simp [hf, h1] at h2
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_qiso hW he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_qiso hW hfS hf01)
    have h3 := finrank_split W e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    omega

end PEqualNP.Outside.Gct122

open PEqualNP.Outside.Gct122 PEqualNP.Gct.Helpers in
theorem PEqualNP.Outside.L_gct_122 : ∀ (m : ℕ) (X : Submodule ℂ (Fin m → ℂ)), (∀ x ∈ X, ∑ i, x i ^ 2 = 0) → (∀ x ∈ X, ∑ i, x i ^ 4 = 0) → 3 * Module.finrank ℂ X ≤ m := by
  intro m X h2 h4
  have hQ : ∀ u ∈ X, ∀ v ∈ X, ∑ i, u i * v i = 0 := by
    intro u hu v hv
    have key : ∑ i, (2 : ℂ) * (u i * v i) =
        (∑ i, (u + v) i ^ 2) - (∑ i, u i ^ 2) - (∑ i, v i ^ 2) := by
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h2 _ (X.add_mem hu hv), h2 u hu, h2 v hv, ← Finset.mul_sum] at key
    simpa using key
  have hC : ∀ u ∈ X, ∀ v ∈ X, ∀ z ∈ X, ∀ w ∈ X, ∑ i, u i * v i * z i * w i = 0 := by
    intro u hu v hv z hz w hw
    have key : ∑ i, (24 : ℂ) * (u i * v i * z i * w i) =
        (∑ i, (u + v + z + w) i ^ 4)
          - (∑ i, (u + v + z) i ^ 4) - (∑ i, (u + v + w) i ^ 4)
          - (∑ i, (u + z + w) i ^ 4) - (∑ i, (v + z + w) i ^ 4)
          + (∑ i, (u + v) i ^ 4) + (∑ i, (u + z) i ^ 4) + (∑ i, (u + w) i ^ 4)
          + (∑ i, (v + z) i ^ 4) + (∑ i, (v + w) i ^ 4) + (∑ i, (z + w) i ^ 4)
          - (∑ i, u i ^ 4) - (∑ i, v i ^ 4) - (∑ i, z i ^ 4) - (∑ i, w i ^ 4) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h4 _ (X.add_mem (X.add_mem (X.add_mem hu hv) hz) hw),
      h4 _ (X.add_mem (X.add_mem hu hv) hz), h4 _ (X.add_mem (X.add_mem hu hv) hw),
      h4 _ (X.add_mem (X.add_mem hu hz) hw), h4 _ (X.add_mem (X.add_mem hv hz) hw),
      h4 _ (X.add_mem hu hv), h4 _ (X.add_mem hu hz), h4 _ (X.add_mem hu hw),
      h4 _ (X.add_mem hv hz), h4 _ (X.add_mem hv hw), h4 _ (X.add_mem hz hw),
      h4 u hu, h4 v hv, h4 z hz, h4 w hw, ← Finset.mul_sum] at key
    have h24 : (24 : ℂ) ≠ 0 := by norm_num
    simpa [h24] using key
  exact quartic_general (kneserFor_of_fin PEqualNP.Gct.L065) m (Fin m) (Fintype.card_fin m) X
    ⟨hQ, hC⟩
