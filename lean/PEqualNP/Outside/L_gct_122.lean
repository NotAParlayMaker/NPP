import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatFromKneser
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace PEqualNP.Outside.L_gct_122

open Module Finset PEqualNP.Gct.Helpers

section General

variable {ι : Type} [Fintype ι]

def QuarticIso (X : Submodule ℂ (ι → ℂ)) : Prop :=
  (∀ u ∈ X, ∀ v ∈ X, ∑ i, u i * v i = 0) ∧
    (∀ u ∈ X, ∀ v ∈ X, ∀ w ∈ X, ∀ z ∈ X, ∑ i, u i * v i * w i * z i = 0)

theorem sq_sum_zero {X : Submodule ℂ (ι → ℂ)} (hX : QuarticIso X) :
    ∀ y ∈ X * X, ∑ i, y i = 0 := by
  intro y hy
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro u hu v hv
    exact hX.1 u hu v hv
  · intro a b ha hb
    simp only [Pi.add_apply, sum_add_distrib, ha, hb, add_zero]

theorem sq_perp {X : Submodule ℂ (ι → ℂ)} (hX : QuarticIso X) :
    ∀ y ∈ X * X, ∀ z ∈ X * X, ∑ i, y i * z i = 0 := by
  intro y hy
  refine Submodule.mul_induction_on hy ?_ ?_
  · intro u hu v hv z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro w hw t ht
      have h := hX.2 u hu v hv w hw t ht
      convert h using 1
      refine sum_congr rfl fun i _ => ?_
      simp only [Pi.mul_apply]
      ring
    · intro a b ha hb
      simp only [Pi.add_apply, mul_add, sum_add_distrib, ha, hb, add_zero]
  · intro a b ha hb z hz
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha z hz, hb z hz, add_zero]

theorem restr_quarticIso {X : Submodule ℂ (ι → ℂ)} (hX : QuarticIso X) {p : ι → ℂ}
    (hp : p ∈ stab (X * X)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    QuarticIso (X.map (restr p)) := by
  have hsum := sq_sum_zero hX
  have hperp := sq_perp hX
  constructor
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k)]
    have h := hsum _ (hp _ (Submodule.mul_mem_mul hu hv))
    simpa only [Pi.mul_apply, mul_assoc] using h
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ _ ⟨z, hz, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k * w k * z k)]
    have h := hperp _ (hp _ (Submodule.mul_mem_mul hu hv)) _ (Submodule.mul_mem_mul hw hz)
    convert h using 1
    refine sum_congr rfl fun k _ => ?_
    simp only [Pi.mul_apply]
    ring

theorem card_ge_three_of_ne_bot {X : Submodule ℂ (ι → ℂ)} (hX : QuarticIso X) (hX0 : X ≠ ⊥) :
    3 ≤ Fintype.card ι := by
  classical
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hu0
  simp only [Pi.zero_apply] at hi₀
  have h2 : ∑ i, u i ^ 2 = 0 := by
    have h := hX.1 u hu u hu
    convert h using 1
    refine sum_congr rfl fun i _ => by ring
  have h4 : ∑ i, u i ^ 4 = 0 := by
    have h := hX.2 u hu u hu u hu u hu
    convert h using 1
    refine sum_congr rfl fun i _ => by ring
  by_contra hlt
  have hle : Fintype.card ι ≤ 2 := by omega
  let s : Finset ι := Finset.univ.erase i₀
  have hscard : s.card + 1 = Fintype.card ι := Finset.card_erase_add_one (Finset.mem_univ i₀)
  rcases Finset.eq_empty_or_nonempty s with hs | hs
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at h2
    change u i₀ ^ 2 + ∑ x ∈ s, u x ^ 2 = 0 at h2
    rw [hs, Finset.sum_empty, add_zero] at h2
    have hsq : u i₀ * u i₀ = 0 := by linear_combination h2
    exact hi₀ (mul_self_eq_zero.1 hsq)
  · have hspos : 0 < s.card := Finset.card_pos.2 hs
    have hs1 : s.card = 1 := by omega
    obtain ⟨i₁, hi₁⟩ := Finset.card_eq_one.1 hs1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at h2 h4
    change u i₀ ^ 2 + ∑ x ∈ s, u x ^ 2 = 0 at h2
    change u i₀ ^ 4 + ∑ x ∈ s, u x ^ 4 = 0 at h4
    rw [hi₁, Finset.sum_singleton] at h2 h4
    have hzero : (2 : ℂ) * ((u i₀ * u i₀) * (u i₀ * u i₀)) = 0 := by
      linear_combination h4 + (u i₀ ^ 2 - u i₁ ^ 2) * h2
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    have hsq4 : (u i₀ * u i₀) * (u i₀ * u i₀) = 0 := (mul_eq_zero.1 hzero).resolve_left h2ne
    exact hi₀ (mul_self_eq_zero.1 (mul_self_eq_zero.1 hsq4))

end General

theorem quartic_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ X : Submodule ℂ (ι → ℂ), QuarticIso X → 3 * finrank ℂ X ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard X hX
  classical
  by_cases hX0 : X = ⊥
  · rw [hX0, finrank_bot]; omega
  by_cases hdim1 : finrank ℂ X ≤ 1
  · have h3 := card_ge_three_of_ne_bot hX hX0
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  set V := X * X with hVdef
  by_cases hconst : ∀ x ∈ stab V, ∀ j k, x j = x k
  · have hSt : finrank ℂ (stab V) ≤ 1 := by
      have : stab V ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x hx i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hk := hK ι X X (stab V) hX0 hX0 (fun _ => Iff.rfl)
    have hp := perp_bound V V (sq_perp hX)
    change finrank ℂ X + finrank ℂ X ≤ finrank ℂ V + finrank ℂ (stab V) at hk
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
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_quarticIso hX he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_quarticIso hX hfS hf01)
    have h3 := finrank_split X e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    omega

end PEqualNP.Outside.L_gct_122

theorem PEqualNP.Outside.L_gct_122 :
    ∀ (m : ℕ) (X : Submodule ℂ (Fin m → ℂ)), (∀ x ∈ X, ∑ i, x i ^ 2 = 0) → (∀ x ∈ X, ∑ i, x i ^ 4 = 0) → 3 * Module.finrank ℂ X ≤ m := by
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
  have hF : ∀ u ∈ X, ∀ v ∈ X, ∀ w ∈ X, ∀ z ∈ X, ∑ i, u i * v i * w i * z i = 0 := by
    intro u hu v hv w hw z hz
    have key : ∑ i, (24 : ℂ) * (u i * v i * w i * z i) =
        (∑ i, (u + v + w + z) i ^ 4)
        - (∑ i, (u + v + w) i ^ 4) - (∑ i, (u + v + z) i ^ 4)
        - (∑ i, (u + w + z) i ^ 4) - (∑ i, (v + w + z) i ^ 4)
        + (∑ i, (u + v) i ^ 4) + (∑ i, (u + w) i ^ 4) + (∑ i, (u + z) i ^ 4)
        + (∑ i, (v + w) i ^ 4) + (∑ i, (v + z) i ^ 4) + (∑ i, (w + z) i ^ 4)
        - (∑ i, u i ^ 4) - (∑ i, v i ^ 4) - (∑ i, w i ^ 4) - (∑ i, z i ^ 4) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h4 _ (X.add_mem (X.add_mem (X.add_mem hu hv) hw) hz),
      h4 _ (X.add_mem (X.add_mem hu hv) hw),
      h4 _ (X.add_mem (X.add_mem hu hv) hz),
      h4 _ (X.add_mem (X.add_mem hu hw) hz),
      h4 _ (X.add_mem (X.add_mem hv hw) hz),
      h4 _ (X.add_mem hu hv), h4 _ (X.add_mem hu hw), h4 _ (X.add_mem hu hz),
      h4 _ (X.add_mem hv hw), h4 _ (X.add_mem hv hz), h4 _ (X.add_mem hw hz),
      h4 u hu, h4 v hv, h4 w hw, h4 z hz, ← Finset.mul_sum] at key
    have h24 : (24 : ℂ) ≠ 0 := by norm_num
    simpa [h24] using key
  exact PEqualNP.Outside.L_gct_122.quartic_general
    (PEqualNP.Gct.Helpers.kneserFor_of_fin PEqualNP.Gct.L065)
    m (Fin m) (Fintype.card_fin m) X ⟨hQ, hF⟩
