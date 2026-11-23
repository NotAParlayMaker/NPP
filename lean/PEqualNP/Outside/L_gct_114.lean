import Mathlib
import PEqualNP.Defs


/-! The dimension argument reuses the repository's Kneser and product-span proofs (L-gct-065 and L-gct-079). -/

section
/-!
# Helper module: finitely many subalgebras of a finite product of fields

Helper module, proofs only. It serves the Kneser-type theorem for coordinatewise products of
subspaces of `ℂ^n` (Mirandola and Zemor 2015, Theorem 3.3).

The algebra is `ι → K` with pointwise multiplication, `ι` finite and `K` a field. A unital
subalgebra `A` contains, for every `x ∈ A` and every scalar `c`, the indicator of the level set
`{j | x j = c}`: it is the Lagrange product `∏ μ ≠ c, (c - μ)⁻¹ • (x - μ)` over the values `μ` of
`x`. Every `x ∈ A` is the combination `∑ c, c • indicator {j | x j = c}` over its values, so `A`
is determined by the set of subsets of `ι` whose indicator lies in `A`. There are finitely many
such sets of subsets.

Main statement: `PEqualNP.Outside.Gct114.Helpers.Kneser.finite_subalgebra`.
-/

namespace PEqualNP.Outside.Gct114.Helpers.Kneser

namespace Fin

open scoped Classical in
/-- The indicator of a level set of a member of a unital subalgebra of `ι → K` is a member. -/
theorem levelSet_indicator_mem {K ι : Type*} [Field K] [Fintype ι]
    (A : Subalgebra K (ι → K)) {x : ι → K} (hx : x ∈ A) (c : K) :
    Set.indicator {j | x j = c} (1 : ι → K) ∈ A := by
  have key : Set.indicator {j | x j = c} (1 : ι → K)
      = ∏ μ ∈ (Finset.univ.image x).erase c,
          ((c - μ)⁻¹ • (x - algebraMap K (ι → K) μ)) := by
    funext j
    rw [Finset.prod_apply]
    by_cases h : x j = c
    · rw [Set.indicator_of_mem (by exact h)]
      symm
      apply Finset.prod_eq_one
      intro μ hμ
      have hne : c - μ ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hμ).symm
      simp [h, hne]
    · rw [Set.indicator_of_notMem (by exact h)]
      symm
      apply Finset.prod_eq_zero (i := x j)
      · exact Finset.mem_erase.mpr ⟨h, Finset.mem_image_of_mem x (Finset.mem_univ j)⟩
      · simp
  rw [key]
  exact A.prod_mem fun μ _ => A.smul_mem (A.sub_mem hx (A.algebraMap_mem μ)) _

open scoped Classical in
/-- A member of `ι → K` is the combination of the indicators of its level sets. -/
theorem eq_sum_levelSet_indicator {K ι : Type*} [Field K] [Fintype ι] (x : ι → K) :
    x = ∑ c ∈ Finset.univ.image x, c • Set.indicator {j | x j = c} (1 : ι → K) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (x j)]
  · simp
  · intro c _ hc
    have : j ∉ {j | x j = c} := fun h => hc (Eq.symm h)
    simp [Set.indicator_of_notMem this]
  · intro h
    exact absurd (Finset.mem_image_of_mem x (Finset.mem_univ j)) h

/-- The set of subsets of `ι` whose indicator lies in the subalgebra. -/
def indicatorSets {K ι : Type*} [Field K] (A : Subalgebra K (ι → K)) : Set (Set ι) :=
  {S | Set.indicator S (1 : ι → K) ∈ A}

/-- A subalgebra is contained in any subalgebra holding at least the same indicators. -/
theorem le_of_indicatorSets_subset {K ι : Type*} [Field K] [Fintype ι]
    {A B : Subalgebra K (ι → K)} (h : indicatorSets A ⊆ indicatorSets B) : A ≤ B := by
  classical
  intro x hx
  rw [eq_sum_levelSet_indicator x]
  exact B.sum_mem fun c _ => B.smul_mem (h (levelSet_indicator_mem A hx c)) c

/-- A subalgebra of `ι → K` is determined by the subsets whose indicator it holds. -/
theorem indicatorSets_injective {K ι : Type*} [Field K] [Fintype ι] :
    Function.Injective (indicatorSets : Subalgebra K (ι → K) → Set (Set ι)) :=
  fun _ _ h => le_antisymm (le_of_indicatorSets_subset h.le) (le_of_indicatorSets_subset h.ge)

/-- A finite product of copies of a field has finitely many unital subalgebras. -/
theorem finite_subalgebra_pi (K ι : Type*) [Field K] [Fintype ι] :
    Finite (Subalgebra K (ι → K)) :=
  Finite.of_injective _ indicatorSets_injective

end Fin

/-- The algebra `ℂ^n` with pointwise multiplication has finitely many unital subalgebras. -/
theorem finite_subalgebra (n : ℕ) : Finite (Subalgebra ℂ (Fin n → ℂ)) :=
  Fin.finite_subalgebra_pi ℂ (_root_.Fin n)

end PEqualNP.Outside.Gct114.Helpers.Kneser
end

section
/-!
# The e-transform lemma for coordinatewise products of subspaces (helper module, proofs only)

Helper module for the Kneser-type theorem for products of subspaces of `ℂ^n` under the
coordinatewise product (after Mirandola and Zemor, 2015, Lemma 3.6). No definitions of the
project are introduced here: only proofs.

For `S T : Submodule ℂ (Fin n → ℂ)` and an invertible `e ∈ T` the transform is
`S(e) = S ⊓ e⁻¹ T` and `T(e) = T ⊔ e S`. We write `e⁻¹ T` as the preimage of `T` under
multiplication by `e`, so no inverse appears in the induction.

* `ETr.core`: the normalized statement (`1 ∈ S`, `1 ∈ T`), by strong induction on `dim S`.
* `etransform`: the general statement, by scaling.
-/

namespace PEqualNP.Outside.Gct114.Helpers.Kneser

namespace ETr

open Module

variable {n : ℕ}

/-- Multiplication by an invertible element is injective. -/
theorem mulLeft_injective {e : Fin n → ℂ} (he : IsUnit e) :
    Function.Injective (LinearMap.mulLeft ℂ e) := by
  obtain ⟨u, rfl⟩ := he
  intro a b h
  have h' : (u : Fin n → ℂ) * a = u * b := h
  have := congrArg (fun z => ((u⁻¹ : (Fin n → ℂ)ˣ) : Fin n → ℂ) * z) h'
  simpa using this

/-- Multiplication by an invertible element is surjective. -/
theorem mulLeft_surjective {e : Fin n → ℂ} (he : IsUnit e) :
    Function.Surjective (LinearMap.mulLeft ℂ e) := by
  obtain ⟨u, rfl⟩ := he
  intro b
  exact ⟨((u⁻¹ : (Fin n → ℂ)ˣ) : Fin n → ℂ) * b, by simp⟩

/-- Scaling by an invertible element preserves the dimension of a subspace. -/
theorem finrank_map_mulLeft {e : Fin n → ℂ} (he : IsUnit e) (S : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S.map (LinearMap.mulLeft ℂ e)) = finrank ℂ S :=
  (Submodule.equivMapOfInjective _ (mulLeft_injective he) S).finrank_eq.symm

/-- Scaling by the inverse of an invertible element (as a preimage) preserves the dimension. -/
theorem finrank_comap_mulLeft {e : Fin n → ℂ} (he : IsUnit e) (S : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S.comap (LinearMap.mulLeft ℂ e)) = finrank ℂ S := by
  rw [← finrank_map_mulLeft he (S.comap (LinearMap.mulLeft ℂ e)),
    Submodule.map_comap_eq_of_surjective (mulLeft_surjective he)]

/-- A subspace of `ℂ^n` containing `1` is spanned by its invertible elements. -/
theorem le_span_units (T : Submodule ℂ (Fin n → ℂ)) (h1 : (1 : Fin n → ℂ) ∈ T) :
    T ≤ Submodule.span ℂ {e | e ∈ T ∧ IsUnit e} := by
  intro v hv
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (insert (0 : ℂ) (Finset.univ.image (fun i => - v i)))
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  have hci : ∀ i, v i + c ≠ 0 := by
    intro i h
    apply hc
    have : c = - v i := by linear_combination h
    rw [this]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hu1 : IsUnit (c • (1 : Fin n → ℂ)) := by
    rw [Pi.isUnit_iff]
    intro i
    simpa using hc0
  have hu2 : IsUnit (v + c • (1 : Fin n → ℂ)) := by
    rw [Pi.isUnit_iff]
    intro i
    simpa using hci i
  have hv' : v = (v + c • (1 : Fin n → ℂ)) - c • (1 : Fin n → ℂ) := by simp
  rw [hv']
  exact Submodule.sub_mem _
    (Submodule.subset_span ⟨T.add_mem hv (T.smul_mem c h1), hu2⟩)
    (Submodule.subset_span ⟨T.smul_mem c h1, hu1⟩)

/-- Case A of the induction: if `e S ≤ T` for every invertible `e ∈ T`, then `V = T` and
`H` the subalgebra generated by `S` work. -/
theorem core_stable (S T : Submodule ℂ (Fin n → ℂ)) (hS : (1 : Fin n → ℂ) ∈ S)
    (hT : (1 : Fin n → ℂ) ∈ T)
    (hA : ∀ e ∈ T, IsUnit e → S ≤ T.comap (LinearMap.mulLeft ℂ e)) :
    ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ T ≤ V ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H) := by
  have hST : ∀ s ∈ S, ∀ t ∈ T, s * t ∈ T := by
    intro s hs t ht
    have hle : Submodule.span ℂ {e | e ∈ T ∧ IsUnit e} ≤ T.comap (LinearMap.mulLeft ℂ s) := by
      rw [Submodule.span_le]
      rintro e ⟨heT, heu⟩
      have := hA e heT heu hs
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at this
      simpa [mul_comm] using this
    have := hle (le_span_units T hT ht)
    simpa using this
  refine ⟨Algebra.adjoin ℂ (S : Set (Fin n → ℂ)), T, ?_, le_rfl, ?_, ?_⟩
  · intro h hh
    induction hh using Algebra.adjoin_induction with
    | mem x hx => exact fun v hv => hST x hx v hv
    | algebraMap r =>
      intro v hv
      rw [← Algebra.smul_def]
      exact T.smul_mem r hv
    | add x y _ _ ihx ihy =>
      intro v hv
      rw [add_mul]
      exact T.add_mem (ihx v hv) (ihy v hv)
    | mul x y _ _ ihx ihy =>
      intro v hv
      rw [mul_assoc]
      exact ihx _ (ihy v hv)
  · intro t ht
    have := Submodule.mul_mem_mul hS ht
    simpa using this
  · have hle : S ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (S : Set (Fin n → ℂ))) :=
      fun s hs => Algebra.subset_adjoin hs
    have := Submodule.finrank_mono hle
    omega

/-- The transform preserves the sum of the dimensions:
`dim (S ⊓ e⁻¹ T) + dim (T ⊔ e S) = dim S + dim T`. -/
theorem finrank_transform (S T : Submodule ℂ (Fin n → ℂ)) {e : Fin n → ℂ} (he : IsUnit e) :
    finrank ℂ (S ⊓ T.comap (LinearMap.mulLeft ℂ e) : Submodule ℂ (Fin n → ℂ)) +
      finrank ℂ (T ⊔ S.map (LinearMap.mulLeft ℂ e) : Submodule ℂ (Fin n → ℂ)) =
    finrank ℂ S + finrank ℂ T := by
  have hinf : T ⊓ S.map (LinearMap.mulLeft ℂ e) =
      (S ⊓ T.comap (LinearMap.mulLeft ℂ e)).map (LinearMap.mulLeft ℂ e) := by
    ext y
    simp only [Submodule.mem_inf, Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨hy, s, hs, rfl⟩
      exact ⟨s, ⟨hs, hy⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hy⟩, rfl⟩
      exact ⟨hy, s, hs, rfl⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq T (S.map (LinearMap.mulLeft ℂ e))
  rw [hinf, finrank_map_mulLeft he, finrank_map_mulLeft he] at h1
  omega

/-- The transform does not enlarge the product: `(S ⊓ e⁻¹ T) * (T ⊔ e S) ≤ S * T`. -/
theorem transform_mul_le (S T : Submodule ℂ (Fin n → ℂ)) (e : Fin n → ℂ) :
    (S ⊓ T.comap (LinearMap.mulLeft ℂ e)) * (T ⊔ S.map (LinearMap.mulLeft ℂ e)) ≤ S * T := by
  rw [Submodule.mul_le]
  intro s hs m hm
  have hmem : T ⊔ S.map (LinearMap.mulLeft ℂ e) ≤ (S * T).comap (LinearMap.mulLeft ℂ s) := by
    refine sup_le ?_ ?_
    · intro t ht
      exact Submodule.mul_mem_mul hs.1 ht
    · rintro _ ⟨s0, hs0, rfl⟩
      have h2 : e * s ∈ T := hs.2
      have := Submodule.mul_mem_mul hs0 h2
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      have heq : s * (e * s0) = s0 * (e * s) := by ring
      rw [heq]
      exact this
  exact hmem hm

/-- CORE (normalized e-transform lemma): if `1 ∈ S` and `1 ∈ T` there are a subalgebra `H` and
a subspace `V`, stable under `H`, with `T ≤ V ≤ S * T` and
`dim S + dim T ≤ dim V + dim H`. -/
theorem core (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (hS : (1 : Fin n → ℂ) ∈ S)
    (hT : (1 : Fin n → ℂ) ∈ T) :
    ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ T ≤ V ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H) := by
  suffices key : ∀ k : ℕ, ∀ S T : Submodule ℂ (Fin n → ℂ), finrank ℂ S = k →
      (1 : Fin n → ℂ) ∈ S → (1 : Fin n → ℂ) ∈ T →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ T ≤ V ∧ V ≤ S * T ∧
        finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H) from
    key _ S T rfl hS hT
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S T hk hS hT
    by_cases hA : ∀ e ∈ T, IsUnit e → S ≤ T.comap (LinearMap.mulLeft ℂ e)
    · exact core_stable S T hS hT hA
    · push Not at hA
      obtain ⟨e, heT, heu, hne⟩ := hA
      have hlt : S ⊓ T.comap (LinearMap.mulLeft ℂ e) < S := inf_lt_left.mpr hne
      have hdim := Submodule.finrank_lt_finrank_of_lt hlt
      have h1S : (1 : Fin n → ℂ) ∈ S ⊓ T.comap (LinearMap.mulLeft ℂ e) := by
        refine ⟨hS, ?_⟩
        simpa using heT
      have h1T : (1 : Fin n → ℂ) ∈ T ⊔ S.map (LinearMap.mulLeft ℂ e) :=
        (le_sup_left : T ≤ _) hT
      obtain ⟨H, V, hHV, hTV, hVle, hfin⟩ :=
        ih _ (hk ▸ hdim) (S ⊓ T.comap (LinearMap.mulLeft ℂ e))
          (T ⊔ S.map (LinearMap.mulLeft ℂ e)) rfl h1S h1T
      refine ⟨H, V, hHV, le_trans le_sup_left hTV, le_trans hVle (transform_mul_le S T e), ?_⟩
      have := finrank_transform S T heu
      omega

end ETr

open Module in
/-- The e-transform lemma (after Mirandola and Zemor, 2015, Lemma 3.6): for subspaces `S`, `T`
of `ℂ^n`, an invertible `x ∈ S` and `T` containing an invertible element, there are a subalgebra
`H` and a subspace `V`, stable under `H`, with `x T ⊆ V ⊆ S * T` and
`dim S + dim T ≤ dim V + dim H`. -/
theorem etransform (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ)
    (hx : x ∈ S) (hxu : IsUnit x) (hT : ∃ t ∈ T, IsUnit t) :
    ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
      Module.finrank ℂ S + Module.finrank ℂ T ≤
        Module.finrank ℂ V + Module.finrank ℂ (Subalgebra.toSubmodule H) := by
  obtain ⟨t, ht, htu⟩ := hT
  have h1S : (1 : Fin n → ℂ) ∈ S.comap (LinearMap.mulLeft ℂ x) := by simpa using hx
  have h1T : (1 : Fin n → ℂ) ∈ T.comap (LinearMap.mulLeft ℂ t) := by simpa using ht
  obtain ⟨H, V0, hHV, hTV, hVle, hfin⟩ := ETr.core n _ _ h1S h1T
  have hxt : IsUnit (x * t) := hxu.mul htu
  refine ⟨H, V0.map (LinearMap.mulLeft ℂ (x * t)), ?_, ?_, ?_, ?_⟩
  · rintro h hh _ ⟨v, hv, rfl⟩
    refine ⟨h * v, hHV h hh v hv, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    ring
  · intro t' ht'
    obtain ⟨u, rfl⟩ := htu
    refine ⟨((u⁻¹ : (Fin n → ℂ)ˣ) : Fin n → ℂ) * t', hTV ?_, ?_⟩
    · simpa using ht'
    · simp only [LinearMap.mulLeft_apply]
      rw [mul_assoc, Units.mul_inv_cancel_left]
  · rw [Submodule.map_le_iff_le_comap]
    refine le_trans hVle ?_
    rw [Submodule.mul_le]
    intro s0 hs0 t0 ht0
    have h1 : x * s0 ∈ S := hs0
    have h2 : t * t0 ∈ T := ht0
    have := Submodule.mul_mem_mul h1 h2
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
    have heq : x * t * (s0 * t0) = x * s0 * (t * t0) := by ring
    rw [heq]
    exact this
  · rw [ETr.finrank_map_mulLeft hxt, ← ETr.finrank_comap_mulLeft hxu S,
      ← ETr.finrank_comap_mulLeft htu T]
    exact hfin

end PEqualNP.Outside.Gct114.Helpers.Kneser
end

section
/-!
Helper module, proofs only, for L-gct-065 (Kneser for codes over the complex numbers, after
Mirandola and Zemor 2015, Theorem 3.3).

The assembly: from finiteness of the set of subalgebras of `Fin n → ℂ` and the e-transform
lemma (both taken as hypotheses here), the Kneser inequality
`dim S + dim T ≤ dim (S * T) + dim St (S * T)` for nonzero subspaces `S`, `T`.

Two stages.

* `Asm.full_of`: if `S` is nonzero with full support and `T` contains a unit, some subalgebra
  `H` stabilizes `S * T` and has `dim S + dim T ≤ dim (S * T) + dim H`. The units `x` of `S`
  are sorted by the subalgebra the e-transform gives for `x`; together with the coordinate
  hyperplanes these finitely many classes cover `S`, and a vector space over an infinite field
  is not a finite union of proper subspaces, so one class spans `S`.
* `kneser_of`: the general case, with no change of the index type. With `W` the space of
  vectors vanishing on the common support of `S` and `T`, stage one is applied to `S ⊔ W` and
  `T ⊔ W`, and the dimensions are compared.
-/

namespace PEqualNP.Outside.Gct114.Helpers.Kneser

open Module

namespace Asm

/-- A subspace of `Fin n → ℂ` with full support contains a unit: it is not the union of its
intersections with the coordinate hyperplanes. -/
theorem exists_isUnit_of_support {n : ℕ} (U : Submodule ℂ (Fin n → ℂ))
    (hU : ∀ i, ∃ u ∈ U, u i ≠ 0) : ∃ u ∈ U, IsUnit u := by
  by_contra hno
  push Not at hno
  let P : Fin n → Submodule ℂ U := fun i =>
    (LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)).comap U.subtype
  have hcov : ⋃ i, (P i : Set U) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    have h1 := hno u.1 u.2
    rw [Pi.isUnit_iff] at h1
    push Not at h1
    obtain ⟨i, hi⟩ := h1
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    have h0 : u.1 i = 0 := by
      by_contra hne
      exact hi (isUnit_iff_ne_zero.2 hne)
    show U.subtype u ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)
    rw [LinearMap.mem_ker]
    exact h0
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  obtain ⟨u, hu, hui⟩ := hU i
  have hmem : (⟨u, hu⟩ : U) ∈ P i := by
    rw [hi]
    exact Submodule.mem_top
  have h0 : U.subtype ⟨u, hu⟩ ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ) := hmem
  rw [LinearMap.mem_ker] at h0
  exact hui h0

/-- Stage one: full support. Some subalgebra stabilizes `S * T` and is large enough. -/
theorem full_of {n : ℕ} (hfin : Finite (Subalgebra ℂ (Fin n → ℂ)))
    (hetr : ∀ (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), x ∈ S → IsUnit x →
      (∃ t ∈ T, IsUnit t) →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
        finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H))
    (S T : Submodule ℂ (Fin n → ℂ)) (hS0 : S ≠ ⊥) (hS : ∀ i, ∃ s ∈ S, s i ≠ 0)
    (hT : ∃ t ∈ T, IsUnit t) :
    ∃ H : Subalgebra ℂ (Fin n → ℂ), (∀ h ∈ H, ∀ v ∈ S * T, h * v ∈ S * T) ∧
      finrank ℂ S + finrank ℂ T ≤
        finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) +
          finrank ℂ (Subalgebra.toSubmodule H) := by
  -- the elements of `S` for which the e-transform can give the subalgebra `H`
  let G : Subalgebra ℂ (Fin n → ℂ) → Set (Fin n → ℂ) := fun H =>
    {x | x ∈ S ∧ ∃ V : Submodule ℂ (Fin n → ℂ),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H)}
  let P : Fin n ⊕ Subalgebra ℂ (Fin n → ℂ) → Submodule ℂ S := fun j =>
    Sum.elim
      (fun i => (LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)).comap S.subtype)
      (fun H => (Submodule.span ℂ (G H)).comap S.subtype) j
  have hcov : ⋃ j, (P j : Set S) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    by_cases hu : IsUnit u.1
    · obtain ⟨H, V, h1, h2, h3, h4⟩ := hetr S T u.1 u.2 hu hT
      refine Set.mem_iUnion.2 ⟨Sum.inr H, ?_⟩
      show S.subtype u ∈ Submodule.span ℂ (G H)
      exact Submodule.subset_span ⟨u.2, V, h1, h2, h3, h4⟩
    · rw [Pi.isUnit_iff] at hu
      push Not at hu
      obtain ⟨i, hi⟩ := hu
      refine Set.mem_iUnion.2 ⟨Sum.inl i, ?_⟩
      have h0 : u.1 i = 0 := by
        by_contra hne
        exact hi (isUnit_iff_ne_zero.2 hne)
      show S.subtype u ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)
      rw [LinearMap.mem_ker]
      exact h0
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  rcases j with i | H
  · exfalso
    obtain ⟨u, hu, hui⟩ := hS i
    have hmem : (⟨u, hu⟩ : S) ∈ P (Sum.inl i) := by
      rw [hj]
      exact Submodule.mem_top
    have h0 : S.subtype ⟨u, hu⟩ ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ) :=
      hmem
    rw [LinearMap.mem_ker] at h0
    exact hui h0
  · have hspan : S ≤ Submodule.span ℂ (G H) := by
      intro s hs
      have hmem : (⟨s, hs⟩ : S) ∈ P (Sum.inr H) := by
        rw [hj]
        exact Submodule.mem_top
      exact hmem
    -- the largest `H`-stable subspace of `S * T`
    let M : Submodule ℂ (Fin n → ℂ) :=
      sSup {V | (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ V ≤ S * T}
    have hM_le : M ≤ S * T := sSup_le fun V hV => hV.2
    have hM_stab : ∀ h ∈ H, ∀ v ∈ M, h * v ∈ M := by
      intro h hh
      have hle : M ≤ M.comap (LinearMap.mulLeft ℂ h) := by
        refine sSup_le fun V hV v hv => ?_
        show (LinearMap.mulLeft ℂ h) v ∈ M
        rw [LinearMap.mulLeft_apply]
        exact (le_sSup hV : V ≤ M) (hV.1 h hh v hv)
      intro v hv
      have h1 := hle hv
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
      exact h1
    have hST_le : S * T ≤ M := by
      rw [Submodule.mul_le]
      intro s hs t ht
      have hle : Submodule.span ℂ (G H) ≤ M.comap (LinearMap.mulRight ℂ t) := by
        rw [Submodule.span_le]
        rintro x ⟨_, V, h1, h2, h3, _⟩
        show (LinearMap.mulRight ℂ t) x ∈ M
        rw [LinearMap.mulRight_apply]
        exact (le_sSup (show V ∈ {V | (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ V ≤ S * T} from
          ⟨h1, h3⟩) : V ≤ M) (h2 t ht)
      have h1 := hle (hspan hs)
      rw [Submodule.mem_comap, LinearMap.mulRight_apply] at h1
      exact h1
    have hne : (G H).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply hS0
      rw [eq_bot_iff]
      intro s hs
      have h1 := hspan hs
      rw [hemp, Submodule.span_empty] at h1
      exact h1
    obtain ⟨x, _, V, _, _, h3, h4⟩ := hne
    have hVle : finrank ℂ V ≤ finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) :=
      Submodule.finrank_mono h3
    refine ⟨H, fun h hh v hv => hM_le (hM_stab h hh v (hST_le hv)), ?_⟩
    omega

/-- The vectors that vanish on the common support of `S` and `T`. -/
def offSupp {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∀ i, (∃ s ∈ S, s i ≠ 0) → (∃ t ∈ T, t i ≠ 0) → x i = 0}
  add_mem' := by
    intro a b ha hb i h1 h2
    simp [ha i h1 h2, hb i h1 h2]
  zero_mem' := by
    intro i _ _
    rfl
  smul_mem' := by
    intro c a ha i h1 h2
    simp [ha i h1 h2]

theorem mem_offSupp {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {x : Fin n → ℂ} :
    x ∈ offSupp S T ↔ ∀ i, (∃ s ∈ S, s i ≠ 0) → (∃ t ∈ T, t i ≠ 0) → x i = 0 :=
  Iff.rfl

theorem mul_mem_offSupp {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ offSupp S T) (a : Fin n → ℂ) : a * x ∈ offSupp S T := by
  intro i h1 h2
  simp [hx i h1 h2]

/-- The product `S * T` vanishes off the common support. -/
theorem mul_apply_eq_zero {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {v : Fin n → ℂ}
    (hv : v ∈ S * T) (i : Fin n) (hi : ¬((∃ s ∈ S, s i ≠ 0) ∧ (∃ t ∈ T, t i ≠ 0))) :
    v i = 0 := by
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro s hs t ht
    by_contra hne
    rw [Pi.mul_apply] at hne
    exact hi ⟨⟨s, hs, left_ne_zero_of_mul hne⟩, ⟨t, ht, right_ne_zero_of_mul hne⟩⟩
  · intro a b ha hb
    simp [ha, hb]

/-- `S ⊔ offSupp S T` has full support. -/
theorem support_sup_offSupp {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) (i : Fin n) :
    ∃ u ∈ S ⊔ offSupp S T, u i ≠ 0 := by
  by_cases hK : ∃ s ∈ S, s i ≠ 0
  · obtain ⟨s, hs, hsi⟩ := hK
    exact ⟨s, (le_sup_left : S ≤ S ⊔ offSupp S T) hs, hsi⟩
  · refine ⟨Pi.single i 1, (le_sup_right : offSupp S T ≤ S ⊔ offSupp S T) ?_, by simp⟩
    intro j h1 _
    by_cases hji : j = i
    · subst hji
      exact absurd h1 hK
    · simp [hji]

theorem support_sup_offSupp' {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) (i : Fin n) :
    ∃ u ∈ T ⊔ offSupp S T, u i ≠ 0 := by
  by_cases hK : ∃ t ∈ T, t i ≠ 0
  · obtain ⟨t, ht, hti⟩ := hK
    exact ⟨t, (le_sup_left : T ≤ T ⊔ offSupp S T) ht, hti⟩
  · refine ⟨Pi.single i 1, (le_sup_right : offSupp S T ≤ T ⊔ offSupp S T) ?_, by simp⟩
    intro j _ h2
    by_cases hji : j = i
    · subst hji
      exact absurd h2 hK
    · simp [hji]

/-- The product of the enlarged spaces is inside `S * T ⊔ offSupp S T`. -/
theorem sup_mul_sup_le {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) :
    (S ⊔ offSupp S T) * (T ⊔ offSupp S T) ≤ S * T ⊔ offSupp S T := by
  rw [Submodule.mul_le]
  intro a ha b hb
  obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨t, ht, w', hw', rfl⟩ := Submodule.mem_sup.1 hb
  have h1 : s * t ∈ S * T := Submodule.mul_mem_mul hs ht
  have h2 : s * w' + w * t + w * w' ∈ offSupp S T := by
    refine Submodule.add_mem _ (Submodule.add_mem _ (mul_mem_offSupp hw' s) ?_)
      (mul_mem_offSupp hw' w)
    rw [mul_comm]
    exact mul_mem_offSupp hw t
  have h3 : (s + w) * (t + w') = s * t + (s * w' + w * t + w * w') := by ring
  rw [h3]
  exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)

/-- The parts of `S` and of `T` off the common support are independent. -/
theorem finrank_inf_offSupp_add_le {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S ⊓ offSupp S T : Submodule ℂ (Fin n → ℂ)) +
      finrank ℂ (T ⊓ offSupp S T : Submodule ℂ (Fin n → ℂ)) ≤ finrank ℂ (offSupp S T) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ offSupp S T) (T ⊓ offSupp S T)
  have h2 : (S ⊓ offSupp S T) ⊓ (T ⊓ offSupp S T) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxS, hxW⟩, ⟨hxT, _⟩⟩
    rw [Submodule.mem_bot]
    funext i
    by_contra hne
    exact hne (hxW i ⟨x, hxS, hne⟩ ⟨x, hxT, hne⟩)
  have h3 : finrank ℂ ((S ⊓ offSupp S T) ⊔ (T ⊓ offSupp S T) : Submodule ℂ (Fin n → ℂ)) ≤
      finrank ℂ (offSupp S T) :=
    Submodule.finrank_mono (sup_le inf_le_right inf_le_right)
  rw [h2, finrank_bot] at h1
  omega

end Asm

open Asm in
/-- Kneser for codes over the complex numbers, from finiteness of the set of subalgebras and
the e-transform lemma. -/
theorem kneser_of
    (hfin : ∀ n : ℕ, Finite (Subalgebra ℂ (Fin n → ℂ)))
    (hetr : ∀ (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), x ∈ S → IsUnit x →
      (∃ t ∈ T, IsUnit t) →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
        Module.finrank ℂ S + Module.finrank ℂ T ≤
          Module.finrank ℂ V + Module.finrank ℂ (Subalgebra.toSubmodule H)) :
    ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
      Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St := by
  intro n S T St hS _ hSt
  have hS' : S ⊔ offSupp S T ≠ ⊥ := by
    intro h
    apply hS
    rw [eq_bot_iff, ← h]
    exact le_sup_left
  obtain ⟨H, hH, hdim⟩ := full_of (hfin n) (hetr n) (S ⊔ offSupp S T) (T ⊔ offSupp S T) hS'
    (support_sup_offSupp S T) (exists_isUnit_of_support _ (support_sup_offSupp' S T))
  -- `H` stabilizes `S * T` itself
  have hHSt : Subalgebra.toSubmodule H ≤ St := by
    intro h hh
    rw [hSt]
    intro v hv
    have hv' : v ∈ (S ⊔ offSupp S T) * (T ⊔ offSupp S T) :=
      (Submodule.mul_le.2 fun s hs t ht =>
        Submodule.mul_mem_mul (Submodule.mem_sup_left hs) (Submodule.mem_sup_left ht)) hv
    obtain ⟨a, ha, w, hw, hsum⟩ :=
      Submodule.mem_sup.1 (sup_mul_sup_le S T (hH h ((Subalgebra.mem_toSubmodule _).1 hh) v hv'))
    have hw0 : w = 0 := by
      funext i
      by_cases hK : (∃ s ∈ S, s i ≠ 0) ∧ (∃ t ∈ T, t i ≠ 0)
      · exact hw i hK.1 hK.2
      · have e1 : a i + w i = h i * v i := by
          rw [← Pi.add_apply, hsum, Pi.mul_apply]
        rw [mul_apply_eq_zero ha i hK, mul_apply_eq_zero hv i hK] at e1
        simpa using e1
    rw [hw0, add_zero] at hsum
    rw [← hsum]
    exact ha
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq S (offSupp S T)
  have d2 := Submodule.finrank_sup_add_finrank_inf_eq T (offSupp S T)
  have d3 := finrank_inf_offSupp_add_le S T
  have d4 : finrank ℂ ((S ⊔ offSupp S T) * (T ⊔ offSupp S T) : Submodule ℂ (Fin n → ℂ)) ≤
      finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) + finrank ℂ (offSupp S T) :=
    (Submodule.finrank_mono (sup_mul_sup_le S T)).trans
      (Submodule.finrank_add_le_finrank_add_finrank _ _)
  have d5 : finrank ℂ (Subalgebra.toSubmodule H) ≤ finrank ℂ St := Submodule.finrank_mono hHSt
  omega

end PEqualNP.Outside.Gct114.Helpers.Kneser
end

section
/-- Kneser for codes over the complex numbers (Mirandola and Zemor 2015, Theorem 3.3): for nonzero
subspaces `S`, `T` of `ℂ^n` with coordinatewise product `S * T` and stabilizer `St` of the
product, `dim S + dim T ≤ dim (S * T) + dim St`. From the finiteness of the set of subalgebras
of `ℂ^n`, the e-transform lemma, and a covering argument with a reduction to full support. -/
theorem PEqualNP.Outside.Gct114.Helpers.kneser_fin : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ → (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) → Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St :=
  PEqualNP.Outside.Gct114.Helpers.Kneser.kneser_of PEqualNP.Outside.Gct114.Helpers.Kneser.finite_subalgebra
    PEqualNP.Outside.Gct114.Helpers.Kneser.etransform
end

section
/-! Helper for L-gct-061, proofs only. The Kneser statement for codes over `ℂ` (the form of
L-gct-065) implies the sharp Fermat bound: a subspace `W` of `ℂ^M` on which both power sums
`∑ x_i^2` and `∑ x_i^3` vanish has `3 * dim W ≤ M`. The proof follows the notes in
`FermatProof.md`: polarize, split along an idempotent of the stabilizer of `(W + ℂ1) W`, and
apply Kneser when the stabilizer is the scalars. -/

namespace PEqualNP.Outside.Gct114.Helpers

open Module Finset

section General

variable {ι : Type} [Fintype ι]

/-- The stabilizer of a subspace in the algebra `ι → ℂ`. -/
def stab (V : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {x | ∀ v ∈ V, x * v ∈ V}
  add_mem' {a b} ha hb v hv := by rw [add_mul]; exact V.add_mem (ha v hv) (hb v hv)
  zero_mem' v _ := by rw [zero_mul]; exact V.zero_mem
  smul_mem' c x hx v hv := by rw [smul_mul_assoc]; exact V.smul_mem c (hx v hv)

omit [Fintype ι] in
theorem one_mem_stab (V : Submodule ℂ (ι → ℂ)) : (1 : ι → ℂ) ∈ stab V := fun v hv => by
  rwa [one_mul]

omit [Fintype ι] in
theorem mul_mem_stab {V : Submodule ℂ (ι → ℂ)} {x y : ι → ℂ} (hx : x ∈ stab V)
    (hy : y ∈ stab V) : x * y ∈ stab V := fun v hv => by
  rw [mul_assoc]; exact hx _ (hy v hv)

/-- The dot product as a linear map to the dual. -/
noncomputable def dotDual : (ι → ℂ) →ₗ[ℂ] Module.Dual ℂ (ι → ℂ) :=
  LinearMap.mk₂ ℂ (fun v z => ∑ i, v i * z i)
    (fun a b z => by simp only [Pi.add_apply, add_mul, sum_add_distrib])
    (fun c a z => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum])
    (fun v a b => by simp only [Pi.add_apply, mul_add, sum_add_distrib])
    (fun c v a => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ => by ring)

/-- Lagrange interpolation in the stabilizer: a level set indicator of an element. -/
theorem exists_indicator {V : Submodule ℂ (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ stab V) (i : ι) :
    ∃ e ∈ stab V, ∀ k, e k = if x k = x i then 1 else 0 := by
  classical
  refine ⟨∏ c ∈ (univ.image x).erase (x i), (x i - c)⁻¹ • (x - c • 1), ?_, ?_⟩
  · refine Finset.prod_induction _ (· ∈ stab V) (fun a b ha hb => mul_mem_stab ha hb)
      (one_mem_stab V) fun c _ => ?_
    exact (stab V).smul_mem _ ((stab V).sub_mem hx ((stab V).smul_mem _ (one_mem_stab V)))
  · intro k
    rw [Finset.prod_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
    split_ifs with hk
    · refine Finset.prod_eq_one fun c hc => ?_
      have hc' : c ≠ x i := (Finset.mem_erase.1 hc).1
      rw [hk]
      exact inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hc'))
    · refine Finset.prod_eq_zero (i := x k) ?_ (by rw [sub_self, mul_zero])
      exact Finset.mem_erase.2 ⟨hk, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

end General

end PEqualNP.Outside.Gct114.Helpers
end

section
/-! Helper for L-gct-079, proofs only. Trace-independent subspaces of `ℂ^n`: if `V_1, ..., V_q`
are subspaces of `ℂ^n` such that the sum of the coordinates of every product `t_(i_1) ... t_(i_r)`
(coordinatewise, `r ≥ 1`, distinct indices, `t_i ∈ V_i`) vanishes, then the span of all such
products, the empty one included, has dimension at least `1 + ∑ dim V_i`.

The proof is a chain of Kneser steps (L-gct-065). With `A` the span of the products over subsets
of a set `T` of indices and `k ∉ T`, the step is `dim (A (V_k + ℂ1)) ≥ dim A + dim V_k`. Let `H`
be the stabilizer of `P = A (V_k + ℂ1)`; it is a subalgebra holding `1`. Kneser applied to `A H`
and `(V_k + ℂ1) H`, whose product is `P`, gives
`dim (A + H) + dim (V_k + ℂ1 + H) ≤ dim P + dim H`. The trace form `(x, y) ↦ ∑ x_i y_i` is
nondegenerate on `H` (Lagrange interpolation gives the indicator of a level set), and `A ∩ H`,
`V_k ∩ H` are orthogonal for it, so `dim (A ∩ H) + dim (V_k ∩ H) ≤ dim H`, and the count
closes. -/

namespace PEqualNP.Outside.Gct114.Helpers.ProdSigmaChain

open Module Finset PEqualNP.Outside.Gct114.Helpers

variable {n : ℕ}

/-- Two subspaces orthogonal for the trace form meet a stabilizer in subspaces whose dimensions
add up to at most the dimension of the stabilizer: the trace form is nondegenerate on it. -/
theorem orth_in_stab (P X Y : Submodule ℂ (Fin n → ℂ))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ∑ i, x i * y i = 0) :
    finrank ℂ ↥(X ⊓ stab P) + finrank ℂ ↥(Y ⊓ stab P) ≤ finrank ℂ ↥(stab P) := by
  classical
  let Φ : ↥(Y ⊓ stab P) →ₗ[ℂ] Module.Dual ℂ ↥(stab P) :=
    (stab P).subtype.dualMap ∘ₗ dotDual ∘ₗ (Y ⊓ stab P).subtype
  have hΦ : ∀ (y : ↥(Y ⊓ stab P)) (z : ↥(stab P)),
      Φ y z = ∑ i, (y : Fin n → ℂ) i * (z : Fin n → ℂ) i := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hne
    have hne' : (y : Fin n → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne'
    obtain ⟨e, he, hev⟩ := exists_indicator (V := P) y.2.2 i
    have h := LinearMap.congr_fun hy ⟨e, he⟩
    rw [hΦ] at h
    simp only [LinearMap.zero_apply] at h
    have hsum : ∑ k, (y : Fin n → ℂ) k * e k
        = ((univ.filter fun k => (y : Fin n → ℂ) k = (y : Fin n → ℂ) i).card : ℂ)
          * (y : Fin n → ℂ) i := by
      simp only [hev, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.sum_congr rfl (fun k hk => (Finset.mem_filter.1 hk).2),
        Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at h
    rcases mul_eq_zero.1 h with h0 | h0
    · have hc : (univ.filter fun k => (y : Fin n → ℂ) k = (y : Fin n → ℂ) i).card ≠ 0 :=
        Finset.card_ne_zero.2 ⟨i, by simp⟩
      exact hc (Nat.cast_eq_zero.1 h0)
    · exact hi h0
  let X' : Submodule ℂ ↥(stab P) := (X ⊓ stab P).comap (stab P).subtype
  have hX' : finrank ℂ ↥X' = finrank ℂ ↥(X ⊓ stab P) :=
    (Submodule.comapSubtypeEquivOfLe (inf_le_right : X ⊓ stab P ≤ stab P)).finrank_eq
  have hrange : LinearMap.range Φ ≤ X'.dualAnnihilator := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    rw [hΦ]
    have h0 := hXY _ (show (z : Fin n → ℂ) ∈ X from hz.1) _ y.2.1
    rw [← h0]
    exact sum_congr rfl fun i _ => mul_comm _ _
  have e1 := LinearMap.finrank_range_of_inj hinj
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq X'
  have e3 := Submodule.finrank_mono hrange
  omega

/-- The Kneser step: if `1 ∈ A` and `V` is orthogonal to `A` for the trace form, then
`dim A + dim V ≤ dim (A (V + ℂ1))`. -/
theorem step (hn : 1 ≤ n) (A V : Submodule ℂ (Fin n → ℂ)) (h1 : (1 : Fin n → ℂ) ∈ A)
    (hperp : ∀ a ∈ A, ∀ v ∈ V, ∑ i, a i * v i = 0) :
    finrank ℂ ↥A + finrank ℂ ↥V
      ≤ finrank ℂ ↥(A * (V ⊔ Submodule.span ℂ {(1 : Fin n → ℂ)})) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨E, hE⟩ : ∃ E : Submodule ℂ (Fin n → ℂ), E = Submodule.span ℂ {(1 : Fin n → ℂ)} :=
    ⟨_, rfl⟩
  rw [← hE]
  obtain ⟨S, hS⟩ : ∃ S : Submodule ℂ (Fin n → ℂ), S = V ⊔ E := ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨P, hP⟩ : ∃ P : Submodule ℂ (Fin n → ℂ), P = A * S := ⟨_, rfl⟩
  rw [← hP]
  obtain ⟨H, hH⟩ : ∃ H : Submodule ℂ (Fin n → ℂ), H = stab P := ⟨_, rfl⟩
  have h1E : (1 : Fin n → ℂ) ∈ E := hE ▸ Submodule.mem_span_singleton_self _
  have h1S : (1 : Fin n → ℂ) ∈ S := hS ▸ Submodule.mem_sup_right h1E
  have h1H : (1 : Fin n → ℂ) ∈ H := hH ▸ one_mem_stab P
  have hHH : H * H = H := by
    apply le_antisymm
    · rw [Submodule.mul_le]
      intro x hx y hy
      rw [hH] at hx hy ⊢
      exact mul_mem_stab hx hy
    · intro x hx
      have := Submodule.mul_mem_mul h1H hx
      rwa [one_mul] at this
  have hPH : P * H = P := by
    apply le_antisymm
    · rw [Submodule.mul_le]
      intro p hp x hx
      rw [hH] at hx
      rw [mul_comm]
      exact hx p hp
    · intro p hp
      have := Submodule.mul_mem_mul hp h1H
      rwa [mul_one] at this
  have hprod : (A * H) * (S * H) = P := by
    rw [mul_mul_mul_comm, hHH, ← hP, hPH]
  have hAH : A ⊔ H ≤ A * H := by
    refine sup_le (fun a ha => ?_) (fun x hx => ?_)
    · have := Submodule.mul_mem_mul ha h1H
      rwa [mul_one] at this
    · have := Submodule.mul_mem_mul h1 hx
      rwa [one_mul] at this
  have hSH : S ⊔ H ≤ S * H := by
    refine sup_le (fun a ha => ?_) (fun x hx => ?_)
    · have := Submodule.mul_mem_mul ha h1H
      rwa [mul_one] at this
    · have := Submodule.mul_mem_mul h1S hx
      rwa [one_mul] at this
  have hne1 : A * H ≠ ⊥ := by
    intro h
    have : (1 : Fin n → ℂ) ∈ A * H := hAH (Submodule.mem_sup_left h1)
    rw [h, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hne2 : S * H ≠ ⊥ := by
    intro h
    have : (1 : Fin n → ℂ) ∈ S * H := hSH (Submodule.mem_sup_left h1S)
    rw [h, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hk := PEqualNP.Outside.Gct114.Helpers.kneser_fin n (A * H) (S * H) H hne1 hne2
    (fun x => by rw [hprod, hH]; exact Iff.rfl)
  rw [hprod] at hk
  have a1 := Submodule.finrank_mono hAH
  have a2 := Submodule.finrank_mono hSH
  have a3 := Submodule.finrank_sup_add_finrank_inf_eq A H
  have a4 := Submodule.finrank_sup_add_finrank_inf_eq S H
  have hVE : V ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxE⟩
    rw [hE] at hxE
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxE
    have h0 := hperp 1 h1 _ hxV
    simp only [Pi.one_apply, Pi.smul_apply, smul_eq_mul, mul_one, one_mul, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (Nat.cast_eq_zero.1 h) (by omega)
    · rw [h, zero_smul]
      exact Submodule.zero_mem _
  have hfE : finrank ℂ ↥E = 1 := by
    rw [hE]
    exact finrank_span_singleton one_ne_zero
  have a5 : finrank ℂ ↥S = finrank ℂ ↥V + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq V E
    rw [hVE, finrank_bot, add_zero, hfE, ← hS] at h
    exact h
  have a6 : finrank ℂ ↥(S ⊓ H) ≤ finrank ℂ ↥(V ⊓ H) + 1 := by
    have hle : S ⊓ H ≤ (V ⊓ H) ⊔ E := by
      rintro x ⟨hxS, hxH⟩
      rw [SetLike.mem_coe, hS] at hxS
      obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 hxS
      have hwH : w ∈ H := by
        rw [hE] at hw
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
        exact H.smul_mem c h1H
      have hvH : v ∈ H := by
        have := H.sub_mem hxH hwH
        rwa [add_sub_cancel_right] at this
      exact Submodule.add_mem_sup ⟨hv, hvH⟩ hw
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (V ⊓ H) E
    have h3 := Submodule.finrank_mono hle
    rw [hfE] at h2
    exact h3.trans h2
  have a7 := orth_in_stab P A V hperp
  rw [← hH] at a7
  omega

/-- The span of the products over the subsets of a set `T` of indices. -/
def prodSpan {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ)) (T : Finset (Fin q)) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ {v : Fin n → ℂ | ∃ (S : Finset (Fin q)) (t : Fin q → (Fin n → ℂ)),
    S ⊆ T ∧ (∀ i ∈ S, t i ∈ V i) ∧ v = ∏ i ∈ S, t i}

theorem one_mem_prodSpan {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ)) (T : Finset (Fin q)) :
    (1 : Fin n → ℂ) ∈ prodSpan V T :=
  Submodule.subset_span ⟨∅, 0, empty_subset T, by simp, by simp⟩

/-- Adding one factor to a product over a set not holding its index. -/
theorem prod_insert_update {q : ℕ} (S : Finset (Fin q)) (t : Fin q → (Fin n → ℂ)) (k : Fin q)
    (hk : k ∉ S) (v : Fin n → ℂ) :
    ∏ i ∈ insert k S, Function.update t k v i = (∏ i ∈ S, t i) * v := by
  rw [Finset.prod_insert hk, Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (show i ≠ k from fun h => hk (h ▸ hi))]

theorem update_mem {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ)) (S : Finset (Fin q))
    (t : Fin q → (Fin n → ℂ)) (k : Fin q) (hk : k ∉ S) (v : Fin n → ℂ) (hv : v ∈ V k)
    (ht : ∀ i ∈ S, t i ∈ V i) : ∀ i ∈ insert k S, Function.update t k v i ∈ V i := by
  intro i hi
  rcases Finset.mem_insert.1 hi with rfl | hi
  · rw [Function.update_self]
    exact hv
  · rw [Function.update_of_ne (show i ≠ k from fun h => hk (h ▸ hi))]
    exact ht i hi

/-- The span over `T`, times `V_k + ℂ1`, lies in the span over `T ∪ {k}`. -/
theorem mul_le_insert {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ)) (T : Finset (Fin q))
    (k : Fin q) (hk : k ∉ T) :
    prodSpan V T * (V k ⊔ Submodule.span ℂ {(1 : Fin n → ℂ)}) ≤ prodSpan V (insert k T) := by
  have hmono : prodSpan V T ≤ prodSpan V (insert k T) := by
    refine Submodule.span_mono ?_
    rintro x ⟨S, t, hS, ht, rfl⟩
    exact ⟨S, t, hS.trans (subset_insert _ _), ht, rfl⟩
  have key : ∀ v ∈ V k, ∀ m ∈ prodSpan V T, m * v ∈ prodSpan V (insert k T) := by
    intro v hv m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, t, hS, ht, rfl⟩ := hx
      have hkS : k ∉ S := fun h => hk (hS h)
      exact Submodule.subset_span ⟨insert k S, Function.update t k v, insert_subset_insert k hS,
        update_mem V S t k hkS v hv ht, (prod_insert_update S t k hkS v).symm⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  rw [Submodule.mul_le]
  intro m hm s hs
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 hs
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [mul_add, mul_smul_comm, mul_one]
  exact Submodule.add_mem _ (key v hv m hm) (Submodule.smul_mem _ c (hmono hm))

/-- The span over `T` is orthogonal to `V_k` for the trace form, when `k ∉ T`. -/
theorem prodSpan_perp {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ))
    (hI : ∀ S : Finset (Fin q), S.Nonempty → ∀ t : Fin q → (Fin n → ℂ),
      (∀ i ∈ S, t i ∈ V i) → ∑ j : Fin n, ∏ i ∈ S, t i j = 0)
    (T : Finset (Fin q)) (k : Fin q) (hk : k ∉ T) :
    ∀ a ∈ prodSpan V T, ∀ v ∈ V k, ∑ j, a j * v j = 0 := by
  intro a ha v hv
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, t, hS, ht, rfl⟩ := hx
    have hkS : k ∉ S := fun h => hk (hS h)
    have h0 := hI (insert k S) (insert_nonempty k S) (Function.update t k v)
      (update_mem V S t k hkS v hv ht)
    rw [← h0]
    refine sum_congr rfl fun j _ => ?_
    have := congr_fun (prod_insert_update S t k hkS v) j
    rw [Finset.prod_apply, Pi.mul_apply] at this
    exact this.symm
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply, add_mul, sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx => simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, hx, mul_zero]

/-- The chain of Kneser steps over a set of indices. -/
theorem chain_aux {q : ℕ} (hn : 1 ≤ n) (V : Fin q → Submodule ℂ (Fin n → ℂ))
    (hI : ∀ S : Finset (Fin q), S.Nonempty → ∀ t : Fin q → (Fin n → ℂ),
      (∀ i ∈ S, t i ∈ V i) → ∑ j : Fin n, ∏ i ∈ S, t i j = 0) (T : Finset (Fin q)) :
    ∑ i ∈ T, finrank ℂ ↥(V i) + 1 ≤ finrank ℂ ↥(prodSpan V T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hle : Submodule.span ℂ {(1 : Fin n → ℂ)} ≤ prodSpan V ∅ :=
      (Submodule.span_singleton_le_iff_mem _ _).2 (one_mem_prodSpan V ∅)
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton one_ne_zero] at this
    simpa using this
  | insert k T hk ih =>
    rw [sum_insert hk]
    have h1 := step hn (prodSpan V T) (V k) (one_mem_prodSpan V T) (prodSpan_perp V hI T k hk)
    have h2 := Submodule.finrank_mono (mul_le_insert V T k hk)
    omega

/-- Trace-independent subspaces of `ℂ^n`: the span of the products over all subsets of the
indices has dimension at least one plus the sum of the dimensions. -/
theorem chain (n q : ℕ) (hn : 1 ≤ n)
    (V : Fin q → Submodule ℂ (Fin n → ℂ))
    (hI : ∀ S : Finset (Fin q), S.Nonempty → ∀ t : Fin q → (Fin n → ℂ),
      (∀ i ∈ S, t i ∈ V i) → ∑ j : Fin n, ∏ i ∈ S, t i j = 0) :
    ∑ i : Fin q, Module.finrank ℂ (V i) + 1 ≤
      Module.finrank ℂ (Submodule.span ℂ
        {v : Fin n → ℂ | ∃ (S : Finset (Fin q)) (t : Fin q → (Fin n → ℂ)),
          (∀ i ∈ S, t i ∈ V i) ∧ v = ∏ i ∈ S, t i}) := by
  have h := chain_aux hn V hI univ
  refine h.trans (Submodule.finrank_mono (Submodule.span_mono ?_))
  rintro x ⟨S, t, -, ht, rfl⟩
  exact ⟨S, t, ht, rfl⟩

end PEqualNP.Outside.Gct114.Helpers.ProdSigmaChain
end

section
/-! Helpers for L-gct-079 (product-type linear spaces through Sigma_m inside the permanent
hypersurface have dimension at most 2m - 2).

The permanent of a matrix whose rows outside a set `T` are all ones is handled without any
sum over injections: `sum_mul_permanent` (multiply one row at a time pointwise by a vector) and
invariance under row swaps give the recursion `rowMat_rec`, and the closed formula
`rowMat_perm_formula` follows by induction on the set of special rows.

The main theorem `main` takes the chain inequality (proved by another module) as a hypothesis. -/

namespace PEqualNP.Outside.Gct114.Helpers.ProdSigma

open Finset

variable {m : ℕ}

theorem eval_permPoly (z : Fin m × Fin m → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ m) =
      (Matrix.of fun i j => z (i, j)).permanent := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

/-- Multiplying the rows one at a time pointwise by `v` and adding the permanents gives the sum
of the entries of `v` times the permanent. -/
theorem sum_mul_permanent (A : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    (∑ c, v c) * A.permanent = ∑ j, (A.updateRow j (A j * v)).permanent := by
  unfold Matrix.permanent
  rw [mul_sum, sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  have h : ∀ j, ∏ i, (A.updateRow j (A j * v)) (σ i) i = v (σ.symm j) * ∏ i, A (σ i) i := by
    intro j
    have h1 : ∀ i, (A.updateRow j (A j * v)) (σ i) i =
        (if i = σ.symm j then v i else 1) * A (σ i) i := by
      intro i
      by_cases hi : i = σ.symm j
      · subst hi
        simp [Matrix.updateRow_self, mul_comm]
      · have hne : σ i ≠ j := fun h => hi (by rw [← h]; simp)
        rw [Matrix.updateRow_ne hne]
        simp [hi]
    simp_rw [h1, prod_mul_distrib]
    simp
  simp_rw [h, ← sum_mul]
  congr 1
  exact (Equiv.sum_comp σ.symm v).symm

/-- The matrix with row `i` equal to `r i` for `i ∈ T` and all ones otherwise. -/
def rowMat (T : Finset (Fin m)) (r : Fin m → Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if i ∈ T then r i j else 1

theorem rowMat_apply (T : Finset (Fin m)) (r : Fin m → Fin m → ℂ) (i j : Fin m) :
    rowMat T r i j = if i ∈ T then r i j else 1 := rfl

/-- The recursion: making one more row special. -/
theorem rowMat_rec (T : Finset (Fin m)) (r : Fin m → Fin m → ℂ) (i0 : Fin m) (hi0 : i0 ∉ T) :
    (∑ c, r i0 c) * (rowMat T r).permanent =
      ((Tᶜ.card : ℕ) : ℂ) * (rowMat (insert i0 T) r).permanent +
        ∑ k ∈ T, (rowMat T (fun i j => if i = k then r k j * r i0 j else r i j)).permanent := by
  rw [sum_mul_permanent, ← sum_add_sum_compl T, add_comm]
  congr 1
  · rw [← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun j hj => ?_
    have hjT : j ∉ T := mem_compl.1 hj
    rw [← Matrix.permanent_permute_cols (Equiv.swap j i0)]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, id_eq, Matrix.updateRow_apply, rowMat_apply, Pi.mul_apply,
      mem_insert]
    by_cases ha : a = i0
    · subst ha
      simp [hjT]
    · by_cases haj : a = j
      · subst haj
        have : i0 ≠ a := fun h => ha h.symm
        simp [hjT, hi0, this, ha]
      · rw [Equiv.swap_apply_of_ne_of_ne haj ha]
        simp [haj, ha]
  · refine sum_congr rfl fun k hk => ?_
    congr 1
    ext a b
    simp only [Matrix.updateRow_apply, rowMat_apply, Pi.mul_apply]
    by_cases ha : a = k
    · subst ha
      simp [hk]
    · simp [ha]

theorem permanent_ones : (rowMat (∅ : Finset (Fin m)) fun _ _ => 0).permanent
    = (m.factorial : ℂ) := by
  simp [Matrix.permanent, rowMat, Fintype.card_perm]

theorem rowMat_empty (r r' : Fin m → Fin m → ℂ) :
    rowMat (∅ : Finset (Fin m)) r = rowMat ∅ r' := by
  ext a b
  simp [rowMat_apply]

/-- One special row. -/
theorem rowMat_single (a : Fin m) (d : ℕ) (hd : 1 + d = m) (r : Fin m → Fin m → ℂ) :
    (rowMat {a} r).permanent = (d.factorial : ℂ) * ∑ j, r a j := by
  have h := rowMat_rec (∅ : Finset (Fin m)) r a (notMem_empty a)
  rw [rowMat_empty r (fun _ _ => 0), permanent_ones] at h
  simp only [sum_empty, add_zero, compl_empty, card_univ, Fintype.card_fin,
    insert_empty_eq] at h
  have hfac : m.factorial = m * d.factorial := by
    rw [← hd, add_comm, Nat.factorial_succ]
  have hne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  apply mul_left_cancel₀ hne
  rw [← h, hfac]
  push_cast
  ring

theorem prod_ite_mul (Q : Finset (Fin m)) (r : Fin m → Fin m → ℂ) (k i0 j : Fin m) :
    ∏ i ∈ Q, (if i = k then r k j * r i0 j else r i j) =
      (∏ i ∈ Q, r i j) * (if k ∈ Q then r i0 j else 1) := by
  have h : ∀ i, (if i = k then r k j * r i0 j else r i j) =
      r i j * (if i = k then r i0 j else 1) := by
    intro i
    by_cases hi : i = k
    · subst hi; simp
    · simp [hi]
  simp_rw [h, prod_mul_distrib]
  congr 1
  simp

/-- The closed formula. Rows in `S` are `r i`, row `a` is `r a`, the other `d` rows are all
ones. If the sum of the entries of the pointwise product of the rows of every nonempty proper
subset of `S` vanishes, and either the row `a` or the product over `S` has entry sum zero, then
the permanent is `d! (-1)^s s!` times the sum of the entries of the product of all rows. -/
theorem rowMat_perm_formula (a : Fin m) : ∀ S : Finset (Fin m), a ∉ S → ∀ d : ℕ,
    S.card + 1 + d = m → ∀ r : Fin m → Fin m → ℂ,
    (∀ Q : Finset (Fin m), Q ⊆ S → Q.Nonempty → Q ≠ S → ∑ j, ∏ i ∈ Q, r i j = 0) →
    (S.Nonempty → (∑ j, r a j = 0) ∨ (∑ j, ∏ i ∈ S, r i j = 0)) →
    (rowMat (insert a S) r).permanent =
      (d.factorial : ℂ) * (-1) ^ S.card * (S.card.factorial : ℂ) *
        ∑ j, r a j * ∏ i ∈ S, r i j := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ d hd r _ _
    have := rowMat_single a d (by simpa [add_comm] using hd) r
    simpa using this
  | insert i0 S' hi0 ih =>
    intro ha d hd r h1 h2
    have hai : a ≠ i0 := fun h => ha (h ▸ mem_insert_self _ _)
    have haS : a ∉ S' := fun h => ha (mem_insert_of_mem h)
    have hcard : (insert i0 S').card = S'.card + 1 := card_insert_of_notMem hi0
    rw [hcard] at hd
    have hd' : S'.card + 1 + (d + 1) = m := by omega
    have hi0T : i0 ∉ insert a S' := by
      simp only [mem_insert, not_or]
      exact ⟨fun h => hai h.symm, hi0⟩
    have hrec := rowMat_rec (insert a S') r i0 hi0T
    set X : ℂ := ∑ j, r a j * ∏ i ∈ insert i0 S', r i j with hX
    set C : ℂ := ((d + 1).factorial : ℂ) * (-1) ^ S'.card * (S'.card.factorial : ℂ) with hC
    -- the left side vanishes
    have hleft : (∑ c, r i0 c) * (rowMat (insert a S') r).permanent = 0 := by
      rcases S'.eq_empty_or_nonempty with hS | hS
      · subst hS
        rw [insert_empty_eq, rowMat_single a (d + 1) (by simpa [add_comm] using hd') r]
        rcases h2 (insert_nonempty _ _) with h | h
        · rw [h]; ring
        · have : ∑ c, r i0 c = 0 := by simpa using h
          rw [this]; ring
      · have : ∑ c, r i0 c = 0 := by
          have := h1 {i0} (by simp) (singleton_nonempty _) (by
            intro h
            obtain ⟨x, hx⟩ := hS
            have : x ∈ ({i0} : Finset (Fin m)) := h ▸ mem_insert_of_mem hx
            rw [mem_singleton] at this
            exact hi0 (this ▸ hx))
          simpa using this
        rw [this]; ring
    -- hypotheses about subsets of S'
    have hsub : ∀ Q : Finset (Fin m), Q ⊆ S' → Q.Nonempty → ∑ j, ∏ i ∈ Q, r i j = 0 := by
      intro Q hQ hne
      refine h1 Q (hQ.trans (subset_insert _ _)) hne ?_
      intro h
      exact hi0 (hQ (h ▸ mem_insert_self _ _))
    have hsub2 : ∀ Q : Finset (Fin m), Q ⊆ S' → Q ≠ S' →
        ∑ j, ∏ i ∈ insert i0 Q, r i j = 0 := by
      intro Q hQ hne
      refine h1 (insert i0 Q) (insert_subset_insert _ hQ) (insert_nonempty _ _) ?_
      intro h
      apply hne
      have hi0Q : i0 ∉ Q := fun h => hi0 (hQ h)
      rw [← erase_insert hi0Q, h, erase_insert hi0]
    have hprodins : ∀ (Q : Finset (Fin m)), Q ⊆ S' → ∀ j,
        ∏ i ∈ insert i0 Q, r i j = (∏ i ∈ Q, r i j) * r i0 j := by
      intro Q hQ j
      rw [prod_insert (fun h => hi0 (hQ h)), mul_comm]
    -- the term k = a
    have hta : (rowMat (insert a S')
        (fun i j => if i = a then r a j * r i0 j else r i j)).permanent = C * X := by
      rw [ih haS (d + 1) hd' _ ?_ ?_]
      · rw [hC, hX]
        congr 1
        refine sum_congr rfl fun j _ => ?_
        rw [prod_ite_mul, if_neg haS, if_pos rfl, hprodins S' subset_rfl]
        ring
      · intro Q hQ hne _
        have : ∀ j, ∏ i ∈ Q, (if i = a then r a j * r i0 j else r i j) = ∏ i ∈ Q, r i j := by
          intro j
          rw [prod_ite_mul, if_neg (fun h => haS (hQ h)), mul_one]
        simp_rw [this]
        exact hsub Q hQ hne
      · intro hne
        right
        have : ∀ j, ∏ i ∈ S', (if i = a then r a j * r i0 j else r i j) = ∏ i ∈ S', r i j := by
          intro j
          rw [prod_ite_mul, if_neg haS, mul_one]
        simp_rw [this]
        exact hsub S' subset_rfl hne
    -- the terms k ∈ S'
    have htk : ∀ k ∈ S', (rowMat (insert a S')
        (fun i j => if i = k then r k j * r i0 j else r i j)).permanent = C * X := by
      intro k hk
      have hak : a ≠ k := fun h => haS (h ▸ hk)
      rw [ih haS (d + 1) hd' _ ?_ ?_]
      · rw [hC, hX]
        congr 1
        refine sum_congr rfl fun j _ => ?_
        rw [prod_ite_mul, if_pos hk, if_neg hak, hprodins S' subset_rfl]
      · intro Q hQ hne hneq
        by_cases hkQ : k ∈ Q
        · have : ∀ j, ∏ i ∈ Q, (if i = k then r k j * r i0 j else r i j) =
              ∏ i ∈ insert i0 Q, r i j := by
            intro j
            rw [prod_ite_mul, if_pos hkQ, hprodins Q hQ]
          simp_rw [this]
          exact hsub2 Q hQ hneq
        · have : ∀ j, ∏ i ∈ Q, (if i = k then r k j * r i0 j else r i j) = ∏ i ∈ Q, r i j := by
            intro j
            rw [prod_ite_mul, if_neg hkQ, mul_one]
          simp_rw [this]
          exact hsub Q hQ hne
      · intro _
        rcases h2 (insert_nonempty _ _) with h | h
        · left
          simpa [hak] using h
        · right
          have : ∀ j, ∏ i ∈ S', (if i = k then r k j * r i0 j else r i j) =
              ∏ i ∈ insert i0 S', r i j := by
            intro j
            rw [prod_ite_mul, if_pos hk, hprodins S' subset_rfl]
          simp_rw [this]
          exact h
    have hcompl : (insert a S')ᶜ.card = d + 1 := by
      rw [card_compl, Fintype.card_fin, card_insert_of_notMem haS]
      omega
    rw [hleft, hcompl, sum_insert haS, hta, sum_congr rfl htk, sum_const, nsmul_eq_mul,
      Finset.insert_comm] at hrec
    have hne : ((d : ℂ) + 1) ≠ 0 := by
      have : (((d + 1 : ℕ)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simpa using this
    apply mul_left_cancel₀ hne
    rw [hcard]
    have hC' : C = ((d : ℂ) + 1) * (d.factorial : ℂ) * (-1) ^ S'.card *
        (S'.card.factorial : ℂ) := by
      rw [hC, Nat.factorial_succ]
      push_cast
      ring
    rw [Nat.factorial_succ S'.card]
    push_cast at hrec ⊢
    rw [hC'] at hrec
    linear_combination -hrec

end PEqualNP.Outside.Gct114.Helpers.ProdSigma
end

namespace PEqualNP.Outside.Gct114

open Finset PEqualNP.Outside.Gct114.Helpers.ProdSigma

private theorem permanent_sum {n : ℕ} (A : Finset (Fin n)) (t : Fin n → Fin n → ℂ) :
    (Matrix.of (fun i j => if i ∈ A then 1 + t i j else 1)).permanent =
      ∑ B ∈ A.powerset, (rowMat B t).permanent := by
  classical
  have rowExpansion (M : Matrix (Fin n) (Fin n) ℂ) :
      M.permanent = ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ i) := by
    rw [← Matrix.permanent_transpose M]
    rfl
  simp only [rowExpansion, Matrix.of_apply, rowMat_apply]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.prod_one_add]
  refine sum_congr rfl fun B _ => ?_
  rw [← Finset.prod_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

private theorem row_permanent_zero {n : ℕ} (V : Fin n → Submodule ℂ (Fin n → ℂ))
    (h : ∀ t : Fin n → Fin n → ℂ, (∀ i, t i ∈ V i) →
      (Matrix.of (fun i j => 1 + t i j)).permanent = (n.factorial : ℂ)) :
    ∀ A : Finset (Fin n), A.Nonempty → ∀ t : Fin n → Fin n → ℂ,
      (∀ i ∈ A, t i ∈ V i) → (rowMat A t).permanent = 0 := by
  classical
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    intro hA t ht
    let u : Fin n → Fin n → ℂ := fun i => if i ∈ A then t i else 0
    have hu : ∀ i, u i ∈ V i := by
      intro i
      by_cases hi : i ∈ A
      · simpa [u, hi] using ht i hi
      · simp [u, hi]
    have hmat : (Matrix.of (fun i j => 1 + u i j)) =
        Matrix.of (fun i j => if i ∈ A then 1 + t i j else 1) := by
      ext i j
      by_cases hi : i ∈ A <;> simp [u, hi]
    have he := h u hu
    rw [hmat, permanent_sum] at he
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_powerset.mpr (Finset.Subset.refl A))] at he
    have hrest : ∑ B ∈ A.powerset \ {A}, (rowMat B t).permanent = (n.factorial : ℂ) := by
      rw [Finset.sum_eq_single ∅]
      · rw [rowMat_empty t (fun _ _ => 0), permanent_ones]
      · intro B hB hB0
        have hBA := Finset.mem_sdiff.mp hB
        have hsub := Finset.mem_powerset.mp hBA.1
        exact ih B (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by simpa using hBA.2⟩)
          (Finset.nonempty_iff_ne_empty.mpr hB0) t (fun i hi => ht i (hsub hi))
      · intro hnot
        exact (hnot (by simp [Ne.symm hA.ne_empty])).elim
    rw [hrest] at he
    exact add_right_cancel (he.trans (zero_add _).symm)

private theorem row_dimension {n : ℕ} (hn : 1 ≤ n)
    (V : Fin n → Submodule ℂ (Fin n → ℂ))
    (h : ∀ t : Fin n → Fin n → ℂ, (∀ i, t i ∈ V i) →
      (Matrix.of (fun i j => 1 + t i j)).permanent = (n.factorial : ℂ)) :
    (∑ i, Module.finrank ℂ (V i)) + 1 ≤ n := by
  classical
  have hz := row_permanent_zero V h
  have hd : ∀ A : Finset (Fin n), A.Nonempty → ∀ t : Fin n → Fin n → ℂ,
      (∀ i ∈ A, t i ∈ V i) → ∑ j, ∏ i ∈ A, t i j = 0 := by
    intro A
    induction A using Finset.strongInduction with
    | H A ih =>
      intro hA t ht
      obtain ⟨a, ha⟩ := hA
      let S := A.erase a
      have haS : a ∉ S := Finset.notMem_erase _ _
      have hAS : insert a S = A := Finset.insert_erase ha
      have hsub : S ⊂ A := Finset.erase_ssubset ha
      have hcard : S.card + 1 + (n - (S.card + 1)) = n := by
        have hc : A.card ≤ n := by simpa using Finset.card_le_univ A
        rw [← hAS, Finset.card_insert_of_notMem haS] at hc
        omega
      have hf := rowMat_perm_formula a S haS _ hcard t
        (fun Q hQS hQ _ => ih Q (lt_of_le_of_lt hQS hsub) hQ t
          (fun i hi => ht i (hsub.le (hQS hi))))
        (fun hS => Or.inr (ih S hsub hS t (fun i hi => ht i (hsub.le hi))))
      rw [hAS, hz A ⟨a, ha⟩ t ht] at hf
      have hc : ((n - (S.card + 1)).factorial : ℂ) * (-1) ^ S.card *
          (S.card.factorial : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
          (pow_ne_zero _ (by norm_num))) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      rw [← hAS]
      simp_rw [Finset.prod_insert haS]
      exact (mul_eq_zero.mp hf.symm).resolve_left hc
  have hb := PEqualNP.Outside.Gct114.Helpers.ProdSigmaChain.chain n n hn V hd
  exact hb.trans ((Submodule.finrank_le _).trans (Module.finrank_fin_fun ℂ).le)

end PEqualNP.Outside.Gct114

theorem PEqualNP.Outside.L_gct_114 : ∀ (n : ℕ) (V S : Fin n → Submodule ℂ (Fin n → ℂ)), (∀ r c : Fin n × Fin n → ℂ, (∀ i : Fin n, (fun j : Fin n => r (i, j)) ∈ V i) → (∀ j : Fin n, (fun i : Fin n => c (i, j)) ∈ S j) → MvPolynomial.eval (fun p => 1 + (r p + c p)) (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) → ∑ i : Fin n, Module.finrank ℂ (V i) + ∑ j : Fin n, Module.finrank ℂ (S j) ≤ 2 * n - 2 := by
  intro n V S h
  by_cases hn : 1 ≤ n
  · have hV := PEqualNP.Outside.Gct114.row_dimension hn V (fun t ht => by
      simpa [PEqualNP.Outside.Gct114.Helpers.ProdSigma.eval_permPoly] using
        h (fun p => t p.1 p.2) 0 ht (fun j => (S j).zero_mem))
    have hS := PEqualNP.Outside.Gct114.row_dimension hn S (fun t ht => by
      rw [← Matrix.permanent_transpose]
      simpa [PEqualNP.Outside.Gct114.Helpers.ProdSigma.eval_permPoly, Matrix.transpose_apply] using
        h 0 (fun p => t p.2 p.1) (fun i => (V i).zero_mem) ht)
    omega
  · have : n = 0 := by omega
    subst n
    simp
