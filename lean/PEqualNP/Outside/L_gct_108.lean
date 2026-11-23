import Mathlib
import PEqualNP.Defs

/-!
Witness for the tight two-row dimension bound: matrices with second row zero and first row
summing to zero form an admissible subspace of dimension `q - 1`.
-/

namespace PEqualNP.Outside.L_gct_108

open Finset Submodule

variable (q : ℕ)

noncomputable def eval1 (j : Fin q) : (Fin 2 × Fin q → ℂ) →ₗ[ℂ] ℂ where
  toFun t := t (1, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def rowSumAll : (Fin 2 × Fin q → ℂ) →ₗ[ℂ] ℂ where
  toFun t := ∑ j, (t (0, j) + t (1, j))
  map_add' t s := by simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' c t := by simp [Finset.mul_sum, mul_add]

noncomputable def embedRow0 : (Fin q → ℂ) →ₗ[ℂ] (Fin 2 × Fin q → ℂ) where
  toFun f := fun p => if p.1 = 0 then f p.2 else 0
  map_add' f g := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> simp [Pi.add_apply]
  map_smul' c f := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]

noncomputable def firstRowSum : (Fin q → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ j, f j
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum, smul_eq_mul]

noncomputable def witnessL : Submodule ℂ (Fin 2 × Fin q → ℂ) :=
  (⨅ j : Fin q, LinearMap.ker (eval1 q j)) ⊓ LinearMap.ker (rowSumAll q)

lemma mem_witnessL {t : Fin 2 × Fin q → ℂ} :
    t ∈ witnessL q ↔ (∀ j, t (1, j) = 0) ∧ ∑ j, (t (0, j) + t (1, j)) = 0 := by
  constructor <;> intro h <;>
    simpa [witnessL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, eval1, rowSumAll] using h

lemma quad_zero {t : Fin 2 × Fin q → ℂ} (ht : t ∈ witnessL q) :
    (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0 := by
  have h1 : ∀ l, t (1, l) = 0 := fun l => (mem_witnessL q).mp ht |>.1 l
  rw [Finset.sum_eq_zero]
  intro j _
  rw [Finset.sum_eq_zero]
  intro l _
  split_ifs with h <;> simp [h1 l, h1 j, mul_zero, zero_mul]

lemma embed_inj : Function.Injective (embedRow0 q) := by
  intro f g h
  funext j
  simpa [embedRow0] using congr_arg (fun t => t (0, j)) h

lemma embedRow0_apply0 (f : Fin q → ℂ) (j : Fin q) : embedRow0 q f (0, j) = f j := by
  simp [embedRow0]

lemma embedRow0_apply1 (f : Fin q → ℂ) (j : Fin q) : embedRow0 q f (1, j) = 0 := by
  simp [embedRow0]

lemma rowSumAll_embed (f : Fin q → ℂ) :
    rowSumAll q (embedRow0 q f) = firstRowSum q f := by
  simp [rowSumAll, firstRowSum, embedRow0_apply0 q, embedRow0_apply1 q, add_zero]

lemma witnessL_eq :
    witnessL q = Submodule.map (embedRow0 q) (LinearMap.ker (firstRowSum q)) := by
  ext t
  constructor
  · intro ht
    have h := (mem_witnessL q).mp ht
    let f : Fin q → ℂ := fun j => t (0, j)
    have hsum : ∑ j, f j = ∑ j, (t (0, j) + t (1, j)) :=
      Finset.sum_congr rfl fun j _ => by simp [f, h.1 j, add_zero]
    have hf : firstRowSum q f = 0 := by simpa [firstRowSum, hsum] using h.2
    have ht' : t = embedRow0 q f := by
      funext p
      rcases p with ⟨i, j⟩
      fin_cases i
      · simp [f, embedRow0]
      · simp [f, embedRow0, h.1 j]
    refine ⟨f, LinearMap.mem_ker.mpr hf, ?_⟩
    rwa [ht']
  · rintro ⟨f, hf, rfl⟩
    refine (mem_witnessL q).mpr ⟨fun j => embedRow0_apply1 q f j, ?_⟩
    simpa [rowSumAll, firstRowSum, embedRow0_apply0 q, embedRow0_apply1 q, add_zero] using
      LinearMap.mem_ker.mp hf

lemma firstRowSum_surjective (hq : 2 ≤ q) : Function.Surjective (firstRowSum q) := by
  haveI : NeZero q := ⟨by omega⟩
  intro c
  refine ⟨(fun j => if j = 0 then c else 0), ?_⟩
  simp [firstRowSum, Finset.sum_ite, Finset.filter_eq', Finset.mem_univ, NeZero.ne q]

lemma finrank_ker_firstRowSum (hq : 2 ≤ q) :
    Module.finrank ℂ ↥(LinearMap.ker (firstRowSum q)) = q - 1 := by
  have hdim : Module.finrank ℂ (Fin q → ℂ) = q :=
    Module.finrank_fin_fun (R := ℂ) (n := q)
  have hfin : Module.finrank ℂ ℂ = 1 := CommSemiring.finrank_self ℂ
  have htop : LinearMap.range (firstRowSum q) = ⊤ :=
    LinearMap.range_eq_top.mpr (firstRowSum_surjective q hq)
  have hrank : Module.finrank ℂ ↥(LinearMap.range (firstRowSum q)) = 1 := by
    rw [htop]
    unfold Module.finrank at hfin ⊢
    simpa using hfin
  have := LinearMap.finrank_range_add_finrank_ker (firstRowSum q)
  rw [hrank, hdim] at this
  omega

lemma finrank_map_ker :
    Module.finrank ℂ ↥(Submodule.map (embedRow0 q) (LinearMap.ker (firstRowSum q))) =
      Module.finrank ℂ ↥(LinearMap.ker (firstRowSum q)) := by
  simpa using (Submodule.equivMapOfInjective (embedRow0 q) (embed_inj q)
    (LinearMap.ker (firstRowSum q))).symm.finrank_eq

lemma finrank_witness (hq : 2 ≤ q) : Module.finrank ℂ (witnessL q) + 1 = q := by
  rw [witnessL_eq q, finrank_map_ker q, finrank_ker_firstRowSum q hq]
  omega

end PEqualNP.Outside.L_gct_108

open PEqualNP.Outside.L_gct_108

theorem PEqualNP.Outside.L_gct_108 : ∀ (q : ℕ), 2 ≤ q →
    ∃ L : Submodule ℂ (Fin 2 × Fin q → ℂ),
      (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧
        (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) ∧
      Module.finrank ℂ L + 1 = q := by
  intro q hq
  refine ⟨witnessL q, ?_, ?_⟩
  · intro t ht
    have h := (mem_witnessL q).mp ht
    exact ⟨h.2, quad_zero q ht⟩
  · exact finrank_witness q hq