import Mathlib
import PEqualNP.Defs

open Finset

-- Scale the permanent by the support size and evaluate the resulting polynomial at zero.
private lemma scaled_constant {n : ℕ} (u v : Fin n → ℂ) (S : Finset (Fin n))
    (hout : ∀ j ∉ S, v j = 0) (hsize : S.card ≠ 0)
    (h : ∀ z : ℂ, (∑ σ : Equiv.Perm (Fin n), ∏ j, (1 + z * u (σ j) * v j)) = n.factorial) :
    (∑ σ : Equiv.Perm (Fin n), ∏ j ∈ S, (u (σ j) * v j)) = 0 := by
  classical
  let F : ℂ → ℂ := fun z => ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ S, (z + u (σ j) * v j)
  let G : ℂ → ℂ := fun z => z ^ S.card * n.factorial
  have same : Set.EqOn F G ({0}ᶜ : Set ℂ) := by
    intro z hz
    have hne : z ≠ 0 := hz
    dsimp [F, G]
    rw [← h z⁻¹, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    calc
      (∏ j ∈ S, (z + u (σ j) * v j)) = ∏ j ∈ S, (z * (1 + z⁻¹ * u (σ j) * v j)) := by
        apply Finset.prod_congr rfl
        intro j _
        field_simp [hne]
      _ = z ^ S.card * ∏ j ∈ S, (1 + z⁻¹ * u (σ j) * v j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ = z ^ S.card * ∏ j, (1 + z⁻¹ * u (σ j) * v j) := by
        congr 1
        exact Finset.prod_subset (Finset.subset_univ S) fun j _ hj => by simp [hout j hj]
  have h0 : F 0 = G 0 := same.closure (by dsimp [F]; fun_prop) (by dsimp [G]; fun_prop)
    (dense_compl_singleton (0 : ℂ) 0)
  simpa [F, G, zero_pow hsize] using h0

-- A surviving permutation maps the support of v onto the support of u.
-- Its product then depends only on those two supports.
theorem PEqualNP.Outside.L_gct_121 :
    ∀ (n : ℕ) (u v : Fin n → ℂ), u ≠ 0 → v ≠ 0 →
      (∀ μ : ℂ, MvPolynomial.eval (fun p : Fin n × Fin n => 1 + μ * u p.1 * v p.2)
        (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ)) →
      (Finset.univ.filter (fun i => u i ≠ 0)).card ≠
        (Finset.univ.filter (fun j => v j ≠ 0)).card := by
  classical
  intro n u v _ hv level equal_sizes
  let U := Finset.univ.filter fun i => u i ≠ 0
  let V := Finset.univ.filter fun j => v j ≠ 0
  change U.card = V.card at equal_sizes
  have memU (i) : i ∈ U ↔ u i ≠ 0 := by simp [U]
  have memV (j) : j ∈ V ↔ v j ≠ 0 := by simp [V]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have hsize := Finset.card_ne_zero.mpr (show V.Nonempty from ⟨j, (memV j).mpr hj⟩)
  have leading := scaled_constant u v V (fun j hj => by simpa [memV] using hj) hsize
    (fun z => by simpa [PEqualNP.Gct.permPoly, Matrix.permanent] using level z)
  let good := Finset.univ.filter fun σ : Equiv.Perm (Fin n) => V.map σ.toEmbedding = U
  have memGood (σ : Equiv.Perm (Fin n)) : σ ∈ good ↔ V.map σ.toEmbedding = U := by
    simp [good]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq V U equal_sizes.symm
  have count : (good.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero.mpr ⟨σ, (memGood σ).mpr hσ⟩)
  let weight := (∏ i ∈ U, u i) * ∏ j ∈ V, v j
  have weight_ne : weight ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i hi => (memU i).mp hi)
    (Finset.prod_ne_zero_iff.mpr fun j hj => (memV j).mp hj)
  apply mul_ne_zero count weight_ne
  calc
    (good.card : ℂ) * weight = ∑ _σ ∈ good, weight := by simp
    _ = ∑ σ ∈ good, ∏ j ∈ V, (u (σ j) * v j) := by
      refine Finset.sum_congr rfl fun σ hσ => ?_
      simp only [weight, ← (memGood σ).mp hσ, Finset.prod_map, Finset.prod_mul_distrib,
        Equiv.coe_toEmbedding]
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ j ∈ V, (u (σ j) * v j) := by
      refine Finset.sum_subset (Finset.subset_univ good) fun σ _ hσ => ?_
      by_contra hprod
      apply hσ
      apply (memGood σ).mpr
      apply Finset.eq_of_subset_of_card_le _ (by simp [equal_sizes])
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      apply (memU _).mpr
      exact left_ne_zero_of_mul (Finset.prod_ne_zero_iff.mp hprod j hj)
    _ = 0 := leading
