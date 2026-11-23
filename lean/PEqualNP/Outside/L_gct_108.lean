import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_108_aux

open Finset

private def rowPart (k : ℕ) (v : Fin k → ℂ) : Fin (k + 1) → ℂ :=
  Fin.lastCases (-∑ i, v i) v

private lemma rowPart_last (k : ℕ) (v : Fin k → ℂ) :
    rowPart k v (Fin.last k) = -∑ i, v i :=
  Fin.lastCases_last

private lemma rowPart_castSucc (k : ℕ) (v : Fin k → ℂ) (i : Fin k) :
    rowPart k v i.castSucc = v i := by
  simp [rowPart]

private lemma sum_rowPart (k : ℕ) (v : Fin k → ℂ) : ∑ j : Fin (k + 1), rowPart k v j = 0 := by
  rw [Fin.sum_univ_castSucc, rowPart_last]
  simp only [rowPart_castSucc, add_neg_cancel]

private def rowFun (k : ℕ) (v : Fin k → ℂ) (p : Fin 2 × Fin (k + 1)) : ℂ :=
  Fin.cases (rowPart k v p.2) (fun _ => 0) p.1

private lemma rowFun_zero (k : ℕ) (v : Fin k → ℂ) (j : Fin (k + 1)) :
    rowFun k v (0, j) = rowPart k v j := rfl

private lemma rowFun_succ (k : ℕ) (v : Fin k → ℂ) (b : Fin 1) (j : Fin (k + 1)) :
    rowFun k v (b.succ, j) = 0 := rfl

private lemma rowFun_one (k : ℕ) (v : Fin k → ℂ) (j : Fin (k + 1)) :
    rowFun k v (1, j) = 0 := rfl

private def rowMap (k : ℕ) : (Fin k → ℂ) →ₗ[ℂ] (Fin 2 × Fin (k + 1) → ℂ) where
  toFun := rowFun k
  map_add' v w := by
    funext ⟨a, j⟩
    refine Fin.cases ?_ ?_ a
    · simp only [Pi.add_apply, rowFun_zero]
      refine Fin.lastCases ?_ ?_ j
      · simp only [rowPart_last, Pi.add_apply, sum_add_distrib]; ring
      · intro i; simp only [rowPart_castSucc, Pi.add_apply]
    · intro b
      simp only [Pi.add_apply, rowFun_succ, add_zero]
  map_smul' c v := by
    funext ⟨a, j⟩
    refine Fin.cases ?_ ?_ a
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, rowFun_zero]
      refine Fin.lastCases ?_ ?_ j
      · simp only [rowPart_last, Pi.smul_apply, smul_eq_mul]
        rw [← mul_sum]; ring
      · intro i; simp only [rowPart_castSucc, Pi.smul_apply, smul_eq_mul]
    · intro b
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, rowFun_succ, mul_zero]

private lemma rowMap_injective (k : ℕ) : Function.Injective (rowMap k) := by
  intro v w h
  funext i
  have h1 := congrFun h (0, i.castSucc)
  simpa only [rowMap, LinearMap.coe_mk, AddHom.coe_mk, rowFun_zero, rowPart_castSucc] using h1

theorem witness :
    ∀ (q : ℕ), 2 ≤ q →
      ∃ L : Submodule ℂ (Fin 2 × Fin q → ℂ),
        (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧
          (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) ∧
        Module.finrank ℂ L + 1 = q := by
  intro q hq
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  refine ⟨LinearMap.range (rowMap k), ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    constructor
    · simp only [rowMap, LinearMap.coe_mk, AddHom.coe_mk, rowFun_zero, rowFun_one, add_zero,
        sum_rowPart]
    · simp [rowMap, rowFun_one]
  · rw [LinearMap.finrank_range_of_inj (rowMap_injective k), Module.finrank_fin_fun]

end PEqualNP.Outside.L_gct_108_aux

theorem PEqualNP.Outside.L_gct_108 : ∀ (q : ℕ), 2 ≤ q → ∃ L : Submodule ℂ (Fin 2 × Fin q → ℂ), (∀ t ∈ L, (∑ j, (t (0, j) + t (1, j))) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else t (0, j) * t (1, l)) = 0) ∧ Module.finrank ℂ L + 1 = q :=
  PEqualNP.Outside.L_gct_108_aux.witness
