import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_208_aux

def embedMap : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun v p :=
    match p.1.val, p.2.val with
    | 0, 0 => -(v 0 + v 1 + v 2 + v 3 + v 4)
    | 0, 1 => v 0
    | 0, 2 => v 1
    | 0, 3 => v 2
    | 0, 4 => v 3
    | 0, 5 => v 4
    | 1, 0 => -(v 5 + v 6)
    | 2, 0 => v 5
    | 3, 0 => v 6
    | _, _ => 0
  map_add' v w := by
    ext ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    interval_cases i <;> interval_cases j <;> simp <;> ring
  map_smul' c v := by
    ext ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    interval_cases i <;> interval_cases j <;> simp <;> ring

lemma embedMap_injective : Function.Injective embedMap := by
  intro v w h
  ext ⟨k, hk⟩
  interval_cases k
  · exact congrFun h (0, 1)
  · exact congrFun h (0, 2)
  · exact congrFun h (0, 3)
  · exact congrFun h (0, 4)
  · exact congrFun h (0, 5)
  · exact congrFun h (2, 0)
  · exact congrFun h (3, 0)

lemma embedMap_zero_off (v : Fin 7 → ℂ) (i : Fin 4) (j : Fin 6) (hi : i ≠ 0) (hj : j ≠ 0) :
    embedMap v (i, j) = 0 := by
  rcases i with ⟨i, hi'⟩
  rcases j with ⟨j, hj'⟩
  have hi0 : i ≠ 0 := fun h => hi (Fin.ext h)
  have hj0 : j ≠ 0 := fun h => hj (Fin.ext h)
  interval_cases i <;> interval_cases j <;> simp_all [embedMap]

lemma embedMap_row0_sum (v : Fin 7 → ℂ) :
    ∑ j : Fin 6, embedMap v (0, j) = 0 := by
  rw [Fin.sum_univ_six]
  simp [embedMap]
  ring

lemma embedMap_col_sum (v : Fin 7 → ℂ) (j : Fin 6) :
    embedMap v (1, j) + embedMap v (2, j) + embedMap v (3, j) = 0 := by
  by_cases hj : j = 0
  · subst hj
    simp [embedMap]
  · rw [embedMap_zero_off v 1 j (by decide) hj,
        embedMap_zero_off v 2 j (by decide) hj,
        embedMap_zero_off v 3 j (by decide) hj]
    simp

def swapEmb (r : Fin 4) : (Fin 4 ↪ Fin 6) ≃ (Fin 4 ↪ Fin 6) where
  toFun f := (Equiv.swap (1 : Fin 4) r).toEmbedding.trans f
  invFun f := (Equiv.swap (1 : Fin 4) r).toEmbedding.trans f
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp

def shiftEmb (k : Fin 6) : (Fin 4 ↪ Fin 6) ≃ (Fin 4 ↪ Fin 6) where
  toFun f := f.trans (Equiv.addRight k).toEmbedding
  invFun f := f.trans (Equiv.addRight (-k)).toEmbedding
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp

lemma prod_expand (v : Fin 7 → ℂ) (f : Fin 4 ↪ Fin 6) :
    (∏ i : Fin 4, (1 + embedMap v (i, f i))) =
      1 + embedMap v (0, f 0) + embedMap v (1, f 1) + embedMap v (2, f 2) + embedMap v (3, f 3) +
      embedMap v (0, f 0) * embedMap v (1, f 1) +
      embedMap v (0, f 0) * embedMap v (2, f 2) +
      embedMap v (0, f 0) * embedMap v (3, f 3) := by
  rw [Fin.prod_univ_four]
  have hpair : ∀ {a b : Fin 4}, a ≠ 0 → b ≠ 0 → a ≠ b →
      embedMap v (a, f a) * embedMap v (b, f b) = 0 := by
    intro a b ha hb hab
    by_cases hfa : f a = 0
    · have hfb : f b ≠ 0 := by
        intro hfb
        exact hab (f.injective (hfa.trans hfb.symm))
      rw [embedMap_zero_off v b (f b) hb hfb, mul_zero]
    · rw [embedMap_zero_off v a (f a) ha hfa, zero_mul]
  have h12 : embedMap v (1, f 1) * embedMap v (2, f 2) = 0 :=
    hpair (by decide) (by decide) (by decide)
  have h13 : embedMap v (1, f 1) * embedMap v (3, f 3) = 0 :=
    hpair (by decide) (by decide) (by decide)
  have h23 : embedMap v (2, f 2) * embedMap v (3, f 3) = 0 :=
    hpair (by decide) (by decide) (by decide)
  have hrest :
      (1 + embedMap v (1, f 1)) * (1 + embedMap v (2, f 2)) * (1 + embedMap v (3, f 3)) =
        1 + embedMap v (1, f 1) + embedMap v (2, f 2) + embedMap v (3, f 3) := by
    linear_combination
      (1 + embedMap v (3, f 3)) * h12 + h13 + h23
  calc
    (1 + embedMap v (0, f 0)) * (1 + embedMap v (1, f 1)) *
        (1 + embedMap v (2, f 2)) * (1 + embedMap v (3, f 3))
      = (1 + embedMap v (0, f 0)) *
          ((1 + embedMap v (1, f 1)) * (1 + embedMap v (2, f 2)) * (1 + embedMap v (3, f 3))) := by
        ring
    _ = (1 + embedMap v (0, f 0)) *
          (1 + embedMap v (1, f 1) + embedMap v (2, f 2) + embedMap v (3, f 3)) := by
        rw [hrest]
    _ = _ := by ring

lemma sum_row0 (v : Fin 7 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0)) = 0 := by
  have h6 : (6 : ℂ) * (∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0)) = 0 := by
    have hshift : ∀ k : Fin 6,
        (∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0)) =
          ∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0 + k) := by
      intro k
      exact (Equiv.sum_comp (shiftEmb k) (fun f : Fin 4 ↪ Fin 6 => embedMap v (0, f 0))).symm
    calc
      (6 : ℂ) * (∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0))
        = ∑ _k : Fin 6, ∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0) := by
          simp
      _ = ∑ k : Fin 6, ∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0 + k) := by
          refine Finset.sum_congr rfl (fun k _ => hshift k)
      _ = ∑ f : Fin 4 ↪ Fin 6, ∑ k : Fin 6, embedMap v (0, f 0 + k) := Finset.sum_comm
      _ = ∑ f : Fin 4 ↪ Fin 6, ∑ j : Fin 6, embedMap v (0, j) := by
          refine Finset.sum_congr rfl (fun f _ => ?_)
          exact Equiv.sum_comp (Equiv.addLeft (f 0)) (fun j : Fin 6 => embedMap v (0, j))
      _ = 0 := by
          simp [embedMap_row0_sum]
  exact (mul_eq_zero.mp h6).resolve_left (by norm_num)

lemma sum_reindex_col (v : Fin 7 → ℂ) (r : Fin 4) :
    (∑ f : Fin 4 ↪ Fin 6, embedMap v (r, f r)) =
      ∑ f : Fin 4 ↪ Fin 6, embedMap v (r, f 1) := by
  have h := (Equiv.sum_comp (swapEmb r) (fun f : Fin 4 ↪ Fin 6 => embedMap v (r, f r))).symm
  simpa [swapEmb] using h

lemma sum_reindex_pair (v : Fin 7 → ℂ) (r : Fin 4) (hr : r ≠ 0) :
    (∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0) * embedMap v (r, f r)) =
      ∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0) * embedMap v (r, f 1) := by
  have h := (Equiv.sum_comp (swapEmb r)
    (fun f : Fin 4 ↪ Fin 6 => embedMap v (0, f 0) * embedMap v (r, f r))).symm
  have h0 : Equiv.swap (1 : Fin 4) r 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) hr.symm
  simpa [swapEmb, h0] using h

lemma sum_all (v : Fin 7 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i : Fin 4, (1 + embedMap v (i, f i))) = 360 := by
  simp_rw [prod_expand v]
  simp only [Finset.sum_add_distrib]
  have hconst : (∑ _f : Fin 4 ↪ Fin 6, (1 : ℂ)) = 360 := by
    simp [Fintype.card_embedding_eq, Nat.descFactorial]
  have hcol :
      (∑ f : Fin 4 ↪ Fin 6, embedMap v (1, f 1)) +
      (∑ f : Fin 4 ↪ Fin 6, embedMap v (2, f 2)) +
      (∑ f : Fin 4 ↪ Fin 6, embedMap v (3, f 3)) = 0 := by
    rw [sum_reindex_col v 2, sum_reindex_col v 3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp [embedMap_col_sum]
  have hpair :
      (∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0) * embedMap v (1, f 1)) +
      (∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0) * embedMap v (2, f 2)) +
      (∑ f : Fin 4 ↪ Fin 6, embedMap v (0, f 0) * embedMap v (3, f 3)) = 0 := by
    rw [sum_reindex_pair v 2 (by decide), sum_reindex_pair v 3 (by decide),
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hterm : ∀ f : Fin 4 ↪ Fin 6,
        embedMap v (0, f 0) * embedMap v (1, f 1) +
        embedMap v (0, f 0) * embedMap v (2, f 1) +
        embedMap v (0, f 0) * embedMap v (3, f 1) = 0 := by
      intro f
      calc
        _ = embedMap v (0, f 0) *
              (embedMap v (1, f 1) + embedMap v (2, f 1) + embedMap v (3, f 1)) := by ring
        _ = 0 := by rw [embedMap_col_sum, mul_zero]
    simp [hterm]
  linear_combination hconst + sum_row0 v + hcol + hpair

end PEqualNP.Outside.L_gct_208_aux

theorem PEqualNP.Outside.L_gct_208 :
    ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧
      Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range PEqualNP.Outside.L_gct_208_aux.embedMap, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact PEqualNP.Outside.L_gct_208_aux.sum_all v
  · rw [← (LinearEquiv.ofInjective PEqualNP.Outside.L_gct_208_aux.embedMap
      PEqualNP.Outside.L_gct_208_aux.embedMap_injective).finrank_eq]
    simp
