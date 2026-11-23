import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_208_aux

def tr (σ : Equiv.Perm (Fin 6)) : (Fin 4 ↪ Fin 6) ≃ (Fin 4 ↪ Fin 6) where
  toFun f := f.trans σ.toEmbedding
  invFun f := f.trans σ.symm.toEmbedding
  left_inv f := by
    ext x
    simp
  right_inv f := by
    ext x
    simp

lemma K_swap (w : (Fin 4 ↪ Fin 6) → ℂ) (r : Fin 4) (σ : Equiv.Perm (Fin 6))
    (hw : ∀ f : Fin 4 ↪ Fin 6, w (f.trans σ.toEmbedding) = w f) (j : Fin 6) :
    (∑ f : Fin 4 ↪ Fin 6, if f r = σ j then w f else 0) =
      ∑ f : Fin 4 ↪ Fin 6, if f r = j then w f else 0 := by
  rw [← Equiv.sum_comp (tr σ)]
  refine Finset.sum_congr rfl fun f _ => ?_
  show (if σ (f r) = σ j then w (f.trans σ.toEmbedding) else 0) = _
  rw [hw]
  simp only [σ.apply_eq_iff_eq]

lemma fiber (w : (Fin 4 ↪ Fin 6) → ℂ) (r : Fin 4) (a : Fin 6 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, w f * a (f r)) =
      ∑ j : Fin 6, a j * ∑ f : Fin 4 ↪ Fin 6, if f r = j then w f else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [mul_comm]

lemma card_E : (∑ _f : Fin 4 ↪ Fin 6, (1 : ℂ)) = 360 := by
  simp [Fintype.card_embedding_eq, Nat.descFactorial]

lemma row_sum (r : Fin 4) (a : Fin 6 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, a (f r)) = 60 * ∑ j : Fin 6, a j := by
  have hN : ∀ j : Fin 6, (∑ f : Fin 4 ↪ Fin 6, if f r = j then (1 : ℂ) else 0) =
      ∑ f : Fin 4 ↪ Fin 6, if f r = 0 then (1 : ℂ) else 0 := by
    intro j
    have := K_swap (fun _ => (1 : ℂ)) r (Equiv.swap 0 j) (fun _ => rfl) 0
    rw [Equiv.swap_apply_left] at this
    exact this
  have htot : (∑ j : Fin 6, ∑ f : Fin 4 ↪ Fin 6, if f r = j then (1 : ℂ) else 0) = 360 := by
    rw [Finset.sum_comm, ← card_E]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp
  have h60 : (∑ f : Fin 4 ↪ Fin 6, if f r = 0 then (1 : ℂ) else 0) = 60 := by
    rw [Finset.sum_congr rfl (fun j _ => hN j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at htot
    push_cast at htot
    linear_combination htot / 6
  have h := fiber (fun _ => 1) r a
  simp only [one_mul] at h
  rw [h, Finset.sum_congr rfl (fun j _ => by rw [hN j, h60]), ← Finset.sum_mul]
  ring

lemma cross (i : Fin 4) (hi : i ≠ 0) (a : Fin 6 → ℂ) (ha : a 1 + a 2 + a 3 + a 4 + a 5 = 0) :
    (∑ f : Fin 4 ↪ Fin 6, if f i = 0 then a (f 0) else 0) = 0 := by
  have h1 : (∑ f : Fin 4 ↪ Fin 6, if f i = 0 then a (f 0) else 0) =
      ∑ f : Fin 4 ↪ Fin 6, (if f i = 0 then (1 : ℂ) else 0) * a (f 0) := by
    refine Finset.sum_congr rfl fun f _ => ?_
    simp
  rw [h1, fiber (fun f => if f i = 0 then (1 : ℂ) else 0) 0 a]
  have hM0 : (∑ f : Fin 4 ↪ Fin 6, if f 0 = 0 then (if f i = 0 then (1 : ℂ) else 0) else 0) = 0 := by
    refine Finset.sum_eq_zero fun f _ => ?_
    by_cases h0 : f 0 = (0 : Fin 6)
    · have : f i ≠ 0 := fun h => hi (f.injective (h.trans h0.symm))
      simp [this]
    · simp [h0]
  have hM : ∀ j : Fin 6, j ≠ 0 →
      (∑ f : Fin 4 ↪ Fin 6, if f 0 = j then (if f i = 0 then (1 : ℂ) else 0) else 0) =
        ∑ f : Fin 4 ↪ Fin 6, if f 0 = 1 then (if f i = 0 then (1 : ℂ) else 0) else 0 := by
    intro j hj
    have hfix : (Equiv.swap 1 j) 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) hj.symm
    have hw : ∀ f : Fin 4 ↪ Fin 6,
        (fun f : Fin 4 ↪ Fin 6 => if f i = 0 then (1 : ℂ) else 0)
          (f.trans (Equiv.swap 1 j).toEmbedding) =
        (fun f : Fin 4 ↪ Fin 6 => if f i = 0 then (1 : ℂ) else 0) f := by
      intro f
      have hiff : (Equiv.swap 1 j) (f i) = 0 ↔ f i = 0 := by
        constructor
        · intro h
          have h' := congrArg (Equiv.swap 1 j) h
          rw [Equiv.swap_apply_self, hfix] at h'
          exact h'
        · intro h
          rw [h, hfix]
      show (if (Equiv.swap 1 j) (f i) = 0 then (1 : ℂ) else 0) = if f i = 0 then (1 : ℂ) else 0
      simp only [hiff]
    have := K_swap (fun f : Fin 4 ↪ Fin 6 => if f i = 0 then (1 : ℂ) else 0) 0
      (Equiv.swap 1 j) hw 1
    rw [Equiv.swap_apply_left] at this
    exact this
  rw [Fin.sum_univ_six, hM0, hM 2 (by decide), hM 3 (by decide), hM 4 (by decide),
    hM 5 (by decide)]
  linear_combination
    (∑ f : Fin 4 ↪ Fin 6, if f 0 = 1 then (if f i = 0 then (1 : ℂ) else 0) else 0) * ha

lemma prod_eq (t : Fin 4 × Fin 6 → ℂ) (h0 : ∀ i j, i ≠ 0 → j ≠ 0 → t (i, j) = 0)
    (f : Fin 4 ↪ Fin 6) :
    ∏ i, (1 + t (i, f i)) = 1 + t (0, f 0) + (if f 1 = 0 then t (1, 0) else 0)
      + (if f 2 = 0 then t (2, 0) else 0) + (if f 3 = 0 then t (3, 0) else 0)
      + t (1, 0) * (if f 1 = 0 then t (0, f 0) else 0)
      + t (2, 0) * (if f 2 = 0 then t (0, f 0) else 0)
      + t (3, 0) * (if f 3 = 0 then t (0, f 0) else 0) := by
  have e : ∀ i : Fin 4, i ≠ 0 → t (i, f i) = if f i = 0 then t (i, 0) else 0 := by
    intro i hi
    by_cases h : f i = 0
    · simp [h]
    · simp [h, h0 i (f i) hi h]
  rw [Fin.prod_univ_four, e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  have n12 : f 1 = 0 → f 2 = 0 → False := fun a b =>
    absurd (f.injective (a.trans b.symm)) (by decide)
  have n13 : f 1 = 0 → f 3 = 0 → False := fun a b =>
    absurd (f.injective (a.trans b.symm)) (by decide)
  have n23 : f 2 = 0 → f 3 = 0 → False := fun a b =>
    absurd (f.injective (a.trans b.symm)) (by decide)
  by_cases h1 : f 1 = 0
  · have h2 : ¬ f 2 = 0 := fun h => n12 h1 h
    have h3 : ¬ f 3 = 0 := fun h => n13 h1 h
    simp only [h1, h2, h3, ite_true, ite_false]
    ring
  · by_cases h2 : f 2 = 0
    · have h3 : ¬ f 3 = 0 := fun h => n23 h2 h
      simp only [h1, h2, h3, ite_true, ite_false]
      ring
    · by_cases h3 : f 3 = 0
      · simp only [h1, h2, h3, ite_true, ite_false]
        ring
      · simp only [h1, h2, h3, ite_false]
        ring

lemma main_id (t : Fin 4 × Fin 6 → ℂ) (h0 : ∀ i j, i ≠ 0 → j ≠ 0 → t (i, j) = 0)
    (h2 : t (0, 1) + t (0, 2) + t (0, 3) + t (0, 4) + t (0, 5) = 0)
    (h3 : t (0, 0) + t (1, 0) + t (2, 0) + t (3, 0) = 0) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360 := by
  rw [Finset.sum_congr rfl (fun f _ => prod_eq t h0 f)]
  have r0 : (∑ f : Fin 4 ↪ Fin 6, t (0, f 0)) = 60 * ∑ j : Fin 6, t (0, j) :=
    row_sum 0 (fun j => t (0, j))
  have re : ∀ i : Fin 4, (∑ f : Fin 4 ↪ Fin 6, if f i = 0 then t (i, 0) else 0) = 60 * t (i, 0) :=
    fun i => (row_sum i (fun j => if j = 0 then t (i, 0) else 0)).trans (by simp)
  have rc : ∀ i : Fin 4, i ≠ 0 →
      (∑ f : Fin 4 ↪ Fin 6, if f i = 0 then t (0, f 0) else 0) = 0 :=
    fun i hi => cross i hi (fun j => t (0, j)) h2
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [card_E, r0, re 1, re 2, re 3, rc 1 (by decide), rc 2 (by decide), rc 3 (by decide),
    Fin.sum_univ_six]
  linear_combination 60 * h2 + 60 * h3

def phiFun (c : Fin 7 → ℂ) (p : Fin 4 × Fin 6) : ℂ :=
  if p.1 = 0 then
    (if p.2 = 0 then -(c 4 + c 5 + c 6) else if p.2 = 1 then c 0 else if p.2 = 2 then c 1
      else if p.2 = 3 then c 2 else if p.2 = 4 then c 3 else -(c 0 + c 1 + c 2 + c 3))
  else if p.2 = 0 then (if p.1 = 1 then c 4 else if p.1 = 2 then c 5 else c 6)
  else 0

noncomputable def phi : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := phiFun
  map_add' c d := by
    ext p
    simp only [phiFun, Pi.add_apply]
    split_ifs <;> ring
  map_smul' r c := by
    ext p
    simp only [phiFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

lemma phi_inj : Function.Injective phi := by
  intro c d h
  have e : ∀ p, phiFun c p = phiFun d p := fun p => congrFun h p
  funext k
  fin_cases k
  · have := e (0, 1)
    simpa [phiFun] using this
  · have := e (0, 2)
    simpa [phiFun] using this
  · have := e (0, 3)
    simpa [phiFun] using this
  · have := e (0, 4)
    simpa [phiFun] using this
  · have := e (1, 0)
    simpa [phiFun] using this
  · have := e (2, 0)
    simpa [phiFun] using this
  · have := e (3, 0)
    simpa [phiFun] using this

end PEqualNP.Outside.L_gct_208_aux

open PEqualNP.Outside.L_gct_208_aux in
theorem PEqualNP.Outside.L_gct_208 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range phi, ?_, ?_⟩
  · rintro t ⟨c, rfl⟩
    refine main_id (phiFun c) ?_ ?_ ?_
    · intro i j hi hj
      simp [phiFun, hi, hj]
    · simp [phiFun]
    · simp [phiFun]
      ring
  · rw [LinearMap.finrank_range_of_inj phi_inj]
    simp
