import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_208_aux

open Finset

private def entries (x : Fin 7 → ℂ) (p : Fin 4 × Fin 6) : ℂ :=
  ![![x 0, x 1, x 2, x 3, x 4, -(x 1 + x 2 + x 3 + x 4)],
    ![x 5, 0, 0, 0, 0, 0],
    ![x 6, 0, 0, 0, 0, 0],
    ![-(x 0 + x 5 + x 6), 0, 0, 0, 0, 0]] p.1 p.2

private def family : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := entries
  map_add' x y := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entries] <;> ring
  map_smul' c x := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entries] <;> ring

private theorem family_injective : Function.Injective family := by
  intro x y h
  let positions : Fin 7 → Fin 4 × Fin 6 :=
    ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (2, 0)]
  funext k
  have hk := congrFun h (positions k)
  fin_cases k <;> exact hk

private abbrev distinct4 (p : Fin 6 × Fin 6 × Fin 6 × Fin 6) : Prop :=
  p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧
    p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2

private def embEquiv :
    (Fin 4 ↪ Fin 6) ≃ { p : Fin 6 × Fin 6 × Fin 6 × Fin 6 // distinct4 p } where
  toFun f :=
    ⟨(f 0, f 1, f 2, f 3),
      ⟨f.injective.ne (by decide), f.injective.ne (by decide), f.injective.ne (by decide),
       f.injective.ne (by decide), f.injective.ne (by decide), f.injective.ne (by decide)⟩⟩
  invFun p :=
    ⟨![p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2], by
      rcases p with ⟨⟨a, b, c, d⟩, h1, h2, h3, h4, h5, h6⟩
      dsimp at h1 h2 h3 h4 h5 h6
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
      · exact (h1 hij).elim
      · exact (h2 hij).elim
      · exact (h3 hij).elim
      · exact (h1 hij.symm).elim
      · exact (h4 hij).elim
      · exact (h5 hij).elim
      · exact (h2 hij.symm).elim
      · exact (h4 hij.symm).elim
      · exact (h6 hij).elim
      · exact (h3 hij.symm).elim
      · exact (h5 hij.symm).elim
      · exact (h6 hij.symm).elim⟩
  left_inv f := by
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨a, b, c, d⟩, h⟩
    rfl

private theorem sum_emb (F : Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, F (f 0) (f 1) (f 2) (f 3)) =
      ∑ j0 : Fin 6, ∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
        if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
          F j0 j1 j2 j3
        else 0 := by
  rw [Fintype.sum_equiv embEquiv (fun f => F (f 0) (f 1) (f 2) (f 3))
    (fun p => F p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2) (fun _ => rfl)]
  have hsub : (∑ p : { p : Fin 6 × Fin 6 × Fin 6 × Fin 6 // distinct4 p },
      F p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2) =
      ∑ p : Fin 6 × Fin 6 × Fin 6 × Fin 6,
        if distinct4 p then F p.1 p.2.1 p.2.2.1 p.2.2.2 else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter distinct4) (fun _ => by simp)
      (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2)).symm
  rw [hsub]
  simp only [Fintype.sum_prod_type, distinct4]

private theorem unused (S : Finset (Fin 6)) (z : ℂ) :
    (∑ i : Fin 6, if i ∈ S then 0 else z) = ((6 - S.card : ℕ) : ℂ) * z := by
  classical
  have h : Sᶜ = univ.filter (fun i => i ∉ S) := by ext; simp
  calc
    _ = ∑ i ∈ Sᶜ, z := by rw [h, sum_filter]; simp
    _ = _ := by simp [Finset.card_compl]

private theorem count_2 (a b : Fin 6) (hab : a ≠ b) (z : ℂ) :
    (∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if a ≠ j2 ∧ a ≠ j3 ∧ b ≠ j2 ∧ b ≠ j3 ∧ j2 ≠ j3 then z else 0) = 12 * z := by
  classical
  have h3 (j2 : Fin 6) (ha : a ≠ j2) (hb : b ≠ j2) :
      (∑ j3 : Fin 6, if a ≠ j2 ∧ a ≠ j3 ∧ b ≠ j2 ∧ b ≠ j3 ∧ j2 ≠ j3 then z else 0) = 3 * z := by
    have hcard : ({a, b, j2} : Finset (Fin 6)).card = 3 := by
      simp [card_insert_of_notMem, hab, ha, hb]
    have hrew : (∑ j3 : Fin 6, if a ≠ j2 ∧ a ≠ j3 ∧ b ≠ j2 ∧ b ≠ j3 ∧ j2 ≠ j3 then z else 0) =
        ∑ j3 : Fin 6, if j3 ∈ ({a, b, j2} : Finset (Fin 6)) then 0 else z := by
      refine sum_congr rfl fun j3 _ => ?_
      by_cases hj : j3 ∈ ({a, b, j2} : Finset (Fin 6))
      · simp only [hj, ↓reduceIte]
        simp only [mem_insert, mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> simp
      · simp only [hj, ↓reduceIte]
        simp only [mem_insert, mem_singleton, not_or] at hj
        simp [ha, hb, Ne.symm hj.1, Ne.symm hj.2.1, Ne.symm hj.2.2]
    rw [hrew, unused, hcard]
    norm_num
  have h2 : (∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if a ≠ j2 ∧ a ≠ j3 ∧ b ≠ j2 ∧ b ≠ j3 ∧ j2 ≠ j3 then z else 0) =
      ∑ j2 : Fin 6, if j2 ∈ ({a, b} : Finset (Fin 6)) then 0 else 3 * z := by
    refine sum_congr rfl fun j2 _ => ?_
    by_cases hj : j2 ∈ ({a, b} : Finset (Fin 6))
    · simp only [hj, ↓reduceIte]
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp
    · simp only [hj, ↓reduceIte]
      simp only [mem_insert, mem_singleton, not_or] at hj
      exact h3 j2 (Ne.symm hj.1) (Ne.symm hj.2)
  have hcard2 : ({a, b} : Finset (Fin 6)).card = 2 := by
    simp [card_insert_of_notMem, hab]
  rw [h2, unused, hcard2]
  norm_num
  ring

private theorem count_all (j0 : Fin 6) :
    (∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then (1 : ℂ) else 0) = 60 := by
  classical
  have h1 : (∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then (1 : ℂ) else 0) =
      ∑ j1 : Fin 6, if j1 ∈ ({j0} : Finset (Fin 6)) then 0 else (12 : ℂ) := by
    refine sum_congr rfl fun j1 _ => ?_
    by_cases hj : j1 = j0
    · subst hj
      simp
    · simp only [mem_singleton, hj, ↓reduceIte]
      have hne : j0 ≠ j1 := Ne.symm hj
      have := count_2 j0 j1 hne 1
      simpa [hne] using this
  rw [h1, unused]
  norm_num

private theorem count_first (j0 : Fin 6) (z : ℂ) :
    (∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (if j1 = 0 then z else 0)
      else 0) = if j0 = 0 then 0 else 12 * z := by
  classical
  have hsplit : (∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (if j1 = 0 then z else 0)
      else 0) =
      ∑ j1 : Fin 6, if j1 = 0 then
        (∑ j2 : Fin 6, ∑ j3 : Fin 6,
          if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then z else 0)
      else 0 := by
    refine sum_congr rfl fun j1 _ => ?_
    by_cases h1 : j1 = 0 <;> simp [h1]
  rw [hsplit, sum_ite_eq']
  simp only [mem_univ, ↓reduceIte]
  by_cases h0 : j0 = 0
  · subst h0
    simp
  · simp only [h0, ↓reduceIte]
    have := count_2 j0 0 h0 z
    simpa [h0] using this

private theorem count_second (j0 : Fin 6) (z : ℂ) :
    (∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (if j2 = 0 then z else 0)
      else 0) = if j0 = 0 then 0 else 12 * z := by
  rw [Finset.sum_comm]
  have hrew : (∑ j2 : Fin 6, ∑ j1 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (if j2 = 0 then z else 0)
      else 0) =
      ∑ j2 : Fin 6, ∑ j1 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j2 ∧ j0 ≠ j1 ∧ j0 ≠ j3 ∧ j2 ≠ j1 ∧ j2 ≠ j3 ∧ j1 ≠ j3 then
        (if j2 = 0 then z else 0)
      else 0 := by
    refine sum_congr rfl fun j2 _ => sum_congr rfl fun j1 _ => sum_congr rfl fun j3 _ => ?_
    have hiff : (j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3) ↔
        (j0 ≠ j2 ∧ j0 ≠ j1 ∧ j0 ≠ j3 ∧ j2 ≠ j1 ∧ j2 ≠ j3 ∧ j1 ≠ j3) := by
      simp only [ne_comm (a := j1) (b := j2)]
      tauto
    simp only [hiff]
  rw [hrew]
  exact count_first j0 z

private theorem count_third (j0 : Fin 6) (z : ℂ) :
    (∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (if j3 = 0 then z else 0)
      else 0) = if j0 = 0 then 0 else 12 * z := by
  have hswap1 : (∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (if j3 = 0 then z else 0)
      else 0) =
      ∑ j1 : Fin 6, ∑ j3 : Fin 6, ∑ j2 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j3 ∧ j0 ≠ j2 ∧ j1 ≠ j3 ∧ j1 ≠ j2 ∧ j3 ≠ j2 then
        (if j3 = 0 then z else 0)
      else 0 := by
    refine sum_congr rfl fun j1 _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun j3 _ => sum_congr rfl fun j2 _ => ?_
    have hiff : (j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3) ↔
        (j0 ≠ j1 ∧ j0 ≠ j3 ∧ j0 ≠ j2 ∧ j1 ≠ j3 ∧ j1 ≠ j2 ∧ j3 ≠ j2) := by
      simp only [ne_comm (a := j2) (b := j3)]
      tauto
    simp only [hiff]
  rw [hswap1]
  exact count_second j0 z

private theorem inner_sum (j0 : Fin 6) (u1 u2 u3 : ℂ) :
    (∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (1 + if j1 = 0 then u1 else 0) *
          (1 + if j2 = 0 then u2 else 0) *
          (1 + if j3 = 0 then u3 else 0)
      else 0) = 60 + if j0 = 0 then 0 else 12 * (u1 + u2 + u3) := by
  have hprod (j1 j2 j3 : Fin 6) :
      (if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (1 + if j1 = 0 then u1 else 0) *
          (1 + if j2 = 0 then u2 else 0) *
          (1 + if j3 = 0 then u3 else 0)
      else 0) =
      (if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then (1 : ℂ) else 0) +
      (if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (if j1 = 0 then u1 else 0) else 0) +
      (if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (if j2 = 0 then u2 else 0) else 0) +
      (if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (if j3 = 0 then u3 else 0) else 0) := by
    by_cases h : j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, ite_eq_left h, ite_eq_left h]
      rcases h with ⟨_, _, _, h12, h13, h23⟩
      by_cases h1 : j1 = 0
      · have h2 : j2 ≠ 0 := by intro e; exact h12 (h1.trans e.symm)
        have h3 : j3 ≠ 0 := by intro e; exact h13 (h1.trans e.symm)
        simp [h1, h2, h3]
      · by_cases h2 : j2 = 0
        · have h3 : j3 ≠ 0 := by intro e; exact h23 (h2.trans e.symm)
          simp [h1, h2, h3]
        · by_cases h3 : j3 = 0 <;> simp [h1, h2, h3]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ite_eq_right h, ite_eq_right h]
      ring
  simp_rw [hprod, sum_add_distrib]
  rw [count_all j0, count_first j0 u1, count_second j0 u2, count_third j0 u3]
  by_cases h0 : j0 = 0
  · simp [h0]
  · simp [h0]
    ring

private theorem entry_row1 (x : Fin 7 → ℂ) (j : Fin 6) :
    entries x (1, j) = if j = 0 then x 5 else 0 := by
  fin_cases j <;> simp [entries]

private theorem entry_row2 (x : Fin 7 → ℂ) (j : Fin 6) :
    entries x (2, j) = if j = 0 then x 6 else 0 := by
  fin_cases j <;> simp [entries]

private theorem entry_row3 (x : Fin 7 → ℂ) (j : Fin 6) :
    entries x (3, j) = if j = 0 then -(x 0 + x 5 + x 6) else 0 := by
  fin_cases j <;> simp [entries]

private theorem main_identity (x : Fin 7 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i : Fin 4, (1 + entries x (i, f i))) = 360 := by
  have hprod : (∑ f : Fin 4 ↪ Fin 6, ∏ i : Fin 4, (1 + entries x (i, f i))) =
      ∑ f : Fin 4 ↪ Fin 6,
        (1 + entries x (0, f 0)) * (1 + entries x (1, f 1)) *
          (1 + entries x (2, f 2)) * (1 + entries x (3, f 3)) := by
    refine sum_congr rfl fun f _ => ?_
    simp [Fin.prod_univ_four, mul_assoc]
  rw [hprod, sum_emb (fun j0 j1 j2 j3 =>
    (1 + entries x (0, j0)) * (1 + entries x (1, j1)) *
      (1 + entries x (2, j2)) * (1 + entries x (3, j3)))]
  have hpull : (∑ j0 : Fin 6, ∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
      if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
        (1 + entries x (0, j0)) * (1 + entries x (1, j1)) *
          (1 + entries x (2, j2)) * (1 + entries x (3, j3))
      else 0) =
      ∑ j0 : Fin 6, (1 + entries x (0, j0)) *
        (∑ j1 : Fin 6, ∑ j2 : Fin 6, ∑ j3 : Fin 6,
          if j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3 then
            (1 + if j1 = 0 then x 5 else 0) *
              (1 + if j2 = 0 then x 6 else 0) *
              (1 + if j3 = 0 then -(x 0 + x 5 + x 6) else 0)
          else 0) := by
    refine sum_congr rfl fun j0 _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j1 _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j2 _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun j3 _ => ?_
    by_cases h : j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j1 ≠ j2 ∧ j1 ≠ j3 ∧ j2 ≠ j3
    · rw [ite_eq_left h, ite_eq_left h, entry_row1, entry_row2, entry_row3]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [hpull]
  simp_rw [inner_sum]
  simp [Fin.sum_univ_six, entries]
  ring

end PEqualNP.Outside.L_gct_208_aux

theorem PEqualNP.Outside.L_gct_208 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range PEqualNP.Outside.L_gct_208_aux.family, ?_, ?_⟩
  · rintro t ⟨x, rfl⟩
    exact PEqualNP.Outside.L_gct_208_aux.main_identity x
  · rw [LinearMap.finrank_range_of_inj PEqualNP.Outside.L_gct_208_aux.family_injective,
      Module.finrank_fin_fun]
