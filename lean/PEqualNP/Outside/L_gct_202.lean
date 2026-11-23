import Mathlib
import PEqualNP.Defs

/-! Separate terms involving the constant row. Summing its unused column index
  contributes q-k choices when the other k columns are distinct. -/

namespace L202count

private theorem avoid {q : ℕ} (s : Finset (Fin q)) (z : ℂ) :
    (∑ j : Fin q, if j ∈ s then 0 else z) = ((q - s.card : ℕ) : ℂ) * z := by
  classical
  calc
    _ = ∑ j : Fin q, if j ∈ sᶜ then z else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ s <;> simp [hj]
    _ = ∑ _j ∈ sᶜ, z := by
      rw [← Finset.sum_filter]
      have hset : Finset.univ.filter (fun j : Fin q => j ∈ sᶜ) = sᶜ := by ext j; simp
      rw [hset]
    _ = _ := by simp [Finset.card_compl, nsmul_eq_mul]

private theorem free₂ {q : ℕ} (x : Fin q) (z : ℂ) :
    (∑ j, if j = x then 0 else z) = ((q - 1 : ℕ) : ℂ) * z := by
  simpa using avoid {x} z

private theorem free₃ {q : ℕ} (x y : Fin q) (z : ℂ) :
    (∑ j, if j = x ∨ j = y ∨ x = y then 0 else z) =
      ((q - 2 : ℕ) : ℂ) * (if x = y then 0 else z) := by
  by_cases h : x = y
  · subst y; simp
  · simpa [h] using avoid {x,y} z

private theorem free₄ {q : ℕ} (x y w : Fin q) (z : ℂ) :
    (∑ j, if j = x ∨ j = y ∨ j = w ∨ x = y ∨ x = w ∨ y = w then 0 else z) =
      ((q - 3 : ℕ) : ℂ) * (if x = y ∨ x = w ∨ y = w then 0 else z) := by
  by_cases hxy : x = y
  · simp [hxy]
  by_cases hxw : x = w
  · simp [hxw]
  by_cases hyw : y = w
  · simp [hyw]
  simpa [hxy,hxw,hyw] using avoid {x,y,w} z

private theorem sum₂ {q : ℕ} (F : Fin q → ℂ) :
    (∑ j, ∑ l, if j = l then 0 else F l) = ((q - 1 : ℕ) : ℂ) * ∑ l, F l := by
  rw [Finset.sum_comm]
  simp_rw [free₂]
  rw [Finset.mul_sum]

private theorem sum₃ {q : ℕ} (F : Fin q → Fin q → ℂ) :
    (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else F l m) =
      ((q - 2 : ℕ) : ℂ) * ∑ l, ∑ m, if l = m then 0 else F l m := by
  calc
    _ = ∑ l, ∑ m, ∑ j, if j = l ∨ j = m ∨ l = m then 0 else F l m := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by simp_rw [free₃]; simp_rw [Finset.mul_sum]

private theorem sum₄ {q : ℕ} (F : Fin q → Fin q → Fin q → ℂ) :
    (∑ j, ∑ l, ∑ m, ∑ n,
        if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else F l m n) =
      ((q - 3 : ℕ) : ℂ) * ∑ l, ∑ m, ∑ n, if l = m ∨ l = n ∨ m = n then 0 else F l m n := by
  calc
    _ = ∑ l, ∑ m, ∑ n, ∑ j,
        if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else F l m n := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by simp_rw [free₄]; simp_rw [Finset.mul_sum]

end L202count


namespace L202

open Finset

private def one {q : ℕ} (f : Fin q → ℂ) : ℂ := ∑ j, f j

private def two {q : ℕ} (f : Fin q → Fin q → ℂ) : ℂ :=
  ∑ j, ∑ l, if j = l then 0 else f j l

private def three {q : ℕ} (f : Fin q → Fin q → Fin q → ℂ) : ℂ :=
  ∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else f j l m

private def four {q : ℕ} (f : Fin q → Fin q → Fin q → Fin q → ℂ) : ℂ :=
  ∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n
    then 0 else f j l m n

private theorem mask (p : Prop) [Decidable p] (c a b : ℂ) :
    (if p then 0 else c * a + b) =
      c * (if p then 0 else a) + (if p then 0 else b) := by
  by_cases h : p <;> simp [h]

private theorem maskMul (p : Prop) [Decidable p] (c a : ℂ) :
    (if p then 0 else c * a) = c * (if p then 0 else a) := by
  by_cases h : p <;> simp [h]

private theorem lin₂ {q : ℕ} (c : ℂ) (f g : Fin q → Fin q → ℂ) :
    two (fun j l => c * f j l + g j l) = c * two f + two g := by
  simp only [two, mask, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem lin₃ {q : ℕ} (c : ℂ) (f g : Fin q → Fin q → Fin q → ℂ) :
    three (fun j l m => c * f j l m + g j l m) = c * three f + three g := by
  simp only [three, mask, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem lin₄ {q : ℕ} (c : ℂ) (f : Fin q → Fin q → Fin q → Fin q → ℂ) :
    four (fun j l m n => c * f j l m n) = c * four f := by
  simp only [four, maskMul, ← Finset.mul_sum]

end L202

open L202 in
theorem PEqualNP.Outside.L_gct_202 : ∀ (q : ℕ) (t : Fin 4 × Fin q → ℂ) (c : ℂ), 4 ≤ q → (∀ j, t (0, j) = c) → (∑ i : Fin 4, ∑ j, t (i, j)) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0 → c = 0 := by
  classical
  intro q t c hq hrow
  rintro ⟨h1, h2, h3, h4⟩
  let A := fun j : Fin q => t (1, j) + t (2, j) + t (3, j)
  let B := fun j l : Fin q =>
    t (1, j) * t (2, l) + t (1, j) * t (3, l) + t (2, j) * t (3, l)
  let D := fun j l m : Fin q => t (1, j) * t (2, l) * t (3, m)
  have e1 : (q : ℂ) * c + one A = 0 := by
    simpa only [Fin.sum_univ_four, hrow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, one, A, Finset.sum_add_distrib, add_assoc] using h1
  have pair (j l : Fin q) :
      (∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) =
        c * A l + B j l := by
    norm_num [Fin.sum_univ_four, hrow, A, B]
    ring
  have triple (j l m : Fin q) :
      (∑ a : Fin 4, ∑ b : Fin 4, ∑ k : Fin 4,
        if a < b ∧ b < k then t (a, j) * t (b, l) * t (k, m) else 0) =
          c * B l m + D j l m := by
    norm_num [Fin.sum_univ_four, hrow, B, D]
    ring
  simp_rw [pair] at h2
  simp_rw [triple] at h3
  have e2 : c * two (fun _ l => A l) + two B = 0 := by
    rw [← lin₂]
    exact h2
  have e3 : c * three (fun _ l m => B l m) + three D = 0 := by
    rw [← lin₃]
    exact h3
  have e4 : c * four (fun _ l m n => D l m n) = 0 := by
    rw [← lin₄]
    simpa only [four, hrow, D, mul_assoc] using h4
  have drop₂ : two (fun _ l => A l) = ((q - 1 : ℕ) : ℂ) * one A :=
    L202count.sum₂ A
  have drop₃ : three (fun _ l m => B l m) = ((q - 2 : ℕ) : ℂ) * two B :=
    L202count.sum₃ B
  have drop₄ : four (fun _ l m n => D l m n) = ((q - 3 : ℕ) : ℂ) * three D :=
    L202count.sum₄ D
  rw [drop₂] at e2
  rw [drop₃] at e3
  rw [drop₄] at e4
  by_contra hn
  have nz (k : ℕ) (hk : k < q) : ((q - k : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show q - k ≠ 0 by omega)
  have d := (mul_eq_zero.mp ((mul_eq_zero.mp e4).resolve_left hn)).resolve_left (nz 3 (by omega))
  rw [d, add_zero] at e3
  have b := (mul_eq_zero.mp ((mul_eq_zero.mp e3).resolve_left hn)).resolve_left (nz 2 (by omega))
  rw [b, add_zero] at e2
  have a := (mul_eq_zero.mp ((mul_eq_zero.mp e2).resolve_left hn)).resolve_left (nz 1 (by omega))
  rw [a, add_zero] at e1
  exact hn ((mul_eq_zero.mp e1).resolve_left (by exact_mod_cast (show q ≠ 0 by omega)))
