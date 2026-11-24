import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_194

open Finset

-- The entry added to 1 in row r and column j: the circulant in rows 0 to 3, the appended row 4.
noncomputable def T (c d : ℂ) (r : Fin 5) (j : Fin 4) : ℂ :=
  if r.val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0)
  else c * (if j.val = r.val then (1 : ℂ) else if j.val = (r.val + 1) % 4 then Complex.I
    else if j.val = (r.val + 2) % 4 then -Complex.I else -1)

-- Four values in Fin 5 as a function on Fin 4.
def quad : Fin 5 × Fin 5 × Fin 5 × Fin 5 ≃ (Fin 4 → Fin 5) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  invFun z := (z 0, z 1, z 2, z 3)
  left_inv _ := rfl
  right_inv z := by ext i; fin_cases i <;> rfl

-- A sum over injections of Fin 4 into Fin 5 as a four-fold sum over distinct values.
theorem sum_emb (G : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ) :
    ∑ e : Fin 4 ↪ Fin 5, G (e 0) (e 1) (e 2) (e 3) =
      ∑ a : Fin 5, ∑ b : Fin 5, ∑ x : Fin 5, ∑ y : Fin 5,
        if a = b ∨ a = x ∨ a = y ∨ b = x ∨ b = y ∨ x = y then 0 else G a b x y := by
  classical
  let u (z : Fin 4 → Fin 5) : ℂ := G (z 0) (z 1) (z 2) (z 3)
  have A : ∑ e : Fin 4 ↪ Fin 5, G (e 0) (e 1) (e 2) (e 3) =
      ∑ z : Fin 4 → Fin 5, if Function.Injective z then u z else 0 := by
    let E := Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 5)
    change (∑ e : Fin 4 ↪ Fin 5, u e) = _
    rw [← E.sum_comp (fun e : Fin 4 ↪ Fin 5 => u e), ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) u).symm
  rw [A, ← quad.sum_comp (fun z => if Function.Injective z then u z else 0)]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun x _ =>
    sum_congr rfl fun y _ => ?_
  let z := quad (a, b, x, y)
  have p0 : z 0 = a := rfl
  have p1 : z 1 = b := rfl
  have p2 : z 2 = x := rfl
  have p3 : z 3 = y := rfl
  have inj : Function.Injective z ↔ ¬ (a = b ∨ a = x ∨ a = y ∨ b = x ∨ b = y ∨ x = y) := by
    constructor
    · intro o
      have h (i j : Fin 4) (g : i ≠ j) : z i ≠ z j := fun h => g (o h)
      exact not_or_intro (h 0 1 (by decide)) (not_or_intro (h 0 2 (by decide))
        (not_or_intro (h 0 3 (by decide)) (not_or_intro (h 1 2 (by decide))
          (not_or_intro (h 1 3 (by decide)) (h 2 3 (by decide))))))
    · intro g i j v
      simp only [not_or] at g
      fin_cases i <;> fin_cases j <;> first | rfl | grind
  change (if Function.Injective z then u z else 0) = _
  by_cases g : a = b ∨ a = x ∨ a = y ∨ b = x ∨ b = y ∨ x = y
  · have k : ¬ Function.Injective z := fun h => inj.mp h g
    rw [ite_eq_right k, ite_eq_left g]
  · rw [ite_eq_left (inj.mpr g), ite_eq_right g]
    show G (z 0) (z 1) (z 2) (z 3) = G a b x y
    rw [p0, p1, p2, p3]

theorem main (c d : ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + T c d (f j) j)) = 120 := by
  have e : (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + T c d (f j) j)) =
      ∑ f : Fin 4 ↪ Fin 5,
        (1 + T c d (f 0) 0) * (1 + T c d (f 1) 1) * (1 + T c d (f 2) 2) * (1 + T c d (f 3) 3) := by
    refine sum_congr rfl fun f _ => ?_
    simp only [Fin.prod_univ_four]
  rw [e]
  refine (sum_emb (fun a b x y : Fin 5 =>
    (1 + T c d a 0) * (1 + T c d b 1) * (1 + T c d x 2) * (1 + T c d y 3))).trans ?_
  have t00 : T c d 0 0 = c := by simp [T]
  have t01 : T c d 0 1 = c * Complex.I := by simp [T]
  have t02 : T c d 0 2 = -(c * Complex.I) := by simp [T]
  have t03 : T c d 0 3 = -c := by simp [T]
  have t10 : T c d 1 0 = -c := by simp [T]
  have t11 : T c d 1 1 = c := by simp [T]
  have t12 : T c d 1 2 = c * Complex.I := by simp [T]
  have t13 : T c d 1 3 = -(c * Complex.I) := by simp [T]
  have t20 : T c d 2 0 = -(c * Complex.I) := by simp [T]
  have t21 : T c d 2 1 = -c := by simp [T]
  have t22 : T c d 2 2 = c := by simp [T]
  have t23 : T c d 2 3 = c * Complex.I := by simp [T]
  have t30 : T c d 3 0 = c * Complex.I := by simp [T]
  have t31 : T c d 3 1 = -(c * Complex.I) := by simp [T]
  have t32 : T c d 3 2 = -c := by simp [T]
  have t33 : T c d 3 3 = c := by simp [T]
  have t40 : T c d 4 0 = d := by simp [T]
  have t41 : T c d 4 1 = -d := by simp [T]
  have t42 : T c d 4 2 = 0 := by simp [T]
  have t43 : T c d 4 3 = 0 := by simp [T]
  simp +decide only [Fin.sum_univ_five, ite_true, ite_false, t00, t01, t02, t03, t10, t11, t12,
    t13, t20, t21, t22, t23, t30, t31, t32, t33, t40, t41, t42, t43]
  linear_combination (24 * c ^ 2 + 2 * c ^ 4 - 8 * c ^ 4 * Complex.I
    + 2 * c ^ 4 * Complex.I ^ 2) * Complex.I_sq

end PEqualNP.Outside.L_gct_194

theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 :=
  fun c d => PEqualNP.Outside.L_gct_194.main c d
