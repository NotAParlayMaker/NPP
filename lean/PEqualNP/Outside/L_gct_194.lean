import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_194

open Finset

/-- Four values in `Fin 5` as a function on `Fin 4`. -/
def tup (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) : Fin 4 → Fin 5 :=
  ![p.1, p.2.1, p.2.2.1, p.2.2.2]

def tupEquiv : Fin 5 × Fin 5 × Fin 5 × Fin 5 ≃ (Fin 4 → Fin 5) where
  toFun := tup
  invFun z := (z 0, z 1, z 2, z 3)
  left_inv _ := rfl
  right_inv z := by ext i; fin_cases i <;> rfl

theorem injective_tup_iff (a b c d : Fin 5) :
    Function.Injective (tup (a, b, c, d)) ↔
      ¬(a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) := by
  constructor
  · intro o
    have h (i j : Fin 4) (g : i ≠ j) : tup (a, b, c, d) i ≠ tup (a, b, c, d) j :=
      fun h => g (o h)
    exact not_or_intro (h 0 1 (by decide)) (not_or_intro (h 0 2 (by decide))
      (not_or_intro (h 0 3 (by decide)) (not_or_intro (h 1 2 (by decide))
        (not_or_intro (h 1 3 (by decide)) (h 2 3 (by decide))))))
  · intro g i j v
    simp only [not_or] at g
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := g
    fin_cases i <;> fin_cases j <;> simp [tup] at v ⊢ <;>
      first | exact absurd v (by assumption) | exact absurd v.symm (by assumption)

/-- A sum over the injections `Fin 4 ↪ Fin 5` as four nested sums. -/
theorem sum_emb (M : Fin 4 → Fin 5 → ℂ) :
    (∑ e : Fin 4 ↪ Fin 5, ∏ r, M r (e r)) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        if a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d then 0 else
          M 0 a * M 1 b * M 2 c * M 3 d := by
  classical
  let u (z : Fin 4 → Fin 5) : ℂ := ∏ r, M r (z r)
  have A : (∑ e : Fin 4 ↪ Fin 5, ∏ r, M r (e r)) =
      ∑ z : Fin 4 → Fin 5, if Function.Injective z then u z else 0 := by
    let E := Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 5)
    change (∑ e : Fin 4 ↪ Fin 5, u e) = _
    rw [← E.sum_comp (fun e : Fin 4 ↪ Fin 5 => u e), ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) u).symm
  rw [A, ← tupEquiv.sum_comp (fun z => if Function.Injective z then u z else 0)]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => ?_
  change (if Function.Injective (tup (a, b, c, d)) then u (tup (a, b, c, d)) else 0) = _
  by_cases g : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d
  · have k : ¬Function.Injective (tup (a, b, c, d)) := fun h => (injective_tup_iff a b c d).mp h g
    rw [if_neg k, if_pos g]
  · rw [if_pos ((injective_tup_iff a b c d).mpr g), if_neg g]
    simp [u, Fin.prod_univ_four, tup, mul_assoc]

/-- The entry for row `r` of the transposed matrix (column `r` of the statement) at `k`. -/
def ent (c d : ℂ) (r : Fin 4) (k : Fin 5) : ℂ :=
  1 + (if k.val = 4 then d * (if r.val = 0 then (1 : ℂ) else if r.val = 1 then -1 else 0)
    else c * (if r.val = k.val then (1 : ℂ) else if r.val = (k.val + 1) % 4 then Complex.I
      else if r.val = (k.val + 2) % 4 then -Complex.I else -1))

end PEqualNP.Outside.L_gct_194

set_option maxHeartbeats 4000000 in
open PEqualNP.Outside.L_gct_194 in
theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  refine Eq.trans (sum_emb (ent c d)) ?_
  simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, or_false, false_or, or_true, true_or,
    or_self, ↓reduceIte, zero_add, add_zero]
  have e00 : ent c d 0 0 = 1 + c := by norm_num [ent]
  have e01 : ent c d 0 1 = 1 + c * -1 := by norm_num [ent]
  have e02 : ent c d 0 2 = 1 + c * -Complex.I := by norm_num [ent]
  have e03 : ent c d 0 3 = 1 + c * Complex.I := by norm_num [ent]
  have e04 : ent c d 0 4 = 1 + d := by norm_num [ent]
  have e10 : ent c d 1 0 = 1 + c * Complex.I := by norm_num [ent]
  have e11 : ent c d 1 1 = 1 + c := by norm_num [ent]
  have e12 : ent c d 1 2 = 1 + c * -1 := by norm_num [ent]
  have e13 : ent c d 1 3 = 1 + c * -Complex.I := by norm_num [ent]
  have e14 : ent c d 1 4 = 1 + -d := by norm_num [ent]
  have e20 : ent c d 2 0 = 1 + c * -Complex.I := by norm_num [ent]
  have e21 : ent c d 2 1 = 1 + c * Complex.I := by norm_num [ent]
  have e22 : ent c d 2 2 = 1 + c := by norm_num [ent]
  have e23 : ent c d 2 3 = 1 + c * -1 := by norm_num [ent]
  have e24 : ent c d 2 4 = 1 := by norm_num [ent]
  have e30 : ent c d 3 0 = 1 + c * -1 := by norm_num [ent]
  have e31 : ent c d 3 1 = 1 + c * -Complex.I := by norm_num [ent]
  have e32 : ent c d 3 2 = 1 + c * Complex.I := by norm_num [ent]
  have e33 : ent c d 3 3 = 1 + c := by norm_num [ent]
  have e34 : ent c d 3 4 = 1 := by norm_num [ent]
  simp only [e00, e01, e02, e03, e04, e10, e11, e12, e13, e14, e20, e21, e22, e23, e24, e30, e31,
    e32, e33, e34]
  ring_nf
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  simp only [h3, h4, Complex.I_sq]
  ring_nf