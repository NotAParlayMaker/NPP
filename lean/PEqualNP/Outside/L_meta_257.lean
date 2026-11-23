import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_257

open PEqualNP.MetaComplexity

private noncomputable def cnt {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

private noncomputable def negcnt {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j c => if j = i ∧ c = false then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

private lemma upd_same {n : ℕ} {i : Fin n} (x : Fin n → Bool) (b : Bool) :
    (Function.update x i b) i = b := Function.update_self _ _ _

private lemma upd_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) (x : Fin n → Bool) (b : Bool) :
    (Function.update x i b) j = x j := by
  rw [Function.update_apply, if_neg h]

private lemma negcnt_le_cnt {n : ℕ} (i : Fin n) : ∀ φ : DMFormula n, negcnt i φ ≤ cnt i φ := by
  intro φ
  induction φ with
  | lit j c =>
    have h1 : negcnt i (DMFormula.lit j c) = (if j = i ∧ c = false then 1 else 0) := rfl
    have h2 : cnt i (DMFormula.lit j c) = (if j = i then 1 else 0) := rfl
    rw [h1, h2]
    by_cases hji : j = i <;> by_cases hc : c = false <;> simp [hji, hc]
  | and φ1 φ2 ih1 ih2 =>
    show negcnt i φ1 + negcnt i φ2 ≤ cnt i φ1 + cnt i φ2
    exact Nat.add_le_add ih1 ih2
  | or φ1 φ2 ih1 ih2 =>
    show negcnt i φ1 + negcnt i φ2 ≤ cnt i φ1 + cnt i φ2
    exact Nat.add_le_add ih1 ih2

private lemma eval_congr_free {n : ℕ} (i : Fin n) : ∀ (φ : DMFormula n), cnt i φ = 0 →
    ∀ {x y : Fin n → Bool}, (∀ j, j ≠ i → x j = y j) → φ.eval x = φ.eval y := by
  intro φ
  induction φ with
  | lit j c =>
    intro h x y hxy
    have h0 : (if j = i then 1 else 0) = 0 := h
    have hji : j ≠ i := by
      by_contra hne
      rw [if_pos hne] at h0
      exact absurd h0 (by simp)
    simp [DMFormula.eval, hxy j hji]
  | and φ1 φ2 ih1 ih2 =>
    intro h x y hxy
    have h' : cnt i φ1 + cnt i φ2 = 0 := h
    obtain ⟨h1, h2⟩ := Nat.add_eq_zero.mp h'
    simp [DMFormula.eval, ih1 h1 hxy, ih2 h2 hxy]
  | or φ1 φ2 ih1 ih2 =>
    intro h x y hxy
    have h' : cnt i φ1 + cnt i φ2 = 0 := h
    obtain ⟨h1, h2⟩ := Nat.add_eq_zero.mp h'
    simp [DMFormula.eval, ih1 h1 hxy, ih2 h2 hxy]

private lemma or_and (a b c : Bool) : ((a || b) && c) = ((a && c) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide

private lemma and_or' (a b c d : Bool) : (a && ((b && c) || d)) = ((b && (a && c)) || (a && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma or_or' (a b c d : Bool) : (a || ((b && c) || d)) = ((b && c) || (a || d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma decomp {n : ℕ} (i : Fin n) : ∀ (φ : DMFormula n), cnt i φ = 1 →
    ∃ (c : Bool) (A B : (Fin n → Bool) → Bool),
      (∀ x, φ.eval x = (((if c then x i else !(x i)) && A x) || B x)) ∧
      (∀ x y, (∀ j, j ≠ i → x j = y j) → A x = A y) ∧
      (∀ x y, (∀ j, j ≠ i → x j = y j) → B x = B y) ∧
      negcnt i φ = (if c = false then 1 else 0) := by
  intro φ
  induction φ with
  | lit j c =>
    intro h
    have h0 : (if j = i then 1 else 0) = 1 := h
    have hji : j = i := by
      by_contra hne
      rw [if_neg hne] at h0
      exact absurd h0 (by simp)
    rw [hji]
    refine ⟨c, fun _ => true, fun _ => false, ?_, ?_, ?_, ?_⟩
    · intro x
      simp [DMFormula.eval]
    · intro x y _
      rfl
    · intro x y _
      rfl
    · show (if i = i ∧ c = false then 1 else 0) = (if c = false then 1 else 0)
      by_cases hc : c = false <;> simp [hc]
  | and φ1 φ2 ih1 ih2 =>
    intro h
    have h' : cnt i φ1 + cnt i φ2 = 1 := h
    have hcases : (cnt i φ1 = 1 ∧ cnt i φ2 = 0) ∨ (cnt i φ1 = 0 ∧ cnt i φ2 = 1) := by
      omega
    rcases hcases with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
    · obtain ⟨c, A1, B1, hev1, hA1, hB1, hneg1⟩ := ih1 hc1
      have hfree2 : ∀ x y, (∀ j, j ≠ i → x j = y j) → φ2.eval x = φ2.eval y :=
        fun x y hxy => eval_congr_free i φ2 hc2 hxy
      have hneg2 : negcnt i φ2 = 0 := by
        have hle := negcnt_le_cnt i φ2
        omega
      refine ⟨c, fun x => A1 x && φ2.eval x, fun x => B1 x && φ2.eval x, ?_, ?_, ?_, ?_⟩
      · intro x
        simp [DMFormula.eval, hev1 x, or_and, Bool.and_assoc]
      · intro x y hxy
        simp [hA1 x y hxy, hfree2 x y hxy]
      · intro x y hxy
        simp [hB1 x y hxy, hfree2 x y hxy]
      · show negcnt i φ1 + negcnt i φ2 = (if c = false then 1 else 0)
        rw [hneg1, hneg2]
        by_cases hc : c = false <;> simp [hc]
    · obtain ⟨c, A2, B2, hev2, hA2, hB2, hneg2⟩ := ih2 hc2
      have hfree1 : ∀ x y, (∀ j, j ≠ i → x j = y j) → φ1.eval x = φ1.eval y :=
        fun x y hxy => eval_congr_free i φ1 hc1 hxy
      have hneg1 : negcnt i φ1 = 0 := by
        have hle := negcnt_le_cnt i φ1
        omega
      refine ⟨c, fun x => φ1.eval x && A2 x, fun x => φ1.eval x && B2 x, ?_, ?_, ?_, ?_⟩
      · intro x
        simp [DMFormula.eval, hev2 x, or_and, and_or', Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      · intro x y hxy
        simp [hfree1 x y hxy, hA2 x y hxy]
      · intro x y hxy
        simp [hfree1 x y hxy, hB2 x y hxy]
      · show negcnt i φ1 + negcnt i φ2 = (if c = false then 1 else 0)
        rw [hneg1, hneg2]
        by_cases hc : c = false <;> simp [hc]
  | or φ1 φ2 ih1 ih2 =>
    intro h
    have h' : cnt i φ1 + cnt i φ2 = 1 := h
    have hcases : (cnt i φ1 = 1 ∧ cnt i φ2 = 0) ∨ (cnt i φ1 = 0 ∧ cnt i φ2 = 1) := by
      omega
    rcases hcases with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
    · obtain ⟨c, A1, B1, hev1, hA1, hB1, hneg1⟩ := ih1 hc1
      have hfree2 : ∀ x y, (∀ j, j ≠ i → x j = y j) → φ2.eval x = φ2.eval y :=
        fun x y hxy => eval_congr_free i φ2 hc2 hxy
      have hneg2 : negcnt i φ2 = 0 := by
        have hle := negcnt_le_cnt i φ2
        omega
      refine ⟨c, A1, fun x => B1 x || φ2.eval x, ?_, ?_, ?_, ?_⟩
      · intro x
        simp [DMFormula.eval, hev1 x, Bool.or_assoc]
      · exact hA1
      · intro x y hxy
        simp [hB1 x y hxy, hfree2 x y hxy]
      · show negcnt i φ1 + negcnt i φ2 = (if c = false then 1 else 0)
        rw [hneg1, hneg2]
        by_cases hc : c = false <;> simp [hc]
    · obtain ⟨c, A2, B2, hev2, hA2, hB2, hneg2⟩ := ih2 hc2
      have hfree1 : ∀ x y, (∀ j, j ≠ i → x j = y j) → φ1.eval x = φ1.eval y :=
        fun x y hxy => eval_congr_free i φ1 hc1 hxy
      have hneg1 : negcnt i φ1 = 0 := by
        have hle := negcnt_le_cnt i φ1
        omega
      refine ⟨c, A2, fun x => φ1.eval x || B2 x, ?_, ?_, ?_, ?_⟩
      · intro x
        simp [DMFormula.eval, hev2 x, or_or', Bool.or_assoc]
      · exact hA2
      · intro x y hxy
        simp [hfree1 x y hxy, hB2 x y hxy]
      · show negcnt i φ1 + negcnt i φ2 = (if c = false then 1 else 0)
        rw [hneg1, hneg2]
        by_cases hc : c = false <;> simp [hc]

end PEqualNP.Outside.L_meta_257

open PEqualNP.Outside.L_meta_257

theorem PEqualNP.Outside.L_meta_257 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 1 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 := by
  intro n f φ i hmono hess hev hcnt
  show negcnt i φ = 0
  have hcnt1 : cnt i φ = 1 := hcnt
  obtain ⟨c, A, B, hdeq, hA, hB, hneg⟩ := decomp i φ hcnt1
  rw [hneg]
  cases c with
  | false =>
    rw [if_pos rfl]
    exfalso
    have hdeq' : ∀ x, φ.eval x = ((!(x i) && A x) || B x) := by
      intro x
      have h2 := hdeq x
      simp only [if_neg Bool.false_ne_true] at h2
      exact h2
    have hAB : ∀ x, A x = true → B x = true := by
      intro x hAx
      by_contra hBx
      have hBxf : B x = false := by
        cases hb : B x with
        | true => exact absurd hb hBx
        | false => rfl
      have hA0 : A (Function.update x i false) = A x :=
        hA _ _ (fun j hj => upd_ne hj x false)
      have hB0 : B (Function.update x i false) = B x :=
        hB _ _ (fun j hj => upd_ne hj x false)
      have hA1 : A (Function.update x i true) = A x :=
        hA _ _ (fun j hj => upd_ne hj x true)
      have hB1 : B (Function.update x i true) = B x :=
        hB _ _ (fun j hj => upd_ne hj x true)
      have hf0 : f (Function.update x i false) = true := by
        simp [← hev, hdeq', upd_same x false, hA0, hB0, hAx, hBxf]
      have hf1 : f (Function.update x i true) = false := by
        simp [← hev, hdeq', upd_same x true, hA1, hB1, hAx, hBxf]
      have hle : ∀ j : Fin n, (Function.update x i false) j = true → (Function.update x i true) j = true := by
        intro j hj
        by_cases hji : j = i
        · rw [hji, upd_same x false] at hj
          simp at hj
        · rw [upd_ne hji x false] at hj
          rw [upd_ne hji x true]
          exact hj
      have htrue := hmono _ _ hle hf0
      rw [hf1] at htrue
      simp at htrue
    have hfB : ∀ x, f x = B x := by
      intro x
      rw [← hev x, hdeq' x]
      by_cases hAx : A x = true
      · rw [hAB x hAx]
        simp
      · have hAx' : A x = false := by
          cases ha : A x with
          | true => exact absurd ha hAx
          | false => rfl
        rw [hAx']
        simp
    obtain ⟨x, hx⟩ := hess
    apply hx
    rw [hfB, hfB]
    exact hB _ _ (fun j hj => by rw [upd_ne hj x true, upd_ne hj x false])
  | true =>
    rw [if_neg (by simp : ¬(true = false))]
