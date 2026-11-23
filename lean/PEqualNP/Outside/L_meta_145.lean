import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta145

open PEqualNP.MetaComplexity

private def countVar {N : ℕ} (i : Fin N) : DMFormula N → ℕ
  | DMFormula.lit j _ => if j = i then 1 else 0
  | DMFormula.and φ ψ => countVar i φ + countVar i ψ
  | DMFormula.or φ ψ => countVar i φ + countVar i ψ

private lemma sum_countVar {N : ℕ} (φ : DMFormula N) :
    ∑ i : Fin N, countVar i φ = φ.leaves := by
  induction φ with
  | lit j b =>
    simp [countVar, DMFormula.leaves]
  | and φ ψ ih₁ ih₂ =>
    simp [countVar, DMFormula.leaves, Finset.sum_add_distrib, ih₁, ih₂]
  | or φ ψ ih₁ ih₂ =>
    simp [countVar, DMFormula.leaves, Finset.sum_add_distrib, ih₁, ih₂]

private lemma eval_update_of_countVar_zero {N : ℕ} {i : Fin N} {φ : DMFormula N}
    (h0 : countVar i φ = 0) (x : Fin N → Bool) (b : Bool) :
    φ.eval (Function.update x i b) = φ.eval x := by
  induction φ with
  | lit j pol =>
    simp only [countVar] at h0
    have hne : j ≠ i := by
      intro hEq
      subst hEq
      simp at h0
    simp [DMFormula.eval, Function.update, hne]
  | and φ ψ ih₁ ih₂ =>
    simp only [countVar] at h0
    simp [DMFormula.eval, ih₁ (by omega), ih₂ (by omega)]
  | or φ ψ ih₁ ih₂ =>
    simp only [countVar] at h0
    simp [DMFormula.eval, ih₁ (by omega), ih₂ (by omega)]

private def upd2 {N : ℕ} (ib ic : Fin N) (x : Fin N → Bool) (vb vc : Bool) : Fin N → Bool :=
  Function.update (Function.update x ib vb) ic vc

private lemma upd2_eq_update_ic {N : ℕ} (ib ic : Fin N) (x : Fin N → Bool) (vb vc₁ vc₂ : Bool) :
    upd2 ib ic x vb vc₂ = Function.update (upd2 ib ic x vb vc₁) ic vc₂ := by
  ext j
  simp only [upd2, Function.update]
  split_ifs <;> rfl

private lemma upd2_eq_update_ib {N : ℕ} {ib ic : Fin N} (hne : ib ≠ ic)
    (x : Fin N → Bool) (vb₁ vb₂ vc : Bool) :
    upd2 ib ic x vb₂ vc = Function.update (upd2 ib ic x vb₁ vc) ib vb₂ := by
  ext j
  simp only [upd2, Function.update]
  by_cases hjc : j = ic
  · subst hjc
    simp [hne.symm]
  · by_cases hjb : j = ib
    · subst hjb
      simp [hjc]
    · simp [hjc, hjb]

private lemma not_both_and_or {N : ℕ} {ib ic : Fin N} (hne : ib ≠ ic)
    (x0 x1 : Fin N → Bool) (φ : DMFormula N)
    (hb : countVar ib φ ≤ 1) (hc : countVar ic φ ≤ 1)
    (hand : ∀ vb vc : Bool, φ.eval (upd2 ib ic x0 vb vc) = (vb && vc))
    (hor : ∀ vb vc : Bool, φ.eval (upd2 ib ic x1 vb vc) = (vb || vc)) : False := by
  induction φ with
  | lit j pol =>
    by_cases hjb : j = ib
    · have hc0 : countVar ic (DMFormula.lit j pol) = 0 := by
        simp [countVar, hjb, hne]
      have h1 := hand true false
      have h2 := hand true true
      have heq : (DMFormula.lit j pol).eval (upd2 ib ic x0 true true) =
          (DMFormula.lit j pol).eval (upd2 ib ic x0 true false) := by
        rw [upd2_eq_update_ic ib ic x0 true false true]
        exact eval_update_of_countVar_zero hc0 _ _
      rw [h1, h2] at heq
      cases heq
    · have hb0 : countVar ib (DMFormula.lit j pol) = 0 := by
        simp [countVar, hjb]
      have h1 := hand false true
      have h2 := hand true true
      have heq : (DMFormula.lit j pol).eval (upd2 ib ic x0 true true) =
          (DMFormula.lit j pol).eval (upd2 ib ic x0 false true) := by
        rw [upd2_eq_update_ib hne x0 false true true]
        exact eval_update_of_countVar_zero hb0 _ _
      rw [h1, h2] at heq
      cases heq
  | and ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [countVar] at hb hc
    have hsplit_b : countVar ib ψ₁ = 0 ∨ countVar ib ψ₂ = 0 := by omega
    have hsplit_c : countVar ic ψ₁ = 0 ∨ countVar ic ψ₂ = 0 := by omega
    rcases hsplit_b with hb1 | hb2 <;> rcases hsplit_c with hc1 | hc2
    · have hconst : ∀ (x : Fin N → Bool) (vb vc : Bool),
          ψ₁.eval (upd2 ib ic x vb vc) = ψ₁.eval (upd2 ib ic x true true) := by
        intro x vb vc
        rw [upd2_eq_update_ic ib ic x vb true vc, eval_update_of_countVar_zero hc1]
        rw [upd2_eq_update_ib hne x true vb true, eval_update_of_countVar_zero hb1]
      have h0t : ψ₁.eval (upd2 ib ic x0 true true) = true := by
        have h := hand true true
        simp only [DMFormula.eval, Bool.and_self] at h
        exact (Bool.and_eq_true _ _).mp h |>.1
      have h1t : ψ₁.eval (upd2 ib ic x1 true true) = true := by
        have h := hor true true
        simp only [DMFormula.eval, Bool.or_self] at h
        exact (Bool.and_eq_true _ _).mp h |>.1
      apply ih₂ (by omega) (by omega)
      · intro vb vc
        have h := hand vb vc
        simp only [DMFormula.eval, hconst x0 vb vc, h0t, Bool.true_and] at h
        exact h
      · intro vb vc
        have h := hor vb vc
        simp only [DMFormula.eval, hconst x1 vb vc, h1t, Bool.true_and] at h
        exact h
    · have h1tf := hor true false
      have h1ft := hor false true
      have h1ff := hor false false
      simp only [DMFormula.eval, Bool.or_false, Bool.false_or] at h1tf h1ft h1ff
      have hψ1_tf : ψ₁.eval (upd2 ib ic x1 true false) = true := ((Bool.and_eq_true _ _).mp h1tf).1
      have hψ2_ft : ψ₂.eval (upd2 ib ic x1 false true) = true := ((Bool.and_eq_true _ _).mp h1ft).2
      have hψ1_ff : ψ₁.eval (upd2 ib ic x1 false false) = true := by
        rw [upd2_eq_update_ib hne x1 true false false, eval_update_of_countVar_zero hb1]
        exact hψ1_tf
      have hψ2_ff : ψ₂.eval (upd2 ib ic x1 false false) = true := by
        rw [upd2_eq_update_ic ib ic x1 false true false, eval_update_of_countVar_zero hc2]
        exact hψ2_ft
      rw [hψ1_ff, hψ2_ff] at h1ff
      cases h1ff
    · have h1tf := hor true false
      have h1ft := hor false true
      have h1ff := hor false false
      simp only [DMFormula.eval, Bool.or_false, Bool.false_or] at h1tf h1ft h1ff
      have hψ1_ft : ψ₁.eval (upd2 ib ic x1 false true) = true := ((Bool.and_eq_true _ _).mp h1ft).1
      have hψ2_tf : ψ₂.eval (upd2 ib ic x1 true false) = true := ((Bool.and_eq_true _ _).mp h1tf).2
      have hψ1_ff : ψ₁.eval (upd2 ib ic x1 false false) = true := by
        rw [upd2_eq_update_ic ib ic x1 false true false, eval_update_of_countVar_zero hc1]
        exact hψ1_ft
      have hψ2_ff : ψ₂.eval (upd2 ib ic x1 false false) = true := by
        rw [upd2_eq_update_ib hne x1 true false false, eval_update_of_countVar_zero hb2]
        exact hψ2_tf
      rw [hψ1_ff, hψ2_ff] at h1ff
      cases h1ff
    · have hconst : ∀ (x : Fin N → Bool) (vb vc : Bool),
          ψ₂.eval (upd2 ib ic x vb vc) = ψ₂.eval (upd2 ib ic x true true) := by
        intro x vb vc
        rw [upd2_eq_update_ic ib ic x vb true vc, eval_update_of_countVar_zero hc2]
        rw [upd2_eq_update_ib hne x true vb true, eval_update_of_countVar_zero hb2]
      have h0t : ψ₂.eval (upd2 ib ic x0 true true) = true := by
        have h := hand true true
        simp only [DMFormula.eval, Bool.and_self] at h
        exact (Bool.and_eq_true _ _).mp h |>.2
      have h1t : ψ₂.eval (upd2 ib ic x1 true true) = true := by
        have h := hor true true
        simp only [DMFormula.eval, Bool.or_self] at h
        exact (Bool.and_eq_true _ _).mp h |>.2
      apply ih₁ (by omega) (by omega)
      · intro vb vc
        have h := hand vb vc
        simp only [DMFormula.eval, hconst x0 vb vc, h0t, Bool.and_true] at h
        exact h
      · intro vb vc
        have h := hor vb vc
        simp only [DMFormula.eval, hconst x1 vb vc, h1t, Bool.and_true] at h
        exact h
  | or ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [countVar] at hb hc
    have hsplit_b : countVar ib ψ₁ = 0 ∨ countVar ib ψ₂ = 0 := by omega
    have hsplit_c : countVar ic ψ₁ = 0 ∨ countVar ic ψ₂ = 0 := by omega
    rcases hsplit_b with hb1 | hb2 <;> rcases hsplit_c with hc1 | hc2
    · have hconst : ∀ (x : Fin N → Bool) (vb vc : Bool),
          ψ₁.eval (upd2 ib ic x vb vc) = ψ₁.eval (upd2 ib ic x false false) := by
        intro x vb vc
        rw [upd2_eq_update_ic ib ic x vb false vc, eval_update_of_countVar_zero hc1]
        rw [upd2_eq_update_ib hne x false vb false, eval_update_of_countVar_zero hb1]
      have h0f : ψ₁.eval (upd2 ib ic x0 false false) = false := by
        have h := hand false false
        simp only [DMFormula.eval, Bool.and_self] at h
        exact (Bool.or_eq_false_iff.mp h).1
      have h1f : ψ₁.eval (upd2 ib ic x1 false false) = false := by
        have h := hor false false
        simp only [DMFormula.eval, Bool.or_self] at h
        exact (Bool.or_eq_false_iff.mp h).1
      apply ih₂ (by omega) (by omega)
      · intro vb vc
        have h := hand vb vc
        simp only [DMFormula.eval, hconst x0 vb vc, h0f, Bool.false_or] at h
        exact h
      · intro vb vc
        have h := hor vb vc
        simp only [DMFormula.eval, hconst x1 vb vc, h1f, Bool.false_or] at h
        exact h
    · have h0tf := hand true false
      have h0ft := hand false true
      have h0tt := hand true true
      simp only [DMFormula.eval, Bool.and_false, Bool.false_and, Bool.and_true] at h0tf h0ft h0tt
      have hψ1_ft : ψ₁.eval (upd2 ib ic x0 false true) = false := (Bool.or_eq_false_iff.mp h0ft).1
      have hψ2_tf : ψ₂.eval (upd2 ib ic x0 true false) = false := (Bool.or_eq_false_iff.mp h0tf).2
      have hψ1_tt : ψ₁.eval (upd2 ib ic x0 true true) = false := by
        rw [upd2_eq_update_ib hne x0 false true true, eval_update_of_countVar_zero hb1]
        exact hψ1_ft
      have hψ2_tt : ψ₂.eval (upd2 ib ic x0 true true) = false := by
        rw [upd2_eq_update_ic ib ic x0 true false true, eval_update_of_countVar_zero hc2]
        exact hψ2_tf
      rw [hψ1_tt, hψ2_tt] at h0tt
      cases h0tt
    · have h0tf := hand true false
      have h0ft := hand false true
      have h0tt := hand true true
      simp only [DMFormula.eval, Bool.and_false, Bool.false_and, Bool.and_true] at h0tf h0ft h0tt
      have hψ1_tf : ψ₁.eval (upd2 ib ic x0 true false) = false := (Bool.or_eq_false_iff.mp h0tf).1
      have hψ2_ft : ψ₂.eval (upd2 ib ic x0 false true) = false := (Bool.or_eq_false_iff.mp h0ft).2
      have hψ1_tt : ψ₁.eval (upd2 ib ic x0 true true) = false := by
        rw [upd2_eq_update_ic ib ic x0 true false true, eval_update_of_countVar_zero hc1]
        exact hψ1_tf
      have hψ2_tt : ψ₂.eval (upd2 ib ic x0 true true) = false := by
        rw [upd2_eq_update_ib hne x0 false true true, eval_update_of_countVar_zero hb2]
        exact hψ2_ft
      rw [hψ1_tt, hψ2_tt] at h0tt
      cases h0tt
    · have hconst : ∀ (x : Fin N → Bool) (vb vc : Bool),
          ψ₂.eval (upd2 ib ic x vb vc) = ψ₂.eval (upd2 ib ic x false false) := by
        intro x vb vc
        rw [upd2_eq_update_ic ib ic x vb false vc, eval_update_of_countVar_zero hc2]
        rw [upd2_eq_update_ib hne x false vb false, eval_update_of_countVar_zero hb2]
      have h0f : ψ₂.eval (upd2 ib ic x0 false false) = false := by
        have h := hand false false
        simp only [DMFormula.eval, Bool.and_self] at h
        exact (Bool.or_eq_false_iff.mp h).2
      have h1f : ψ₂.eval (upd2 ib ic x1 false false) = false := by
        have h := hor false false
        simp only [DMFormula.eval, Bool.or_self] at h
        exact (Bool.or_eq_false_iff.mp h).2
      apply ih₁ (by omega) (by omega)
      · intro vb vc
        have h := hand vb vc
        simp only [DMFormula.eval, hconst x0 vb vc, h0f, Bool.or_false] at h
        exact h
      · intro vb vc
        have h := hor vb vc
        simp only [DMFormula.eval, hconst x1 vb vc, h1f, Bool.or_false] at h
        exact h

private def orRange (N : ℕ) : (start len : ℕ) → 1 ≤ len → start + len ≤ N → DMFormula N
  | start, 1, _, hlt => DMFormula.lit ⟨start, by omega⟩ true
  | start, d + 2, _, hlt =>
      DMFormula.or (DMFormula.lit ⟨start, by omega⟩ true)
        (orRange N (start + 1) (d + 1) (by omega) (by omega))

private lemma orRange_leaves (N start len : ℕ) (h1 : 1 ≤ len) (hlt : start + len ≤ N) :
    (orRange N start len h1 hlt).leaves = len := by
  induction len generalizing start with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ d =>
      simp only [orRange, DMFormula.leaves]
      rw [ih (start + 1) (by omega) (by omega)]
      omega

private lemma orRange_eval (N start len : ℕ) (h1 : 1 ≤ len) (hlt : start + len ≤ N)
    (x : Fin N → Bool) :
    (orRange N start len h1 hlt).eval x =
      decide (∃ i : Fin N, start ≤ i.val ∧ i.val < start + len ∧ x i = true) := by
  induction len generalizing start with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp only [orRange, DMFormula.eval, ite_true]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro hx
        exact ⟨⟨start, by omega⟩, by dsimp only; omega, by dsimp only; omega, hx⟩
      · rintro ⟨i, hi1, hi2, hxi⟩
        have hEq : i = ⟨start, by omega⟩ := Fin.ext (by dsimp only; omega)
        rwa [← hEq]
    | succ d =>
      simp only [orRange, DMFormula.eval, ite_true]
      rw [ih (start + 1) (by omega) (by omega)]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (hx | ⟨i, hi1, hi2, hxi⟩)
        · exact ⟨⟨start, by omega⟩, by dsimp only; omega, by dsimp only; omega, hx⟩
        · exact ⟨i, by omega, by omega, hxi⟩
      · rintro ⟨i, hi1, hi2, hxi⟩
        rcases Nat.eq_or_lt_of_le hi1 with hEq | hgt
        · left
          have hfin : i = ⟨start, by omega⟩ := Fin.ext hEq.symm
          rwa [← hfin]
        · right
          exact ⟨i, by omega, by omega, hxi⟩

end PEqualNP.Outside.Meta145

open PEqualNP.MetaComplexity PEqualNP.Outside.Meta145 in
theorem PEqualNP.Outside.L_meta_145 :
    ∀ (ka kb kc kd s : ℕ), 1 ≤ ka → 1 ≤ kb → 1 ≤ kc → 1 ≤ kd → (PEqualNP.MetaComplexity.HasLeafSize (ka + kb + kc + kd) (fun x : Fin (ka + kb + kc + kd) → Bool => decide (((∃ i : Fin (ka + kb + kc + kd), i.val < ka ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true)) ∨ ((∃ i : Fin (ka + kb + kc + kd), ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true)) ∨ ((∃ i : Fin (ka + kb + kc + kd), ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true) ∧ (∃ i : Fin (ka + kb + kc + kd), ka + kb + kc ≤ i.val ∧ x i = true)))) s ↔ ka + kb + kc + kd + min kb kc ≤ s) := by
  intro ka kb kc kd s hka hkb hkc hkd
  let N := ka + kb + kc + kd
  let f : (Fin N → Bool) → Bool := fun x =>
    decide (((∃ i : Fin N, i.val < ka ∧ x i = true) ∧
      (∃ i : Fin N, ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true)) ∨
      ((∃ i : Fin N, ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true) ∧
      (∃ i : Fin N, ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true)) ∨
      ((∃ i : Fin N, ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true) ∧
      (∃ i : Fin N, ka + kb + kc ≤ i.val ∧ x i = true)))
  change HasLeafSize N f s ↔ N + min kb kc ≤ s
  constructor
  · rintro ⟨φ, hle, heval⟩
    by_contra hlt
    have hφlt : φ.leaves < N + min kb kc := by omega
    have hge1 : ∀ i : Fin N, 1 ≤ countVar i φ := by
      intro i
      by_contra h0
      have hzero : countVar i φ = 0 := by omega
      have hinv : ∀ x : Fin N → Bool, f (Function.update x i true) = f (Function.update x i false) := by
        intro x
        rw [← heval, ← heval, eval_update_of_countVar_zero hzero, eval_update_of_countVar_zero hzero]
      by_cases hi1 : i.val < ka
      · let p : Fin N := ⟨ka, by omega⟩
        have hEq := hinv (fun j : Fin N => decide (j = p))
        have hT : f (Function.update (fun j : Fin N => decide (j = p)) i true) = true := by
          simp only [f, decide_eq_true_eq]
          left
          refine ⟨⟨i, hi1, by simp⟩, ⟨p, by dsimp only [p]; omega, by dsimp only [p]; omega, ?_⟩⟩
          have hne : p ≠ i := fun h => by have := congrArg Fin.val h; dsimp only [p] at this; omega
          simp [Function.update, hne]
        have hF : f (Function.update (fun j : Fin N => decide (j = p)) i false) = false := by
          simp only [f, decide_eq_false_iff_not]
          rintro (⟨⟨j, hj1, hj2⟩, _⟩ | ⟨_, ⟨j, hj1, hj2, hj3⟩⟩ | ⟨⟨j, hj1, hj2, hj3⟩, _⟩)
          · by_cases hji : j = i
            · subst hji; simp at hj2
            · simp [Function.update, hji] at hj2
              subst hj2; dsimp only [p] at hj1; omega
          · by_cases hji : j = i
            · subst hji; simp at hj3
            · simp [Function.update, hji] at hj3
              subst hj3; dsimp only [p] at hj1; omega
          · by_cases hji : j = i
            · subst hji; simp at hj3
            · simp [Function.update, hji] at hj3
              subst hj3; dsimp only [p] at hj1; omega
        rw [hT, hF] at hEq
        cases hEq
      · by_cases hi2 : i.val < ka + kb
        · let p : Fin N := ⟨0, by omega⟩
          have hEq := hinv (fun j : Fin N => decide (j = p))
          have hT : f (Function.update (fun j : Fin N => decide (j = p)) i true) = true := by
            simp only [f, decide_eq_true_eq]
            left
            refine ⟨⟨p, by dsimp only [p]; omega, ?_⟩, ⟨i, by omega, hi2, by simp⟩⟩
            have hne : p ≠ i := fun h => by have := congrArg Fin.val h; dsimp only [p] at this; omega
            simp [Function.update, hne]
          have hF : f (Function.update (fun j : Fin N => decide (j = p)) i false) = false := by
            simp only [f, decide_eq_false_iff_not]
            rintro (⟨_, ⟨j, hj1, hj2, hj3⟩⟩ | ⟨⟨j, hj1, hj2, hj3⟩, _⟩ | ⟨⟨j, hj1, hj2, hj3⟩, _⟩)
            · by_cases hji : j = i
              · subst hji; simp at hj3
              · simp [Function.update, hji] at hj3
                subst hj3; dsimp only [p] at hj1; omega
            · by_cases hji : j = i
              · subst hji; simp at hj3
              · simp [Function.update, hji] at hj3
                subst hj3; dsimp only [p] at hj1; omega
            · by_cases hji : j = i
              · subst hji; simp at hj3
              · simp [Function.update, hji] at hj3
                subst hj3; dsimp only [p] at hj1; omega
          rw [hT, hF] at hEq
          cases hEq
        · by_cases hi3 : i.val < ka + kb + kc
          · let p : Fin N := ⟨ka + kb + kc, by omega⟩
            have hEq := hinv (fun j : Fin N => decide (j = p))
            have hT : f (Function.update (fun j : Fin N => decide (j = p)) i true) = true := by
              simp only [f, decide_eq_true_eq]
              right; right
              refine ⟨⟨i, by omega, hi3, by simp⟩, ⟨p, by dsimp only [p]; omega, ?_⟩⟩
              have hne : p ≠ i := fun h => by have := congrArg Fin.val h; dsimp only [p] at this; omega
              simp [Function.update, hne]
            have hF : f (Function.update (fun j : Fin N => decide (j = p)) i false) = false := by
              simp only [f, decide_eq_false_iff_not]
              rintro (⟨⟨j, hj1, hj2⟩, _⟩ | ⟨_, ⟨j, hj1, hj2, hj3⟩⟩ | ⟨⟨j, hj1, hj2, hj3⟩, _⟩)
              · by_cases hji : j = i
                · subst hji; simp at hj2
                · simp [Function.update, hji] at hj2
                  subst hj2; dsimp only [p] at hj1; omega
              · by_cases hji : j = i
                · subst hji; simp at hj3
                · simp [Function.update, hji] at hj3
                  subst hj3; dsimp only [p] at hj2; omega
              · by_cases hji : j = i
                · subst hji; simp at hj3
                · simp [Function.update, hji] at hj3
                  subst hj3; dsimp only [p] at hj2; omega
            rw [hT, hF] at hEq
            cases hEq
          · let p : Fin N := ⟨ka + kb, by omega⟩
            have hEq := hinv (fun j : Fin N => decide (j = p))
            have hT : f (Function.update (fun j : Fin N => decide (j = p)) i true) = true := by
              simp only [f, decide_eq_true_eq]
              right; right
              refine ⟨⟨p, by dsimp only [p]; omega, by dsimp only [p]; omega, ?_⟩, ⟨i, by omega, by simp⟩⟩
              have hne : p ≠ i := fun h => by have := congrArg Fin.val h; dsimp only [p] at this; omega
              simp [Function.update, hne]
            have hF : f (Function.update (fun j : Fin N => decide (j = p)) i false) = false := by
              simp only [f, decide_eq_false_iff_not]
              rintro (⟨⟨j, hj1, hj2⟩, _⟩ | ⟨⟨j, hj1, hj2, hj3⟩, _⟩ | ⟨_, ⟨j, hj1, hj2⟩⟩)
              · by_cases hji : j = i
                · subst hji; simp at hj2
                · simp [Function.update, hji] at hj2
                  subst hj2; dsimp only [p] at hj1; omega
              · by_cases hji : j = i
                · subst hji; simp at hj3
                · simp [Function.update, hji] at hj3
                  subst hj3; dsimp only [p] at hj2; omega
              · by_cases hji : j = i
                · subst hji; simp at hj2
                · simp [Function.update, hji] at hj2
                  subst hj2; dsimp only [p] at hj1; omega
            rw [hT, hF] at hEq
            cases hEq
    have hexB : ∃ ib : Fin N, ka ≤ ib.val ∧ ib.val < ka + kb ∧ countVar ib φ ≤ 1 := by
      by_contra hno
      push Not at hno
      let B : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => ka ≤ i.val ∧ i.val < ka + kb)
      have hBcard : B.card = kb := by
        let e : Fin kb → Fin N := fun j => ⟨ka + j.val, by omega⟩
        have hBeq : B = Finset.univ.image e := by
          ext i
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, e]
          constructor
          · intro ⟨h1, h2⟩
            exact ⟨⟨i.val - ka, by omega⟩, Fin.ext (by dsimp only; omega)⟩
          · rintro ⟨j, rfl⟩
            exact ⟨by dsimp only; omega, by dsimp only; omega⟩
        rw [hBeq, Finset.card_image_of_injective _ (fun j₁ j₂ h => Fin.ext (by have := congrArg Fin.val h; dsimp only [e] at this; omega)), Finset.card_fin]
      have hsum : N + kb ≤ ∑ i : Fin N, countVar i φ := by
        have hstep : ∀ i ∈ (Finset.univ : Finset (Fin N)),
            (1 + if i ∈ B then 1 else 0) ≤ countVar i φ := by
          intro i _
          split_ifs with hiB
          · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hiB
            exact hno i hiB.1 hiB.2
          · exact hge1 i
        have hle' := Finset.sum_le_sum hstep
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one] at hle'
        have hBsum : ∑ i : Fin N, (if i ∈ B then (1 : ℕ) else 0) = B.card := by
          simp
        rw [hBsum, hBcard] at hle'
        exact hle'
      rw [sum_countVar] at hsum
      omega
    have hexC : ∃ ic : Fin N, ka + kb ≤ ic.val ∧ ic.val < ka + kb + kc ∧ countVar ic φ ≤ 1 := by
      by_contra hno
      push Not at hno
      let C : Finset (Fin N) :=
        Finset.univ.filter (fun i : Fin N => ka + kb ≤ i.val ∧ i.val < ka + kb + kc)
      have hCcard : C.card = kc := by
        let e : Fin kc → Fin N := fun j => ⟨ka + kb + j.val, by omega⟩
        have hCeq : C = Finset.univ.image e := by
          ext i
          simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, e]
          constructor
          · intro ⟨h1, h2⟩
            exact ⟨⟨i.val - (ka + kb), by omega⟩, Fin.ext (by dsimp only; omega)⟩
          · rintro ⟨j, rfl⟩
            exact ⟨by dsimp only; omega, by dsimp only; omega⟩
        rw [hCeq, Finset.card_image_of_injective _ (fun j₁ j₂ h => Fin.ext (by have := congrArg Fin.val h; dsimp only [e] at this; omega)), Finset.card_fin]
      have hsum : N + kc ≤ ∑ i : Fin N, countVar i φ := by
        have hstep : ∀ i ∈ (Finset.univ : Finset (Fin N)),
            (1 + if i ∈ C then 1 else 0) ≤ countVar i φ := by
          intro i _
          split_ifs with hiC
          · simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hiC
            exact hno i hiC.1 hiC.2
          · exact hge1 i
        have hle' := Finset.sum_le_sum hstep
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one] at hle'
        have hCsum : ∑ i : Fin N, (if i ∈ C then (1 : ℕ) else 0) = C.card := by
          simp
        rw [hCsum, hCcard] at hle'
        exact hle'
      rw [sum_countVar] at hsum
      omega
    rcases hexB with ⟨ib, hib1, hib2, hcb⟩
    rcases hexC with ⟨ic, hic1, hic2, hcc⟩
    have hne_bc : ib ≠ ic := fun h => by have := congrArg Fin.val h; omega
    let x0 : Fin N → Bool := fun _ => false
    let ia : Fin N := ⟨0, by omega⟩
    let id_v : Fin N := ⟨ka + kb + kc, by omega⟩
    let x1 : Fin N → Bool := fun j => decide (j = ia ∨ j = id_v)
    apply not_both_and_or hne_bc x0 x1 φ hcb hcc
    · intro vb vc
      rw [heval]
      apply Bool.eq_iff_iff.mpr
      simp only [f, decide_eq_true_eq, Bool.and_eq_true]
      constructor
      · rintro (⟨⟨j, hj1, hj2⟩, _⟩ | ⟨⟨j₁, hj1a, hj1b, hj1c⟩, ⟨j₂, hj2a, hj2b, hj2c⟩⟩ | ⟨_, ⟨j, hj1, hj2⟩⟩)
        · exfalso
          by_cases h1 : j = ic
          · subst h1; omega
          · by_cases h2 : j = ib
            · subst h2; omega
            · simp [upd2, Function.update, h1, h2, x0] at hj2
        · have hj1_eq : j₁ = ib := by
            by_cases h1 : j₁ = ic
            · subst h1; omega
            · by_cases h2 : j₁ = ib
              · exact h2
              · simp [upd2, Function.update, h1, h2, x0] at hj1c
          have hj2_eq : j₂ = ic := by
            by_cases h1 : j₂ = ic
            · exact h1
            · by_cases h2 : j₂ = ib
              · subst h2; omega
              · simp [upd2, Function.update, h1, h2, x0] at hj2c
          subst hj1_eq hj2_eq
          simp [upd2, Function.update, hne_bc] at hj1c hj2c
          exact ⟨hj1c, hj2c⟩
        · exfalso
          by_cases h1 : j = ic
          · subst h1; omega
          · by_cases h2 : j = ib
            · subst h2; omega
            · simp [upd2, Function.update, h1, h2, x0] at hj2
      · rintro ⟨hvb, hvc⟩
        right; left
        refine ⟨⟨ib, hib1, hib2, ?_⟩, ⟨ic, hic1, hic2, ?_⟩⟩
        · simp [upd2, Function.update, hne_bc, hvb]
        · simp [upd2, Function.update, hvc]
    · intro vb vc
      rw [heval]
      apply Bool.eq_iff_iff.mpr
      simp only [f, decide_eq_true_eq, Bool.or_eq_true]
      constructor
      · rintro (⟨_, ⟨j, hj1, hj2, hj3⟩⟩ | ⟨⟨j, hj1, hj2, hj3⟩, _⟩ | ⟨⟨j, hj1, hj2, hj3⟩, _⟩)
        · left
          by_cases h1 : j = ic
          · subst h1; omega
          · by_cases h2 : j = ib
            · subst h2; simpa [upd2, Function.update, h1] using hj3
            · simp [upd2, Function.update, h1, h2, x1] at hj3
              rcases hj3 with rfl | rfl <;> (dsimp only [ia, id_v] at hj1 hj2; omega)
        · left
          by_cases h1 : j = ic
          · subst h1; omega
          · by_cases h2 : j = ib
            · subst h2; simpa [upd2, Function.update, h1] using hj3
            · simp [upd2, Function.update, h1, h2, x1] at hj3
              rcases hj3 with rfl | rfl <;> (dsimp only [ia, id_v] at hj1 hj2; omega)
        · right
          by_cases h1 : j = ic
          · subst h1; simpa [upd2, Function.update] using hj3
          · by_cases h2 : j = ib
            · subst h2; omega
            · simp [upd2, Function.update, h1, h2, x1] at hj3
              rcases hj3 with rfl | rfl <;> (dsimp only [ia, id_v] at hj1 hj2; omega)
      · rintro (hvb | hvc)
        · left
          refine ⟨⟨ia, by dsimp only [ia]; omega, ?_⟩, ⟨ib, hib1, hib2, ?_⟩⟩
          · have h1 : ia ≠ ic := fun h => by have := congrArg Fin.val h; dsimp only [ia] at this; omega
            have h2 : ia ≠ ib := fun h => by have := congrArg Fin.val h; dsimp only [ia] at this; omega
            simp [upd2, Function.update, h1, h2, x1]
          · simp [upd2, Function.update, hne_bc, hvb]
        · right; right
          refine ⟨⟨ic, hic1, hic2, ?_⟩, ⟨id_v, by dsimp only [id_v]; omega, ?_⟩⟩
          · simp [upd2, Function.update, hvc]
          · have h1 : id_v ≠ ic := fun h => by have := congrArg Fin.val h; dsimp only [id_v] at this; omega
            have h2 : id_v ≠ ib := fun h => by have := congrArg Fin.val h; dsimp only [id_v] at this; omega
            simp [upd2, Function.update, h1, h2, x1]
  · intro hs
    let φA := orRange N 0 ka hka (by omega)
    let φB := orRange N ka kb hkb (by omega)
    let φC := orRange N (ka + kb) kc hkc (by omega)
    let φD := orRange N (ka + kb + kc) kd hkd (by omega)
    have hA : ∀ x : Fin N → Bool, φA.eval x = decide (∃ i : Fin N, i.val < ka ∧ x i = true) := by
      intro x
      rw [orRange_eval]
      simp
    have hB : ∀ x : Fin N → Bool, φB.eval x =
        decide (∃ i : Fin N, ka ≤ i.val ∧ i.val < ka + kb ∧ x i = true) := fun x =>
      orRange_eval N ka kb hkb (by omega) x
    have hC : ∀ x : Fin N → Bool, φC.eval x =
        decide (∃ i : Fin N, ka + kb ≤ i.val ∧ i.val < ka + kb + kc ∧ x i = true) := fun x =>
      orRange_eval N (ka + kb) kc hkc (by omega) x
    have hD : ∀ x : Fin N → Bool, φD.eval x =
        decide (∃ i : Fin N, ka + kb + kc ≤ i.val ∧ x i = true) := by
      intro x
      rw [orRange_eval]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨i, hi1, _, hxi⟩; exact ⟨i, hi1, hxi⟩
      · rintro ⟨i, hi1, hxi⟩; exact ⟨i, hi1, by have := i.isLt; omega, hxi⟩
    by_cases hbc : kb ≤ kc
    · refine ⟨DMFormula.or (DMFormula.and φB φA) (DMFormula.and φC (DMFormula.or φB φD)), ?_, ?_⟩
      · simp only [DMFormula.leaves, φA, φB, φC, φD, orRange_leaves]
        omega
      · intro x
        simp only [DMFormula.eval, hA, hB, hC, hD, f]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨hb, ha⟩ | ⟨hc, hb | hd⟩)
          · exact Or.inl ⟨ha, hb⟩
          · exact Or.inr (Or.inl ⟨hb, hc⟩)
          · exact Or.inr (Or.inr ⟨hc, hd⟩)
        · rintro (⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨hc, hd⟩)
          · exact Or.inl ⟨hb, ha⟩
          · exact Or.inr ⟨hc, Or.inl hb⟩
          · exact Or.inr ⟨hc, Or.inr hd⟩
    · refine ⟨DMFormula.or (DMFormula.and φB (DMFormula.or φA φC)) (DMFormula.and φC φD), ?_, ?_⟩
      · simp only [DMFormula.leaves, φA, φB, φC, φD, orRange_leaves]
        omega
      · intro x
        simp only [DMFormula.eval, hA, hB, hC, hD, f]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨hb, ha | hc⟩ | ⟨hc, hd⟩)
          · exact Or.inl ⟨ha, hb⟩
          · exact Or.inr (Or.inl ⟨hb, hc⟩)
          · exact Or.inr (Or.inr ⟨hc, hd⟩)
        · rintro (⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨hc, hd⟩)
          · exact Or.inl ⟨hb, Or.inl ha⟩
          · exact Or.inl ⟨hb, Or.inr hc⟩
          · exact Or.inr ⟨hc, hd⟩
