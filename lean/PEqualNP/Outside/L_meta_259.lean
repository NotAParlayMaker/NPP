import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_259

open PEqualNP.MetaComplexity

private noncomputable def cnt {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

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
    obtain ⟨h1, h2⟩ := Nat.add_eq_zero_iff.mp h'
    simp [DMFormula.eval, ih1 h1 hxy, ih2 h2 hxy]
  | or φ1 φ2 ih1 ih2 =>
    intro h x y hxy
    have h' : cnt i φ1 + cnt i φ2 = 0 := h
    obtain ⟨h1, h2⟩ := Nat.add_eq_zero_iff.mp h'
    simp [DMFormula.eval, ih1 h1 hxy, ih2 h2 hxy]

private lemma or_and (a b c : Bool) : ((a || b) && c) = ((a && c) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> decide

private lemma and_or' (a b c d : Bool) : (a && ((b && c) || d)) = ((b && (a && c)) || (a && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma or_or' (a b c d : Bool) : (a || ((b && c) || d)) = ((b && c) || (a || d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma decomp {n : ℕ} (i : Fin n) : ∀ (φ : DMFormula n), cnt i φ = 1 →
    ∃ (pol : Bool) (A B : (Fin n → Bool) → Bool),
      (∀ x, φ.eval x = (((if pol = true then x i else !(x i)) && A x) || B x)) ∧
      (∀ x y, (∀ j, j ≠ i → x j = y j) → A x = A y) ∧
      (∀ x y, (∀ j, j ≠ i → x j = y j) → B x = B y) ∧
      (∀ j, cnt j φ = 0 → (∀ x y, (∀ k, k ≠ j → x k = y k) → A x = A y) ∧
                           (∀ x y, (∀ k, k ≠ j → x k = y k) → B x = B y)) := by
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
    · intro j hj
      exact ⟨fun x y _ => rfl, fun x y _ => rfl⟩
  | and φ1 φ2 ih1 ih2 =>
    intro h
    have h' : cnt i φ1 + cnt i φ2 = 1 := h
    have hcases : (cnt i φ1 = 1 ∧ cnt i φ2 = 0) ∨ (cnt i φ1 = 0 ∧ cnt i φ2 = 1) := by
      omega
    rcases hcases with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
    · obtain ⟨pol, A1, B1, hev1, hA1, hB1, hf1⟩ := ih1 hc1
      have hfree2 : ∀ j, cnt j φ2 = 0 → ∀ x y, (∀ k, k ≠ j → x k = y k) → φ2.eval x = φ2.eval y :=
        fun j hj x y hxy => eval_congr_free j φ2 hj hxy
      refine ⟨pol, fun x => A1 x && φ2.eval x, fun x => B1 x && φ2.eval x, ?_, ?_, ?_, ?_⟩
      · intro x
        simp [DMFormula.eval, hev1 x, or_and, Bool.and_assoc]
      · intro x y hxy
        simp [hA1 x y hxy, hfree2 i hc2 x y hxy]
      · intro x y hxy
        simp [hB1 x y hxy, hfree2 i hc2 x y hxy]
      · intro j hj
        have hj' : cnt j φ1 + cnt j φ2 = 0 := hj
        have hj1 : cnt j φ1 = 0 := by omega
        have hj2 : cnt j φ2 = 0 := by omega
        obtain ⟨hA1j, hB1j⟩ := hf1 j hj1
        constructor
        · intro x y hxy
          simp [hA1j x y hxy, hfree2 j hj2 x y hxy]
        · intro x y hxy
          simp [hB1j x y hxy, hfree2 j hj2 x y hxy]
    · obtain ⟨pol, A2, B2, hev2, hA2, hB2, hf2⟩ := ih2 hc2
      have hfree1 : ∀ j, cnt j φ1 = 0 → ∀ x y, (∀ k, k ≠ j → x k = y k) → φ1.eval x = φ1.eval y :=
        fun j hj x y hxy => eval_congr_free j φ1 hj hxy
      refine ⟨pol, fun x => φ1.eval x && A2 x, fun x => φ1.eval x && B2 x, ?_, ?_, ?_, ?_⟩
      · intro x
        simp [DMFormula.eval, hev2 x, or_and, and_or', Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
      · intro x y hxy
        simp [hfree1 i hc1 x y hxy, hA2 x y hxy]
      · intro x y hxy
        simp [hfree1 i hc1 x y hxy, hB2 x y hxy]
      · intro j hj
        have hj' : cnt j φ1 + cnt j φ2 = 0 := hj
        have hj1 : cnt j φ1 = 0 := by omega
        have hj2 : cnt j φ2 = 0 := by omega
        obtain ⟨hA2j, hB2j⟩ := hf2 j hj2
        constructor
        · intro x y hxy
          simp [hfree1 j hj1 x y hxy, hA2j x y hxy]
        · intro x y hxy
          simp [hfree1 j hj1 x y hxy, hB2j x y hxy]
  | or φ1 φ2 ih1 ih2 =>
    intro h
    have h' : cnt i φ1 + cnt i φ2 = 1 := h
    have hcases : (cnt i φ1 = 1 ∧ cnt i φ2 = 0) ∨ (cnt i φ1 = 0 ∧ cnt i φ2 = 1) := by
      omega
    rcases hcases with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
    · obtain ⟨pol, A1, B1, hev1, hA1, hB1, hf1⟩ := ih1 hc1
      have hfree2 : ∀ j, cnt j φ2 = 0 → ∀ x y, (∀ k, k ≠ j → x k = y k) → φ2.eval x = φ2.eval y :=
        fun j hj x y hxy => eval_congr_free j φ2 hj hxy
      refine ⟨pol, A1, fun x => B1 x || φ2.eval x, ?_, ?_, ?_, ?_⟩
      · intro x
        simp [DMFormula.eval, hev1 x, Bool.or_assoc]
      · exact hA1
      · intro x y hxy
        simp [hB1 x y hxy, hfree2 i hc2 x y hxy]
      · intro j hj
        have hj' : cnt j φ1 + cnt j φ2 = 0 := hj
        have hj1 : cnt j φ1 = 0 := by omega
        have hj2 : cnt j φ2 = 0 := by omega
        obtain ⟨hA1j, hB1j⟩ := hf1 j hj1
        constructor
        · exact hA1j
        · intro x y hxy
          simp [hB1j x y hxy, hfree2 j hj2 x y hxy]
    · obtain ⟨pol, A2, B2, hev2, hA2, hB2, hf2⟩ := ih2 hc2
      have hfree1 : ∀ j, cnt j φ1 = 0 → ∀ x y, (∀ k, k ≠ j → x k = y k) → φ1.eval x = φ1.eval y :=
        fun j hj x y hxy => eval_congr_free j φ1 hj hxy
      refine ⟨pol, A2, fun x => φ1.eval x || B2 x, ?_, ?_, ?_, ?_⟩
      · intro x
        simp [DMFormula.eval, hev2 x, or_or', Bool.or_assoc]
      · exact hA2
      · intro x y hxy
        simp [hfree1 i hc1 x y hxy, hB2 x y hxy]
      · intro j hj
        have hj' : cnt j φ1 + cnt j φ2 = 0 := hj
        have hj1 : cnt j φ1 = 0 := by omega
        have hj2 : cnt j φ2 = 0 := by omega
        obtain ⟨hA2j, hB2j⟩ := hf2 j hj2
        constructor
        · exact hA2j
        · intro x y hxy
          simp [hfree1 j hj1 x y hxy, hB2j x y hxy]


private lemma nope_and : ∀ (l1 A10 A11 B10 B11 l2 A20 A21 B20 B21 : Bool),
    ¬ (∀ y : Fin 3 → Bool,
      (((((if l1 = true then y 0 else !(y 0)) && (if y 2 = true then A11 else A10)) || (if y 2 = true then B11 else B10)) &&
       (((if l2 = true then y 1 else !(y 1)) && (if y 2 = true then A21 else A20)) || (if y 2 = true then B21 else B20)))) =
      ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 0))) := by
  decide

private lemma nope_or : ∀ (l1 A10 A11 B10 B11 l2 A20 A21 B20 B21 : Bool),
    ¬ (∀ y : Fin 3 → Bool,
      (((((if l1 = true then y 0 else !(y 0)) && (if y 2 = true then A11 else A10)) || (if y 2 = true then B11 else B10)) ||
       (((if l2 = true then y 1 else !(y 1)) && (if y 2 = true then A21 else A20)) || (if y 2 = true then B21 else B20)))) =
      ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 0))) := by
  decide

private def xm {n : ℕ} (a b c : Fin n) (y : Fin 3 → Bool) : Fin n → Bool :=
  fun j => if j = a then y 0 else if j = b then y 1 else if j = c then y 2 else false

private def t3 (y : Fin 3 → Bool) : Bool := (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 0)

private def y00 : Fin 3 → Bool := fun _ => false
private def y01 : Fin 3 → Bool := fun i => if i = 2 then true else false
private def y10 : Fin 3 → Bool := fun i => if i = 0 then true else if i = 1 then true else false
private def y11 : Fin 3 → Bool := fun _ => true

private lemma upd_same' {n : ℕ} {i : Fin n} (x : Fin n → Bool) (b : Bool) :
    (Function.update x i b) i = b := Function.update_self _ _ _

private lemma upd_ne' {n : ℕ} {i j : Fin n} (h : j ≠ i) (x : Fin n → Bool) (b : Bool) :
    (Function.update x i b) j = x j := by
  rw [Function.update_apply, if_neg h]

private lemma free_two {n : ℕ} {a b : Fin n} (F : (Fin n → Bool) → Bool)
    (hFa : ∀ x y, (∀ k, k ≠ a → x k = y k) → F x = F y)
    (hFb : ∀ x y, (∀ k, k ≠ b → x k = y k) → F x = F y)
    {x y : Fin n → Bool} (hxy : ∀ k, k ≠ a → k ≠ b → x k = y k) : F x = F y := by
  have s1 : F x = F (Function.update x b (y b)) :=
    hFb x _ (fun k hk => (upd_ne' hk x (y b)).symm)
  have s2 : F (Function.update x b (y b)) = F y :=
    hFa _ y (fun k hk => by
      by_cases hkb : k = b
      · rw [hkb, upd_same']
      · rw [upd_ne' hkb, hxy k hk hkb])
  rw [s1, s2]

private lemma cval {n : ℕ} (a b c : Fin n) (F : (Fin n → Bool) → Bool)
    (hFa : ∀ x y, (∀ k, k ≠ a → x k = y k) → F x = F y)
    (hFb : ∀ x y, (∀ k, k ≠ b → x k = y k) → F x = F y)
    (y : Fin 3 → Bool) :
    F (xm a b c y) = (if y 2 = true then F (xm a b c y01) else F (xm a b c y00)) := by
  have h2 := free_two F hFa hFb (x := xm a b c y)
    (y := xm a b c (if y 2 = true then y01 else y00)) (by
      intro k hk1 hk2
      by_cases hka : k = a
      · exact absurd hka hk1
      · by_cases hkb : k = b
        · exact absurd hkb hk2
        · by_cases hy : y 2 = true
          · simp [xm, hka, hkb, y00, y01, hy]
          · simp [xm, hka, hkb, y00, y01, hy])
  rw [h2]
  split_ifs <;> rfl

private lemma Q {n : ℕ} {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (ψ : DMFormula n), cnt a ψ = 1 → cnt b ψ = 1 →
      ¬ (∀ y : Fin 3 → Bool, ψ.eval (xm a b c y) = t3 y) := by
  intro ψ
  induction ψ with
  | lit j pol =>
    intro hA hB
    have h0 : (if j = a then 1 else 0) = 1 := hA
    have hja : j = a := by
      by_contra hne
      rw [if_neg hne] at h0
      exact absurd h0 (by simp)
    have h1 : (if a = b then 1 else 0) = 0 := by rw [if_neg hab]
    have hB' : (if a = b then 1 else 0) = 1 := by rw [← hja]; exact hB
    rw [h1] at hB'
    exact absurd hB' (by simp)
  | and ψ1 ψ2 ih1 ih2 =>
    intro hA hB
    by_contra hR
    have hA' : cnt a ψ1 + cnt a ψ2 = 1 := hA
    have hB' : cnt b ψ1 + cnt b ψ2 = 1 := hB
    have hR' : ∀ y : Fin 3 → Bool, (ψ1.eval (xm a b c y) && ψ2.eval (xm a b c y)) = t3 y := by
      intro y
      exact hR y
    rcases (by omega : (cnt a ψ1 = 1 ∧ cnt a ψ2 = 0) ∨ (cnt a ψ1 = 0 ∧ cnt a ψ2 = 1)) with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
    · rcases (by omega : (cnt b ψ1 = 1 ∧ cnt b ψ2 = 0) ∨ (cnt b ψ1 = 0 ∧ cnt b ψ2 = 1)) with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
      · -- ψ1 has both leaves, ψ2 has none
        have hR2 := cval a b c ψ2.eval (fun x y h => eval_congr_free a ψ2 ha2 h)
          (fun x y h => eval_congr_free b ψ2 hb2 h)
        have e10 : (ψ1.eval (xm a b c y10) && ψ2.eval (xm a b c y10)) = true := by
          rw [hR' y10]; decide
        have e11 : (ψ1.eval (xm a b c y11) && ψ2.eval (xm a b c y11)) = true := by
          rw [hR' y11]; decide
        have hr0 : ψ2.eval (xm a b c y00) = true := by
          have h := e10
          rw [hR2 y10, if_neg (by decide : ¬(y10 2 = true))] at h
          exact (Bool.and_eq_true_iff.mp h).2
        have hr1 : ψ2.eval (xm a b c y01) = true := by
          have h := e11
          rw [hR2 y11, if_pos (by decide : y11 2 = true)] at h
          exact (Bool.and_eq_true_iff.mp h).2
        have hR1 : ∀ y : Fin 3 → Bool, ψ1.eval (xm a b c y) = t3 y := by
          intro y
          have h := hR' y
          rw [hR2 y] at h
          rcases Bool.eq_false_or_eq_true (y 2) with hy | hy
          · rw [if_pos hy, hr1] at h
            simp only [Bool.and_true] at h
            exact h
          · rw [if_neg (by rw [hy]; decide), hr0] at h
            simp only [Bool.and_true] at h
            exact h
        exact ih1 ha1 hb1 hR1
      · -- ψ1 has a-leaf only, ψ2 has b-leaf only
        obtain ⟨pol1, A1, B1, hev1, hA1f, hB1f, hf1⟩ := decomp a ψ1 ha1
        obtain ⟨pol2, A2, B2, hev2, hA2f, hB2f, hf2⟩ := decomp b ψ2 hb2
        obtain ⟨hA1b, hB1b⟩ := hf1 b hb1
        obtain ⟨hA2a, hB2a⟩ := hf2 a ha2
        have hA1c := cval a b c A1 hA1f hA1b
        have hB1c := cval a b c B1 hB1f hB1b
        have hA2c := cval a b c A2 hA2a hA2f
        have hB2c := cval a b c B2 hB2a hB2f
        have hxa : ∀ y : Fin 3 → Bool, (xm a b c y) a = y 0 := by intro y; simp [xm]
        have hxb : ∀ y : Fin 3 → Bool, (xm a b c y) b = y 1 := by intro y; simp [xm, Ne.symm hab]
        have hc1 : ∀ y : Fin 3 → Bool, ψ1.eval (xm a b c y) =
            ((((if pol1 = true then y 0 else !(y 0)) && (if y 2 = true then A1 (xm a b c y01) else A1 (xm a b c y00))) ||
              (if y 2 = true then B1 (xm a b c y01) else B1 (xm a b c y00)))) := by
          intro y
          rw [hev1 (xm a b c y), hxa y, hA1c y, hB1c y]
        have hc2 : ∀ y : Fin 3 → Bool, ψ2.eval (xm a b c y) =
            ((((if pol2 = true then y 1 else !(y 1)) && (if y 2 = true then A2 (xm a b c y01) else A2 (xm a b c y00))) ||
              (if y 2 = true then B2 (xm a b c y01) else B2 (xm a b c y00)))) := by
          intro y
          rw [hev2 (xm a b c y), hxb y, hA2c y, hB2c y]
        exact nope_and pol1 (A1 (xm a b c y00)) (A1 (xm a b c y01)) (B1 (xm a b c y00)) (B1 (xm a b c y01))
          pol2 (A2 (xm a b c y00)) (A2 (xm a b c y01)) (B2 (xm a b c y00)) (B2 (xm a b c y01))
          (fun y => by rw [← hc1 y, ← hc2 y]; exact hR' y)
    · rcases (by omega : (cnt b ψ1 = 1 ∧ cnt b ψ2 = 0) ∨ (cnt b ψ1 = 0 ∧ cnt b ψ2 = 1)) with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
      · -- ψ1 has b-leaf only, ψ2 has a-leaf only: swap sides
        obtain ⟨pol2, A2, B2, hev2, hA2f, hB2f, hf2⟩ := decomp a ψ2 ha2
        obtain ⟨pol1, A1, B1, hev1, hA1f, hB1f, hf1⟩ := decomp b ψ1 hb1
        obtain ⟨hA2b, hB2b⟩ := hf2 b hb2
        obtain ⟨hA1a, hB1a⟩ := hf1 a ha1
        have hA2c := cval a b c A2 hA2f hA2b
        have hB2c := cval a b c B2 hB2f hB2b
        have hA1c := cval a b c A1 hA1a hA1f
        have hB1c := cval a b c B1 hB1a hB1f
        have hxa : ∀ y : Fin 3 → Bool, (xm a b c y) a = y 0 := by intro y; simp [xm]
        have hxb : ∀ y : Fin 3 → Bool, (xm a b c y) b = y 1 := by intro y; simp [xm, Ne.symm hab]
        have hc2 : ∀ y : Fin 3 → Bool, ψ2.eval (xm a b c y) =
            ((((if pol2 = true then y 0 else !(y 0)) && (if y 2 = true then A2 (xm a b c y01) else A2 (xm a b c y00))) ||
              (if y 2 = true then B2 (xm a b c y01) else B2 (xm a b c y00)))) := by
          intro y
          rw [hev2 (xm a b c y), hxa y, hA2c y, hB2c y]
        have hc1 : ∀ y : Fin 3 → Bool, ψ1.eval (xm a b c y) =
            ((((if pol1 = true then y 1 else !(y 1)) && (if y 2 = true then A1 (xm a b c y01) else A1 (xm a b c y00))) ||
              (if y 2 = true then B1 (xm a b c y01) else B1 (xm a b c y00)))) := by
          intro y
          rw [hev1 (xm a b c y), hxb y, hA1c y, hB1c y]
        refine nope_and pol2 (A2 (xm a b c y00)) (A2 (xm a b c y01)) (B2 (xm a b c y00)) (B2 (xm a b c y01))
          pol1 (A1 (xm a b c y00)) (A1 (xm a b c y01)) (B1 (xm a b c y00)) (B1 (xm a b c y01)) (fun y => ?_)
        rw [← hc2 y, ← hc1 y, Bool.and_comm]
        exact hR' y
      · -- ψ1 has none, ψ2 has both
        have hR1 := cval a b c ψ1.eval (fun x y h => eval_congr_free a ψ1 ha1 h)
          (fun x y h => eval_congr_free b ψ1 hb1 h)
        have e10 : (ψ1.eval (xm a b c y10) && ψ2.eval (xm a b c y10)) = true := by
          rw [hR' y10]; decide
        have e11 : (ψ1.eval (xm a b c y11) && ψ2.eval (xm a b c y11)) = true := by
          rw [hR' y11]; decide
        have hr0 : ψ1.eval (xm a b c y00) = true := by
          have h := e10
          rw [hR1 y10, if_neg (by decide : ¬(y10 2 = true))] at h
          exact (Bool.and_eq_true_iff.mp h).1
        have hr1 : ψ1.eval (xm a b c y01) = true := by
          have h := e11
          rw [hR1 y11, if_pos (by decide : y11 2 = true)] at h
          exact (Bool.and_eq_true_iff.mp h).1
        have hR2 : ∀ y : Fin 3 → Bool, ψ2.eval (xm a b c y) = t3 y := by
          intro y
          have h := hR' y
          rw [hR1 y] at h
          rcases Bool.eq_false_or_eq_true (y 2) with hy | hy
          · rw [if_pos hy, hr1] at h
            simp only [Bool.true_and] at h
            exact h
          · rw [if_neg (by rw [hy]; decide), hr0] at h
            simp only [Bool.true_and] at h
            exact h
        exact ih2 ha2 hb2 hR2
  | or ψ1 ψ2 ih1 ih2 =>
    intro hA hB
    by_contra hR
    have hA' : cnt a ψ1 + cnt a ψ2 = 1 := hA
    have hB' : cnt b ψ1 + cnt b ψ2 = 1 := hB
    have hR' : ∀ y : Fin 3 → Bool, (ψ1.eval (xm a b c y) || ψ2.eval (xm a b c y)) = t3 y := by
      intro y
      exact hR y
    rcases (by omega : (cnt a ψ1 = 1 ∧ cnt a ψ2 = 0) ∨ (cnt a ψ1 = 0 ∧ cnt a ψ2 = 1)) with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
    · rcases (by omega : (cnt b ψ1 = 1 ∧ cnt b ψ2 = 0) ∨ (cnt b ψ1 = 0 ∧ cnt b ψ2 = 1)) with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
      · -- ψ1 both, ψ2 none; OR: R2 ≡ false
        have hR2 := cval a b c ψ2.eval (fun x y h => eval_congr_free a ψ2 ha2 h)
          (fun x y h => eval_congr_free b ψ2 hb2 h)
        have e00 : (ψ1.eval (xm a b c y00) || ψ2.eval (xm a b c y00)) = false := by
          rw [hR' y00]; decide
        have e01 : (ψ1.eval (xm a b c y01) || ψ2.eval (xm a b c y01)) = false := by
          rw [hR' y01]; decide
        have hr0 : ψ2.eval (xm a b c y00) = false := by
          have h := e00
          rw [hR2 y00, if_neg (by decide : ¬(y00 2 = true))] at h
          exact (Bool.or_eq_false_iff.mp h).2
        have hr1 : ψ2.eval (xm a b c y01) = false := by
          have h := e01
          rw [hR2 y01, if_pos (by decide : y01 2 = true)] at h
          exact (Bool.or_eq_false_iff.mp h).2
        have hR1 : ∀ y : Fin 3 → Bool, ψ1.eval (xm a b c y) = t3 y := by
          intro y
          have h := hR' y
          rw [hR2 y] at h
          rcases Bool.eq_false_or_eq_true (y 2) with hy | hy
          · rw [if_pos hy, hr1] at h
            simp only [Bool.or_false] at h
            exact h
          · rw [if_neg (by rw [hy]; decide), hr0] at h
            simp only [Bool.or_false] at h
            exact h
        exact ih1 ha1 hb1 hR1
      · -- ψ1 a-only, ψ2 b-only; OR
        obtain ⟨pol1, A1, B1, hev1, hA1f, hB1f, hf1⟩ := decomp a ψ1 ha1
        obtain ⟨pol2, A2, B2, hev2, hA2f, hB2f, hf2⟩ := decomp b ψ2 hb2
        obtain ⟨hA1b, hB1b⟩ := hf1 b hb1
        obtain ⟨hA2a, hB2a⟩ := hf2 a ha2
        have hA1c := cval a b c A1 hA1f hA1b
        have hB1c := cval a b c B1 hB1f hB1b
        have hA2c := cval a b c A2 hA2a hA2f
        have hB2c := cval a b c B2 hB2a hB2f
        have hxa : ∀ y : Fin 3 → Bool, (xm a b c y) a = y 0 := by intro y; simp [xm]
        have hxb : ∀ y : Fin 3 → Bool, (xm a b c y) b = y 1 := by intro y; simp [xm, Ne.symm hab]
        have hc1 : ∀ y : Fin 3 → Bool, ψ1.eval (xm a b c y) =
            ((((if pol1 = true then y 0 else !(y 0)) && (if y 2 = true then A1 (xm a b c y01) else A1 (xm a b c y00))) ||
              (if y 2 = true then B1 (xm a b c y01) else B1 (xm a b c y00)))) := by
          intro y
          rw [hev1 (xm a b c y), hxa y, hA1c y, hB1c y]
        have hc2 : ∀ y : Fin 3 → Bool, ψ2.eval (xm a b c y) =
            ((((if pol2 = true then y 1 else !(y 1)) && (if y 2 = true then A2 (xm a b c y01) else A2 (xm a b c y00))) ||
              (if y 2 = true then B2 (xm a b c y01) else B2 (xm a b c y00)))) := by
          intro y
          rw [hev2 (xm a b c y), hxb y, hA2c y, hB2c y]
        exact nope_or pol1 (A1 (xm a b c y00)) (A1 (xm a b c y01)) (B1 (xm a b c y00)) (B1 (xm a b c y01))
          pol2 (A2 (xm a b c y00)) (A2 (xm a b c y01)) (B2 (xm a b c y00)) (B2 (xm a b c y01))
          (fun y => by rw [← hc1 y, ← hc2 y]; exact hR' y)
    · rcases (by omega : (cnt b ψ1 = 1 ∧ cnt b ψ2 = 0) ∨ (cnt b ψ1 = 0 ∧ cnt b ψ2 = 1)) with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
      · -- ψ1 b-only, ψ2 a-only; OR swapped
        obtain ⟨pol2, A2, B2, hev2, hA2f, hB2f, hf2⟩ := decomp a ψ2 ha2
        obtain ⟨pol1, A1, B1, hev1, hA1f, hB1f, hf1⟩ := decomp b ψ1 hb1
        obtain ⟨hA2b, hB2b⟩ := hf2 b hb2
        obtain ⟨hA1a, hB1a⟩ := hf1 a ha1
        have hA2c := cval a b c A2 hA2f hA2b
        have hB2c := cval a b c B2 hB2f hB2b
        have hA1c := cval a b c A1 hA1a hA1f
        have hB1c := cval a b c B1 hB1a hB1f
        have hxa : ∀ y : Fin 3 → Bool, (xm a b c y) a = y 0 := by intro y; simp [xm]
        have hxb : ∀ y : Fin 3 → Bool, (xm a b c y) b = y 1 := by intro y; simp [xm, Ne.symm hab]
        have hc2 : ∀ y : Fin 3 → Bool, ψ2.eval (xm a b c y) =
            ((((if pol2 = true then y 0 else !(y 0)) && (if y 2 = true then A2 (xm a b c y01) else A2 (xm a b c y00))) ||
              (if y 2 = true then B2 (xm a b c y01) else B2 (xm a b c y00)))) := by
          intro y
          rw [hev2 (xm a b c y), hxa y, hA2c y, hB2c y]
        have hc1 : ∀ y : Fin 3 → Bool, ψ1.eval (xm a b c y) =
            ((((if pol1 = true then y 1 else !(y 1)) && (if y 2 = true then A1 (xm a b c y01) else A1 (xm a b c y00))) ||
              (if y 2 = true then B1 (xm a b c y01) else B1 (xm a b c y00)))) := by
          intro y
          rw [hev1 (xm a b c y), hxb y, hA1c y, hB1c y]
        refine nope_or pol2 (A2 (xm a b c y00)) (A2 (xm a b c y01)) (B2 (xm a b c y00)) (B2 (xm a b c y01))
          pol1 (A1 (xm a b c y00)) (A1 (xm a b c y01)) (B1 (xm a b c y00)) (B1 (xm a b c y01)) (fun y => ?_)
        rw [← hc2 y, ← hc1 y, Bool.or_comm]
        exact hR' y
      · -- ψ1 none, ψ2 both; OR
        have hR1 := cval a b c ψ1.eval (fun x y h => eval_congr_free a ψ1 ha1 h)
          (fun x y h => eval_congr_free b ψ1 hb1 h)
        have e00 : (ψ1.eval (xm a b c y00) || ψ2.eval (xm a b c y00)) = false := by
          rw [hR' y00]; decide
        have e01 : (ψ1.eval (xm a b c y01) || ψ2.eval (xm a b c y01)) = false := by
          rw [hR' y01]; decide
        have hr0 : ψ1.eval (xm a b c y00) = false := by
          have h := e00
          rw [hR1 y00, if_neg (by decide : ¬(y00 2 = true))] at h
          exact (Bool.or_eq_false_iff.mp h).1
        have hr1 : ψ1.eval (xm a b c y01) = false := by
          have h := e01
          rw [hR1 y01, if_pos (by decide : y01 2 = true)] at h
          exact (Bool.or_eq_false_iff.mp h).1
        have hR2 : ∀ y : Fin 3 → Bool, ψ2.eval (xm a b c y) = t3 y := by
          intro y
          have h := hR' y
          rw [hR1 y] at h
          rcases Bool.eq_false_or_eq_true (y 2) with hy | hy
          · rw [if_pos hy, hr1] at h
            simp only [Bool.false_or] at h
            exact h
          · rw [if_neg (by rw [hy]; decide), hr0] at h
            simp only [Bool.false_or] at h
            exact h
        exact ih2 ha2 hb2 hR2

end PEqualNP.Outside.L_meta_259

open PEqualNP.Outside.L_meta_259

theorem PEqualNP.Outside.L_meta_259 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (a b c : Fin n), a ≠ b → b ≠ c → a ≠ c → (∀ x : Fin n → Bool, φ.eval x = f x) → (∀ x : Fin n → Bool, (∀ j : Fin n, j ≠ a → j ≠ b → j ≠ c → x j = false) → f x = (x a && x b || x b && x c || x c && x a)) → 3 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = a then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ + PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = b then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ := by
  intro n f φ a b c hab hbc hac hev hrest
  show 3 ≤ cnt a φ + cnt b φ
  have hxma : ∀ y : Fin 3 → Bool, xm a b c y a = y 0 := by intro y; simp [xm]
  have hxmb : ∀ y : Fin 3 → Bool, xm a b c y b = y 1 := by intro y; simp [xm, Ne.symm hab]
  have hxmc : ∀ y : Fin 3 → Bool, xm a b c y c = y 2 := by intro y; simp [xm, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
  have hR : ∀ y : Fin 3 → Bool, φ.eval (xm a b c y) = t3 y := by
    intro y
    rw [hev (xm a b c y), hrest (xm a b c y) (by
      intro j hj1 hj2 hj3
      show (if j = a then y 0 else if j = b then y 1 else if j = c then y 2 else false) = false
      rw [if_neg hj1, if_neg hj2, if_neg hj3])]
    rw [hxma y, hxmb y, hxmc y]
    rfl
  have hA1 : 1 ≤ cnt a φ := by
    by_contra h
    have h0 : cnt a φ = 0 := by omega
    have hf0 : f (fun j => if j = b then true else false) = false := by
      rw [hrest (fun j => if j = b then true else false) (by
        intro j hj1 hj2 hj3
        show (if j = b then true else false) = false
        rw [if_neg hj2])]
      simp [hab, Ne.symm hbc]
    have hf1 : f (Function.update (fun j => if j = b then true else false) a true) = true := by
      rw [hrest (Function.update (fun j => if j = b then true else false) a true) (by
        intro j hj1 hj2 hj3
        rw [upd_ne' hj1]
        show (if j = b then true else false) = false
        rw [if_neg hj2])]
      simp [upd_same', upd_ne' hab.symm, upd_ne' hac.symm, hab, Ne.symm hbc]
    have hEq := eval_congr_free a φ h0 (x := fun j => if j = b then true else false)
      (y := Function.update (fun j => if j = b then true else false) a true)
      (fun j hj => (upd_ne' hj (fun j => if j = b then true else false) true).symm)
    rw [hev, hev] at hEq
    rw [hf0, hf1] at hEq
    exact absurd hEq (by simp)
  have hB1 : 1 ≤ cnt b φ := by
    by_contra h
    have h0 : cnt b φ = 0 := by omega
    have hf0 : f (fun j => if j = a then true else false) = false := by
      rw [hrest (fun j => if j = a then true else false) (by
        intro j hj1 hj2 hj3
        show (if j = a then true else false) = false
        rw [if_neg hj1])]
      simp [Ne.symm hab, Ne.symm hac]
    have hf1 : f (Function.update (fun j => if j = a then true else false) b true) = true := by
      rw [hrest (Function.update (fun j => if j = a then true else false) b true) (by
        intro j hj1 hj2 hj3
        rw [upd_ne' hj2]
        show (if j = a then true else false) = false
        rw [if_neg hj1])]
      simp [upd_same', upd_ne' hab, upd_ne' hbc, Ne.symm hab, Ne.symm hac]
    have hEq := eval_congr_free b φ h0 (x := fun j => if j = a then true else false)
      (y := Function.update (fun j => if j = a then true else false) b true)
      (fun j hj => (upd_ne' hj (fun j => if j = a then true else false) true).symm)
    rw [hev, hev] at hEq
    rw [hf0, hf1] at hEq
    exact absurd hEq (by simp)
  by_contra hle
  have hA : cnt a φ = 1 := by omega
  have hB : cnt b φ = 1 := by omega
  exact Q hab hac hbc φ hA hB hR
