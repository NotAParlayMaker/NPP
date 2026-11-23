import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_258

open PEqualNP.MetaComplexity

noncomputable def cnt {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

noncomputable def negc {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

noncomputable def posc {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun (j : Fin n) (c : Bool) => if j = i ∧ c = true then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

lemma cnt_lit {n : ℕ} (i j : Fin n) (b : Bool) :
    cnt i (DMFormula.lit j b) = if j = i then 1 else 0 := rfl

lemma cnt_and {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    cnt i (DMFormula.and φ ψ) = cnt i φ + cnt i ψ := rfl

lemma cnt_or {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    cnt i (DMFormula.or φ ψ) = cnt i φ + cnt i ψ := rfl

lemma negc_lit {n : ℕ} (i j : Fin n) (b : Bool) :
    negc i (DMFormula.lit j b) = if j = i ∧ b = false then 1 else 0 := rfl

lemma negc_and {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    negc i (DMFormula.and φ ψ) = negc i φ + negc i ψ := rfl

lemma negc_or {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    negc i (DMFormula.or φ ψ) = negc i φ + negc i ψ := rfl

lemma posc_lit {n : ℕ} (i j : Fin n) (b : Bool) :
    posc i (DMFormula.lit j b) = if j = i ∧ b = true then 1 else 0 := rfl

lemma posc_and {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    posc i (DMFormula.and φ ψ) = posc i φ + posc i ψ := rfl

lemma posc_or {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    posc i (DMFormula.or φ ψ) = posc i φ + posc i ψ := rfl

lemma cnt_split {n : ℕ} (i : Fin n) (φ : DMFormula n) : cnt i φ = posc i φ + negc i φ := by
  induction φ with
  | lit j b =>
    rw [cnt_lit, posc_lit, negc_lit]
    by_cases h : j = i <;> cases b <;> simp [h]
  | and φ ψ ih1 ih2 =>
    rw [cnt_and, posc_and, negc_and, ih1, ih2]
    omega
  | or φ ψ ih1 ih2 =>
    rw [cnt_or, posc_or, negc_or, ih1, ih2]
    omega

lemma leaves_pos {n : ℕ} (φ : DMFormula n) : 1 ≤ φ.leaves := by
  induction φ with
  | lit j b => simp [DMFormula.leaves]
  | and φ ψ ih1 ih2 =>
    simp only [DMFormula.leaves]
    omega
  | or φ ψ ih1 ih2 =>
    simp only [DMFormula.leaves]
    omega

def ev {n : ℕ} (i : Fin n) : DMFormula n → (Fin n → Bool) → Bool → Bool → Bool
  | DMFormula.lit j b, x, p, q =>
    if j = i then (if b then p else q) else (if b then x j else !x j)
  | DMFormula.and φ ψ, x, p, q => ev i φ x p q && ev i ψ x p q
  | DMFormula.or φ ψ, x, p, q => ev i φ x p q || ev i ψ x p q

lemma ev_eval {n : ℕ} (i : Fin n) (φ : DMFormula n) (x : Fin n → Bool) :
    ev i φ x (x i) (!x i) = φ.eval x := by
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · subst h
      simp [ev, DMFormula.eval]
    · simp [ev, DMFormula.eval, h]
  | and φ ψ ih1 ih2 => simp only [ev, DMFormula.eval, ih1, ih2]
  | or φ ψ ih1 ih2 => simp only [ev, DMFormula.eval, ih1, ih2]

lemma ev_update {n : ℕ} (i : Fin n) (φ : DMFormula n) (x : Fin n → Bool) (v p q : Bool) :
    ev i φ (Function.update x i v) p q = ev i φ x p q := by
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · simp [ev, h]
    · simp [ev, h]
  | and φ ψ ih1 ih2 => simp only [ev, ih1, ih2]
  | or φ ψ ih1 ih2 => simp only [ev, ih1, ih2]

lemma ev_mono {n : ℕ} (i : Fin n) (φ : DMFormula n) (x : Fin n → Bool) (p q p' q' : Bool)
    (hp : p = true → p' = true) (hq : q = true → q' = true) :
    ev i φ x p q = true → ev i φ x p' q' = true := by
  induction φ with
  | lit j b =>
    by_cases h : j = i
    · cases b <;> simp only [ev, h, ↓reduceIte, Bool.false_eq_true]
      · exact hq
      · exact hp
    · simp only [ev, h, ↓reduceIte]
      exact fun h' => h'
  | and φ ψ ih1 ih2 =>
    simp only [ev, Bool.and_eq_true]
    exact fun h => ⟨ih1 h.1, ih2 h.2⟩
  | or φ ψ ih1 ih2 =>
    simp only [ev, Bool.or_eq_true]
    exact fun h => h.elim (fun h => Or.inl (ih1 h)) (fun h => Or.inr (ih2 h))

lemma ev_nopos {n : ℕ} (i : Fin n) (φ : DMFormula n) (x : Fin n → Bool) (p p' q : Bool)
    (h0 : posc i φ = 0) : ev i φ x p q = ev i φ x p' q := by
  induction φ with
  | lit j b =>
    rw [posc_lit] at h0
    by_cases h : j = i
    · cases b
      · simp [ev, h]
      · simp [h] at h0
    · simp [ev, h]
  | and φ ψ ih1 ih2 =>
    rw [posc_and] at h0
    simp only [ev, ih1 (by omega), ih2 (by omega)]
  | or φ ψ ih1 ih2 =>
    rw [posc_or] at h0
    simp only [ev, ih1 (by omega), ih2 (by omega)]

lemma ev_noneg {n : ℕ} (i : Fin n) (φ : DMFormula n) (x : Fin n → Bool) (p q q' : Bool)
    (h0 : negc i φ = 0) : ev i φ x p q = ev i φ x p q' := by
  induction φ with
  | lit j b =>
    rw [negc_lit] at h0
    by_cases h : j = i
    · cases b
      · simp [h] at h0
      · simp [ev, h]
    · simp [ev, h]
  | and φ ψ ih1 ih2 =>
    rw [negc_and] at h0
    simp only [ev, ih1 (by omega), ih2 (by omega)]
  | or φ ψ ih1 ih2 =>
    rw [negc_or] at h0
    simp only [ev, ih1 (by omega), ih2 (by omega)]

lemma bool_le (u v : Bool) : (u = true → v = true) ↔ (u && v) = u := by
  cases u <;> cases v <;> simp

lemma shape {n : ℕ} (i : Fin n) (φ : DMFormula n) (hp : posc i φ = 1) (hn : negc i φ = 1) :
    (∀ x : Fin n → Bool, ev i φ x true true = (ev i φ x true false || ev i φ x false true)) ∨
    (∀ x : Fin n → Bool, ev i φ x false false = (ev i φ x true false && ev i φ x false true)) := by
  induction φ with
  | lit j b =>
    rw [posc_lit] at hp
    rw [negc_lit] at hn
    by_cases h : j = i <;> cases b <;> simp [h] at hp hn
  | and φ ψ ih1 ih2 =>
    rw [posc_and] at hp
    rw [negc_and] at hn
    have c1 : (posc i φ = 1 ∧ negc i φ = 1 ∧ posc i ψ = 0 ∧ negc i ψ = 0) ∨
        (posc i φ = 0 ∧ negc i φ = 0 ∧ posc i ψ = 1 ∧ negc i ψ = 1) ∨
        (posc i φ = 1 ∧ negc i φ = 0 ∧ posc i ψ = 0 ∧ negc i ψ = 1) ∨
        (posc i φ = 0 ∧ negc i φ = 1 ∧ posc i ψ = 1 ∧ negc i ψ = 0) := by omega
    rcases c1 with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · have hs : ∀ x p q, ev i ψ x p q = ev i ψ x false false := fun x p q => by
        rw [ev_nopos i ψ x p false q a3, ev_noneg i ψ x false q false a4]
      rcases ih1 a1 a2 with h | h
      · left
        intro x
        simp only [ev, hs x true true, hs x true false, hs x false true, h x]
        cases ev i φ x true false <;> cases ev i φ x false true <;>
          cases ev i ψ x false false <;> rfl
      · right
        intro x
        simp only [ev, hs x true false, hs x false true, h x]
        cases ev i φ x true false <;> cases ev i φ x false true <;>
          cases ev i ψ x false false <;> rfl
    · have hs : ∀ x p q, ev i φ x p q = ev i φ x false false := fun x p q => by
        rw [ev_nopos i φ x p false q a1, ev_noneg i φ x false q false a2]
      rcases ih2 a3 a4 with h | h
      · left
        intro x
        simp only [ev, hs x true true, hs x true false, hs x false true, h x]
        cases ev i ψ x true false <;> cases ev i ψ x false true <;>
          cases ev i φ x false false <;> rfl
      · right
        intro x
        simp only [ev, hs x true false, hs x false true, h x]
        cases ev i ψ x true false <;> cases ev i ψ x false true <;>
          cases ev i φ x false false <;> rfl
    · right
      intro x
      have e1 : ∀ p q, ev i φ x p q = ev i φ x p false := fun p q => ev_noneg i φ x p q false a2
      have e2 : ∀ p q, ev i ψ x p q = ev i ψ x false q := fun p q => ev_nopos i ψ x p false q a3
      have m1 := (bool_le _ _).mp
        (ev_mono i φ x false false true false (fun h => absurd h (by simp)) (fun h => h))
      have m2 := (bool_le _ _).mp
        (ev_mono i ψ x false false false true (fun h => h) (fun h => absurd h (by simp)))
      simp only [ev, e1 false true, e2 true false]
      revert m1 m2
      cases ev i φ x true false <;> cases ev i φ x false false <;>
        cases ev i ψ x false true <;> cases ev i ψ x false false <;> simp
    · right
      intro x
      have e1 : ∀ p q, ev i φ x p q = ev i φ x false q := fun p q => ev_nopos i φ x p false q a1
      have e2 : ∀ p q, ev i ψ x p q = ev i ψ x p false := fun p q => ev_noneg i ψ x p q false a4
      have m1 := (bool_le _ _).mp
        (ev_mono i φ x false false false true (fun h => h) (fun h => absurd h (by simp)))
      have m2 := (bool_le _ _).mp
        (ev_mono i ψ x false false true false (fun h => absurd h (by simp)) (fun h => h))
      simp only [ev, e1 true false, e2 false true]
      revert m1 m2
      cases ev i φ x false true <;> cases ev i φ x false false <;>
        cases ev i ψ x true false <;> cases ev i ψ x false false <;> simp
  | or φ ψ ih1 ih2 =>
    rw [posc_or] at hp
    rw [negc_or] at hn
    have c1 : (posc i φ = 1 ∧ negc i φ = 1 ∧ posc i ψ = 0 ∧ negc i ψ = 0) ∨
        (posc i φ = 0 ∧ negc i φ = 0 ∧ posc i ψ = 1 ∧ negc i ψ = 1) ∨
        (posc i φ = 1 ∧ negc i φ = 0 ∧ posc i ψ = 0 ∧ negc i ψ = 1) ∨
        (posc i φ = 0 ∧ negc i φ = 1 ∧ posc i ψ = 1 ∧ negc i ψ = 0) := by omega
    rcases c1 with ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3, a4⟩
    · have hs : ∀ x p q, ev i ψ x p q = ev i ψ x false false := fun x p q => by
        rw [ev_nopos i ψ x p false q a3, ev_noneg i ψ x false q false a4]
      rcases ih1 a1 a2 with h | h
      · left
        intro x
        simp only [ev, hs x true true, hs x true false, hs x false true, h x]
        cases ev i φ x true false <;> cases ev i φ x false true <;>
          cases ev i ψ x false false <;> rfl
      · right
        intro x
        simp only [ev, hs x true false, hs x false true, h x]
        cases ev i φ x true false <;> cases ev i φ x false true <;>
          cases ev i ψ x false false <;> rfl
    · have hs : ∀ x p q, ev i φ x p q = ev i φ x false false := fun x p q => by
        rw [ev_nopos i φ x p false q a1, ev_noneg i φ x false q false a2]
      rcases ih2 a3 a4 with h | h
      · left
        intro x
        simp only [ev, hs x true true, hs x true false, hs x false true, h x]
        cases ev i ψ x true false <;> cases ev i ψ x false true <;>
          cases ev i φ x false false <;> rfl
      · right
        intro x
        simp only [ev, hs x true false, hs x false true, h x]
        cases ev i ψ x true false <;> cases ev i ψ x false true <;>
          cases ev i φ x false false <;> rfl
    · left
      intro x
      have e1 : ∀ p q, ev i φ x p q = ev i φ x p false := fun p q => ev_noneg i φ x p q false a2
      have e2 : ∀ p q, ev i ψ x p q = ev i ψ x false q := fun p q => ev_nopos i ψ x p false q a3
      have m1 := (bool_le _ _).mp
        (ev_mono i φ x false false true false (fun h => absurd h (by simp)) (fun h => h))
      have m2 := (bool_le _ _).mp
        (ev_mono i ψ x false false false true (fun h => h) (fun h => absurd h (by simp)))
      simp only [ev, e1 true true, e1 false true, e2 true true, e2 true false]
      revert m1 m2
      cases ev i φ x true false <;> cases ev i φ x false false <;>
        cases ev i ψ x false true <;> cases ev i ψ x false false <;> simp
    · left
      intro x
      have e1 : ∀ p q, ev i φ x p q = ev i φ x false q := fun p q => ev_nopos i φ x p false q a1
      have e2 : ∀ p q, ev i ψ x p q = ev i ψ x p false := fun p q => ev_noneg i ψ x p q false a4
      have m1 := (bool_le _ _).mp
        (ev_mono i φ x false false false true (fun h => h) (fun h => absurd h (by simp)))
      have m2 := (bool_le _ _).mp
        (ev_mono i ψ x false false true false (fun h => absurd h (by simp)) (fun h => h))
      simp only [ev, e1 true true, e1 true false, e2 true true, e2 false true]
      revert m1 m2
      cases ev i φ x false true <;> cases ev i φ x false false <;>
        cases ev i ψ x true false <;> cases ev i ψ x false false <;> simp

lemma ev_noneg_eval {n : ℕ} (i : Fin n) (φ : DMFormula n) (x : Fin n → Bool) (c : Bool)
    (h0 : negc i φ = 0) : ev i φ x (x i) c = φ.eval x := by
  rw [ev_noneg i φ x (x i) c (!x i) h0, ev_eval]

lemma shrink {n : ℕ} (i : Fin n) (c : Bool) (φ : DMFormula n) (hn : negc i φ = 1) :
    (∃ k : Bool, ∀ x : Fin n → Bool, ev i φ x (x i) c = k) ∨
    (∃ ψ : DMFormula n, ψ.leaves < φ.leaves ∧
      ∀ x : Fin n → Bool, ψ.eval x = ev i φ x (x i) c) := by
  induction φ with
  | lit j b =>
    rw [negc_lit] at hn
    by_cases h : j = i
    · cases b
      · left
        exact ⟨c, fun x => by simp [ev, h]⟩
      · simp [h] at hn
    · simp [h] at hn
  | and φ ψ ih1 ih2 =>
    rw [negc_and] at hn
    have l1 := leaves_pos φ
    have l2 := leaves_pos ψ
    have c1 : (negc i φ = 1 ∧ negc i ψ = 0) ∨ (negc i φ = 0 ∧ negc i ψ = 1) := by omega
    rcases c1 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rcases ih1 a1 with ⟨k, hk⟩ | ⟨χ, hl, hχ⟩
      · cases k
        · left
          exact ⟨false, fun x => by simp only [ev, hk x, Bool.false_and]⟩
        · right
          refine ⟨ψ, by simp only [DMFormula.leaves]; omega, fun x => ?_⟩
          simp only [ev, hk x, Bool.true_and, ev_noneg_eval i ψ x c a2]
      · right
        refine ⟨DMFormula.and χ ψ, by simp only [DMFormula.leaves]; omega, fun x => ?_⟩
        simp only [ev, DMFormula.eval, hχ x, ev_noneg_eval i ψ x c a2]
    · rcases ih2 a2 with ⟨k, hk⟩ | ⟨χ, hl, hχ⟩
      · cases k
        · left
          exact ⟨false, fun x => by simp only [ev, hk x, Bool.and_false]⟩
        · right
          refine ⟨φ, by simp only [DMFormula.leaves]; omega, fun x => ?_⟩
          simp only [ev, hk x, Bool.and_true, ev_noneg_eval i φ x c a1]
      · right
        refine ⟨DMFormula.and φ χ, by simp only [DMFormula.leaves]; omega, fun x => ?_⟩
        simp only [ev, DMFormula.eval, hχ x, ev_noneg_eval i φ x c a1]
  | or φ ψ ih1 ih2 =>
    rw [negc_or] at hn
    have l1 := leaves_pos φ
    have l2 := leaves_pos ψ
    have c1 : (negc i φ = 1 ∧ negc i ψ = 0) ∨ (negc i φ = 0 ∧ negc i ψ = 1) := by omega
    rcases c1 with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rcases ih1 a1 with ⟨k, hk⟩ | ⟨χ, hl, hχ⟩
      · cases k
        · right
          refine ⟨ψ, by simp only [DMFormula.leaves]; omega, fun x => ?_⟩
          simp only [ev, hk x, Bool.false_or, ev_noneg_eval i ψ x c a2]
        · left
          exact ⟨true, fun x => by simp only [ev, hk x, Bool.true_or]⟩
      · right
        refine ⟨DMFormula.or χ ψ, by simp only [DMFormula.leaves]; omega, fun x => ?_⟩
        simp only [ev, DMFormula.eval, hχ x, ev_noneg_eval i ψ x c a2]
    · rcases ih2 a2 with ⟨k, hk⟩ | ⟨χ, hl, hχ⟩
      · cases k
        · right
          refine ⟨φ, by simp only [DMFormula.leaves]; omega, fun x => ?_⟩
          simp only [ev, hk x, Bool.or_false, ev_noneg_eval i φ x c a1]
        · left
          exact ⟨true, fun x => by simp only [ev, hk x, Bool.or_true]⟩
      · right
        refine ⟨DMFormula.or φ χ, by simp only [DMFormula.leaves]; omega, fun x => ?_⟩
        simp only [ev, DMFormula.eval, hχ x, ev_noneg_eval i φ x c a1]

end PEqualNP.Outside.L_meta_258

theorem PEqualNP.Outside.L_meta_258 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)) → (∀ x : Fin n → Bool, φ.eval x = f x) → (∀ ψ : PEqualNP.MetaComplexity.DMFormula n, (∀ x : Fin n → Bool, ψ.eval x = f x) → φ.leaves ≤ ψ.leaves) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ ≤ 2 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 := by
  intro n f φ i hmono hess hφ hmin hcnt
  have hcnt' : PEqualNP.Outside.L_meta_258.cnt i φ ≤ 2 := hcnt
  show PEqualNP.Outside.L_meta_258.negc i φ = 0
  by_contra hneg
  have hsplit := PEqualNP.Outside.L_meta_258.cnt_split i φ
  have hT : ∀ x : Fin n → Bool, f (Function.update x i true) = PEqualNP.Outside.L_meta_258.ev i φ x true false := by
    intro x
    rw [← hφ, ← PEqualNP.Outside.L_meta_258.ev_eval i φ, PEqualNP.Outside.L_meta_258.ev_update]
    simp
  have hF : ∀ x : Fin n → Bool, f (Function.update x i false) = PEqualNP.Outside.L_meta_258.ev i φ x false true := by
    intro x
    rw [← hφ, ← PEqualNP.Outside.L_meta_258.ev_eval i φ, PEqualNP.Outside.L_meta_258.ev_update]
    simp
  have hle : ∀ x : Fin n → Bool, PEqualNP.Outside.L_meta_258.ev i φ x false true = true → PEqualNP.Outside.L_meta_258.ev i φ x true false = true := by
    intro x h
    rw [← hT x]
    rw [← hF x] at h
    refine hmono _ _ (fun j hj => ?_) h
    by_cases hji : j = i
    · rw [hji]
      simp
    · rw [Function.update_of_ne hji] at hj ⊢
      exact hj
  obtain ⟨x0, hx0⟩ := hess
  rw [hT x0, hF x0] at hx0
  have hfx : ∀ (c : Bool) (g : (Fin n → Bool) → Bool), (∀ x, f x = PEqualNP.Outside.L_meta_258.ev i φ x (x i) c) →
      PEqualNP.Outside.L_meta_258.negc i φ = 1 → False := by
    intro c g hfc hn1
    rcases PEqualNP.Outside.L_meta_258.shrink i c φ hn1 with ⟨k, hk⟩ | ⟨ψ, hl, hψ⟩
    · have e1 := hT x0
      have e2 := hF x0
      rw [hfc, hk] at e1 e2
      rw [← e1, ← e2] at hx0
      exact hx0 rfl
    · have := hmin ψ (fun x => by rw [hψ x, ← hfc x])
      omega
  by_cases hp : PEqualNP.Outside.L_meta_258.posc i φ = 0
  · apply hx0
    have h1 : PEqualNP.Outside.L_meta_258.ev i φ x0 true false = true → PEqualNP.Outside.L_meta_258.ev i φ x0 false true = true := by
      intro h
      rw [PEqualNP.Outside.L_meta_258.ev_nopos i φ x0 true false false hp] at h
      exact PEqualNP.Outside.L_meta_258.ev_mono i φ x0 false false false true (fun h => h) (fun h => absurd h (by simp)) h
    have h2 := hle x0
    revert h1 h2
    cases PEqualNP.Outside.L_meta_258.ev i φ x0 true false <;> cases PEqualNP.Outside.L_meta_258.ev i φ x0 false true <;> simp
  · have hp1 : PEqualNP.Outside.L_meta_258.posc i φ = 1 := by omega
    have hn1 : PEqualNP.Outside.L_meta_258.negc i φ = 1 := by omega
    rcases PEqualNP.Outside.L_meta_258.shape i φ hp1 hn1 with h | h
    · apply hfx true f _ hn1
      intro x
      cases hxi : x i
      · rw [← hφ x, ← PEqualNP.Outside.L_meta_258.ev_eval i φ x, hxi]
        rfl
      · rw [← hφ x, ← PEqualNP.Outside.L_meta_258.ev_eval i φ x, hxi, h x]
        have := hle x
        revert this
        simp only [Bool.not_true]
        cases PEqualNP.Outside.L_meta_258.ev i φ x true false <;> cases PEqualNP.Outside.L_meta_258.ev i φ x false true <;> simp
    · apply hfx false f _ hn1
      intro x
      cases hxi : x i
      · rw [← hφ x, ← PEqualNP.Outside.L_meta_258.ev_eval i φ x, hxi, h x]
        have := hle x
        revert this
        simp only [Bool.not_false]
        cases PEqualNP.Outside.L_meta_258.ev i φ x true false <;> cases PEqualNP.Outside.L_meta_258.ev i φ x false true <;> simp
      · rw [← hφ x, ← PEqualNP.Outside.L_meta_258.ev_eval i φ x, hxi]
        rfl
