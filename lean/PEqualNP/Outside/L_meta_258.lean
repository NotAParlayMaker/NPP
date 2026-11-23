import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_258

open PEqualNP.MetaComplexity

variable {n : ℕ}

noncomputable def tot (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

noncomputable def neg (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

noncomputable def pos (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun (j : Fin n) (c : Bool) => if j = i ∧ c = true then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

theorem tot_eq (i : Fin n) (φ : DMFormula n) : tot i φ = pos i φ + neg i φ := by
  induction φ with
  | lit j c =>
    show (if j = i then 1 else 0) = (if j = i ∧ c = true then 1 else 0) +
      (if j = i ∧ c = false then 1 else 0)
    by_cases h : j = i <;> cases c <;> simp [h]
  | and a b iha ihb =>
    show tot i a + tot i b = (pos i a + pos i b) + (neg i a + neg i b)
    omega
  | or a b iha ihb =>
    show tot i a + tot i b = (pos i a + pos i b) + (neg i a + neg i b)
    omega

theorem neg_le_leaves (i : Fin n) (φ : DMFormula n) : neg i φ ≤ φ.leaves := by
  induction φ with
  | lit j c =>
    show (if j = i ∧ c = false then 1 else 0) ≤ 1
    split <;> omega
  | and a b iha ihb =>
    show neg i a + neg i b ≤ a.leaves + b.leaves
    omega
  | or a b iha ihb =>
    show neg i a + neg i b ≤ a.leaves + b.leaves
    omega

def ev2 (i : Fin n) : DMFormula n → (Fin n → Bool) → Bool → Bool → Bool
  | DMFormula.lit j c, x, p, y => if j = i then (if c then p else y) else (if c then x j else !x j)
  | DMFormula.and a b, x, p, y => ev2 i a x p y && ev2 i b x p y
  | DMFormula.or a b, x, p, y => ev2 i a x p y || ev2 i b x p y

theorem eval_eq (i : Fin n) (φ : DMFormula n) (x : Fin n → Bool) :
    φ.eval x = ev2 i φ x (x i) (!x i) := by
  induction φ with
  | lit j c =>
    simp only [DMFormula.eval, ev2]
    by_cases h : j = i
    · subst h; cases c <;> simp
    · simp [h]
  | and a b iha ihb => simp only [DMFormula.eval, ev2, iha, ihb]
  | or a b iha ihb => simp only [DMFormula.eval, ev2, iha, ihb]

theorem ev2_update (i : Fin n) (φ : DMFormula n) (x : Fin n → Bool) (b p y : Bool) :
    ev2 i φ (Function.update x i b) p y = ev2 i φ x p y := by
  induction φ with
  | lit j c =>
    simp only [ev2]
    by_cases h : j = i
    · simp [h]
    · simp [h]
  | and a b iha ihb => simp only [ev2, iha, ihb]
  | or a b iha ihb => simp only [ev2, iha, ihb]

theorem ev2_mono (i : Fin n) (φ : DMFormula n) (x : Fin n → Bool) (p p' y y' : Bool)
    (hp : p = true → p' = true) (hy : y = true → y' = true) :
    ev2 i φ x p y = true → ev2 i φ x p' y' = true := by
  induction φ with
  | lit j c =>
    simp only [ev2]
    by_cases h : j = i <;> cases c <;> simp [h] <;> assumption
  | and a b iha ihb =>
    simp only [ev2, Bool.and_eq_true]
    exact fun h => ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb =>
    simp only [ev2, Bool.or_eq_true]
    exact fun h => h.elim (fun h => Or.inl (iha h)) (fun h => Or.inr (ihb h))

theorem ev2_pos0 (i : Fin n) (φ : DMFormula n) (h : pos i φ = 0) (x : Fin n → Bool)
    (p p' y : Bool) : ev2 i φ x p y = ev2 i φ x p' y := by
  induction φ with
  | lit j c =>
    have h' : (if j = i ∧ c = true then 1 else 0) = 0 := h
    simp only [ev2]
    by_cases hj : j = i
    · cases c
      · simp [hj]
      · simp [hj] at h'
    · simp [hj]
  | and a b iha ihb =>
    have h' : pos i a + pos i b = 0 := h
    simp only [ev2, iha (by omega), ihb (by omega)]
  | or a b iha ihb =>
    have h' : pos i a + pos i b = 0 := h
    simp only [ev2, iha (by omega), ihb (by omega)]

theorem ev2_neg0 (i : Fin n) (φ : DMFormula n) (h : neg i φ = 0) (x : Fin n → Bool)
    (p y y' : Bool) : ev2 i φ x p y = ev2 i φ x p y' := by
  induction φ with
  | lit j c =>
    have h' : (if j = i ∧ c = false then 1 else 0) = 0 := h
    simp only [ev2]
    by_cases hj : j = i
    · cases c
      · simp [hj] at h'
      · simp [hj]
    · simp [hj]
  | and a b iha ihb =>
    have h' : neg i a + neg i b = 0 := h
    simp only [ev2, iha (by omega), ihb (by omega)]
  | or a b iha ihb =>
    have h' : neg i a + neg i b = 0 := h
    simp only [ev2, iha (by omega), ihb (by omega)]

def AndPat (i : Fin n) (φ : DMFormula n) : Prop :=
  ∃ x, ev2 i φ x true false = false ∧ ev2 i φ x false true = false ∧ ev2 i φ x true true = true

def OrPat (i : Fin n) (φ : DMFormula n) : Prop :=
  ∃ x, ev2 i φ x false false = false ∧ ev2 i φ x false true = true ∧ ev2 i φ x true false = true

theorem pat (i : Fin n) (φ : DMFormula n) (hp : pos i φ ≤ 1) (hn : neg i φ ≤ 1) :
    ¬ AndPat i φ ∨ ¬ OrPat i φ := by
  induction φ with
  | lit j c =>
    left
    rintro ⟨x, h1, h2, h3⟩
    simp only [ev2] at h1 h2 h3
    by_cases hj : j = i <;> cases c <;> simp_all
  | and a b iha ihb =>
    have hp' : pos i a + pos i b ≤ 1 := hp
    have hn' : neg i a + neg i b ≤ 1 := hn
    by_cases ha : pos i a = 0 ∧ neg i a = 0
    · have e : ∀ x p y, ev2 i a x p y = ev2 i a x false false := fun x p y => by
        rw [ev2_pos0 i a ha.1 x p false y, ev2_neg0 i a ha.2 x false y false]
      rcases ihb (by omega) (by omega) with h | h
      · left; rintro ⟨x, h1, h2, h3⟩
        simp only [ev2, e] at h1 h2 h3
        have hax : ev2 i a x false false = true := by
          revert h3; cases ev2 i a x false false <;> simp
        simp only [hax, Bool.true_and] at h1 h2 h3
        exact h ⟨x, h1, h2, h3⟩
      · right; rintro ⟨x, h1, h2, h3⟩
        simp only [ev2, e] at h1 h2 h3
        have hax : ev2 i a x false false = true := by
          revert h3; cases ev2 i a x false false <;> simp
        simp only [hax, Bool.true_and] at h1 h2 h3
        exact h ⟨x, h1, h2, h3⟩
    by_cases hb : pos i b = 0 ∧ neg i b = 0
    · have e : ∀ x p y, ev2 i b x p y = ev2 i b x false false := fun x p y => by
        rw [ev2_pos0 i b hb.1 x p false y, ev2_neg0 i b hb.2 x false y false]
      rcases iha (by omega) (by omega) with h | h
      · left; rintro ⟨x, h1, h2, h3⟩
        simp only [ev2, e] at h1 h2 h3
        have hbx : ev2 i b x false false = true := by
          revert h3; cases ev2 i b x false false <;> simp
        simp only [hbx, Bool.and_true] at h1 h2 h3
        exact h ⟨x, h1, h2, h3⟩
      · right; rintro ⟨x, h1, h2, h3⟩
        simp only [ev2, e] at h1 h2 h3
        have hbx : ev2 i b x false false = true := by
          revert h3; cases ev2 i b x false false <;> simp
        simp only [hbx, Bool.and_true] at h1 h2 h3
        exact h ⟨x, h1, h2, h3⟩
    right
    rintro ⟨x, h1, h2, h3⟩
    simp only [ev2, Bool.and_eq_true, Bool.and_eq_false_iff] at h1 h2 h3
    by_cases hpa : pos i a = 0
    · have hnb : neg i b = 0 := by omega
      have e1 := ev2_pos0 i a hpa x false true false
      have e2 := ev2_neg0 i b hnb x false false true
      rcases h1 with h | h
      · rw [e1, h3.1] at h; exact absurd h (by simp)
      · rw [e2, h2.2] at h; exact absurd h (by simp)
    · have hpb : pos i b = 0 := by omega
      have hna : neg i a = 0 := by omega
      have e1 := ev2_neg0 i a hna x false false true
      have e2 := ev2_pos0 i b hpb x false true false
      rcases h1 with h | h
      · rw [e1, h2.1] at h; exact absurd h (by simp)
      · rw [e2, h3.2] at h; exact absurd h (by simp)
  | or a b iha ihb =>
    have hp' : pos i a + pos i b ≤ 1 := hp
    have hn' : neg i a + neg i b ≤ 1 := hn
    by_cases ha : pos i a = 0 ∧ neg i a = 0
    · have e : ∀ x p y, ev2 i a x p y = ev2 i a x false false := fun x p y => by
        rw [ev2_pos0 i a ha.1 x p false y, ev2_neg0 i a ha.2 x false y false]
      rcases ihb (by omega) (by omega) with h | h
      · left; rintro ⟨x, h1, h2, h3⟩
        simp only [ev2, e] at h1 h2 h3
        have hax : ev2 i a x false false = false := by
          revert h1; cases ev2 i a x false false <;> simp
        simp only [hax, Bool.false_or] at h1 h2 h3
        exact h ⟨x, h1, h2, h3⟩
      · right; rintro ⟨x, h1, h2, h3⟩
        simp only [ev2, e] at h1 h2 h3
        have hax : ev2 i a x false false = false := by
          revert h1; cases ev2 i a x false false <;> simp
        simp only [hax, Bool.false_or] at h1 h2 h3
        exact h ⟨x, h1, h2, h3⟩
    by_cases hb : pos i b = 0 ∧ neg i b = 0
    · have e : ∀ x p y, ev2 i b x p y = ev2 i b x false false := fun x p y => by
        rw [ev2_pos0 i b hb.1 x p false y, ev2_neg0 i b hb.2 x false y false]
      rcases iha (by omega) (by omega) with h | h
      · left; rintro ⟨x, h1, h2, h3⟩
        simp only [ev2, e] at h1 h2 h3
        have hbx : ev2 i b x false false = false := by
          revert h1; cases ev2 i b x false false <;> simp
        simp only [hbx, Bool.or_false] at h1 h2 h3
        exact h ⟨x, h1, h2, h3⟩
      · right; rintro ⟨x, h1, h2, h3⟩
        simp only [ev2, e] at h1 h2 h3
        have hbx : ev2 i b x false false = false := by
          revert h1; cases ev2 i b x false false <;> simp
        simp only [hbx, Bool.or_false] at h1 h2 h3
        exact h ⟨x, h1, h2, h3⟩
    left
    rintro ⟨x, h1, h2, h3⟩
    simp only [ev2, Bool.or_eq_false_iff, Bool.or_eq_true] at h1 h2 h3
    by_cases hpa : pos i a = 0
    · have hnb : neg i b = 0 := by omega
      have e1 := ev2_pos0 i a hpa x true false true
      have e2 := ev2_neg0 i b hnb x true true false
      rcases h3 with h | h
      · rw [e1, h2.1] at h; exact absurd h (by simp)
      · rw [e2, h1.2] at h; exact absurd h (by simp)
    · have hpb : pos i b = 0 := by omega
      have hna : neg i a = 0 := by omega
      have e1 := ev2_neg0 i a hna x true true false
      have e2 := ev2_pos0 i b hpb x true false true
      rcases h3 with h | h
      · rw [e1, h1.1] at h; exact absurd h (by simp)
      · rw [e2, h2.2] at h; exact absurd h (by simp)

def sub (i : Fin n) (c : Bool) : DMFormula n → Bool ⊕ DMFormula n
  | DMFormula.lit j b => if j = i ∧ b = false then Sum.inl c else Sum.inr (DMFormula.lit j b)
  | DMFormula.and a b =>
    match sub i c a with
    | Sum.inl true => sub i c b
    | Sum.inl false => Sum.inl false
    | Sum.inr a' =>
      match sub i c b with
      | Sum.inl true => Sum.inr a'
      | Sum.inl false => Sum.inl false
      | Sum.inr b' => Sum.inr (DMFormula.and a' b')
  | DMFormula.or a b =>
    match sub i c a with
    | Sum.inl true => Sum.inl true
    | Sum.inl false => sub i c b
    | Sum.inr a' =>
      match sub i c b with
      | Sum.inl true => Sum.inl true
      | Sum.inl false => Sum.inr a'
      | Sum.inr b' => Sum.inr (DMFormula.or a' b')

def val (r : Bool ⊕ DMFormula n) (x : Fin n → Bool) : Bool :=
  Sum.elim id (fun ψ => ψ.eval x) r

theorem sub_spec (i : Fin n) (c : Bool) (φ : DMFormula n) :
    (∀ x, val (sub i c φ) x = ev2 i φ x (x i) c) ∧
    (∀ ψ, sub i c φ = Sum.inr ψ → ψ.leaves + neg i φ ≤ φ.leaves) := by
  induction φ with
  | lit j b =>
    by_cases h : j = i ∧ b = false
    · obtain ⟨rfl, rfl⟩ := h
      refine ⟨fun x => ?_, fun ψ hψ => ?_⟩
      · simp [sub, val, ev2]
      · simp [sub] at hψ
    · refine ⟨fun x => ?_, fun ψ hψ => ?_⟩
      · simp only [sub, h, ite_false, val, Sum.elim_inr, DMFormula.eval, ev2]
        by_cases hj : j = i
        · subst hj; cases b <;> simp_all
        · simp [hj]
      · simp only [sub, h, ite_false, Sum.inr.injEq] at hψ
        subst hψ
        show 1 + (if j = i ∧ b = false then 1 else 0) ≤ 1
        simp [h]
  | and a b iha ihb =>
    have hla := neg_le_leaves i a
    have hlb := neg_le_leaves i b
    have hn : neg i (DMFormula.and a b) = neg i a + neg i b := rfl
    have hl : (DMFormula.and a b).leaves = a.leaves + b.leaves := rfl
    rw [hn, hl]
    rcases ha : sub i c a with (_ | _) | a' <;> rcases hb : sub i c b with (_ | _) | b' <;>
      simp only [sub, ha, hb] <;>
      exact ⟨fun x => by
        have h1 := iha.1 x
        have h2 := ihb.1 x
        rw [ha] at h1
        rw [hb] at h2
        simp only [ev2]
        rw [← h1, ← h2]
        try simp [val, DMFormula.eval],
      fun ψ hψ => by
        simp only [Sum.inr.injEq, reduceCtorEq] at hψ <;> subst hψ <;>
        first
        | (have h3 := iha.2 _ ha; have h4 := ihb.2 _ hb; simp only [DMFormula.leaves]; omega)
        | (have h3 := iha.2 _ ha; omega)
        | (have h4 := ihb.2 _ hb; omega)⟩
  | or a b iha ihb =>
    have hla := neg_le_leaves i a
    have hlb := neg_le_leaves i b
    have hn : neg i (DMFormula.or a b) = neg i a + neg i b := rfl
    have hl : (DMFormula.or a b).leaves = a.leaves + b.leaves := rfl
    rw [hn, hl]
    rcases ha : sub i c a with (_ | _) | a' <;> rcases hb : sub i c b with (_ | _) | b' <;>
      simp only [sub, ha, hb] <;>
      exact ⟨fun x => by
        have h1 := iha.1 x
        have h2 := ihb.1 x
        rw [ha] at h1
        rw [hb] at h2
        simp only [ev2]
        rw [← h1, ← h2]
        try simp [val, DMFormula.eval],
      fun ψ hψ => by
        simp only [Sum.inr.injEq, reduceCtorEq] at hψ <;> subst hψ <;>
        first
        | (have h3 := iha.2 _ ha; have h4 := ihb.2 _ hb; simp only [DMFormula.leaves]; omega)
        | (have h3 := iha.2 _ ha; omega)
        | (have h4 := ihb.2 _ hb; omega)⟩

theorem main (f : (Fin n → Bool) → Bool) (φ : DMFormula n) (i : Fin n)
    (hmono : ∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) →
      f x = true → f y = true)
    (hess : ∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false))
    (heval : ∀ x : Fin n → Bool, φ.eval x = f x)
    (hmin : ∀ ψ : DMFormula n, (∀ x : Fin n → Bool, ψ.eval x = f x) → φ.leaves ≤ ψ.leaves)
    (htot : tot i φ ≤ 2) : neg i φ = 0 := by
  by_contra hneg
  have hsum := tot_eq i φ
  have hf : ∀ x, f x = ev2 i φ x (x i) (!x i) := fun x => by rw [← heval, eval_eq i φ x]
  have hup : ∀ x b, f (Function.update x i b) = ev2 i φ x b (!b) := fun x b => by
    rw [hf, ev2_update]; simp
  have hle : ∀ x, ∀ j, Function.update x i false j = true → Function.update x i true j = true :=
    fun x j h => by
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj] at h ⊢; exact h
  have Q : ∀ x, ev2 i φ x false true = true → ev2 i φ x true false = true := fun x h => by
    have := hmono _ _ (hle x) (by rw [hup]; simpa using h)
    rw [hup] at this; simpa using this
  obtain ⟨x0, hx0⟩ := hess
  have hft : ev2 i φ x0 true false = true ∧ ev2 i φ x0 false true = false := by
    rw [hup, hup] at hx0
    simp only [Bool.not_true, Bool.not_false] at hx0
    constructor
    · by_contra h
      have h' : ev2 i φ x0 true false = false := by simpa using h
      have : ev2 i φ x0 false true = false := by
        cases e : ev2 i φ x0 false true
        · rfl
        · exact absurd (Q x0 e) (by simp [h'])
      exact hx0 (by rw [h', this])
    · cases e : ev2 i φ x0 false true
      · rfl
      · exact absurd (by rw [Q x0 e, e]) hx0
  have hc : ∃ c, ∀ x, ev2 i φ x (x i) c = f x := by
    by_cases hp0 : pos i φ = 0
    · exfalso
      have h1 := hft.1
      rw [ev2_pos0 i φ hp0 x0 true false false] at h1
      have := ev2_mono i φ x0 false false false true id (fun _ => rfl) h1
      rw [hft.2] at this; exact absurd this (by simp)
    rcases pat i φ (by omega) (by omega) with h | h
    · refine ⟨true, fun x => ?_⟩
      rw [hf]
      cases hx : x i
      · rfl
      · simp only [Bool.not_true]
        cases e1 : ev2 i φ x true true <;> cases e2 : ev2 i φ x true false
        · rfl
        · exact absurd (ev2_mono i φ x true true false true id (fun _ => rfl) e2) (by simp [e1])
        · exfalso; apply h
          refine ⟨x, e2, ?_, e1⟩
          cases e3 : ev2 i φ x false true
          · rfl
          · exact absurd (Q x e3) (by simp [e2])
        · rfl
    · refine ⟨false, fun x => ?_⟩
      rw [hf]
      cases hx : x i
      · simp only [Bool.not_false]
        cases e1 : ev2 i φ x false false <;> cases e2 : ev2 i φ x false true
        · rfl
        · exfalso; apply h
          exact ⟨x, e1, e2, Q x e2⟩
        · exact absurd (ev2_mono i φ x false false false true id (fun _ => rfl) e1) (by simp [e2])
        · rfl
      · rfl
  obtain ⟨c, hc⟩ := hc
  obtain ⟨hs1, hs2⟩ := sub_spec i c φ
  rcases hs : sub i c φ with b | ψ
  · have e : ∀ x, f x = b := fun x => by
      rw [← hc x, ← hs1 x, hs]; rfl
    exact hx0 (by rw [e, e])
  · have hψ : ∀ x, ψ.eval x = f x := fun x => by
      rw [← hc x, ← hs1 x, hs]; rfl
    have := hmin ψ hψ
    have := hs2 ψ hs
    omega

end PEqualNP.Outside.L_meta_258

theorem PEqualNP.Outside.L_meta_258 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)) → (∀ x : Fin n → Bool, φ.eval x = f x) → (∀ ψ : PEqualNP.MetaComplexity.DMFormula n, (∀ x : Fin n → Bool, ψ.eval x = f x) → φ.leaves ≤ ψ.leaves) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ ≤ 2 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 := by
  intro n f φ i hmono hess heval hmin htot
  exact PEqualNP.Outside.L_meta_258.main f φ i hmono hess heval hmin htot
