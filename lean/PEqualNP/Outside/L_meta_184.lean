import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_184_aux

open PEqualNP.MetaComplexity

private def paw (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3)

private def maj3 (y : Fin 3 → Bool) : Bool :=
  (y 0 && y 1) || (y 0 && y 2) || (y 1 && y 2)

private def pawFormula : DMFormula 4 :=
  DMFormula.or
    (DMFormula.and (DMFormula.lit 0 true)
      (DMFormula.or (DMFormula.lit 1 true)
        (DMFormula.or (DMFormula.lit 2 true) (DMFormula.lit 3 true))))
    (DMFormula.and (DMFormula.lit 1 true) (DMFormula.lit 2 true))

private lemma pawFormula_leaves : pawFormula.leaves = 6 := rfl

private lemma pawFormula_eval (x : Fin 4 → Bool) : pawFormula.eval x = paw x := by
  simp only [pawFormula, paw, DMFormula.eval, ↓reduceIte]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> rfl

private def countVar3 : DMFormula 4 → ℕ
  | DMFormula.lit i _ => if i = 3 then 1 else 0
  | DMFormula.and a b => countVar3 a + countVar3 b
  | DMFormula.or a b => countVar3 a + countVar3 b

private lemma countVar3_le_leaves (φ : DMFormula 4) : countVar3 φ ≤ φ.leaves := by
  induction φ with
  | lit i b =>
    simp only [countVar3, DMFormula.leaves]
    split_ifs <;> omega
  | and a b iha ihb =>
    simp only [countVar3, DMFormula.leaves]
    omega
  | or a b iha ihb =>
    simp only [countVar3, DMFormula.leaves]
    omega

private lemma eval_indep_of_countVar3_zero (φ : DMFormula 4) (hc : countVar3 φ = 0)
    (x y : Fin 4 → Bool) (hxy : ∀ i : Fin 4, i ≠ 3 → x i = y i) :
    φ.eval x = φ.eval y := by
  induction φ with
  | lit i b =>
    have hi : i ≠ 3 := by
      intro heq
      simp [countVar3, heq] at hc
    simp only [DMFormula.eval, hxy i hi]
  | and a b iha ihb =>
    simp only [countVar3, Nat.add_eq_zero_iff] at hc
    simp only [DMFormula.eval, iha hc.1, ihb hc.2]
  | or a b iha ihb =>
    simp only [countVar3, Nat.add_eq_zero_iff] at hc
    simp only [DMFormula.eval, iha hc.1, ihb hc.2]

private def ext3 (y : Fin 3 → Bool) (b : Bool) (i : Fin 4) : Bool :=
  if h : i.val < 3 then y ⟨i.val, h⟩ else b

private def subst3 : DMFormula 4 → Sum Bool (DMFormula 3)
  | DMFormula.lit i b =>
    if h : i.val < 3 then Sum.inr (DMFormula.lit ⟨i.val, h⟩ b)
    else Sum.inl (if b then false else true)
  | DMFormula.and a b =>
    match subst3 a, subst3 b with
    | Sum.inl false, _ => Sum.inl false
    | _, Sum.inl false => Sum.inl false
    | Sum.inl true, r => r
    | l, Sum.inl true => l
    | Sum.inr a', Sum.inr b' => Sum.inr (DMFormula.and a' b')
  | DMFormula.or a b =>
    match subst3 a, subst3 b with
    | Sum.inl true, _ => Sum.inl true
    | _, Sum.inl true => Sum.inl true
    | Sum.inl false, r => r
    | l, Sum.inl false => l
    | Sum.inr a', Sum.inr b' => Sum.inr (DMFormula.or a' b')

private lemma subst3_eval (φ : DMFormula 4) (y : Fin 3 → Bool) :
    (match subst3 φ with
      | Sum.inl b => b
      | Sum.inr ψ => ψ.eval y) = φ.eval (ext3 y false) := by
  induction φ with
  | lit i b =>
    cases b <;> by_cases h : i.val < 3 <;> simp [subst3, DMFormula.eval, ext3, h]
  | and a b iha ihb =>
    simp only [subst3, DMFormula.eval, ← iha, ← ihb]
    cases subst3 a with
    | inl ba =>
      cases ba <;> cases subst3 b with
      | inl bb => cases bb <;> rfl
      | inr ψb => simp
    | inr ψa =>
      cases subst3 b with
      | inl bb => cases bb <;> simp
      | inr ψb => rfl
  | or a b iha ihb =>
    simp only [subst3, DMFormula.eval, ← iha, ← ihb]
    cases subst3 a with
    | inl ba =>
      cases ba <;> cases subst3 b with
      | inl bb => cases bb <;> rfl
      | inr ψb => simp
    | inr ψa =>
      cases subst3 b with
      | inl bb => cases bb <;> simp
      | inr ψb => rfl

private lemma subst3_leaves (φ : DMFormula 4) :
    ∀ ψ : DMFormula 3, subst3 φ = Sum.inr ψ → ψ.leaves + countVar3 φ ≤ φ.leaves := by
  induction φ with
  | lit i b =>
    intro ψ hψ
    simp only [subst3] at hψ
    split_ifs at hψ with hi
    injection hψ with hψ'
    subst hψ'
    have hne : i ≠ 3 := by intro heq; subst heq; omega
    simp [countVar3, hne, DMFormula.leaves]
  | and a b iha ihb =>
    intro ψ hψ
    simp only [subst3] at hψ
    have hca := countVar3_le_leaves a
    have hcb := countVar3_le_leaves b
    cases ha : subst3 a with
    | inl ba =>
      rw [ha] at hψ
      cases ba
      · cases hψ
      · cases hb : subst3 b with
        | inl bb => rw [hb] at hψ; cases bb <;> cases hψ
        | inr ψb =>
          rw [hb] at hψ
          injection hψ with hψ'
          subst hψ'
          have := ihb ψb hb
          simp only [countVar3, DMFormula.leaves]
          omega
    | inr ψa =>
      rw [ha] at hψ
      cases hb : subst3 b with
      | inl bb =>
        rw [hb] at hψ
        cases bb
        · cases hψ
        · injection hψ with hψ'
          subst hψ'
          have := iha ψa ha
          simp only [countVar3, DMFormula.leaves]
          omega
      | inr ψb =>
        rw [hb] at hψ
        injection hψ with hψ'
        subst hψ'
        have := iha ψa ha
        have := ihb ψb hb
        simp only [countVar3, DMFormula.leaves]
        omega
  | or a b iha ihb =>
    intro ψ hψ
    simp only [subst3] at hψ
    have hca := countVar3_le_leaves a
    have hcb := countVar3_le_leaves b
    cases ha : subst3 a with
    | inl ba =>
      rw [ha] at hψ
      cases ba
      · cases hb : subst3 b with
        | inl bb => rw [hb] at hψ; cases bb <;> cases hψ
        | inr ψb =>
          rw [hb] at hψ
          injection hψ with hψ'
          subst hψ'
          have := ihb ψb hb
          simp only [countVar3, DMFormula.leaves]
          omega
      · cases hψ
    | inr ψa =>
      rw [ha] at hψ
      cases hb : subst3 b with
      | inl bb =>
        rw [hb] at hψ
        cases bb
        · injection hψ with hψ'
          subst hψ'
          have := iha ψa ha
          simp only [countVar3, DMFormula.leaves]
          omega
        · cases hψ
      | inr ψb =>
        rw [hb] at hψ
        injection hψ with hψ'
        subst hψ'
        have := iha ψa ha
        have := ihb ψb hb
        simp only [countVar3, DMFormula.leaves]
        omega

private lemma leaves_pos {n : ℕ} (φ : DMFormula n) : 1 ≤ φ.leaves := by
  induction φ with
  | lit _ _ => simp [DMFormula.leaves]
  | and a b iha ihb => simp only [DMFormula.leaves]; omega
  | or a b iha ihb => simp only [DMFormula.leaves]; omega

private lemma lit_not_le_maj3 (i : Fin 3) (b : Bool) :
    ¬ (∀ y : Fin 3 → Bool, (DMFormula.lit i b).eval y = true → maj3 y = true) := by
  intro h
  fin_cases i <;> cases b
  · have := h ![false, false, false] (by rfl); simp [maj3] at this
  · have := h ![true, false, false] (by rfl); simp [maj3] at this
  · have := h ![false, false, false] (by rfl); simp [maj3] at this
  · have := h ![false, true, false] (by rfl); simp [maj3] at this
  · have := h ![false, false, false] (by rfl); simp [maj3] at this
  · have := h ![false, false, true] (by rfl); simp [maj3] at this

private lemma maj3_not_le_lit (i : Fin 3) (b : Bool) :
    ¬ (∀ y : Fin 3 → Bool, maj3 y = true → (DMFormula.lit i b).eval y = true) := by
  intro h
  fin_cases i <;> cases b
  · have := h ![true, true, false] (by rfl); simp [DMFormula.eval] at this
  · have := h ![false, true, true] (by rfl); simp [DMFormula.eval] at this
  · have := h ![true, true, false] (by rfl); simp [DMFormula.eval] at this
  · have := h ![true, false, true] (by rfl); simp [DMFormula.eval] at this
  · have := h ![true, false, true] (by rfl); simp [DMFormula.eval] at this
  · have := h ![true, true, false] (by rfl); simp [DMFormula.eval] at this

private lemma two_le_maj3_at_most_one (a : DMFormula 3) (ha : a.leaves ≤ 2)
    (hle : ∀ y : Fin 3 → Bool, a.eval y = true → maj3 y = true) :
    (a.eval ![true, true, false] = false ∧ a.eval ![true, false, true] = false) ∨
    (a.eval ![true, true, false] = false ∧ a.eval ![false, true, true] = false) ∨
    (a.eval ![true, false, true] = false ∧ a.eval ![false, true, true] = false) := by
  cases a with
  | lit i b => exact absurd hle (lit_not_le_maj3 i b)
  | or a1 a2 =>
    have h1 := leaves_pos a1
    have h2 := leaves_pos a2
    simp only [DMFormula.leaves] at ha
    cases a1 with
    | lit i b =>
      exfalso
      apply lit_not_le_maj3 i b
      intro y hy
      exact hle y (by change (DMFormula.lit i b).eval y || a2.eval y = true; rw [hy]; rfl)
    | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
    | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
  | and a1 a2 =>
    have h1 := leaves_pos a1
    have h2 := leaves_pos a2
    simp only [DMFormula.leaves] at ha
    cases a1 with
    | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
    | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
    | lit i1 b1 =>
      cases a2 with
      | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
      | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
      | lit i2 b2 =>
        fin_cases i1 <;> fin_cases i2 <;> cases b1 <;> cases b2
        all_goals
          first
          | (left; constructor <;> rfl)
          | (right; left; constructor <;> rfl)
          | (right; right; constructor <;> rfl)
          | exact absurd (hle ![true, false, false] (by rfl)) (by decide)
          | exact absurd (hle ![false, true, false] (by rfl)) (by decide)
          | exact absurd (hle ![false, false, true] (by rfl)) (by decide)

private lemma maj3_le_two_at_most_one (a : DMFormula 3) (ha : a.leaves ≤ 2)
    (hle : ∀ y : Fin 3 → Bool, maj3 y = true → a.eval y = true) :
    (a.eval ![true, false, false] = true ∧ a.eval ![false, true, false] = true) ∨
    (a.eval ![true, false, false] = true ∧ a.eval ![false, false, true] = true) ∨
    (a.eval ![false, true, false] = true ∧ a.eval ![false, false, true] = true) := by
  cases a with
  | lit i b => exact absurd hle (maj3_not_le_lit i b)
  | and a1 a2 =>
    have h1 := leaves_pos a1
    have h2 := leaves_pos a2
    simp only [DMFormula.leaves] at ha
    cases a1 with
    | lit i b =>
      exfalso
      apply maj3_not_le_lit i b
      intro y hy
      have h := hle y hy
      simp only [DMFormula.eval, Bool.and_eq_true] at h
      exact h.1
    | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
    | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
  | or a1 a2 =>
    have h1 := leaves_pos a1
    have h2 := leaves_pos a2
    simp only [DMFormula.leaves] at ha
    cases a1 with
    | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
    | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
    | lit i1 b1 =>
      cases a2 with
      | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
      | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves] at ha; omega
      | lit i2 b2 =>
        fin_cases i1 <;> fin_cases i2 <;> cases b1 <;> cases b2
        all_goals
          first
          | (left; constructor <;> rfl)
          | (right; left; constructor <;> rfl)
          | (right; right; constructor <;> rfl)
          | exact absurd (hle ![true, true, false] (by rfl)) (by decide)
          | exact absurd (hle ![true, false, true] (by rfl)) (by decide)
          | exact absurd (hle ![false, true, true] (by rfl)) (by decide)

private lemma maj3_leaves_ge_5 (φ : DMFormula 3) (heval : ∀ y, φ.eval y = maj3 y) :
    5 ≤ φ.leaves := by
  by_contra hlt
  have hle4 : φ.leaves ≤ 4 := by omega
  cases φ with
  | lit i b =>
    exact lit_not_le_maj3 i b (fun y hy => (heval y).symm.trans hy)
  | or a b =>
    simp only [DMFormula.leaves] at hle4
    have ha_le : ∀ y, a.eval y = true → maj3 y = true := fun y hy => by
      rw [← heval y]; simp [DMFormula.eval, hy]
    have hb_le : ∀ y, b.eval y = true → maj3 y = true := fun y hy => by
      rw [← heval y]; simp [DMFormula.eval, hy]
    have ha_ge2 : 2 ≤ a.leaves := by
      cases a with
      | lit i b0 => exact absurd ha_le (lit_not_le_maj3 i b0)
      | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves]; omega
      | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves]; omega
    have hb_ge2 : 2 ≤ b.leaves := by
      cases b with
      | lit i b0 => exact absurd hb_le (lit_not_le_maj3 i b0)
      | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves]; omega
      | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves]; omega
    have ha2 : a.leaves ≤ 2 := by omega
    have hb2 : b.leaves ≤ 2 := by omega
    have ca := two_le_maj3_at_most_one a ha2 ha_le
    have cb := two_le_maj3_at_most_one b hb2 hb_le
    have h110 : (DMFormula.or a b).eval ![true, true, false] = true := heval ![true, true, false]
    have h101 : (DMFormula.or a b).eval ![true, false, true] = true := heval ![true, false, true]
    have h011 : (DMFormula.or a b).eval ![false, true, true] = true := heval ![false, true, true]
    simp only [DMFormula.eval, Bool.or_eq_true] at h110 h101 h011
    rcases ca with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases cb with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2⟩ <;>
    simp_all
  | and a b =>
    simp only [DMFormula.leaves] at hle4
    have ha_ge : ∀ y, maj3 y = true → a.eval y = true := fun y hy => by
      have h := heval y
      rw [hy] at h
      simp only [DMFormula.eval, Bool.and_eq_true] at h
      exact h.1
    have hb_ge : ∀ y, maj3 y = true → b.eval y = true := fun y hy => by
      have h := heval y
      rw [hy] at h
      simp only [DMFormula.eval, Bool.and_eq_true] at h
      exact h.2
    have ha_ge2 : 2 ≤ a.leaves := by
      cases a with
      | lit i b0 => exact absurd ha_ge (maj3_not_le_lit i b0)
      | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves]; omega
      | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves]; omega
    have hb_ge2 : 2 ≤ b.leaves := by
      cases b with
      | lit i b0 => exact absurd hb_ge (maj3_not_le_lit i b0)
      | and x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves]; omega
      | or x1 x2 => have := leaves_pos x1; have := leaves_pos x2; simp [DMFormula.leaves]; omega
    have ha2 : a.leaves ≤ 2 := by omega
    have hb2 : b.leaves ≤ 2 := by omega
    have ca := maj3_le_two_at_most_one a ha2 ha_ge
    have cb := maj3_le_two_at_most_one b hb2 hb_ge
    have h100 : (DMFormula.and a b).eval ![true, false, false] = false := heval ![true, false, false]
    have h010 : (DMFormula.and a b).eval ![false, true, false] = false := heval ![false, true, false]
    have h001 : (DMFormula.and a b).eval ![false, false, true] = false := heval ![false, false, true]
    simp only [DMFormula.eval, Bool.and_eq_false_iff] at h100 h010 h001
    rcases ca with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases cb with ⟨g1, g2⟩ | ⟨g1, g2⟩ | ⟨g1, g2⟩ <;>
    simp_all

private lemma paw_leaves_ge_6 (φ : DMFormula 4) (heval : ∀ x, φ.eval x = paw x) :
    6 ≤ φ.leaves := by
  have hc3 : 1 ≤ countVar3 φ := by
    by_contra h0
    have hzero : countVar3 φ = 0 := by omega
    have hsame := eval_indep_of_countVar3_zero φ hzero
      ![true, false, false, false] ![true, false, false, true] (by
        intro i hi
        fin_cases i <;> first | rfl | exact absurd rfl hi)
    rw [heval, heval] at hsame
    simp [paw] at hsame
  cases hsub : subst3 φ with
  | inl b =>
    have h0 := subst3_eval φ ![false, false, false]
    have h1 := subst3_eval φ ![true, true, false]
    rw [hsub, heval] at h0 h1
    simp [ext3, paw] at h0 h1
    rw [h0] at h1
    cases h1
  | inr ψ =>
    have hψ_eval : ∀ y : Fin 3 → Bool, ψ.eval y = maj3 y := by
      intro y
      have h := subst3_eval φ y
      rw [hsub, heval] at h
      dsimp only at h
      rw [h]
      simp [ext3, paw, maj3]
    have h5 : 5 ≤ ψ.leaves := maj3_leaves_ge_5 ψ hψ_eval
    have hle : ψ.leaves + countVar3 φ ≤ φ.leaves := subst3_leaves φ ψ hsub
    omega

end PEqualNP.Outside.L_meta_184_aux

theorem PEqualNP.Outside.L_meta_184 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3)) s ↔ 6 ≤ s := by
  intro s
  constructor
  · rintro ⟨φ, hle, heval⟩
    have h6 := PEqualNP.Outside.L_meta_184_aux.paw_leaves_ge_6 φ heval
    omega
  · intro hs
    exact ⟨PEqualNP.Outside.L_meta_184_aux.pawFormula,
      by rw [PEqualNP.Outside.L_meta_184_aux.pawFormula_leaves]; exact hs,
      PEqualNP.Outside.L_meta_184_aux.pawFormula_eval⟩
