import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_261

open PEqualNP.MetaComplexity

variable {n : ℕ}

noncomputable def cnt (i : Fin n) (ψ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) ψ

def P (φ : DMFormula n) : Prop :=
  PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (_ : Fin n) (_ : Bool) => False) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) φ

def rv : DMFormula n ⊕ Bool → (Fin n → Bool) → Bool
  | Sum.inl f, x => f.eval x
  | Sum.inr b, _ => b

def lv : DMFormula n ⊕ Bool → ℕ
  | Sum.inl f => f.leaves
  | Sum.inr _ => 0

lemma rv_inl (f : DMFormula n) (x : Fin n → Bool) : rv (Sum.inl f) x = f.eval x := rfl

lemma lv_inl (f : DMFormula n) : lv (Sum.inl f) = f.leaves := rfl

lemma lv_inr (b : Bool) : lv (n := n) (Sum.inr b) = 0 := rfl

def mkAnd : DMFormula n ⊕ Bool → DMFormula n ⊕ Bool → DMFormula n ⊕ Bool
  | Sum.inr false, _ => Sum.inr false
  | Sum.inr true, r => r
  | Sum.inl _, Sum.inr false => Sum.inr false
  | Sum.inl f, Sum.inr true => Sum.inl f
  | Sum.inl f, Sum.inl g => Sum.inl (DMFormula.and f g)

def mkOr : DMFormula n ⊕ Bool → DMFormula n ⊕ Bool → DMFormula n ⊕ Bool
  | Sum.inr true, _ => Sum.inr true
  | Sum.inr false, r => r
  | Sum.inl _, Sum.inr true => Sum.inr true
  | Sum.inl f, Sum.inr false => Sum.inl f
  | Sum.inl f, Sum.inl g => Sum.inl (DMFormula.or f g)

lemma rv_mkAnd (r s : DMFormula n ⊕ Bool) (x : Fin n → Bool) :
    rv (mkAnd r s) x = (rv r x && rv s x) := by
  rcases r with f | (_ | _) <;> rcases s with g | (_ | _) <;> simp [mkAnd, rv, DMFormula.eval]

lemma rv_mkOr (r s : DMFormula n ⊕ Bool) (x : Fin n → Bool) :
    rv (mkOr r s) x = (rv r x || rv s x) := by
  rcases r with f | (_ | _) <;> rcases s with g | (_ | _) <;> simp [mkOr, rv, DMFormula.eval]

lemma lv_mkAnd (r s : DMFormula n ⊕ Bool) : lv (mkAnd r s) ≤ lv r + lv s := by
  rcases r with f | (_ | _) <;> rcases s with g | (_ | _) <;> simp [mkAnd, lv, DMFormula.leaves]

lemma lv_mkOr (r s : DMFormula n ⊕ Bool) : lv (mkOr r s) ≤ lv r + lv s := by
  rcases r with f | (_ | _) <;> rcases s with g | (_ | _) <;> simp [mkOr, lv, DMFormula.leaves]

def restrict (i : Fin n) (c : Bool) : DMFormula n → DMFormula n ⊕ Bool
  | DMFormula.lit j b => if j = i then Sum.inr (if b then c else !c) else Sum.inl (DMFormula.lit j b)
  | DMFormula.and A B => mkAnd (restrict i c A) (restrict i c B)
  | DMFormula.or A B => mkOr (restrict i c A) (restrict i c B)

lemma restrict_eval (i : Fin n) (c : Bool) (x : Fin n → Bool) (hx : x i = c) :
    ∀ ψ : DMFormula n, rv (restrict i c ψ) x = ψ.eval x := by
  intro ψ
  induction ψ with
  | lit j b =>
    by_cases hj : j = i
    · subst hj
      simp [restrict, rv, DMFormula.eval, hx]
    · simp [restrict, rv, hj]
  | and A B ihA ihB => simp [restrict, rv_mkAnd, ihA, ihB, DMFormula.eval]
  | or A B ihA ihB => simp [restrict, rv_mkOr, ihA, ihB, DMFormula.eval]

lemma restrict_lv (i : Fin n) (c : Bool) :
    ∀ ψ : DMFormula n, lv (restrict i c ψ) + cnt i ψ ≤ ψ.leaves := by
  intro ψ
  induction ψ with
  | lit j b =>
    by_cases hj : j = i
    · simp [restrict, lv, cnt, hj, DMFormula.leaves]
    · simp [restrict, lv, cnt, hj, DMFormula.leaves]
  | and A B ihA ihB =>
    have h := lv_mkAnd (restrict i c A) (restrict i c B)
    have e : cnt i (DMFormula.and A B) = cnt i A + cnt i B := rfl
    simp only [restrict, DMFormula.leaves, e]
    omega
  | or A B ihA ihB =>
    have h := lv_mkOr (restrict i c A) (restrict i c B)
    have e : cnt i (DMFormula.or A B) = cnt i A + cnt i B := rfl
    simp only [restrict, DMFormula.leaves, e]
    omega

lemma leaves_pos (ψ : DMFormula n) : 1 ≤ ψ.leaves := by
  induction ψ with
  | lit j b => simp [DMFormula.leaves]
  | and A B ihA _ => simp only [DMFormula.leaves]; omega
  | or A B ihA _ => simp only [DMFormula.leaves]; omega

lemma lit_true (i : Fin n) (b : Bool) (x : Fin n → Bool)
    (h : (DMFormula.lit i b).eval x = true) : x i = b := by
  cases b <;> cases hx : x i <;> simp_all [DMFormula.eval]

lemma lit_false (i : Fin n) (b : Bool) (x : Fin n → Bool)
    (h : (DMFormula.lit i b).eval x = false) : x i = !b := by
  cases b <;> cases hx : x i <;> simp_all [DMFormula.eval]

lemma main : ∀ φ : DMFormula n, P φ →
    ∃ R : DMFormula n ⊕ Bool, (∀ x, rv R x = φ.eval x) ∧ lv R < φ.leaves := by
  intro φ
  induction φ with
  | lit j b => intro h; exact h.elim
  | and A B ihA ihB =>
    intro hP
    obtain h | h | ⟨i, hA, hB⟩ | ⟨i, hB, hA⟩ := hP
    · obtain ⟨R, hR, hl⟩ := ihA h
      refine ⟨mkAnd R (Sum.inl B), fun x => ?_, ?_⟩
      · rw [rv_mkAnd, hR, rv_inl]; rfl
      · have := lv_mkAnd R (Sum.inl B)
        rw [lv_inl] at this
        simp only [DMFormula.leaves]
        omega
    · obtain ⟨R, hR, hl⟩ := ihB h
      refine ⟨mkAnd (Sum.inl A) R, fun x => ?_, ?_⟩
      · rw [rv_mkAnd, hR, rv_inl]; rfl
      · have := lv_mkAnd (Sum.inl A) R
        rw [lv_inl] at this
        simp only [DMFormula.leaves]
        omega
    · cases A with
      | and _ _ => exact hA.elim
      | or _ _ => exact hA.elim
      | lit j b =>
        have hj : j = i := hA
        subst hj
        have hc : 1 ≤ cnt j B := hB
        refine ⟨mkAnd (Sum.inl (DMFormula.lit j b)) (restrict j b B), fun x => ?_, ?_⟩
        · rw [rv_mkAnd, rv_inl]
          show ((DMFormula.lit j b).eval x && rv (restrict j b B) x) = ((DMFormula.lit j b).eval x && B.eval x)
          cases hl : (DMFormula.lit j b).eval x
          · rfl
          · rw [restrict_eval j b x (lit_true j b x hl)]
        · have h1 := lv_mkAnd (Sum.inl (DMFormula.lit j b)) (restrict j b B)
          have h2 := restrict_lv j b B
          rw [lv_inl] at h1
          simp only [DMFormula.leaves] at h1
          simp only [DMFormula.leaves]
          omega
    · cases B with
      | and _ _ => exact hB.elim
      | or _ _ => exact hB.elim
      | lit j b =>
        have hj : j = i := hB
        subst hj
        have hc : 1 ≤ cnt j A := hA
        refine ⟨mkAnd (restrict j b A) (Sum.inl (DMFormula.lit j b)), fun x => ?_, ?_⟩
        · rw [rv_mkAnd, rv_inl]
          show (rv (restrict j b A) x && (DMFormula.lit j b).eval x) = (A.eval x && (DMFormula.lit j b).eval x)
          cases hl : (DMFormula.lit j b).eval x
          · simp only [Bool.and_false]
          · rw [restrict_eval j b x (lit_true j b x hl)]
        · have h1 := lv_mkAnd (restrict j b A) (Sum.inl (DMFormula.lit j b))
          have h2 := restrict_lv j b A
          rw [lv_inl] at h1
          simp only [DMFormula.leaves] at h1
          simp only [DMFormula.leaves]
          omega
  | or A B ihA ihB =>
    intro hP
    obtain h | h | ⟨i, hA, hB⟩ | ⟨i, hB, hA⟩ := hP
    · obtain ⟨R, hR, hl⟩ := ihA h
      refine ⟨mkOr R (Sum.inl B), fun x => ?_, ?_⟩
      · rw [rv_mkOr, hR, rv_inl]; rfl
      · have := lv_mkOr R (Sum.inl B)
        rw [lv_inl] at this
        simp only [DMFormula.leaves]
        omega
    · obtain ⟨R, hR, hl⟩ := ihB h
      refine ⟨mkOr (Sum.inl A) R, fun x => ?_, ?_⟩
      · rw [rv_mkOr, hR, rv_inl]; rfl
      · have := lv_mkOr (Sum.inl A) R
        rw [lv_inl] at this
        simp only [DMFormula.leaves]
        omega
    · cases A with
      | and _ _ => exact hA.elim
      | or _ _ => exact hA.elim
      | lit j b =>
        have hj : j = i := hA
        subst hj
        have hc : 1 ≤ cnt j B := hB
        refine ⟨mkOr (Sum.inl (DMFormula.lit j b)) (restrict j (!b) B), fun x => ?_, ?_⟩
        · rw [rv_mkOr, rv_inl]
          show ((DMFormula.lit j b).eval x || rv (restrict j (!b) B) x) = ((DMFormula.lit j b).eval x || B.eval x)
          cases hl : (DMFormula.lit j b).eval x
          · rw [restrict_eval j (!b) x (lit_false j b x hl)]
          · rfl
        · have h1 := lv_mkOr (Sum.inl (DMFormula.lit j b)) (restrict j (!b) B)
          have h2 := restrict_lv j (!b) B
          rw [lv_inl] at h1
          simp only [DMFormula.leaves] at h1
          simp only [DMFormula.leaves]
          omega
    · cases B with
      | and _ _ => exact hB.elim
      | or _ _ => exact hB.elim
      | lit j b =>
        have hj : j = i := hB
        subst hj
        have hc : 1 ≤ cnt j A := hA
        refine ⟨mkOr (restrict j (!b) A) (Sum.inl (DMFormula.lit j b)), fun x => ?_, ?_⟩
        · rw [rv_mkOr, rv_inl]
          show (rv (restrict j (!b) A) x || (DMFormula.lit j b).eval x) = (A.eval x || (DMFormula.lit j b).eval x)
          cases hl : (DMFormula.lit j b).eval x
          · rw [restrict_eval j (!b) x (lit_false j b x hl)]
          · simp only [Bool.or_true]
        · have h1 := lv_mkOr (restrict j (!b) A) (Sum.inl (DMFormula.lit j b))
          have h2 := restrict_lv j (!b) A
          rw [lv_inl] at h1
          simp only [DMFormula.leaves] at h1
          simp only [DMFormula.leaves]
          omega

end PEqualNP.Outside.L_meta_261

theorem PEqualNP.Outside.L_meta_261 : ∀ (n : ℕ) (φ : PEqualNP.MetaComplexity.DMFormula n), (∃ x y : Fin n → Bool, φ.eval x ≠ φ.eval y) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (_ : Fin n) (_ : Bool) => False) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) φ → ∃ ψ : PEqualNP.MetaComplexity.DMFormula n, ψ.leaves < φ.leaves ∧ ∀ x : Fin n → Bool, ψ.eval x = φ.eval x := by
  intro n φ hnc hP
  obtain ⟨R, hR, hl⟩ := PEqualNP.Outside.L_meta_261.main φ hP
  rcases R with ψ | b
  · exact ⟨ψ, hl, hR⟩
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hR x, ← hR y]
    rfl
