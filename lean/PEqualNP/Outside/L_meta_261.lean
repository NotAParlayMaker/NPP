import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_261
open PEqualNP.MetaComplexity

noncomputable def count {n : ℕ} (i : Fin n) : DMFormula n → ℕ :=
  DMFormula.rec (fun j _ => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q)

def isLit {n : ℕ} (i : Fin n) : DMFormula n → Prop :=
  DMFormula.rec (fun j _ => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False)

def bad {n : ℕ} : DMFormula n → Prop :=
  DMFormula.rec (fun _ _ => False)
    (fun A B p q => p ∨ q ∨
      (∃ i, isLit i A ∧ 1 ≤ count i B) ∨ (∃ i, isLit i B ∧ 1 ≤ count i A))
    (fun A B p q => p ∨ q ∨
      (∃ i, isLit i A ∧ 1 ≤ count i B) ∨ (∃ i, isLit i B ∧ 1 ≤ count i A))

def join {n : ℕ} (o : Bool) (A B : DMFormula n) : DMFormula n :=
  if o then .and A B else .or A B

def op (o a b : Bool) : Bool := if o then a && b else a || b

lemma join_eval {n : ℕ} (o : Bool) (A B : DMFormula n) (x : Fin n → Bool) :
    (join o A B).eval x = op o (A.eval x) (B.eval x) := by
  cases o <;> rfl

lemma join_leaves {n : ℕ} (o : Bool) (A B : DMFormula n) :
    (join o A B).leaves = A.leaves + B.leaves := by
  cases o <;> rfl

lemma join_count {n : ℕ} (o : Bool) (i : Fin n) (A B : DMFormula n) :
    count i (join o A B) = count i A + count i B := by
  cases o <;> rfl

lemma op_left (o a b : Bool) : op o a b = if a = o then b else a := by
  cases o <;> cases a <;> cases b <;> rfl

lemma op_right (o a b : Bool) : op o a b = if b = o then a else b := by
  cases o <;> cases a <;> cases b <;> rfl

lemma op_comm (o a b : Bool) : op o a b = op o b a := by
  cases o <;> cases a <;> cases b <;> rfl

lemma op_restrict (o a b c : Bool) (h : a = o → b = c) : op o a b = op o a c := by
  cases o <;> cases a <;> simp_all [op]

lemma leaves_pos {n : ℕ} (A : DMFormula n) : 0 < A.leaves := by
  induction A <;> simp_all [DMFormula.leaves]

lemma count_le {n : ℕ} (i : Fin n) (A : DMFormula n) : count i A ≤ A.leaves := by
  induction A with
  | lit j b => by_cases h : j = i <;> simp [count, DMFormula.leaves, h]
  | and A B hA hB => simp_all [count, DMFormula.leaves]; omega
  | or A B hA hB => simp_all [count, DMFormula.leaves]; omega

def Restriction {n : ℕ} (A : DMFormula n) (i : Fin n) (v : Bool) : Prop :=
  (∃ c : Bool, ∀ x, x i = v → A.eval x = c) ∨
  ∃ B : DMFormula n, B.leaves + count i A ≤ A.leaves ∧
    ∀ x, x i = v → B.eval x = A.eval x

lemma restrict_join {n : ℕ} (o : Bool) (A B : DMFormula n) (i : Fin n) (v : Bool)
    (hA : Restriction A i v) (hB : Restriction B i v) : Restriction (join o A B) i v := by
  rcases hA with ⟨a, ha⟩ | ⟨A', hAs, hAe⟩
  · by_cases hao : a = o
    · rcases hB with ⟨b, hb⟩ | ⟨B', hBs, hBe⟩
      · exact Or.inl ⟨b, fun x hx => by rw [join_eval, ha x hx, op_left, ite_eq_left hao, hb x hx]⟩
      · refine Or.inr ⟨B', ?_, ?_⟩
        · rw [join_count, join_leaves]
          have := count_le i A
          omega
        · intro x hx
          rw [join_eval, ha x hx, op_left, ite_eq_left hao]
          exact hBe x hx
    · exact Or.inl ⟨a, fun x hx => by rw [join_eval, ha x hx, op_left, ite_eq_right hao]⟩
  · rcases hB with ⟨b, hb⟩ | ⟨B', hBs, hBe⟩
    · by_cases hbo : b = o
      · refine Or.inr ⟨A', ?_, ?_⟩
        · rw [join_count, join_leaves]
          have := count_le i B
          omega
        · intro x hx
          rw [join_eval, hb x hx, op_right, ite_eq_left hbo]
          exact hAe x hx
      · exact Or.inl ⟨b, fun x hx => by rw [join_eval, hb x hx, op_right, ite_eq_right hbo]⟩
    · refine Or.inr ⟨join o A' B', ?_, ?_⟩
      · rw [join_count, join_leaves, join_leaves]
        omega
      · intro x hx
        rw [join_eval, join_eval, hAe x hx, hBe x hx]

lemma restrict_exists {n : ℕ} (A : DMFormula n) (i : Fin n) (v : Bool) :
    Restriction A i v := by
  induction A with
  | lit j b =>
    by_cases h : j = i
    · subst j
      exact Or.inl ⟨if b then v else !v, fun x hx => by simp [DMFormula.eval, hx]⟩
    · exact Or.inr ⟨.lit j b, by simp [count, h], fun _ _ => rfl⟩
  | and A B hA hB => exact restrict_join true A B i v hA hB
  | or A B hA hB => exact restrict_join false A B i v hA hB

def Nonconstant {n : ℕ} (A : DMFormula n) : Prop := ∃ x y, A.eval x ≠ A.eval y

def Reduced {n : ℕ} (A : DMFormula n) : Prop :=
  ∃ B : DMFormula n, B.leaves < A.leaves ∧ ∀ x, B.eval x = A.eval x

lemma reduce_lit {n : ℕ} (o b : Bool) (i : Fin n) (B : DMFormula n)
    (hc : 1 ≤ count i B) (hn : Nonconstant (join o (.lit i b) B)) :
    Reduced (join o (.lit i b) B) := by
  let v := if b then o else !o
  have hv (x : Fin n → Bool) : (DMFormula.lit i b).eval x = o ↔ x i = v := by
    cases b <;> cases o <;> simp [v, DMFormula.eval]
  rcases restrict_exists B i v with ⟨c, he⟩ | ⟨B', hs, he⟩
  · have heq (x : Fin n → Bool) :
        (join o (.lit i b) B).eval x = op o ((DMFormula.lit i b).eval x) c := by
      rw [join_eval]
      apply op_restrict
      exact fun h => he x ((hv x).mp h)
    by_cases hco : c = o
    · refine ⟨.lit i b, ?_, ?_⟩
      · rw [join_leaves]
        have := leaves_pos B
        omega
      · intro x
        rw [heq, op_right, ite_eq_left hco]
    · rcases hn with ⟨x, y, hxy⟩
      exact False.elim (hxy (by rw [heq, heq, op_right, op_right, ite_eq_right hco, ite_eq_right hco]))
  · refine ⟨join o (.lit i b) B', ?_, ?_⟩
    · rw [join_leaves, join_leaves]
      omega
    · intro x
      rw [join_eval, join_eval]
      apply op_restrict
      exact fun h => he x ((hv x).mp h)

lemma join_swap {n : ℕ} (o : Bool) (A B : DMFormula n) (x : Fin n → Bool) :
    (join o A B).eval x = (join o B A).eval x := by
  rw [join_eval, join_eval, op_comm]

lemma nonconstant_swap {n : ℕ} (o : Bool) (A B : DMFormula n)
    (h : Nonconstant (join o A B)) : Nonconstant (join o B A) := by
  rcases h with ⟨x, y, hxy⟩
  refine ⟨x, y, ?_⟩
  rw [join_swap o B A x, join_swap o B A y]
  exact hxy

lemma reduced_swap {n : ℕ} (o : Bool) (A B : DMFormula n)
    (h : Reduced (join o B A)) : Reduced (join o A B) := by
  rcases h with ⟨C, hs, he⟩
  refine ⟨C, ?_, ?_⟩
  · rw [join_leaves] at hs ⊢
    omega
  · intro x
    rw [he x, join_swap]

lemma reduce_const_left {n : ℕ} (o : Bool) (A B : DMFormula n)
    (hc : ¬ Nonconstant A) (hn : Nonconstant (join o A B)) :
    Reduced (join o A B) := by
  obtain ⟨x, y, hxy⟩ := hn
  have he (z : Fin n → Bool) : A.eval z = A.eval x := by
    by_contra h
    exact hc ⟨z, x, h⟩
  have ho : A.eval x = o := by
    by_contra h
    apply hxy
    rw [join_eval, join_eval, he y, op_left, op_left, ite_eq_right h, ite_eq_right h]
  refine ⟨B, ?_, ?_⟩
  · rw [join_leaves]
    have := leaves_pos A
    omega
  · intro z
    rw [join_eval, he z, op_left, ite_eq_left ho]

lemma reduce_join {n : ℕ} (o : Bool) (A B : DMFormula n)
    (hA : Nonconstant A → bad A → Reduced A)
    (hB : Nonconstant B → bad B → Reduced B)
    (hn : Nonconstant (join o A B))
    (hb : bad A ∨ bad B ∨ (∃ i, isLit i A ∧ 1 ≤ count i B) ∨
      (∃ i, isLit i B ∧ 1 ≤ count i A)) : Reduced (join o A B) := by
  by_cases hna : Nonconstant A
  · by_cases hnb : Nonconstant B
    · rcases hb with ha | hb | ⟨i, hi, hc⟩ | ⟨i, hi, hc⟩
      · obtain ⟨A', hs, he⟩ := hA hna ha
        refine ⟨join o A' B, ?_, ?_⟩
        · rw [join_leaves, join_leaves]
          omega
        · intro x
          rw [join_eval, join_eval, he x]
      · obtain ⟨B', hs, he⟩ := hB hnb hb
        refine ⟨join o A B', ?_, ?_⟩
        · rw [join_leaves, join_leaves]
          omega
        · intro x
          rw [join_eval, join_eval, he x]
      · cases A with
        | lit j b =>
          change j = i at hi
          subst j
          exact reduce_lit o b i B hc hn
        | and A₁ A₂ => exact hi.elim
        | or A₁ A₂ => exact hi.elim
      · apply reduced_swap
        have hn' := nonconstant_swap o A B hn
        cases B with
        | lit j b =>
          change j = i at hi
          subst j
          exact reduce_lit o b i A hc hn'
        | and B₁ B₂ => exact hi.elim
        | or B₁ B₂ => exact hi.elim
    · exact reduced_swap o A B (reduce_const_left o B A hnb (nonconstant_swap o A B hn))
  · exact reduce_const_left o A B hna hn

lemma reduce {n : ℕ} (A : DMFormula n) : Nonconstant A → bad A → Reduced A := by
  induction A with
  | lit i b => intro _ h; exact h.elim
  | and A B hA hB => exact reduce_join true A B hA hB
  | or A B hA hB => exact reduce_join false A B hA hB

end PEqualNP.Outside.L_meta_261

theorem PEqualNP.Outside.L_meta_261 : ∀ (n : ℕ) (φ : PEqualNP.MetaComplexity.DMFormula n), (∃ x y : Fin n → Bool, φ.eval x ≠ φ.eval y) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (_ : Fin n) (_ : Bool) => False) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) (fun A B p q => p ∨ q ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) A ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) B) ∨ (∃ i : Fin n, PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => Prop) (fun (j : Fin n) (_ : Bool) => j = i) (fun _ _ _ _ => False) (fun _ _ _ _ => False) B ∧ 1 ≤ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) A)) φ → ∃ ψ : PEqualNP.MetaComplexity.DMFormula n, ψ.leaves < φ.leaves ∧ ∀ x : Fin n → Bool, ψ.eval x = φ.eval x := by
  intro n φ hn hb
  exact PEqualNP.Outside.L_meta_261.reduce φ hn hb
