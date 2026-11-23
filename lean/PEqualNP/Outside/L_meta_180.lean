import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_180

private def append {n k : ℕ} (x : Fin n → Bool) (y : Fin k → Bool) (idx : Fin (n + k)) : Bool :=
  if h : idx.val < n then x ⟨idx.val, h⟩ else y ⟨idx.val - n, by omega⟩

private lemma append_castAdd {n k : ℕ} (x : Fin n → Bool) (y : Fin k → Bool) (i : Fin n) :
    append x y (Fin.castAdd k i) = x i := by
  simp [append]

private lemma append_natAdd {n k : ℕ} (x : Fin n → Bool) (y : Fin k → Bool) (j : Fin k) :
    append x y (Fin.natAdd n j) = y j := by
  have h : ¬ n + j.val < n := by omega
  simp [append, h]

private def liftLeft {n k : ℕ} : DMFormula n → DMFormula (n + k)
  | DMFormula.lit i b => DMFormula.lit (Fin.castAdd k i) b
  | DMFormula.and φ ψ => DMFormula.and (liftLeft φ) (liftLeft ψ)
  | DMFormula.or φ ψ => DMFormula.or (liftLeft φ) (liftLeft ψ)

private lemma liftLeft_leaves {n k : ℕ} (φ : DMFormula n) :
    (liftLeft (k := k) φ).leaves = φ.leaves := by
  induction φ with
  | lit _ _ => rfl
  | and φ ψ ih1 ih2 => simp [liftLeft, DMFormula.leaves, ih1, ih2]
  | or φ ψ ih1 ih2 => simp [liftLeft, DMFormula.leaves, ih1, ih2]

private lemma liftLeft_eval {n k : ℕ} (φ : DMFormula n) (z : Fin (n + k) → Bool) :
    (liftLeft (k := k) φ).eval z = φ.eval (fun i => z (Fin.castAdd k i)) := by
  induction φ with
  | lit i b => simp [liftLeft, DMFormula.eval]
  | and φ ψ ih1 ih2 => simp [liftLeft, DMFormula.eval, ih1, ih2]
  | or φ ψ ih1 ih2 => simp [liftLeft, DMFormula.eval, ih1, ih2]

private def liftRight {n k : ℕ} : DMFormula k → DMFormula (n + k)
  | DMFormula.lit j b => DMFormula.lit (Fin.natAdd n j) b
  | DMFormula.and φ ψ => DMFormula.and (liftRight φ) (liftRight ψ)
  | DMFormula.or φ ψ => DMFormula.or (liftRight φ) (liftRight ψ)

private lemma liftRight_leaves {n k : ℕ} (ψ : DMFormula k) :
    (liftRight (n := n) ψ).leaves = ψ.leaves := by
  induction ψ with
  | lit _ _ => rfl
  | and φ ψ ih1 ih2 => simp [liftRight, DMFormula.leaves, ih1, ih2]
  | or φ ψ ih1 ih2 => simp [liftRight, DMFormula.leaves, ih1, ih2]

private lemma liftRight_eval {n k : ℕ} (ψ : DMFormula k) (z : Fin (n + k) → Bool) :
    (liftRight (n := n) ψ).eval z = ψ.eval (fun j => z (Fin.natAdd n j)) := by
  induction ψ with
  | lit j b => simp [liftRight, DMFormula.eval]
  | and φ ψ ih1 ih2 => simp [liftRight, DMFormula.eval, ih1, ih2]
  | or φ ψ ih1 ih2 => simp [liftRight, DMFormula.eval, ih1, ih2]

private def leftLeaves {n k : ℕ} : DMFormula (n + k) → ℕ
  | DMFormula.lit idx _ => if idx.val < n then 1 else 0
  | DMFormula.and φ ψ => leftLeaves φ + leftLeaves ψ
  | DMFormula.or φ ψ => leftLeaves φ + leftLeaves ψ

private def rightLeaves {n k : ℕ} : DMFormula (n + k) → ℕ
  | DMFormula.lit idx _ => if idx.val < n then 0 else 1
  | DMFormula.and φ ψ => rightLeaves φ + rightLeaves ψ
  | DMFormula.or φ ψ => rightLeaves φ + rightLeaves ψ

private lemma leftLeaves_add_rightLeaves {n k : ℕ} (φ : DMFormula (n + k)) :
    leftLeaves φ + rightLeaves φ = φ.leaves := by
  induction φ with
  | lit idx _ =>
    by_cases h : idx.val < n <;> simp [leftLeaves, rightLeaves, DMFormula.leaves, h]
  | and φ ψ ih1 ih2 =>
    simp only [leftLeaves, rightLeaves, DMFormula.leaves]
    omega
  | or φ ψ ih1 ih2 =>
    simp only [leftLeaves, rightLeaves, DMFormula.leaves]
    omega

private def combineAnd {m : ℕ} : Sum Bool (DMFormula m) → Sum Bool (DMFormula m) → Sum Bool (DMFormula m)
  | Sum.inl false, _ => Sum.inl false
  | _, Sum.inl false => Sum.inl false
  | Sum.inl true, r => r
  | r, Sum.inl true => r
  | Sum.inr φ, Sum.inr ψ => Sum.inr (DMFormula.and φ ψ)

private def combineOr {m : ℕ} : Sum Bool (DMFormula m) → Sum Bool (DMFormula m) → Sum Bool (DMFormula m)
  | Sum.inl true, _ => Sum.inl true
  | _, Sum.inl true => Sum.inl true
  | Sum.inl false, r => r
  | r, Sum.inl false => r
  | Sum.inr φ, Sum.inr ψ => Sum.inr (DMFormula.or φ ψ)

private def evalRes {m : ℕ} (x : Fin m → Bool) : Sum Bool (DMFormula m) → Bool
  | Sum.inl b => b
  | Sum.inr φ => φ.eval x

private def resLeaves {m : ℕ} : Sum Bool (DMFormula m) → ℕ
  | Sum.inl _ => 0
  | Sum.inr φ => φ.leaves

private lemma evalRes_combineAnd {m : ℕ} (x : Fin m → Bool) (r1 r2 : Sum Bool (DMFormula m)) :
    evalRes x (combineAnd r1 r2) = (evalRes x r1 && evalRes x r2) := by
  cases r1 with
  | inl b1 =>
    cases b1 <;> cases r2 with
    | inl b2 => cases b2 <;> rfl
    | inr ψ => simp [combineAnd, evalRes]
  | inr φ =>
    cases r2 with
    | inl b2 => cases b2 <;> simp [combineAnd, evalRes]
    | inr ψ => rfl

private lemma evalRes_combineOr {m : ℕ} (x : Fin m → Bool) (r1 r2 : Sum Bool (DMFormula m)) :
    evalRes x (combineOr r1 r2) = (evalRes x r1 || evalRes x r2) := by
  cases r1 with
  | inl b1 =>
    cases b1 <;> cases r2 with
    | inl b2 => cases b2 <;> rfl
    | inr ψ => simp [combineOr, evalRes]
  | inr φ =>
    cases r2 with
    | inl b2 => cases b2 <;> simp [combineOr, evalRes]
    | inr ψ => rfl

private lemma resLeaves_combineAnd {m : ℕ} (r1 r2 : Sum Bool (DMFormula m)) :
    resLeaves (combineAnd r1 r2) ≤ resLeaves r1 + resLeaves r2 := by
  cases r1 with
  | inl b1 =>
    cases b1 <;> cases r2 with
    | inl b2 => cases b2 <;> simp [combineAnd, resLeaves]
    | inr ψ => simp [combineAnd, resLeaves]
  | inr φ =>
    cases r2 with
    | inl b2 => cases b2 <;> simp [combineAnd, resLeaves]
    | inr ψ => simp [combineAnd, resLeaves, DMFormula.leaves]

private lemma resLeaves_combineOr {m : ℕ} (r1 r2 : Sum Bool (DMFormula m)) :
    resLeaves (combineOr r1 r2) ≤ resLeaves r1 + resLeaves r2 := by
  cases r1 with
  | inl b1 =>
    cases b1 <;> cases r2 with
    | inl b2 => cases b2 <;> simp [combineOr, resLeaves]
    | inr ψ => simp [combineOr, resLeaves]
  | inr φ =>
    cases r2 with
    | inl b2 => cases b2 <;> simp [combineOr, resLeaves]
    | inr ψ => simp [combineOr, resLeaves, DMFormula.leaves]

private def restrictLeft {n k : ℕ} (y : Fin k → Bool) : DMFormula (n + k) → Sum Bool (DMFormula n)
  | DMFormula.lit idx b =>
    if h : idx.val < n then
      Sum.inr (DMFormula.lit ⟨idx.val, h⟩ b)
    else
      Sum.inl (if b then y ⟨idx.val - n, by omega⟩ else !(y ⟨idx.val - n, by omega⟩))
  | DMFormula.and φ ψ => combineAnd (restrictLeft y φ) (restrictLeft y ψ)
  | DMFormula.or φ ψ => combineOr (restrictLeft y φ) (restrictLeft y ψ)

private lemma evalRes_restrictLeft {n k : ℕ} (y : Fin k → Bool) (φ : DMFormula (n + k)) (x : Fin n → Bool) :
    evalRes x (restrictLeft y φ) = φ.eval (append x y) := by
  induction φ with
  | lit idx b =>
    by_cases h : idx.val < n
    · simp [restrictLeft, h, evalRes, DMFormula.eval, append]
    · simp [restrictLeft, h, evalRes, DMFormula.eval, append]
  | and φ ψ ih1 ih2 =>
    simp [restrictLeft, evalRes_combineAnd, DMFormula.eval, ih1, ih2]
  | or φ ψ ih1 ih2 =>
    simp [restrictLeft, evalRes_combineOr, DMFormula.eval, ih1, ih2]

private lemma resLeaves_restrictLeft {n k : ℕ} (y : Fin k → Bool) (φ : DMFormula (n + k)) :
    resLeaves (restrictLeft y φ) ≤ leftLeaves φ := by
  induction φ with
  | lit idx b =>
    by_cases h : idx.val < n <;> simp [restrictLeft, h, resLeaves, leftLeaves, DMFormula.leaves]
  | and φ ψ ih1 ih2 =>
    calc
      resLeaves (restrictLeft y (DMFormula.and φ ψ))
          ≤ resLeaves (restrictLeft y φ) + resLeaves (restrictLeft y ψ) := resLeaves_combineAnd _ _
      _ ≤ leftLeaves φ + leftLeaves ψ := Nat.add_le_add ih1 ih2
  | or φ ψ ih1 ih2 =>
    calc
      resLeaves (restrictLeft y (DMFormula.or φ ψ))
          ≤ resLeaves (restrictLeft y φ) + resLeaves (restrictLeft y ψ) := resLeaves_combineOr _ _
      _ ≤ leftLeaves φ + leftLeaves ψ := Nat.add_le_add ih1 ih2

private def restrictRight {n k : ℕ} (x : Fin n → Bool) : DMFormula (n + k) → Sum Bool (DMFormula k)
  | DMFormula.lit idx b =>
    if h : idx.val < n then
      Sum.inl (if b then x ⟨idx.val, h⟩ else !(x ⟨idx.val, h⟩))
    else
      Sum.inr (DMFormula.lit ⟨idx.val - n, by omega⟩ b)
  | DMFormula.and φ ψ => combineAnd (restrictRight x φ) (restrictRight x ψ)
  | DMFormula.or φ ψ => combineOr (restrictRight x φ) (restrictRight x ψ)

private lemma evalRes_restrictRight {n k : ℕ} (x : Fin n → Bool) (φ : DMFormula (n + k)) (y : Fin k → Bool) :
    evalRes y (restrictRight x φ) = φ.eval (append x y) := by
  induction φ with
  | lit idx b =>
    by_cases h : idx.val < n
    · simp [restrictRight, h, evalRes, DMFormula.eval, append]
    · simp [restrictRight, h, evalRes, DMFormula.eval, append]
  | and φ ψ ih1 ih2 =>
    simp [restrictRight, evalRes_combineAnd, DMFormula.eval, ih1, ih2]
  | or φ ψ ih1 ih2 =>
    simp [restrictRight, evalRes_combineOr, DMFormula.eval, ih1, ih2]

private lemma resLeaves_restrictRight {n k : ℕ} (x : Fin n → Bool) (φ : DMFormula (n + k)) :
    resLeaves (restrictRight x φ) ≤ rightLeaves φ := by
  induction φ with
  | lit idx b =>
    by_cases h : idx.val < n <;> simp [restrictRight, h, resLeaves, rightLeaves, DMFormula.leaves]
  | and φ ψ ih1 ih2 =>
    calc
      resLeaves (restrictRight x (DMFormula.and φ ψ))
          ≤ resLeaves (restrictRight x φ) + resLeaves (restrictRight x ψ) := resLeaves_combineAnd _ _
      _ ≤ rightLeaves φ + rightLeaves ψ := Nat.add_le_add ih1 ih2
  | or φ ψ ih1 ih2 =>
    calc
      resLeaves (restrictRight x (DMFormula.or φ ψ))
          ≤ resLeaves (restrictRight x φ) + resLeaves (restrictRight x ψ) := resLeaves_combineOr _ _
      _ ≤ rightLeaves φ + rightLeaves ψ := Nat.add_le_add ih1 ih2

end PEqualNP.Outside.L_meta_180

open PEqualNP.Outside.L_meta_180 in
theorem PEqualNP.Outside.L_meta_180 : ∀ (n k : ℕ) (f : (Fin n → Bool) → Bool) (g : (Fin k → Bool) → Bool) (a b : ℕ), (∃ x : Fin n → Bool, f x = true) → (∃ x : Fin n → Bool, f x = false) → (∃ y : Fin k → Bool, g y = true) → (∃ y : Fin k → Bool, g y = false) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize n f r ↔ a ≤ r) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize k g r ↔ b ≤ r) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasLeafSize (n + k) (fun z : Fin (n + k) → Bool => f (fun i : Fin n => z (Fin.castAdd k i)) || g (fun j : Fin k => z (Fin.natAdd n j))) s ↔ a + b ≤ s) := by
  intro n k f g a b ⟨xT, hxT⟩ ⟨xF, hxF⟩ ⟨yT, hyT⟩ ⟨yF, hyF⟩ hf hg s
  constructor
  · rintro ⟨Φ, hΦ_leaves, hΦ_eval⟩
    have hLeftEval : ∀ x : Fin n → Bool, evalRes x (restrictLeft yF Φ) = f x := by
      intro x
      rw [evalRes_restrictLeft, hΦ_eval]
      dsimp only
      have h1 : (fun i : Fin n => append x yF (Fin.castAdd k i)) = x := by
        funext i
        exact append_castAdd x yF i
      have h2 : (fun j : Fin k => append x yF (Fin.natAdd n j)) = yF := by
        funext j
        exact append_natAdd x yF j
      rw [h1, h2, hyF, Bool.or_false]
    have ha : a ≤ leftLeaves Φ := by
      rw [← hf (leftLeaves Φ)]
      cases hres : restrictLeft yF Φ with
      | inl c =>
        have hT : c = true := by
          have := hLeftEval xT
          rw [hres] at this
          simpa [evalRes, hxT] using this
        have hF : c = false := by
          have := hLeftEval xF
          rw [hres] at this
          simpa [evalRes, hxF] using this
        rw [hT] at hF
        exact Bool.noConfusion hF
      | inr φ =>
        refine ⟨φ, ?_, ?_⟩
        · have hle := resLeaves_restrictLeft yF Φ
          rw [hres] at hle
          exact hle
        · intro x
          have hx := hLeftEval x
          rw [hres] at hx
          exact hx
    have hRightEval : ∀ y : Fin k → Bool, evalRes y (restrictRight xF Φ) = g y := by
      intro y
      rw [evalRes_restrictRight, hΦ_eval]
      dsimp only
      have h1 : (fun i : Fin n => append xF y (Fin.castAdd k i)) = xF := by
        funext i
        exact append_castAdd xF y i
      have h2 : (fun j : Fin k => append xF y (Fin.natAdd n j)) = y := by
        funext j
        exact append_natAdd xF y j
      rw [h1, h2, hxF, Bool.false_or]
    have hb : b ≤ rightLeaves Φ := by
      rw [← hg (rightLeaves Φ)]
      cases hres : restrictRight xF Φ with
      | inl c =>
        have hT : c = true := by
          have := hRightEval yT
          rw [hres] at this
          simpa [evalRes, hyT] using this
        have hF : c = false := by
          have := hRightEval yF
          rw [hres] at this
          simpa [evalRes, hyF] using this
        rw [hT] at hF
        exact Bool.noConfusion hF
      | inr ψ =>
        refine ⟨ψ, ?_, ?_⟩
        · have hle := resLeaves_restrictRight xF Φ
          rw [hres] at hle
          exact hle
        · intro y
          have hy := hRightEval y
          rw [hres] at hy
          exact hy
    have hsum := leftLeaves_add_rightLeaves Φ
    omega
  · intro hab
    obtain ⟨φ, hφ_leaves, hφ_eval⟩ := (hf a).mpr (Nat.le_refl a)
    obtain ⟨ψ, hψ_leaves, hψ_eval⟩ := (hg b).mpr (Nat.le_refl b)
    refine ⟨DMFormula.or (liftLeft φ) (liftRight ψ), ?_, ?_⟩
    · simp only [DMFormula.leaves, liftLeft_leaves, liftRight_leaves]
      omega
    · intro z
      simp only [DMFormula.eval, liftLeft_eval, liftRight_eval, hφ_eval, hψ_eval]
