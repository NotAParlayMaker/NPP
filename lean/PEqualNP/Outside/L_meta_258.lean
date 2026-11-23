import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_258

open PEqualNP.MetaComplexity

variable {n : ℕ}

def pc (i : Fin n) : DMFormula n → ℕ
  | DMFormula.lit j c => if j = i ∧ c = true then 1 else 0
  | DMFormula.and φ ψ => pc i φ + pc i ψ
  | DMFormula.or φ ψ => pc i φ + pc i ψ

def nc (i : Fin n) : DMFormula n → ℕ
  | DMFormula.lit j c => if j = i ∧ c = false then 1 else 0
  | DMFormula.and φ ψ => nc i φ + nc i ψ
  | DMFormula.or φ ψ => nc i φ + nc i ψ

def es (i : Fin n) (y : Fin n → Bool) (a b : Bool) : DMFormula n → Bool
  | DMFormula.lit j c => if j = i then (if c then a else b) else (if c then y j else !y j)
  | DMFormula.and φ ψ => es i y a b φ && es i y a b ψ
  | DMFormula.or φ ψ => es i y a b φ || es i y a b ψ

theorem eval_es (i : Fin n) (x : Fin n → Bool) (φ : DMFormula n) :
    φ.eval x = es i x (x i) (!x i) φ := by
  induction φ with
  | lit j c =>
    by_cases h : j = i
    · subst h
      cases c <;> simp [DMFormula.eval, es]
    · simp [DMFormula.eval, es, h]
  | and φ ψ ih1 ih2 => simp [DMFormula.eval, es, ih1, ih2]
  | or φ ψ ih1 ih2 => simp [DMFormula.eval, es, ih1, ih2]

theorem es_update (i : Fin n) (y : Fin n → Bool) (v a b : Bool) (φ : DMFormula n) :
    es i (Function.update y i v) a b φ = es i y a b φ := by
  induction φ with
  | lit j c =>
    by_cases h : j = i
    · simp [es, h]
    · simp [es, h, Function.update]
  | and φ ψ ih1 ih2 => simp [es, ih1, ih2]
  | or φ ψ ih1 ih2 => simp [es, ih1, ih2]

theorem es_mono_a (i : Fin n) (y : Fin n → Bool) (b : Bool) (φ : DMFormula n) :
    es i y false b φ = true → es i y true b φ = true := by
  induction φ with
  | lit j c =>
    by_cases h : j = i
    · cases c <;> simp [es, h]
    · simp [es, h]
  | and φ ψ ih1 ih2 =>
    intro hh
    simp only [es, Bool.and_eq_true] at hh ⊢
    exact ⟨ih1 hh.1, ih2 hh.2⟩
  | or φ ψ ih1 ih2 =>
    intro hh
    simp only [es, Bool.or_eq_true] at hh ⊢
    rcases hh with hh | hh
    · exact Or.inl (ih1 hh)
    · exact Or.inr (ih2 hh)

theorem es_mono_b (i : Fin n) (y : Fin n → Bool) (a : Bool) (φ : DMFormula n) :
    es i y a false φ = true → es i y a true φ = true := by
  induction φ with
  | lit j c =>
    by_cases h : j = i
    · cases c <;> simp [es, h]
    · simp [es, h]
  | and φ ψ ih1 ih2 =>
    intro hh
    simp only [es, Bool.and_eq_true] at hh ⊢
    exact ⟨ih1 hh.1, ih2 hh.2⟩
  | or φ ψ ih1 ih2 =>
    intro hh
    simp only [es, Bool.or_eq_true] at hh ⊢
    rcases hh with hh | hh
    · exact Or.inl (ih1 hh)
    · exact Or.inr (ih2 hh)

theorem es_a (i : Fin n) (φ : DMFormula n) (h : pc i φ = 0) :
    ∀ (y : Fin n → Bool) (a a' b : Bool), es i y a b φ = es i y a' b φ := by
  induction φ with
  | lit j c =>
    intro y a a' b
    by_cases hj : j = i
    · cases c <;> simp_all [pc, es]
    · simp [es, hj]
  | and φ ψ ih1 ih2 =>
    intro y a a' b
    simp only [pc] at h
    simp only [es, ih1 (by omega) y a a' b, ih2 (by omega) y a a' b]
  | or φ ψ ih1 ih2 =>
    intro y a a' b
    simp only [pc] at h
    simp only [es, ih1 (by omega) y a a' b, ih2 (by omega) y a a' b]

theorem es_b (i : Fin n) (φ : DMFormula n) (h : nc i φ = 0) :
    ∀ (y : Fin n → Bool) (a b b' : Bool), es i y a b φ = es i y a b' φ := by
  induction φ with
  | lit j c =>
    intro y a b b'
    by_cases hj : j = i
    · cases c <;> simp_all [nc, es]
    · simp [es, hj]
  | and φ ψ ih1 ih2 =>
    intro y a b b'
    simp only [nc] at h
    simp only [es, ih1 (by omega) y a b b', ih2 (by omega) y a b b']
  | or φ ψ ih1 ih2 =>
    intro y a b b'
    simp only [nc] at h
    simp only [es, ih1 (by omega) y a b b', ih2 (by omega) y a b b']

def AndT (i : Fin n) (φ : DMFormula n) : Prop :=
  ∀ y : Fin n → Bool, es i y false true φ = true → es i y true false φ = true →
    es i y false false φ = true

def OrT (i : Fin n) (φ : DMFormula n) : Prop :=
  ∀ y : Fin n → Bool, es i y true true φ = true →
    es i y false true φ = true ∨ es i y true false φ = true

theorem typ (i : Fin n) (φ : DMFormula n) : pc i φ = 1 → nc i φ = 1 → AndT i φ ∨ OrT i φ := by
  induction φ with
  | lit j c =>
    intro h1 h2
    by_cases hj : j = i
    · cases c <;> simp [pc, nc, hj] at h1 h2
    · simp [pc, hj] at h1
  | and φ ψ ih1 ih2 =>
    intro h1 h2
    simp only [pc] at h1
    simp only [nc] at h2
    rcases (show (pc i φ = 1 ∧ pc i ψ = 0) ∨ (pc i φ = 0 ∧ pc i ψ = 1) by omega) with
      ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
    rcases (show (nc i φ = 1 ∧ nc i ψ = 0) ∨ (nc i φ = 0 ∧ nc i ψ = 1) by omega) with
      ⟨q1, q2⟩ | ⟨q1, q2⟩
    · -- both in φ
      have ca := es_a i ψ p2
      have cb := es_b i ψ q2
      rcases ih1 p1 q1 with hA | hO
      · left
        intro y h01 h10
        simp only [es, Bool.and_eq_true] at h01 h10 ⊢
        exact ⟨hA y h01.1 h10.1, by rw [cb y false false true]; exact h01.2⟩
      · right
        intro y h11
        simp only [es, Bool.and_eq_true] at h11 ⊢
        rcases hO y h11.1 with h | h
        · left
          exact ⟨h, by rw [ca y false true true]; exact h11.2⟩
        · right
          exact ⟨h, by rw [cb y true false true]; exact h11.2⟩
    · -- positive in φ, negative in ψ
      left
      intro y h01 h10
      simp only [es, Bool.and_eq_true] at h01 h10 ⊢
      exact ⟨by rw [es_b i φ q1 y false false true]; exact h01.1,
        by rw [es_a i ψ p2 y false true false]; exact h10.2⟩
    · -- negative in φ, positive in ψ
      left
      intro y h01 h10
      simp only [es, Bool.and_eq_true] at h01 h10 ⊢
      exact ⟨by rw [es_a i φ p1 y false true false]; exact h10.1,
        by rw [es_b i ψ q2 y false false true]; exact h01.2⟩
    · -- both in ψ
      have ca := es_a i φ p1
      have cb := es_b i φ q1
      rcases ih2 p2 q2 with hA | hO
      · left
        intro y h01 h10
        simp only [es, Bool.and_eq_true] at h01 h10 ⊢
        exact ⟨by rw [cb y false false true]; exact h01.1, hA y h01.2 h10.2⟩
      · right
        intro y h11
        simp only [es, Bool.and_eq_true] at h11 ⊢
        rcases hO y h11.2 with h | h
        · left
          exact ⟨by rw [ca y false true true]; exact h11.1, h⟩
        · right
          exact ⟨by rw [cb y true false true]; exact h11.1, h⟩
  | or φ ψ ih1 ih2 =>
    intro h1 h2
    simp only [pc] at h1
    simp only [nc] at h2
    rcases (show (pc i φ = 1 ∧ pc i ψ = 0) ∨ (pc i φ = 0 ∧ pc i ψ = 1) by omega) with
      ⟨p1, p2⟩ | ⟨p1, p2⟩ <;>
    rcases (show (nc i φ = 1 ∧ nc i ψ = 0) ∨ (nc i φ = 0 ∧ nc i ψ = 1) by omega) with
      ⟨q1, q2⟩ | ⟨q1, q2⟩
    · -- both in φ
      have ca := es_a i ψ p2
      have cb := es_b i ψ q2
      rcases ih1 p1 q1 with hA | hO
      · left
        intro y h01 h10
        simp only [es, Bool.or_eq_true] at h01 h10 ⊢
        rcases h01 with h01 | h01
        · rcases h10 with h10 | h10
          · exact Or.inl (hA y h01 h10)
          · right
            rw [ca y false true false]
            exact h10
        · right
          rw [cb y false false true]
          exact h01
      · right
        intro y h11
        simp only [es, Bool.or_eq_true] at h11 ⊢
        rcases h11 with h11 | h11
        · rcases hO y h11 with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
        · left
          right
          rw [ca y false true true]
          exact h11
    · -- positive in φ, negative in ψ
      right
      intro y h11
      simp only [es, Bool.or_eq_true] at h11 ⊢
      rcases h11 with h11 | h11
      · right
        left
        rw [es_b i φ q1 y true false true]
        exact h11
      · left
        right
        rw [es_a i ψ p2 y false true true]
        exact h11
    · -- negative in φ, positive in ψ
      right
      intro y h11
      simp only [es, Bool.or_eq_true] at h11 ⊢
      rcases h11 with h11 | h11
      · left
        left
        rw [es_a i φ p1 y false true true]
        exact h11
      · right
        right
        rw [es_b i ψ q2 y true false true]
        exact h11
    · -- both in ψ
      have ca := es_a i φ p1
      have cb := es_b i φ q1
      rcases ih2 p2 q2 with hA | hO
      · left
        intro y h01 h10
        simp only [es, Bool.or_eq_true] at h01 h10 ⊢
        rcases h01 with h01 | h01
        · left
          rw [cb y false false true]
          exact h01
        · rcases h10 with h10 | h10
          · left
            rw [ca y false true false]
            exact h10
          · exact Or.inr (hA y h01 h10)
      · right
        intro y h11
        simp only [es, Bool.or_eq_true] at h11 ⊢
        rcases h11 with h11 | h11
        · left
          left
          rw [ca y false true true]
          exact h11
        · rcases hO y h11 with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inr h)

def sand : Bool ⊕ DMFormula n → Bool ⊕ DMFormula n → Bool ⊕ DMFormula n
  | Sum.inl true, r => r
  | Sum.inl false, _ => Sum.inl false
  | Sum.inr φ, Sum.inl true => Sum.inr φ
  | Sum.inr _, Sum.inl false => Sum.inl false
  | Sum.inr φ, Sum.inr ψ => Sum.inr (DMFormula.and φ ψ)

def sor : Bool ⊕ DMFormula n → Bool ⊕ DMFormula n → Bool ⊕ DMFormula n
  | Sum.inl true, _ => Sum.inl true
  | Sum.inl false, r => r
  | Sum.inr _, Sum.inl true => Sum.inl true
  | Sum.inr φ, Sum.inl false => Sum.inr φ
  | Sum.inr φ, Sum.inr ψ => Sum.inr (DMFormula.or φ ψ)

def sev : Bool ⊕ DMFormula n → (Fin n → Bool) → Bool
  | Sum.inl b, _ => b
  | Sum.inr φ, x => φ.eval x

def sz : Bool ⊕ DMFormula n → ℕ
  | Sum.inl _ => 0
  | Sum.inr φ => φ.leaves

theorem sev_sand (r s : Bool ⊕ DMFormula n) (x : Fin n → Bool) :
    sev (sand r s) x = (sev r x && sev s x) := by
  rcases r with b | φ <;> rcases s with b' | ψ <;> (try cases b) <;> (try cases b') <;>
    simp [sand, sev, DMFormula.eval]

theorem sev_sor (r s : Bool ⊕ DMFormula n) (x : Fin n → Bool) :
    sev (sor r s) x = (sev r x || sev s x) := by
  rcases r with b | φ <;> rcases s with b' | ψ <;> (try cases b) <;> (try cases b') <;>
    simp [sor, sev, DMFormula.eval]

theorem sz_sand (r s : Bool ⊕ DMFormula n) : sz (sand r s) ≤ sz r + sz s := by
  rcases r with b | φ <;> rcases s with b' | ψ <;> (try cases b) <;> (try cases b') <;>
    simp [sand, sz, DMFormula.leaves]

theorem sz_sor (r s : Bool ⊕ DMFormula n) : sz (sor r s) ≤ sz r + sz s := by
  rcases r with b | φ <;> rcases s with b' | ψ <;> (try cases b) <;> (try cases b') <;>
    simp [sor, sz, DMFormula.leaves]

def cs (i : Fin n) (c : Bool) : DMFormula n → Bool ⊕ DMFormula n
  | DMFormula.lit j d => if j = i ∧ d = false then Sum.inl c else Sum.inr (DMFormula.lit j d)
  | DMFormula.and φ ψ => sand (cs i c φ) (cs i c ψ)
  | DMFormula.or φ ψ => sor (cs i c φ) (cs i c ψ)

theorem sev_cs (i : Fin n) (c : Bool) (x : Fin n → Bool) (φ : DMFormula n) :
    sev (cs i c φ) x = es i x (x i) c φ := by
  induction φ with
  | lit j d =>
    by_cases hj : j = i
    · subst hj
      cases d <;> simp [cs, sev, es, DMFormula.eval]
    · simp [cs, sev, es, DMFormula.eval, hj]
  | and φ ψ ih1 ih2 => simp [cs, sev_sand, ih1, ih2, es]
  | or φ ψ ih1 ih2 => simp [cs, sev_sor, ih1, ih2, es]

theorem sz_cs (i : Fin n) (c : Bool) (φ : DMFormula n) :
    sz (cs i c φ) + nc i φ ≤ φ.leaves := by
  induction φ with
  | lit j d =>
    by_cases hj : j = i
    · cases d <;> simp [cs, sz, nc, DMFormula.leaves, hj]
    · simp [cs, sz, nc, DMFormula.leaves, hj]
  | and φ ψ ih1 ih2 =>
    have := sz_sand (cs i c φ) (cs i c ψ)
    simp only [cs, nc, DMFormula.leaves]
    omega
  | or φ ψ ih1 ih2 =>
    have := sz_sor (cs i c φ) (cs i c ψ)
    simp only [cs, nc, DMFormula.leaves]
    omega

theorem occ_eq (i : Fin n) (φ : DMFormula n) :
    DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0)
      (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = pc i φ + nc i φ := by
  induction φ with
  | lit j c =>
    by_cases hj : j = i
    · cases c <;> simp [pc, nc, hj]
    · simp [pc, nc, hj]
  | and φ ψ ih1 ih2 =>
    dsimp only
    rw [ih1, ih2]
    simp only [pc, nc]
    omega
  | or φ ψ ih1 ih2 =>
    dsimp only
    rw [ih1, ih2]
    simp only [pc, nc]
    omega

theorem neg_eq (i : Fin n) (φ : DMFormula n) :
    DMFormula.rec (motive := fun _ => ℕ)
      (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0)
      (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = nc i φ := by
  induction φ with
  | lit j c => simp [nc]
  | and φ ψ ih1 ih2 =>
    dsimp only
    rw [ih1, ih2]
    simp only [nc]
  | or φ ψ ih1 ih2 =>
    dsimp only
    rw [ih1, ih2]
    simp only [nc]

theorem main (f : (Fin n → Bool) → Bool) (φ : DMFormula n) (i : Fin n)
    (hmono : ∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true →
      f y = true)
    (hess : ∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false))
    (hφ : ∀ x : Fin n → Bool, φ.eval x = f x)
    (hmin : ∀ ψ : DMFormula n, (∀ x : Fin n → Bool, ψ.eval x = f x) → φ.leaves ≤ ψ.leaves)
    (hocc : pc i φ + nc i φ ≤ 2) : nc i φ = 0 := by
  by_contra hq
  have key : ∀ x, f x = es i x (x i) (!x i) φ := fun x => by rw [← hφ x, eval_es i x φ]
  have fx1 : ∀ x, f (Function.update x i true) = es i x true false φ := by
    intro x
    rw [key, es_update]
    simp
  have fx0 : ∀ x, f (Function.update x i false) = es i x false true φ := by
    intro x
    rw [key, es_update]
    simp
  have up1 : ∀ x, f x = true → f (Function.update x i true) = true := by
    intro x hx
    refine hmono x _ (fun j hj => ?_) hx
    by_cases hji : j = i
    · subst hji
      simp
    · simp [Function.update, hji, hj]
  have dn0 : ∀ x, f (Function.update x i false) = true → f x = true := by
    intro x hx
    refine hmono _ x (fun j hj => ?_) hx
    by_cases hji : j = i
    · subst hji
      simp at hj
    · simpa [Function.update, hji] using hj
  have fconst : ∀ b : Bool, ¬ ∀ x, f x = b := by
    intro b hb
    obtain ⟨x0, hx0⟩ := hess
    exact hx0 (by rw [hb, hb])
  have finish : ∀ c : Bool, (∀ x, sev (cs i c φ) x = f x) → False := by
    intro c hc
    have hsz := sz_cs i c φ
    cases hcs : cs i c φ with
    | inl b =>
      apply fconst b
      intro x
      rw [← hc x, hcs]
      rfl
    | inr ψ =>
      have hψ : ∀ x, ψ.eval x = f x := fun x => by
        have := hc x
        rw [hcs] at this
        exact this
      have := hmin ψ hψ
      rw [hcs] at hsz
      simp only [sz] at hsz
      omega
  by_cases hp : pc i φ = 0
  · obtain ⟨x0, hx0⟩ := hess
    apply hx0
    rw [fx1, fx0, es_a i φ hp x0 true false false]
    cases h00 : es i x0 false false φ
    · cases h01 : es i x0 false true φ
      · rfl
      · exfalso
        have := up1 _ (by rw [fx0]; exact h01)
        rw [Function.update_idem, fx1, es_a i φ hp x0 true false false, h00] at this
        exact Bool.false_ne_true this
    · exact (es_mono_b i x0 false φ h00).symm
  · have hp1 : pc i φ = 1 := by omega
    have hq1 : nc i φ = 1 := by omega
    rcases typ i φ hp1 hq1 with hA | hO
    · apply finish false
      intro x
      rw [sev_cs, key x]
      cases hxi : x i
      · simp only [Bool.not_false]
        apply Bool.eq_iff_iff.mpr
        constructor
        · exact es_mono_b i x false φ
        · intro h01
          apply hA x h01
          rw [← fx1]
          apply up1
          rw [key x, hxi]
          exact h01
      · rfl
    · apply finish true
      intro x
      rw [sev_cs, key x]
      cases hxi : x i
      · rfl
      · simp only [Bool.not_true]
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro h11
          rcases hO x h11 with h | h
          · have := dn0 x (by rw [fx0]; exact h)
            rw [key x, hxi] at this
            exact this
          · exact h
        · exact es_mono_b i x true φ

end PEqualNP.Outside.L_meta_258

theorem PEqualNP.Outside.L_meta_258 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)) → (∀ x : Fin n → Bool, φ.eval x = f x) → (∀ ψ : PEqualNP.MetaComplexity.DMFormula n, (∀ x : Fin n → Bool, ψ.eval x = f x) → φ.leaves ≤ ψ.leaves) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ ≤ 2 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 := by
  intro n f φ i hmono hess hφ hmin hocc
  have h1 := PEqualNP.Outside.L_meta_258.occ_eq i φ
  have h2 := PEqualNP.Outside.L_meta_258.neg_eq i φ
  have := PEqualNP.Outside.L_meta_258.main f φ i hmono hess hφ hmin (by omega)
  omega
