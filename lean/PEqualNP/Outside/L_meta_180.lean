import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_180_aux

open PEqualNP.MetaComplexity

def evalR {M : ℕ} : Bool ⊕ DMFormula M → (Fin M → Bool) → Bool
  | Sum.inl c, _ => c
  | Sum.inr φ, x => φ.eval x

def leavesR {M : ℕ} : Bool ⊕ DMFormula M → ℕ
  | Sum.inl _ => 0
  | Sum.inr φ => φ.leaves

def cAnd {M : ℕ} : Bool ⊕ DMFormula M → Bool ⊕ DMFormula M → Bool ⊕ DMFormula M
  | Sum.inl true, r => r
  | Sum.inl false, _ => Sum.inl false
  | Sum.inr a, Sum.inl true => Sum.inr a
  | Sum.inr _, Sum.inl false => Sum.inl false
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.and a b)

def cOr {M : ℕ} : Bool ⊕ DMFormula M → Bool ⊕ DMFormula M → Bool ⊕ DMFormula M
  | Sum.inl false, r => r
  | Sum.inl true, _ => Sum.inl true
  | Sum.inr a, Sum.inl false => Sum.inr a
  | Sum.inr _, Sum.inl true => Sum.inl true
  | Sum.inr a, Sum.inr b => Sum.inr (DMFormula.or a b)

theorem evalR_cAnd {M : ℕ} (r s : Bool ⊕ DMFormula M) (x : Fin M → Bool) :
    evalR (cAnd r s) x = (evalR r x && evalR s x) := by
  rcases r with (_ | _) | a <;> rcases s with (_ | _) | b <;>
    simp [cAnd, evalR, DMFormula.eval]

theorem evalR_cOr {M : ℕ} (r s : Bool ⊕ DMFormula M) (x : Fin M → Bool) :
    evalR (cOr r s) x = (evalR r x || evalR s x) := by
  rcases r with (_ | _) | a <;> rcases s with (_ | _) | b <;>
    simp [cOr, evalR, DMFormula.eval]

theorem leavesR_cAnd {M : ℕ} (r s : Bool ⊕ DMFormula M) :
    leavesR (cAnd r s) ≤ leavesR r + leavesR s := by
  rcases r with (_ | _) | a <;> rcases s with (_ | _) | b <;>
    simp [cAnd, leavesR, DMFormula.leaves]

theorem leavesR_cOr {M : ℕ} (r s : Bool ⊕ DMFormula M) :
    leavesR (cOr r s) ≤ leavesR r + leavesR s := by
  rcases r with (_ | _) | a <;> rcases s with (_ | _) | b <;>
    simp [cOr, leavesR, DMFormula.leaves]

def restr {N M : ℕ} (m : Fin N → Fin M ⊕ Bool) : DMFormula N → Bool ⊕ DMFormula M
  | DMFormula.lit i s =>
      match m i with
      | Sum.inl j => Sum.inr (DMFormula.lit j s)
      | Sum.inr c => Sum.inl (if s then c else !c)
  | DMFormula.and φ ψ => cAnd (restr m φ) (restr m ψ)
  | DMFormula.or φ ψ => cOr (restr m φ) (restr m ψ)

def cntP {N : ℕ} (p : Fin N → Bool) : DMFormula N → ℕ
  | DMFormula.lit i _ => if p i then 1 else 0
  | DMFormula.and φ ψ => cntP p φ + cntP p ψ
  | DMFormula.or φ ψ => cntP p φ + cntP p ψ

theorem cntP_add {N : ℕ} (p : Fin N → Bool) (φ : DMFormula N) :
    cntP p φ + cntP (fun i => !p i) φ = φ.leaves := by
  induction φ with
  | lit i s =>
    cases hp : p i <;> simp [cntP, DMFormula.leaves, hp]
  | and φ ψ ihφ ihψ =>
    simp only [cntP, DMFormula.leaves]
    omega
  | or φ ψ ihφ ihψ =>
    simp only [cntP, DMFormula.leaves]
    omega

theorem restr_leaves {N M : ℕ} (m : Fin N → Fin M ⊕ Bool) (p : Fin N → Bool)
    (hp : ∀ i j, m i = Sum.inl j → p i = true) (φ : DMFormula N) :
    leavesR (restr m φ) ≤ cntP p φ := by
  induction φ with
  | lit i s =>
    rcases hm : m i with j | c
    · have h1 := hp i j hm
      simp [restr, hm, cntP, leavesR, DMFormula.leaves, h1]
    · simp [restr, hm, cntP, leavesR]
  | and φ ψ ihφ ihψ =>
    simp only [restr, cntP]
    exact (leavesR_cAnd _ _).trans (Nat.add_le_add ihφ ihψ)
  | or φ ψ ihφ ihψ =>
    simp only [restr, cntP]
    exact (leavesR_cOr _ _).trans (Nat.add_le_add ihφ ihψ)

theorem restr_eval {N M : ℕ} (m : Fin N → Fin M ⊕ Bool) (x : Fin M → Bool) (z : Fin N → Bool)
    (h1 : ∀ i j, m i = Sum.inl j → z i = x j) (h2 : ∀ i c, m i = Sum.inr c → z i = c)
    (φ : DMFormula N) : evalR (restr m φ) x = φ.eval z := by
  induction φ with
  | lit i s =>
    rcases hm : m i with j | c
    · simp [restr, hm, evalR, DMFormula.eval, h1 i j hm]
    · simp [restr, hm, evalR, DMFormula.eval, h2 i c hm]
  | and φ ψ ihφ ihψ =>
    simp only [restr, evalR_cAnd, DMFormula.eval, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
    simp only [restr, evalR_cOr, DMFormula.eval, ihφ, ihψ]

def mX (n k : ℕ) (y0 : Fin k → Bool) (i : Fin (n + k)) : Fin n ⊕ Bool :=
  if h : i.val < n then Sum.inl ⟨i.val, h⟩
  else Sum.inr (y0 ⟨i.val - n, by have := i.2; omega⟩)

def mY (n k : ℕ) (x0 : Fin n → Bool) (i : Fin (n + k)) : Fin k ⊕ Bool :=
  if h : i.val < n then Sum.inr (x0 ⟨i.val, h⟩)
  else Sum.inl ⟨i.val - n, by have := i.2; omega⟩

def zX (n k : ℕ) (x : Fin n → Bool) (y0 : Fin k → Bool) (i : Fin (n + k)) : Bool :=
  if h : i.val < n then x ⟨i.val, h⟩ else y0 ⟨i.val - n, by have := i.2; omega⟩

def zY (n k : ℕ) (x0 : Fin n → Bool) (y : Fin k → Bool) (i : Fin (n + k)) : Bool :=
  if h : i.val < n then x0 ⟨i.val, h⟩ else y ⟨i.val - n, by have := i.2; omega⟩

theorem mX_inl {n k : ℕ} (x : Fin n → Bool) (y0 : Fin k → Bool) :
    ∀ i j, mX n k y0 i = Sum.inl j → zX n k x y0 i = x j := by
  intro i j hij
  by_cases h : i.val < n
  · simp only [mX, h, dif_pos] at hij
    have hj : (⟨i.val, h⟩ : Fin n) = j := Sum.inl.inj hij
    subst hj
    simp [zX, h]
  · simp [mX, h] at hij

theorem mX_inr {n k : ℕ} (x : Fin n → Bool) (y0 : Fin k → Bool) :
    ∀ i c, mX n k y0 i = Sum.inr c → zX n k x y0 i = c := by
  intro i c hij
  by_cases h : i.val < n
  · simp [mX, h] at hij
  · simp only [mX, h, dif_neg, not_false_eq_true] at hij
    have hc := Sum.inr.inj hij
    simp [zX, h, hc]

theorem mY_inl {n k : ℕ} (x0 : Fin n → Bool) (y : Fin k → Bool) :
    ∀ i j, mY n k x0 i = Sum.inl j → zY n k x0 y i = y j := by
  intro i j hij
  by_cases h : i.val < n
  · simp [mY, h] at hij
  · simp only [mY, h, dif_neg, not_false_eq_true] at hij
    have hj : (⟨i.val - n, by have := i.2; omega⟩ : Fin k) = j := Sum.inl.inj hij
    subst hj
    simp [zY, h]

theorem mY_inr {n k : ℕ} (x0 : Fin n → Bool) (y : Fin k → Bool) :
    ∀ i c, mY n k x0 i = Sum.inr c → zY n k x0 y i = c := by
  intro i c hij
  by_cases h : i.val < n
  · simp only [mY, h, dif_pos] at hij
    have hc := Sum.inr.inj hij
    simp [zY, h, hc]
  · simp [mY, h] at hij

theorem zX_left {n k : ℕ} (x : Fin n → Bool) (y0 : Fin k → Bool) :
    (fun i : Fin n => zX n k x y0 (Fin.castAdd k i)) = x := by
  funext i
  simp [zX]

theorem zX_right {n k : ℕ} (x : Fin n → Bool) (y0 : Fin k → Bool) :
    (fun j : Fin k => zX n k x y0 (Fin.natAdd n j)) = y0 := by
  funext j
  have h : ¬ (n + j.val < n) := by omega
  simp [zX, h]

theorem zY_left {n k : ℕ} (x0 : Fin n → Bool) (y : Fin k → Bool) :
    (fun i : Fin n => zY n k x0 y (Fin.castAdd k i)) = x0 := by
  funext i
  simp [zY]

theorem zY_right {n k : ℕ} (x0 : Fin n → Bool) (y : Fin k → Bool) :
    (fun j : Fin k => zY n k x0 y (Fin.natAdd n j)) = y := by
  funext j
  have h : ¬ (n + j.val < n) := by omega
  simp [zY, h]

def mapF {n N : ℕ} (σ : Fin n → Fin N) : DMFormula n → DMFormula N
  | DMFormula.lit i s => DMFormula.lit (σ i) s
  | DMFormula.and φ ψ => DMFormula.and (mapF σ φ) (mapF σ ψ)
  | DMFormula.or φ ψ => DMFormula.or (mapF σ φ) (mapF σ ψ)

theorem mapF_leaves {n N : ℕ} (σ : Fin n → Fin N) (φ : DMFormula n) :
    (mapF σ φ).leaves = φ.leaves := by
  induction φ with
  | lit i s => simp [mapF, DMFormula.leaves]
  | and φ ψ ihφ ihψ => simp [mapF, DMFormula.leaves, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [mapF, DMFormula.leaves, ihφ, ihψ]

theorem mapF_eval {n N : ℕ} (σ : Fin n → Fin N) (z : Fin N → Bool) (φ : DMFormula n) :
    (mapF σ φ).eval z = φ.eval (fun i => z (σ i)) := by
  induction φ with
  | lit i s => simp [mapF, DMFormula.eval]
  | and φ ψ ihφ ihψ => simp [mapF, DMFormula.eval, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [mapF, DMFormula.eval, ihφ, ihψ]

end PEqualNP.Outside.L_meta_180_aux

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_180_aux

theorem PEqualNP.Outside.L_meta_180 : ∀ (n k : ℕ) (f : (Fin n → Bool) → Bool) (g : (Fin k → Bool) → Bool) (a b : ℕ), (∃ x : Fin n → Bool, f x = true) → (∃ x : Fin n → Bool, f x = false) → (∃ y : Fin k → Bool, g y = true) → (∃ y : Fin k → Bool, g y = false) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize n f r ↔ a ≤ r) → (∀ r : ℕ, PEqualNP.MetaComplexity.HasLeafSize k g r ↔ b ≤ r) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasLeafSize (n + k) (fun z : Fin (n + k) → Bool => f (fun i : Fin n => z (Fin.castAdd k i)) || g (fun j : Fin k => z (Fin.natAdd n j))) s ↔ a + b ≤ s) := by
  intro n k f g a b ⟨xt, hxt⟩ ⟨xf, hxf⟩ ⟨yt, hyt⟩ ⟨yf, hyf⟩ hf hg s
  constructor
  · rintro ⟨φ, hφ, hev⟩
    have h1 : a ≤ cntP (fun i : Fin (n + k) => decide (i.val < n)) φ := by
      have hcnt := restr_leaves (mX n k yf) (fun i : Fin (n + k) => decide (i.val < n))
        (by
          intro i j hij
          by_cases h : i.val < n
          · simp [h]
          · simp [mX, h] at hij) φ
      have hsem : ∀ x : Fin n → Bool, evalR (restr (mX n k yf) φ) x = f x := by
        intro x
        rw [restr_eval (mX n k yf) x (zX n k x yf) (mX_inl x yf) (mX_inr x yf) φ, hev
          ]
        beta_reduce
        rw [zX_left, zX_right, hyf]
        simp
      rcases hs : restr (mX n k yf) φ with c | ψ
      · exfalso
        rw [hs] at hsem
        have e1 := hsem xt
        have e2 := hsem xf
        simp only [evalR] at e1 e2
        rw [hxt] at e1
        rw [hxf] at e2
        rw [e1] at e2
        exact absurd e2 (by decide)
      · rw [hs] at hcnt hsem
        exact (hf _).1 ⟨ψ, hcnt, fun x => hsem x⟩
    have h2 : b ≤ cntP (fun i : Fin (n + k) => !(decide (i.val < n))) φ := by
      have hcnt := restr_leaves (mY n k xf) (fun i : Fin (n + k) => !(decide (i.val < n)))
        (by
          intro i j hij
          by_cases h : i.val < n
          · simp [mY, h] at hij
          · simp [h]) φ
      have hsem : ∀ y : Fin k → Bool, evalR (restr (mY n k xf) φ) y = g y := by
        intro y
        rw [restr_eval (mY n k xf) y (zY n k xf y) (mY_inl xf y) (mY_inr xf y) φ, hev
          ]
        beta_reduce
        rw [zY_left, zY_right, hxf]
        simp
      rcases hs : restr (mY n k xf) φ with c | ψ
      · exfalso
        rw [hs] at hsem
        have e1 := hsem yt
        have e2 := hsem yf
        simp only [evalR] at e1 e2
        rw [hyt] at e1
        rw [hyf] at e2
        rw [e1] at e2
        exact absurd e2 (by decide)
      · rw [hs] at hcnt hsem
        exact (hg _).1 ⟨ψ, hcnt, fun y => hsem y⟩
    have h3 := cntP_add (fun i : Fin (n + k) => decide (i.val < n)) φ
    omega
  · intro hs
    obtain ⟨φf, hφf, hevf⟩ := (hf a).2 le_rfl
    obtain ⟨φg, hφg, hevg⟩ := (hg b).2 le_rfl
    refine ⟨DMFormula.or (PEqualNP.Outside.L_meta_180_aux.mapF (Fin.castAdd k) φf)
      (PEqualNP.Outside.L_meta_180_aux.mapF (Fin.natAdd n) φg), ?_, ?_⟩
    · simp only [DMFormula.leaves, PEqualNP.Outside.L_meta_180_aux.mapF_leaves]
      omega
    · intro z
      simp only [DMFormula.eval, PEqualNP.Outside.L_meta_180_aux.mapF_eval, hevf, hevg]
