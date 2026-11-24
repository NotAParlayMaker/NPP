import Mathlib
import PEqualNP.Defs

-- The search adapts Astro's proof of L-meta-163, based on Vivek Rajkumar's signature search.

namespace PEqualNP.Outside.L_meta_1427_aux

open PEqualNP.CircuitLowerBounds

abbrev B := BitVec 256
abbrev Sig := B × B

def mkBVLoop : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n + 1, p => 2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0

def mkBV (p : Fin 256 → Bool) : B :=
  BitVec.ofNat 256 (mkBVLoop 256 (fun i => if h : i < 256 then p ⟨i, h⟩ else false))

lemma testBit_mkBVLoop (n : ℕ) : ∀ (p : ℕ → Bool) (i : ℕ), i < n →
    (mkBVLoop n p).testBit i = p i := by
  induction n with
  | zero => intro p i hi; omega
  | succ n ih =>
    intro p i hi
    cases i with
    | zero =>
      simp only [mkBVLoop]
      cases p 0 <;> simp
    | succ i =>
      simp only [mkBVLoop]
      have hbit : (2 * mkBVLoop n (fun k => p (k + 1)) + if p 0 then 1 else 0).testBit (i + 1) =
          (mkBVLoop n (fun k => p (k + 1))).testBit i := by
        cases p 0 <;> simp [Nat.testBit_succ, Nat.mul_add_div]
      rw [hbit, ih (fun k => p (k + 1)) i (by omega)]

lemma getElem_mkBV (p : Fin 256 → Bool) (i : ℕ) (hi : i < 256) :
    (mkBV p)[i] = p ⟨i, hi⟩ := by
  unfold mkBV
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow]
  simp only [decide_eq_true hi, Bool.true_and]
  rw [testBit_mkBVLoop 256 _ i hi]
  simp [hi]

lemma zero_bit (i : ℕ) (hi : i < 256) : (0 : B)[i] = false := by simp

def top : B := BitVec.allOnes 256
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)

def neg (a : Sig) : Sig := (~~~ a.1, ~~~ a.2)

def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)

def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~ a.2

def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a :: l => sep d a ||| unionSep d l

def before (a b : Sig) : Bool :=
  if a.1 == b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)

def dropped (del v : List Sig) : List Sig :=
  v.filter (fun x => !del.contains x)

def tryGate (k t : ℕ) (r : List Sig → Bool) (v rest : List Sig) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  g != zero && g != one && !v.contains g &&
    (let d := decide (0 < t)
     let base := sep d g ||| unionSep d rest
     keep.any (fun h => decide (rest.length + h.length + 1 ≤ k - t + 1) &&
       (base ||| unionSep d h == top) && r (g :: (h ++ rest))))

def search : ℕ → ℕ → List Sig → Bool
  | 0, _, v => v.contains target
  | k + 1, t, v =>
    v.contains target ||
    (decide (0 < t) &&
      v.any (fun a => tryGate k (t - 1) (search k (t - 1)) v (dropped [a] v) (neg a) [[], [a]])) ||
    (decide (t ≤ k) &&
      v.any (fun a => v.any (fun b =>
        before a b &&
        (let rest := dropped [a, b] v
         let keep := [[], [a], [b], [a, b]]
         tryGate k t (search k t) v rest (bin false a b) keep ||
         tryGate k t (search k t) v rest (bin true a b) keep))))

def wiresToSigs (wa wb : Fin 256 → List Bool) (len : ℕ) : List Sig :=
  (List.range len).map (fun idx =>
    (mkBV (fun r => (wa r).getD idx false),
     mkBV (fun r => (wb r).getD idx false)))

def evalGateSig (g : Gate) (W : List Sig) : Sig :=
  match g.op, g.inputs with
  | GateOp.and, [] => one
  | GateOp.and, [p] => W.getD p zero
  | GateOp.and, [p, q] => bin false (W.getD p zero) (W.getD q zero)
  | GateOp.or, [] => zero
  | GateOp.or, [p] => W.getD p zero
  | GateOp.or, [p, q] => bin true (W.getD p zero) (W.getD q zero)
  | GateOp.not, [] => one
  | GateOp.not, p :: _ => neg (W.getD p zero)
  | _, _ => zero

def evalGates (gs : List Gate) (W : List Sig) : List Sig :=
  gs.foldl (fun W g => W ++ [evalGateSig g W]) W

def evalWires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_cons (g : Gate) (rest : List Gate) (W : List Sig) :
    evalGates (g :: rest) W = evalGates rest (W ++ [evalGateSig g W]) := rfl

lemma evalWires_cons (g : Gate) (rest : List Gate) (w : List Bool) :
    evalWires (g :: rest) w =
      evalWires rest (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma target_ne_zero : target ≠ zero := by decide
lemma target_ne_one : target ≠ one := by decide

def cellNot (k t : ℕ) (v : List Sig) (a : Sig) : Bool :=
  tryGate k (t - 1) (search k (t - 1)) v (dropped [a] v) (neg a) [[], [a]]

def cell (k t : ℕ) (v : List Sig) (a b : Sig) : Bool :=
  before a b &&
    (let rest := dropped [a, b] v
     let keep := [[], [a], [b], [a, b]]
     tryGate k t (search k t) v rest (bin false a b) keep ||
     tryGate k t (search k t) v rest (bin true a b) keep)

lemma search_succ (k t : ℕ) (v : List Sig) :
    search (k + 1) t v = (v.contains target ||
      (decide (0 < t) && v.any (fun a => cellNot k t v a)) ||
      (decide (t ≤ k) && v.any (fun a => v.any (fun b => cell k t v a b)))) := rfl

lemma bin_comm (isOr : Bool) (a b : Sig) : bin isOr a b = bin isOr b a := by
  cases isOr <;> simp only [bin, BitVec.or_comm, BitVec.and_comm]

lemma bin_self (isOr : Bool) (a : Sig) : bin isOr a a = a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, Bool.false_eq_true, ↓reduceIte, BitVec.and_self]
  · simp only [bin, ↓reduceIte, BitVec.or_self]

lemma bin_zero_left (isOr : Bool) (a : Sig) : bin isOr zero a = if isOr then a else zero := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, zero, Bool.false_eq_true, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp
  · simp only [bin, zero, ↓reduceIte]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;> simp

lemma bin_zero_right (isOr : Bool) (a : Sig) : bin isOr a zero = if isOr then a else zero := by
  rw [bin_comm, bin_zero_left]

lemma bin_one_left (isOr : Bool) (a : Sig) : bin isOr one a = if isOr then one else a := by
  rcases a with ⟨a1, a2⟩
  cases isOr
  · simp only [bin, one, top, Bool.false_eq_true, ↓reduceIte, BitVec.allOnes_and]
  · simp only [bin, one, top, ↓reduceIte, BitVec.allOnes_or]

lemma bin_one_right (isOr : Bool) (a : Sig) : bin isOr a one = if isOr then one else a := by
  rw [bin_comm, bin_one_left]

lemma neg_zero : neg zero = one := by decide
lemma neg_one : neg one = zero := by decide

lemma before_trichotomy {a b : Sig} (hne : a ≠ b) : before a b = true ∨ before b a = true := by
  unfold before
  by_cases h1 : a.1 = b.1
  · have h2 : a.2 ≠ b.2 := fun h => hne (Prod.ext h1 h)
    have h2n : a.2.toNat ≠ b.2.toNat := fun h => h2 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = true := by rw [beq_iff_eq]; exact h1
    have hb2 : (b.1 == a.1) = true := by rw [beq_iff_eq]; exact h1.symm
    rw [hb1, hb2]
    simp only [↓reduceIte, decide_eq_true_eq]
    omega
  · have h1n : a.1.toNat ≠ b.1.toNat := fun h => h1 (BitVec.eq_of_toNat_eq h)
    have hb1 : (a.1 == b.1) = false := beq_false_of_ne h1
    have hb2 : (b.1 == a.1) = false := beq_false_of_ne (Ne.symm h1)
    rw [hb1, hb2]
    simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    omega

lemma unionSep_perm {d : Bool} {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    unionSep d v₁ = unionSep d v₂ := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp only [unionSep, ih]
  | swap a b l =>
    simp only [unionSep]
    rw [← BitVec.or_assoc, ← BitVec.or_assoc, BitVec.or_comm (sep d a) (sep d b)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

lemma unionSep_append (d : Bool) (l₁ l₂ : List Sig) :
    unionSep d (l₁ ++ l₂) = unionSep d l₁ ||| unionSep d l₂ := by
  induction l₁ with
  | nil => simp [unionSep]
  | cons a t ih => simp only [List.cons_append, unionSep, ih, BitVec.or_assoc]

lemma unionSep_bit_iff (d : Bool) (v : List Sig) (i : ℕ) (hi : i < 256) :
    (unionSep d v)[i] = true ↔ ∃ s ∈ v, (sep d s)[i] = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a t ih =>
    simp only [unionSep, BitVec.getElem_or, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨s, hs, h⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨s, Or.inr hs, h⟩
    · rintro ⟨s, rfl | hs, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, hs, h⟩

lemma bv_eq_top_of_bits {x : B} (h : ∀ i (hi : i < 256), x[i] = true) : x = top := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [top, BitVec.getElem_allOnes]
  exact h i hi

lemma top_bit (i : ℕ) (hi : i < 256) : top[i] = true := by
  rw [top, BitVec.getElem_allOnes]

lemma sep_mono_true (d : Bool) (a : Sig) (i : ℕ) (hi : i < 256) :
    (sep d a)[i] = true → (sep true a)[i] = true := by
  cases d
  · simp only [sep, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, BitVec.getElem_not,
      BitVec.getElem_xor, Bool.and_eq_true, Bool.not_eq_true']
    intro h
    simp [h.1, h.2]
  · exact id

lemma sep_neg_true (a : Sig) (i : ℕ) (hi : i < 256) :
    (sep true (neg a))[i] = (sep true a)[i] := by
  simp only [sep, neg, ↓reduceIte, BitVec.getElem_xor, BitVec.getElem_not]
  cases a.1[i] <;> cases a.2[i] <;> rfl

lemma sep_bin_bit (d isOr : Bool) (a b : Sig) (i : ℕ) (hi : i < 256) :
    (sep d (bin isOr a b))[i] = true → (sep d a)[i] = true ∨ (sep d b)[i] = true := by
  cases d <;> cases isOr <;>
    simp only [sep, bin, ↓reduceIte, Bool.false_eq_true, BitVec.getElem_and,
      BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_not] <;>
    cases a.1[i] <;> cases a.2[i] <;> cases b.1[i] <;> cases b.2[i] <;> decide

lemma unionSep_target_eq_top : unionSep false [target] = top := by decide

lemma dropped_perm {del v₁ v₂ : List Sig} (hp : v₁.Perm v₂) :
    (dropped del v₁).Perm (dropped del v₂) :=
  hp.filter _

lemma contains_perm {v₁ v₂ : List Sig} (hp : v₁.Perm v₂) (x : Sig) :
    v₁.contains x = v₂.contains x := by
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem, List.contains_iff_mem]
  exact hp.mem_iff

lemma list_any_eq_of_eq {α : Type} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = g a) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

lemma search_perm : ∀ k t {v₁ v₂ : List Sig}, v₁.Perm v₂ → search k t v₁ = search k t v₂ := by
  intro k
  induction k with
  | zero =>
    intro t v₁ v₂ hp
    exact contains_perm hp target
  | succ k ih =>
    intro t v₁ v₂ hp
    have htry : ∀ (t' : ℕ) (rest₁ rest₂ : List Sig) (g : Sig) (keep : List (List Sig)),
        rest₁.Perm rest₂ →
        tryGate k t' (search k t') v₁ rest₁ g keep =
          tryGate k t' (search k t') v₂ rest₂ g keep := by
      intro t' rest₁ rest₂ g keep hrest
      have hlen : rest₁.length = rest₂.length := hrest.length_eq
      have hcont : v₁.contains g = v₂.contains g := contains_perm hp g
      have husep : unionSep (decide (0 < t')) rest₁ = unionSep (decide (0 < t')) rest₂ :=
        unionSep_perm hrest
      simp only [tryGate, hcont, hlen, husep]
      congr 1
      refine list_any_eq_of_eq keep _ _ (fun h _ => ?_)
      have hp' : (g :: (h ++ rest₁)).Perm (g :: (h ++ rest₂)) :=
        List.Perm.cons g (List.Perm.append_left h hrest)
      rw [ih t' hp']
    have hcontT : v₁.contains target = v₂.contains target := contains_perm hp target
    have hunary : v₁.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₁ (dropped [a] v₁) (neg a) [[], [a]]) =
        v₂.any (fun a => tryGate k (t - 1) (search k (t - 1)) v₂ (dropped [a] v₂) (neg a) [[], [a]]) := by
      apply Bool.eq_iff_iff.2
      rw [List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.1 ha, ?_⟩
        rw [← htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
      · rintro ⟨a, ha, h⟩
        refine ⟨a, hp.mem_iff.2 ha, ?_⟩
        rw [htry (t - 1) (dropped [a] v₁) (dropped [a] v₂) (neg a) [[], [a]] (dropped_perm hp)]
        exact h
    have hbinary :
        v₁.any (fun a => v₁.any (fun b => before a b &&
          (let rest := dropped [a, b] v₁
           let keep := [[], [a], [b], [a, b]]
           tryGate k t (search k t) v₁ rest (bin false a b) keep ||
           tryGate k t (search k t) v₁ rest (bin true a b) keep))) =
        v₂.any (fun a => v₂.any (fun b => before a b &&
          (let rest := dropped [a, b] v₂
           let keep := [[], [a], [b], [a, b]]
           tryGate k t (search k t) v₂ rest (bin false a b) keep ||
           tryGate k t (search k t) v₂ rest (bin true a b) keep))) := by
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.1 ha, b, hp.mem_iff.1 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨a, hp.mem_iff.2 ha, b, hp.mem_iff.2 hb, ?_⟩
        have h1 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin false a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        have h2 := htry t (dropped [a, b] v₁) (dropped [a, b] v₂) (bin true a b)
          [[], [a], [b], [a, b]] (dropped_perm hp)
        simpa only [h1, h2] using h
    simp only [search, hcontT, hunary, hbinary]

lemma getD_mem_of_ne {W : List Sig} {p : ℕ} (hne : W.getD p zero ≠ zero) :
    W.getD p zero ∈ W := by
  by_cases hp : p < W.length
  · rw [List.getD_eq_getElem _ _ hp]
    exact List.getElem_mem hp
  · rw [List.getD_eq_default _ _ (by omega)] at hne
    exact absurd rfl hne

lemma perm_of_nodup_same_mem {l₁ l₂ : List Sig} (h1 : l₁.Nodup) (h2 : l₂.Nodup)
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Perm l₂ :=
  (List.perm_ext_iff_of_nodup h1 h2).2 hmem

lemma mem_dropped_iff {del v : List Sig} {x : Sig} :
    x ∈ dropped del v ↔ x ∈ v ∧ x ∉ del := by
  simp only [dropped, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, fun hm => ?_⟩
    have hc : del.contains x = true := List.contains_iff_mem.2 hm
    rw [hc] at hnot
    cases hnot
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    cases hc : del.contains x
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot

lemma tryGate_eq_true {k t : ℕ} {r : List Sig → Bool} {v rest : List Sig} {g : Sig}
    {keep : List (List Sig)} (h0 : g ≠ zero) (h1 : g ≠ one) (hnot : g ∉ v)
    (h : List Sig) (hh : h ∈ keep)
    (hlen : rest.length + h.length + 1 ≤ k - t + 1)
    (hsep : (sep (decide (0 < t)) g ||| unionSep (decide (0 < t)) rest) |||
      unionSep (decide (0 < t)) h = top)
    (hr : r (g :: (h ++ rest)) = true) :
    tryGate k t r v rest g keep = true := by
  unfold tryGate
  have hb0 : (g != zero) = true := bne_iff_ne.2 h0
  have hb1 : (g != one) = true := bne_iff_ne.2 h1
  have hbn : (!v.contains g) = true := by
    cases hc : v.contains g
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hnot
  rw [hb0, hb1, hbn]
  simp only [Bool.true_and, List.any_eq_true]
  refine ⟨h, hh, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨hlen, hsep⟩, hr⟩

lemma extract_binary_step {k t : ℕ} {isOr : Bool} {W V' U : List Sig} {sg a0 b0 : Sig}
    (ht : t ≤ k) (hVnd : V'.Nodup) (hVlen : V'.length ≤ k - t + 1)
    (hVsep : unionSep (decide (0 < t)) V' = top) (hVsearch : search k t V' = true)
    (hsgW : sg ∉ W) (hsg0 : sg ≠ zero) (hsg1 : sg ≠ one)
    (hUnd : U.Nodup) (hsgU : sg ∉ U) (hPermV' : V'.Perm (sg :: U))
    (hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one) (hUlen : U.length + 1 = V'.length)
    (ha0W : a0 ∈ W) (hb0W : b0 ∈ W) (ha0_ne0 : a0 ≠ zero) (ha0_ne1 : a0 ≠ one)
    (hb0_ne0 : b0 ≠ zero) (hb0_ne1 : b0 ≠ one) (hab_ne : a0 ≠ b0)
    (hsgeq : sg = bin isOr a0 b0) :
    ∃ V : List Sig,
      V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
      V.length ≤ (k + 1) - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
      search (k + 1) t V = true := by
  obtain ⟨a, b, hab_ord, haW, hbW, ha0, ha1, hb0, hb1, hab, hbin⟩ :
      ∃ a b : Sig, before a b = true ∧ a ∈ W ∧ b ∈ W ∧ a ≠ zero ∧ a ≠ one ∧
        b ≠ zero ∧ b ≠ one ∧ a ≠ b ∧ sg = bin isOr a b := by
    rcases before_trichotomy hab_ne with h | h
    · exact ⟨a0, b0, h, ha0W, hb0W, ha0_ne0, ha0_ne1, hb0_ne0, hb0_ne1, hab_ne, hsgeq⟩
    · exact ⟨b0, a0, h, hb0W, ha0W, hb0_ne0, hb0_ne1, ha0_ne0, ha0_ne1, hab_ne.symm,
        by rw [hsgeq, bin_comm]⟩
  let addA : List Sig := if a ∈ U then [] else [a]
  let addB : List Sig := if b ∈ U then [] else [b]
  let V : List Sig := addA ++ addB ++ U
  have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x = b ∨ x ∈ U := by
    intro x
    simp only [V, addA, addB, List.mem_append]
    constructor
    · intro hx
      rcases hx with (hx | hx) | hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inl hx
      · split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx; exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · rintro (rfl | rfl | hx)
      · by_cases haU : x ∈ U
        · exact Or.inr haU
        · exact Or.inl (Or.inl (by simp [haU]))
      · by_cases hbU : x ∈ U
        · exact Or.inr hbU
        · exact Or.inl (Or.inr (by simp [hbU]))
      · exact Or.inr hx
  have hV_nd : V.Nodup := by
    simp only [V, addA, addB]
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [haU, hbU, hUnd, hab]
  have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
    intro s hs
    rw [hV_mem] at hs
    rcases hs with rfl | rfl | hsU
    · exact ⟨haW, ha0, ha1⟩
    · exact ⟨hbW, hb0, hb1⟩
    · exact hUsub s hsU
  have hV_len : V.length ≤ (k + 1) - t + 1 := by
    have hA : addA.length ≤ 1 := by simp only [addA]; split_ifs <;> simp
    have hB : addB.length ≤ 1 := by simp only [addB]; split_ifs <;> simp
    have hlenV : V.length = addA.length + addB.length + U.length := by
      simp only [V, List.length_append]
    omega
  have hV_sep : unionSep (decide (0 < t)) V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hsV', hsi⟩ := htop
    rw [hPermV'.mem_iff, List.mem_cons] at hsV'
    rcases hsV' with rfl | hsU
    · rw [hbin] at hsi
      rcases sep_bin_bit _ _ a b i hi hsi with ha_b | hb_b
      · exact ⟨a, (hV_mem a).2 (Or.inl rfl), ha_b⟩
      · exact ⟨b, (hV_mem b).2 (Or.inr (Or.inl rfl)), hb_b⟩
    · exact ⟨s, (hV_mem s).2 (Or.inr (Or.inr hsU)), hsi⟩
  let hkeep : List Sig :=
    if a ∈ U then (if b ∈ U then [a, b] else [a]) else (if b ∈ U then [b] else [])
  have hhkeep_mem : hkeep ∈ [[], [a], [b], [a, b]] := by
    simp only [hkeep]; split_ifs <;> simp
  have hdrop_nd : (dropped [a, b] V).Nodup := hV_nd.filter _
  have hperm_next : (sg :: (hkeep ++ dropped [a, b] V)).Perm V' := by
    refine perm_of_nodup_same_mem ?_ hVnd ?_
    · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
      have hkh_nd : hkeep.Nodup := by
        simp only [hkeep]; split_ifs <;> simp [hab]
      rw [List.nodup_cons, List.nodup_append]
      refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
      · intro hm
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · apply hsgU
          simp only [hkeep] at hm
          split_ifs at hm <;> simp at hm <;> rcases hm with rfl | rfl <;> assumption
        · exact hsgV_not (mem_dropped_iff.1 hm).1
      · intro x hx y hy hxy
        subst hxy
        have hynot := (mem_dropped_iff.1 hy).2
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hynot
        simp only [hkeep] at hx
        split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
        · exact hynot.1 rfl
        · exact hynot.2 rfl
    · intro x
      rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
      constructor
      · rintro (rfl | hx | hx)
        · exact Or.inl rfl
        · right
          simp only [hkeep] at hx
          split_ifs at hx <;> simp at hx <;> rcases hx with rfl | rfl <;> assumption
        · right
          have hx' := mem_dropped_iff.1 hx
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
          rw [hV_mem] at hx'
          rcases hx'.1 with rfl | rfl | hxU
          · exact absurd rfl hx'.2.1
          · exact absurd rfl hx'.2.2
          · exact hxU
      · rintro (rfl | hxU)
        · exact Or.inl rfl
        · right
          by_cases hxa : x = a
          · subst hxa; left; simp only [hkeep]; split_ifs <;> simp
          · by_cases hxb : x = b
            · subst hxb; left; simp only [hkeep]; split_ifs <;> simp
            · right
              rw [mem_dropped_iff]
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              exact ⟨(hV_mem x).2 (Or.inr (Or.inr hxU)), hxa, hxb⟩
  have htry_ok : tryGate k t (search k t) V (dropped [a, b] V) (bin isOr a b)
      [[], [a], [b], [a, b]] = true := by
    have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
    rw [← hbin]
    refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
    · have := hperm_next.length_eq
      simp only [List.length_cons, List.length_append] at this
      omega
    · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
      rw [hVsep] at husep
      simp only [unionSep, unionSep_append] at husep
      rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a, b] V)) (unionSep _ hkeep)]
      exact husep
    · rw [search_perm k t hperm_next]
      exact hVsearch
  have hsearch_new : search (k + 1) t V = true := by
    simp only [search, Bool.or_eq_true]
    right
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    refine ⟨ht, a, (hV_mem a).2 (Or.inl rfl), b, (hV_mem b).2 (Or.inr (Or.inl rfl)),
      hab_ord, ?_⟩
    cases isOr
    · simp only [Bool.or_eq_true]; exact Or.inl htry_ok
    · simp only [Bool.or_eq_true]; exact Or.inr htry_ok
  exact ⟨V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

def isNotGate (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

lemma isNotGate_iff (g : Gate) : isNotGate g = true ↔ g.op = GateOp.not := by
  cases g with
  | mk op ins => cases op <;> simp [isNotGate]

lemma notCount_le_one (gs : List Gate)
    (unique : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not →
      (gs.get j).op = GateOp.not → i = j) : gs.countP isNotGate ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g rest ih =>
    by_cases head : isNotGate g = true
    · have tailZero : rest.countP isNotGate = 0 := by
        apply List.countP_eq_zero.mpr
        intro a ha haNot
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
        have h0 : (⟨0, by simp⟩ : Fin (g :: rest).length) = i.succ :=
          unique _ _ ((isNotGate_iff g).mp head)
            (show (rest.get i).op = GateOp.not from hi ▸ (isNotGate_iff a).mp haNot)
        have hval := congrArg Fin.val h0
        simp at hval
      simp [head, tailZero]
    · rw [List.countP_cons_of_neg head]
      apply ih
      intro i j hi hj
      exact Fin.succ_inj.mp (unique i.succ j.succ hi hj)

lemma extract_live (gs : List Gate) (hfan : ∀ g ∈ gs,
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ W : List Sig, target ∈ evalGates gs W →
      ∃ k ≤ gs.length, ∃ t ≤ k, t ≤ gs.countP isNotGate ∧ k + gs.countP isNotGate ≤ gs.length + t ∧ ∃ V : List Sig,
        V.Nodup ∧ (∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one) ∧
        V.length ≤ k - t + 1 ∧ unionSep (decide (0 < t)) V = top ∧
        search k t V = true := by
  induction gs with
  | nil =>
    intro W hT
    refine ⟨0, le_rfl, 0, le_rfl, by simp, by simp, [target], by simp, ?_, by simp, unionSep_target_eq_top, ?_⟩
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst hs
      exact ⟨hT, target_ne_zero, target_ne_one⟩
    · exact List.contains_iff_mem.2 (List.mem_singleton_self target)
  | cons g rest ih =>
    intro W hT
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    rw [evalGates_cons] at hT
    set sg := evalGateSig g W
    obtain ⟨k, hk, t, ht, hbudget, hbinary, V', hVnd, hVsub, hVlen, hVsep, hVsearch⟩ := ih hrest (W ++ [sg]) hT
    have hbudget' : t ≤ (g :: rest).countP isNotGate := by
      rw [List.countP_cons]
      split <;> omega
    have hnewBin : k + (g :: rest).countP isNotGate ≤ (g :: rest).length + t := by
      rw [List.countP_cons, List.length_cons]
      split <;> omega
    by_cases hskip : sg ∉ V' ∨ sg ∈ W
    · refine ⟨k, by simp; omega, t, ht, hbudget', hnewBin, V', hVnd, ?_, hVlen, hVsep, hVsearch⟩
      intro s hs
      obtain ⟨hsmem, hs0, hs1⟩ := hVsub s hs
      rw [List.mem_append, List.mem_singleton] at hsmem
      rcases hsmem with hsmem | rfl
      · exact ⟨hsmem, hs0, hs1⟩
      · rcases hskip with hnot | hin
        · exact absurd hs hnot
        · exact ⟨hin, hs0, hs1⟩
    · push Not at hskip
      obtain ⟨hsgV, hsgW⟩ := hskip
      have hsg01 := hVsub sg hsgV
      have hsg0 : sg ≠ zero := hsg01.2.1
      have hsg1 : sg ≠ one := hsg01.2.2
      set U := V'.erase sg
      have hUnd : U.Nodup := hVnd.erase sg
      have hsgU : sg ∉ U := List.Nodup.not_mem_erase hVnd
      have hPermV' : V'.Perm (sg :: U) := List.perm_cons_erase hsgV
      have hUsub : ∀ s ∈ U, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
        intro s hs
        have hsV : s ∈ V' := List.mem_of_mem_erase hs
        have hsne : s ≠ sg := fun h => hsgU (h ▸ hs)
        obtain ⟨hsm, hs0, hs1⟩ := hVsub s hsV
        rw [List.mem_append, List.mem_singleton] at hsm
        exact ⟨hsm.resolve_right hsne, hs0, hs1⟩
      have hUlen : U.length + 1 = V'.length := by
        have := hPermV'.length_eq
        simp at this
        omega
      rcases hg with ⟨hop, hinlen⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop | hop
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin false (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_left]; rfl
          have hb0_ne0 : b0 ≠ zero := by
            intro h; apply hsg0; rw [hsgeq, h, bin_zero_right]; rfl
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_left]; simpa using hb0W
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsgW; rw [hsgeq, h, bin_one_right]; simpa using ha0W
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          have hpos : ¬isNotGate g = true := by rw [isNotGate_iff, hop]; intro h; cases h
          exact ⟨k + 1, by simp; omega, t, by omega, hbudget',
            by rw [List.countP_cons_of_neg hpos, List.length_cons]; omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
        · exfalso; apply hsg0; simp [sg, evalGateSig, hop, hin]
        · exfalso
          have hsgeq : sg = W.getD p zero := by simp [sg, evalGateSig, hop, hin]
          rw [hsgeq] at hsg0 hsgW
          exact hsgW (getD_mem_of_ne hsg0)
        · have hsgeq : sg = bin true (W.getD p zero) (W.getD q zero) := by
            simp [sg, evalGateSig, hop, hin]
          set a0 := W.getD p zero
          set b0 := W.getD q zero
          have ha0_ne0 : a0 ≠ zero := by
            intro h
            have hsgeq' : sg = b0 := by rw [hsgeq, h, bin_zero_left]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have hb0_ne0 : b0 ≠ zero := by
            intro h
            have hsgeq' : sg = a0 := by rw [hsgeq, h, bin_zero_right]; rfl
            rw [hsgeq'] at hsg0 hsgW
            exact hsgW (getD_mem_of_ne hsg0)
          have ha0W : a0 ∈ W := getD_mem_of_ne ha0_ne0
          have hb0W : b0 ∈ W := getD_mem_of_ne hb0_ne0
          have ha0_ne1 : a0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_left]; rfl
          have hb0_ne1 : b0 ≠ one := by
            intro h; apply hsg1; rw [hsgeq, h, bin_one_right]; rfl
          have hab_ne : a0 ≠ b0 := by
            intro h; apply hsgW; rw [hsgeq, h, bin_self]; exact hb0W
          obtain ⟨V, hV⟩ := extract_binary_step ht hVnd hVlen hVsep hVsearch hsgW hsg0 hsg1
            hUnd hsgU hPermV' hUsub hUlen ha0W hb0W ha0_ne0 ha0_ne1 hb0_ne0 hb0_ne1 hab_ne hsgeq
          have hpos : ¬isNotGate g = true := by rw [isNotGate_iff, hop]; intro h; cases h
          exact ⟨k + 1, by simp; omega, t, by omega, hbudget',
            by rw [List.countP_cons_of_neg hpos, List.length_cons]; omega, V, hV⟩
        · rw [hin] at hinlen; simp at hinlen
      · rcases hin : g.inputs with _ | ⟨p, _⟩
        · exfalso; apply hsg1; simp [sg, evalGateSig, hop, hin]
        · have hsgeq : sg = neg (W.getD p zero) := by simp [sg, evalGateSig, hop, hin]
          set a := W.getD p zero
          have ha0 : a ≠ zero := by intro h; apply hsg1; rw [hsgeq, h, neg_zero]
          have ha1 : a ≠ one := by intro h; apply hsg0; rw [hsgeq, h, neg_one]
          have haW : a ∈ W := getD_mem_of_ne ha0
          let V : List Sig := if a ∈ U then U else a :: U
          have hV_mem : ∀ x, x ∈ V ↔ x = a ∨ x ∈ U := by
            intro x
            simp only [V]
            by_cases haU : a ∈ U
            · simp only [haU, ↓reduceIte]
              exact ⟨Or.inr, fun h => h.elim (fun hxa => hxa ▸ haU) id⟩
            · simp only [haU, ↓reduceIte, List.mem_cons]
          have hV_nd : V.Nodup := by
            simp only [V]
            by_cases haU : a ∈ U <;> simp [haU, hUnd]
          have hV_sub : ∀ s ∈ V, s ∈ W ∧ s ≠ zero ∧ s ≠ one := by
            intro s hs
            rw [hV_mem] at hs
            rcases hs with rfl | hsU
            · exact ⟨haW, ha0, ha1⟩
            · exact hUsub s hsU
          have hV_len : V.length ≤ (k + 1) - (t + 1) + 1 := by
            have : V.length ≤ U.length + 1 := by simp only [V]; split_ifs <;> simp
            omega
          have hV_sep : unionSep (decide (0 < t + 1)) V = top := by
            apply bv_eq_top_of_bits
            intro i hi
            rw [unionSep_bit_iff _ _ i hi]
            have htop : (unionSep (decide (0 < t)) V')[i] = true := by rw [hVsep]; exact top_bit i hi
            rw [unionSep_bit_iff _ _ i hi] at htop
            obtain ⟨s, hsV', hsi⟩ := htop
            have hsi' : (sep true s)[i] = true := sep_mono_true _ s i hi hsi
            rw [hPermV'.mem_iff, List.mem_cons] at hsV'
            rcases hsV' with rfl | hsU
            · rw [hsgeq, sep_neg_true a i hi] at hsi'
              exact ⟨a, (hV_mem a).2 (Or.inl rfl), by simpa using hsi'⟩
            · exact ⟨s, (hV_mem s).2 (Or.inr hsU), by simpa using hsi'⟩
          let hkeep : List Sig := if a ∈ U then [a] else []
          have hhkeep_mem : hkeep ∈ [[], [a]] := by simp only [hkeep]; split_ifs <;> simp
          have hdrop_nd : (dropped [a] V).Nodup := hV_nd.filter _
          have hperm_next : (sg :: (hkeep ++ dropped [a] V)).Perm V' := by
            refine perm_of_nodup_same_mem ?_ hVnd ?_
            · have hsgV_not : sg ∉ V := fun h => hsgW (hV_sub sg h).1
              have hkh_nd : hkeep.Nodup := by simp only [hkeep]; split_ifs <;> simp
              rw [List.nodup_cons, List.nodup_append]
              refine ⟨?_, hkh_nd, hdrop_nd, ?_⟩
              · intro hm
                rw [List.mem_append] at hm
                rcases hm with hm | hm
                · apply hsgU
                  simp only [hkeep] at hm
                  split_ifs at hm <;> simp at hm
                  rw [hm]; assumption
                · exact hsgV_not (mem_dropped_iff.1 hm).1
              · intro x hx y hy hxy
                subst hxy
                have hynot := (mem_dropped_iff.1 hy).2
                simp only [List.mem_singleton] at hynot
                simp only [hkeep] at hx
                split_ifs at hx <;> simp at hx
                exact hynot hx
            · intro x
              rw [hPermV'.mem_iff, List.mem_cons, List.mem_cons, List.mem_append]
              constructor
              · rintro (rfl | hx | hx)
                · exact Or.inl rfl
                · right
                  simp only [hkeep] at hx
                  split_ifs at hx <;> simp at hx
                  subst hx; assumption
                · right
                  have hx' := mem_dropped_iff.1 hx
                  simp only [List.mem_singleton] at hx'
                  rw [hV_mem] at hx'
                  exact hx'.1.resolve_left hx'.2
              · rintro (rfl | hxU)
                · exact Or.inl rfl
                · right
                  by_cases hxa : x = a
                  · subst hxa; left; simp only [hkeep]; split_ifs; simp
                  · right
                    rw [mem_dropped_iff]
                    simp only [List.mem_singleton]
                    exact ⟨(hV_mem x).2 (Or.inr hxU), hxa⟩
          have hsearch_new : search (k + 1) (t + 1) V = true := by
            simp only [search, Bool.or_eq_true]
            left
            right
            simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
            refine ⟨by omega, a, (hV_mem a).2 (Or.inl rfl), ?_⟩
            simp only [Nat.add_sub_cancel]
            have hsg_notV : sg ∉ V := fun h => hsgW (hV_sub sg h).1
            rw [← hsgeq]
            refine tryGate_eq_true hsg0 hsg1 hsg_notV hkeep hhkeep_mem ?_ ?_ ?_
            · have := hperm_next.length_eq
              simp only [List.length_cons, List.length_append] at this
              omega
            · have husep := unionSep_perm (d := decide (0 < t)) hperm_next
              rw [hVsep] at husep
              simp only [unionSep, unionSep_append] at husep
              rw [BitVec.or_assoc, BitVec.or_comm (unionSep _ (dropped [a] V)) (unionSep _ hkeep)]
              exact husep
            · rw [search_perm k t hperm_next]
              exact hVsearch
          exact ⟨k + 1, by simp; omega, t + 1, by omega, by simpa [(isNotGate_iff g).mpr hop] using Nat.succ_le_succ hbudget,
            by rw [List.countP_cons_of_pos ((isNotGate_iff g).mpr hop), List.length_cons]; omega,
            V, hV_nd, hV_sub, hV_len, hV_sep, hsearch_new⟩

lemma wiresToSigs_getD (wa wb : Fin 256 → List Bool) (len : ℕ)
    (hwa : ∀ r, (wa r).length = len) (hwb : ∀ r, (wb r).length = len) (i : ℕ) :
    (wiresToSigs wa wb len).getD i zero =
      (mkBV (fun r => (wa r).getD i false),
       mkBV (fun r => (wb r).getD i false)) := by
  by_cases hi : i < len
  · have hlen : (wiresToSigs wa wb len).length = len := by simp [wiresToSigs]
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp [wiresToSigs]
  · have hlen : (wiresToSigs wa wb len).length = len := by simp [wiresToSigs]
    rw [List.getD_eq_default _ _ (by omega)]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [zero, getElem_mkBV]
      rw [zero_bit r hr, List.getD_eq_default _ _ (by rw [hwa ⟨r, hr⟩]; omega)]
    · simp only [zero, getElem_mkBV]
      rw [zero_bit r hr, List.getD_eq_default _ _ (by rw [hwb ⟨r, hr⟩]; omega)]

lemma wiresToSigs_step (wa wb : Fin 256 → List Bool) (len : ℕ)
    (hwa : ∀ r, (wa r).length = len) (hwb : ∀ r, (wb r).length = len)
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    wiresToSigs
      (fun r => wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])
      (fun r => wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])
      (len + 1) =
    wiresToSigs wa wb len ++ [evalGateSig g (wiresToSigs wa wb len)] := by
  have hprefix :
      (List.range len).map (fun idx =>
        (mkBV (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD idx false),
         mkBV (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD idx false))) =
      wiresToSigs wa wb len := by
    unfold wiresToSigs
    apply List.map_congr_left
    intro idx hidx
    rw [List.mem_range] at hidx
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [getElem_mkBV]
      rw [List.getD_eq_getElem _ _ (by simp [hwa ⟨r, hr⟩]; omega),
        List.getElem_append_left (by rw [hwa ⟨r, hr⟩]; omega),
        List.getD_eq_getElem _ _ (by rw [hwa ⟨r, hr⟩]; omega)]
    · simp only [getElem_mkBV]
      rw [List.getD_eq_getElem _ _ (by simp [hwb ⟨r, hr⟩]; omega),
        List.getElem_append_left (by rw [hwb ⟨r, hr⟩]; omega),
        List.getD_eq_getElem _ _ (by rw [hwb ⟨r, hr⟩]; omega)]
  have hlast :
      (mkBV (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD len false),
       mkBV (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD len false)) =
      evalGateSig g (wiresToSigs wa wb len) := by
    have hgetLast : ∀ (w : List Bool) (v : Bool), w.length = len → (w ++ [v]).getD len false = v := by
      intro w v hw
      rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_append_right (by omega)]
      simp [hw]
    have hA : (fun r => (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)]).getD len false) =
        fun r => g.op.eval (g.inputs.map fun i => (wa r).getD i false) := by
      funext r; exact hgetLast (wa r) _ (hwa r)
    have hB : (fun r => (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)]).getD len false) =
        fun r => g.op.eval (g.inputs.map fun i => (wb r).getD i false) := by
      funext r; exact hgetLast (wb r) _ (hwb r)
    rw [hA, hB]
    rcases hg with ⟨hop, hinlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop | hop
    · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.all_nil]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [one, top, getElem_mkBV, BitVec.getElem_allOnes]
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact (wiresToSigs_getD wa wb len hwa hwb p).symm
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true]
        rw [wiresToSigs_getD wa wb len hwa hwb p, wiresToSigs_getD wa wb len hwa hwb q]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [bin, Bool.false_eq_true, ↓reduceIte, BitVec.getElem_and, getElem_mkBV]
      · rw [hin] at hinlen; simp at hinlen
    · rcases hin : g.inputs with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.any_nil]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          (simp only [zero, getElem_mkBV]; exact (zero_bit r hr).symm)
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact (wiresToSigs_getD wa wb len hwa hwb p).symm
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        rw [wiresToSigs_getD wa wb len hwa hwb p, wiresToSigs_getD wa wb len hwa hwb q]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [bin, ↓reduceIte, BitVec.getElem_or, getElem_mkBV]
      · rw [hin] at hinlen; simp at hinlen
    · rcases hin : g.inputs with _ | ⟨p, _⟩
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_nil, List.headD_nil, Bool.not_false]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [one, top, getElem_mkBV, BitVec.getElem_allOnes]
      · simp only [evalGateSig, hop, hin, GateOp.eval, List.map_cons, List.headD_cons]
        rw [wiresToSigs_getD wa wb len hwa hwb p]
        apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr <;>
          simp only [neg, BitVec.getElem_not, getElem_mkBV]
  show (List.range (len + 1)).map _ = _
  rw [List.range_succ, List.map_append, List.map_singleton, hprefix, hlast]

lemma evalWires_len (gs : List Gate) (w : List Bool) :
    (evalWires gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalWires]
  | cons g rest ih =>
    rw [evalWires_cons, ih]
    simp
    omega

lemma wiresToSigs_evalGates (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (wa wb : Fin 256 → List Bool) (len : ℕ),
      (∀ r, (wa r).length = len) → (∀ r, (wb r).length = len) →
      wiresToSigs (fun r => evalWires gs (wa r)) (fun r => evalWires gs (wb r)) (len + gs.length) =
        evalGates gs (wiresToSigs wa wb len) := by
  induction gs with
  | nil =>
    intro wa wb len _ _
    simp [evalWires, evalGates]
  | cons g rest ih =>
    intro wa wb len hwa hwb
    have hg := hfan g List.mem_cons_self
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem g hg')
    have h1 := ih hrest
      (fun r => wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])
      (fun r => wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])
      (len + 1)
      (fun r => by simp [hwa r])
      (fun r => by simp [hwb r])
    simp only [List.length_cons]
    rw [show len + (rest.length + 1) = len + 1 + rest.length by omega]
    have hwa_eq : (fun r => evalWires (g :: rest) (wa r)) =
        (fun r => evalWires rest (wa r ++ [g.op.eval (g.inputs.map fun i => (wa r).getD i false)])) := rfl
    have hwb_eq : (fun r => evalWires (g :: rest) (wb r)) =
        (fun r => evalWires rest (wb r ++ [g.op.eval (g.inputs.map fun i => (wb r).getD i false)])) := rfl
    rw [hwa_eq, hwb_eq, evalGates_cons, h1, wiresToSigs_step wa wb len hwa hwb g hg]

def wireX (v : List Sig) (side : Bool) (r : Fin 256) (i : Fin 5) : Bool :=
  (if side then (v.getD i zero).1 else (v.getD i zero).2)[r.val]

lemma wiresToSigs_init (v : List Sig) (hv : v.length = 5) :
    wiresToSigs (fun r => List.ofFn (wireX v true r))
      (fun r => List.ofFn (wireX v false r)) 5 = v := by
  apply List.ext_getElem
  · simp [wiresToSigs, hv]
  · intro i hi hj
    have hi5 : i < 5 := by omega
    simp only [wiresToSigs, List.getElem_map, List.getElem_range]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    all_goals
      simp only [getElem_mkBV, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi5,
        ↓reduceDIte, Option.getD_some, wireX, List.getElem?_eq_getElem hj, Bool.true_eq,
        ↓reduceIte, Bool.false_eq_true]

def sampleMask (x : Fin 5 → Bool) : ℕ :=
  ∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0

lemma sample_lower (C : Circuit) (v : List Sig) (bound table : ℕ)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit table (sampleMask x))
    (hlenv : v.length = 5) (hnd : v.Nodup)
    (essential : v.all (fun s => unionSep true (v.erase s) != top) = true)
    (positive : ∀ r : Fin 256, Nat.testBit table (sampleMask (wireX v true r)) = true)
    (negative : ∀ r : Fin 256, Nat.testBit table (sampleMask (wireX v false r)) = false)
    (noRun : ∀ k t, k < bound → t ≤ k → t ≤ 1 → k + 1 < bound + t → 5 ≤ k - t + 1 → search k t v = false) :
    bound ≤ C.size := by
  by_contra small
  have hlen : C.gates.length < bound := by
    change ¬ bound ≤ C.gates.length at small
    omega
  let pairA := wireX v true
  let pairB := wireX v false
  have initList_eq := wiresToSigs_init v hlenv
  have all_init_needed : ∀ s ∈ v, unionSep true (v.erase s) ≠ top :=
    fun s hs => bne_iff_ne.1 (List.all_eq_true.1 essential s hs)
  have accepts (r : Fin 256) := (hcorrect (pairA r)).trans (positive r)
  have rejects (r : Fin 256) := (hcorrect (pairB r)).trans (negative r)
  have hW := wiresToSigs_evalGates C.gates hfan
    (fun r => List.ofFn (pairA r)) (fun r => List.ofFn (pairB r)) 5
    (fun r => by simp) (fun r => by simp)
  have htarget_eq : (evalGates C.gates v).getD C.output zero = target := by
    rw [← initList_eq, ← hW]
    rw [wiresToSigs_getD _ _ (5 + C.gates.length)
      (fun r => by rw [evalWires_len]; simp)
      (fun r => by rw [evalWires_len]; simp) C.output]
    apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro r hr
    · simp only [target, top, getElem_mkBV, BitVec.getElem_allOnes]
      exact accepts ⟨r, hr⟩
    · simp only [target, getElem_mkBV]
      rw [zero_bit r hr]
      exact rejects ⟨r, hr⟩
  have hTmem : target ∈ evalGates C.gates v :=
    htarget_eq ▸ getD_mem_of_ne (by rw [htarget_eq]; exact target_ne_zero)
  obtain ⟨k, hk, t, ht, hbudget, hbinary, V, hVnd, hVsub, hVlen, hVsep, hVsearch⟩ :=
    extract_live C.gates hfan v hTmem
  have hVsep_true : unionSep true V = top := by
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep (decide (0 < t)) V)[i] = true := by rw [hVsep]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨s, hs, hsi⟩ := htop
    exact ⟨s, hs, sep_mono_true _ s i hi hsi⟩
  have hall_in_V : ∀ s ∈ v, s ∈ V := by
    intro s hs
    by_contra hnot
    apply all_init_needed s hs
    apply bv_eq_top_of_bits
    intro i hi
    rw [unionSep_bit_iff _ _ i hi]
    have htop : (unionSep true V)[i] = true := by rw [hVsep_true]; exact top_bit i hi
    rw [unionSep_bit_iff _ _ i hi] at htop
    obtain ⟨u, huV, hui⟩ := htop
    have huInit : u ∈ v := (hVsub u huV).1
    have hune : u ≠ s := fun h => hnot (h ▸ huV)
    exact ⟨u, (List.mem_erase_of_ne hune).2 huInit, hui⟩
  have hPermInit : V.Perm v :=
    perm_of_nodup_same_mem hVnd hnd (fun x => ⟨fun h => (hVsub x h).1, hall_in_V x⟩)
  have hVlen5 : V.length = 5 := hPermInit.length_eq.trans hlenv
  have hsearch_init : search k t v = true := by
    rw [← search_perm k t hPermInit]
    exact hVsearch
  have hn := noRun k t (lt_of_le_of_lt hk hlen) ht (by omega) (by omega) (hVlen5 ▸ hVlen)
  simp [hn] at hsearch_init


def oneRound (k t : Nat) (v : List Sig) (r : Nat → List Sig → Bool) : Bool :=
  v.contains target ||
    (decide (0 < t) && v.any (fun a =>
      tryGate k (t - 1) (r (t - 1)) v (dropped [a] v) (neg a) [[], [a]])) ||
    (decide (t ≤ k) && v.any (fun a => v.any (fun b =>
      before a b &&
        (let rest := dropped [a, b] v
         let keep := [[], [a], [b], [a, b]]
         tryGate k t (r t) v rest (bin false a b) keep ||
         tryGate k t (r t) v rest (bin true a b) keep))))

lemma negRound (k t : Nat) (v : List Sig) (r : Nat → List Sig → Bool)
    (hr : ∀ t' w, search k t' w = true → r t' w = true)
    (h : oneRound k t v r = false) : search (k+1) t v = false := by
  have gate (t' : Nat) (rest : List Sig) (g : Sig) (keep : List (List Sig))
      (hp : tryGate k t' (search k t') v rest g keep = true) :
      tryGate k t' (r t') v rest g keep = true := by
    simp only [tryGate, Bool.and_eq_true, List.any_eq_true] at hp ⊢
    obtain ⟨ha, s, hs, hb, hc⟩ := hp
    exact ⟨ha, s, hs, hb, hr t' _ hc⟩
  apply Bool.eq_false_iff.mpr
  intro hx
  have hy : oneRound k t v r = true := by
    change oneRound k t v (search k) = true at hx
    simp only [oneRound, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at hx ⊢
    rcases hx with (hx | ⟨ht, a, ha, hnot⟩) | ⟨ht, a, ha, b, hb, hab, hop⟩
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr ⟨ht, a, ha, gate _ _ _ _ hnot⟩)
    · exact Or.inr ⟨ht, a, ha, b, hb, hab, hop.imp (gate _ _ _ _) (gate _ _ _ _)⟩
  simp [h] at hy

def pathStep (wire : List Sig) (op : Nat) : List Sig :=
  if op = 1023 then wire else
  let a := wire.getD (op % 8) zero
  let b := wire.getD (op / 8 % 8) zero
  let kind := op / 64 % 3
  let keep := op / 192
  let ls := if keep % 2 = 1 then [a] else []
  let rs := if keep ≥ 2 then [b] else []
  if kind = 2 then neg a :: (ls ++ dropped [a] wire)
  else bin (kind = 1) a b :: (ls ++ rs ++ dropped [a,b] wire)

def stateHash (v : List Sig) : Nat :=
  v.foldl (fun acc s =>
    let n := (s.1.toNat ^^^ s.2.toNat ^^^ (s.1.toNat >>> 71) ^^^ (s.2.toNat >>> 113)) % 4294967291
    acc + n*n*n) 0 % 18446744073709551557

def takeField (word width i : Nat) : Nat := (word >>> (width*i)) &&& (2^width-1)

def rowBits (p : Fin 256 → Fin 256) (s : B) : B := mkBV fun i => s[(p i).val]

def rowSig (p : Fin 256 → Fin 256) (s : Sig) : Sig := (rowBits p s.1, rowBits p s.2)

lemma rowBits_bit (p : Fin 256 → Fin 256) (s : B) (i : ℕ) (hi : i < 256) :
    (rowBits p s)[i] = s[(p ⟨i, hi⟩).val] := getElem_mkBV _ i hi

lemma rowBits_invol (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) (s : B) :
    rowBits p (rowBits p s) = s := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [rowBits_bit, hp]

lemma rowSig_inj (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) :
    Function.Injective (rowSig p) := by
  intro a b hab
  have h := congrArg (rowSig p) hab
  simpa only [rowSig, rowBits_invol p hp] using h

lemma rowBits_or (p : Fin 256 → Fin 256) (a b : B) :
    rowBits p (a ||| b) = rowBits p a ||| rowBits p b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [rowBits_bit, BitVec.getElem_or]

lemma rowBits_and (p : Fin 256 → Fin 256) (a b : B) :
    rowBits p (a &&& b) = rowBits p a &&& rowBits p b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [rowBits_bit, BitVec.getElem_and]

lemma rowBits_top (p : Fin 256 → Fin 256) : rowBits p top = top := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [rowBits_bit, top, BitVec.getElem_allOnes]

lemma rowBits_zero (p : Fin 256 → Fin 256) : rowBits p 0 = 0 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [rowBits_bit]

lemma rowSig_target (p : Fin 256 → Fin 256) : rowSig p target = target := by
  exact Prod.ext (rowBits_top p) (rowBits_zero p)

lemma rowSig_zero (p : Fin 256 → Fin 256) : rowSig p zero = zero := by
  exact Prod.ext (rowBits_zero p) (rowBits_zero p)

lemma rowSig_one (p : Fin 256 → Fin 256) : rowSig p one = one := by
  simp [rowSig, one, rowBits_top]

lemma rowSig_neg (p : Fin 256 → Fin 256) (s : Sig) : rowSig p (neg s) = neg (rowSig p s) := by
  apply Prod.ext <;> apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
    simp only [rowSig, neg, rowBits_bit, BitVec.getElem_not]

lemma rowSig_bin (p : Fin 256 → Fin 256) (b : Bool) (a c : Sig) :
    rowSig p (bin b a c) = bin b (rowSig p a) (rowSig p c) := by
  cases b <;> simp [rowSig, bin, rowBits_or, rowBits_and]

lemma rowSep (p : Fin 256 → Fin 256) (d : Bool) (a : Sig) :
    sep d (rowSig p a) = rowBits p (sep d a) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  cases d <;> simp [sep, rowSig, rowBits_bit]

lemma rowUnion (p : Fin 256 → Fin 256) (d : Bool) (l : List Sig) :
    unionSep d (l.map (rowSig p)) = rowBits p (unionSep d l) := by
  induction l with
  | nil => exact (rowBits_zero p).symm
  | cons a l ih => simp [unionSep, ih, rowSep, rowBits_or]

lemma rowDropped (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) (u v : List Sig) :
    dropped (u.map (rowSig p)) (v.map (rowSig p)) = (dropped u v).map (rowSig p) := by
  have hinj := rowSig_inj p hp
  unfold dropped
  rw [List.filter_map]
  congr 2
  funext a
  change (!(u.map (rowSig p)).contains (rowSig p a)) = (!u.contains a)
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map, hinj.eq_iff, exists_eq_right]

lemma tryData {k t : ℕ} {r : List Sig → Bool} {v rest : List Sig} {g : Sig}
    {keep : List (List Sig)} (hg : tryGate k t r v rest g keep = true) :
    g ≠ zero ∧ g ≠ one ∧ g ∉ v ∧ ∃ h ∈ keep,
    rest.length + h.length + 1 ≤ k-t+1 ∧
    (sep (decide (0 < t)) g ||| unionSep (decide (0 < t)) rest) |||
        unionSep (decide (0 < t)) h = top ∧ r (g :: (h ++ rest)) = true := by
  simpa [tryGate, List.any_eq_true, Bool.and_eq_true, and_assoc] using hg

lemma rowTry (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) {k t : ℕ}
    (ih : ∀ V, search k t V = true → search k t (V.map (rowSig p)) = true)
    {v rest : List Sig} {g : Sig} {keep keep' : List (List Sig)}
    (hkeep : ∀ h ∈ keep, ∃ h' ∈ keep', h'.Perm (h.map (rowSig p)))
    (hs : tryGate k t (search k t) v rest g keep = true) :
    tryGate k t (search k t) (v.map (rowSig p)) (rest.map (rowSig p)) (rowSig p g) keep' = true := by
  obtain ⟨hz,ho,hn,h,hh,hl,hsep,hr⟩ := tryData hs
  obtain ⟨h',hh',perm⟩ := hkeep h hh
  have inj := rowSig_inj p hp
  apply tryGate_eq_true _ _ _ h' hh'
  · simpa only [List.length_map, perm.length_eq] using hl
  · rw [unionSep_perm perm, rowUnion, rowUnion, rowSep, ← rowBits_or, ← rowBits_or,
      hsep, rowBits_top]
  · have mapped := ih _ hr
    have hperm := List.Perm.cons (rowSig p g) (perm.append_right (rest.map (rowSig p)))
    rw [search_perm k t hperm]
    simpa using mapped
  · exact fun h0 => hz (inj (h0.trans (rowSig_zero p).symm))
  · exact fun h1 => ho (inj (h1.trans (rowSig_one p).symm))
  · simpa [List.mem_map, inj.eq_iff] using hn

def edgeRun (k t : ℕ) (v : List Sig) (d : Bool) (a b : Sig) : Bool :=
  tryGate k t (search k t) v (dropped [a,b] v) (bin d a b) [[],[a],[b],[a,b]]

lemma dropped_swap (a b : Sig) (v : List Sig) : dropped [a,b] v = dropped [b,a] v := by
  unfold dropped
  apply List.filter_congr
  intro s _
  simp only [List.contains_cons, List.contains_nil, Bool.false_or, Bool.or_false]
  rw [Bool.or_comm]

lemma rowEdge (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) {k t : ℕ}
    (ih : ∀ V, search k t V = true → search k t (V.map (rowSig p)) = true)
    {v : List Sig} {a b : Sig} {d : Bool} (h : edgeRun k t v d a b = true) :
    edgeRun k t (v.map (rowSig p)) d (rowSig p a) (rowSig p b) = true ∧
    edgeRun k t (v.map (rowSig p)) d (rowSig p b) (rowSig p a) = true := by
  let f := rowSig p
  have move (K : List (List Sig)) (hk : ∀ u ∈ [[],[a],[b],[a,b]],
      ∃ z ∈ K, z.Perm (u.map f)) :
      tryGate k t (search k t) (v.map f) (dropped [f a,f b] (v.map f)) (bin d (f a) (f b)) K = true := by
    have zz := rowTry p hp ih hk h
    rw [← rowDropped p hp [a,b] v, rowSig_bin] at zz
    exact zz
  constructor
  · apply move
    intro u hu
    refine ⟨u.map f, ?_, .refl _⟩
    simpa only [List.map_cons, List.map_nil] using
      (List.mem_map_of_mem (f := List.map f) hu)
  · unfold edgeRun
    rw [dropped_swap (rowSig p b) (rowSig p a), bin_comm d (rowSig p b) (rowSig p a)]
    apply move
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl
    · exact ⟨[], by simp, .refl _⟩
    · exact ⟨[f a], by simp [f], .refl _⟩
    · exact ⟨[f b], by simp [f], .refl _⟩
    · exact ⟨[f b,f a], by simp [f], .swap _ _ _⟩

lemma rowSearch (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i) :
    ∀ k t v, search k t v = true → search k t (v.map (rowSig p)) = true := by
  intro k
  induction k with
  | zero =>
    intro t v hs
    simp only [search, List.contains_iff_mem] at hs ⊢
    exact rowSig_target p ▸ (List.mem_map_of_mem (f := rowSig p) hs)
  | succ k ih =>
    intro t v hs
    simp only [search, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
      List.contains_iff_mem, decide_eq_true_eq] at hs ⊢
    rcases hs with (ha | ⟨ht,a,ha,hnot⟩) | ⟨ht,a,ha,b,hb,hab,habop⟩
    · exact Or.inl (Or.inl (rowSig_target p ▸ (List.mem_map_of_mem (f := rowSig p) ha)))
    · refine Or.inl (Or.inr ⟨ht,rowSig p a,List.mem_map_of_mem ha,?_⟩)
      have hk : ∀ u ∈ [[],[a]], ∃ z ∈ [[], [rowSig p a]], z.Perm (u.map (rowSig p)) := by
        intro u hu
        refine ⟨_, ?_, .refl _⟩
        simpa only [List.map_cons, List.map_nil] using
          (List.mem_map_of_mem (f := List.map (rowSig p)) hu)
      have zz := rowTry p hp (ih (t-1)) hk hnot
      rw [← rowDropped p hp [a] v, rowSig_neg] at zz
      exact zz
    · right
      refine ⟨ht, ?_⟩
      have hne : rowSig p a ≠ rowSig p b := by
        intro he
        obtain rfl := rowSig_inj p hp he
        simp [before] at hab
      have hsort := before_trichotomy hne
      rcases hsort with hlt|hlt
      · refine ⟨rowSig p a, List.mem_map_of_mem ha, rowSig p b, List.mem_map_of_mem hb, hlt, ?_⟩
        rcases habop with hh|hh
        · exact Or.inl (rowEdge p hp (ih t) (d := false) hh).1
        · exact Or.inr (rowEdge p hp (ih t) (d := true) hh).1
      · refine ⟨rowSig p b, List.mem_map_of_mem hb, rowSig p a, List.mem_map_of_mem ha, hlt, ?_⟩
        rcases habop with hh|hh
        · exact Or.inl (rowEdge p hp (ih t) (d := false) hh).2
        · exact Or.inr (rowEdge p hp (ih t) (d := true) hh).2

def packedSwap (code : ℕ) (i : Fin 256) : Fin 256 :=
  ⟨(code >>> (8 * i.val)) % 256, Nat.mod_lt _ (by decide)⟩


def v_eae8e800 : List Sig :=
  [(115792088805957871501439408897036743934658157590416147955223623669442576121855, 3827888368706363051558477129442195477686831428038274947117714303567798954),
   (115792089237315372672861596846363856296719279935419864958427147850829724647423, 64136325694471138602425131114940657246381433856935189569219093251259253964),
   (115792089237316195422001709574846946653081861149323266573610524684460202917888, 128200182914078329831325152453259014645991244130378106184740217604276521200),
   (115792089237316195423570985008682198862499160826116330971137649753281922072575, 199543670977756806034092748733707920939160099612247203553873979616411455232),
   (115792089237316195423570985008687907853269984665640563963899720281998806220800, 224390005216824476956987529289925011260859613952455073393177601870806904832)]

set_option maxRecDepth 10000 in
lemma nodup_eae8e800 : v_eae8e800.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eae8e800 : v_eae8e800.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eae8e800 : v_eae8e800.all (fun s => unionSep true (v_eae8e800.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eae8e800 : ∀ r : Fin 256, Nat.testBit 0xeae8e800 (sampleMask (wireX v_eae8e800 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eae8e800 : ∀ r : Fin 256, Nat.testBit 0xeae8e800 (sampleMask (wireX v_eae8e800 false r)) = false := by decide +kernel

def v_e8e8e888 : List Sig :=
  [(115792061630436120552984392450516392524273432151330734722848134141403067318271, 965199105048353576196696263555041197544380644314392669255786930245290461330),
   (115792089237210883533636938886737536410416709379719412650033005877382327828479, 1930398210096707152393392527110082395088761288628785338511573860490580922660),
   (115792089237316195021838006439481204856552749660165382760651319418305392672768, 3860354706742216614230777184526872625565637957089701839922635948460026765880),
   (115792089237316195423569452513147041964411626643131967388700692051878247137280, 6811221417468388373641350670565178315260842988537468089891532275902924964800),
   (115792089237316195423570985008687907853269984341122010381030857224757109063680, 7208763523546309874048433394528126465957001139619421480352127544924496460800)]

set_option maxRecDepth 10000 in
lemma nodup_e8e8e888 : v_e8e8e888.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_e8e8e888 : v_e8e8e888.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_e8e8e888 : v_e8e8e888.all (fun s => unionSep true (v_e8e8e888.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_e8e8e888 : ∀ r : Fin 256, Nat.testBit 0xe8e8e888 (sampleMask (wireX v_e8e8e888 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_e8e8e888 : ∀ r : Fin 256, Nat.testBit 0xe8e8e888 (sampleMask (wireX v_e8e8e888 false r)) = false := by decide +kernel

def v_eaa8a8a8 : List Sig :=
  [(115792061630436120552984392456362376772851845293523570453311912469070545420287, 58361389739494864712539783226227249345255439679670101905117944354972371010),
   (115792089237210883533635406397042677070881962705505763741119948787881037004799, 2392872193500689164533632095986978743731958604387457782747399690119009096340),
   (115792089237316195021836473949786345517018002985952971777610502303665593516032, 4318853269085419411366945926164139492701873691337554750253855825398239224600),
   (115792089237316195423570985002841901303946373317344378367019160698046910562304, 6359790270344348625401307844020586081914761176975516573168500759302873777120),
   (115792089237316195423570985008687907853269984341122010381030857224757109063680, 7208763523546309874048433394528126465957001139619421480352127544924496460800)]

set_option maxRecDepth 10000 in
lemma nodup_eaa8a8a8 : v_eaa8a8a8.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eaa8a8a8 : v_eaa8a8a8.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eaa8a8a8 : v_eaa8a8a8.all (fun s => unionSep true (v_eaa8a8a8.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eaa8a8a8 : ∀ r : Fin 256, Nat.testBit 0xeaa8a8a8 (sampleMask (wireX v_eaa8a8a8 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eaa8a8a8 : ∀ r : Fin 256, Nat.testBit 0xeaa8a8a8 (sampleMask (wireX v_eaa8a8a8 false r)) = false := by decide +kernel

def v_eaa8e888 : List Sig :=
  [(115792061630436120552984392456362376772851845293522332517994993571665291509759, 60569956995483317492579131692688072404678540519014287407676806960647768210),
   (115792089237210883533635406397042677070881962705507001671714519216883874398207, 2382712784123142281745451093041258957658612340526474529435628922132902269220),
   (115792089237316195021836473949786345517018002985952971782332832757806939242496, 4312669280768651743582835750458049188135489008987391030846691010102348112440),
   (115792089237316195423570985002841901303946373317344378367019178712376700567552, 6358906843441953244289292104634001752690991936639778898967477214260603618240),
   (115792089237316195423570985008687907853269984341122010381030857224757109063680, 7208763523546309874048433394528126465957001139619421480352127544924496460800)]

set_option maxRecDepth 10000 in
lemma nodup_eaa8e888 : v_eaa8e888.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eaa8e888 : v_eaa8e888.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eaa8e888 : v_eaa8e888.all (fun s => unionSep true (v_eaa8e888.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eaa8e888 : ∀ r : Fin 256, Nat.testBit 0xeaa8e888 (sampleMask (wireX v_eaa8e888 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eaa8e888 : ∀ r : Fin 256, Nat.testBit 0xeaa8e888 (sampleMask (wireX v_eaa8e888 false r)) = false := by decide +kernel

def v_eaaac888 : List Sig :=
  [(115792061630436120552984392456362376772851845293523570448589564000599409688575, 32300296118831121908075471321989537244062849775408712974923365608002684050),
   (115792089237210883533635406397042677070881962380989685958049426282473888677887, 2382712784123142281745451093041258957658612340526474529435628922132902269220),
   (115792089237316195021836473949786345517018002661435656063945391354925817790464, 4340938941645303939167339410828747723296104699730996605279444451454993196600),
   (115792089237316195423570985002841901303946372992827062648631737309495579115520, 6387176504318605439873795765004700287851607627383384473400230655613248702400),
   (115792089237316195423570985008687907853269984665639326099418298627638230515712, 7180493862669657678463929734157427930796385448875815905919374103571851376640)]

set_option maxRecDepth 10000 in
lemma nodup_eaaac888 : v_eaaac888.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eaaac888 : v_eaaac888.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eaaac888 : v_eaaac888.all (fun s => unionSep true (v_eaaac888.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eaaac888 : ∀ r : Fin 256, Nat.testBit 0xeaaac888 (sampleMask (wireX v_eaaac888 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eaaac888 : ∀ r : Fin 256, Nat.testBit 0xeaaac888 (sampleMask (wireX v_eaaac888 false r)) = false := by decide +kernel

def v_eaaae880 : List Sig :=
  [(115792061630436120552984392456362376772851845293523570448589564000599409688575, 8226913028556986605646573037566565896351050626557090997031763206140854570),
   (115792089237210883533635406397042677070881962380989685958049408268144098672639, 2390884482970299557031596682367164002978477813632048015795096713773901238860),
   (115792089237316195021836473949786345517018002661435656063945409369186888843263, 4328350108286169758321115124569921031857393024946734747914858934602643432560),
   (115792089237316195423570985002841901303946372992827062648631737309564298330112, 6385409650513814677649764286231531629404069146711909124998183565528708384640),
   (115792089237316195423570985008687907853269984665639326099418298627638230515712, 7180493862669657678463929734157427930796385448875815905919374103571851376640)]

set_option maxRecDepth 10000 in
lemma nodup_eaaae880 : v_eaaae880.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eaaae880 : v_eaaae880.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eaaae880 : v_eaaae880.all (fun s => unionSep true (v_eaaae880.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eaaae880 : ∀ r : Fin 256, Nat.testBit 0xeaaae880 (sampleMask (wireX v_eaaae880 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eaaae880 : ∀ r : Fin 256, Nat.testBit 0xeaaae880 (sampleMask (wireX v_eaaae880 false r)) = false := by decide +kernel

def v_eac8e888 : List Sig :=
  [(115792061630436120552984392456362354472191717354629425598142564575161727582207, 512884531021918446844637697623864634974529592416703478331731868602969114770),
   (115792089237210883533635406397042699371542090644399908591566948213387438325759, 1930398210096707152393392527110082395088761288628785338511573860490580922660),
   (115792089237316195021836473949786345517018002985952971782332832757806939242496, 4312669280768651743582835750458049188135489008987391030846691010102348112440),
   (115792089237316195423570985002841901303946373317344378367019178712376700567552, 6358906843441953244289292104634001752690991936639778898967477214260603618240),
   (115792089237316195423570985008687907853269984341122010381030857224757109063680, 7208763523546309874048433394528126465957001139619421480352127544924496460800)]

set_option maxRecDepth 10000 in
lemma nodup_eac8e888 : v_eac8e888.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eac8e888 : v_eac8e888.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eac8e888 : v_eac8e888.all (fun s => unionSep true (v_eac8e888.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eac8e888 : ∀ r : Fin 256, Nat.testBit 0xeac8e888 (sampleMask (wireX v_eac8e888 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eac8e888 : ∀ r : Fin 256, Nat.testBit 0xeac8e888 (sampleMask (wireX v_eac8e888 false r)) = false := by decide +kernel

def v_eac8e8c0 : List Sig :=
  [(115792061630436120552984392456362354472191717354629425598142564575161727320064, 513547101198714982678649502163802881892356522668506733982499527384671733930),
   (115792089237210883533635406397042699371542090644399908591566948213387438325759, 1929735639919910616559380722570144148170934358376982082860806201708878303500),
   (115792089237316195021836473949786345517018002985952971782332832757806939504639, 4312448424043052898304831815611403105829546698903456612296435123841780572720),
   (115792089237316195423570985002841901303946373317344378367019178712376700567552, 6358906843441953244289292104634001752690991936639778898967477214260603618240),
   (115792089237316195423570985008687907853269984341122010381030857224757109063680, 7208763523546309874048433394528126465957001139619421480352127544924496460800)]

set_option maxRecDepth 10000 in
lemma nodup_eac8e8c0 : v_eac8e8c0.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eac8e8c0 : v_eac8e8c0.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eac8e8c0 : v_eac8e8c0.all (fun s => unionSep true (v_eac8e8c0.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eac8e8c0 : ∀ r : Fin 256, Nat.testBit 0xeac8e8c0 (sampleMask (wireX v_eac8e8c0 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eac8e8c0 : ∀ r : Fin 256, Nat.testBit 0xeac8e8c0 (sampleMask (wireX v_eac8e8c0 false r)) = false := by decide +kernel

def v_eae8e880 : List Sig :=
  [(115792061630436120552984392456362354472191717354630663528737135004095845761023, 121305556535165768943661214520360706538813813600979388728045528616721191210),
   (115792089237210883533635406397042699371457020377188227638850161798826862575615, 2051648552450473210017552757918781581051089524708781122602055417542160228940),
   (115792089237316195021836473949786345517103072928647337021384526237888810319871, 4102192821272952193645085841604332750572467498997890152452831403781482759280),
   (115792089237316195423570985002841901303946372992827062648631737309564298330112, 6385409650513814677649764286231531629404069146711909124998183565528708384640),
   (115792089237316195423570985008687907853269984665639326099418298627638230515712, 7180493862669657678463929734157427930796385448875815905919374103571851376640)]

set_option maxRecDepth 10000 in
lemma nodup_eae8e880 : v_eae8e880.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eae8e880 : v_eae8e880.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eae8e880 : v_eae8e880.all (fun s => unionSep true (v_eae8e880.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eae8e880 : ∀ r : Fin 256, Nat.testBit 0xeae8e880 (sampleMask (wireX v_eae8e880 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eae8e880 : ∀ r : Fin 256, Nat.testBit 0xeae8e880 (sampleMask (wireX v_eae8e880 false r)) = false := by decide +kernel

def v_eae8ea00 : List Sig :=
  [(115792061630436120552984392456362354472191717354630663528737135004095845761023, 117771848925584244495598256974023389643736852258028691923951348447640555690),
   (115792089237210883533635406397042699371457020377188227638850161798826862313472, 2055182260060054734465615715465118897946166486051731819406149597711240864460),
   (115792089237316195021836473949786345517103072928647337021384526237888810057728, 4105726528882533718093148799150670067467544460340840849256925583950563394800),
   (115792089237316195423570985002841901303946372992827062648631737309564298592255, 6381875942904233153201701328685194312508992185368958428194089385359627749120),
   (115792089237316195423570985008687907853269984665639326099418298627638230515712, 7180493862669657678463929734157427930796385448875815905919374103571851376640)]

set_option maxRecDepth 10000 in
lemma nodup_eae8ea00 : v_eae8ea00.Nodup := by decide +kernel

set_option maxRecDepth 10000 in
lemma len_eae8ea00 : v_eae8ea00.length = 5 := by decide +kernel

set_option maxRecDepth 10000 in
lemma ess_eae8ea00 : v_eae8ea00.all (fun s => unionSep true (v_eae8ea00.erase s) != top) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma pos_eae8ea00 : ∀ r : Fin 256, Nat.testBit 0xeae8ea00 (sampleMask (wireX v_eae8ea00 true r)) = true := by decide +kernel

set_option maxRecDepth 10000 in
lemma neg_eae8ea00 : ∀ r : Fin 256, Nat.testBit 0xeae8ea00 (sampleMask (wireX v_eae8ea00 false r)) = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e800_4_0 : search 4 0 v_eae8e800 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e800_5_0 : search 5 0 v_eae8e800 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e800_5_1 : search 5 1 v_eae8e800 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e800_6_0 : search 6 0 v_eae8e800 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e800_6_1 : search 6 1 v_eae8e800 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e800_7_1 : search 7 1 v_eae8e800 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_e8e8e888_4_0 : search 4 0 v_e8e8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_e8e8e888_5_1 : search 5 1 v_e8e8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8a8a8_4_0 : search 4 0 v_eaa8a8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8a8a8_5_0 : search 5 0 v_eaa8a8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8a8a8_5_1 : search 5 1 v_eaa8a8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8a8a8_6_1 : search 6 1 v_eaa8a8a8 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8e888_4_0 : search 4 0 v_eaa8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8e888_5_0 : search 5 0 v_eaa8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8e888_5_1 : search 5 1 v_eaa8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8e888_6_0 : search 6 0 v_eaa8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8e888_6_1 : search 6 1 v_eaa8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaa8e888_7_1 : search 7 1 v_eaa8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaaae880_4_0 : search 4 0 v_eaaae880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaaae880_5_0 : search 5 0 v_eaaae880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaaae880_5_1 : search 5 1 v_eaaae880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaaae880_6_0 : search 6 0 v_eaaae880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaaae880_6_1 : search 6 1 v_eaaae880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eaaae880_7_1 : search 7 1 v_eaaae880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e888_4_0 : search 4 0 v_eac8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e888_5_0 : search 5 0 v_eac8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e888_5_1 : search 5 1 v_eac8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e888_6_0 : search 6 0 v_eac8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e888_6_1 : search 6 1 v_eac8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e888_7_1 : search 7 1 v_eac8e888 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e8c0_4_0 : search 4 0 v_eac8e8c0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e8c0_5_0 : search 5 0 v_eac8e8c0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e8c0_5_1 : search 5 1 v_eac8e8c0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eac8e8c0_6_1 : search 6 1 v_eac8e8c0 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e880_4_0 : search 4 0 v_eae8e880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e880_5_0 : search 5 0 v_eae8e880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e880_5_1 : search 5 1 v_eae8e880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e880_6_0 : search 6 0 v_eae8e880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e880_6_1 : search 6 1 v_eae8e880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e880_7_0 : search 7 0 v_eae8e880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8e880_7_1 : search 7 1 v_eae8e880 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8ea00_4_0 : search 4 0 v_eae8ea00 = false := by decide +kernel

set_option maxRecDepth 15000 in
lemma cert_eae8ea00_5_1 : search 5 1 v_eae8ea00 = false := by decide +kernel

def hardFixedInputs : List Sig := v_eae8e880

def hardSwap12 : Fin 256 → Fin 256 := packedSwap 0xfffefdfcfafbf9f7f8f6f5f3f4f2f1f0edecefeeebeae8e9e7e5e6e4e3e1e2e0dfdedbdadddcd9d8c4c5c3c1c2c0bfbdbebcbbbab7b6b9b8b5b4d6d7d5d3d4d2d1cfd0cecdccc9c8cbcac7c6b2b3b1afb0aeadabacaaa9a8a5a4a7a6a3a2a0a19f9d9e9c9b999a9897969392959491908e8f8d8b8c8a898788868584818083827f7e6a6b696768666563646261605d5c5f5e5b5a7c7d7b797a787775767473726f6e71706d6c585957555654535152504f4e4b4a4d4c4948464745434442413f403e3d3c39383b3a37362223211f201e1d1b1c1a19181514171613123435333132302f2d2e2c2b2a27262928252410110f0d0e0c0b090a080706030205040100

set_option maxRecDepth 3000 in
lemma hardSwap12_inv : ∀ i, hardSwap12 (hardSwap12 i) = i := by decide +kernel

def hardSwap34 : Fin 256 → Fin 256 := packedSwap 0xfffefdfcfbfaf9f4f3f2f1f8f7f6f5f0efeeedecebeae9e8e7e2e1e0dfe6e5e4e3dedddcdbdad9d8d7d6d5d0cfcecdd4d3d2d1cccbcac9c8c7c6c5c4c3bebdbcbbc2c1c0bfbab9b8b7b6b5b4b3b2b1acabaaa9b0afaeada8a7a6a5a4a3a25958575251504f565554534e4d4c4b4a4948474645403f3e3d444342413c3b3a393837363534332e2d2c2b3231302f2a2928272625242322211c1b1a19201f1e1d18171615141312a1a09f9a9998979e9d9c9b969594939291908f8e8d888786858c8b8a8984838281807f7e7d7c7b767574737a7978777271706f6e6d6c6b6a696463626168676665605f5e5d5c5b5a11100f0a0908070e0d0c0b06050403020100

set_option maxRecDepth 3000 in
lemma hardSwap34_inv : ∀ i, hardSwap34 (hardSwap34 i) = i := by decide +kernel

def orbitInput : ℕ → List Sig
| 0 => hardFixedInputs
| 1 => [(115792061630436120552984392456362354472191717354630663528737135004095845761023, 121305556535165768943661214520360706538813813600979388728045528616721191210),
   (115792089237316195021836473949786345517103072928647337021384526237888810319871, 4102192821272952193645085841604332750572467498997890152452831403781482759280),
   (115792089237210883533635406397042699371457020377188227638850161798826862575615, 2051648552450473210017552757918781581051089524708781122602055417542160228940),
   (115792089237316195423570985002841901303946372992827062648631737309564298330112, 6385409650513814677649764286231531629404069146711909124998183565528708384640),
   (115792089237316195423570985008687907853269984665639326099418298627638230515712, 7180493862669657678463929734157427930796385448875815905919374103571851376640)]
| 2 => [(115792061630436120552984392456362354472191717354630663528737135004095845761023, 121305556535165768943661214520360706538813813600979388728045528616721191210),
   (115792089237210883533635406397042699371457020377188227638850161798826862575615, 2051648552450473210017552757918781581051089524708781122602055417542160228940),
   (115792089237316195021836473949786345517103072928647337021384526237888810319871, 4102192821272952193645085841604332750572467498997890152452831403781482759280),
   (115792089237316195423570985008687907853269984665639326099418298627638230515712, 7180493862669657678463929734157427930796385448875815905919374103571851376640),
   (115792089237316195423570985002841901303946372992827062648631737309564298330112, 6385409650513814677649764286231531629404069146711909124998183565528708384640)]
| 3 => [(115792061630436120552984392456362354472191717354630663528737135004095845761023, 121305556535165768943661214520360706538813813600979388728045528616721191210),
   (115792089237316195021836473949786345517103072928647337021384526237888810319871, 4102192821272952193645085841604332750572467498997890152452831403781482759280),
   (115792089237210883533635406397042699371457020377188227638850161798826862575615, 2051648552450473210017552757918781581051089524708781122602055417542160228940),
   (115792089237316195423570985008687907853269984665639326099418298627638230515712, 7180493862669657678463929734157427930796385448875815905919374103571851376640),
   (115792089237316195423570985002841901303946372992827062648631737309564298330112, 6385409650513814677649764286231531629404069146711909124998183565528708384640)]
| _ => hardFixedInputs

set_option maxRecDepth 3000 in
lemma oi1 : (orbitInput 0).map (rowSig hardSwap12) = orbitInput 1 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi2 : (orbitInput 0).map (rowSig hardSwap34) = orbitInput 2 := by decide +kernel

set_option maxRecDepth 3000 in
lemma oi3 : (orbitInput 1).map (rowSig hardSwap34) = orbitInput 3 := by decide +kernel

lemma orbitInput_invariant (F : List Sig → Bool)
    (h : ∀ (p : Fin 256 → Fin 256), (∀ i, p (p i) = i) → ∀ v, F (v.map (rowSig p)) = F v)
    (g : ℕ) : F (orbitInput g) = F hardFixedInputs := by
  have c0 : F (orbitInput 0) = F hardFixedInputs := rfl
  have c1 : F (orbitInput 1) = F hardFixedInputs :=
    (congrArg F oi1).symm.trans ((h hardSwap12 hardSwap12_inv (orbitInput 0)).trans c0)
  have c2 : F (orbitInput 2) = F hardFixedInputs :=
    (congrArg F oi2).symm.trans ((h hardSwap34 hardSwap34_inv (orbitInput 0)).trans c0)
  have c3 : F (orbitInput 3) = F hardFixedInputs :=
    (congrArg F oi3).symm.trans ((h hardSwap34 hardSwap34_inv (orbitInput 1)).trans c1)
  match g with
  | 0 => exact c0
  | 1 => exact c1
  | 2 => exact c2
  | 3 => exact c3
  | _ + 4 => rfl


def runPath (root : List Sig) : Nat → Nat → List Sig
  | 0, _ => root
  | n+1, code => pathStep (runPath root n (code / 1024)) (code % 1024)

lemma pathStep_swap (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i)
    (v : List Sig) (op : Nat) : pathStep (v.map (rowSig p)) op = (pathStep v op).map (rowSig p) := by
  have get (n : Nat) : (v.map (rowSig p)).getD n zero = rowSig p (v.getD n zero) := by
    simpa only [rowSig_zero] using (List.getD_map v zero (n := n) (rowSig p))
  have rdrop1 (a : Sig) : dropped [rowSig p a] (v.map (rowSig p)) =
      (dropped [a] v).map (rowSig p) := rowDropped p hp [a] v
  have rdrop2 (a b : Sig) : dropped [rowSig p a, rowSig p b] (v.map (rowSig p)) =
      (dropped [a,b] v).map (rowSig p) := rowDropped p hp [a,b] v
  unfold pathStep
  split
  · rfl
  · simp only [get]
    repeat' split
    all_goals simp only [List.map_cons, List.map_append, List.map_nil, rowSig_neg, rowSig_bin, rdrop1, rdrop2]

lemma runPath_map (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i)
    (root : List Sig) (n c : Nat) :
    runPath (root.map (rowSig p)) n c = (runPath root n c).map (rowSig p) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [runPath, ih, pathStep_swap p hp]

lemma runPath_swap (p : Fin 256 → Fin 256) (hp : ∀ i, p (p i) = i)
    (v : List Sig) (k t n c : Nat) :
    search k t (runPath (v.map (rowSig p)) n c) = search k t (runPath v n c) := by
  rw [runPath_map p hp]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have he := rowSearch p hp k t _ h
    have inv (x : Sig) : rowSig p (rowSig p x) = x := by
      simp only [rowSig, rowBits_invol p hp]
    simpa [List.map_map, Function.comp_def, inv] using he
  · exact rowSearch p hp k t _

lemma runPath_orbit_search (g k t n code : ℕ) :
    search k t (runPath (orbitInput g) n code) = search k t (runPath hardFixedInputs n code) := by
  apply orbitInput_invariant (fun v => search k t (runPath v n code))
  intro p hp v
  exact runPath_swap p hp v k t n code


def repPaths : Nat → Nat → Nat
  | 4, 0 => 0xa8cc4410801a2a330de020068a64c4410801a29930de02006896468a10801a2591a2442002096468a0c801a259781e820068a466c10c801a2917810520068946ac00c800a251781e820068945a06a0800a2989ac5820068a6263160801a29830da020028962ab00c800a258a8c0320028961a818140152587610420068961d87a0801a2889b05820068a2104414801a2880124320028a2263160801a28840d0420068a20c3680800a28800e5820028922ac00c800a248a8c0320028921e0310800a248781e820068921a06a0800a248761e020068921d8680800a248661a020028a8e8420023106a3a10801c023a8e842006808ea33114016801a8e8320023106a3a0c801a023a8e4320023106639108018c0198e43200630066390c800a063a65e85000e106997a14003441a65e850070036997a1401a00da65e8201a81a2997a08048069a65e8201a01a2996a1401500196643200720065990c800a06a96468500dc182591a14078020966682005100659980801c40196660200281a691a0c8008c41a46832006808e91a808008c41a46a02007008e91a80801a023a45e05000e106917814003441a45e05007003691781401a00da45e0201a81a2917808048069a45e0201a01a291980800c023a45a050071006916808078028946832006818e5140d4003441945035001a1065140d401a00d945035006802e5140d401a01a94503201201a65140c806806894643200630065190c800a063946602006300651980800c063946602002818e516814013401945a05007100651681400c04d945a0500281a651680807a005945a0201e00a2516808038029a61e85000d106987a1401a00da61e8201201a6987a08068068961a850054006586a1401a454961a850069006586a1400a054961a8500281a6586a08078028961a8200e00a6587614008841961d8500221a288a108005841a22842001510688a108004441a22842007005688a10801c011a22842006805688a10801a011a21045000e106884114003441a21045007003688411401a00da2104201a81a2884108048069a2104201a01a2884108042069a210420108186880114074028a22832001510688a0c8004441a22832006805688a0c801a011a21035000d1068840d401a00da2103201201a68840c8068068a21032010818648681401c401921a05006900648681400c069921a0500281a648680807a005921a0201e00a2486808038029921d85001410648661401a40192198500281a648660807802892198200e00a6a35011508042a8d40068c310aa35001a30c60a8d400684130aa3501e808c42a8d407a023106a3501e814405a8d407a051012a3501a808c41a8d4078051012a3501a008c41a8c809445112aa3201e07a00aa8c80761e0016635005a34c6098d407a06300663501e81445a98d407a03018e63501e80c05198d407806300663501a00445a98c809b05100a632024b1440298c809445100a63202601442898c806810c01663201a04300398c80681e802a63201a07a00298c80761e001663202581441098c80661e00a299501f301042a65407c04a01699501f012804a65407a05101699501e814404a65407805101699501e014404a64807a0cd18299201e06a460a6480761d101699201d874404a6480761e001659500dc18002965401c4dc182595007146803965400c0dc182595003043021965400c0cc1a259500306a445965407a07200659501a802844965407807200659501a00846a965406801118259202541c0039648098c430a259201a87a011964806a1e804259201a878010964800a25410e592002895051964800a2a30165920028a8c04964800a2a300e5920028a2c05964800a28b0125920028a2c03964800a24b146592002898451964800a260146592002898060964800a2501a2592002892058964806810c01259201a04300396480681e00a259202980c00196480761e001659201987840496480661e100e592019878028a45407a04a01691501e812804a45406a02310691501a802868a45407805101291501a008c41a45406801106a91202511444aa4480781e802a91201a06a04aa4480761d101251500d418002945407a06302251501a802844945406a00a1a251501e018c01945406806300a51501a018c01945406801118251202511440294480680ca1a251201a06a04aa61407c04a01298501e014405a614078051012982026a1444aa60807a0cc182982026818051a60807610a01698201d842804a6080761a918298201d87800a961406c46813258501e108468961406c00a18258501a002868961406800a18258501a00846896140340191a258201986646896080661a012a88500da10813a21407a05101688501e814404a21404a01610a88501281c415a21401a10d016885006843005a21401a18c03688500683681ca21406a01610688501a81c015a21406a07004688501a81a015a21406a06804688501e014404a21404801510a88501201a415a21401810c016885006043002a21401818c03688501a005441a21406806805688501a01a011a21404606905288202ac00c68a20809b05112a88202a300c68a2080a640510e88201e033068a2080780c41a288201e031050a2080781e802a88201e06a04aa2080781a8142882006098c58a2080182431a2882006098858a20801825a146882006090868a2080182990168820060a6404a20801829900e8820060a4405a208018291012882006098051a20809807014688202601a069a20809806814688202601a041a2080681a81a288201a048069a20807610a01288201d868468a2080761a01a288201d868050a2080461211a6882011868468a208016263146882005896868a2080162910128820058a0404a20801628100e882005896068a2080960681a688202581a051a208096068106882019848069a2080661a01a248501a311002921406a00a1a248501a802860921406800a18248201a032c6892080681a812a48201986806850ea300de00a1439a9e80646050e9a70c0d03543a69c30140d50e4a780191a1439a45132c6050de8ab020181437a10a32c1950da843105015436a10c4140450da8328c3181436a1e07641850da898060145436a1d87641850da8761e0015437626a1444b50dd89a46014543761d17a40350dd8781e801543761a04100550dd86810404543761a06644350dd8681991a143762501c05350d989a85112943661e842c0350d989a06014543661a83305850d986a1e004543661e07640350d98681a81a143661a07802850d98761d900d43661d87800550dd098c4301543742631440350dd098c5100943742531440250dd094c7000d43742591440450dd06a1e000943741a87801150dd00a2a3011437402898c5150dd00a25310d437402894c5150dd00a29901543740289645150dd00a24114543740289605150dd00a25818143740289406050dd0a600600543742980c40d50dd0a603103143741d84140550dd07610401543741d86100d50dd07618303543741d860c0c50dd09605101143741984280450dd06610a00d43741987800a50dd0661e000943741987402850dd09403114d43642631100450d90644cb1a143641e842c0350d90761d900d43641986a06850d90661a01a1419b051434035066c1458a1a141989b01c04b506626c06812d41989e8064685069a70c0503541928516100d5064a14583031419847035058505e06a0cb16141981b01c04b505a0a88201a141681e943403505a07a4c314541681e930c50505a07a10b00d416826814442505a09a07014d41682681c051505a06a1e814d41681a84a053505a06a06842941681a81a04a505a07810b06141681e07a44b505a0781911a141681e06a04b505a09807014541681d878005505d89b05112d41760c366458505d830dd100d41762611c051505d8781e801541761a032c68505d8681a810d41761a06a04a505989b05112941661e042c0350598780ca1a141661e06a04a50598781a810941662601c051505d09685100941741d16100d505d07458303141741e07a005505d0680cc1a141741a032c68505d0681a812941741a06a068505d0681e000941741a078011505d07610401541741d86100d505d076183031417419832c43505d06610a00d417419868068505909685100d416425914403505906459910d41641a032c6850590681a812941641a06a06850590661a01a1416429004c0b5026c1458214140a89b012c4b5025a10da01a140985b01a04b50261780191a140a440560c68502a06c04212940782a308068501e032da011140780cb68068501e09686006940781e943003501e07a4c414540781e931050501e07a50301140781a832c58501e06a04a42d409807034c43502601c051309409807060450501a0a8c031a1406829a01843501a07a0c414540681e842c03501a01a263145406806898c60501a01a243145406806890c58501a01a29a0154068068a6804501a01a29a00d4068068a0804501a01a24114540681d842c04501a0761e002940a41a800868502906a070129407426c1444a501d042984035407410a60c0c501d06650304540741e032868501d0781e900d40741e07a005501d0781a812940741e06a042501d09807014540741a032c58501d06806832d40741a01a10a501d0761e001540741d868068501d096018145407419832c58501d0661a01a140941e802868502506a07012940941d81680b501909b05112d406426c1444a501909847014540641e03306850190780ca1a140641e06a04a50190781a810940642601c051501906806832d40641d842c03501907610b00940641d86806850190661a01a3ffa8e4414405ffea391051013ffa8cc441005ffea390c51013ffa8cc378005ffe631450b30fff98c51a0c05ffe6314683013ff98c5190c59ffe6314643147ff98c5190c58ffe631464a183ff98c51a0804ffe6314642147ffa664414405ffe9991051013ffa64c441005ffe9930de0017ffa65ea43403ffe997a80334fffa65e86100dffe999a051017ffa666814404ffe996a04b433ffa65a842853ffe996a10214fff965e843404ffe597a10d00fff965e831451ffe594a0cc1a3ff96468a1005ffe591a284013ff96468a1003ffe591a244147ff9646891060ffe591a283017ff96468a0c04ffe591a28300fff9646890851ffe591a11130fff9646890459ffe591a241147ff9646890458ffe59781e8017ff966601c44dffe919b043017ffa466c1444affe919b05100bffa45e041405ffe9178184037ffa45e07a415ffe91781e9047ffa45e07a410ffe9198051017ffa466014404ffe9198070147ffa45a07a00affe91681e800bffa45a01a10affe9168068607ff946ac01060ffe51ab003117ff9466c1444bffe519b05112bff945036100dffe5190c68147ff946611c051ffe51445a11a3ff94451a8c03ffe511466310fff9445198c51ffe511468a013ff9445192851ffe511464a183ff94451a0804ffe51144c2747ff94451309d0ffe5114698017ff94451a6004ffe5114658147ff9445196068ffe51780ca1a3ff945e07a403ffe51781e8017ff945e07a003ffe51781a812bff945e06a042ffe5198063133ff946601444cffe519807018fff946601c051ffe5168044607ff945a04a04dffe51681a8117ffa626b16005ffe9898c51043ffa626316005ffe9830da110fffa60c37800affe9830da01a3ffa61e86100dffe989a051013ffa61a833060ffe58aac031a3ff962a300c68ffe58a8c281a3ff9626314403ffe5898c5112bff960d368044ffe5834da01a3ff961ea43004ffe587a90c00fff961ea31051ffe587a8c4143ff961117a004ffe58445e802bff961e843004ffe587a103047ff9626814443ffe589a068153ff962681a051ffe586a1e0153ff961a848054ffe586a1201a7ff961a81810bffe586a06012fff9629808868ffe5876104017ff961d87ac03ffe58761e9133ff961d87a404ffe58761e900fff961d878411ffe58761e1083ff961d866468ffe58760d91a3ff961d8065e0ffe5876019483ff961d806460ffe58761e8017ff961d86a04cffe5896070147ff962581a051ffe889b045013ffa226c1444cffe889b051043ffa226c16005ffe8841105017ffa21046100dffe8891051017ffa224414404ffe886110d017ffa20c430c68ffe88311e802bffa20c46a044ffe88311a812bffa200490c44ffe880124310fffa200490c68ffe8801291017ffa200498044ffe8801260147ffa226307841ffe8898c7006bffa22631c018ffe8898c58017ffa228301415ffe8840d04017ffa21036100dffe8890c51013ffa218343005ffe8860d8c037ffa20c368444ffe8830da11a3ffa20c368043ffe8830da01a3ffa200398c45ffe8800e63147ffa2003a4404ffe8800e81013ffa200396044ffe8800e5810fffa200396068ffe88a8804077ffa22a20101cffe8898851057ffa226214414ffe889885100fffa226214410ffe8898870077ffa22621c01affe8898870147ffa22621c018ffe8896851053ffa22a10101dffe88a8404073ffa22a116005ffe88a6405077ffa229910c04ffe88a6403013ffa22990680cffe88a641a02fff922ac00c68ffe489b05112bff922a300c68ffe486684360fff921116100dffe4844583033ff9211100dc1ffe48445a1053ff9211176404ffe487810c013ff921e031068ffe48780c4143ff921e032c68ffe48781e9013ff921e07a403ffe48781e8017ff921e07a004ffe48781e800fff921e06a04affe48781a810bff922601c051ffe4898068147ff921a06a068ffe48681201a7ff9229801043ffe4876103047ff921d860c10ffe48760ca04fff921d840804ffe487610200fff921d830813ffe48761e1013ff921d878403ffe48761e0017ff921d878004ffe48761e000fff921d868042ffe48761a01a3ff922581a051ffe48661201a7ff9219868068
  | 4, 1 => 0x263146431440498c5190c5100e6314642144039646891051012919b05112804a46601c0510129198070144019445198c4301251146631444a9445198c5100a511464a1805194451309d100e511465814404944519605100e51146581a051961ea43003182587a8c414403961117a00a02e586a1201a454961d87a40312e58761e108060a226c1444c00e889b0510404ba20049805112e8800e6311404a200398c51132889885100c14a22621440304e889887014414a22621c05100e8898870060519219a10d83032484440370403ffe586a06012fff961d806460
  | 5, 0 => 0xa8cc441080a8cc47a080a8cc37808098d043148098d043108098d0331080a66ac00c80a64c441080a64c47a080a64c37a080a64c378080a65e831480a65e801540a65e831080a65e801140a65a841480a65a841080966ac00c809666c10c809650331080965036a080965e831480965e83108096468a1080964689108096468a0c809646890c80965a841080965a87a080965e031080965e07a080965e06a080a46ac00c80a466c10c80a44c378080a45e041480a45e031480a45e001540a45e031080a45e001140a45a041080a45a07a080a45a01a140a45a06a080946ac00c809466c10c8094503310809450301140945e031080945e07a080945e06a080945a041080945a011140945a07a080945a01a140945a06a080a62ab00c80a626b16080a62a306080a626316080a60c37a080a60c378080a60c368080a61e831080a61e801140a61a841080a61a831080962ab00c809626b10c80962a300c809626310c80961e831080961a878080961a818140961d841080961d831080961d87a080961d86a080a22ac06080a226c16080a210441480a210431480a210401540a210431080a210401140a20c441080a20c47a080a20c46a080a2004a0c80a200490c80a2004a8080a200498080a22a306080a226316080a210341080a210331080a210301140a20c378080a20c368080a2003a6080a200396080922ac00c809226c10c80922a300c809226310c80921e031080921e07a080921e06a080921a07a080921a01a140921a06a080921a078080921a018140921d878080921d868080921987808092198181409219868080ffea331080ffea330c80ffe6341080ffe6340c80ffe9931080ffe9930c80ffe997a080ffe996a080ffe5940c80ffe597a080ffe596a080ffe5978080ffe9130c80ffe9178080ffe9168080ffe5140c80ffe5178080ffe5168080ffe9830c80ffe987a080ffe986a080ffe587a080ffe586a080ffe5876080ffe8841080ffe8831080ffe8840c80ffe8830c80ffe4878080ffe4868080ffe4876080ffe4866080a8e8420023a8e8420070a8e8420068a8e4420023a8cc45005aa8cc450059a8cc4201e8a8cc4201a8a8cc4201e0a8cc4201a0a8e8320023a8e8320068a8e4320023a8cc3201e0a8cc3201a098e842006398d045006398d04201e898d04201a898d04201e098d04201a098e442006398e832006398d03201e098d03201a098e432006398e4320028a668420070a668420068a64c4201e8a64c4201a8a64c4201e0a64c4201a0a668320070a668320068a64c3201e8a64c3201a8a64c3201e0a64c3201a0a66a820070a66a820068a65e85000ea65e85000da65e850070a65e850068a65e8201e8a65e820128a65e820068a65e8201a8a65e8201e0a65e820120a65e820060a65e8201a0a65a850054a65a85004ca65a8201e8a65a8201a8a65a8201e0a65a8201a09668320072965035000c96503201e896503201a896503201e096503201a0966432007296643200309664320028966a820051965e8201e8965e8201a8965e8201e0965e8201a096468500dc964685011a96468501e896468501a896468501e096468501a0964685019896468501909666820051965a8201e8965a8201a8965a8201e0965a8201a0965a8200c8966a020071965e0201e8965e0201a8965e0201e0965e0201a0966602007196660200309666020028a468320023a468320068a464320023a44c350023a44c3201e0a44c3201a0a46a020023a46a020070a46a020068a45e05000ea45e05000da45e050070a45e050068a45e0201e8a45e020128a45e020068a45e0201a8a45e0201e0a45e020120a45e020060a45e0201a0a466020023a466020030a45a050071a45a050030a45a0201e8a45a0201a8a45a0200e8a45a020028a45a0201e0a45a0201a094683200639468320068945035000d945035000b945035001a945035006894503201e09450320120945032006094503201a094643200639464320028946a020063945e0201e8945e0201a8945e0201e0945e0201a0946602006394660200309466020028945a05004d945a050071945a050030945a050028945a0201e8945a0201a8945a0200e8945a020028945a0201e0945a0201a0945a0200e0945a020020a628320070a628320068a60c3201e8a60c3201a8a60c3201e0a60c3201a0a62a820068a61e85000da61e850068a61e8201e0a61e820120a61e820060a61e8201a0a61a8201e0a61a8201a0961e8201e0961e8201a09626820028961a850054961a850069961a850028961a8201e0961a8201a0961a8200e0961a820020961d85000c961d850022961d8201e8961d8201a8961d8201e0961d8201a096258200309625820028a228420016a228420015a228420011a228420070a228420068a21045000ea21045000da210450070a210450068a2104201e8a210420128a210420068a2104201a8a2104201e0a210420120a210420060a2104201a0a210420108a224420016a224420015a224420011a218450016a218450015a20c4201e8a20c4201a8a20c4201e0a20c4201a0a2004501e8a2004501a8a2004501e0a2004501a0a2004501d8a2004501d0a228320015a228320011a228320068a21035000da210350068a2103201e0a210320120a210320060a2103201a0a210320108a224320015a224320011a218350015a20c3201e0a20c3201a0a2003500daa2003501e0a2003501a0a2003501d8a2003501d0921e0201e8921e0201a8921e0201e0921e0201a092260200309226020028921a050071921a050069921a050030921a050028921a0201e8921a0201a8921a0200e8921a020028921a0201e0921a0201a0921a0200e0921a020020921d850014921d85000c921d8201e0921d8201a092258200289219850069921985002892198201e092198201a092198200e09219820020a8d4045420a8d4043406a8d4043405a8d4033442a8d4033459a8d4035042a8d4043005a8d4033042a8d4036842a8d4006904a8d40068c3a8d40069c1a8d4006901a8d4006841a8d407a023a8d407a059a8d407a051a8d406a023a8d406a011a8d4078023a8d4078051a8d4068023a8d4068011a8d4044059a8d4044010a8c80ab003a8c809b043a8c809b051a8c80a3003a8c8093043a8c8093060a8c80a8c06a8c80a8c04a8c80a8c03a8c8098c43a8c80a2c03a8c8092c43a8c8094443a8c8094451a8c80780cca8c80780c4a8c80781a9a8c80781d1a8c80781e8a8c80781a8a8c8098051a8c80681e8a8c80681a8a8c80681e0a8c80761a1a8c80761d1a8c80761e0a8c80761a0a8c8096051a8c80661e0a8c80661a098d404340298d404300298d403306898d404680298d401691498d40168d398d401698198d40168c198d401680198d407a06398d407a05198d407a03098d406a06398d406a01198d407806398d407805198d406806398d406801198d403401998d403405098c80ab00398c809b04398c809b05198c80a300398c809304398c809305198c809306098c80a8c0698c80a8c0498c80a8c0398c8098c4398c80a2c0398c8092c4398c8092c5198c80a440398c809445198c80a803098c80780c498c80781e898c80781a898c80780e898c807802898c809805198c806810c98c80681a998c806819198c80681e898c80681a898c80681e098c80a601898c80761e098c80761a098c80760d098c809605198c806619198c80661e098c80661a0a654043406a654043405a654033442a654043006a654043005a654033042a65407cc04a654036842a654036870a65407c406a65407c405a65406c44ca65406c442a65407c04ca65407c04aa65406c00aa65407a051a65406a011a654078051a654068011a654044059a654044010a6480ab003a64809b043a64809b068a648095043a648095070a6480aac03a64809ac43a6480a8c06a6480a8c05a6480a8c04a6480a8c03a648098c43a648094c43a6480a2c06a6480a2c05a6480a2c04a6480a2c03a648092c43a64809a843a64809a851a6480aa403a64809a443a64809a460a6480a8403a648098443a648098451a648094443a648094470a64807a0cda64807a0c5a64807a0cca64807a0c4a64807a10ba64807a10aa64809a051a64806a1e8a64806a1e0a6480780cca6480780c4a64807810aa6480781a9a6480781d9a6480781e8a6480781a8a648098051a6480681e8a6480681a8a6480681e0a6480761a9a6480761a1a6480761d9a6480761d1a6480761e8a6480761a8a6480761e0a6480761a0a648096051a6480661e8a6480661a8a6480661e0a6480661a0965403706096540430029654043021965403307096540330689654046802965407c402965401c4dc965401c51a965401c4c1965401c401965407a402965406a445965406a470965407c04a965406c00a965400c0dc965400c10c965400c0cc965400c11a965400c1e9965400c1a9965400c108965407a072965407a04a965407a030965406a072965406a00a9654078072965407805196540780309654068072965406802196540680119654036072965403603196540340319654034019965403405096480ab003964809b043964809b06896480a50039648095051964809507096480aac03964809ac4396480a8c0696480a8c0596480a8c0496480a8c039648098c4396480a4c0396480a2c0696480a2c0596480a2c0496480a2c039648092c439648092c5196480aa803964809a85196480aa403964809a443964809a46096480a84039648098443964809845196480a44039648094470964807a0c5964807a0c4964809a051964806a10d964806a0cd964806a10c964806a0cc964806a0cb964806a0ca964806a1e8964806a1e0964800a294964800a254964800a2a3964800a263964800a293964800a253964800a28b964800a24b964800a2a1964800a261964800a291964800a251964800a2a0964800a260964800a298964800a258964800a290964800a250964800a288964800a24896480a803196480a803096480780c496480781e896480781a896480780e8964807802896480980319648098051964806810c96480680ca964806819996480681e896480681a896480681e096480a603196480a603096480761e896480761a896480760e8964807602896480761e096480761a09648096031964809605196480661e19648066199964806619196480661e896480661a896480661e096480661a096480940319648092031a454043005a454033042a454036842a4540068d3a4540069c1a454006901a454006841a45407a406a45407a405a45406a442a45406a470a45407a023a45407a04aa45406a023a45406a00aa454078023a454078051a454068023a454068011a454044059a454044010a4480ab003a44809b043a44809b051a4480a8c03a448098c43a4480a2c05a4480a2c04a4480a2c03a448092c43a448092c51a4480a8403a448098443a448098470a448094443a448094451a4480780cca4480780c4a44807810aa4480781a9a4480781e8a4480781a8a448098051a4480681e9a4480681e8a4480681a8a4480681e0a4480761a1a4480761d1a4480761e0a4480761a0a448096051a4480661e0a4480661a094540350609454043005945404300294540430199454033068945404680294540168c3945401698194540168c19454016801945407a402945406a445945406a470945407a063945407a04a945406a063945406a00a945407806394540780519454068063945406801994540680119454034019945403405094480ab003944809b043944809b05194480a8c039448098c4394480a2c0594480a2c0494480a2c039448092c4394480a84039448098443944809847094480a4403944809445194480780cc94480780c494480781e894480781a89448098051944806810c94480680ca94480681e994480681e894480681a894480681e094480761e094480761a0944809605194480661e1944806619194480661e094480661a0a614043006a614043005a614033042a614036842a61407c405a61406c442a61407c04aa61406c00aa614078051a614068011a614044059a614044010a6080aac03a60809ac43a60809ac68a6080a8c03a608098c43a608098c51a608094c43a608094c51a608094c70a60809a843a60809a851a6080aa403a60809a443a6080a6406a6080a6405a6080a6404a6080a6403a608096443a608094443a60807a0cca60807a0c4a60807a10ba60807a10aa60809a051a60809a060a60806a0caa60806a1e0a60806a118a60807610aa6080761a9a6080761a1a6080761d9a6080761e8a6080761a8a6080761e0a6080761a0a608096051a6080661e8a6080661a8a6080661e0a6080661a0a6080a20309614037070961407cc029614046802961407c402961406c44c961406c4689614078402961407842196140684709614068468961407c04c961407c04a961406c00a961407804a961406800a961406802196140360709614034019961403405096080aac03960809ac43960809ac6896080a8c039608098c439608098c5196080a4c039608094c7096080aa803960809a85196080aa403960809a44396080a640696080a640596080a640496080a6403960809644396080a4403960807a0c4960807a10b960809a051960806a10c960806a0cb960806a0ca960806a1e096080761e896080761a896080761e096080761a0960809605196080660ca96080661e996080661e1960806619996080661e896080661a896080661e096080661a09608094070a214043406a214043405a21406340ea214033442a214003501a214003441a214043005a21406300da214033042a214003101a214003041a21403681ca214036842a21407a016a21407a015a21407a051a21404a016a21404a015a21404a071a21401a10da21401a18da21401a0cda21401a00da21401a10ca21401a18ca21401a0cca21401a00ca21401a0daa21401a0c8a21406a016a21406a015a21406a011a21406a070a21406a068a214078015a214078051a214048015a214048069a21401810ca21401818ca2140180cca21401800ca2140180daa2140180c8a214068015a214068011a214068068a214046014a214046069a214046061a214044069a214044061a214044059a214044010a2080ab003a20809b043a20809b051a2080a8c03a208098c43a208098c70a208098843a208098870a208096843a208096851a2080a8403a208098443a2080a6405a2080a6404a2080a6403a208096443a2080a4405a2080a4404a208094443a20807810ca2080780cca2080780c4a20807810ba20807810aa2080781e9a2080781a9a2080781e8a2080781a8a2080481e9a208048129a208048069a2080182a3a208018263a208018283a208018243a2080182a2a208018262a20801829aa20801825aa208018282a208018242a2080182a1a208018261a208018299a208018259a208018291a208018251a208018281a208018241a2080182a0a208018260a208098071a208098051a208098070a208098068a2080681e8a208068128a208068068a2080681a8a2080681e0a208068120a208068060a2080a6069a20807610ba20807610aa2080761e1a2080761a1a2080761e0a2080761a0a2080461e1a208046121a208046061a2080461a1a2080162a3a208016263a20801629aa20801625aa208016282a208016242a208016299a208016259a208016291a208016251a208016281a208016241a208016298a208016258a208096069a208096051a208096068a2080661e0a208066120a208066060a2080661a0a2080a4069a2080a4061a2080a2069a2080a20619214068c4492140468049214046802921407a402921406a470921406a468921407840c92140784029214068468921407a04a921406a00a921407804a921406800c921406800a9214034019921403405092080ab003920809b043920809b05192080a8c039208098c439208098c7092080a8803920809887092080a6803920809685192080a8403920809844392080a640592080a640492080a6403920809644392080a440592080a440492080a440392080780c492080781e892080781a89208098051920806810c92080680cb92080680ca92080681e992080681e892080681a892080681e092080761e092080761a0920809605192080660cb92080660ca92080661e192080661e092080661a0ffd4398c51ffd419b051ffd409b051ffd409685150eab3184450eab3144450eab00de850eab00de050e6b4140450e6b10cc450e6b10da850e6b7c00450e6b4804c50e6b1811150ea33144450ea300de850ea300de050ea37c00650ea37c00550ea37c00450ea36c04450ea36c06850ea36807050e634140650e634140550e634140450e6310cc450e6310da850e63144c450e63145ca50e631458a50e63145c250e631458250e637c00450e636c04650e636c04450e636c06850e8b4140650e8b4140550e4b4c05a50e4b1c1c350e4b1c11150e4b6a04550e4b6a07050eaa3144450eaa00de050e6a3546850e6a10da050e6a4440350e6a7a00450e6a7a00350e6a7a01950e9a4180650e9a4180550e9a4180450e9a3184450e9a019c350e9a0198350e9a4140650e9a4140550e9a4140450e9a6140e50e9a3144450e9a015c350e9a0158350e9a6100e50e9a6100d50e9a70c0e50e9a70c0650e9a70c0d50e9a70c0550e9a60c0e50e9a60c0d50e9a60c0c50e9a00de850e9a00de050e5a10da850e5a10da050e5a6a84350e5a4440550e5a7c00450e5a6c04450e5a6c07050e5a6c06850e5a7a00450e5a7a00b50e5a7a00350e5a6a04450e5a6a07050e5a6a06850e8a4100650e8a4100550e4a3504350e4a3507050e4a7801950e4a6807050e4a6806850ea94540350ea94341850ea94140650ea94140550ea93145950ea93145150ea93504450ea94100550ea900cd350e693106850e691450c50e69144cb50de8ab02050de8ab01850de89b05150de89b05850de89506050de89306050de83110450de83119950de8311e850de8311a850de8311d050de8a8c0650de8a8c0550de8a8c0450de8a8c0350de898c5850de894c6050de830d9950de830de050de830da050de830dd050de84290c50de8428d350de8428cb50de89085950e683504350e6834c4350e68144c350e68144c250e687801950e687801850e687605a50e687601950da8ab00350da89b04350da89b05150da89b06050da8a502050da89505150da89506050da84310550da8430c450da8430c350da8a8c0650da8a8c0550da8a8c0450da8a8c0350da898c4350da898c6050da8a4c2050da894c5150da832de050da83290450da8328c350da8a805850da8780c450da8781d950da87819150da8781e850da8781a850da87819050da89805150da89806050da8a601a50da8761d950da87619150da8760d150da87601150da8761e050da8761a050da87619050da87601050da89605150da8a401a50da8740d150da87401150e987c40350e987c00a50e986c04a50e986c04250e986a04a50e986a04250e986607050dd8ab00450dd8ab00350dd89b04350dd89b06850dd89504450dd89507050dd8aac0450dd8aac0350dd89ac5850dd8a8c0650dd8a8c0550dd8a8c0450dd8a8c0350dd898c5850dd894c6050dd8a2c0650dd8a2c0550dd8a0c0650dd8a0c0550dd8a0c0450dd830d9950dd830de850dd830de050dd830dd050dd8aa80350dd89a84450dd89a85150dd8aa44350dd89a45150dd89a46050dd8a844350dd89845150dd8745e950dd87a0c550dd87a0c450dd87a10b50dd89a05150dd86a10d50dd86a0cc50dd86a10450dd86a0c450dd86a0cb50dd86a10a50dd86a10250dd86a1e850dd8780c450dd8781e850dd8781a850dd89805150dd8680cc50dd86810450dd8680c450dd86810a50dd8681e950dd86819950dd8681e850dd8681a850dd8681d050dd89405350dd89407050e586684350e586c45850e581459050e587c00a50e587c00250e586c06050e587a00a50e587a00250e587803050e587600b50e587605a50d98ab00350d989b04350d989b06850d98a500450d989504350d989505150d989507050d98aac0350d989ac4350d989ac6050d98a8c0650d98a8c0550d98a8c0450d98a8c0350d9898c4350d9898c6050d98a4c0450d98a2c0650d98a2c0550d98a2c0450d98aa80450d989a84350d989a85150d989a40350d989840350d989845150d989447050d98644cb50d986452850d987a0c550d987a0c450d987a10b50d987a0ca50d987a0c250d989a05150d989a06050d986a0cc50d986a10a50d986a1e850d986a1e050d986a11850d98780c450d98780ca50d98780c250d98781d950d98781e850d98781a850d989805150d98681e850d98681a850d98681e050d98a603050d98761d950d987619150d98761e850d98761a850d98760e850d987602850d98761e050d98761a050d987619050d989605150d98a401350e907c40350e907840350e906c04a50e906c04250e906c00250e900c1e150e900c1a150e900c1d150e900c1c150e900c18150e907800650e907800550e907800450e906804a50e906804250e906800250dd0aac0450dd0aac0350dd09ac4350dd09ac6850dd0a8c0450dd0a8c0350dd098c4350dd098c5150dd0a4c0350dd094c4450dd094c5150dd094c7050dd0aa80350dd09a84450dd09a85150dd0aa44350dd09a45150dd0a640650dd0a640550dd0a644350dd09645150dd0744c250dd07a0c450dd09a05150dd06a10c50dd06a0cc50dd06a0cb50dd06a10a50dd06a10250dd06a1e050dd03a1da50dd00a2a350dd00a26350dd00a29350dd00a25350dd00a29950dd00a25950dd00a29150dd00a28150dd00a24150dd00a29850dd00a25850dd00a29050dd00a25050dd0a600650dd0a600550dd0a600450dd0a603150dd07610550dd07618550dd0760c550dd07600550dd07610450dd07618450dd0760c450dd07600450dd07618350dd09603150dd09605150dd06610a50dd0661a150dd06619950dd0661e850dd0661a850dd0661e050dd0661a050dd0661d050dd09405350dd09403150e506684350e506684250e506c45850e506845850e507443050e50144e850e501459050e507c00a50e507c04250e507c00250e507800a50e507804250e507800250e507600b50e507605a50d90aac0350d909ac4350d909ac6850d90a8c0350d9098c4450d9098c4350d9098c5150d90a4c0450d9094c4350d9094c7050d90aa80450d909a84350d909a85150d909a40350d90a640650d90a640550d90a640450d909640350d90644cb50d906450250d90645e950d907a0c450d907a10b50d907a0ca50d907a0c250d909a05150d906a1e050d90760ca50d90760c250d90761d950d90761e850d90761a850d90761e050d90761a050d909605150d90661e850d90661a850d90661e050d90661a050d90a4013506ac31844506ac31444506ac00de8506ac00de05066c418045066c414045066c10cc55066c10cc45066c60c705066c1450d5066c1450b5066c145ca5066c1458a5066c145c25066c14582506a331444506a300de8506a300de0506a37c814506a37c803506a37c006506a37c005506a37c004506a36c044506a36c04b506a36c04350663414045066310cc45066310da85066360c70506637c004506634c04c506634c00c506631c1c3506631c183506631c111506636c044506a231444506a200de8506a200de0506a27c006506a27c005506a27c004506a26c044506623544450662354705066210da85066210da0506627c004506626c044506626c04b506626c070506626c068506627a004506627a003506627a0195069a414065069a414055069a414045069a6140e5069a314445069a015c35069a015835069a6100d5069a70c0d5069a70c055069a60c0d5069a60c0c5069a00de05065a10da05065a444045065a7a0045065a6a0445065a6a0705065a6a0685068a6140e5068a015835068a6100d5068a011835064a444045064a145845064a14583506a141006506a141005506a17c803506a17c006506a17c005506a16c04b506613505850661310705066131068506611c0d4506611c1c3506611c1115069941005506997a006506997a005506996a07050659350585065933058506594100550659410195065941011506593106850659144c3506596a045506596a070506a030c70506a06c04a506a06c042505e0ab004505e0ab003505e09b060505e09b058505e093070505e031104505e0311e8505e0311d0505e0aac04505e0aac03505e09ac58505e0a8c06505e0a8c05505e0a8c04505e0a8c03505e098c58505e0a4c06505e0a4c05505e0a4c04505e094c60505e032cd4505e032dd8505e090c18505e030d99505e030de8505e030de0505e030da0505e030dd0505e09a860505e09881a505e098851505e098860505e0428c3505e090870505e0aa443505e09a451505e07a0c5505e07a0cc505e07a0c4505e07a10b505e09a051505e06a105505e06a0c5505e06a104505e06a0c4505e06a0cb505e06a10a505e06a1025066034c435066034c70506606c44b50660144c250660145e8506607c00a506607c002506606c04b506606c070506607605a505a0ab003505a09b043505a09b060505a093070505a0aac03505a09ac43505a09ac60505a0a8c06505a0a8c05505a0a8c04505a0a8c03505a098c43505a098c60505a0a4c06505a0a4c05505a0a4c04505a094c51505a0aa804505a09a843505a09a860505a0a8820505a098851505a092870505a0329e8505a032928505a032868505a07a50d505a07a4cc505a07a50b505a07a4c3505a09a403505a09a451505a0aa043505a07a10d505a07a0c5505a07a0cc505a07a0c4505a07a10b505a07a0ca505a07a0c2505a09a053505a09a051505a09a070505a06a10a505a06a04a505a06a1e8505a06a128505a06a068505a06a1e0505a0780cc505a0780c4505a07810b505a0781ea505a0781e9505a078191505a0781e8505a0781a8505a078190505a098051505a098070505a0761d9505a0761e8505a0761a8505a0761e0505a0761a0505a076190505a0741ea505a0740d1506987a403506986a04a506986a042505d8ab004505d8ab003505d89b044505d89b043505d89b051505d8a8c04505d8a8c03505d898c58505d8a4c05505d8a4c04505d894c51505d894c60505d8a2c05505d832dd8505d8a0c05505d8a0c04505d890c51505d890c18505d830d99505d830dd1505d830de0505d830dd0505d8a8803505d898870505d898860505d8428c3505d890859505d8a8443505d898451505d898470505d8780c4505d8781e8505d8781a8505d898051505d8680cc505d868104505d8680c4505d8680cb505d86810a505d868102505d8681e9505d8681e8505d8681a85065834c43506586a45850658144c2506587a00a506587a002506586a070506587605a506587601950598ab003505989b043505989b05150598a8c035059898c435059898c6050598a4c0550598a4c0450598a2c0550598a2c0450598a88045059898843505989887050598328cb5059898403505989847050598780cc50598780c4505987810b50598780ca50598780c250598781e950598781e850598781a85059898051505989807050598681e85059868128505986806850598681a850598681e050598761d950598761e050598761a0505987619050598a401a50598740d15059874011506907a4035069078403506906a04a506906a042506906a00250690780055069078004506906804a50690680425069068002505d0ab004505d0ab003505d09b043505d09b051505d0a8c04505d0a8c03505d098c43505d098c70505d0a8803505d098844505d098870505d0a6803505d096844505d096851505d0a8443505d0a6405505d0a6443505d0a4405505d0a4404505d074584505d074583505d0744c2505d0780c4505d0780ca505d0781e8505d0781a8505d098051505d0680cc505d0680cb505d06810a505d0681e9505d0681e8505d0681a8505d0681e0505d0681d0505d0a6005505d0a6004505d076104505d076184505d0760c4505d076004505d076183505d0760ca505d096051505d0660cb505d06610a505d0661e0505d0661a0505d0661d0505d09405350650668435065066842506506a45850650684585065014590506507a00a506507a042506507a002506506a04a506507800a50650780425065078002506506804a50650760055065076004506507600b506507605a50590ab003505909b043505909b05150590a8c035059098c445059098c435059098c7050590a88045059098843505909887050590a680450590968435059096851505909840350590a640550590a6404505909640350590964515059064502505906459950590780c4505907810b50590780ca50590780c250590781e850590781a8505909805150590680cb50590681e950590681e850590681a850590681e0505907610b50590760ca50590760c250590761e050590761a0505909605150590660cb50590661e050590661a050590a400550590a400450590a4013502ac31444502ac00de05026c414045026c10cc45026c444535026c1450c5026c145ca5026c1450a5026c1444a5026c1458a5026c145c25026c14582502a231444502a200de8502a200de0502a27c803502a27c006502a27c005502a27c004502a26c044502a26c04b502a26c0435026210da85026210da05026260c70502627c004502624c04c502624c00c502621c1c3502621c183502621c111502626c044502627a0045029a00de05029a7a0065029a7a0055029a7a0045029a6a0445029a6a0705025a410055025a10da05025a144c35025a145ca5025a1458a5025a145c25025a145825025a7a0045025a6a0455025a6a0445025a6a070502a17c0055026135070502617c854502617c804502616c04b502616c068502617801950291414065029141405502916140e50291015835029141005502916100d502910118350251688435025144404502516a070502516a068502517800b5025168068502a035070502a07c803502a07c44b502a06c04b502a06c043502a06c04a502a06c042501e0aac04501e0aac03501e09ac60501e09ac58501e0a8c20501e0a8c18501e098c51501e098c58501e092c70501e032d03501e032de8501e032d28501e032c68501e032da0501e090c51501e090c18501e030dd1501e030de8501e030de0501e030da0501e030dd0501e09a860501e0a6806501e0a6805501e0a6804501e09681a501e096860501e0428c3501e0308d3501e0aa443501e07a50c501e07a4c4501e07a4cb501e07a503501e09a451501e07a0c4501e09a053501e09a051501e06a104501e06a0c4501e06a0cb501e06a1ca501e06a10a501e06a04a501e06a102501e06a0425026034c4350260144c2502607c05a502607c00a502607c002502604c05a502601c0d3502601c1d1502601c111502601c051502601c191502601c1c1502601c181502607605a501a0aac03501a09ac43501a09ac60501a0a8c03501a098c43501a098c51501a098c60501a092c70501a0aa804501a09a843501a0a6806501a0a6805501a0a6804501a09a403501a09a451501a07a10c501a07a0cc501a07a0c4501a07a0d3501a07a10b501a07a0ca501a07a0c2501a04a0d3501a01a2a3501a01a263501a01a28b501a01a24b501a01a283501a01a243501a01a29a501a01a25a501a01a24a501a01a0ca501a01a282501a01a242501a01a281501a01a241501a09a051501a06a1e0501a0a6071501a07610b501a0761a1501a0761e8501a0761a8501a0761e0501a0761a0501a076190501a096071501a096070501a0a4071501a0740d15029044c04502907a403502906a470502907840b502906a04a502906a042502906a002502906a070502907800b502906804a5029068042501d0ab004501d0ab003501d09b043501d09b051501d0a8c04501d0a8c03501d098c43501d098c70501d0a8803501d098860501d0a6805501d0a6804501d096860501d0a2805501d0a2804501d042984501d042983501d0428c3501d042803501d0a8443501d098470501d0a6443501d096451501d0664d3501d0664cb501d066503501d0780c4501d0780ca501d0781e9501d0781e8501d0781a8501d098051501d098070501d0680cb501d06810a501d0681e8501d068128501d068068501d0681a8501d0681e0501d0681d0501d0a6013501d0760ca501d07600a501d0761e0501d0761a0501d096051501d096018501d0660cb501d06610a501d0661e0501d0661a0501d0661d05025034c435025034c42502506a470502506a45850250144c2502507a00a502507a042502507a002502506a04a502506a070502507800a50250780425025078002502506804a50250760055025076004502507605a50190ab003501909b044501909b043501909b05150190a8c035019098c445019098c435019098c7050190a8804501909884350190a680550190a68045019096843501903290250190328425019098403501909845150190984705019096403501909645150190780cc50190780c4501907810b50190780ca50190780c250190781e950190781e850190781a85019098051501909807050190680cb50190681e85019068128501906806850190681a850190681e0501907610b50190760ca50190760c250190761e050190761a0501909605150190660cb50190661e050190661a050190a400550190a400450190740d1ffea3a1006ffea3a1005ffea391051ffea331104ffea3311e8ffea3a0c05ffea390c51ffea330de0ffe63410c5ffe63410c4ffe6340cc4ffe6390c68ffe6344514ffe631468bffe631450bffe631464bffe6314683ffe6314643ffe631468affe631464affe6314682ffe6314642ffe99ab003ffe99a1006ffe99a1005ffe9991051ffe9931104ffe99311d9ffe99311e8ffe99311d8ffe99a0c06ffe99a0c05ffe9930de8ffe9930de0ffe99aa804ffe997a90dffe997a8d4ffe997a983ffe997a8c3ffe997a803ffe999a851ffe99aa454ffe99aa443ffe99aa006ffe99aa005ffe997a185ffe997a0c5ffe997a005ffe997a184ffe997a0c4ffe997a004ffe999a054ffe999a051ffe996a105ffe996a104ffe996a1cbffe996a10bffe996a04bffe996a103ffe996a043ffe996a10affe996a102ffe59ab005ffe59ab004ffe59ab003ffe599b043ffe5940cc4ffe5940da8ffe5990c70ffe5990c68ffe599a851ffe599a403ffe59444c3ffe59445a9ffe597a10dffe597a0cdffe597a0c5ffe597a0c4ffe597a0cbffe597a0c3ffe597a11affe597a0caffe597a0c2ffe594a10cffe594a0ccffe594a11affe591a294ffe591a254ffe591a284ffe591a244ffe591a283ffe591a243ffe591a282ffe591a242ffe591a291ffe591a111ffe591a251ffe591a281ffe591a241ffe599a051ffe596a104ffe596a1e8ffe59a8071ffe59780c4ffe59781e8ffe59781a8ffe5978198ffe5998045ffe5998071ffe5998070ffe91ab003ffe919b043ffe919b051ffe91a0c05ffe9130de0ffe91a8404ffe91a8443ffe9198470ffe91a8006ffe91a8005ffe9178105ffe9178185ffe91780c5ffe9178005ffe9178184ffe91780c4ffe9178004ffe91781e9ffe9198051ffe9198070ffe9168104ffe916810affe9168102ffe91681a9ffe91681e8ffe9168128ffe9168068ffe91681a8ffe51ab004ffe51ab003ffe519b044ffe519b043ffe519b051ffe51a0c05ffe5140d84ffe5140cc4ffe5140c04ffe5190c51ffe5190c68ffe5198403ffe5198451ffe5198470ffe5198460ffe51444c3ffe51445e1ffe51445a1ffe51146a3ffe5114663ffe511468affe511464affe5114682ffe5114642ffe51144c2ffe5114698ffe5114658ffe51a8063ffe51780c4ffe51780caffe51780c2ffe51781e9ffe51781e8ffe51781a8ffe5198045ffe5198063ffe5198051ffe5198070ffe51681c4ffe5168104ffe5168044ffe51681e8ffe5168128ffe5168068ffe51681a8ffe98aac03ffe989ac68ffe989ac58ffe98a8c18ffe9898c44ffe9898c51ffe9898c68ffe9898c58ffe9894c70ffe98a0c06ffe98a0c05ffe9830da9ffe9830da1ffe9830de8ffe9830de0ffe9830da0ffe9830dd8ffe98aa804ffe989a851ffe98aa443ffe98aa005ffe987a184ffe987a0c4ffe987a004ffe989a051ffe986a0ccffe986a104ffe986a0c4ffe986a10bffe986a103ffe986a0c3ffe986a10affe986a102ffe58aac05ffe58aac04ffe58aac03ffe589ac43ffe589ac68ffe58a8c04ffe58a8c03ffe58a8c28ffe5898c43ffe5898c51ffe5894c70ffe5834d03ffe5834de8ffe5834d28ffe5834c68ffe5834da0ffe587a90cffe587a8c4ffe589a851ffe589a454ffe589a403ffe58444c3ffe58445a9ffe58445e8ffe58aa044ffe587a10cffe587a0c4ffe587a0cbffe587a103ffe587a0c3ffe587a0caffe587a0c2ffe589a054ffe589a051ffe589a068ffe586a10bffe586a04bffe586a1e0ffe586a120ffe586a060ffe58a6022ffe5876104ffe58760c4ffe58761ebffe58760c3ffe5876003ffe58761e9ffe58761e1ffe5876199ffe58760d9ffe5876019ffe58761e8ffe58761a8ffe5896051ffe5896070ffe5896068ffe88ab018ffe889b045ffe889b051ffe889b058ffe88a1006ffe88a1005ffe8841105ffe8841185ffe88410c5ffe8841005ffe8841184ffe88410c4ffe8841004ffe8891051ffe886110dffe886118dffe88610cdffe886100dffe8831104ffe88310c3ffe88310c2ffe88311e9ffe88311a9ffe88311e8ffe88311a8ffe8801283ffe8801243ffe8801282ffe8801291ffe8801281ffe88012a0ffe8801260ffe88a8c1effe88a8c1affe88a8c18ffe8898c1effe8898c45ffe8898c44ffe8898c1affe8898c70ffe8898c58ffe88a0c15ffe88a0c05ffe8840d04ffe8840d84ffe8840cc4ffe8840c04ffe8890c15ffe8890c51ffe8860d0cffe8860d8cffe8860cccffe8860c0cffe8830cc3ffe8830cc2ffe8830de1ffe8830da1ffe8830de0ffe8830da0ffe8800ea3ffe8800e63ffe8800e91ffe8800e81ffe8800e98ffe8800e58ffe88a881effe88a881dffe88a8804ffe88a881affe88a8818ffe889881effe889881dffe889881affe8898851ffe8898870ffe88a681dffe88a681affe88a6818ffe889681dffe8896851ffe88a841effe88a841dffe88a8404ffe88a841affe88a8458ffe88a8418ffe889841effe889841dffe889841affe88a6405ffe88a6443ffe88a6403ffe88a641affe48ab005ffe48ab004ffe48ab003ffe489b043ffe489b051ffe48a8c05ffe48a8c04ffe48a8c03ffe4898c43ffe4898c70ffe4898870ffe4896844ffe4896851ffe48669c3ffe4866903ffe4866843ffe48669c2ffe4898403ffe4898460ffe48a6405ffe4896414ffe4896403ffe48a4405ffe48a4404ffe4844584ffe4844583ffe48444c3ffe4844403ffe48445a1ffe48445d9ffe487810cffe48780c4ffe48780cbffe4878103ffe48780c3ffe48780caffe4878102ffe48780c2ffe48781e9ffe48781e8ffe48781a8ffe4898051ffe4898070ffe4898068ffe48681e8ffe4868128ffe4868068ffe48681a8ffe48681e0ffe4868120ffe4868060ffe48a6014ffe48a6004ffe487618bffe48760cbffe487600bffe4876103ffe4876183ffe48760c3ffe4876003ffe48760caffe4876102ffe48760c2ffe48761e1ffe48761e0ffe48761a0ffe4896051ffe4896068ffe48661e0ffe4866120ffe4866060ffe48661a0
  | 5, 1 => 0xa8e4414405a8e4414404a8cc441005a8e4314404a8cc37800598c5142cc398c51a0c0598c51a0c0498c5190c5998c5190c5198c5190c5898c519286098c51a080498c5190851a664414405a664414404a64c441005a664314405a664314404a64c378005a65ea43403a65ea00cd3a65e86100da666814405a666814404a65a812d0c966431a051965e843404965e843403965e831451965283306896468a100596468a100496468a10039646891051964689106096468a0c0596468a0c0496468a0c0396468444c396468904599646890458965e07a005966601c44d966601444ca466c10c05a466c1444aa466c14402a464314404a45e041405a45e06100da45e07a415a45e07a411a466014405a466014404a46601c051a45a07a00aa45a01a10aa45a01a181946ac01060946ac00c459466c1444b9466c1444a945036100d946431a051946611c051945116846894451a8c039445198c439445198c5194451a28049445192851944519286094451a080494451309d194451309d094451a600594451a600494451960519445196068945e032868945e07a403945e07a005945e06a04a9466018c4c946601444c946601c063946601c051945a011181945a04a04d945a06a045a626b16005a626314410a626316005a624314405a624314404a60c368443a60c37800aa60c368068a61e86100da626814404a61a833060962ab00c68962a300c68962a30a0689626314403962631444a960d368044960d368068961ea43004961ea43003961ea31051961117a004961117a00a961e843004961e840c11962681a054962681a051961a878054961a848054961a848069961a81810b961a81804b9629808868961d841005961d87ac03961d87a44c961d87a404961d87a403961d878411961d878420961d866468961d836468961d8065e0961d806520961d806460961d87a005961d86a04c962581c051962581a051a226c11404a226c1444ca226c14410a226c16005a210441405a21046100da224414405a224414404a218443405a20c47a00aa20c46a04aa200490c44a200490c43a200490c68a200498044a200498051a226307841a22631c01aa22631c018a226316005a228301415a210341005a21036100da224314404a218343005a21836300da20c368444a20c368468a20c368068a200398c45a200398c51a2003a0404a200396044a200396043a200396068a22a20101da22a20101ca226214415a226214414a226214403a22621c01da22621c01aa22621c051a22621c018a229a0101ca225a14414a22a10101da22a10101ca22990141da22990680ca22990680b922ac00c689226c1444a922a300c689219a10d83921d16100d921d160c0c921116100d9211160c0c9211100dc192111684149211176404921e043004921e031068921e032c68921e07a404921e07a403921e07a005921e06a04a922601c051922601a051921a06a068921a048069921d840c11921d878404921d878403921d878005921d868068922581a05192198480699219868068ffe631450bffe997a803ffe997a005ffe997a004ffe996a04bffe996a043ffe591a111ffe9178005ffe9178004ffe9168068ffe5140c04ffe51144c2ffe5168044ffe5168068ffe987a004ffe5834c68ffe586a04bffe586a060ffe5876003ffe5876019ffe8841005ffe8841004ffe886100dffe8840c04ffe8860c0cffe4866843ffe4844403ffe4868068ffe4868060ffe487600bffe4876003ffe4866060
  | 6, 0 => 0xa8e84202a391080a8cc4502a331080a8e83202a390c80a8cc3502a330c8098e84202634114098d04202639108098e832026340d4098d032026390c80a66842029991080a64c45029931080a66832029990c80a64c35029930c80a66a8202997a140a65e8202999a080a65a8502996a080966832025940d40965032025990c80966a8202597a140965e8202594a14096468502599a080965a8502596a080966a02025978140965e02025998080a46832029190c80a44c35029130c80a46a02029178140a45e02029198080a45a05029168080946832025140d40945032025190c80946a02025178140945e02025198080945a05025168080a62832029890c80a60c35029830c80a62a8202987a140a61e8202989a080a61a8502986a080962a8202587a140961e8202589a080961a8502586a080962982025876140961d82025896080a22842028841140a21042028891080a21845028831140a20c42028801140a22832028840d40a21032028890c80a21835028830d40a20c32028800d40922a02024878140921e02024898080921a05024868080922982024876140921d82024896080921985024866080ffea3203ff98c80ffe99203ff96480ffe91203ff94480ffe98203ff96080ffe88203ff92080a8d40456a35010da8d40336a3500d4a8d40432a3500cca8d4036aa35001aa8d407a2a3501a8a8d40782a3501a0a8d40442a3202aca8c809b2a32028ca8c80932a3202a3a8c8098ea32028ba8c8092ea320291a8c80946a3202a0a8c80782a320260a8c80682a320298a8c80762a320258a8c80662a32028898d4043663500cd98d4043263500cc98d4046a635005a98d407a263501a898d4078263501a098d4034263202ac98c809b2632028c98c8093263202a398c8098e632028b98c8092e632029198c8094663202a098c80782632026098c80682632029898c80762632025898c806626320248a654043699500cda654043299500cca65407ce99500daa65407c699501b1a65407c299501b0a65407a299501a8a654078299501a0a65404629950110a6480ab2992026ca6480a529920254a6480aae992026ba6480a8e9920263a6480a4e9920253a6480a2e992024ba6480aaa992026aa6480aa69920269a6480a869920261a6480a469920251a6480aa299201e8a64809a299201a8a6480a8299201e0a648098299201a0a6480a6299201d8a64809629920198a6480a42992028896540372595010c96540332595011a965407c65950131965401c659501b1965407a659501a9965407c259501b0965403c25950030965407a259501a89654078259501a09654036259500d096480ab2592026c96480a52592025496480aae592026b96480a8e592026396480a4e592025396480a2e592024b96480aaa592026a96480aa6592026996480a86592026196480a46592025196480aa259201e8964809a259201a8964803a2592002896480a8259201e09648098259201a096480a6259201d8964809625920198964809425920248a454043291500cca454036a915001aa45407a691501a9a45407a291501a8a454078291501a0a454044291202aca44809b291202a3a448098e912028ba448092e91202a1a44809869120291a448094691202a0a44807829120260a44806829120298a44807629120258a4480662912028894540352515010c94540332515011a9454016a51501e9945406a651501e8945406a251501e09454068251500d094480ab2512026c94480a8e512026394480a2e512024b94480a86512026194480a46512025194480a8251201e09448098251201a094480a6251201d894480962512019894480922985010ca614033298500daa61407c698501b1a61407c298501b0a614078298501a0a61404629850110a6080aae982026ba6080a8e9820263a6080a4e9820253a6080aaa982026aa6080aa69820269a6080a669820259a6080a469820251a6080aa298201e8a60809a298201a8a6080a6298201d8a60809629820198a6080a4298202889614037258501f39614046a58501f1961406c658501e19614068658501f0961406c258501e09614068258500d89614034258202ab960809ae58202a39608098e58202939608094e58202aa960809aa58202a9960809a658202999608096658202919608094658202a8960807a25820268960806a2582029896080762582025896080662582025096080922885010da214063688500cda2140036885010ca214063288500cca214003288500daa21407a28850128a21401a288501a8a21407828850120a214018288501a0a21404628850110a2080ab2882026ca2080a8e8820263a2080a8a8820262a2080a6a882025aa2080a868820261a2080a668820259a2080a468820251a2080a8288201e0a20804828820060a208098288201a0a2080a6288201d8a20804628820058a20809628820198a2080a4288202889214068e485011a921407a648501a99214078648501a1921407a248501a89214078248501a09214036248500d092080ab2482026c92080a8e482026392080a8a482026292080a6a482025a92080a86482026192080a66482025992080a46482025192080a8248201e09208098248201a092080a6248201d8920809624820198920809424820248ffd43aafff50e6bffd43a8fff50e63ffd43aabff50e6affd43a6bff50e5affd41ab3ff5066cffd41a8fff50663ffd41a8bff50662ffd41a6bff5065affd40ab3ff5026cffd40a8bff50262ffd40a6bff5025a50eab31943aacc550eab31143aadc350eab60d43aacc350eab00d439ad0550e6b70d439ad0350e6b10d439ad8350e6b445439adf050e6b781439ad2050e6b18143a8cc550ea370d43a8d8350ea330d43a8c0350ea37c143a8db050ea36814398d0550e6370d4398d0350e6310d4398d8350e634454398c5150e637c14398db050e6378143a2d0550e8b31543a2cc450e8b30d43a2c0350e8b6c14392d0450e4b40d4392c4350e4b7454392d1150e4b1454392df050e4b4c14392c7050e4b7a14392da850eaa31543aa8c450eaa70d43aa98350eaa30d43aa80350e6a355439a9c350e6a40d439a84350e6a60d439a91150e6a7a1439a9e050e9a41943a698650e9a31943a680650e9a41543a698550e9a31543a680550e9a61143a68c450e9a01143a69c350e9a60d43a68c350e9a00d43969c350e5a40d439684350e5a60d43969aa50e5a44543969f050e5a6c143969e850e5a6a143969e050e8a41143a28c450e8a30d43a280350e8a6c143928d450e4a40d439284350e4a745439291150e4a14543929f050e4a78143929a050ea945543aa50d50ea941543aa4c550ea935143aa4cc50ea941143aa4c450ea930d43aa40350e69415439a4c550e69411439a4c450e6940d439a44350e69745439a51150e6914543aa0c550ea831143aa11350ea830d437a2ac50de89b1437a29450de8951437a28c50de8931437a28450de8911437a0c450de8a8d437a26350de8a4d437a25350de8a2d437a24b50de8a0d437a24350de830d437a28a50de8429437a24250de8309439a11550e68351439a0d350e68745439a11150e68145439a1e850e68781439a1d850da8ab1436a26c50da8a51436a25450da8a31436a10c50da8931436a2a350da898d436a29350da894d436a28b50da892d436a0cb50da8929436a0ca50da8a81436a1e050da8981436a29850da8761436a25850da8a41436a1d050e9831143a61da50e987c543a61b150e987a543a61f050e986c143a61e850e986a143a619850dd8ab1437626c50dd8a51437625450dd8aad437626b50dd8a8d437626350dd8a4d437625350dd8a2d437624b50dd8a0d437624350dd830d43762aa50dd89a943762a950dd89a543762a150dd8985437629150dd874543762a850dd87a1437626850dd86a143762a050dd8781437626050dd8681437625050e5866943961f150e586c543961e950e586a543961d150e58445439605150e587c143961b050e587a143961a850e5878143961d850d98ab1436626c50d98a51436625450d98aad436626b50d98a8d436626350d98a4d436625350d98a2d436624b50d98aa9436626a50d98aa5436626950d98a85436626150d98945436619150d98aa143661e850d989a143661a850d98a8143661e050d9898143661a050d98a6143661d850d98961436629050e9076943a41f150e906c543a41e150e9068543a41f050e906c143a40f050e900c143a41e050e9068143a419850dd0aad437426b50dd0a8d437426350dd0a4d437425350dd0aa9437426a50dd0aa5437426950dd0a65437425950dd0a4543741d150dd0aa143741e850dd09a143741a850dd03a1437402850dd0a6143741d850dd0961437419850dd0941439419a50e507c543941b150e5078543941a150e50745439411150e5014543941f050e506c143941e050e5068143941d850d90aad436426b50d90a8d436426350d90a4d436425350d90aa9436426a50d90aa5436426950d90a65436425950d90945436419150d90aa143641e850d909a143641a850d90a6143641d850d90961436419850d90a4141ab0c6506ac31541ab0c4506ac70d41ab183506ac30d41ab0035066c419419b1055066c411419b1c35066c40d419b0435066c60d419b1115066c14541a8cc5506a331141a8dc3506a360d41a8cc3506a300d41a8df2506a37c141a8db0506634154198d045066370d4198d035066310d4198d83506634454198df0506634c14198c70506636c141a88c5506a231141a89c3506a260d41a88c3506a200d41a89f0506a26c141988d55066270d41989035066210d4198983506627c94198911506627c141989b0506627a141989e05069a41541a69855069a31541a68055069a61141a68c45069a01141a69c35069a60d41a68c35069a00d41969c35065a40d41968435065a60d41969115065a7a141969a85065a78141a29855068a31541a28055068a61141a28c45068a01141a28c35068a00d41929035064a10d41929d15064a44541928515064a7a141929e0506a131541a8504506a131141a84c3506a100d41a85f2506a17c141a85b05066135141985045066131141985035066110d4198511506617c14198530506611c141985b0506617a141a65045069931141a64c35069900d41a65e8506996a141964d45065933141965045065931141965035065910d41965d1506594454196451506597a141965a8506a031541a80d4506a031141a8113506a030d41a81f1506a07c141a81b0505e0ab1417826c505e0a31417824c505e0a114178244505e031141782ab505e09ad41782a3505e098d4178293505e094d417828b505e092d41780cb505e0a0d4178243505e030d41782aa505e09a941782a2505e0989417828a505e04294178242505e030941782a9505e09a541782a8505e07a14178268505e06a141980d3506607c941981f1506606c541981d1506604454198051506607c141981b0506607a141981e05066076141682ac505a09b1416828c505a093141682ab505a09ad41682a3505a098d4168293505a094d416828b505a092d41682aa505a09a941682a2505a0989416824a505a032941682a9505a07a54168269505a0aa141681e8505a09a141681a8505a0a8141681e0505a09814168298505a07614168258505a0a4141681d05069835141a60c45069844d41a60c3506987a541a61a9506987a141a61a8505d8ab1417626c505d8a8d4176263505d8a4d4176253505d8a2d417624b505d832d4176283505d890d41760c3505d8a894176262505d8a29417610a505d890941760c2505d8a854176261505d8a8141761e0505d898141761a05065834d41961e9506586a541961d1506584454196051506587a141961a85065878141961d850598ab1416626c50598a8d416626350598a4d416625350598a2d416624b50598a8941662625059892941660ca50598a85416626150598a8141661e05059898141661a050598a6141661d85059896141662905059874141a41da506907a541a41a95069078541a41a1506907a141a41a85069078141a41a05069066141742ac505d09b141742a3505d098d41742a2505d0989417429a505d096941742a1505d09854174299505d09654174291505d074541742a0505d07814174260505d06814174298505d07614174258505d066141742505065066941941e9506506a541941e15065068541941d1506504454194051506507a141941a85065078141941a05065076141642ac505909b141642a35059098d41642a250590989416429a5059096941642a15059098541642995059096541642515059064541642a0505907814164260505906814164298505907614164258505906614164290502ac31540ab0c4502ac70d40ab183502ac30d40ab0035026c415409b1045026c70d409b1035026c10d409b1835026c445409b051502a231540a88c4502a270d40a8983502a230d40a8803502a27c940a89f0502a26c140989045026270d40989035026210d40989835026244540989f0502624c14098870502626c140989e85029a31140a69c35029a60d40a68c35029a00d40a69e85029a6a140969045025a70d40969035025a10d40969835025a44540968515025a7a140969a8502a131140a84c3502a100d40a85f0502a16c140984d45026140d4098443502617c94098511502617c140985b05026178140a45055029161540a44c55029101540a45045029161140a44c45029101140a44c35029100d40945035025110d40945a25025144540945e8502516a140945e05025168140a80d4502a031140a8113502a030d40a81f2502a07c540a81f0502a06c140782ab501e09ad40782a3501e098d407828b501e092d40780cb501e0a0d4078243501e030d40782aa501e09a9407829a501e0969407828a501e04294078242501e030940782a9501e07a54078269501e0aa140781e8501e09a140781a85026034d40981f1502606c540981d1502604454098051502607c14098130502601c140981b05026078140981d8501a0aad406826b501a0a8d4068263501a0a2d406824b501a0aa9406826a501a0a69406825a501a092940680ca501a0aa54068269501a0aa140681e8501a04a14068068501a09a140681a8501a0a6140681d8501a09614068290501a074140a41135029030d40a41a2502907a540a41a95029078540a41e8502906a140a41e05029068140742ac501d09b140742a3501d098d40742a2501d0989407429a501d0969407428a501d04294074242501d030940742a1501d09854074299501d09654074199501d0a8140741e0501d098140741a0501d0a6140741d8501d096140741985025034d40941e9502506a540941e15025068540941d1502504454094051502507a140941a85025078140941a05025076140642ac501909b140642a35019098d40642a250190989406429a50190969406424a5019032940642a15019098540642995019096540642a050190781406426050190681406429850190761406425850190661406429050190743ffa8e84ffea3913ffa8cc4ffea3a0fffa8e43ffea330fff98e84ffe63413ff98e44ffe63a0fff98d03ffe6390fff98e91ffe63447ff98c51ffe99ab3ffa6694ffe99a13ffa6644ffe99313ffa6683ffe9990fffa64c3ffe99aabffa65eaffe999abffa66a9ffe99aa3ffa65e8ffe999a3ffa65a8ffe59ab3ff9666cffe59a53ff96654ffe59a0fff96503ffe5990fff966aaffe599abff966a9ffe599a7ff96691ffe59447ff966a8ffe597a3ff96528ffe591a3ff96668ffe596a3ff966a0ffe59783ff96660ffe91ab3ffa466cffe91a0fffa4643ffe9130fffa46a1ffe91987ffa46a0ffe91783ffa4660ffe91683ff946acffe519b3ff94683ffe5140fff94643ffe51a87ff94661ffe51a47ff94511ffe51147ff946a0ffe51783ff94660ffe51683ffa62abffe989afffa62a3ffe9898fffa6293ffe9894fffa6283ffe9890fffa60c3ffe98aabffa626affe98aa7ffa62a8ffe987a3ffa6268ffe986a3ff962abffe589afff962a3ffe5898fff96293ffe5894fff960d3ffe58aabff961eaffe589abff962a9ffe589a7ff96291ffe58447ff962a8ffe587a3ff96268ffe586a3ff96298ffe58763ff96258ffe88ab3ffa226cffe88a13ffa2104ffe88913ffa2184ffe88313ffa2004ffe88a8fffa2263ffe88a0fffa2103ffe8890fffa2183ffe8830fffa2003ffe88a8bffa2262ffe88a6bffa225affe88a87ffa2261ffe88a67ff922acffe489b3ff922a3ffe4898fff922a2ffe4898bff9229affe4896bff9219affe48a87ff92261ffe48a67ff92259ffe48a47ff92111ffe48a83ff921e0ffe48983ff921a0ffe48a63ff921d8ffe48963ff92198
  | 6, 1 => 0x2a3a1006a8e84016a391051a8cc4412a3311e8a8e83016a390c51a8cc378263410c598d04312639105198d033126390c5198e431a2634451498c51a2e631450b98c5192e631468398c5190e631468a98c5192a631468298c5190a99ab003a668401a99a1005a66441469931104a64c476699311e8a668301a99a0c05a66431469930de8a64c378299aa804a65ea436997a8d4a65ea60e997a8c3a65ea00e999a851a66a915299aa006a66a8016997a185a65e8316997a005a65e8612997a0c4a65e8012999a054a6668146996a105a65a8412996a1cba65a842e996a04ba65a842a59ab005966ac01259ab0039666c10e5940cc4965036a25990c51966431c25990c689666a112599a851965d133259745a99651130e59445a9965e8436597a0cd965e8316597a0c4965e832e597a11a965e832a594a10c96528332594a1da9652846a591a29496468952591a28496468912591a2839646890e591a2829646890a591a29196468446591a28196468906599a051965a8412596a1e8966a01c659780c4965e066659781e8965e06a25998045966601c65998051966601c291ab003a466c10e919b051a46830169190c51a44c378291a8404a46611c291a8006a46a00169178105a45e061691780c5a45e00169178184a45e03129178004a45e07a69198051a46601c29168104a45a042a91681a9a45a07a29168128a45a01a291681a8946ac01251ab0039466c112519b0439466c14651a0c05945036125140cc4945030125190c51946431a25198451946611c251984609451130e51445e19451168651146a39445198e511468a9445192a51146829445190a51144c294451a625114658946a018e51780c4945e032a51781e9945e07a251781a8946601165198063946601465198070945a07125168104945a011251681e8945a04a25168068945a06a298aac03a626b1a2989ac58a62a30629898c44a62631469898c68a626316298a4c04a62531469894c70a628301a98a0c05a62431469830da9a60c36869830dd9a60c37a29830de0a60c368298aa804a626a14698aa005a61e8612987a0c4a61e8012989a051a61a8332986a104a61a8312986a10ba61a830e986a10a962ab01658aac04962ab00e589ac439626b1a258a8c04962a300e58a8c289626310e5898c51962531125894c70960d370e5834d03960d37a25834d28960d31a25834da0961ea432587a8c49626a112589a8519626915258745a99611130e58445a9961117a2587a10c961e8312587a0cb961e840e587a0ca96268152589a051962681a2586a10b961a812e586a1e0961a8482586a0609629808a5876104961d831258761eb961d87a658761e1961d866658760d9961d806658761e8961d86a25896051962581c25896068a22ac062889b045a226c146889b058a228401a88a1005a21044168841185a21043168841005a210461288410c4a21040128891051a2184436886118da2184336886100da20c441288310c3a20c430a88311e9a20c46a688311e8a20c46a28801283a200490e8801282a2004a0688012a0a200498288a8c1ea22a306a88a8c18a226307a8898c45a22631128898c1aa22631c28898c58a228305688a0c05a21034128840d84a21033128840c04a22430568890c51a21834328860d8ca21833328860c0ca20c330e8830cc2a20c37868830da1a20c37828830da0a2003a8e8800e63a2003a068800e98a200396288a881ea22a207688a8804a22a206a889881ea2262076889881aa22621468898870a229a07688a6804a229a06a889681da225a14688a841ea22a107688a8404a22a106a889841ea2261076889841aa229901688a641a922ac01648ab004922ac00e489b0439226c14648a8c05922a301248a8c039226310e4898c709226211248988709225a11248968519219a70e48669039219a10e48669c29226118248a64059225905248a4405922910124874584921d160e48745a1921d176648445849211160e48444c39211100e48445a192111766487810c921e031248780cb921e040e48780ca921e040a48781e9921e07a248781a8922601464898070922601a248681e8921a04a24868068921a06a248681e0921a048248680609229805248a6004921d862e48760cb921d802e4876103921d860e48760ca921d840a48761e1921d878248761a09225814648960689219878248661209219818248661a0ffea3313ffa8cc3ffe63413ff98d03ffe63447ff98c51ffe99313ffa64c3ffe997abffa65e8ffe996a3ff96503ffe59747ff96511ffe597a3ff96528ffe591a3ff965a8ffe59783ffa44c3ffe91783ffa45a0ffe5140fff94511ffe51147ff945e0ffe51683ffa60c3ffe987a3ffa61a8ffe5834fff961eaffe58747ff96111ffe587a3ff961a8ffe58763ffa2104ffe88613ffa20c4ffe88013ffa2103ffe8860fffa20c3ffe8800fff9219affe48747ff92111ffe48783ff921a0ffe48763ff92198
  | 7, 0 => 0xa8d40a8c8098d4098c80a6540a64809654096480a4540a44809454094480a6140a60809614096080a2140a20809214092080ffd43ffd41ffd4050eab50e6b50ea350e6350e8b50e4b50eaa50e6a50e9a50e5a50e8a50e4a50ea950e6950ea850de850e6850da850e9850dd850e5850d9850e9050dd050e5050d90506ac5066c506a350663506a2506625069a5065a5068a5064a506a1506615069950659506a0505e050660505a050698505d8506585059850690505d05065050590502ac5026c502a2502625029a5025a502a1502615029150251502a0501e050260501a050290501d05025050190ffea3ffe63ffe99ffe59ffe91ffe51ffe98ffe58ffe88ffe48
  | 7, 1 => 0xa8e84a8e44a8cc4a8e83a8e43a8cc398e8498d0498e4498e8398d0398e4398e9198d1198c51a66aca6694a6684a6644a64c4a6683a6643a64c3a66aaa65eaa666aa66a9a66a8a65e8a6668a65a8966ac9666c9669496654966839650396643966aa9666a966a99666996691965d196511966a8965e8965289646896668965a8966a0965e096660a46aca466ca4683a4643a44c3a46a1a4661a46a0a45e0a4660a45a0946ac9466c946839450394643946a194661946919451194451946a0945e094660945a0a62aba626ba62a3a6263a6293a6253a6283a6243a60c3a62aaa626aa62a9a62a8a61e8a6268a61a8962ab9626b962a3962639629396253960d3962aa961ea9626a962a99626996291961d196111962a8961e896268961a896298961d896258a22aca226ca2284a2104a2244a2184a20c4a2004a22a3a2263a2283a2103a2243a2183a20c3a2003a22a2a2262a229aa225aa22a1a2261a2299922ac9226c922a392263922a2922629229a9225a9219a922a192261922999225992291921d192111922a0921e092260921a092298921d89225892198ffea3ffe63ffe99ffe59ffe91ffe51ffe98ffe58ffe88ffe48
  | 8, 0 => 0x50d41503ff
  | 8, 1 => 0x2a398e99966919469896288923ff
  | _, _ => 0

def repWidth : Nat → Nat → Nat
  | 4, 0 => 50
  | 4, 1 => 50
  | 5, 0 => 40
  | 5, 1 => 40
  | 6, 0 => 30
  | 6, 1 => 30
  | 7, 0 => 20
  | 7, 1 => 20
  | 8, 0 => 10
  | 8, 1 => 10
  | _, _ => 0

def repCount : Nat → Nat → Nat
  | 4, 0 => 800
  | 4, 1 => 35
  | 5, 0 => 2850
  | 5, 1 => 253
  | 6, 0 => 1604
  | 6, 1 => 475
  | 7, 0 => 103
  | 7, 1 => 174
  | 8, 0 => 4
  | 8, 1 => 11
  | _, _ => 0

def hitSlots : Nat → Nat → Nat
  | 4, 0 => 0x4ed0000000008e5000000b431cda1587f0629254951278456c17611fda09bd50004b30453fd1039715255014c10bd03a0993a5747b1d6ef0a12451259890bb4adbf9a2a2a7c353f9035c755a5a670362417d53ed7296712616e779d7025698fd9a1669889b2997d0410006e528939e171b315cf000c1500010d23900057d6152c16753c1adea952e15dd00082b00086f00000078d0e10000000000000000000ad0191190002097ef349797a5188e64dbcd16a59d8cd529abd5b90e9327a790250911c989f1859213519a247972154f46d0b382dc61000af18490004f1000000000af945b000000b8d319000000000000add0000002197e100000072d000a816c90000008158751627ed5ed5797ad99d3b15d71552461598f981f20d2b96fd4e16bd5193cd78900048d22529d00000056163100000000000049da635310690d900018d00000071116d9029fda7fb95b61759189aafc4d8610f11d54717435110890fd2bd91d0212d514101ac118b176a719b2bc714ae27a70d4897091a92edbdaa9d145c7d8791791024fd745a8d07d6be0c5727881b7d0c15e27e51157cd6c57cb5654213015059d546113112900032100084d9dda4998d0006f50006d1b39b5da399bd1da7491e57a9029c41985776b576b543f0055c34e974d279bc1bb53f500077dbd10005b5b1504da0d5bb775a210004ab0000009af042b4f2b12b54122130e527dab10007bf00044957500053d3c59296d59f9012afe1112059393692118d9077a7194d5660eda7d13516f2e73d1677000000231c5db717bbbe90d14bd9c92a58116454250499ad36d999a771e97a13158a9000000911bbd0004590005f1071000000000259000000aaa6a555d405000000000009391c09000000afa0000003bdbf10814e500000033305160503d2e9a31895659000b2560d9cdc597eb08741d43190b7f19bbac100082f5e180500000098157660908f89da613662df7dd782207469aa500da350dd0111c547d4529b9bc50006f385d000000000ba516b265961af528d079aa990163d5098c10f50cd90530d1e217d73d8192993059986af8c93094014a600000000022d0f90000000000007b31d68e1596bdd0af000841a0e0017552c7a7315d06b19dc310a9b3fb17c0da6982365daed1d1885169b59959865415a7b0003b988f47506d8a10009a5b3a4465393ad7a50002e20002f18b92915590572a14678013253750392833898bd0005417794c544d6f95d187d739c2975d4d5a019fa2493a14395ea1db55100080a00000021531d1b9a6d9d17f90005cd335725b092695c100059920106f1b576d4af3be02db195553451ea74ea85c45275bc9c051dd5810003da7af00095554950e1656d7ba10316b3b859752cd619765a41512b4d1918d12fb7954819e505d4dd4cd000a5546a00000096295d6a14a57bd3619cb5b7181000b0d0004412230000000ff647a663e1601000000000000781000bad00092d0000000002357b10008990d5095b810000005020009ab7fd331ba95b1b89a9185e7e7965000000000000685000000282699ae5741803a99a05000000000000000bf5000000451000000000735341777000000b410003953850006890000001950000004f50000007269a96414357050b5000000000411000bd953586dae1a3f23d3e549100000033d83d6798660a524d20354551722912d9f1aa10334994b5be12dd0651055df2859430000000000005fd0008910000000000004290000000008ed0002a30000008090c7b45c2d0009f5a438f10007a343d032000bc6649b9152d4330006ffac9bb9661b3d9e17a7083753b556656f1b756dda4d2c5000000000175ad11ed7d1000000271b35919bfdac5c3dafd00058d8d55f54f99b166d4a1ad5691a199a64c9c018c58298e97993f144b5854d98070c96e96edab553f67d5e5a65571251a598dd96d8fbb4b1f571351561d000c190000007f5000000000b113290000000003a9a2db9d54d0009e92d959f21dc6d4b716c00000050d34d09d40db6547bc693b56296a98510558ad71d3710004a32810ab0756d90000000000965bf3659ed14d62120fa2575183535900000042d3990000003dd83925d000c1d90d5ad00000069d000b69b21b6d5a9000a890851b17c50001a50004d110100081dacd7853d5c65ae9000b2d9c17c10000000000000000000000006032fd48b1c10b97b500014900000026dbb11991f90cb109b055914b19c5b516c22952f59957c993179b1d937d825855915a1e771b799691f18a52732ad01d9c245db87bcaab945500ba29979821061a5e13948580d64a80b9b52d19350007570007012020000000004a9a1d93d2a941900039d94968179120b1ee6359d92f9b99000a5d6a20000004023390000000975d9951000616b3e7d99946e149f00000000011d0009910348d78698310158bf6ee255b776b1a45059c791bd2e5ad95e9bed0b17315d54da3e72c95215bd00008d9063812d2ae67b985994123602e52732d1b6409000000000c2188d94515139a00062d909161a116135951216258b58f2379b0187100056d85f6ad38d5896cd000000c512af8f5445be50007e9639827ae21e613d73f6559471a10000002215f9c55c3951d3d9b3b6513c9a756b9b49aadc255c54b91ad1335a136b00061100068d35d715c498ee1e13e9769000aea0005c9000000000695000a3d0003554650fe311000
  | 4, 1 => 0x350046494155000000000000003d050000390e6913651909591d610000000000002d638589216d4d51718125005f000000003129000082795d7d3a750b110000060d45004b0115
  | 5, 0 => 0x15b43adb8919640d997fda597bdcdfd673dd3b1595c693bbce2d6b3900b0815fa52494f956b556f134b462a5c3662167962f54595cb558e5c253949f9d00020b502540719fb5e499b74d1500469d595ceb115da58a9209447938748eb6029d29286a79a066664d051465183863013ef46916aa52190e281d935359b15845831ab945d8000068d00756b618d665d000000061b400000023358b365d90000000000000000000009d9895d712d9716de48e17484945626671d0b9586a78f46a98be45c160640a10000000a04d6b15188000a925bad77d5b515d5400000008113ab4000432433247c8000006412e000066d796494d7be5c0d95e60293794a37562427a5ff6c612aa60d909647357f0537160e4e2b1b4490680258c76a66a155306b2d68c4c2102fc69d00028c950a9f89410d72300000000001d550002a7d1bdcd79940405969441ef950578f567665963e4c712c05f022234bba61756f524e5fad67e59812984bb2079d1596536b9125e412da7148b599d47199a05f5d3584a7d42a4cad16742d97d8de7da2a5d7986f46e550599d1763e9c664a64473ea4c1572edb6916450617754e3d71551b55cd485f2e6400099b400000000004c09a6512c57f1b114000000000000000000000000a2840000000ac14f84e0b98f4cdd5bf9fb770f80000ce6c51ac657218a7dc3a34d4991a944fb73aa9267745e3919c969f10001f09000000029b4f0d0000000025800000000005035d89000000040a53dd23e4c010594bc95a961f95a7e2a12f09e4188240001e880009495d1db1040002a8400000028d914a400000000000000b95add435189247dd88a5aa122c45de57d9ed51454000000212d22a5de10ee59596f0da29798800000003c98314159000037315d80006b1400030449190d15221643400014661193bb4441728527600003c11ca42c31751dc51feceda00001f9ac05519471e1610000000181400000000000001bed40152314f040e14045197561439979d67d19c147d1b135ec189c5851a4365d168894f906d68655c6574797f69452055be55635889001d66daf061e33145cf50ccde99203504da08624d7405345a66428143b5209309446e4fd569d0d65db529043c6681494f414682a4c463113da581d334ac752d6679531a599d71d4ef9000000064c487e450abb961f43f5000054f0000000000000000005895dbe017435402d9df625106ae42a5b74ff7727576163f535d1025a55a7e4632aa85d658ea978b1d246692bf960d49f67dd7135ad903a4fc9964681d258906d863527184f4e2923a59c128fcf2301d41a190061451f6496127f6aed4dec9e3a3e54013d0448301263e600010b52e04c3f573671107b444d43ce27548f40005d2400000022952c9e6e56fe6bf9000026d365c89eb1a673d25c517588591ce6dbcd090000000000000094342de620c00000000009e144890000000921646172e40005999d6103e87c98144e150f9c4c68305399000000000012f900000000002671462c5dd8404ab91cf5e194e141253b5d6193ca41eb0aa5f2700005850b5947f39bcc07000101b000036f81f6c098ab46662ac467552f57ef65446c96dca2ed0000c2d6b9584526e498357456818374459604800000016de615400018464a168748d59b251c16e7600112fc0006c46371000197d867400000000001e95efd1efd3919fa6409158dc05564400000015813f94c456cdc49530162799eb49c90000000000000000000004d440c90001321a42400000000000000000a566a9901a40005b256357a28e8d2705c8d18f4b1100000005de4d0d2674a7b61a54e50000000400d6e9081cda921f417baa95fc9076db4d0000000841445500010d10000000a4451a14a05ed195c5b0f1ee6a4150d6349a9641304655a9503e44d755b5d227aa678228e56492fadc854175199283c000000000082642b63294385000000064640000000000368400084840005f9545a9046169514c000a5540000000aed5ca400000016a62cc628d76b677e68e5c76a7b418b84768194006c01071c000a8e606d3dd4a9d73ae45d00000003646b8d0000000000178e8955a4353443f1abc413d4c1400000011c595140000000000ab052c539f41391fe62b9a6f52895814e896f0400000000008b4400000000003db5f7146dc69e93f6bed57b57a9ad25e5aa464000000057d435c00000000003efe21562e800000000003fe5a193d9591f0001b3d6cd4d372d34000a52400069f46ea59bd6e68e645ed8c5527e78e4b6d869cf61003d4190c14b658595dfd590500d04759df00357c52446709454816700d5f15064dce300249bd20f432124d9ed93e060216f9d5a11e44c8797a69655b052954c4df8124058a53a864f978241190509da525b4b39a6155ce58540005e1c000a67502b50468a39844000348400072cd7dd3594f396dc6b41339e305000000067d449d18dea7100008c900000000001fef976cb6902aac157a680008814e7133ac0e5018602d3a8800000010c158295e27b247855aa88cd66540001ea4000000000017941792f9dac9000000000000008ca4000000000078d66419e467353cc6429983e33251b683500025c5000157b2b180001af4bb770240000000e31178e7657b940000001b052294e5a00028b91f8e38982a623100000000df615100004113b555c12f35b1798b61a1b0a55ad84d4fa50001f5148340004cb4f1d4cf55e1780cfdd0000935000240d328a8d15dd440d07f87e95fd58d1278675676a4abd375450d85c49ab451845d5e360f56d7dc7d9abc0001ed54250000000008ce7f000000000003119394000000000000024c10000b2b0000a31a3f5b7515340008124000000000093767d90001875907962536050a34af5fe70001475000000057d400052a4db614b40008f3400000002c97cddc8b5564c6d1fb90dd50b67c115649fa1da9e1e3d44b41139533900000000000000000000090eddf96ce5f052a7e1157ee4bf150ba921470c3a59ed400029454918b0c0009a3c1312d26c355c545a94b948750ede0450001eb164559650001cf76199901a8f48ed0002091b09400000002d55eb55d598d507d0002b61842626daac404e2fa64c509256f91d36bbd96865ef1c55f13266df45a384a773124cf7823513653d4f7f8986b315bb49f648a93b9830d80d00000007f1400027c603d000000000000000b15f6d4f4400059c51dd1335bd5000000019946010000000065c0000001f796ad800000000005ca8c8500000005d040004ac5a757fe436b4e9400092742b90000000856604784355caa315b650135c1d6624ef567b557d612c5af73a59d955c810e94762382664493768427d000098153663ad07853ed0001c9122680000cbe915026c9f500011260f4400087f40000002b996efe08f0894ca3000076b0000ccbaf754159ff400072f400074555010001f9105c40007b35ab56fa472f00005610002a1989a5665875a0bd026400042269c111ac00000c800016b647d29d5ce5371656d0001f8d211509b000000000000003a45e6971754397ca400000011eaafa4679a87594b4bc53a1766578943d57013824edd60d5fb150c8469031cf47821513aab55c1955d600d52fda7f11fd7116025ce144c5f554de8a932fe5eb95f654b5098475d8b7468500029e93fc48bf08d62f16c04d256844000000138397ce6ad128800026a512f6fd402500017312e85d379fe40003c158658c3509e107e5515254000ab2400039b4dba000000000000001d161e16ab80004ba498f000145d3d540002bcc0006e940009914f11b07400030a4cf14ae400000000000000d55295800061c877d286c8ad860400000000004f58a8544a53879bb693d9daa981449612503c64aa403e78d38792f57d86c853eb421504ed7ed7956b4d6315b6b6d0c84a807400024a4b0599ac00000024a92c7641950164453c91b1577742c60ba8e213bc4b91057842157695dd23c4c5d140eb2100026c54b8400000017057ed45c50408a2205a61f50e48000006c3d97d942ff46060ad374658daea5bf39e4a6eb756463f99252053f0e97d591400000028269756a6d000027944e4365111cd3f4c75fd96246031000046d000113d0000000000000074640009e2a4fa7044ea962b65658ac55613fa65ed0976002ae147551c05107000188729a40007b759a3a01400000011fd00006e7000000000000000b04f3d20084bd7225ffd00000001356a9159a56f2ab15525a2d46ad833407daf2579d9dd4395648437933e5045370dec583449d9729e0a55b844b90ff6221000231d04be0c9a0bea9d1f685e79135e77000000073668cd0000000000000000007fd0955792569469a0d0400001149a3971800024f8000000000090f8d515b3400069c4ee1193461d7fc5cdf0bb6749a0559b7551a61533f61758f258bf7634e4a69a5efa2df46c151053898ee59f11e09b6727547f74d041b927e5f4d5158fd1a9940008655f9541e574578c40c55e0526a90f50cf23396615b45c157875b7698e528d94640000001555000000000026d154d400000a842f0ded86192b400092e6a09a08e67f40f50354ef818906be0891e0435d093487711d4acd3fae42d3b043ed05563394c5876dad55785244da41947a4bd25449e5a5d6bd11f152d52846c496ef45758d065dd265c93106de7cdb1e5f0f8b8400097c559a739e70d9bc50a185046fd045470543c400000000006f1420132646d95aa5cfd33b46550001d2d513400092c4000000081d00000001e6853d000000025dc00000007b1000000005769ad0000000000103100006310002b450001b53000083a81540008a0672d046800091e62e50000db24eb4759a205cad213a875352400000025890c969315a6420dad940008fe66513b240000000edf0001c3d79766259244f7165850a772543a12974fdf71240007734a0d004e48d65e634d1d88dada0e4361742d5c275b6b954e3568934f453595f4bb574d5f416ed67198f84d9570d5fc3384439e4ef4d995d944c5a1b490a6a969cda3541a5078e49546ee065754469973263211e7dfdea6c5ba17005cc129644252bd5b3172f82717ebc9858eb839a5af63753626449916675e0214d114538fd56bd43150cd40004e74000000000097480000000000a6240007c760819d558b54f3400000028e976450255ffc86943a5ca596b4000447dcd79335c33415d6870000d863d764e600025e179e47b65ef66a557ba6e10000bc14156a1b03f400058b80004544000886930d00e5bd947f9799000043945e5ea1066a677485800000001c50428e2317863776b45895ac361b963c5c1354b5c2130e5d0900000000002b1d571400080e40000145b8d0000000ab450fd000000020d8000219400066d4055163da9da8c4000a475e1597240000000000825685568048fd000071a6e45d820014de182c4000000276952c54a53c049b50c3400025fc0000d7c00000009a599f40000000000a1a46fa218414d98a5eaf75f64259d8a80d37bc5a56d04821077e6a718b66913df681b4a74639290cc0d1b5485d00017024fe40007ad400013e5f0d60a5509000000056d592b9b357a5000000052254a18a140003f86bd5000187f000019d28f502163961b193d554da6967510c389210f35db954a47d5b1f50c500018d5236450b4ea595db034000737400000000005cb66a194981f1323412187641cf9535bcf096ceb90eb514577254ad53f5cedaa054d5000000064f68417a46a855b641a947e6c813975675457609fa8085219a252910000a6500023457cc6299442ea0d63865290fcd10500000000bed71e42e542164e42e19a4c03684a689f7604431a87cfab06540cd8e15b59000000097053791a24f2550f40000a266f99e1825187b403a2776097228810593451f12cd62bda02dbc70a29a5d040400000026870000a990002a8935b400000014e200000001e7482933952490c2a6010cf4b255a568a580a9b3300008892fd40000000000099638d632400000022fd5799a6b3d78775000000017d5cd11c859bf96c5325744c4856516219319400000029faaf150716444000000000097ec00083a4000656cce9b174c439f95431b0c5c31a245225000000000000008626b058534a1794389ad23958dd37c464b6c6d1ee9e78acf0864000000042d94c40000001a210e2607100000004936a4d6fc5485a786415000000042f634b02a41dd2a453b158c5d5d154c29148768291365cb103786490001e95766ce950000ee9720c0000002a111a8e9514c9a7bd3185c390000000188400080d400006c5d2f39c99356f7c0000f54e514944f120000ac549854454ab408f9b6598d864569137ca5bd0002439000039d000000000006f16205b990002b6900000008c640000844ab342349956c942d10dc632556f4d71636cca91075caf6d761ab61ce7765374c3a24aa3dd0f8c4996b35bcd9585bdb2fb430120c582d8aa5268531400054f40000e4512200021223bf5d5a9524a21325561d93645ba1e541f6a574b8542758251496be556a54092aac0db0f7541d9874bd18614b214915b293fcd10d1184fd978043a29ccd3297984f190000000000174317f68615e540009ae63b201964696b7dcc335a4a3b30759051e35d9d45a465f13a40b93894c7d1dda36500017e9662e3b544553750000000000048b3164000000000097e4f494d3621160f41d156e90959c8423b1afa77a3155fa10d2634f3e14ba93c54ae176989755598cf510fe1791eb4be58b648a15f053d54394b29469504113b48793b96ae1b0b66e92fdab15366838e603d5f11b340b54778ab5ad4621e64fc90d8016c3904266854bc92550001a17000008d00025f72124bd700023610644a8d6c64e3900006aa0ab63d559f50392baa809855639d9bf64e1143d53136e5d8632e541a73bd45500004fd00007f536fc1f5000222e2c56069454c0b168f495e44743e1651db6da1240004da4969000000000006413ff51bd6c1ec7157783750e04ca19c54e8547266f5922400000000008d74143000021d0000be16d6c0298fd4b8d8f225de4fc455d00000000000fb96bb69d9105400000001063ed40003ac4000a88523591d40000000eba3e843a669e509900010197b84f221fb40000000000002d429a0c5191642652d15440d176f63b16bf4000438c1b30000c920000000377400051a52390001c6565d400006b52a60000000000125d0000000000000000000007c59e872a24000000000065b400000011f374a919d3e740009f140005e198a17dc8d0b00004910000ea60001ae98df6245000285d00026b5000000000018b919c4b0d15c607500000000000000000246d68d527576c44364d5511b0ad56556b2e41d15a514109d4c79887551d9a8d1e9a2363d16ec555d53b5d3f5cdcd5d4074765a2543190db516d3e6401f86b4aa5700c14f2f78e7960065a99a28000000000096bc00000f53654b251be245c00000025552208e6588e675900029615234de94426369123692d5d2a4654b447f108e60f10a353d914ad01372064ed7dddf35165675a643cfc5424517b67860a17945abd4ed6523a505dc120b5bdd2e741bd43de9dd0d8eadd39144ad3516b8100069d27a0df9a32458da284e7725804000000068100004431dc4000762c60991542469e6694d000226eaf840003b648350000000000000000012a1af360075bb8000942400000024e941dde053a961b584c4dd901752291d855fd687e15d83b5c935c7609d67159dd461595e623dffb3cd5f49afc5a892ff5d71a0950a518ee1ddb1b4c2eb044cc137e50b15ee49898b049657648b5d1d461a56f451a951f489990d4000000000094e5c6d000229d00000009d1400014c40004ff9ff35d74c095f35349255c0da65540002dc51eda05ec591755506897400024f40003734000366c8f50001a4500013371c440007a040005d440000001f3d2b44000000000072ac0000000000a1c4b890ba604d16363c5480a079352e9f617acd8500000000da6b891014081920454520244326696ba13f5d8159e5905f6c0d60908b41293ad514d9e85a2f7a1680182e5a6e2f4d265a1165211f35d313648c7556c66df36d49cdac950cd22f4a1631340000001f210000000af668ad4cc5f590726957527400000008815ad400015b40003b2864512044519db455f0fe4a3528a5d25000000094680002f6c00052e454b4f26761000000049a44b526359a91f947a10001a1baab402e00004017cb5fcdadc40005bf40000000000a0b5fff6f251e641948c11cb45a87c45c591d98aad0cb931f063d3ca85241221de5ebd07ca1df37b4cd942149ed10a5cfb434c9f368391cbae940211a3a85928141352819a4977646e10000091786ac65672e5b28a24bad0000b7917c4cbd5df4e590605849282400000027d54d64b2d98367a95ec4e619368915a2bd8c194481c100020d5446400088340d31064b550b75f7589f5eed2be4c35211a4c948063958a4536d8f04d311f7e457910878671869c9532586b0c4c24796d5d0d7f564d515541491a9903fa64687d28999c996e4161340453900006f50ca62596f2c00059356ea444d0d921345e95484c810445afb1b744a52d440318acc2fd25edc4500000005718c4100007575fe48b261bc35b119d73900000005dc5cf383f5be12d0c58114058e9926e8853b34000000000048545a13564d2905b591da6349c58094dbd77a473949e638173e5241287431e9a762010000000000000000000003a7517d7105f3a00003a911f40000000a550000511402444540540f22244175000009d92967412bf5a0d75a4ec50001dd10000c8e000000000017b50001fdd5ab4000000000000000000000000000159e1eb9bb900008b9000000002b400000000002f74949588556500000007f6c0e262f151195ac0009c040000000000478529924c800078b4c8996762e900018050a9a6b187a42860002535000296d8dc8000000092d47d63ed5944a71351e7c907f659500027b116e6c056f8e53d41666a96c7cf4d73c669f52646252c25b955c24000000211e46c9fd17ef4ff5678ea298044756650c3db8db44c28ab99a12b54062689968667f46f98d55885291478951c49d147554f183943c57a74bbda4e4e4d1ae52fd0001049273cb6163b6bada7f52a920643b303a860d9f869ceaed65a6a2f66318fc64517c05a2d572666521642852254c3d00002f500000000000ccd96140000002a2504de3e920140006a4630978361f1000000054e40006c2c31b00008d179080002178855a1e49df4ad55992f15fe9a9e5a257f94331a6e68c1280432d4fa513b3694959abd4e558105bfd7525af12b9598598640003c9c0002925481ad764f100016b962f4000a26400000022b5383576d5edd10171e400000006c55e840d253bc0000000000125c000000000099540004484e0a000216d46e4f9700012a5a6d400034740000000000000000051b8000793458a000269b77c44719b041cd08860f9220e8d737d660760dc7bd1d050812a541e500002e74fea54300000001c25ef360583b58b15b55872494179ca50a0a85ba769862a5a4148fa4634177926451d2ee592d8e850f97c656e5ade6a751c2ac2124e96130614bd5293475e5514a7937265054744885a954ad35a9c2695505e452dcc0006a051cdaec6bf500003b14bb4dc174441cb3d66a694c65b4978840af7df48011cc4fc173fc7022bc424115068f549fdb09583d9561eaa42e71c40007a24e6900000007c8d983334635173140000001c2969354e98ef4ebd3634e410001d335d382bd99be979566c0006235ee949ea56953ac4c917e67f10d3605daae5ac103042091c7485110d64415126b293f9e5753315af912a9fa96045ccd1a557d14cd41d79a36bfd0001d9500025469e9400000016d5635e97100000000000000000000000000000000000000245a32d4fed6e16abd91c40001f0400015240000001841a685075799418d52f94362b651a2070c9050b365998e946ed3a6400054369350000c369dc56290001bbb51e61e5202912e0ac6a5d1384c9d55c410d6524fb13eec97d6df400000025cd26c633149b40000002241a8b52cd1fa9c4305f46a51f8400095767f5000000058e93e5a655e8e6e05d417a35ef52dd408758f42451b7c000005483b59646e90002b6d6135549982c2a54ff5e71000038d0002b3587442f997d63fd67a44d1029605b99852dd7fd44dd000171200027312e2e0153f8e811aaa46199e042958ca9451119483901e5ab94845d071a595b965044f1a8d5023045aae901b660945c551595e8d9d8735fed3a04db1726dd9e0001e254b656856c7506934e40000000e490000a8b12a4a250002739123c0000002a057bc40003816a4513059cd684cbb100004490000ce30fbc6a200000006d1c6150002ab50000000000084197940000399cb76fdc0000ef48fe00000003325d3917709664585e11a80459718a677902f4d8a85f4d7d519660559768b108fc692a3c675d6d16502649643144b633d9af585961e52da554467d734d7067e1431d2c6568d66f5af37ab4d756856a8d1285ae12e9400026bc9a1000086f08c40009ee42430001d750e0c65d5f540000000a9b8b25a8dacf5d4d094db7b03d4c195d34b45ae768330106acd7614f458de5ea516f45b19b542290b6a8893c86929abf62355a849e948f95e576eda3310f434f4c551d90bc5c0f63d6b7d000157928b51ad8fbd2c12475b573a8d3018704b3d1424d05335450543853c56d8c955a7965810000000ab6660344455f9075692500016c500018cb9e39a6d067a6695414000a404000350ab090c5c00057a800021c46e30000000000114a05058b30001c51608417e9e7619996940001ad8000a145f25b06415100000004c880003afc0008b54ae90000000000173d69ec0000001569a7d48923c240001bcc00021e800000000000000000511800046c545966e4f91084d3610002559000000000000000001467b154000000283d439d1cf0001ba987145b50001309174589d74f637f77948e6000057900002235f8cd41000000022740009a54cc742b63d91c364051cc8a811c940005f85d6600000d51a8400048b40003e3d4cd6334f799444cb100020599ca59d558b61a999e43095cec0008cb63a9a395aad455667b4df46b58fdc88e0f9528530c53816bfc5c9000125900001ba00022255655c991734bd94698cef88b59ad40b6a958445f3990869d172a6af98ef970a0fa54e61da4f8da6a43550001a852bdc00039d41532374d2e3864f8913d5e273cb63e51e640003f340ed1ac459955280006666c3d0002789a2755e98185149000000078a5f9963640dd1e482bf77b587189965159a5c000000000000000003b44000000066190cc000000023d00011e584e4202000000000018b10002b3988a9991a135cd5000167970b400016d800024240000224add9d340005e44d19a3b45d987542990001b6124b8a8721b507f6c8400007a40000002a616ac40000000000682400092d4000809e0191dfa8dd3384ac928651355765725000df1bad65d0588f429d6b75b2d2315f693806699026a359a07ce35285596975151897f86969000000051840001f380006c353955f25e6d5d654e1
  | 5, 1 => 0x391ec4d7b7a9ae779e04b11d819ca525b346faa6452b5dda870e6b6ed8d4000032d001d5b5521d04c5000384c6729240e965e90036939725000001f571584007940005400000364e61a000812fe7d817b97e45be847edd60f0a679003b1214006c43a575b9146e100209001457440d476250000000169c2c4b018db6f701f86ddbe4b90f58d6a4093e785537ad19ca90290144fe68369df763d7f7e988761f080000001f65a300000003bd000000034900229bf733b4400001170a9e1ed7e54b581000d30d599f041f374eb829a1b15552f46bba449434036d4413263f05b4d83b8dfc6d34264f0b7d5ab800cd515254c1e971d9b5513c76500000a66199564188b3ddc5677d40000000000001649100025000007a80000135156d95f546976b5b940087651237ed00331d64000023398b510019d8dc0527611c16ad5cdd90000000000736611a68551c46c262df24a1c5669355c1f16af344e11d46aac71959632e7755df4614f4638557500000565f15b6c10dd0f2d69500395934000000004c4500000001c91e61e00000d74ff615410003122400264008c40000000b247108c0033c00000000018919400b3f45806651b591000003d4fdf180000216f4791f3721db6a500000000003340022e71000ede66f5af4006568dbc7111740000149ce6754a63bc3519e24ea3657944400bf82f0005738dc5a44e90001a074a5694bb8e6dba268104505086f3
  | 6, 0 => 0xd78154f17b5f0001a7aad6c76dd64000bfa7a0cfac001179248a5c400000000041840006e3c52bcc5bb40000005336bea64b73e82f54432d6327c57c42b5ab310ac346e2859098bc34a450ea8b5bbf5e3f47605a80002ba00000040e550a91f2408000000425942bfe4000e7785ce0044d2000a448144001781414902400000000061140001570001c3d923649aecc8c5512139630c5463ae00013cb454f8a47a816d9e48cf289c6edcc49ab5618dcac8a82a6e17ab25e6e0f3a9222de555220000001aad8bc00043dc9855cd05d38cdf56b4288579291963f27378ec84055fa9994bbbb35a5a00098caefa74e433a70c99e44229fae68000684b59a9ebf44fab57500041243ca1f9524d8340000000000000000c7619680000014ad0005295d82a760a39ee85a408900010d608ad9dc48dd463bf6de9bc80024ec2f20000002326d0d1cc8000000f111141574d0b1cdaaadb4c000000b0aa4e6f5200047d800082a13d1bd00000007b5702825c5469058f1dc14b932e5a4e866a6b57ad03349e8fba9619aecf653bae79420aa793227590000000bcb6058c2d9a0062000ab4aa080014633c7d9ad72b64d52cbf56efa0001f5a21c000e3546acd66d72d85471b8b963c701344df853431719eed676e4a9657d6d99cd8acea38a88994e43f179c800124600074cdaa40000000004fe70b20000001ccc75200004a8ec94fce2d8c482e555a45332ac43c9620000000000000afe68092f425d0d1960b2d6cbc2a5666e2064ca129235e234d3b161698a5d80000000002554c8e000000114496a00000055258a51553bf87669ba4c944dd7a18aacc9158d65683a00023495f800062500008258f525123b005ca8d4e5c648fa4aa30870002c46dc20008ce8000000000316800000000079eb794deb2b112ac454000000000000171b46d338800307234d00000000002a900012bc0001b58c6b8c8a5e0001d7000000000000000006974a9346af1a77919150a9445e6a36fa50be14216cc69df8b5878b06b9e88c06476f515f6b50653b225be8c97ed1e517a069db40007a700003b47166750b880000232a729cc69ebfa1699dd9d748fa0a5812d71400000004fd5045832498b6cfbc0c2ef70005264d328156d1024861e00050c96d6bf24d15d73358000000564db946c49b100051c4000000b334d06f3a49a880cf0adb4502b1a9555ffac99484b9a93aab21bbcba7595333da868001b53719396a99664a00000000000017160005065f1365b359984400123f7069415c7400096a80014f20ff0004234fdb24dbd2e386d1aeed0000002622e19456d454000f21284dc7661b66d25cc46c000c0d00056151b333232680000000007da8000000b6a000000000000031d94fded648a269334400126d0003044001505688bfc4bfa4a50e4e1842a2cf5bd086764267710cc37a5c4cd615712da641e73f0cdddb587347d0853f14c7ad190000000000000c828a14000d720005154000df91b31e74c6200000000027131c5905e074000c510c591040000008cb8000000acd7a6a929304000748bf359d2fcb8aea6b4f92abd75943f40016460004a86f1a0006348001c160004f7aa945c2b5e2909e4ce529e19e79cf4ab3599615360925f27548ee0357c479bbe2cee98da375144856e8cf66907d4015c92347042c205cab4ff30d896487a5611091bb578b7d97b9a04409f1f2560a114e1a9b5025c4154dd43171e91bc0003314f9800000127911e80000007790002ada76330a000000000000075d00000007fb2f49b7c000000c7c992408e6e522c9b6dfec0009a50000b72d451aead0400086167700000014e95828002ab2aa91cb58f529e000a9880028f200000039668a38ad36ba8dddd73a53e0c3ea6a35e4a10ab66ba213591aca54c3f7f553d29ed7aa8552075f95e931457afb7644e32ca05d15071d2f160bc80000000000004cd9542ef1b6884561ee0009f09af400000000050f6cfb66247cd40939e0c216d80000000000003906f7acf9000000000155100000000000000005f26afabba6c6a325c54dc590cdb04ec2d2926cc47800066f62142666dcbbd0d4946cfd60e343ab5555726a79dec974000c35a088c851c2be68ffb304326c790004ae80000000000000000000000065c00138d28cb3b59c4709179acc52429c17efc5a70520008318000000bd9b9c8001892251ac487b05b265d0003c16df4000000089c53ac2e5430001fbc6fb2788c4f15209302147c4c731f618e9a05a7534d837b4280eeaf9074800098a36d8219c743d77b1b58a30e9a60126d32cd6e9284f89de0f40e6fdd1b590e4c2a1321948c440ab7016e688d645a1bd026c74c00000000002f800000000000022b600097c80000000000000f4c67a84b973016806f8bd00000000000001468cae7d29a504ec9a678c2a11b0a31c0006dd9ed00008aa3b614ad7c43e26697e380025d4000000000191225d3659ad5372222051aa349ac15554b4336c7c000c5a8002096000000290c000000906bc240520004a6be04000c45a208891dc2f2200000000011ad4d4a1fc000000b6e8a45d550e90000036252229aa6acaa06b1db4288e463922f5789bfd5476f2629a8b36f32299226a029612f662baa1e6c4ad9a000075400000000000000000006030c240000007cc800020e6050002c2cb4a00000012d8000c591334084001211996e2c432d9095d0cebe07b41f71892846920134a2a8f9bbcf1a040bee6cb21434e9b62692a8bd6b88002c536cf4168e763320000002ee670c57977294cde3cb0a87ab886d34faf227998711204900000024021b10b2c4c697b031796e34400000020ce2743d5713c3ac6963ea00000001ba67e000322800288a0002f0a8b57246d9a1e16aa022000093ce8c162df11d8dca40000a134ab8086156577e4b39400000027d9259dec389033d42400000000012640000000002ce54d30f6734bd9400000026e97b5f534d5612a266d0cd65000000000007d00000000002c644b800092a0005748ff430ed918a92a756a200000000029a2000357b0754836f988b98dc00000000000bb062000000000210a000000000287551901ed7780016f13e8a7f4000a112ca8fecf22b85856a17ed12a290169b344c2915c28ac66d3b02a460cee5fef8f1af6c485ca4199294be747aaa351b4cf34e7635537fa244000000b229b05a3a74fb8a84193b2769b1880000001090001c440017fd07282b617e0006f09614000fa511025d5cea0007388086d030dd3a5e1766e2376c26c2d60d36821f09e85d5cb0656e84145cb6a1683089710afbe1c0a566a5a26d9a4a33485b103758aea9c1356d4face5690b09310680000013cbb32cd869222b200037fa0a30b15ce9d44000be5000000003e9c981700c9d5b0ee8a180011bebfd71c800000056da32800000000000052e70e20795d88879042eef700b5790d6b45178800080e0007b384355038057ec800172d139000275dd92f6d0004c5939a2e274d112c00000099c80000000006c08246122cbd0000000000000000000000057d0003565b2a40656d0000000449780a49cf1b5d3b5b32c5cc218130eb856fd286d620c7f4b7b5011c38ba69b36090a0c6548e27bd80d5b0816c00052681a400000000000000002ed00053f450200086c4ab4de22458e0cb180bb8f52d71369f42a390a7cb244fc4ffadcb94712add200043cc00099e0000001e8a00067880000000000968000b6083916b80000011e52334b14e853fd39a8aeedda000000000284600083eb6fa9e2c314418d1575a0004cfc20c13647e845a9b6234b46966d09c39a4a9218b92d50e2b7358c474e720001f283440000f6000000000173586b000253c00080f441d1520003b3858400000001acfe8fc326b9b28384000d490004466d221891f7b6f4a3f75d0000000001525276c1059a4549000126c00000051980013da9c50003ad80006c98449c163aa00003ab77475a3670b853c8a3a00000012add1ad02000000000000019f25f541b0f200000009128d14a580000000000000002b4a7fd1278ee40000007d8d316012ebdb00a0c56ba000000460466e00000051ad5060004a894544d4c09206bbce7da00000036d4000000000131800000082680000000000001cc40008f724e800070b5da0004e0680b1491ee971713216e1656334a0c92b00000000015b50002894e4a4863df0c640000009048e49cda0000ca8000000ab500056f41324f95b2923e482000000000031f36d4e8a0f529362b25680000000002d09df52033213a6dba44460000003b740012f18d0d1d41f253d246cad800000078380000014c95c4adf46e4b7687c8000cda89f63291a80012a935497566125c18fdce29ef2103092d3d47427f51fb0b753473f3032a66969295fa0335f9d736b5426ac9a5b56c93f2caf55da2d34f5add5a6a0006fa88b674297300000006658210003b14b1b6a50000001b74000562dbf71b29037ca90a408b06d120beae2cac7d88686e459c7cd596900cbcd079870a19db3201d0000003013529401bc751168c5652931c58b6d500002a400124536aabc4e8a0000000002bcabf10001e7d27a0fdc5cb3d980a755b42b4c80000004c7000076a3c9a1c44083da062a00c9c5702f7d0acd0ee89a00045cce762fa00078780017fd46f17ca065984000726d484f7203398e8002e34a468a68003203015057cda80014374f8800000000044a800218f6f574f000000000043480009fa00015e983400000036380000000000004ae40000000a532540007afaeeb00a4720000003d549c2fb71b52cad0ca000a1f20365b200006693a62168a511c80021560000000000000ba92afba98c52312000264a08f42b5e880015350a9332ca0a032000a86000000000000000000000000002374232000499b426ecab1d7428934aca6794d10000b3309d8eecfd500e9113d8a4c6b1b70d861aa540009727f080002748fd87887a2c727ad00007a4000741c7ea8c45aa21f27bd5c59fc0008778844b1309700031880e200000011ce6033555ccb7567cf177bb889e9652dfdb3880250125450f38ce9b5cf29002a49499b2a2a5aa915b849699d6d886db200000011868acea200000000000001108ab4bf2e450004074000a8ea768645add4f69c28000a5ab4d0778b240005dd30b8159db327d00000000010a100060954035c1549000000111132080000007210005944000fe541a818c0000008830000000000662b1d6ff200000000022ea01b272a7a4000f150e0d0da75784994080016c55450000000a4a0002013d85e2466b7ddccc400144b00000000009f9000000000030d00058640000000005975da477532c8000f122a73b2a699092b017d3d9d5e32000102920a85a0d95039fa6c230d43008001c4b27e0000db91130d70004366ed2000000000000089d000082000000075280000016e410c958d9cd69500000005725d1b8f0000000ab24d9434eb220006db3a5547a4de2d7ced636af69b5194ecf4668700033640017f1b9044fe37a000000415528287d00023fc000000000509400173d0000000000000000176400000084787f58520001cf0000000000000000000000000000000000000001ab40000000f309f400000000000027aa4977b7b6e51eb6e20000001c220f2091ba262b230598ab5e64b2d7d0d2800306a92900000000000000003485d42f03000000000048500010842d8000a1c8001cf600000005be98217d6ba8000ca63a5872a6157d279577dc1665fc6a1c3ca7967831e71a8dd5400016ba7db27614ac196569e04b235af9a280016c20007d1800083a81d0000000255299b5eadc82a6b79311b68666aaf50003fcc000000000000148e0000000bf4b9e411b88d98438b1e100000000000006f68000000d4d236ce4400003e7a10b44000000732800080ae29902d3e589ab71692bb447a38c50000000f320000000000000749568800000164a446a9d68523d947883d6b02bc157d07d71cb0e219c900537acd5952ab94e5f72164694346fa0ab0004f0030b0d2b7f5109f220006388002d9acdd27a8001d6ab5567d2f2b21ac3d7a9102c43abcd0001fe65a2000000000228285d1f147440000000005a6661c2492e68d040017cd155c0068ba881132d7294841e300037240000003b1afe40009fb0000000d4a00000000001babc90004d78000000892d9563d20000000104000000c6a80000000000005904c3366c0001e94000000b778000000052ab2800000104f7deb3c89831b13ffd9086f2b3d16f0e2a0ca000368b8d80017b90000001b6200085e800121a0009e28002bc3459a58cdf595467d4c30002b5adad00048a51ca3cd29898d6fda4793b93dd42d55e976a80024c66fd77a8ef647a501860b41584334e09f82c8032825395e304222c5d52886fae8b12d1188e4dfd200000059a956291995add3500a54d2658003032162000000000000045880018acad28d483057c2e3e4ae82340010d54d740361fcea91f1c3b53121469219eac56b312982832429268b0001f1c000db25811c2c62abdd56ad444d237913c28fc9b3c65119acb86346d1aaae982618ae817e1b70648eec79f28514f8600067e8002f6a3ed0000054000fb39c7451c0000000000a7990a3339e4b055eb37c12cebbca0e3789c50c3aeaf237397ac4d49c58119b4d7387f2edf0d0d4e47821ad90e800000113d82707fafba2cf50e8002d5a00000000000734616d515a63da06d0e8852d684c2d00035a612a000c0a8001aba000a4080000010c900050d4001841504c5ce212000000512533b40a99480022df86517300002daf63c36800172200000058b40000002d48000000000c2aa65412ca7d1ffa18e77c0000000000bfc000aebac940000000001d190e239a83ab87418a8010000002a3a000000000000039722e8d64beb28db849be54e20017dfcba464a5ad99d800000148d0000166b63535a2380e9ee2d3600000000000000000002eeae5d1ca91d65da3d7aeaa14dba22ae670bf0404a0001fa94d9575291ad48001ada00047480007ce00088f9ba400000000000000000000002975b4b69e4c6afd4b032177c6bb8cd734690ce00000000001412b784022f7b3bb4e59720f1ba087740d4877ae4878540a11d3f8a4d4ef6ee909b4b770faf5d090b83cf5372d52aa2861cc0a7476b206dc05f15dadae82eb6c59baab86dc67ef06a89894c230e7b926067328b525d140c0000007e3000125a00000029fc65e0eb0000000000fed77cadb8000000b6f800031a365bb0cbf6e3f86990a8000000c460a68000000000000013ac3b78500025b471b3f101b1f6705aba5073b006226a995b68f98b6200013a8b6a4aa493029b545c0d02958a95c59436d6000000000140954f8000000000
  | 6, 1 => 0x439000624002b2e5534ddaa65d4b334000000012473080016dab524ddd20b7144ed8d6ba64d5703790af3878ee16f29c656800c62f287c800e6c000b2800a33af4a0a7d383154000007120000018b0f312e09800000001c700000000048bc1c122c54a8d963adf40043ec9a0031e9f70010a72e8004aa4f7a69e5000002ce94f372ec720d41ae2af62c9019eaeaa73e293dc00000239334000000001421279f000c5a83586b214b2599a28a56e338c0882531a7f68580b1ca1d5f4cc1a3abcdd0db99db9e16e8bf70a37c1794952f4f87f6c230b627659eda5bbe40050d5e2146d89b507400000627000000e5000000000004d197291d04ecd2e20662f000000001a480000000336bada9b9ff1e2415db5759c9ea86cdb708ae1213c36a350e55a35582c17703075a6d7dd0b3c53bc0d06bbc5e893154d8743eca1822f5521c5d9bf2f54c9d280a73836f4925a52c573bd062000003a68e3d04001a10011855b9e94beed82c90d16170546c7966a449f281a4223f7829d550b4cf88d3d00038ce2f45001d5607af5a12817a719d84b00554c07e5c8f54ddf917aa94538d136c0000000013200000351d02bf4cd8003dee650fc8953b09aa881ee7202509c0987aa1cb0a5d39a00000000001c788ca913a2e3416da7a4e8840003984367c9cedb2f77a702e6556b6b6deb110000034cc6d000a2670800acaff796a7f6aa0014fc81752d88000009b2001bd42a0008d492d452bb75577a3f526b4618b9d56364690d79b337ee43dc93c3b559b649e1235f54e4509a75931bc95160000020700000038847a234e646a156fd114d126ae45b3e648000001778a80000100eace95603b067ca452fbc86e697565ae56b4c8b0ca00399a617f2a84d4eb911a20683c7f02af657f80012ea075880da0a14d17867384002daf1d00110430d2900114400062000002b08000d39d00000000007400183000014936d904482f7b761be236df0f263028756a8ce75e001c8e7d1e73f63ed8559ae2d270c5dfa4542b3526322b5933ed9ca5e6d29aa7e39f0eccd662a34ef2f35a5fc95e695658ad6624e19d1abe72bb65cd25b447a33aab9647aa69b529d583dfd64a8a69ad75a4b95400121c86000002c32d2f168f80032bcf40014d0142ab8cd8192a9ef62800ca4002ecdedab6000d2c9dc9cf76f5f31bc2da864bcf000000006ed4352a71c80092e8c5d2ae500000000000000002ca80017313768800a2a334f880068200310800bcfd44001dec1c00000000dca0020de0d001807b28000fe007ab0000000000008a85cdd41d80083200350ae7000000000f607d8940043ad12ccb1abff86a698ab87b3f20020abf35b3a44e4806a029379488918c000000000000005a8864e6002958e1001194393cb252000000000002152da2dcea0021682123a9b50c96b000f1c000004ce0006e9b157200077800ade00179679dbb24e988001832c6e72c1beec2652aa20b6774dec75067c047d029abd5b4cc80f4a22be34b69d92788d69f0986a3d3ce71ebbba79906b000ee59e9f53f600100cb55d25666e85528a001988000000000000000000000000000e6e6a80000000000111d3a000005f51d2003acdd16c22570ada1a9210525c9998a003638003224d6749550000f40000000000054aeb7ea114a8ef5766e0912ac9885da4769ae1d7ad594e51
  | 7, 0 => 0x5486f286aad2b4176ccc1200b898532d99e8f4000000001f32d8ae44c91a00124016100002fa4761944ba3b0003cfa0649d57027110016929b00068628594a343c006ab595ef6cce255a3f2bce98a118c9384375808c8d0ce88cd4004d5c8a46a660000000c67518a1e00a2bf5c2dd000000059bce570a1b93aa67f25488b68c698f0d96359004fa54f1652963a0b65a9a5d694edb69a2a3caea966360800018d9dc2662c2408008200004151253a889636e9b2af4eaee63c8e6e1f4fb9400454bad43a0d668099ebe17326720036800000000000000000001ea003380242006880072652aa8400000047c32d2aea88000000000004a0e000030b
  | 7, 1 => 0x13b001a1476536fddd54ce51e800a969e8440000000aa40033c00188009963c16a3971d41195cd1b8be000003996900000694002e529854008759b5ddd58161e000001aa293ba210025100000000009c4015cda00000000000000662580002c007d400000000000067c00001c35bc356c6758345f649e545d8735c1c924d57f5c9078c500000000a15f58d0024500000001d10340000000015831ec091f4f1056a10012138821960e9ab431674866f4611446d87df96145d405153265744e5c2048f904ed91a32435ee4ce6d5d8000025b8063d784db9a41955d6a585b7954d92fccd564c14d800001c84aa9600079871b51047194945246b25458b426795c48d4dc99488f56a4c24c4dd0458129445a25d90024d00000001e97040000259000d18d40006a311a400000006b400000000003b0012f5956672a99276171f92649400575c50027d86a192a40006c000fc00000006700067a0946400080296e54907e8300261018735eded5b400000955ea954b4cb03d951fe2d0b4430969a47c598943d0e51b3f4d62f59195989a34777193512463ab962214476ecf931c02a144d224ea4f43a27cad2c57f5d59a6669d30cb5a44550745e86eb1975f1416b688082249cc4e94d3795a9695523a545e6812687528eb534d5e4e493000e172d11
  | 8, 0 => 0xfa5109000d
  | 8, 1 => 0x257c001d8002536558c6a4190d00000a3d188001e161
  | _, _ => 0

def hitWidth : Nat → Nat → Nat
  | 4, 0 => 12
  | 4, 1 => 8
  | 5, 0 => 14
  | 5, 1 => 10
  | 6, 0 => 13
  | 6, 1 => 11
  | 7, 0 => 9
  | 7, 1 => 10
  | 8, 0 => 4
  | 8, 1 => 6
  | _, _ => 0

def hitCount : Nat → Nat → Nat
  | 4, 0 => 1297
  | 4, 1 => 71
  | 5, 0 => 4759
  | 5, 1 => 419
  | 6, 0 => 3251
  | 6, 1 => 877
  | 7, 0 => 223
  | 7, 1 => 383
  | 8, 0 => 11
  | 8, 1 => 29
  | _, _ => 0

def jumpSlots : Nat → Nat → Nat
  | 4, 0 => 0x20800000020010000000401061020000001800000000c00000002800020050050050000000001010000832800800110080000070000000000000400401000420000402870400000c008410408400300000404000000000014a0040040460410023820004c00420000400000000020440060020010000000410420000000021ea0840c01410480421000000020461400402000010c000000416c0800000000c02800400030810000004912400000800000400801400c10000800020070c0141044041001542000004d001402c01000a82c900000000c0c51490400400010020040820000800030010000c00c000004b01000314008058000000300100100c0820010c50400400000430010020000033002800001c00000000430080400460010c300018608100a0000801000050010000c00020010000402821c104108000100100700414000700000100004004300000300300204004000008000500120a0400000800000000405440003451c100000034e1000010000420000020000400040011040000000000000c01000c40000000060000801c000000c0800460030c00011070820800010800020130030000032400010001890430400000000800010000000040000020010081100000000c00020400400050230000000000018c10005800840060010070021004000011524440050c000200e0800030000000005c00400050010413400410000031c32430000400400410001030400031000000050000020020000100000020010055801c10000010804010400cc0c10050403401430800000100000010c20020c00c200b100000000146105002080000040
  | 4, 1 => 0x40201019045ad0000000000000050
  | 5, 0 => 0x1a34000004004f04000000004300108a0000000461c60020c02090c000100000010a0020800000015c008528300408500000000000000200d0001801c000000c14600d04014418004100101d0400c00800000000800045401000030c43800020001800c000000104f0010810400040003400001402c04401806400000000000860010801000011000000800010400010410800090003000c00000400000040031850000000001400090000000460030010010c004a1000010401810010000c00020800400002401000000004420001830000000000044000820001830000000001c00000000000000020000012400000000020000000400000000810000000800c100004114b00200010000818000128704200008000208010000024008800740a1c00410001010410410400000800000000800010001c10020000800140c008000a0000130c000000d0830001000c00c70410000000000000c224014110004614c1410400410c20004410000050400000000000c004400008304000008000000100000000400a08a0000000090010000400003423080405800411000022c00000000010000410c000301e1c000300200138000c00100004100004100000000000500010000d00000008000200400008a00114004534001b0840010100030400000000010050070800010400000000930c00000420021c000001b00100a0c001e0400440410000000000000440c00040c00040400010c004a0000400420002402800000000180001800800400400c40c00c40040001c00400000000c00000801001440130000000002040800001400001010060003420001000019d00400070400cc0016401c0000d8004305a0422820000010c80020006010000820840000420400021400424000400000020440140010060000800802001c0002142041000001001100b420350000000050010401800020000120040030000000000000030000807c00820000000410000800801850000040000021636833410c31400800010000150800404c20030014810001850030040801031001423c00800406c00001c30c30000000000800010000020003800442011c005a00c0003000410000000430040060000010620043811410010000070062000400010143000410177000000000c00c108000014000100000208300004008000a00014100000800000004010c0850020081830460000010000000000830060190400000000000040000010400000110000c02800000c008000c0000000800000c00000060c03000c30000c00000431960800003000400000000800000000000071800000000003400403070050030000000280010c100700100000b00000000a0402400011c01010040430000800c414000000200c1d200000000000405000000018100024310000000300008000b0000000420800000020000000070420022804000020401420000030030000010000000090011830000020000023c210204000000000000000d00a1000001470000000000000000001000011c00001410000030010830120400c00c000208a08000000308201300b04504000004008010200300004118030a0012804000000010002800001000000000830000c000000000000060900e40e0010000000010802000841000001400000000000090000021c500000000008200024220a0000003400041070891800840c064100000000000000b20000600008b00124004104100b0021cb1400050004410000010060c00042403c20021d70020c00840c00000000800000000420000000000400800000010010151000020000400c01410430002000001400400010430400000010040000440000401c104000300700000f0000000010000040000820401400000000000000c10000000000093c034000008014904000000000000030904a00500000204010004c0020000400010030001860003c00020000040c61000c01400010400c60c300100a00224000400000000000200f0021cf0410580003430000000000010900000001000070002c000000100038000000104d04d04200114008100a1400002000411010410020800000040800100400020000000000001c02c10001c00140470000070400000000400000002400420000074440020012830000002c02400000050000000000010450820000000400400000002c000024100000000b0400000411c00400021000412c00000400001031801c00003800c00c00890400040001000000000010400000080c028130018b00100024100000228000000400004000000100000c0000c01000001801000111000822400000c00030000010400000400160c00000000800000400004c00000000000800030030001410120800400020009500000417401660000000000001890000000400a26450032406c3000000002dc00431400080010000c2080001c004820402000003c00023000010002001141400007c404674000100208000104a9c00400c000b03300000e04004200404304200500b0000800000022c07c10000000040000004400000010010000c10070420000423800c00020410020000c21000480050000650010060020010400420013430c00230070000000c00030400800c00020000000c200010a00020000000c0c104204000010105300400001a0011400000c500000000018100000200008004100000000001300c1400050000090010860002000c00400000020001400000030045c200208000500300004000000000100008109500010020000500014200004014d0000000020c62050800000420001400402c10400030000080000000060020001010020420430000810c4281340040040000001000048002a4100004610100308205008004a2c00000000000020001051485c00010830c01cb0c000104008100208c00008000004000b0830000400000020000000000040000402901480400021000400000830010000030000000000001000400001000000050400400000002400020800030000800850000030000010000000010000802402000050800003400000020010011c10c00c03c004700100008000004104401d1c00001c9000
  | 5, 1 => 0x422004000080018000208030000100409000220040001d4000000080021000100c00001c20740010000005201000c0800b0a040000200012000040100402844008c65010001000108001084200042200042000410006400000008e010c030500800000018e008426280600000020007000000000e280000842000020064001800018001fc4800001d108201082008082000012000000000084000000010000
  | 6, 0 => 0x80000450000430030004c00000000011c500404700000f00004500000000100200000d0020060040000010c00400000001400430010c10000400020031400820000000c100700200000008000210000504000000a0410010000400c30000400000030000000400010000000020020001000401000000450400400000010003400000850c304100008a0800000030000480460020020001c20000000000002000000400410000400000020000000870060020081420020090000400000800040000010030000060004800400000050800010000032400000050800030890000050000000000000000000400410000030060000000000010c02800000020802811c31041000010003c20410000050000000000800001c10021000840001050402c00c00400810051000000010000070000810060c00002800010000400400080041400000000001800040410c00002000020000800400060000060000040000010000410c10c100008c0410820417000820000400000000080020002050002c60031002410c00020000410870400090000000030001002000000000411400050000002805050000000000020000040010010000000000030c10010410c000d0400220000060000810000004000010004c00040020010800430020011400400c20400800c10000001000000801000000000003800401400010000010064800120000010000000410450010000050030440010c00009000000010000470c00800010400026000010020400000010000000000000800080480010000010ca00108200000000400c0000001410000000801000000c000000400000000004300510004030000a0000000000c000110000000218100004000000000004e0400000044810090810802400000030010000000080000001802820800020420403800400422800410000000000000010000000400001440002000000000000020000400000000000020400400000010040020001000000000040000050031804400012400820400000000010000400000000000440000041051c00000814800021810002810430020030080000450c00821880800000400800000840000030440020000000c00000c004000420004300000100010000200000c04000a0001400010820010090020040030020000000030c00821000801800010000001050000400010400020c00000000000c01cb0010400420000000c228001004000900008200100d0830800491470000090000001c00c00030000010030000050400040c20c00810050400000000000000000001800030400400401830000810021000003c00061000000000470000800000400020010000030800401004000480005432c00400810050830000060020010010800000030400430001800803400000004c00810000000000000000c40c00010000050041000051c00000000000020400420010060030000000000400400000006410000000400000000000020070800000400010000020010430480000000030000050004841004413c00c00010410010840410c40000052800410000400802c00000000840a20010000410400420000c60028c200064100b0830010800400001001c03c004000000000000200000438000005604100008e2400000c2040940000003b800001020000070200000010c00000030000000090800000400400403401800001400001800400000000400000800000c00000000001000000000404010820c00811cc00008a0400400070c40c104000000000100100101a00004e1004410000400410400040004012c000000000000100000000008004018010004000d0401000400000445000020400810c00040801840800000020072030430800000030000001000000040800010050000000420000010000c11401810800022c10002460000000000000012c00800c0002001000000040041000
  | 6, 1 => 0x1400000010440020c00000030000410030400021430010400031c200000c0010020000030820000000400400070460000000080030000002000000090404000082000c04800001c108000200104000a0401001900011800120c00003c000000004c0c00000000803433410000000431c000201e00000002700304a0420001000000000c00030020000921010011c200001800000a0020831c10010010000030080140000070022000000863400080050000420400001071421002401800000000030000000cb0010090400010011001801400c00040003000010050000001820000020000840400001c00000010020400c00010000810020000400430000070030022420000062450000000002011c100808000000008014008400000904000600100004000514208300010004a24a0000200000011800c014004500500008000010a0010c18c00840810000071c01020000012820800070010000400c00030000050430400000430000000401801c40480800800030010001400050000403400000001c0001015000540001000085000000081001004
  | 7, 0 => 0x103080100010003d2202722115020050130e1700050001005000430010020506017030001084140101020050204510223000010023130001002c3110021000010200090
  | 7, 1 => 0x18008000700200000f0000020050030000000832160000020010000001810260400050a00000000800010000130420480040000c10000080410000800000010400040001810000010000807000850071c130a0020420df0000c008058700000600000000200000000010400000004308030034d1000000001410000010000010001c000001c01700003d00100100104600204180000018501600004d0800000012000820c2000040000000000044080000000
  | 8, 0 => 0x0
  | 8, 1 => 0x200000204000
  | _, _ => 0

def jumpWidth : Nat → Nat → Nat
  | 4, 0 => 6
  | 4, 1 => 3
  | 5, 0 => 6
  | 5, 1 => 5
  | 6, 0 => 6
  | 6, 1 => 6
  | 7, 0 => 4
  | 7, 1 => 6
  | 8, 0 => 1
  | 8, 1 => 3
  | _, _ => 0

def jumpCount : Nat → Nat → Nat
  | 4, 0 => 808
  | 4, 1 => 39
  | 5, 0 => 2969
  | 5, 1 => 257
  | 6, 0 => 1879
  | 6, 1 => 542
  | 7, 0 => 136
  | 7, 1 => 238
  | 8, 0 => 6
  | 8, 1 => 18
  | _, _ => 0

def repCode (k t i : Nat) : Nat := takeField (repPaths k t) (repWidth k t) i

def orbitHit (k t : Nat) (w : List Sig) : Bool :=
  let h := stateHash w
  let b := h % jumpCount k t
  let idx := (h / jumpCount k t + takeField (jumpSlots k t) (jumpWidth k t) b) % hitCount k t
  let val := takeField (hitSlots k t) (hitWidth k t) idx
  let rid := (val - 1) / 4
  let g := (val - 1) % 4
  val != 0 && decide (rid < repCount k t) &&
    w.isPerm (runPath (orbitInput g) (9 - k) (repCode k t rid))

def orbitEntry (k t i : Nat) : Bool :=
  let v := runPath hardFixedInputs (9 - k) (repCode k t i)
  if k ≤ 4 then !search k t v
  else !oneRound (k - 1) t v (fun t' w => !orbitHit (k - 1) t' w)

lemma orbitHit_sound (k t : Nat) (hneg : ∀ i < repCount k t,
    search k t (runPath hardFixedInputs (9 - k) (repCode k t i)) = false) {w : List Sig}
    (ok : orbitHit k t w = true) : search k t w = false := by
  let h := stateHash w
  let bucket := h % jumpCount k t
  let idx := (h / jumpCount k t + takeField (jumpSlots k t) (jumpWidth k t) bucket) % hitCount k t
  let val := takeField (hitSlots k t) (hitWidth k t) idx
  let rid := (val - 1) / 4
  let g := (val - 1) % 4
  change (val != 0 && decide (rid < repCount k t) && w.isPerm (runPath (orbitInput g) (9 - k) (repCode k t rid))) = true at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at ok
  rw [search_perm k t ok.2, runPath_orbit_search]
  exact hneg rid ok.1.2

lemma orbitTable_sound (hcheck : ∀ k t i, i < repCount k t → orbitEntry k t i = true)
    (k t i : Nat) (hi : i < repCount k t) :
    search k t (runPath hardFixedInputs (9 - k) (repCode k t i)) = false := by
  induction k generalizing t i with
  | zero =>
    have hc := hcheck 0 t i hi
    simpa only [orbitEntry, Nat.zero_le, ite_true, Bool.not_eq_true'] using hc
  | succ k ih =>
    have hc := hcheck (k + 1) t i hi
    by_cases hsmall : k + 1 ≤ 4
    · simpa only [orbitEntry, ite_eq_left hsmall, Bool.not_eq_true'] using hc
    · simp only [orbitEntry, ite_eq_right hsmall, Nat.add_sub_cancel, Bool.not_eq_true'] at hc
      apply negRound k t _ _ _ hc
      intro t' w hw
      cases hm : orbitHit k t' w with
      | false => rfl
      | true =>
        have he := orbitHit_sound k t' (fun j hj => ih t' j hj) hm
        simp [he] at hw

def spanOK (f : Nat → Bool) (a b : Nat) : Prop := ∀ i, a ≤ i → i < b → f i = true

lemma span_decide (f : Nat → Bool) (a b : Nat)
    (hc : (List.range' a (b - a)).all f = true) : spanOK f a b := by
  intro i h1 h2
  apply List.all_eq_true.mp hc i
  exact List.mem_range'_1.mpr ⟨h1, by omega⟩

lemma span_join (f : Nat → Bool) (a m b : Nat) (hl : spanOK f a m)
    (hr : spanOK f m b) : spanOK f a b := by
  intro i h1 h2
  by_cases hm : i < m
  · exact hl i h1 hm
  · exact hr i (by omega) h2

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_0 : (List.range' 0 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_24 : (List.range' 24 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_48 : (List.range' 48 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_72 : (List.range' 72 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_96 : (List.range' 96 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_120 : (List.range' 120 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_144 : (List.range' 144 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_168 : (List.range' 168 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_192 : (List.range' 192 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_216 : (List.range' 216 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_240 : (List.range' 240 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_264 : (List.range' 264 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_288 : (List.range' 288 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_312 : (List.range' 312 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_336 : (List.range' 336 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_360 : (List.range' 360 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_384 : (List.range' 384 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_408 : (List.range' 408 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_432 : (List.range' 432 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_456 : (List.range' 456 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_480 : (List.range' 480 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_504 : (List.range' 504 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_528 : (List.range' 528 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_552 : (List.range' 552 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_576 : (List.range' 576 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_600 : (List.range' 600 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_624 : (List.range' 624 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_648 : (List.range' 648 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_672 : (List.range' 672 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_696 : (List.range' 696 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_720 : (List.range' 720 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_744 : (List.range' 744 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_768 : (List.range' 768 24).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_0_792 : (List.range' 792 8).all (orbitEntry 4 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_1_0 : (List.range' 0 24).all (orbitEntry 4 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_4_1_24 : (List.range' 24 11).all (orbitEntry 4 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_0 : (List.range' 0 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_24 : (List.range' 24 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_48 : (List.range' 48 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_72 : (List.range' 72 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_96 : (List.range' 96 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_120 : (List.range' 120 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_144 : (List.range' 144 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_168 : (List.range' 168 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_192 : (List.range' 192 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_216 : (List.range' 216 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_240 : (List.range' 240 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_264 : (List.range' 264 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_288 : (List.range' 288 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_312 : (List.range' 312 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_336 : (List.range' 336 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_360 : (List.range' 360 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_384 : (List.range' 384 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_408 : (List.range' 408 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_432 : (List.range' 432 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_456 : (List.range' 456 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_480 : (List.range' 480 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_504 : (List.range' 504 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_528 : (List.range' 528 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_552 : (List.range' 552 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_576 : (List.range' 576 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_600 : (List.range' 600 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_624 : (List.range' 624 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_648 : (List.range' 648 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_672 : (List.range' 672 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_696 : (List.range' 696 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_720 : (List.range' 720 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_744 : (List.range' 744 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_768 : (List.range' 768 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_792 : (List.range' 792 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_816 : (List.range' 816 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_840 : (List.range' 840 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_864 : (List.range' 864 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_888 : (List.range' 888 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_912 : (List.range' 912 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_936 : (List.range' 936 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_960 : (List.range' 960 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_984 : (List.range' 984 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1008 : (List.range' 1008 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1032 : (List.range' 1032 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1056 : (List.range' 1056 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1080 : (List.range' 1080 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1104 : (List.range' 1104 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1128 : (List.range' 1128 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1152 : (List.range' 1152 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1176 : (List.range' 1176 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1200 : (List.range' 1200 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1224 : (List.range' 1224 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1248 : (List.range' 1248 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1272 : (List.range' 1272 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1296 : (List.range' 1296 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1320 : (List.range' 1320 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1344 : (List.range' 1344 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1368 : (List.range' 1368 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1392 : (List.range' 1392 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1416 : (List.range' 1416 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1440 : (List.range' 1440 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1464 : (List.range' 1464 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1488 : (List.range' 1488 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1512 : (List.range' 1512 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1536 : (List.range' 1536 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1560 : (List.range' 1560 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1584 : (List.range' 1584 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1608 : (List.range' 1608 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1632 : (List.range' 1632 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1656 : (List.range' 1656 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1680 : (List.range' 1680 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1704 : (List.range' 1704 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1728 : (List.range' 1728 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1752 : (List.range' 1752 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1776 : (List.range' 1776 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1800 : (List.range' 1800 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1824 : (List.range' 1824 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1848 : (List.range' 1848 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1872 : (List.range' 1872 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1896 : (List.range' 1896 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1920 : (List.range' 1920 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1944 : (List.range' 1944 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1968 : (List.range' 1968 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_1992 : (List.range' 1992 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2016 : (List.range' 2016 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2040 : (List.range' 2040 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2064 : (List.range' 2064 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2088 : (List.range' 2088 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2112 : (List.range' 2112 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2136 : (List.range' 2136 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2160 : (List.range' 2160 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2184 : (List.range' 2184 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2208 : (List.range' 2208 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2232 : (List.range' 2232 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2256 : (List.range' 2256 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2280 : (List.range' 2280 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2304 : (List.range' 2304 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2328 : (List.range' 2328 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2352 : (List.range' 2352 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2376 : (List.range' 2376 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2400 : (List.range' 2400 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2424 : (List.range' 2424 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2448 : (List.range' 2448 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2472 : (List.range' 2472 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2496 : (List.range' 2496 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2520 : (List.range' 2520 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2544 : (List.range' 2544 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2568 : (List.range' 2568 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2592 : (List.range' 2592 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2616 : (List.range' 2616 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2640 : (List.range' 2640 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2664 : (List.range' 2664 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2688 : (List.range' 2688 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2712 : (List.range' 2712 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2736 : (List.range' 2736 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2760 : (List.range' 2760 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2784 : (List.range' 2784 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2808 : (List.range' 2808 24).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_0_2832 : (List.range' 2832 18).all (orbitEntry 5 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_0 : (List.range' 0 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_24 : (List.range' 24 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_48 : (List.range' 48 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_72 : (List.range' 72 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_96 : (List.range' 96 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_120 : (List.range' 120 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_144 : (List.range' 144 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_168 : (List.range' 168 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_192 : (List.range' 192 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_216 : (List.range' 216 24).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_5_1_240 : (List.range' 240 13).all (orbitEntry 5 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_0 : (List.range' 0 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_24 : (List.range' 24 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_48 : (List.range' 48 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_72 : (List.range' 72 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_96 : (List.range' 96 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_120 : (List.range' 120 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_144 : (List.range' 144 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_168 : (List.range' 168 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_192 : (List.range' 192 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_216 : (List.range' 216 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_240 : (List.range' 240 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_264 : (List.range' 264 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_288 : (List.range' 288 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_312 : (List.range' 312 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_336 : (List.range' 336 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_360 : (List.range' 360 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_384 : (List.range' 384 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_408 : (List.range' 408 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_432 : (List.range' 432 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_456 : (List.range' 456 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_480 : (List.range' 480 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_504 : (List.range' 504 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_528 : (List.range' 528 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_552 : (List.range' 552 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_576 : (List.range' 576 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_600 : (List.range' 600 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_624 : (List.range' 624 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_648 : (List.range' 648 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_672 : (List.range' 672 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_696 : (List.range' 696 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_720 : (List.range' 720 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_744 : (List.range' 744 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_768 : (List.range' 768 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_792 : (List.range' 792 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_816 : (List.range' 816 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_840 : (List.range' 840 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_864 : (List.range' 864 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_888 : (List.range' 888 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_912 : (List.range' 912 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_936 : (List.range' 936 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_960 : (List.range' 960 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_984 : (List.range' 984 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1008 : (List.range' 1008 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1032 : (List.range' 1032 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1056 : (List.range' 1056 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1080 : (List.range' 1080 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1104 : (List.range' 1104 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1128 : (List.range' 1128 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1152 : (List.range' 1152 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1176 : (List.range' 1176 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1200 : (List.range' 1200 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1224 : (List.range' 1224 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1248 : (List.range' 1248 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1272 : (List.range' 1272 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1296 : (List.range' 1296 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1320 : (List.range' 1320 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1344 : (List.range' 1344 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1368 : (List.range' 1368 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1392 : (List.range' 1392 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1416 : (List.range' 1416 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1440 : (List.range' 1440 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1464 : (List.range' 1464 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1488 : (List.range' 1488 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1512 : (List.range' 1512 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1536 : (List.range' 1536 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1560 : (List.range' 1560 24).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_0_1584 : (List.range' 1584 20).all (orbitEntry 6 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_0 : (List.range' 0 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_24 : (List.range' 24 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_48 : (List.range' 48 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_72 : (List.range' 72 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_96 : (List.range' 96 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_120 : (List.range' 120 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_144 : (List.range' 144 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_168 : (List.range' 168 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_192 : (List.range' 192 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_216 : (List.range' 216 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_240 : (List.range' 240 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_264 : (List.range' 264 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_288 : (List.range' 288 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_312 : (List.range' 312 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_336 : (List.range' 336 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_360 : (List.range' 360 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_384 : (List.range' 384 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_408 : (List.range' 408 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_432 : (List.range' 432 24).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_6_1_456 : (List.range' 456 19).all (orbitEntry 6 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_0_0 : (List.range' 0 24).all (orbitEntry 7 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_0_24 : (List.range' 24 24).all (orbitEntry 7 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_0_48 : (List.range' 48 24).all (orbitEntry 7 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_0_72 : (List.range' 72 24).all (orbitEntry 7 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_0_96 : (List.range' 96 7).all (orbitEntry 7 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_0 : (List.range' 0 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_24 : (List.range' 24 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_48 : (List.range' 48 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_72 : (List.range' 72 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_96 : (List.range' 96 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_120 : (List.range' 120 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_144 : (List.range' 144 24).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_7_1_168 : (List.range' 168 6).all (orbitEntry 7 1) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_8_0_0 : (List.range' 0 4).all (orbitEntry 8 0) = true := by decide +kernel

set_option maxRecDepth 25000 in
lemma checkedOrbit_8_1_0 : (List.range' 0 11).all (orbitEntry 8 1) = true := by decide +kernel

lemma layerOrbit_4_0 : spanOK (orbitEntry 4 0) 0 800 :=
  (span_join _ 0 768 800 (span_join _ 0 384 768 (span_join _ 0 192 384 (span_join _ 0 96 192 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_4_0_0) (span_decide _ 24 48 checkedOrbit_4_0_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_4_0_48) (span_decide _ 72 96 checkedOrbit_4_0_72))) (span_join _ 96 144 192 (span_join _ 96 120 144 (span_decide _ 96 120 checkedOrbit_4_0_96) (span_decide _ 120 144 checkedOrbit_4_0_120)) (span_join _ 144 168 192 (span_decide _ 144 168 checkedOrbit_4_0_144) (span_decide _ 168 192 checkedOrbit_4_0_168)))) (span_join _ 192 288 384 (span_join _ 192 240 288 (span_join _ 192 216 240 (span_decide _ 192 216 checkedOrbit_4_0_192) (span_decide _ 216 240 checkedOrbit_4_0_216)) (span_join _ 240 264 288 (span_decide _ 240 264 checkedOrbit_4_0_240) (span_decide _ 264 288 checkedOrbit_4_0_264))) (span_join _ 288 336 384 (span_join _ 288 312 336 (span_decide _ 288 312 checkedOrbit_4_0_288) (span_decide _ 312 336 checkedOrbit_4_0_312)) (span_join _ 336 360 384 (span_decide _ 336 360 checkedOrbit_4_0_336) (span_decide _ 360 384 checkedOrbit_4_0_360))))) (span_join _ 384 576 768 (span_join _ 384 480 576 (span_join _ 384 432 480 (span_join _ 384 408 432 (span_decide _ 384 408 checkedOrbit_4_0_384) (span_decide _ 408 432 checkedOrbit_4_0_408)) (span_join _ 432 456 480 (span_decide _ 432 456 checkedOrbit_4_0_432) (span_decide _ 456 480 checkedOrbit_4_0_456))) (span_join _ 480 528 576 (span_join _ 480 504 528 (span_decide _ 480 504 checkedOrbit_4_0_480) (span_decide _ 504 528 checkedOrbit_4_0_504)) (span_join _ 528 552 576 (span_decide _ 528 552 checkedOrbit_4_0_528) (span_decide _ 552 576 checkedOrbit_4_0_552)))) (span_join _ 576 672 768 (span_join _ 576 624 672 (span_join _ 576 600 624 (span_decide _ 576 600 checkedOrbit_4_0_576) (span_decide _ 600 624 checkedOrbit_4_0_600)) (span_join _ 624 648 672 (span_decide _ 624 648 checkedOrbit_4_0_624) (span_decide _ 648 672 checkedOrbit_4_0_648))) (span_join _ 672 720 768 (span_join _ 672 696 720 (span_decide _ 672 696 checkedOrbit_4_0_672) (span_decide _ 696 720 checkedOrbit_4_0_696)) (span_join _ 720 744 768 (span_decide _ 720 744 checkedOrbit_4_0_720) (span_decide _ 744 768 checkedOrbit_4_0_744)))))) (span_join _ 768 792 800 (span_decide _ 768 792 checkedOrbit_4_0_768) (span_decide _ 792 800 checkedOrbit_4_0_792)))

lemma layerOrbit_4_1 : spanOK (orbitEntry 4 1) 0 35 :=
  (span_join _ 0 24 35 (span_decide _ 0 24 checkedOrbit_4_1_0) (span_decide _ 24 35 checkedOrbit_4_1_24))

lemma layerOrbit_5_0 : spanOK (orbitEntry 5 0) 0 2850 :=
  (span_join _ 0 1536 2850 (span_join _ 0 768 1536 (span_join _ 0 384 768 (span_join _ 0 192 384 (span_join _ 0 96 192 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_5_0_0) (span_decide _ 24 48 checkedOrbit_5_0_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_5_0_48) (span_decide _ 72 96 checkedOrbit_5_0_72))) (span_join _ 96 144 192 (span_join _ 96 120 144 (span_decide _ 96 120 checkedOrbit_5_0_96) (span_decide _ 120 144 checkedOrbit_5_0_120)) (span_join _ 144 168 192 (span_decide _ 144 168 checkedOrbit_5_0_144) (span_decide _ 168 192 checkedOrbit_5_0_168)))) (span_join _ 192 288 384 (span_join _ 192 240 288 (span_join _ 192 216 240 (span_decide _ 192 216 checkedOrbit_5_0_192) (span_decide _ 216 240 checkedOrbit_5_0_216)) (span_join _ 240 264 288 (span_decide _ 240 264 checkedOrbit_5_0_240) (span_decide _ 264 288 checkedOrbit_5_0_264))) (span_join _ 288 336 384 (span_join _ 288 312 336 (span_decide _ 288 312 checkedOrbit_5_0_288) (span_decide _ 312 336 checkedOrbit_5_0_312)) (span_join _ 336 360 384 (span_decide _ 336 360 checkedOrbit_5_0_336) (span_decide _ 360 384 checkedOrbit_5_0_360))))) (span_join _ 384 576 768 (span_join _ 384 480 576 (span_join _ 384 432 480 (span_join _ 384 408 432 (span_decide _ 384 408 checkedOrbit_5_0_384) (span_decide _ 408 432 checkedOrbit_5_0_408)) (span_join _ 432 456 480 (span_decide _ 432 456 checkedOrbit_5_0_432) (span_decide _ 456 480 checkedOrbit_5_0_456))) (span_join _ 480 528 576 (span_join _ 480 504 528 (span_decide _ 480 504 checkedOrbit_5_0_480) (span_decide _ 504 528 checkedOrbit_5_0_504)) (span_join _ 528 552 576 (span_decide _ 528 552 checkedOrbit_5_0_528) (span_decide _ 552 576 checkedOrbit_5_0_552)))) (span_join _ 576 672 768 (span_join _ 576 624 672 (span_join _ 576 600 624 (span_decide _ 576 600 checkedOrbit_5_0_576) (span_decide _ 600 624 checkedOrbit_5_0_600)) (span_join _ 624 648 672 (span_decide _ 624 648 checkedOrbit_5_0_624) (span_decide _ 648 672 checkedOrbit_5_0_648))) (span_join _ 672 720 768 (span_join _ 672 696 720 (span_decide _ 672 696 checkedOrbit_5_0_672) (span_decide _ 696 720 checkedOrbit_5_0_696)) (span_join _ 720 744 768 (span_decide _ 720 744 checkedOrbit_5_0_720) (span_decide _ 744 768 checkedOrbit_5_0_744)))))) (span_join _ 768 1152 1536 (span_join _ 768 960 1152 (span_join _ 768 864 960 (span_join _ 768 816 864 (span_join _ 768 792 816 (span_decide _ 768 792 checkedOrbit_5_0_768) (span_decide _ 792 816 checkedOrbit_5_0_792)) (span_join _ 816 840 864 (span_decide _ 816 840 checkedOrbit_5_0_816) (span_decide _ 840 864 checkedOrbit_5_0_840))) (span_join _ 864 912 960 (span_join _ 864 888 912 (span_decide _ 864 888 checkedOrbit_5_0_864) (span_decide _ 888 912 checkedOrbit_5_0_888)) (span_join _ 912 936 960 (span_decide _ 912 936 checkedOrbit_5_0_912) (span_decide _ 936 960 checkedOrbit_5_0_936)))) (span_join _ 960 1056 1152 (span_join _ 960 1008 1056 (span_join _ 960 984 1008 (span_decide _ 960 984 checkedOrbit_5_0_960) (span_decide _ 984 1008 checkedOrbit_5_0_984)) (span_join _ 1008 1032 1056 (span_decide _ 1008 1032 checkedOrbit_5_0_1008) (span_decide _ 1032 1056 checkedOrbit_5_0_1032))) (span_join _ 1056 1104 1152 (span_join _ 1056 1080 1104 (span_decide _ 1056 1080 checkedOrbit_5_0_1056) (span_decide _ 1080 1104 checkedOrbit_5_0_1080)) (span_join _ 1104 1128 1152 (span_decide _ 1104 1128 checkedOrbit_5_0_1104) (span_decide _ 1128 1152 checkedOrbit_5_0_1128))))) (span_join _ 1152 1344 1536 (span_join _ 1152 1248 1344 (span_join _ 1152 1200 1248 (span_join _ 1152 1176 1200 (span_decide _ 1152 1176 checkedOrbit_5_0_1152) (span_decide _ 1176 1200 checkedOrbit_5_0_1176)) (span_join _ 1200 1224 1248 (span_decide _ 1200 1224 checkedOrbit_5_0_1200) (span_decide _ 1224 1248 checkedOrbit_5_0_1224))) (span_join _ 1248 1296 1344 (span_join _ 1248 1272 1296 (span_decide _ 1248 1272 checkedOrbit_5_0_1248) (span_decide _ 1272 1296 checkedOrbit_5_0_1272)) (span_join _ 1296 1320 1344 (span_decide _ 1296 1320 checkedOrbit_5_0_1296) (span_decide _ 1320 1344 checkedOrbit_5_0_1320)))) (span_join _ 1344 1440 1536 (span_join _ 1344 1392 1440 (span_join _ 1344 1368 1392 (span_decide _ 1344 1368 checkedOrbit_5_0_1344) (span_decide _ 1368 1392 checkedOrbit_5_0_1368)) (span_join _ 1392 1416 1440 (span_decide _ 1392 1416 checkedOrbit_5_0_1392) (span_decide _ 1416 1440 checkedOrbit_5_0_1416))) (span_join _ 1440 1488 1536 (span_join _ 1440 1464 1488 (span_decide _ 1440 1464 checkedOrbit_5_0_1440) (span_decide _ 1464 1488 checkedOrbit_5_0_1464)) (span_join _ 1488 1512 1536 (span_decide _ 1488 1512 checkedOrbit_5_0_1488) (span_decide _ 1512 1536 checkedOrbit_5_0_1512))))))) (span_join _ 1536 2304 2850 (span_join _ 1536 1920 2304 (span_join _ 1536 1728 1920 (span_join _ 1536 1632 1728 (span_join _ 1536 1584 1632 (span_join _ 1536 1560 1584 (span_decide _ 1536 1560 checkedOrbit_5_0_1536) (span_decide _ 1560 1584 checkedOrbit_5_0_1560)) (span_join _ 1584 1608 1632 (span_decide _ 1584 1608 checkedOrbit_5_0_1584) (span_decide _ 1608 1632 checkedOrbit_5_0_1608))) (span_join _ 1632 1680 1728 (span_join _ 1632 1656 1680 (span_decide _ 1632 1656 checkedOrbit_5_0_1632) (span_decide _ 1656 1680 checkedOrbit_5_0_1656)) (span_join _ 1680 1704 1728 (span_decide _ 1680 1704 checkedOrbit_5_0_1680) (span_decide _ 1704 1728 checkedOrbit_5_0_1704)))) (span_join _ 1728 1824 1920 (span_join _ 1728 1776 1824 (span_join _ 1728 1752 1776 (span_decide _ 1728 1752 checkedOrbit_5_0_1728) (span_decide _ 1752 1776 checkedOrbit_5_0_1752)) (span_join _ 1776 1800 1824 (span_decide _ 1776 1800 checkedOrbit_5_0_1776) (span_decide _ 1800 1824 checkedOrbit_5_0_1800))) (span_join _ 1824 1872 1920 (span_join _ 1824 1848 1872 (span_decide _ 1824 1848 checkedOrbit_5_0_1824) (span_decide _ 1848 1872 checkedOrbit_5_0_1848)) (span_join _ 1872 1896 1920 (span_decide _ 1872 1896 checkedOrbit_5_0_1872) (span_decide _ 1896 1920 checkedOrbit_5_0_1896))))) (span_join _ 1920 2112 2304 (span_join _ 1920 2016 2112 (span_join _ 1920 1968 2016 (span_join _ 1920 1944 1968 (span_decide _ 1920 1944 checkedOrbit_5_0_1920) (span_decide _ 1944 1968 checkedOrbit_5_0_1944)) (span_join _ 1968 1992 2016 (span_decide _ 1968 1992 checkedOrbit_5_0_1968) (span_decide _ 1992 2016 checkedOrbit_5_0_1992))) (span_join _ 2016 2064 2112 (span_join _ 2016 2040 2064 (span_decide _ 2016 2040 checkedOrbit_5_0_2016) (span_decide _ 2040 2064 checkedOrbit_5_0_2040)) (span_join _ 2064 2088 2112 (span_decide _ 2064 2088 checkedOrbit_5_0_2064) (span_decide _ 2088 2112 checkedOrbit_5_0_2088)))) (span_join _ 2112 2208 2304 (span_join _ 2112 2160 2208 (span_join _ 2112 2136 2160 (span_decide _ 2112 2136 checkedOrbit_5_0_2112) (span_decide _ 2136 2160 checkedOrbit_5_0_2136)) (span_join _ 2160 2184 2208 (span_decide _ 2160 2184 checkedOrbit_5_0_2160) (span_decide _ 2184 2208 checkedOrbit_5_0_2184))) (span_join _ 2208 2256 2304 (span_join _ 2208 2232 2256 (span_decide _ 2208 2232 checkedOrbit_5_0_2208) (span_decide _ 2232 2256 checkedOrbit_5_0_2232)) (span_join _ 2256 2280 2304 (span_decide _ 2256 2280 checkedOrbit_5_0_2256) (span_decide _ 2280 2304 checkedOrbit_5_0_2280)))))) (span_join _ 2304 2688 2850 (span_join _ 2304 2496 2688 (span_join _ 2304 2400 2496 (span_join _ 2304 2352 2400 (span_join _ 2304 2328 2352 (span_decide _ 2304 2328 checkedOrbit_5_0_2304) (span_decide _ 2328 2352 checkedOrbit_5_0_2328)) (span_join _ 2352 2376 2400 (span_decide _ 2352 2376 checkedOrbit_5_0_2352) (span_decide _ 2376 2400 checkedOrbit_5_0_2376))) (span_join _ 2400 2448 2496 (span_join _ 2400 2424 2448 (span_decide _ 2400 2424 checkedOrbit_5_0_2400) (span_decide _ 2424 2448 checkedOrbit_5_0_2424)) (span_join _ 2448 2472 2496 (span_decide _ 2448 2472 checkedOrbit_5_0_2448) (span_decide _ 2472 2496 checkedOrbit_5_0_2472)))) (span_join _ 2496 2592 2688 (span_join _ 2496 2544 2592 (span_join _ 2496 2520 2544 (span_decide _ 2496 2520 checkedOrbit_5_0_2496) (span_decide _ 2520 2544 checkedOrbit_5_0_2520)) (span_join _ 2544 2568 2592 (span_decide _ 2544 2568 checkedOrbit_5_0_2544) (span_decide _ 2568 2592 checkedOrbit_5_0_2568))) (span_join _ 2592 2640 2688 (span_join _ 2592 2616 2640 (span_decide _ 2592 2616 checkedOrbit_5_0_2592) (span_decide _ 2616 2640 checkedOrbit_5_0_2616)) (span_join _ 2640 2664 2688 (span_decide _ 2640 2664 checkedOrbit_5_0_2640) (span_decide _ 2664 2688 checkedOrbit_5_0_2664))))) (span_join _ 2688 2784 2850 (span_join _ 2688 2736 2784 (span_join _ 2688 2712 2736 (span_decide _ 2688 2712 checkedOrbit_5_0_2688) (span_decide _ 2712 2736 checkedOrbit_5_0_2712)) (span_join _ 2736 2760 2784 (span_decide _ 2736 2760 checkedOrbit_5_0_2736) (span_decide _ 2760 2784 checkedOrbit_5_0_2760))) (span_join _ 2784 2832 2850 (span_join _ 2784 2808 2832 (span_decide _ 2784 2808 checkedOrbit_5_0_2784) (span_decide _ 2808 2832 checkedOrbit_5_0_2808)) (span_decide _ 2832 2850 checkedOrbit_5_0_2832))))))

lemma layerOrbit_5_1 : spanOK (orbitEntry 5 1) 0 253 :=
  (span_join _ 0 192 253 (span_join _ 0 96 192 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_5_1_0) (span_decide _ 24 48 checkedOrbit_5_1_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_5_1_48) (span_decide _ 72 96 checkedOrbit_5_1_72))) (span_join _ 96 144 192 (span_join _ 96 120 144 (span_decide _ 96 120 checkedOrbit_5_1_96) (span_decide _ 120 144 checkedOrbit_5_1_120)) (span_join _ 144 168 192 (span_decide _ 144 168 checkedOrbit_5_1_144) (span_decide _ 168 192 checkedOrbit_5_1_168)))) (span_join _ 192 240 253 (span_join _ 192 216 240 (span_decide _ 192 216 checkedOrbit_5_1_192) (span_decide _ 216 240 checkedOrbit_5_1_216)) (span_decide _ 240 253 checkedOrbit_5_1_240)))

lemma layerOrbit_6_0 : spanOK (orbitEntry 6 0) 0 1604 :=
  (span_join _ 0 1536 1604 (span_join _ 0 768 1536 (span_join _ 0 384 768 (span_join _ 0 192 384 (span_join _ 0 96 192 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_6_0_0) (span_decide _ 24 48 checkedOrbit_6_0_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_6_0_48) (span_decide _ 72 96 checkedOrbit_6_0_72))) (span_join _ 96 144 192 (span_join _ 96 120 144 (span_decide _ 96 120 checkedOrbit_6_0_96) (span_decide _ 120 144 checkedOrbit_6_0_120)) (span_join _ 144 168 192 (span_decide _ 144 168 checkedOrbit_6_0_144) (span_decide _ 168 192 checkedOrbit_6_0_168)))) (span_join _ 192 288 384 (span_join _ 192 240 288 (span_join _ 192 216 240 (span_decide _ 192 216 checkedOrbit_6_0_192) (span_decide _ 216 240 checkedOrbit_6_0_216)) (span_join _ 240 264 288 (span_decide _ 240 264 checkedOrbit_6_0_240) (span_decide _ 264 288 checkedOrbit_6_0_264))) (span_join _ 288 336 384 (span_join _ 288 312 336 (span_decide _ 288 312 checkedOrbit_6_0_288) (span_decide _ 312 336 checkedOrbit_6_0_312)) (span_join _ 336 360 384 (span_decide _ 336 360 checkedOrbit_6_0_336) (span_decide _ 360 384 checkedOrbit_6_0_360))))) (span_join _ 384 576 768 (span_join _ 384 480 576 (span_join _ 384 432 480 (span_join _ 384 408 432 (span_decide _ 384 408 checkedOrbit_6_0_384) (span_decide _ 408 432 checkedOrbit_6_0_408)) (span_join _ 432 456 480 (span_decide _ 432 456 checkedOrbit_6_0_432) (span_decide _ 456 480 checkedOrbit_6_0_456))) (span_join _ 480 528 576 (span_join _ 480 504 528 (span_decide _ 480 504 checkedOrbit_6_0_480) (span_decide _ 504 528 checkedOrbit_6_0_504)) (span_join _ 528 552 576 (span_decide _ 528 552 checkedOrbit_6_0_528) (span_decide _ 552 576 checkedOrbit_6_0_552)))) (span_join _ 576 672 768 (span_join _ 576 624 672 (span_join _ 576 600 624 (span_decide _ 576 600 checkedOrbit_6_0_576) (span_decide _ 600 624 checkedOrbit_6_0_600)) (span_join _ 624 648 672 (span_decide _ 624 648 checkedOrbit_6_0_624) (span_decide _ 648 672 checkedOrbit_6_0_648))) (span_join _ 672 720 768 (span_join _ 672 696 720 (span_decide _ 672 696 checkedOrbit_6_0_672) (span_decide _ 696 720 checkedOrbit_6_0_696)) (span_join _ 720 744 768 (span_decide _ 720 744 checkedOrbit_6_0_720) (span_decide _ 744 768 checkedOrbit_6_0_744)))))) (span_join _ 768 1152 1536 (span_join _ 768 960 1152 (span_join _ 768 864 960 (span_join _ 768 816 864 (span_join _ 768 792 816 (span_decide _ 768 792 checkedOrbit_6_0_768) (span_decide _ 792 816 checkedOrbit_6_0_792)) (span_join _ 816 840 864 (span_decide _ 816 840 checkedOrbit_6_0_816) (span_decide _ 840 864 checkedOrbit_6_0_840))) (span_join _ 864 912 960 (span_join _ 864 888 912 (span_decide _ 864 888 checkedOrbit_6_0_864) (span_decide _ 888 912 checkedOrbit_6_0_888)) (span_join _ 912 936 960 (span_decide _ 912 936 checkedOrbit_6_0_912) (span_decide _ 936 960 checkedOrbit_6_0_936)))) (span_join _ 960 1056 1152 (span_join _ 960 1008 1056 (span_join _ 960 984 1008 (span_decide _ 960 984 checkedOrbit_6_0_960) (span_decide _ 984 1008 checkedOrbit_6_0_984)) (span_join _ 1008 1032 1056 (span_decide _ 1008 1032 checkedOrbit_6_0_1008) (span_decide _ 1032 1056 checkedOrbit_6_0_1032))) (span_join _ 1056 1104 1152 (span_join _ 1056 1080 1104 (span_decide _ 1056 1080 checkedOrbit_6_0_1056) (span_decide _ 1080 1104 checkedOrbit_6_0_1080)) (span_join _ 1104 1128 1152 (span_decide _ 1104 1128 checkedOrbit_6_0_1104) (span_decide _ 1128 1152 checkedOrbit_6_0_1128))))) (span_join _ 1152 1344 1536 (span_join _ 1152 1248 1344 (span_join _ 1152 1200 1248 (span_join _ 1152 1176 1200 (span_decide _ 1152 1176 checkedOrbit_6_0_1152) (span_decide _ 1176 1200 checkedOrbit_6_0_1176)) (span_join _ 1200 1224 1248 (span_decide _ 1200 1224 checkedOrbit_6_0_1200) (span_decide _ 1224 1248 checkedOrbit_6_0_1224))) (span_join _ 1248 1296 1344 (span_join _ 1248 1272 1296 (span_decide _ 1248 1272 checkedOrbit_6_0_1248) (span_decide _ 1272 1296 checkedOrbit_6_0_1272)) (span_join _ 1296 1320 1344 (span_decide _ 1296 1320 checkedOrbit_6_0_1296) (span_decide _ 1320 1344 checkedOrbit_6_0_1320)))) (span_join _ 1344 1440 1536 (span_join _ 1344 1392 1440 (span_join _ 1344 1368 1392 (span_decide _ 1344 1368 checkedOrbit_6_0_1344) (span_decide _ 1368 1392 checkedOrbit_6_0_1368)) (span_join _ 1392 1416 1440 (span_decide _ 1392 1416 checkedOrbit_6_0_1392) (span_decide _ 1416 1440 checkedOrbit_6_0_1416))) (span_join _ 1440 1488 1536 (span_join _ 1440 1464 1488 (span_decide _ 1440 1464 checkedOrbit_6_0_1440) (span_decide _ 1464 1488 checkedOrbit_6_0_1464)) (span_join _ 1488 1512 1536 (span_decide _ 1488 1512 checkedOrbit_6_0_1488) (span_decide _ 1512 1536 checkedOrbit_6_0_1512))))))) (span_join _ 1536 1584 1604 (span_join _ 1536 1560 1584 (span_decide _ 1536 1560 checkedOrbit_6_0_1536) (span_decide _ 1560 1584 checkedOrbit_6_0_1560)) (span_decide _ 1584 1604 checkedOrbit_6_0_1584)))

lemma layerOrbit_6_1 : spanOK (orbitEntry 6 1) 0 475 :=
  (span_join _ 0 384 475 (span_join _ 0 192 384 (span_join _ 0 96 192 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_6_1_0) (span_decide _ 24 48 checkedOrbit_6_1_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_6_1_48) (span_decide _ 72 96 checkedOrbit_6_1_72))) (span_join _ 96 144 192 (span_join _ 96 120 144 (span_decide _ 96 120 checkedOrbit_6_1_96) (span_decide _ 120 144 checkedOrbit_6_1_120)) (span_join _ 144 168 192 (span_decide _ 144 168 checkedOrbit_6_1_144) (span_decide _ 168 192 checkedOrbit_6_1_168)))) (span_join _ 192 288 384 (span_join _ 192 240 288 (span_join _ 192 216 240 (span_decide _ 192 216 checkedOrbit_6_1_192) (span_decide _ 216 240 checkedOrbit_6_1_216)) (span_join _ 240 264 288 (span_decide _ 240 264 checkedOrbit_6_1_240) (span_decide _ 264 288 checkedOrbit_6_1_264))) (span_join _ 288 336 384 (span_join _ 288 312 336 (span_decide _ 288 312 checkedOrbit_6_1_288) (span_decide _ 312 336 checkedOrbit_6_1_312)) (span_join _ 336 360 384 (span_decide _ 336 360 checkedOrbit_6_1_336) (span_decide _ 360 384 checkedOrbit_6_1_360))))) (span_join _ 384 432 475 (span_join _ 384 408 432 (span_decide _ 384 408 checkedOrbit_6_1_384) (span_decide _ 408 432 checkedOrbit_6_1_408)) (span_join _ 432 456 475 (span_decide _ 432 456 checkedOrbit_6_1_432) (span_decide _ 456 475 checkedOrbit_6_1_456))))

lemma layerOrbit_7_0 : spanOK (orbitEntry 7 0) 0 103 :=
  (span_join _ 0 96 103 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_7_0_0) (span_decide _ 24 48 checkedOrbit_7_0_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_7_0_48) (span_decide _ 72 96 checkedOrbit_7_0_72))) (span_decide _ 96 103 checkedOrbit_7_0_96))

lemma layerOrbit_7_1 : spanOK (orbitEntry 7 1) 0 174 :=
  (span_join _ 0 96 174 (span_join _ 0 48 96 (span_join _ 0 24 48 (span_decide _ 0 24 checkedOrbit_7_1_0) (span_decide _ 24 48 checkedOrbit_7_1_24)) (span_join _ 48 72 96 (span_decide _ 48 72 checkedOrbit_7_1_48) (span_decide _ 72 96 checkedOrbit_7_1_72))) (span_join _ 96 144 174 (span_join _ 96 120 144 (span_decide _ 96 120 checkedOrbit_7_1_96) (span_decide _ 120 144 checkedOrbit_7_1_120)) (span_join _ 144 168 174 (span_decide _ 144 168 checkedOrbit_7_1_144) (span_decide _ 168 174 checkedOrbit_7_1_168))))

lemma layerOrbit_8_0 : spanOK (orbitEntry 8 0) 0 4 :=
  (span_decide _ 0 4 checkedOrbit_8_0_0)

lemma layerOrbit_8_1 : spanOK (orbitEntry 8 1) 0 11 :=
  (span_decide _ 0 11 checkedOrbit_8_1_0)

lemma orbitEntries_checked (k t i : Nat) (hi : i < repCount k t) : orbitEntry k t i = true := by
  have hr : 4 ≤ k ∧ k ≤ 8 ∧ t ≤ 1 := by
    unfold repCount at hi
    split at hi <;> omega
  obtain ⟨hk, hk', ht⟩ := hr
  interval_cases k <;> interval_cases t
  · exact layerOrbit_4_0 i (Nat.zero_le _) hi
  · exact layerOrbit_4_1 i (Nat.zero_le _) hi
  · exact layerOrbit_5_0 i (Nat.zero_le _) hi
  · exact layerOrbit_5_1 i (Nat.zero_le _) hi
  · exact layerOrbit_6_0 i (Nat.zero_le _) hi
  · exact layerOrbit_6_1 i (Nat.zero_le _) hi
  · exact layerOrbit_7_0 i (Nat.zero_le _) hi
  · exact layerOrbit_7_1 i (Nat.zero_le _) hi
  · exact layerOrbit_8_0 i (Nat.zero_le _) hi
  · exact layerOrbit_8_1 i (Nat.zero_le _) hi

lemma certifiedOrbit_hit (k t : Nat) {w : List Sig} (hit : orbitHit k t w = true) : search k t w = false :=
  orbitHit_sound k t (fun i hi => orbitTable_sound orbitEntries_checked k t i hi) hit

set_option maxRecDepth 25000 in
lemma cert_eae8e880_8_0 : search 8 0 v_eae8e880 = false :=
  certifiedOrbit_hit 8 0 (by decide +kernel)

set_option maxRecDepth 25000 in
lemma cert_eae8e880_8_1 : search 8 1 v_eae8e880 = false :=
  certifiedOrbit_hit 8 1 (by decide +kernel)

set_option maxRecDepth 25000 in
lemma cert_eae8e880_9_1 : search 9 1 v_eae8e880 = false := by
  apply negRound 8 1 hardFixedInputs (fun t' w => !orbitHit 8 t' w)
  · intro t' w hw
    cases hm : orbitHit 8 t' w with
    | false => rfl
    | true =>
      have he := certifiedOrbit_hit 8 t' hm
      simp [he] at hw
  · decide +kernel

lemma lower_eae8e800 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeae8e800 (sampleMask x)) :
    8 ≤ C.size := by
  apply sample_lower C v_eae8e800 8 0xeae8e800 hfan hnot hcorrect len_eae8e800 nodup_eae8e800 ess_eae8e800 pos_eae8e800 neg_eae8e800
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eae8e800_4_0
  · exact cert_eae8e800_5_0
  · exact cert_eae8e800_5_1
  · exact cert_eae8e800_6_0
  · exact cert_eae8e800_6_1
  · exact cert_eae8e800_7_1

lemma lower_e8e8e888 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xe8e8e888 (sampleMask x)) :
    6 ≤ C.size := by
  apply sample_lower C v_e8e8e888 6 0xe8e8e888 hfan hnot hcorrect len_e8e8e888 nodup_e8e8e888 ess_e8e8e888 pos_e8e8e888 neg_e8e8e888
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_e8e8e888_4_0
  · exact cert_e8e8e888_5_1

lemma lower_eaa8a8a8 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaa8a8a8 (sampleMask x)) :
    7 ≤ C.size := by
  apply sample_lower C v_eaa8a8a8 7 0xeaa8a8a8 hfan hnot hcorrect len_eaa8a8a8 nodup_eaa8a8a8 ess_eaa8a8a8 pos_eaa8a8a8 neg_eaa8a8a8
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eaa8a8a8_4_0
  · exact cert_eaa8a8a8_5_0
  · exact cert_eaa8a8a8_5_1
  · exact cert_eaa8a8a8_6_1

lemma lower_eaa8e888 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaa8e888 (sampleMask x)) :
    8 ≤ C.size := by
  apply sample_lower C v_eaa8e888 8 0xeaa8e888 hfan hnot hcorrect len_eaa8e888 nodup_eaa8e888 ess_eaa8e888 pos_eaa8e888 neg_eaa8e888
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eaa8e888_4_0
  · exact cert_eaa8e888_5_0
  · exact cert_eaa8e888_5_1
  · exact cert_eaa8e888_6_0
  · exact cert_eaa8e888_6_1
  · exact cert_eaa8e888_7_1

lemma lower_eaaac888 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaaac888 (sampleMask x)) :
    5 ≤ C.size := by
  apply sample_lower C v_eaaac888 5 0xeaaac888 hfan hnot hcorrect len_eaaac888 nodup_eaaac888 ess_eaaac888 pos_eaaac888 neg_eaaac888
  intro k t hk ht hone hs hlive
  omega

lemma lower_eaaae880 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeaaae880 (sampleMask x)) :
    8 ≤ C.size := by
  apply sample_lower C v_eaaae880 8 0xeaaae880 hfan hnot hcorrect len_eaaae880 nodup_eaaae880 ess_eaaae880 pos_eaaae880 neg_eaaae880
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eaaae880_4_0
  · exact cert_eaaae880_5_0
  · exact cert_eaaae880_5_1
  · exact cert_eaaae880_6_0
  · exact cert_eaaae880_6_1
  · exact cert_eaaae880_7_1

lemma lower_eac8e888 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeac8e888 (sampleMask x)) :
    8 ≤ C.size := by
  apply sample_lower C v_eac8e888 8 0xeac8e888 hfan hnot hcorrect len_eac8e888 nodup_eac8e888 ess_eac8e888 pos_eac8e888 neg_eac8e888
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eac8e888_4_0
  · exact cert_eac8e888_5_0
  · exact cert_eac8e888_5_1
  · exact cert_eac8e888_6_0
  · exact cert_eac8e888_6_1
  · exact cert_eac8e888_7_1

lemma lower_eac8e8c0 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeac8e8c0 (sampleMask x)) :
    7 ≤ C.size := by
  apply sample_lower C v_eac8e8c0 7 0xeac8e8c0 hfan hnot hcorrect len_eac8e8c0 nodup_eac8e8c0 ess_eac8e8c0 pos_eac8e8c0 neg_eac8e8c0
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eac8e8c0_4_0
  · exact cert_eac8e8c0_5_0
  · exact cert_eac8e8c0_5_1
  · exact cert_eac8e8c0_6_1

lemma lower_eae8e880 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeae8e880 (sampleMask x)) :
    10 ≤ C.size := by
  apply sample_lower C v_eae8e880 10 0xeae8e880 hfan hnot hcorrect len_eae8e880 nodup_eae8e880 ess_eae8e880 pos_eae8e880 neg_eae8e880
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 0) ∨ (k = 5 ∧ t = 1) ∨ (k = 6 ∧ t = 0) ∨ (k = 6 ∧ t = 1) ∨ (k = 7 ∧ t = 0) ∨ (k = 7 ∧ t = 1) ∨ (k = 8 ∧ t = 0) ∨ (k = 8 ∧ t = 1) ∨ (k = 9 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eae8e880_4_0
  · exact cert_eae8e880_5_0
  · exact cert_eae8e880_5_1
  · exact cert_eae8e880_6_0
  · exact cert_eae8e880_6_1
  · exact cert_eae8e880_7_0
  · exact cert_eae8e880_7_1
  · exact cert_eae8e880_8_0
  · exact cert_eae8e880_8_1
  · exact cert_eae8e880_9_1

lemma lower_eae8ea00 (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : C.gates.countP isNotGate = 1)
    (hcorrect : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeae8ea00 (sampleMask x)) :
    6 ≤ C.size := by
  apply sample_lower C v_eae8ea00 6 0xeae8ea00 hfan hnot hcorrect len_eae8ea00 nodup_eae8ea00 ess_eae8ea00 pos_eae8ea00 neg_eae8ea00
  intro k t hk ht hone hs hlive
  have casesKt : (k = 4 ∧ t = 0) ∨ (k = 5 ∧ t = 1) := by omega
  rcases casesKt with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact cert_eae8ea00_4_0
  · exact cert_eae8ea00_5_1

def monotoneWitness (t k : ℕ) : Prop :=
  ∃ (gates : List Gate) (o : ℕ),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    gates.length ≤ k ∧ ∀ x : Fin 5 → Bool,
      Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
        Nat.testBit t (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

lemma everyRow (P : (Fin 5 → Bool) → Prop)
    (h : ∀ a b c d e : Bool, P ![a, b, c, d, e]) : ∀ x, P x := by
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i
    fin_cases i <;> rfl
  exact hx ▸ h (x 0) (x 1) (x 2) (x 3) (x 4)

lemma upper_eae8e800 : monotoneWitness 0xeae8e800 8 := by
  refine ⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [6, 11]⟩], 12, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_e8e8e888 : monotoneWitness 0xe8e8e888 6 := by
  refine ⟨[⟨.or, [3, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [8, 9]⟩], 10, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eaa8a8a8 : monotoneWitness 0xeaa8a8a8 7 := by
  refine ⟨[⟨.and, [3, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [9, 10]⟩], 11, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eaa8e888 : monotoneWitness 0xeaa8e888 8 := by
  refine ⟨[⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [8, 11]⟩], 12, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eaaac888 : monotoneWitness 0xeaaac888 5 := by
  refine ⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩], 9, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eaaae880 : monotoneWitness 0xeaaae880 8 := by
  refine ⟨[⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [7, 11]⟩], 12, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eac8e888 : monotoneWitness 0xeac8e888 8 := by
  refine ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [8, 11]⟩], 12, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eac8e8c0 : monotoneWitness 0xeac8e8c0 7 := by
  refine ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [9, 10]⟩], 11, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eae8e880 : monotoneWitness 0xeae8e880 10 := by
  refine ⟨[⟨.or, [3, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [12, 13]⟩], 14, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel

lemma upper_eae8ea00 : monotoneWitness 0xeae8ea00 6 := by
  refine ⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [8, 9]⟩], 10, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · apply everyRow
    decide +kernel


lemma solveRow {T bound : ℕ} (upper : monotoneWitness T bound)
    (lower : ∀ (C : Circuit), (∀ g ∈ C.gates,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      C.gates.countP isNotGate = 1 →
      (∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit T (sampleMask x)) →
      bound ≤ C.size)
    (gates : List Gate) (o : ℕ)
    (hf : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit T (sampleMask x)) : monotoneWitness T gates.length := by
  have count := notCount_le_one gates hu
  by_cases hz : gates.countP isNotGate = 0
  · refine ⟨gates, o, ?_, le_rfl, he⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hf g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim ((List.countP_eq_zero.mp hz g hg) ((isNotGate_iff g).mpr h))
  · have hone : gates.countP isNotGate = 1 := by omega
    have fan : ∀ g ∈ gates,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hf
    have enough : bound ≤ gates.length := lower ⟨gates, o⟩ fan hone he
    obtain ⟨gs, out, hfan, hsz, heval⟩ := upper
    exact ⟨gs, out, hfan, hsz.trans enough, heval⟩

end PEqualNP.Outside.L_meta_1427_aux

open PEqualNP.Outside.L_meta_1427_aux

theorem PEqualNP.Outside.L_meta_1427 : ∀ T ∈ ({0xeae8e800, 0xe8e8e888, 0xeaa8a8a8, 0xeaa8e888, 0xeaaac888, 0xeaaae880, 0xeac8e888, 0xeac8e8c0, 0xeae8e880, 0xeae8ea00} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gates o hf hu he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact solveRow upper_eae8e800 lower_eae8e800 gates o hf hu he
  · exact solveRow upper_e8e8e888 lower_e8e8e888 gates o hf hu he
  · exact solveRow upper_eaa8a8a8 lower_eaa8a8a8 gates o hf hu he
  · exact solveRow upper_eaa8e888 lower_eaa8e888 gates o hf hu he
  · exact solveRow upper_eaaac888 lower_eaaac888 gates o hf hu he
  · exact solveRow upper_eaaae880 lower_eaaae880 gates o hf hu he
  · exact solveRow upper_eac8e888 lower_eac8e888 gates o hf hu he
  · exact solveRow upper_eac8e8c0 lower_eac8e8c0 gates o hf hu he
  · exact solveRow upper_eae8e880 lower_eae8e880 gates o hf hu he
  · exact solveRow upper_eae8ea00 lower_eae8ea00 gates o hf hu he
