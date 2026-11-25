import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12408

open PEqualNP.CircuitLowerBounds

lemma length_filter_eq_countP {α : Type*} (p : α → Bool) (l : List α) :
    (l.filter p).length = l.countP p := by
  induction l with
  | nil => simp
  | cons x xs ih => cases h : p x <;> simp [List.filter_cons, List.countP_cons, h, ih]

lemma countP_singleton_bool (p : Nat → Bool) (x : Nat) :
    [x].countP p = if p x then 1 else 0 := by
  rw [List.countP_cons, List.countP_nil]
  simp only [Nat.zero_add]

lemma getD_eq_getElem {α : Type*} (l : List α) (d : α) {i : Nat} (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, hi]

lemma getD_eq_default {α : Type*} (l : List α) (d : α) {i : Nat} (hi : ¬ i < l.length) :
    l.getD i d = d := by
  simp [List.getD, hi]

lemma getD_append_left {α : Type*} (l r : List α) (d : α) {i : Nat} (hi : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  have hi2 : i < (l ++ r).length := Nat.lt_of_lt_of_le hi (by simp)
  rw [getD_eq_getElem (l ++ r) d hi2, getD_eq_getElem l d hi, List.getElem_append_left hi]

lemma getD_append_self {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD]

lemma getD_append_gt {α : Type*} (l : List α) (x d : α) {i : Nat} (hi : l.length + 1 ≤ i) :
    (l ++ [x]).getD i d = d := by
  have h : ¬ i < (l ++ [x]).length := by simp; omega
  exact getD_eq_default (l ++ [x]) d h

lemma getD_mem_of_lt (l : List Nat) {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [getD_eq_getElem l 0 hi]
  exact List.getElem_mem hi

def B : Fin 4 → Nat
  | 0 => 5461
  | 1 => 9830
  | 2 => 14456
  | 3 => 16256

def initMasks : List Nat :=
  List.ofFn (fun q : Fin 14 => 2 ^ q.val)

def evalOrMask (acc : List Nat) (g : Gate) : Nat :=
  match g.inputs with
  | [] => 0
  | [a] => acc.getD a 0
  | a :: b :: _ => (acc.getD a 0) ||| (acc.getD b 0)

def simMasks (acc : List Nat) : List Gate → List Nat
  | [] => acc
  | g :: gs => simMasks (acc ++ [evalOrMask acc g]) gs

def gateMasksFrom (acc : List Nat) : List Gate → List Nat
  | [] => []
  | g :: gs =>
    let v := evalOrMask acc g
    v :: gateMasksFrom (acc ++ [v]) gs

lemma simMasks_eq_append (acc : List Nat) (gs : List Gate) :
    simMasks acc gs = acc ++ gateMasksFrom acc gs := by
  induction gs generalizing acc with
  | nil => simp [simMasks, gateMasksFrom]
  | cons g gs ih =>
    simp only [simMasks, gateMasksFrom, ih, List.append_assoc, List.cons_append, List.nil_append]

lemma gateMasksFrom_length (acc : List Nat) (gs : List Gate) :
    (gateMasksFrom acc gs).length = gs.length := by
  induction gs generalizing acc with
  | nil => simp [gateMasksFrom]
  | cons g gs ih => simp [gateMasksFrom, ih]

lemma getD_lt_of_lt (l : List Nat) (hl : ∀ x ∈ l, x < 16384) (i : Nat) :
    l.getD i 0 < 16384 := by
  by_cases hi : i < l.length
  · rw [getD_eq_getElem l 0 hi]
    exact hl _ (List.getElem_mem hi)
  · rw [getD_eq_default l 0 hi]
    omega

lemma evalOrMask_lt (acc : List Nat) (hl : ∀ x ∈ acc, x < 16384) (g : Gate) :
    evalOrMask acc g < 16384 := by
  rcases g with ⟨op, ins⟩
  rcases ins with _ | ⟨a, _ | ⟨b, _⟩⟩
  · simp [evalOrMask]
  · simp [evalOrMask]
    exact getD_lt_of_lt acc hl a
  · simp [evalOrMask]
    have ha := getD_lt_of_lt acc hl a
    have hb := getD_lt_of_lt acc hl b
    exact Nat.or_lt_two_pow (n := 14) ha hb

lemma simMasks_lt (acc : List Nat) (hl : ∀ x ∈ acc, x < 16384) (gs : List Gate) :
    ∀ x ∈ simMasks acc gs, x < 16384 := by
  induction gs generalizing acc with
  | nil => simpa [simMasks] using hl
  | cons g gs ih =>
    apply ih
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hl x hx
    · exact evalOrMask_lt acc hl g

lemma gateMasksFrom_lt (acc : List Nat) (hl : ∀ x ∈ acc, x < 16384) (gs : List Gate) :
    ∀ x ∈ gateMasksFrom acc gs, x < 16384 := by
  intro x hx
  apply simMasks_lt acc hl gs
  rw [simMasks_eq_append]
  exact List.mem_append_right acc hx

lemma initMasks_lt : ∀ x ∈ initMasks, x < 16384 := by
  intro x hx
  simp only [initMasks, List.mem_ofFn] at hx
  rcases hx with ⟨q, rfl⟩
  have hq : q.val < 14 := q.isLt
  have hpow : 2 ^ q.val < 2 ^ 14 := Nat.pow_lt_pow_right (by omega) hq
  simpa using hpow

lemma B_lt (v : Fin 4) : B v < 16384 := by
  fin_cases v <;> decide

lemma B_testBit (v : Fin 4) (p : Fin 14) :
    (B v).testBit p.val = Nat.testBit (p.val + 1) v.val := by
  revert v p
  decide

lemma simMasks_testBit_step (p : Fin 14) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) :
    ∀ (acc : List Nat) (xs : List Bool),
      acc.length = xs.length →
      (∀ w, (acc.getD w 0).testBit p.val = xs.getD w false) →
      ∀ w, ((simMasks acc gs).getD w 0).testBit p.val =
        (List.foldl (fun ws g => ws ++ [g.op.eval (List.map (fun i => ws.getD i false) g.inputs)]) xs gs).getD w false := by
  induction gs with
  | nil =>
    intro acc xs _ h w
    simpa [simMasks] using h w
  | cons g gs ih =>
    intro acc xs hlen h w
    have hg := hgs g (by simp)
    have hgs' : ∀ g' ∈ gs, g'.op = GateOp.or ∧ g'.inputs.length ≤ 2 := fun g' hg' => hgs g' (by simp [hg'])
    apply ih hgs' (acc ++ [evalOrMask acc g])
      (xs ++ [g.op.eval (List.map (fun i => xs.getD i false) g.inputs)])
    · simp [hlen]
    · intro u
      by_cases hu : u < acc.length
      · have hu' : u < xs.length := hlen ▸ hu
        rw [getD_append_left acc [evalOrMask acc g] 0 hu]
        rw [getD_append_left xs [g.op.eval (List.map (fun i => xs.getD i false) g.inputs)] false hu']
        exact h u
      · by_cases heq : u = acc.length
        · have heq' : u = xs.length := hlen ▸ heq
          rw [heq, getD_append_self acc (evalOrMask acc g) 0]
          rw [← heq, heq', getD_append_self xs _ false]
          rcases hg with ⟨hop, hlen_in⟩
          rcases g with ⟨op, ins⟩
          dsimp at hop hlen_in
          subst hop
          rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
          · simp [evalOrMask, GateOp.eval]
          · simp only [evalOrMask]
            have hev : ∀ x : Bool, GateOp.or.eval [x] = x := by decide
            rw [List.map_cons, List.map_nil, hev, h a]
          · simp only [evalOrMask, Nat.testBit_or]
            have hev : ∀ x y : Bool, GateOp.or.eval [x, y] = (x || y) := by decide
            rw [List.map_cons, List.map_cons, List.map_nil, hev, h a, h b]
          · simp at hlen_in
        · have hgt : acc.length + 1 ≤ u := by omega
          have hgt' : xs.length + 1 ≤ u := by omega
          rw [getD_append_gt acc (evalOrMask acc g) 0 hgt]
          rw [getD_append_gt xs _ false hgt']
          simp

lemma initMasks_testBit (p : Fin 14) (w : Nat) :
    (initMasks.getD w 0).testBit p.val =
      (List.ofFn (fun q : Fin 14 => decide (q = p))).getD w false := by
  by_cases hw : w < 14
  · have hdec : ∀ (p q : Fin 14), ((initMasks.getD q.val 0).testBit p.val ==
        (List.ofFn (fun r : Fin 14 => decide (r = p))).getD q.val false) = true := by decide
    have := hdec p ⟨w, hw⟩
    simpa using this
  · have h1 : ¬ w < initMasks.length := by simp only [initMasks, List.length_ofFn]; exact hw
    have h2 : ¬ w < (List.ofFn (fun q : Fin 14 => decide (q = p))).length := by simp only [List.length_ofFn]; exact hw
    rw [getD_eq_default initMasks 0 h1, getD_eq_default _ false h2]
    simp

lemma simMasks_computes_B (C : Circuit)
    (hor : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (v : Fin 4) (w : ℕ)
    (hw : ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false =
      Nat.testBit (p.val + 1) v.val) :
    (simMasks initMasks C.gates).getD w 0 = B v := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 14
  · let p : Fin 14 := ⟨i, hi⟩
    have hstep := simMasks_testBit_step p C.gates hor initMasks
      (List.ofFn (fun q : Fin 14 => decide (q = p)))
      (by simp [initMasks])
      (initMasks_testBit p)
      w
    have hwire : C.wires (List.ofFn (fun q : Fin 14 => decide (q = p))) =
        List.foldl (fun ws g => ws ++ [g.op.eval (List.map (fun i => ws.getD i false) g.inputs)])
          (List.ofFn (fun q : Fin 14 => decide (q = p))) C.gates := rfl
    rw [hstep, ← hwire, hw p, ← B_testBit v p]
  · have hm : (simMasks initMasks C.gates).getD w 0 < 2 ^ 14 :=
      getD_lt_of_lt _ (simMasks_lt initMasks initMasks_lt C.gates) w
    have hbv : B v < 2 ^ 14 := B_lt v
    have hm2 : (simMasks initMasks C.gates).getD w 0 < 2 ^ i :=
      lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega))
    have hbv2 : B v < 2 ^ i :=
      lt_of_lt_of_le hbv (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hm2, Nat.testBit_lt_two_pow hbv2]

def isSingleton (m : Nat) : Bool :=
  (List.range 14).any (fun i => m == 2 ^ i)

def inTarget (v : Fin 4) (m : Nat) : Bool :=
  (m &&& B v) == m

def targetCount (m : Nat) : Nat :=
  (if inTarget 0 m then 1 else 0) +
  (if inTarget 1 m then 1 else 0) +
  (if inTarget 2 m then 1 else 0) +
  (if inTarget 3 m then 1 else 0)

def famPair : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (1, 2)
  | 4 => (1, 3)
  | 5 => (2, 3)

def famInter (f : Fin 6) : Nat :=
  B (famPair f).1 &&& B (famPair f).2

def inFam (f : Fin 6) (m : Nat) : Bool :=
  (m != 0) && (!isSingleton m) && ((m &&& famInter f) == m)

def isPriv (v : Fin 4) (m : Nat) : Bool :=
  (m != 0) && (!isSingleton m) && inTarget v m && (targetCount m == 1)

def famBits : Fin 6 → Nat × Nat × Nat
  | 0 => (2, 6, 10)
  | 1 => (4, 6, 12)
  | 2 => (8, 10, 12)
  | 3 => (5, 6, 13)
  | 4 => (9, 10, 13)
  | 5 => (11, 12, 13)

def famMask (f : Fin 6) (c : Nat) : Nat :=
  let (a, b, d) := famBits f
  match c with
  | 0 => 0
  | 1 => (1 <<< a) ||| (1 <<< b)
  | 2 => (1 <<< a) ||| (1 <<< d)
  | 3 => (1 <<< b) ||| (1 <<< d)
  | _ => (1 <<< a) ||| (1 <<< b) ||| (1 <<< d)

def cCost (c : Nat) : Nat :=
  if c == 0 then 0 else if c == 4 then 2 else 1

def pop14 (m : Nat) : Nat :=
  (List.range 14).countP (fun i => m.testBit i)

def minCov (t m1 m2 m3 : Nat) : Nat :=
  let p (mask used : Nat) := used + pop14 (t &&& (16383 ^^^ mask))
  Nat.min (p 0 0) <|
  Nat.min (p m1 1) <|
  Nat.min (p m2 1) <|
  Nat.min (p m3 1) <|
  Nat.min (p (m1 ||| m2) 2) <|
  Nat.min (p (m1 ||| m3) 2) <|
  Nat.min (p (m2 ||| m3) 2)
          (p (m1 ||| m2 ||| m3) 3)

def famSubmasks (f : Fin 6) : List Nat :=
  let (a, b, d) := famBits f
  [0, 1 <<< a, 1 <<< b, 1 <<< d,
   (1 <<< a) ||| (1 <<< b), (1 <<< a) ||| (1 <<< d), (1 <<< b) ||| (1 <<< d),
   (1 <<< a) ||| (1 <<< b) ||| (1 <<< d)]

def famHasBit (f : Fin 6) (i : Nat) : Bool :=
  let (a, b, d) := famBits f
  (i == a) || (i == b) || (i == d)

def mkSub (f : Fin 6) (ba bb bd : Bool) : Nat :=
  let (a, b, d) := famBits f
  (if ba then 1 <<< a else 0) ||| (if bb then 1 <<< b else 0) ||| (if bd then 1 <<< d else 0)

lemma famInter_lt (f : Fin 6) : famInter f < 16384 := by
  fin_cases f <;> decide

lemma mkSub_lt (f : Fin 6) (ba bb bd : Bool) : mkSub f ba bb bd < 16384 := by
  revert f ba bb bd
  decide

lemma mkSub_mem_famSubmasks (f : Fin 6) (ba bb bd : Bool) :
    mkSub f ba bb bd ∈ famSubmasks f := by
  revert f ba bb bd
  decide

lemma famInter_testBit_false (f : Fin 6) (i : Nat) (hf : famHasBit f i = false) :
    (famInter f).testBit i = false := by
  by_cases hi : i < 14
  · have hdec : ((List.finRange 6).all fun g => (List.range 14).all fun j =>
        famHasBit g j || !(famInter g).testBit j) = true := by decide
    have hg := List.all_eq_true.mp hdec f (List.mem_finRange f)
    have hj := List.all_eq_true.mp hg i (List.mem_range.mpr hi)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hj
    rcases hj with h | h
    · rw [h] at hf; cases hf
    · exact h
  · have hflt : famInter f < 2 ^ 14 := famInter_lt f
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hflt (Nat.pow_le_pow_right (by omega) (by omega)))

lemma mkSub_testBit_lt14 (f : Fin 6) (ba bb bd : Bool) (i : Nat) (hi : i < 14) :
    (mkSub f ba bb bd).testBit i =
      ((if i == (famBits f).1 then ba else false) ||
       (if i == (famBits f).2.1 then bb else false) ||
       (if i == (famBits f).2.2 then bd else false)) := by
  have hdec : ∀ (g : Fin 6) (a b d : Bool) (j : Fin 14),
      (mkSub g a b d).testBit j.val =
        ((if j.val == (famBits g).1 then a else false) ||
         (if j.val == (famBits g).2.1 then b else false) ||
         (if j.val == (famBits g).2.2 then d else false)) := by
    decide
  exact hdec f ba bb bd ⟨i, hi⟩

lemma famBits_lt14 (f : Fin 6) :
    (famBits f).1 < 14 ∧ (famBits f).2.1 < 14 ∧ (famBits f).2.2 < 14 := by
  fin_cases f <;> decide

lemma mem_famSubmasks_of_le (f : Fin 6) (x : Nat) (hx : x < 16384)
    (h : x &&& famInter f = x) : x ∈ famSubmasks f := by
  let ba := x.testBit (famBits f).1
  let bb := x.testBit (famBits f).2.1
  let bd := x.testBit (famBits f).2.2
  suffices hseq : x = mkSub f ba bb bd by
    rw [hseq]
    exact mkSub_mem_famSubmasks f ba bb bd
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 14
  · rw [mkSub_testBit_lt14 f ba bb bd i hi]
    by_cases hfb : famHasBit f i = true
    · have hbits : (famBits f).1 ≠ (famBits f).2.1 ∧ (famBits f).1 ≠ (famBits f).2.2 ∧
          (famBits f).2.1 ≠ (famBits f).2.2 := by fin_cases f <;> decide
      simp only [famHasBit, Bool.or_eq_true, beq_iff_eq] at hfb
      rcases hfb with (hia | hib) | hid
      · subst hia
        have h12 : ((famBits f).1 == (famBits f).2.1) = false := beq_false_of_ne hbits.1
        have h13 : ((famBits f).1 == (famBits f).2.2) = false := beq_false_of_ne hbits.2.1
        simp [h12, h13, ba]
      · subst hib
        have h21 : ((famBits f).2.1 == (famBits f).1) = false := beq_false_of_ne hbits.1.symm
        have h23 : ((famBits f).2.1 == (famBits f).2.2) = false := beq_false_of_ne hbits.2.2
        simp [h21, h23, bb]
      · subst hid
        have h31 : ((famBits f).2.2 == (famBits f).1) = false := beq_false_of_ne hbits.2.1.symm
        have h32 : ((famBits f).2.2 == (famBits f).2.1) = false := beq_false_of_ne hbits.2.2.symm
        simp [h31, h32, bd]
    · have hfbf : famHasBit f i = false := Bool.eq_false_iff.mpr hfb
      have hsub := congrArg (fun n => n.testBit i) h
      rw [Nat.testBit_and, famInter_testBit_false f i hfbf, Bool.and_false] at hsub
      simp only [famHasBit, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hfbf
      have h1 : (i == (famBits f).1) = false := beq_false_of_ne hfbf.1.1
      have h2 : (i == (famBits f).2.1) = false := beq_false_of_ne hfbf.1.2
      have h3 : (i == (famBits f).2.2) = false := beq_false_of_ne hfbf.2
      simp [← hsub, h1, h2, h3]
  · have hi14 : 14 ≤ i := Nat.le_of_not_lt hi
    have hx2 : x < 2 ^ 14 := by omega
    have hm2 : mkSub f ba bb bd < 2 ^ 14 := by have := mkSub_lt f ba bb bd; omega
    have hxi : x < 2 ^ i := lt_of_lt_of_le hx2 (Nat.pow_le_pow_right (by omega) hi14)
    have hmi : mkSub f ba bb bd < 2 ^ i := lt_of_lt_of_le hm2 (Nat.pow_le_pow_right (by omega) hi14)
    rw [Nat.testBit_lt_two_pow hxi, Nat.testBit_lt_two_pow hmi]

lemma or_eq_famInter_inFam (f : Fin 6) (x y : Nat) (hx : x < 16384) (hy : y < 16384)
    (hxy : x ||| y = famInter f) (hxne : x ≠ famInter f) (hyne : y ≠ famInter f) :
    inFam f x = true ∨ inFam f y = true := by
  have hax : x &&& famInter f = x := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, ← hxy, Nat.testBit_or]
    cases x.testBit i <;> simp
  have hay : y &&& famInter f = y := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, ← hxy, Nat.testBit_or]
    cases y.testBit i <;> simp
  have hmx := mem_famSubmasks_of_le f x hx hax
  have hmy := mem_famSubmasks_of_le f y hy hay
  have hdec : ((List.finRange 6).all fun g =>
      (famSubmasks g).all fun a => (famSubmasks g).all fun b =>
        !((a ||| b == famInter g) && (a != famInter g) && (b != famInter g)) ||
          (inFam g a || inFam g b)) = true := by
    decide
  have hf := List.all_eq_true.mp hdec f (List.mem_finRange f)
  have ha := List.all_eq_true.mp hf x hmx
  have hb := List.all_eq_true.mp ha y hmy
  have hcond : ((x ||| y == famInter f) && (x != famInter f) && (y != famInter f)) = true := by
    simp [hxy, hxne, hyne]
  rw [hcond] at hb
  simpa using hb

lemma initMasks_not_inFam (f : Fin 6) :
    ∀ m ∈ initMasks, inFam f m = false := by
  have h : ∀ (f : Fin 6) (q : Fin 14), inFam f (2 ^ q.val) = false := by decide
  intro m hm
  simp only [initMasks, List.mem_ofFn] at hm
  rcases hm with ⟨q, rfl⟩
  exact h f q

lemma famMask_four_eq_famInter (f : Fin 6) : famMask f 4 = famInter f := by
  fin_cases f <;> decide

lemma famInter_requires_two (f : Fin 6) (acc : List Nat)
    (hl : ∀ x ∈ acc, x < 16384)
    (hno : famInter f ∉ acc)
    (gs : List Gate)
    (hmem : famInter f ∈ gateMasksFrom acc gs) :
    2 ≤ (gateMasksFrom acc gs).countP (inFam f) + acc.countP (inFam f) := by
  induction gs generalizing acc with
  | nil => simp [gateMasksFrom] at hmem
  | cons g gs ih =>
    simp only [gateMasksFrom, List.mem_cons] at hmem
    have hval_lt : evalOrMask acc g < 16384 := evalOrMask_lt acc hl g
    have hnz : ∀ f0 : Fin 6, famInter f0 ≠ 0 := by decide
    have h0_not : ∀ f0 : Fin 6, inFam f0 0 = false := by decide
    by_cases hval : evalOrMask acc g = famInter f
    · have hnon0 : evalOrMask acc g ≠ 0 := by rw [hval]; exact hnz f
      rcases g with ⟨op, ins⟩
      rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · simp [evalOrMask] at hnon0
      · exfalso
        apply hno
        rw [← hval]
        simp only [evalOrMask]
        by_cases ha : a < acc.length
        · exact getD_mem_of_lt acc ha
        · simp only [evalOrMask] at hnon0
          rw [getD_eq_default acc 0 ha] at hnon0
          exact False.elim (hnon0 rfl)
      · have hax : acc.getD a 0 < 16384 := getD_lt_of_lt acc hl a
        have hay : acc.getD b 0 < 16384 := getD_lt_of_lt acc hl b
        have hor : acc.getD a 0 ||| acc.getD b 0 = famInter f := by
          simpa [evalOrMask] using hval
        have hne_a : acc.getD a 0 ≠ famInter f := by
          intro he
          by_cases ha : a < acc.length
          · apply hno; rw [← he]; exact getD_mem_of_lt acc ha
          · rw [getD_eq_default acc 0 ha] at he; exact (hnz f) he.symm
        have hne_b : acc.getD b 0 ≠ famInter f := by
          intro he
          by_cases hb : b < acc.length
          · apply hno; rw [← he]; exact getD_mem_of_lt acc hb
          · rw [getD_eq_default acc 0 hb] at he; exact (hnz f) he.symm
        have hin := or_eq_famInter_inFam f _ _ hax hay hor hne_a hne_b
        have hacc1 : 1 ≤ acc.countP (inFam f) := by
          rcases hin with ha_in | hb_in
          · have ha_mem : acc.getD a 0 ∈ acc := by
              by_cases ha : a < acc.length
              · exact getD_mem_of_lt acc ha
              · rw [getD_eq_default acc 0 ha, h0_not f] at ha_in; cases ha_in
            exact List.countP_pos_iff.mpr ⟨_, ha_mem, ha_in⟩
          · have hb_mem : acc.getD b 0 ∈ acc := by
              by_cases hb : b < acc.length
              · exact getD_mem_of_lt acc hb
              · rw [getD_eq_default acc 0 hb, h0_not f] at hb_in; cases hb_in
            exact List.countP_pos_iff.mpr ⟨_, hb_mem, hb_in⟩
        have hfin : inFam f (evalOrMask acc ⟨op, a :: b :: rest⟩) = true := by
          rw [hval]
          have htrue : ∀ f0 : Fin 6, inFam f0 (famInter f0) = true := by decide
          exact htrue f
        simp only [gateMasksFrom, List.countP_cons, hfin, ↓reduceIte]
        omega
    · have hgs_mem : famInter f ∈ gateMasksFrom (acc ++ [evalOrMask acc g]) gs := by
        rcases hmem with heq | hmem'
        · exact absurd heq.symm hval
        · exact hmem'
      have hl' : ∀ x ∈ acc ++ [evalOrMask acc g], x < 16384 := by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hl x hx
        · exact hval_lt
      have hno' : famInter f ∉ acc ++ [evalOrMask acc g] := by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hno, fun he => hval he.symm⟩
      have hih := ih (acc ++ [evalOrMask acc g]) hl' hno' hgs_mem
      rw [List.countP_append, countP_singleton_bool] at hih
      simp only [gateMasksFrom, List.countP_cons]
      split_ifs at hih ⊢ <;> omega

lemma inFam_imp_mem_famSubmasks (f : Fin 6) (m : Nat) (hm : m < 16384) (hin : inFam f m = true) :
    m ∈ famSubmasks f := by
  simp only [inFam, Bool.and_eq_true, beq_iff_eq] at hin
  exact mem_famSubmasks_of_le f m hm hin.2

lemma inFam_cases (f : Fin 6) (m : Nat) (hm : m < 16384) (hin : inFam f m = true) :
    m = famMask f 1 ∨ m = famMask f 2 ∨ m = famMask f 3 ∨ m = famInter f := by
  have hmem := inFam_imp_mem_famSubmasks f m hm hin
  have hdec : ((List.finRange 6).all fun g => (famSubmasks g).all fun x =>
      !inFam g x || (x == famMask g 1 || x == famMask g 2 || x == famMask g 3 || x == famInter g)) = true := by
    decide
  have hf := List.all_eq_true.mp hdec f (List.mem_finRange f)
  have hall := List.all_eq_true.mp hf m hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hall
  rcases hall with hfalse | hcases
  · rw [hin] at hfalse
    cases hfalse
  · rcases hcases with ((h1 | h2) | h3) | h4
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr h4))

lemma inFam_le_famMask_four (f : Fin 6) (m : Nat) (hm : m < 16384) (hin : inFam f m = true) :
    (m &&& famMask f 4) = m := by
  have hmem := inFam_imp_mem_famSubmasks f m hm hin
  have hdec : ((List.finRange 6).all fun g => (famSubmasks g).all fun x =>
      !inFam g x || ((x &&& famMask g 4) == x)) = true := by
    decide
  have hf := List.all_eq_true.mp hdec f (List.mem_finRange f)
  have hall := List.all_eq_true.mp hf m hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hall
  rcases hall with hfalse | heq
  · rw [hin] at hfalse
    cases hfalse
  · exact heq

def optOf (f : Fin 6) (L : List Nat) : Nat :=
  let lf := L.filter (inFam f)
  if lf.length = 0 then 0
  else if lf.length = 1 then
    match lf with
    | [m] => if m == famMask f 1 then 1 else if m == famMask f 2 then 2 else 3
    | _ => 0
  else 4

lemma optOf_cost_le (f : Fin 6) (L : List Nat) :
    cCost (optOf f L) ≤ L.countP (inFam f) := by
  dsimp [optOf]
  have hlen : (L.filter (inFam f)).length = L.countP (inFam f) := length_filter_eq_countP _ _
  split_ifs with h0 h1
  · simp [cCost]
  · rcases hlf : L.filter (inFam f) with _ | ⟨m, _ | ⟨m2, t⟩⟩
    · simp [hlf] at h1
    · dsimp only
      split_ifs <;> simp [cCost, ← hlen, hlf]
    · simp [hlf] at h1
  · have h2 : 2 ≤ L.countP (inFam f) := by omega
    simpa [cCost] using h2

lemma optOf_covers (f : Fin 6) (gs : List Gate)
    (m : Nat) (hm : m ∈ gateMasksFrom initMasks gs) (hin : inFam f m = true) :
    m &&& famMask f (optOf f (gateMasksFrom initMasks gs)) = m := by
  set L := gateMasksFrom initMasks gs
  have hmlt : m < 16384 := gateMasksFrom_lt initMasks initMasks_lt gs m hm
  have hlen : (L.filter (inFam f)).length = L.countP (inFam f) := length_filter_eq_countP _ _
  dsimp [optOf]
  split_ifs with h0 h1
  · exfalso
    have hpos : 0 < (L.filter (inFam f)).length :=
      List.length_pos_iff_exists_mem.mpr ⟨m, List.mem_filter.mpr ⟨hm, hin⟩⟩
    omega
  · rcases hlf : L.filter (inFam f) with _ | ⟨x, _ | ⟨y, t⟩⟩
    · simp [hlf] at h1
    · have hm_in_lf : m ∈ L.filter (inFam f) := List.mem_filter.mpr ⟨hm, hin⟩
      rw [hlf, List.mem_singleton] at hm_in_lf
      subst hm_in_lf
      have hne : m ≠ famInter f := by
        intro heq
        subst heq
        have htrue : ∀ f0 : Fin 6, inFam f0 (famInter f0) = true := by decide
        have hno : famInter f ∉ initMasks := by
          intro hinit
          have hfl := initMasks_not_inFam f _ hinit
          rw [htrue f] at hfl
          cases hfl
        have hge2 := famInter_requires_two f initMasks initMasks_lt hno gs hm
        have hinit0 : initMasks.countP (inFam f) = 0 := by
          rw [List.countP_eq_zero]
          intro z hz
          simp [initMasks_not_inFam f z hz]
        rw [hinit0] at hge2
        have hct1 : (L.countP (inFam f)) = 1 := by rw [← hlen, hlf]; simp
        dsimp [L] at hge2
        rw [hct1] at hge2
        omega
      have hself : ∀ (f0 : Fin 6) (c : Fin 5), famMask f0 c.val &&& famMask f0 c.val = famMask f0 c.val := by decide
      have hdist : ∀ f0 : Fin 6, famMask f0 2 ≠ famMask f0 1 ∧ famMask f0 3 ≠ famMask f0 1 ∧ famMask f0 3 ≠ famMask f0 2 := by
        decide
      rcases inFam_cases f m hmlt hin with rfl | rfl | rfl | he
      · have h11 : (famMask f 1 == famMask f 1) = true := by simp
        simp only [h11, ↓reduceIte]
        exact hself f ⟨1, by decide⟩
      · have h21 : (famMask f 2 == famMask f 1) = false := beq_false_of_ne (hdist f).1
        have h22 : (famMask f 2 == famMask f 2) = true := by simp
        simp only [h21, h22, Bool.false_eq_true, ↓reduceIte]
        exact hself f ⟨2, by decide⟩
      · have h31 : (famMask f 3 == famMask f 1) = false := beq_false_of_ne (hdist f).2.1
        have h32 : (famMask f 3 == famMask f 2) = false := beq_false_of_ne (hdist f).2.2
        simp only [h31, h32, Bool.false_eq_true, ↓reduceIte]
        exact hself f ⟨3, by decide⟩
      · exact absurd he hne
    · simp [hlf] at h1
  · exact inFam_le_famMask_four f m hmlt hin

lemma inFam_disjoint (f1 f2 : Fin 6) (hne : f1 ≠ f2) (x : Nat) (hx : x < 16384) :
    (inFam f1 x && inFam f2 x) = false := by
  by_cases hf1 : inFam f1 x = true
  · have hmem := inFam_imp_mem_famSubmasks f1 x hx hf1
    have hdec : ((List.finRange 6).all fun a => (List.finRange 6).all fun b =>
        (a == b) || ((famSubmasks a).all fun y => !(inFam a y && inFam b y))) = true := by
      decide
    have ha := List.all_eq_true.mp hdec f1 (List.mem_finRange f1)
    have hb := List.all_eq_true.mp ha f2 (List.mem_finRange f2)
    simp only [Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with heq | hall
    · exact absurd heq hne
    · have hxtrue := List.all_eq_true.mp hall x hmem
      simpa only [Bool.not_eq_true'] using hxtrue
  · have hff : inFam f1 x = false := Bool.eq_false_iff.mpr hf1
    simp [hff]

lemma inFam_targetCount_ge2 (f : Fin 6) (m : Nat) (hm : m < 16384) (hin : inFam f m = true) :
    2 ≤ targetCount m := by
  have hmem := inFam_imp_mem_famSubmasks f m hm hin
  have hdec : ((List.finRange 6).all fun g => (famSubmasks g).all fun x =>
      !inFam g x || decide (2 ≤ targetCount x)) = true := by
    decide
  have hf := List.all_eq_true.mp hdec f (List.mem_finRange f)
  have hx := List.all_eq_true.mp hf m hmem
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hx
  rcases hx with hfalse | hge
  · rw [hin] at hfalse; cases hfalse
  · exact hge

lemma isPriv_unique (v1 v2 : Fin 4) (m : Nat) (h1 : isPriv v1 m = true) (h2 : isPriv v2 m = true) :
    v1 = v2 := by
  by_contra hne
  simp only [isPriv, Bool.and_eq_true, beq_iff_eq] at h1 h2
  have ht1 : inTarget v1 m = true := h1.1.2
  have ht2 : inTarget v2 m = true := h2.1.2
  have htc : targetCount m = 1 := h1.2
  have hge2 : 2 ≤ targetCount m := by
    have h0 : ∀ x : Fin 4, inTarget x m = true →
        (x = 0 ∧ inTarget 0 m = true) ∨ (x = 1 ∧ inTarget 1 m = true) ∨
        (x = 2 ∧ inTarget 2 m = true) ∨ (x = 3 ∧ inTarget 3 m = true) := by
      intro ⟨x, hx⟩ htx
      match x with
      | 0 => exact Or.inl ⟨rfl, htx⟩
      | 1 => exact Or.inr (Or.inl ⟨rfl, htx⟩)
      | 2 => exact Or.inr (Or.inr (Or.inl ⟨rfl, htx⟩))
      | 3 => exact Or.inr (Or.inr (Or.inr ⟨rfl, htx⟩))
      | _ + 4 => omega
    rcases h0 v1 ht1 with ⟨rfl, ht1'⟩ | ⟨rfl, ht1'⟩ | ⟨rfl, ht1'⟩ | ⟨rfl, ht1'⟩ <;>
      rcases h0 v2 ht2 with ⟨rfl, ht2'⟩ | ⟨rfl, ht2'⟩ | ⟨rfl, ht2'⟩ | ⟨rfl, ht2'⟩ <;>
      first
      | exact absurd rfl hne
      | (simp [targetCount, ht1', ht2']; try omega)
  omega

lemma class_sum_le_one_explicit (m : Nat) (hm : m < 16384) :
    (if inFam 0 m then 1 else 0) + (if inFam 1 m then 1 else 0) +
    (if inFam 2 m then 1 else 0) + (if inFam 3 m then 1 else 0) +
    (if inFam 4 m then 1 else 0) + (if inFam 5 m then 1 else 0) +
    (if isPriv 0 m then 1 else 0) + (if isPriv 1 m then 1 else 0) +
    (if isPriv 2 m then 1 else 0) + (if isPriv 3 m then 1 else 0) ≤ 1 := by
  have hfam_le1 : ∀ (f1 f2 : Fin 6), f1 ≠ f2 → inFam f1 m = true → inFam f2 m = true → False := by
    intro f1 f2 hne h1 h2
    have hd := inFam_disjoint f1 f2 hne m hm
    rw [h1, h2] at hd
    cases hd
  have hfp : ∀ (f : Fin 6) (v : Fin 4), inFam f m = true → isPriv v m = true → False := by
    intro f v hf hp
    have hge2 := inFam_targetCount_ge2 f m hm hf
    simp only [isPriv, Bool.and_eq_true, beq_iff_eq] at hp
    omega
  have hp_le1 : ∀ (v1 v2 : Fin 4), v1 ≠ v2 → isPriv v1 m = true → isPriv v2 m = true → False := by
    intro v1 v2 hne h1 h2
    exact hne (isPriv_unique v1 v2 m h1 h2)
  by_cases hf0 : inFam 0 m = true
  · have := fun g h => hfam_le1 0 g h hf0
    have hf1 : inFam 1 m = false := Bool.eq_false_iff.mpr (this 1 (by decide))
    have hf2 : inFam 2 m = false := Bool.eq_false_iff.mpr (this 2 (by decide))
    have hf3 : inFam 3 m = false := Bool.eq_false_iff.mpr (this 3 (by decide))
    have hf4 : inFam 4 m = false := Bool.eq_false_iff.mpr (this 4 (by decide))
    have hf5 : inFam 5 m = false := Bool.eq_false_iff.mpr (this 5 (by decide))
    have hv0 : isPriv 0 m = false := Bool.eq_false_iff.mpr (hfp 0 0 hf0)
    have hv1 : isPriv 1 m = false := Bool.eq_false_iff.mpr (hfp 0 1 hf0)
    have hv2 : isPriv 2 m = false := Bool.eq_false_iff.mpr (hfp 0 2 hf0)
    have hv3 : isPriv 3 m = false := Bool.eq_false_iff.mpr (hfp 0 3 hf0)
    simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2, hv3]
  · by_cases hf1 : inFam 1 m = true
    · have := fun g h => hfam_le1 1 g h hf1
      have hf2 : inFam 2 m = false := Bool.eq_false_iff.mpr (this 2 (by decide))
      have hf3 : inFam 3 m = false := Bool.eq_false_iff.mpr (this 3 (by decide))
      have hf4 : inFam 4 m = false := Bool.eq_false_iff.mpr (this 4 (by decide))
      have hf5 : inFam 5 m = false := Bool.eq_false_iff.mpr (this 5 (by decide))
      have hv0 : isPriv 0 m = false := Bool.eq_false_iff.mpr (hfp 1 0 hf1)
      have hv1 : isPriv 1 m = false := Bool.eq_false_iff.mpr (hfp 1 1 hf1)
      have hv2 : isPriv 2 m = false := Bool.eq_false_iff.mpr (hfp 1 2 hf1)
      have hv3 : isPriv 3 m = false := Bool.eq_false_iff.mpr (hfp 1 3 hf1)
      simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2, hv3]
    · by_cases hf2 : inFam 2 m = true
      · have := fun g h => hfam_le1 2 g h hf2
        have hf3 : inFam 3 m = false := Bool.eq_false_iff.mpr (this 3 (by decide))
        have hf4 : inFam 4 m = false := Bool.eq_false_iff.mpr (this 4 (by decide))
        have hf5 : inFam 5 m = false := Bool.eq_false_iff.mpr (this 5 (by decide))
        have hv0 : isPriv 0 m = false := Bool.eq_false_iff.mpr (hfp 2 0 hf2)
        have hv1 : isPriv 1 m = false := Bool.eq_false_iff.mpr (hfp 2 1 hf2)
        have hv2 : isPriv 2 m = false := Bool.eq_false_iff.mpr (hfp 2 2 hf2)
        have hv3 : isPriv 3 m = false := Bool.eq_false_iff.mpr (hfp 2 3 hf2)
        simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2, hv3]
      · by_cases hf3 : inFam 3 m = true
        · have := fun g h => hfam_le1 3 g h hf3
          have hf4 : inFam 4 m = false := Bool.eq_false_iff.mpr (this 4 (by decide))
          have hf5 : inFam 5 m = false := Bool.eq_false_iff.mpr (this 5 (by decide))
          have hv0 : isPriv 0 m = false := Bool.eq_false_iff.mpr (hfp 3 0 hf3)
          have hv1 : isPriv 1 m = false := Bool.eq_false_iff.mpr (hfp 3 1 hf3)
          have hv2 : isPriv 2 m = false := Bool.eq_false_iff.mpr (hfp 3 2 hf3)
          have hv3 : isPriv 3 m = false := Bool.eq_false_iff.mpr (hfp 3 3 hf3)
          simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2, hv3]
        · by_cases hf4 : inFam 4 m = true
          · have hf5 : inFam 5 m = false := Bool.eq_false_iff.mpr (hfam_le1 4 5 (by decide) hf4)
            have hv0 : isPriv 0 m = false := Bool.eq_false_iff.mpr (hfp 4 0 hf4)
            have hv1 : isPriv 1 m = false := Bool.eq_false_iff.mpr (hfp 4 1 hf4)
            have hv2 : isPriv 2 m = false := Bool.eq_false_iff.mpr (hfp 4 2 hf4)
            have hv3 : isPriv 3 m = false := Bool.eq_false_iff.mpr (hfp 4 3 hf4)
            simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2, hv3]
          · by_cases hf5 : inFam 5 m = true
            · have hv0 : isPriv 0 m = false := Bool.eq_false_iff.mpr (hfp 5 0 hf5)
              have hv1 : isPriv 1 m = false := Bool.eq_false_iff.mpr (hfp 5 1 hf5)
              have hv2 : isPriv 2 m = false := Bool.eq_false_iff.mpr (hfp 5 2 hf5)
              have hv3 : isPriv 3 m = false := Bool.eq_false_iff.mpr (hfp 5 3 hf5)
              simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2, hv3]
            · by_cases hv0 : isPriv 0 m = true
              · have hv1 : isPriv 1 m = false := Bool.eq_false_iff.mpr (hp_le1 0 1 (by decide) hv0)
                have hv2 : isPriv 2 m = false := Bool.eq_false_iff.mpr (hp_le1 0 2 (by decide) hv0)
                have hv3 : isPriv 3 m = false := Bool.eq_false_iff.mpr (hp_le1 0 3 (by decide) hv0)
                simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2, hv3]
              · by_cases hv1 : isPriv 1 m = true
                · have hv2 : isPriv 2 m = false := Bool.eq_false_iff.mpr (hp_le1 1 2 (by decide) hv1)
                  have hv3 : isPriv 3 m = false := Bool.eq_false_iff.mpr (hp_le1 1 3 (by decide) hv1)
                  simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2, hv3]
                · by_cases hv2 : isPriv 2 m = true
                  · have hv3 : isPriv 3 m = false := Bool.eq_false_iff.mpr (hp_le1 2 3 (by decide) hv2)
                    simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2, hv3]
                  · simp [hf0, hf1, hf2, hf3, hf4, hf5, hv0, hv1, hv2]
                    split_ifs <;> omega

lemma countP_class_sum_le (L : List Nat) (hL : ∀ m ∈ L, m < 16384) :
    L.countP (inFam 0) + L.countP (inFam 1) + L.countP (inFam 2) +
    L.countP (inFam 3) + L.countP (inFam 4) + L.countP (inFam 5) +
    L.countP (isPriv 0) + L.countP (isPriv 1) + L.countP (isPriv 2) +
    L.countP (isPriv 3) ≤ L.length := by
  induction L with
  | nil => simp
  | cons m ms ih =>
    have hsingle := class_sum_le_one_explicit m (hL m (by simp))
    have hms := ih (fun x hx => hL x (by simp [hx]))
    simp only [List.countP_cons, List.length_cons]
    omega

def orAll (l : List Nat) : Nat :=
  l.foldr (· ||| ·) 0

lemma testBit_orAll (l : List Nat) (i : Nat) :
    (orAll l).testBit i = l.any (fun x => x.testBit i) := by
  induction l with
  | nil => simp [orAll]
  | cons x xs ih =>
    simp only [orAll, List.foldr_cons, Nat.testBit_or, List.any_cons]
    change (x.testBit i || (orAll xs).testBit i) = (x.testBit i || xs.any (fun x => x.testBit i))
    rw [ih]

lemma or_inTarget (v : Fin 4) (x y : Nat)
    (h : inTarget v (x ||| y) = true) : inTarget v x = true ∧ inTarget v y = true := by
  simp only [inTarget, beq_iff_eq] at h ⊢
  constructor <;> apply Nat.eq_of_testBit_eq <;> intro i
  · rw [Nat.testBit_and]
    have hi := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_or] at hi
    cases hxi : x.testBit i <;> simp_all
  · rw [Nat.testBit_and]
    have hi := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_or] at hi
    cases hyi : y.testBit i <;> simp_all

lemma isSingleton_exists (m : Nat) (hm : isSingleton m = true) :
    ∃ p : Nat, p < 14 ∧ m = 2 ^ p := by
  simp only [isSingleton, List.any_eq_true, List.mem_range, beq_iff_eq] at hm
  exact hm

lemma inTarget_targetCount_pos (v : Fin 4) (m : Nat) (hin : inTarget v m = true) :
    1 ≤ targetCount m := by
  rcases v with ⟨v, hv⟩
  match v with
  | 0 => have h0 : inTarget 0 m = true := hin; simp [targetCount, h0]; try omega
  | 1 => have h1 : inTarget 1 m = true := hin; simp [targetCount, h1]; try omega
  | 2 => have h2 : inTarget 2 m = true := hin; simp [targetCount, h2]; try omega
  | 3 => have h3 : inTarget 3 m = true := hin; simp [targetCount, h3]; try omega
  | _ + 4 => omega

lemma filter_ne_length_add_one (k : Nat) (l : List Nat) (hk : k ∈ l) :
    (l.filter (fun u => u != k)).length + 1 ≤ l.length := by
  induction l with
  | nil => simp at hk
  | cons x xs ih =>
    simp only [List.mem_cons] at hk
    have hle : (xs.filter (fun u => u != k)).length ≤ xs.length := List.length_filter_le _ _
    rw [List.filter_cons, List.length_cons]
    by_cases hx : x = k
    · subst hx
      simp
      omega
    · have hkxs : k ∈ xs := by
        rcases hk with rfl | hmem
        · exact absurd rfl hx
        · exact hmem
      have hih := ih hkxs
      have hxne : (x != k) = true := bne_iff_ne.mpr hx
      simp [hxne]
      omega

lemma eq_of_bool_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma orAll_filter_ne_eq (acc : List Nat) (val : Nat) (l : List Nat)
    (hl : ∀ u ∈ l, u < acc.length + 1)
    (hk : acc.length ∈ l) :
    orAll (l.map (fun u => (acc ++ [val]).getD u 0)) =
      val ||| orAll ((l.filter (fun u => u != acc.length)).map (fun u => acc.getD u 0)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_orAll, testBit_orAll]
  apply eq_of_bool_iff
  simp only [List.any_map, List.any_eq_true, List.mem_filter, Function.comp_def, bne_iff_ne,
    Bool.or_eq_true]
  constructor
  · rintro ⟨u, hu, hbit⟩
    by_cases huk : u = acc.length
    · subst huk
      rw [getD_append_self] at hbit
      exact Or.inl hbit
    · have hult := hl u hu
      have hua : u < acc.length := by omega
      rw [getD_append_left acc [val] 0 hua] at hbit
      exact Or.inr ⟨u, ⟨hu, huk⟩, hbit⟩
  · rintro (hval | ⟨u, ⟨hu, huk⟩, hbit⟩)
    · refine ⟨acc.length, hk, ?_⟩
      rw [getD_append_self]
      exact hval
    · have hult := hl u hu
      have hua : u < acc.length := by omega
      refine ⟨u, hu, ?_⟩
      rw [getD_append_left acc [val] 0 hua]
      exact hbit

lemma orAll_lt_eq (acc : List Nat) (val : Nat) (l : List Nat)
    (hl : ∀ u ∈ l, u < acc.length) :
    orAll (l.map (fun u => (acc ++ [val]).getD u 0)) =
      orAll (l.map (fun u => acc.getD u 0)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_orAll, testBit_orAll]
  apply eq_of_bool_iff
  simp only [List.any_map, Function.comp_def, List.any_eq_true]
  constructor <;> rintro ⟨u, hu, hbit⟩ <;> refine ⟨u, hu, ?_⟩
  · rw [getD_append_left acc [val] 0 (hl u hu)] at hbit
    exact hbit
  · rw [getD_append_left acc [val] 0 (hl u hu)]
    exact hbit

lemma backward_expand (v : Fin 4) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) :
    ∀ (acc : List Nat),
      (∀ x ∈ acc, x < 16384) →
      initMasks.length ≤ acc.length →
      (∀ i (hi : i < 14), acc.getD i 0 = 2 ^ i) →
      ∀ (activeEnd sharedEnd : List Nat),
        (∀ u ∈ activeEnd, u < (simMasks acc gs).length ∧ inTarget v ((simMasks acc gs).getD u 0) = true) →
        (∀ m ∈ sharedEnd, m < 16384 ∧ m ≠ 0 ∧ isSingleton m = false ∧ inTarget v m = true ∧ 2 ≤ targetCount m) →
        (orAll (activeEnd.map (fun u => (simMasks acc gs).getD u 0)) ||| orAll sharedEnd) = B v →
        ∃ (active0 shared0 : List Nat),
          (∀ u ∈ active0, u < acc.length ∧ inTarget v (acc.getD u 0) = true) ∧
          (∀ m ∈ shared0, m < 16384 ∧ m ≠ 0 ∧ isSingleton m = false ∧ inTarget v m = true ∧ 2 ≤ targetCount m ∧
            (m ∈ sharedEnd ∨ m ∈ gateMasksFrom acc gs)) ∧
          (orAll (active0.map (fun u => acc.getD u 0)) ||| orAll shared0) = B v ∧
          active0.length + shared0.length ≤
            activeEnd.length + sharedEnd.length + (gateMasksFrom acc gs).countP (isPriv v) := by
  induction gs with
  | nil =>
    intro acc _ _ _ activeEnd sharedEnd hact hsh hor
    refine ⟨activeEnd, sharedEnd, ?_, ?_, ?_, ?_⟩
    · simpa [simMasks] using hact
    · intro m hm
      rcases hsh m hm with ⟨h1, h2, h3, h4, h5⟩
      exact ⟨h1, h2, h3, h4, h5, Or.inl hm⟩
    · simpa [simMasks] using hor
    · simp [gateMasksFrom]
  | cons g gs ih =>
    intro acc hl hlen14 hinit activeEnd sharedEnd hact hsh hor
    have hg := hgs g (by simp)
    have hgs' : ∀ g' ∈ gs, g'.op = GateOp.or ∧ g'.inputs.length ≤ 2 := fun g' hg' => hgs g' (by simp [hg'])
    let val := evalOrMask acc g
    have hval_lt : val < 16384 := evalOrMask_lt acc hl g
    have hl' : ∀ x ∈ acc ++ [val], x < 16384 := by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hl x hx
      · exact hval_lt
    have hlen14' : initMasks.length ≤ (acc ++ [val]).length := by simp; omega
    have hinit' : ∀ i (hi : i < 14), (acc ++ [val]).getD i 0 = 2 ^ i := by
      intro i hi
      have hia : i < acc.length := by simp [initMasks] at hlen14; omega
      rw [getD_append_left acc [val] 0 hia]
      exact hinit i hi
    have hsim : simMasks acc (g :: gs) = simMasks (acc ++ [val]) gs := rfl
    rw [hsim] at hact hor
    rcases ih hgs' (acc ++ [val]) hl' hlen14' hinit' activeEnd sharedEnd hact hsh hor with
      ⟨active', shared', hact', hsh', hor', hlen'⟩
    have lift_sh : ∀ m ∈ shared', m < 16384 ∧ m ≠ 0 ∧ isSingleton m = false ∧ inTarget v m = true ∧ 2 ≤ targetCount m ∧
        (m ∈ sharedEnd ∨ m ∈ gateMasksFrom acc (g :: gs)) := by
      intro m hm
      rcases hsh' m hm with ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨h1, h2, h3, h4, h5, ?_⟩
      rcases h6 with h6 | h6
      · exact Or.inl h6
      · exact Or.inr (by simp [gateMasksFrom, val, h6])
    have hgm : gateMasksFrom acc (g :: gs) = val :: gateMasksFrom (acc ++ [val]) gs := rfl
    by_cases hk : acc.length ∈ active'
    · have hrest_lt : ∀ u ∈ active'.filter (fun u => u != acc.length), u < acc.length := by
        intro u hu
        simp only [List.mem_filter, bne_iff_ne] at hu
        have := (hact' u hu.1).1
        simp only [List.length_append, List.length_singleton] at this
        omega
      have hk_targ : inTarget v val = true := by
        have ht := (hact' acc.length hk).2
        rw [getD_append_self] at ht
        exact ht
      have hact_filt_targ : ∀ u ∈ active'.filter (fun u => u != acc.length), inTarget v (acc.getD u 0) = true := by
        intro u hu
        have hu' := List.mem_filter.mp hu
        have ht := (hact' u hu'.1).2
        have hua := hrest_lt u hu
        rw [getD_append_left acc [val] 0 hua] at ht
        exact ht
      have hfilt_len := filter_ne_length_add_one acc.length active' hk
      have hact_lt' : ∀ u ∈ active', u < acc.length + 1 := fun u hu => by simpa using (hact' u hu).1
      have hor_filt : orAll (active'.map (fun u => (acc ++ [val]).getD u 0)) =
          val ||| orAll ((active'.filter (fun u => u != acc.length)).map (fun u => acc.getD u 0)) :=
        orAll_filter_ne_eq acc val active' hact_lt' hk
      set rest := active'.filter (fun u => u != acc.length)
      by_cases hval0 : val = 0
      · refine ⟨rest, shared', ?_, lift_sh, ?_, ?_⟩
        · intro u hu; exact ⟨hrest_lt u hu, hact_filt_targ u hu⟩
        · rw [hor_filt, hval0, Nat.zero_or] at hor'
          exact hor'
        · rw [hgm, List.countP_cons]
          omega
      · by_cases hsing : isSingleton val = true
        · rcases isSingleton_exists val hsing with ⟨p, hp14, hpow⟩
          have hp_acc : p < acc.length := by simp [initMasks] at hlen14; omega
          have hp_val : acc.getD p 0 = val := by rw [hinit p hp14, ← hpow]
          refine ⟨p :: rest, shared', ?_, lift_sh, ?_, ?_⟩
          · intro u hu
            simp only [List.mem_cons] at hu
            rcases hu with rfl | hu
            · exact ⟨hp_acc, by rw [hp_val]; exact hk_targ⟩
            · exact ⟨hrest_lt u hu, hact_filt_targ u hu⟩
          · simp only [List.map_cons, orAll, List.foldr_cons, hp_val]
            rw [hor_filt] at hor'
            exact hor'
          · simp only [List.length_cons, hgm, List.countP_cons]
            omega
        · by_cases htc : 2 ≤ targetCount val
          · refine ⟨rest, val :: shared', ?_, ?_, ?_, ?_⟩
            · intro u hu; exact ⟨hrest_lt u hu, hact_filt_targ u hu⟩
            · intro m hm
              simp only [List.mem_cons] at hm
              rcases hm with rfl | hm
              · exact ⟨hval_lt, hval0, by simp [hsing], hk_targ, htc, Or.inr (by simp [gateMasksFrom, val])⟩
              · exact lift_sh m hm
            · rw [hor_filt] at hor'
              simp only [orAll, List.foldr_cons] at hor' ⊢
              apply Nat.eq_of_testBit_eq
              intro i
              have hi := congrArg (fun n => n.testBit i) hor'
              simp only [Nat.testBit_or] at hi ⊢
              rw [← hi]
              cases val.testBit i <;> cases (List.foldr (· ||| ·) 0 (rest.map (fun u => acc.getD u 0))).testBit i <;>
                cases (List.foldr (· ||| ·) 0 shared').testBit i <;> rfl
            · simp only [List.length_cons, hgm, List.countP_cons]
              omega
          · have htc1 : targetCount val = 1 := by
              have hge1 := inTarget_targetCount_pos v val hk_targ
              omega
            have hpriv : isPriv v val = true := by
              simp [isPriv, hval0, hsing, hk_targ, htc1]
            rcases hg with ⟨_, hlen_in⟩
            rcases g with ⟨op, ins⟩
            dsimp at hlen_in
            rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
            · exfalso; apply hval0; simp [val, evalOrMask]
            · have ha_eq : acc.getD a 0 = val := rfl
              by_cases ha : a < acc.length
              · refine ⟨a :: rest, shared', ?_, lift_sh, ?_, ?_⟩
                · intro u hu
                  simp only [List.mem_cons] at hu
                  rcases hu with rfl | hu
                  · exact ⟨ha, by rw [ha_eq]; exact hk_targ⟩
                  · exact ⟨hrest_lt u hu, hact_filt_targ u hu⟩
                · simp only [List.map_cons, orAll, List.foldr_cons, ha_eq]
                  rw [hor_filt] at hor'
                  exact hor'
                · simp only [List.length_cons, hgm, List.countP_cons, hpriv, ↓reduceIte]
                  omega
              · exfalso
                apply hval0
                change evalOrMask acc ⟨op, [a]⟩ = 0
                simp only [evalOrMask]
                exact getD_eq_default acc 0 ha
            · have hor_val : acc.getD a 0 ||| acc.getD b 0 = val := rfl
              have hxy_targ := or_inTarget v (acc.getD a 0) (acc.getD b 0) (by rw [hor_val]; exact hk_targ)
              let addList := (if a < acc.length then [a] else []) ++ (if b < acc.length then [b] else [])
              have hadd_len : addList.length ≤ 2 := by
                dsimp [addList]
                split_ifs <;> simp
              have hadd_or : orAll (addList.map (fun u => acc.getD u 0)) = val := by
                by_cases ha : a < acc.length <;> by_cases hb : b < acc.length
                · have hl : addList = [a, b] := by dsimp [addList]; simp [ha, hb]
                  rw [hl]
                  simp only [List.map_cons, List.map_nil, orAll, List.foldr_cons, List.foldr_nil, Nat.or_zero]
                  exact hor_val
                · have hzb : acc.getD b 0 = 0 := getD_eq_default acc 0 hb
                  have hl : addList = [a] := by dsimp [addList]; simp [ha, hb]
                  rw [hl, ← hor_val, hzb]
                  simp only [List.map_cons, List.map_nil, orAll, List.foldr_cons, List.foldr_nil, Nat.or_zero]
                · have hza : acc.getD a 0 = 0 := getD_eq_default acc 0 ha
                  have hl : addList = [b] := by dsimp [addList]; simp [ha, hb]
                  rw [hl, ← hor_val, hza]
                  simp only [List.map_cons, List.map_nil, orAll, List.foldr_cons, List.foldr_nil, Nat.or_zero, Nat.zero_or]
                · have hza : acc.getD a 0 = 0 := getD_eq_default acc 0 ha
                  have hzb : acc.getD b 0 = 0 := getD_eq_default acc 0 hb
                  have hl : addList = [] := by dsimp [addList]; simp [ha, hb]
                  rw [hl, ← hor_val, hza, hzb]
                  rfl
              refine ⟨addList ++ rest, shared', ?_, lift_sh, ?_, ?_⟩
              · intro u hu
                simp only [List.mem_append] at hu
                rcases hu with hu | hu
                · dsimp [addList] at hu
                  simp only [List.mem_append] at hu
                  rcases hu with hua | hub
                  · split_ifs at hua with ha
                    · simp only [List.mem_singleton] at hua
                      subst hua
                      exact ⟨ha, hxy_targ.1⟩
                    · simp at hua
                  · split_ifs at hub with hb
                    · simp only [List.mem_singleton] at hub
                      subst hub
                      exact ⟨hb, hxy_targ.2⟩
                    · simp at hub
                · exact ⟨hrest_lt u hu, hact_filt_targ u hu⟩
              · rw [hor_filt] at hor'
                apply Nat.eq_of_testBit_eq
                intro i
                have hi := congrArg (fun n => n.testBit i) hor'
                rw [Nat.testBit_or, Nat.testBit_or] at hi
                rw [Nat.testBit_or, testBit_orAll, List.map_append, List.any_append]
                rw [← testBit_orAll (addList.map (fun u => acc.getD u 0)) i, hadd_or]
                rw [← testBit_orAll (rest.map (fun u => acc.getD u 0)) i]
                exact hi
              · simp only [List.length_append, hgm, List.countP_cons, hpriv, ↓reduceIte]
                omega
            · simp at hlen_in
    · have hlt : ∀ u ∈ active', u < acc.length := by
        intro u hu
        have := (hact' u hu).1
        simp only [List.length_append, List.length_singleton] at this
        have hne : u ≠ acc.length := fun heq => hk (heq ▸ hu)
        omega
      refine ⟨active', shared', ?_, lift_sh, ?_, ?_⟩
      · intro u hu
        have hua := hlt u hu
        have ht := (hact' u hu).2
        refine ⟨hua, ?_⟩
        rw [getD_append_left acc [val] 0 hua] at ht
        exact ht
      · rw [orAll_lt_eq acc val active' hlt] at hor'
        exact hor'
      · simp only [hgm, List.countP_cons]
        omega

def famsOf : Fin 4 → Fin 6 × Fin 6 × Fin 6
  | 0 => (0, 1, 2)
  | 1 => (0, 3, 4)
  | 2 => (1, 3, 5)
  | 3 => (2, 4, 5)

lemma inTarget_and_pair (i j : Fin 4) (m : Nat)
    (hi : inTarget i m = true) (hj : inTarget j m = true) :
    (m &&& (B i &&& B j)) = m := by
  simp only [inTarget, beq_iff_eq] at hi hj
  apply Nat.eq_of_testBit_eq
  intro k
  have hik := congrArg (fun n => n.testBit k) hi
  have hjk := congrArg (fun n => n.testBit k) hj
  rw [Nat.testBit_and] at hik hjk ⊢
  rw [Nat.testBit_and]
  cases hmk : m.testBit k <;> simp_all

lemma mem_famsOf (v : Fin 4) (m : Nat) (hnz : m ≠ 0)
    (hsing : isSingleton m = false) (htarg : inTarget v m = true) (htc : 2 ≤ targetCount m) :
    inFam (famsOf v).1 m = true ∨ inFam (famsOf v).2.1 m = true ∨ inFam (famsOf v).2.2 m = true := by
  have hinFam_of : ∀ f : Fin 6, inTarget (famPair f).1 m = true → inTarget (famPair f).2 m = true →
      inFam f m = true := by
    intro f h1 h2
    simp only [inFam, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', beq_iff_eq]
    exact ⟨⟨hnz, hsing⟩, inTarget_and_pair _ _ m h1 h2⟩
  rcases v with ⟨v, hv⟩
  interval_cases v
  · change inTarget 0 m = true at htarg
    change inFam 0 m = true ∨ inFam 1 m = true ∨ inFam 2 m = true
    by_cases h1 : inTarget 1 m = true
    · exact Or.inl (hinFam_of 0 htarg h1)
    · by_cases h2 : inTarget 2 m = true
      · exact Or.inr (Or.inl (hinFam_of 1 htarg h2))
      · by_cases h3 : inTarget 3 m = true
        · exact Or.inr (Or.inr (hinFam_of 2 htarg h3))
        · simp [targetCount, htarg, h1, h2, h3] at htc
  · change inTarget 1 m = true at htarg
    change inFam 0 m = true ∨ inFam 3 m = true ∨ inFam 4 m = true
    by_cases h0 : inTarget 0 m = true
    · exact Or.inl (hinFam_of 0 h0 htarg)
    · by_cases h2 : inTarget 2 m = true
      · exact Or.inr (Or.inl (hinFam_of 3 htarg h2))
      · by_cases h3 : inTarget 3 m = true
        · exact Or.inr (Or.inr (hinFam_of 4 htarg h3))
        · simp [targetCount, htarg, h0, h2, h3] at htc
  · change inTarget 2 m = true at htarg
    change inFam 1 m = true ∨ inFam 3 m = true ∨ inFam 5 m = true
    by_cases h0 : inTarget 0 m = true
    · exact Or.inl (hinFam_of 1 h0 htarg)
    · by_cases h1 : inTarget 1 m = true
      · exact Or.inr (Or.inl (hinFam_of 3 h1 htarg))
      · by_cases h3 : inTarget 3 m = true
        · exact Or.inr (Or.inr (hinFam_of 5 htarg h3))
        · simp [targetCount, htarg, h0, h1, h3] at htc
  · change inTarget 3 m = true at htarg
    change inFam 2 m = true ∨ inFam 4 m = true ∨ inFam 5 m = true
    by_cases h0 : inTarget 0 m = true
    · exact Or.inl (hinFam_of 2 h0 htarg)
    · by_cases h1 : inTarget 1 m = true
      · exact Or.inr (Or.inl (hinFam_of 4 h1 htarg))
      · by_cases h2 : inTarget 2 m = true
        · exact Or.inr (Or.inr (hinFam_of 5 h2 htarg))
        · simp [targetCount, htarg, h0, h1, h2] at htc

lemma three_disjoint_any_le_length (f1 f2 f3 : Fin 6)
    (h12 : f1 ≠ f2) (h13 : f1 ≠ f3) (h23 : f2 ≠ f3)
    (l : List Nat) (hl : ∀ x ∈ l, x < 16384) :
    (if l.any (inFam f1) then 1 else 0) +
    (if l.any (inFam f2) then 1 else 0) +
    (if l.any (inFam f3) then 1 else 0) ≤ l.length := by
  have h_le_sum : ∀ (f : Fin 6), (if l.any (inFam f) then 1 else 0) ≤ l.countP (inFam f) := by
    intro f
    split_ifs with h
    · rw [List.any_eq_true] at h
      rcases h with ⟨x, hx, hfx⟩
      exact List.countP_pos_iff.mpr ⟨x, hx, hfx⟩
    · omega
  have hsum : l.countP (inFam f1) + l.countP (inFam f2) + l.countP (inFam f3) ≤ l.length := by
    clear h_le_sum
    induction l with
    | nil => simp
    | cons x xs ih =>
      have hxs := ih (fun y hy => hl y (by simp [hy]))
      have hx := hl x (by simp)
      have hdisj : (if inFam f1 x then 1 else 0) + (if inFam f2 x then 1 else 0) +
          (if inFam f3 x then 1 else 0) ≤ 1 := by
        cases h1 : inFam f1 x <;> cases h2 : inFam f2 x <;> cases h3 : inFam f3 x
        · simp
        · simp
        · simp
        · have hf := inFam_disjoint f2 f3 h23 x hx; rw [h2, h3] at hf; cases hf
        · simp
        · have hf := inFam_disjoint f1 f3 h13 x hx; rw [h1, h3] at hf; cases hf
        · have hf := inFam_disjoint f1 f2 h12 x hx; rw [h1, h2] at hf; cases hf
        · have hf := inFam_disjoint f1 f2 h12 x hx; rw [h1, h2] at hf; cases hf
      simp only [List.countP_cons, List.length_cons]
      omega
  have ha1 := h_le_sum f1
  have ha2 := h_le_sum f2
  have ha3 := h_le_sum f3
  omega

lemma minCov_le_of_bools (t m1 m2 m3 : Nat) (b1 b2 b3 : Bool) :
    minCov t m1 m2 m3 ≤
      ((if b1 then 1 else 0) + (if b2 then 1 else 0) + (if b3 then 1 else 0)) +
      pop14 (t &&& (16383 ^^^ ((if b1 then m1 else 0) ||| (if b2 then m2 else 0) ||| (if b3 then m3 else 0)))) := by
  cases b1 <;> cases b2 <;> cases b3 <;>
    simp only [minCov, Bool.false_eq_true, ↓reduceIte, Nat.zero_or, Nat.or_zero, Nat.add_zero, Nat.zero_add]
  · exact Nat.min_le_left _ _
  · exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)))
  · exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))
  · have h2 : (1 : Nat) + 1 = 2 := rfl
    rw [h2]
    exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _)
      (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))))))
  · exact le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
  · have h2 : (1 : Nat) + 1 = 2 := rfl
    rw [h2]
    exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _)
      (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)))))
  · have h2 : (1 : Nat) + 1 = 2 := rfl
    rw [h2]
    exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _)
      (le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _))))
  · have h3 : (1 : Nat) + 1 + 1 = 3 := rfl
    rw [h3]
    exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _)
      (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _))))))

lemma countP_range14_le_length (l : List Nat) (p : Nat → Bool)
    (hp : ∀ i ∈ List.range 14, p i = true → i ∈ l) :
    (List.range 14).countP p ≤ l.length := by
  rw [← length_filter_eq_countP]
  have hsub : ((List.range 14).filter p) ⊆ l := by
    intro i hi
    simp only [List.mem_filter] at hi
    exact hp i hi.1 hi.2
  have hnd : ((List.range 14).filter p).Nodup := List.Nodup.filter _ List.nodup_range
  have hfin : ((List.range 14).filter p).toFinset ⊆ l.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact hsub hx
  have hcard := Finset.card_le_card hfin
  rw [List.toFinset_card_of_nodup hnd] at hcard
  exact le_trans hcard (List.toFinset_card_le l)

lemma xor_16383_testBit (u i : Nat) (hi : i < 14) :
    (16383 ^^^ u).testBit i = !(u.testBit i) := by
  have hdec : ∀ j : Fin 14, (16383 : Nat).testBit j.val = true := by decide
  rw [Nat.testBit_xor, hdec ⟨i, hi⟩]
  cases u.testBit i <;> rfl

lemma famMask_lt (f : Fin 6) (c : Nat) : famMask f c < 16384 := by
  have h5 : ∀ (f0 : Fin 6) (c0 : Fin 5), famMask f0 c0.val < 16384 := by decide
  by_cases hc : c < 5
  · exact h5 f ⟨c, hc⟩
  · have heq : famMask f c = famMask f 4 := by
      rcases c with _ | _ | _ | _ | _ | c
      · omega
      · omega
      · omega
      · omega
      · omega
      · rfl
    rw [heq]
    exact h5 f ⟨4, by decide⟩

lemma minCov_le_one_add_priv (v : Fin 4) (C : Circuit)
    (hor : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (w : ℕ)
    (hw : ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false =
      Nat.testBit (p.val + 1) v.val) :
    let L := gateMasksFrom initMasks C.gates
    let fs := famsOf v
    minCov (B v) (famMask fs.1 (optOf fs.1 L)) (famMask fs.2.1 (optOf fs.2.1 L)) (famMask fs.2.2 (optOf fs.2.2 L)) ≤
      1 + L.countP (isPriv v) := by
  intro L fs
  have hB := simMasks_computes_B C hor v w hw
  have hnz_B : B v ≠ 0 := by fin_cases v <;> decide
  have hw_lt : w < (simMasks initMasks C.gates).length := by
    by_contra h
    have : (simMasks initMasks C.gates).getD w 0 = 0 := getD_eq_default _ 0 h
    rw [this] at hB
    exact hnz_B hB.symm
  have hinit_all : ∀ i (hi : i < 14), initMasks.getD i 0 = 2 ^ i := by
    intro i hi
    have hdec : ∀ q : Fin 14, initMasks.getD q.val 0 = 2 ^ q.val := by decide
    exact hdec ⟨i, hi⟩
  have hact0 : ∀ u ∈ [w], u < (simMasks initMasks C.gates).length ∧
      inTarget v ((simMasks initMasks C.gates).getD u 0) = true := by
    intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    refine ⟨hw_lt, ?_⟩
    rw [hB]
    fin_cases v <;> decide
  have hor0 : (orAll ([w].map (fun u => (simMasks initMasks C.gates).getD u 0)) ||| orAll []) = B v := by
    simp [orAll]
    exact hB
  rcases backward_expand v C.gates hor initMasks initMasks_lt (le_refl _) hinit_all [w] []
      hact0 (fun m hm => by simp at hm) hor0 with
    ⟨active0, shared0, hact0_res, hsh0_res, hor0_res, hlen0_res⟩
  dsimp only [List.length_nil, List.length_singleton, Nat.add_zero] at hlen0_res
  set m1 := famMask fs.1 (optOf fs.1 L)
  set m2 := famMask fs.2.1 (optOf fs.2.1 L)
  set m3 := famMask fs.2.2 (optOf fs.2.2 L)
  set b1 := shared0.any (inFam fs.1)
  set b2 := shared0.any (inFam fs.2.1)
  set b3 := shared0.any (inFam fs.2.2)
  set usedMask := (if b1 then m1 else 0) ||| (if b2 then m2 else 0) ||| (if b3 then m3 else 0)
  have hmin := minCov_le_of_bools (B v) m1 m2 m3 b1 b2 b3
  have hdisj : fs.1 ≠ fs.2.1 ∧ fs.1 ≠ fs.2.2 ∧ fs.2.1 ≠ fs.2.2 := by
    fin_cases v <;> decide
  have hsh0_lt : ∀ m ∈ shared0, m < 16384 := fun m hm => (hsh0_res m hm).1
  have hused_le := three_disjoint_any_le_length fs.1 fs.2.1 fs.2.2 hdisj.1 hdisj.2.1 hdisj.2.2 shared0 hsh0_lt
  have hshared_sub : ∀ m ∈ shared0, m &&& usedMask = m := by
    intro m hm
    rcases hsh0_res m hm with ⟨hm_lt, hm_nz, hm_sing, hm_targ, hm_tc, hm_src⟩
    simp only [List.not_mem_nil, false_or] at hm_src
    rcases mem_famsOf v m hm_nz hm_sing hm_targ hm_tc with hf1 | hf2 | hf3
    · have hb1 : b1 = true := List.any_eq_true.mpr ⟨m, hm, hf1⟩
      have hcov := optOf_covers fs.1 C.gates m hm_src hf1
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and]
      by_cases hmi : m.testBit i = true
      · have hm1 : m1.testBit i = true := by
          have := congrArg (fun n => n.testBit i) hcov
          rw [Nat.testBit_and, hmi] at this
          simpa using this
        have hui : usedMask.testBit i = true := by
          dsimp [usedMask]
          simp [hb1, Nat.testBit_or, hm1]
        simp [hmi, hui]
      · simp [hmi]
    · have hb2 : b2 = true := List.any_eq_true.mpr ⟨m, hm, hf2⟩
      have hcov := optOf_covers fs.2.1 C.gates m hm_src hf2
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and]
      by_cases hmi : m.testBit i = true
      · have hm2 : m2.testBit i = true := by
          have := congrArg (fun n => n.testBit i) hcov
          rw [Nat.testBit_and, hmi] at this
          simpa using this
        have hui : usedMask.testBit i = true := by
          dsimp [usedMask]
          simp [hb2, Nat.testBit_or, hm2]
        simp [hmi, hui]
      · simp [hmi]
    · have hb3 : b3 = true := List.any_eq_true.mpr ⟨m, hm, hf3⟩
      have hcov := optOf_covers fs.2.2 C.gates m hm_src hf3
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and]
      by_cases hmi : m.testBit i = true
      · have hm3 : m3.testBit i = true := by
          have := congrArg (fun n => n.testBit i) hcov
          rw [Nat.testBit_and, hmi] at this
          simpa using this
        have hui : usedMask.testBit i = true := by
          dsimp [usedMask]
          simp [hb3, Nat.testBit_or, hm3]
        simp [hmi, hui]
      · simp [hmi]
  have hpop_le : pop14 (B v &&& (16383 ^^^ usedMask)) ≤ active0.length := by
    apply countP_range14_le_length
    intro i hi hbit
    simp only [List.mem_range] at hi
    rw [Nat.testBit_and, xor_16383_testBit usedMask i hi] at hbit
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hbit
    rcases hbit with ⟨hbv, hum0⟩
    have hor_bit := congrArg (fun n => n.testBit i) hor0_res
    rw [hbv, Nat.testBit_or, testBit_orAll, testBit_orAll] at hor_bit
    have hsh0_bit : shared0.any (fun x => x.testBit i) = false := by
      rw [Bool.eq_false_iff]
      intro hany
      rw [List.any_eq_true] at hany
      rcases hany with ⟨m, hm, hmi⟩
      have hsub := congrArg (fun n => n.testBit i) (hshared_sub m hm)
      rw [Nat.testBit_and, hmi, hum0] at hsub
      simp at hsub
    rw [hsh0_bit, Bool.or_false] at hor_bit
    have hact_any := List.any_eq_true.mp hor_bit
    rcases hact_any with ⟨x, hxmem, hxi⟩
    simp only [List.mem_map] at hxmem
    rcases hxmem with ⟨u, hu, rfl⟩
    have hu14 : u < 14 := by
      have := (hact0_res u hu).1
      simpa [initMasks] using this
    rw [hinit_all u hu14, Nat.testBit_two_pow, decide_eq_true_eq] at hxi
    subst hxi
    exact hu
  dsimp only [L, usedMask, b1, b2, b3, m1, m2, m3] at *
  omega

def checkAll : Bool :=
  (List.range 5).all fun c0 =>
  (List.range 5).all fun c1 =>
  (List.range 5).all fun c2 =>
  (List.range 5).all fun c3 =>
  (List.range 5).all fun c4 =>
  (List.range 5).all fun c5 =>
    let sc := cCost c0 + cCost c1 + cCost c2 + cCost c3 + cCost c4 + cCost c5
    let m0 := famMask 0 c0
    let m1 := famMask 1 c1
    let m2 := famMask 2 c2
    let m3 := famMask 3 c3
    let m4 := famMask 4 c4
    let m5 := famMask 5 c5
    let p0 := minCov (B 0) m0 m1 m2 - 1
    let p1 := minCov (B 1) m0 m3 m4 - 1
    let p2 := minCov (B 2) m1 m3 m5 - 1
    let p3 := minCov (B 3) m2 m4 m5 - 1
    sc + p0 + p1 + p2 + p3 ≥ 20

lemma checkAll_true : checkAll = true := by
  decide +kernel

lemma optOf_lt5 (f : Fin 6) (L : List Nat) : optOf f L < 5 := by
  dsimp [optOf]
  split_ifs
  · omega
  · generalize L.filter (inFam f) = lf
    rcases lf with _ | ⟨m, _ | ⟨m2, t⟩⟩
    · dsimp only; omega
    · dsimp only
      split_ifs <;> omega
    · dsimp only; omega
  · omega

lemma bound_all_ge_20 (c0 c1 c2 c3 c4 c5 : Nat)
    (hc0 : c0 < 5) (hc1 : c1 < 5) (hc2 : c2 < 5) (hc3 : c3 < 5) (hc4 : c4 < 5) (hc5 : c5 < 5) :
    cCost c0 + cCost c1 + cCost c2 + cCost c3 + cCost c4 + cCost c5 +
      (minCov (B 0) (famMask 0 c0) (famMask 1 c1) (famMask 2 c2) - 1) +
      (minCov (B 1) (famMask 0 c0) (famMask 3 c3) (famMask 4 c4) - 1) +
      (minCov (B 2) (famMask 1 c1) (famMask 3 c3) (famMask 5 c5) - 1) +
      (minCov (B 3) (famMask 2 c2) (famMask 4 c4) (famMask 5 c5) - 1) ≥ 20 := by
  have h := checkAll_true
  simp only [checkAll, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h c0 hc0 c1 hc1 c2 hc2 c3 hc3 c4 hc4 c5 hc5

end PEqualNP.Outside.L_meta_12408

theorem PEqualNP.Outside.L_meta_12408 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 19 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false = Nat.testBit (p.val + 1) v.val) := by
  rintro ⟨C, hor, hsize, hcomp⟩
  rcases hcomp 0 with ⟨w0, hw0⟩
  rcases hcomp 1 with ⟨w1, hw1⟩
  rcases hcomp 2 with ⟨w2, hw2⟩
  rcases hcomp 3 with ⟨w3, hw3⟩
  let L := PEqualNP.Outside.L_meta_12408.gateMasksFrom PEqualNP.Outside.L_meta_12408.initMasks C.gates
  have hp0 := PEqualNP.Outside.L_meta_12408.minCov_le_one_add_priv 0 C hor w0 hw0
  have hp1 := PEqualNP.Outside.L_meta_12408.minCov_le_one_add_priv 1 C hor w1 hw1
  have hp2 := PEqualNP.Outside.L_meta_12408.minCov_le_one_add_priv 2 C hor w2 hw2
  have hp3 := PEqualNP.Outside.L_meta_12408.minCov_le_one_add_priv 3 C hor w3 hw3
  have hc0 := PEqualNP.Outside.L_meta_12408.optOf_cost_le 0 L
  have hc1 := PEqualNP.Outside.L_meta_12408.optOf_cost_le 1 L
  have hc2 := PEqualNP.Outside.L_meta_12408.optOf_cost_le 2 L
  have hc3 := PEqualNP.Outside.L_meta_12408.optOf_cost_le 3 L
  have hc4 := PEqualNP.Outside.L_meta_12408.optOf_cost_le 4 L
  have hc5 := PEqualNP.Outside.L_meta_12408.optOf_cost_le 5 L
  have h20 := PEqualNP.Outside.L_meta_12408.bound_all_ge_20
    (PEqualNP.Outside.L_meta_12408.optOf 0 L)
    (PEqualNP.Outside.L_meta_12408.optOf 1 L)
    (PEqualNP.Outside.L_meta_12408.optOf 2 L)
    (PEqualNP.Outside.L_meta_12408.optOf 3 L)
    (PEqualNP.Outside.L_meta_12408.optOf 4 L)
    (PEqualNP.Outside.L_meta_12408.optOf 5 L)
    (PEqualNP.Outside.L_meta_12408.optOf_lt5 0 L)
    (PEqualNP.Outside.L_meta_12408.optOf_lt5 1 L)
    (PEqualNP.Outside.L_meta_12408.optOf_lt5 2 L)
    (PEqualNP.Outside.L_meta_12408.optOf_lt5 3 L)
    (PEqualNP.Outside.L_meta_12408.optOf_lt5 4 L)
    (PEqualNP.Outside.L_meta_12408.optOf_lt5 5 L)
  have hsum := PEqualNP.Outside.L_meta_12408.countP_class_sum_le L
    (PEqualNP.Outside.L_meta_12408.gateMasksFrom_lt _ PEqualNP.Outside.L_meta_12408.initMasks_lt _)
  have hlen : L.length = C.size := PEqualNP.Outside.L_meta_12408.gateMasksFrom_length _ _
  dsimp only [PEqualNP.Outside.L_meta_12408.famsOf] at hp0 hp1 hp2 hp3
  dsimp only [L] at hc0 hc1 hc2 hc3 hc4 hc5 h20 hsum hlen
  omega
