import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2309_aux

-- The live-wire search follows L-meta-2331. The first-gate contraction follows L-meta-2539.
namespace Main2331
abbrev Sig := Nat × Nat
def top : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def unionSep (d : Bool) : List Sig → Nat
  | [] => 0
  | a :: l => sep d a ||| unionSep d l
def Valid1 (x : Nat) : Prop := ∀ j, 414 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
lemma top_eq_pow : top = 2 ^ 207 * 2 ^ 207 - 1 := by decide
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 414) := by
  rw [top_eq_pow]; exact pow_add_testBit 207 207 j
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 414 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
lemma testBit_bnot_lt (x : Nat) {j : Nat} (hj : j < 414) :
    (bnot x).testBit j = !(x.testBit j) := by
  simp [bnot, Nat.testBit_xor, testBit_top, hj]
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 414 by omega]
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 414 by omega]
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
lemma valid1_xor {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ^^^ y) := fun j hj => by
  rw [Nat.testBit_xor, hx j hj, hy j hj]; rfl
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 207 * 2 ^ 207 := by
    have hp : 0 < 2 ^ 207 * 2 ^ 207 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
lemma valid_sep {d : Bool} {a : Sig} (ha : Valid a) : Valid1 (sep d a) := by
  cases d
  · exact valid1_and ha.1
  · exact valid1_xor ha.1 ha.2
lemma valid_unionSep {d : Bool} {v : List Sig} (hv : ∀ a ∈ v, Valid a) : Valid1 (unionSep d v) := by
  induction v with
  | nil => exact valid1_zero
  | cons a l ih =>
    exact valid1_or (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
lemma bin_laws {a : Sig} (ha : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p, n⟩ := a
  obtain ⟨hp, hn⟩ := ha
  have land_top {x : Nat} (hx : Valid1 x) : x &&& top = x := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  simp [bin, one, zero, land_top hp, land_top hn, lor_top hp, lor_top hn]
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
lemma land_eq (x y : Nat) : Nat.land x y = x &&& y := rfl
lemma lor_eq (x y : Nat) : Nat.lor x y = x ||| y := rfl
lemma lxor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl
lemma testBit_land (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := Nat.testBit_and x y i
lemma testBit_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) := Nat.testBit_or x y i
lemma testBit_lxor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simp [bne]
abbrev Cov := Nat × Nat × Nat
def ValidCov (c : Cov) : Prop :=
  Valid1 c.1 ∧ Valid1 c.2.1 ∧ Valid1 c.2.2 ∧
  (∀ i, c.2.1.testBit i = true → c.1.testBit i = true) ∧
  (∀ i, c.2.2.testBit i = true → c.1.testBit i = true)
def covAdd (z : Nat) (c : Cov) : Cov :=
  (Nat.lor z c.1,
   Nat.land (Nat.xor z c.1) (Nat.lor z c.2.1),
   Nat.xor c.2.2 (Nat.land z (Nat.xor c.2.2 c.2.1)))
def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => covAdd (sep d a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := Nat.xor c.1 (Nat.land c.2.1 a)
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  Nat.xor c.1 (Nat.lor (Nat.land c.2.1 (Nat.lor a b)) (Nat.land c.2.2 (Nat.land a b)))
lemma validCov_zero : ValidCov (0, 0, 0) :=
  ⟨valid1_zero, valid1_zero, valid1_zero, fun _ h => by simp at h, fun _ h => by simp at h⟩
lemma validCov_add {z : Nat} {c : Cov} (hz : Valid1 z) (hc : ValidCov c) : ValidCov (covAdd z c) := by
  refine ⟨valid1_or hz hc.1, valid1_and (valid1_xor hz hc.1), valid1_xor hc.2.2.1 (valid1_and hz), ?_, ?_⟩
  · intro i h; have h1 := hc.2.2.2.1 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
  · intro i h; have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1 h2; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases c.2.2.testBit i <;> simp
lemma validCov_coverage (d : Bool) {v : List Sig} (hv : ∀ a ∈ v, Valid a) : ValidCov (coverage d v) := by
  induction v with
  | nil => exact validCov_zero
  | cons a l ih => exact validCov_add (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma cov_one {c : Cov} {a : Nat} (hc : ValidCov c) : takeOne (covAdd a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [takeOne, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1; cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
lemma cov_two {c : Cov} {a b : Nat} (hc : ValidCov c) :
    takeTwo (covAdd a (covAdd b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
  simp only [takeTwo, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1 h2; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_two_unique_disj {c : Cov} {a b : Nat} (hc : ValidCov c) :
    Nat.land (Nat.land (covAdd a (covAdd b c)).2.1 a) b = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [covAdd, testBit_land, testBit_lor, testBit_lxor, Nat.zero_testBit]
  revert h1; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> simp
lemma covAdd_swap {c : Cov} {a b : Nat} (hc : ValidCov c) :
    covAdd a (covAdd b c) = covAdd b (covAdd a c) := by
  have h1 := hc.2.2.2.1; have h2 := hc.2.2.2.2
  refine Prod.ext (Nat.eq_of_testBit_eq fun i => ?_)
    (Prod.ext (Nat.eq_of_testBit_eq fun i => ?_) (Nat.eq_of_testBit_eq fun i => ?_))
  · simp only [covAdd, testBit_lor]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · have h1i := h1 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> simp
  · have h1i := h1 i; have h2i := h2 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i h2i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_perm (d : Bool) {l r : List Sig} (hl : ∀ a ∈ l, Valid a) (h : l.Perm r) :
    coverage d l = coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    exact congrArg (covAdd (sep d a)) (ih (fun x hx => hl x (by simp [hx])))
  | swap a b t =>
    exact covAdd_swap (validCov_coverage d (fun x hx => hl x (by simp [hx])))
  | trans h1 _ ih1 ih2 =>
    exact (ih1 hl).trans (ih2 (fun x hx => hl x (h1.mem_iff.2 hx)))
lemma cov_union (d : Bool) (v : List Sig) : (coverage d v).1 = unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = sep d a ||| unionSep d v; rw [ih]
def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))
def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))
lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    rw [← List.mem_toFinset, he]; simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _, hv.filter _, ?_⟩
    intro a ha b hb eq; subst b
    simp [keepOf] at ha; simp [dropped] at hb; exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset, List.mem_append, List.mem_filter, keepOf, dropped,
      decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, memv]
    by_cases h : x ∈ del <;> simp_all
lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd, hv.filter _, ?_⟩
    intro a ha b hb e; subst b; simp [dropped] at hb; exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset, List.mem_append, dropped, List.mem_filter, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) :
    v.length - 1 = (dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a) = unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_one (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length - 2 = (dropped [a, b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b) = unionSep d (dropped [a, b] v) := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a, b] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_two (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest_disj (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    Nat.land (Nat.land (coverage d v).2.1 (sep d a)) (sep d b) = 0 := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  rw [cov_perm d hval p]
  exact cov_two_unique_disj (validCov_coverage d (fun x hx => hval x (List.mem_of_mem_filter hx)))
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩
lemma sep_unary (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) (neg a)).testBit i = true) :
    (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, neg, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot (valid1_bnot ha.2), testBit_bnot ha.1, testBit_bnot ha.2,
      hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simp only [sep, neg, ht, ite_true, Nat.testBit_xor,
      testBit_bnot ha.1, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
lemma sep_binary (t d : Bool) {a b : Sig} (_ha : Valid a) (_hb : Valid b) (i : Nat) (hi : i < 414)
    (h : (sep t (bin d a b)).testBit i = true) :
    (sep t a).testBit i = true ∨ (sep t b).testBit i = true := by
  cases t <;> cases d <;>
    simp only [sep, bin, Bool.false_eq_true, ite_true, ite_false, Nat.testBit_xor,
      Nat.testBit_and, Nat.testBit_or, testBit_bnot_lt _ hi] at h ⊢ <;>
    revert h <;>
    cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> simp
lemma sep_weaken (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) a).testBit i = true) : (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simpa [ht] using h
lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 414) :
    ∃ a ∈ S, (sep (decide (0 < t)) a).testBit i = true := by
  induction h with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [sep, target, Nat.testBit_and, testBit_top, testBit_bnot valid1_zero, hi]
  | unary ha _ tail ih =>
    obtain ⟨x, hx, h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ, decide_true]
    rcases hx with rfl | hU
    · exact ⟨_, Finset.mem_insert_self _ _, sep_unary _ ha.1 i hi h⟩
    · exact ⟨x, Finset.mem_insert_of_mem hU,
        sep_weaken _ (live_proper tail x (Finset.mem_insert_of_mem hU)).1 i hi h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨x, hx, h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ ha.1 hb.1 i hi h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU), h⟩
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).testBit i = true ↔ ∃ a ∈ v, (sep d a).testBit i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih =>
    simp only [unionSep, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset = S) :
    unionSep (decide (0 < t)) v = top := by
  have hv : ∀ a ∈ v, Valid a := fun a ha => (live_proper h a (he ▸ List.mem_toFinset.mpr ha)).1
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_top]
  by_cases hi : i < 414
  · simp only [hi, decide_true]
    obtain ⟨a, hm, ha⟩ := live_sep h i hi
    exact (mem_unionSep _ _ _).2 ⟨a, List.mem_toFinset.mp (he.symm ▸ hm), ha⟩
  · simp only [hi, decide_false]
    exact valid_unionSep hv i (by omega)
lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l ++ r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep, ih, Nat.or_assoc]
open PEqualNP.CircuitLowerBounds
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ valid_zero rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' ≤ k + 1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
lemma extract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pull_gate ht (gate_rep hw g (legal g (by simp))) hs
    exact ⟨l, u, T, by simp; omega, hu, hT⟩
def bit (side : Bool) (i : Fin 414) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
lemma run_bit (s i) (g : Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil => exact (bit_neg s i valid_zero).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_neg s i (valid_getD hw a)
lemma execute_bits (gs : List Gate) (s i) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ hw' (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit s i g w hw (hg g (by simp))]
lemma foldl_append_getD {α : Type} (f : List α → Gate → α) (gs : List Gate)
    (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (l ++ [f l g]).length := by simp; omega
    rw [ih (l ++ [f l g]) hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
def raw0 : Sig := (0xc4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f, 0x15115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07)
def raw1 : Sig := (0x10c000000000000003ffc000000000003ffffffe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279, 0x208e08e08e08e08e08e08e08e08e08e08e08fe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038)
def raw2 : Sig := (0x218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0, 0xc50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0)
def raw3 : Sig := (0x430000000003ffc000000000003fffffc00000084208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480, 0x1a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000)
def raw4 : Sig := (0x60000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802, 0x2a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000)
def raw5 : Sig := (0x2883ffc003ffc000000003ffc0000000000000010842084210822109042108882108917fffffc00802010fffffffffe000101004, 0x6c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000)
def raw6 : Sig := (0x1100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020, 0x3703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff0000000000000000000)
def raw7 : Sig := (0xa00000003ffc003ffc000000000000000000003ffffff0002080003ffffffffffffffa108211000041004208821085000002100, 0x3383383383383383383383383383383383383fffffe0000000003ffffffffffffff8000000000000000000000000000000000)
def raw8 : Sig := (0x3403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000, 0x3c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000)
def raw : List Sig := [raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]
def symKey1 : Nat := 0x32799cc653399bc965b2b9acee5e25108bc5a2b1488c66271887c3ab558afd7abb5cacd86b760abd5a9d4ca9d4aa350a6d569f54a5d2a3d1c91c8a43208ec963f248dc6afd7cc1e0b0380bee16ff84bddeae570bbddaeb74b8de6e778b7dba0d0485c2a130882c360f0c81c0a6d349dcea73389acf66f3c99cca552897cba5b2c94cc6573093c9acd64b5daad368b2db6cf6cb1d8b1588c7e3b1b8cc4e471790c3e1a8540a3d1a8b44a0d2687489fcf90a8342219046c351acda693a9cce87639168ac582b96cb2542914caae774391cae67192890492591c482211885b0d96a359aad76934d9ed0688c05c2f188b41a090582818080301d7cbd5fb0580bc5c2dd72bb5d2cd64b45b2d55cad57ac560aa54ab156803f1fd027d3319cd0653c9ecf07a3e1dcc26031190c65d2e178be70379c4dc4e27944a04c26bfa02ff803f54aa85329d489b4f2713e9d4d3d1eef57b3cd1c9047a35f2fc7d3edf0a15128d40964aa5d329848a492893773c9daf077bc5d2ec753ad148945a310e886fb89c0e16f108884521918821e1007c3a381d0ec723c1b85c32180d05996ce663359429150ac58280201406dd6db71b43f1f1007a1c0d8cc6a341b0c8241109854280e0784192c563b1990c46130c4c27128000202
def symKey2 : Nat := 0x32995cce6b3796c9e63399dcbe4a411f8ec6a43259247a471b8e48a592b94c9a5b31984aa5f27944bab95bacd5abb61b056abf57ac57ad167b2d8ad36db659ad763b25aae973b8dbaeb79bc5caef6fb85da71379acca733d9e4da77339a4ea291388c3a2b198c44a2f0f8845aa14fa6d2aa355aa53aa74ba654b017fbedeb0385c25fb077bbe60b198bc4e1b1b91c862b1f87c463a8943a0cfa8b49a450a8f3fa051a110782c0a130d8641a17038242972b85dae96eb459ad96ab24ba5932984aa71369e4fa75349248a51267b3d1e4f8773c188c26431980bc5d2f97076391c0e878371a8d066361904c24150a04430170c8682c0f070417ebe60b0178bd7fbfa03007ebe9f2fc7dbe14ca55429d48a250a8d40af572c560ad552b156a977bc1dcf278bb5eaf47bbd9e6ea74bb1d68b45231128e4823d1a87442110a864120cd66c369a4d4e57439dcce372124944b23920462410888fe80409f4fc6734194cce06fb89c2de6db75b8da219148444231047c3f200f43e1e10074381b3a1d4ec723995cb4582d964ac532a154a4d56cb59b0d76a341a6d268b3c5e30188b45c0a0682c1809038200c70389b8de4f289409c4d263198ec96431598cb6733594c26230c5629150b05026138940202000100a03
def rawPermCodes : Fin 12 → Nat := ![0x876543210, 0x267143850, 0x374268501, 0x364872105, 0x547068321, 0x146072385, 0x846375012, 0x247361058, 0x64175832, 0x74561238, 0x567840123, 0x176240583]
def perm1 : Fin 9 → Nat := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
def perm2 : Fin 9 → Nat := ![1, 0, 5, 8, 6, 2, 4, 7, 3]
def gOfV : Fin 9 → Fin 12 := ![0, 2, 6, 10, 0, 4, 2, 4, 8]
def recipeFuel : Nat := 12
def recipeBuckets : Nat := 128
def recipeWidth : Nat := 8
def recipeMask : Nat := 255
def recipeEntryBits : Nat := 48
def recipeEntryMask : Nat := 0xffffffffffff
def recipeShift : Nat := 0x1090409000301000500000002030803000000000101000201000c150a060404010000000000020000000300000d00010000000000030000010000000000030000000200040000020200000001010505000002000005050201010000000001000b0000010104000000010200000000000000000000000102000000010802
def recipeData : Nat := 0xc2900000bc36c29000000000000000000ac6c21000000000000000000000000000c1bc19c640000cac6c24900000000ac69000000cac2970000000c4c630000c1cac6230000000000a300000bc19c64000000cac2360000000b1c64000000cac633000000000c230000cac2c634000000000c3900000000ac16c3bcac297c29000000cac3640000000c9c160000000c6c2900000bc63c140000000c1c36000000cac2610000000c4c2300bcac297c2900000000ac13000000000001cbcac297c299000000cac16900000bc29c1400000cc13c6400000cc36c2400000000000000000000ac19000000cac64200000bc14c2600000000000000000000000200000000000000000000ac630000000c2c6300000c4c1c9600000bc94c160000000000000000000000000000000000000000000c2c4100cac9c14c9400000000000000000000000000000000000000000000000000000000000000000cc92c64000000000000c1bcac297c2900cac2c41c24000000000c3400000c9c2c61000000cac264000000cac16100000000ac120000000000040000000000000000000000000000000000000000c1cac9270000000c4c6900cac2c63c26000000bac6340000000000070000000c9c1400000000000600000cc19c2400000000000000000000000000000000000900000000000000000000000000000000000000cac4c63c460000c1cac4150000c3cac638cbcac927c925000000000000000000cac6380000cac2c631cbcac297c2980000c3cac92700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ac940000c9cac145000000cac14500000000000000000000000000000000ac26000000000000000000000000000000000000000000cac36600000bc16c260000000c6c410000cac2c6380000c3cac1450000c1cac269000000000c1400000000ac2400000bc14c64000000000c640000000000050000000c3c140000cac2c63900000000ac6400000000ac14000000000000000000000000000000000000000000ac6c41000000000c240000000c9c360000000000000000000000000000000000000000000000000000c9cac461000000000c2600cac2c46c2600cac2c63c63000000000000000000000c940000000000000000000000000000000c1c390000000000000000000000000000c9cac4660000000000000000000000000000c4cac297000000000000000000000000000c7bc19c64000000000000000000000000000000000000c4bcac927c92000000cac46100000cc41c3900cac4c63c630000c3cac4610000000000a90000000000a6c6bcac927c92000c3bc19c64000000000000000000000000000000cac623000000000000000000000000000000000000000000000000000000000000000000000c120000000000a400000000ac340000000000080000000c3c920000cac2c64300000c3c6c210000c1cac622000000000000cbcac927c9220000c2cac4150000000c3c1200cac3c14c34000000000000000000000000000000cac1630000000b1c2600000bc14c240000000c9c34000000cac644000000cac14400000cc26c39000000cac639000000000c63000000cac6430000000000000000000000000000000000a2000000000000000000000c19000000cac466000000000000000000000000000000000c16000000000c130000000000000000000000000000000000000000000000a100000cc14c2600000000000000000bc26c3900000000000000000000000000cac2c63c2300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000bc41c39000000000000000000000000000000000000000000000c6900000000000300bcac145c140000000c1c92000000cac3620000000c6c2100000000000000000bc12c9400000000000000000000000000000000000000000000000000000000ac290000000c2c64000000000000000000cac64900000000000000000000000000000bc19c24000000000000000000cac631000000000000000000ac2c640000000000000000000c4c29000000bac641
def wireCount : Nat := 161
def wireEntryBits : Nat := 10
def wireEntryMask : Nat := 1023
def wireTable0 : Nat := 0x3de7fffffffffffc003fffffffffffc000003fffbdefbc077c0077ffbef7bbddf7bdbb03fd83c1fdd003f07bfef41de1bf7b802f1bf000000000ffffff000ffffffffffffffffff39cff9fe73ffe7f937fff91dffff9fbf2fff1faffffff3e39ffff8cfbffffff7d77c003ffc003ffffffffc003ffffffffffffffef7bdf7bdef7ddef6fbdef777def76e8000003ff7fdfef0000000001fffefeffb2ff000000fff000ffffffffffffffffffffffff00000000000000007def7bffdf7bffef7bef77bbddf775efbbef7bdffef7bffffef3ffffffffffffffc003fffffffffffc0000001f07dfe83fef03dfdf7bdc0f03de1df7bef77bbeefbbae81e07fa0fa183dfd86fceffffffffffffffffff000000fffffffff000f7bc07fdee03fe07f81f07fbbe07f07ef7deef703c0f0fdf77def7b775e0707c3bcfffffffffc003fffffffffffc000003ffffff7bdf7bdef7deefbb7003ffbb0001ffef606ff7600f77fdf7a0037ff768003b7f000000000000000000000000000000000000000f87ff807f1fc3ff803e180103ff8000000600007c620801207e1040021ff81000480000000003ffc000003ffc000000000000000a52fe4294ff117e40c630000a3181014bf9440188a03028a7ffca12004311004800fff0000000000000000000000000000000004a53fa1295fc89fa03e8800009fa0014a7f48007c220829257ffa420001f81002887ffc003ffc000000003ffc000000000003ffd284a28425092252904a128982528b37fffffc00902414fffffffffe02052120d020000000000000000000fff0000000000000006018a000c0280c5003e140303ff8240318633007c4a0407f8fe11fc821ff8501173c003ffc003ffffffffc000003fffffffffffff6f837b7e81dfc36e0dc37f6fc37e2884108bdc1f07c717e1f805f1df7c3c3f9feefffffffffffffffffffff000fffffffff000f7bc87fdee23fe47f91f47fbbe47f47fffffff723c8f4fffffffffff75e4747d1738003ffc003ffffffffc000003ffffffffc002d6b017b5a80dd816e05c1766d817408000003dc0f03c30000000001dd781c1f0d0cffffff000fff000000000000ffffff000000ffffffffffffffffa3ff84113fff8014a7f48a67fe2a8a9257ffa42225fff120034c000000000003fffffc003ffc000003fffffc00000000000000007000e73300016e80000016600554d0000000001768002b7b18e000000000ffffff000000000fffffffff000318c31fe62ffe61133ff1119bfff913f27ff0fa7ffff03e317fff887b5fffff436dffffffc003fffffc003fffffc003ffffffffffffffffffffffffe5fcbf4338ff27efe32fe7f3fafffefc731cff3be6cff7fdfbbffff000fffffffff000ffffffffffffffffff7bdffbfef7ffeffb77fffb3fffffbfffffffffaffffff3ffffffffffbffffff7c01c000000000000000000000000003ffffffffc6018a030c0318c600f8820300fe2621802980c1f20cc4306018cc30c60fe46d9003000000000000000000000000000000ffffff18c7f8fe31ffe3f80220880c038818920012090442199241806090c118388096753ffffffc003ffc003ffc000003fffffffffffffffffffffffffffeaffe33f4ffffe25adfdaaddff8ee7b7f5ffedf8df7ffc6f9143000000000fff000fff000000000000fffffff93e290df20c7f190a3108fc3f8c7882144221146411145f87f017c179f8c09e4084000000000000000003ffc000000000003ffca02a20014090152004a52050fd283214bf9440091241428a7ffca120a7d2120df73ffffffffffff000fffffffff000000ffffffffffffffffffffffcff9fefe7ffe7fdffffff9dfe7f9fffffffffff9fbffcf9ffcc7fffffffffffc000003fffffc000000003fffffffffffffffffff1fe3f899a7f8bf7fffffe33f8fe3efffffffffe22c7f3e0f831fff000000000000000ffffff000000000fff4a53fa1295fc89fa07e0f80441f80f918c31908fc3f0f230cc318c688a1f8f83e087ffc000000000000003ffc000000000003fffe8fa2857d092fd28048120108520324630c64009024148c330c631a02452120df6fffffffffffff000ffffff000ffffffffffffffffffffffffffffebffceff3ffffcdffffffb77febbdffffffffffb7dfff5bf75fffffffc003ffc003ffffffffffffffffffffffffffffffffffffebffff3f5fffffe5effdeefffffeffbff7ffeffaffffffefffb0fffffffffffffff000ffffff000000000000ffffffffffffffffd610f702e0840779cc19dccc23cceb306c10cc3c83084e418f38000003fffffffffffc000003ffffffffc0008420842108211045effc0feeffffc1b9dfb99cdff09c173cdffdce5dd7ffc5f038c000000fffffffff000000000ffffff000000210821084208441173ff0313bfff806c67ec4627fc26018237ff601625fff1603e03ffffffffffffffc000000000000000000003ffffffffffffffff48421c0a821001e31063311088322c41904310d004210100fbcfffffffffffffff000ffffffffffff00000027c9f7fa4ffbc4f7f7fff713ffff877deffddeefffeeeba27fffe83ea7ffff61bdfffffffffffffc003fffffffffffffffffffffffffffffffffffffbffffbfdffffff7fffffefffffefffffffffffeffffffeff3cf000000ffffffffffff000000fffffffffffff93e290df20c7f197bff0bffbffff8ee77ee6737fc3715dfb7ff77d77dfff1fe4b0c000003ffc003fffffc000000000003ffffffe0f82017c010fc2160842ffafc21e3a9412994411054557e9f815f55e7c20379921fff000000fff000000fff000000000000ffffb3eab1df62cff5b03f0480421fc0c918c319007e0b05230cc318c68091fc58375cffffffc003ffc003ffffffffc000003fffffffffffffffffffffe3fc7f3f1fff1fe4e71cee77f9fe7f9ff3fc67fa7efff3e7f963fff000000fff000ffffff000000000fffffffb3eab1df62cff5b0bf148fc3ffc7c939c73b117e4b1567fcff19fe979ffc59f4ac4000003ffc003ffc003fffffc000000003ffc210fe00847f007e15f83ec1b07e03fa520a5523f0fd3c482a0852172287e3f0f900fff000000fff0000000000000000000000006318a318c628cc53023100303f8c20129452a0046400025fc7f097e021f8c0000404000000003ffc000000000000000000003ffca52fe4294ff117e408c62050fe302200110000119842400a1fc00100a7e30209131000000000fff000000ffffff000000000fff294bf90a53fc45f907f0f80461fc0f810c21108fe3f0f0208c3108488b1fcf83ff0bfffffffffffffffffc000000000003ffc003ffffffffffffffff68421faa8211c1eb506bb55088363d7590435ed544210170beefff000fffffffffffffff000fffffffff0006318a318c628cc537bff43fbbffff47ffffff737fca747ffffffffff75fff57d3cf7fffffffffffc000003fffffffffffc003fffffffffffffffffff9ffff8ddfffebf7fffffebbfffebefffffffffeabffffe8f6df000ffffff000ffffff000fffffffffffffff9ce75ce739d733acfc0fbfffde03fbee73ce6ff81f5fbdcf33ce7397fee03afee4b3ffc000003ffc000003ffc003fffffc0000018c628c6318a3314c8ffd0044fffe1056bfd6489ff2890acb7ffeb1a897ffd484ba0fff000fffffffff000fff000000000000000ffffffd8c6aacc53fffffffffffffff9ce39d407e1a44338ee39ce7c011fcd412483ffc000003ffc000003ffc0000000000000018c628c6318a3314c0fc1000087f0104630c6401f828108c330c631a0047f1404101000000000fff000000000000000000000ffff93e290df20c7f1903f0080421fc088004200007e030101084310440091fc1827673fffffc003fffffc000003ffffffffc000003fffffffffffffffedb5ad40782d60cc210423bb6edbaa8411042109a1c2ded82dd3ffffff000fffffffff000fff000000ffffffffffffffffffffff9e10bdcce0845bb084108ddc235dbe1044108425db084adef70bfffffc003ffffffffc000000000003ffc003fffffffffffffffe68421722821140c2104235508836384110421095442101705df000fff000fffffffff000ffffffffffffffffdff7deffbdf7fbdbef7bdfdffbdfba210422ffdff7fbc5f87e017c7fffbfbfeedffffc003fffffc003fffffffffffffffffffffedffec7fdff3ffedbfffebfdffffff7fffffceffffcfdfffffffffeffffffeff12d000000000fff000000fff000ffffff000fff290aa908522c455923ff48153fff8c852fe51227fcb250a29fff284a2dfff5a356f4003ffc003fffffc003fffffffffffc003ffcb72ff7a96ffd17f6dffff457fffe3e94bf947bbffffbe28a7ffca13abfffff8f4f3000fff000000ffffffffffff000000fffffffcfffce7f9ff3ffc9fe1fdfcfff87fa318633ddfc7fdfc7f8fe11fcdfbff8fdffef7ffffffffffffffc003fffffffffffc003ffd3f4fffea7fff27ffdffbfc9f27febffffffffbbfeffbeffffffffffa387fff8f5bd000fff000ffffff000ffffffffffff000fff0dc3fdea1bff41fdb7f6fd05c1fd8fa108211eeffbfef8208821084e8e1fffe3d2c4003ffc000003ffc003fffffc000000003ffc330ff38867fc07f25f83f41307e03e842084733f0ff3e08220842132287e3f0ffbcfffffffffffffff000ffffffffffff00000067d9f7facffbccf7f7fff733ffffa77ffffffeefffeeebfffffffffea7ffff61bef3ffffffffffffffc003fffffffffffc0000011f47dfea3fef23dfdf7bdc8f23de9dfffffffbbeefbbaffffffffffa183dfd864d3000fff000000ffffff000fff000000fffffffcff5ce7f9d73fac9c21bdfcff087ba210422dd8475dbc5f87e017c5fbf08aded30c003ffc000003fffffc000000000003fffffff2f83397e01cfc32608437f2fc21e2884108b5411074717e1f805f15e7c20379ef3fffffffff000ffffffffffff000000ffffffdef7fef7bdffbbfedfe0ffeec1f87ffbd83bfddfc3fdff7de821dffdda1f8fdfff7bfffffffffffffffffc003fffffffffffc003fff19ffffc6ff8dffffc9fffffffc9fffffbbffff1bcbfffffffdedfffffcdf2fceffffffffffffffffff000000fffffffff000f7bc27fdee0bfe17fbff07fbbffff07ef7feef77fc2f0fdf77fff7b775fff17c177c003ffc003ffffffffc003ffffffffffffffef7bdf7bdef7ddef6fffef777ffff6e909f903ffffdfef2085ffc801fffffeffb5ce000fff000fffffffff000000fffffffff000b5ac25ed6a0b7615bbff05d9bfffd02427e40f77fc2f0c8217ff200775fff17c3fbbffffffffffffffffffffc003ffffffffc003def29ff7b8aff95feffd1feeffffd1fffffffddff2bd3ffffffffffdd7ffd5f4ef3fffffffff000ffffffffffff000000ffffffdef7fef7bdffbbfedfe8ffeec9fa7ffffffffddfc3fdfffffffffffdda1f8fdffbebffffffffc003ffffffffffffffc003ffc003ffd31bfffccee99bf6319fff318dd9ffffffffec4335bffffffffffff91899764da000fff000000ffffff000ffffff000fff000ffe444ffff133224fc8425ffc421523ff9000ff9104d2ffff8840007fe42225cbb8bffffffffc003ffffffffc000000003ffc0035ad21bd6b08ee91b64211faa2109d1fffffff54802353ffffffffff540101174fceffffffffffffffffff000000fffffffff000f7bc17ffeefffe07f85f17fbbe17f17ff7dfeff0bfff0fff77deffb7f5e17ffc3adbffffffffc003ffc003fffffc003fffffc0005b175bf8b7ff8b9b510bdc2b08425dff227f7f222fffaf85a10be2fe48847fd6006000000000000000000000000000ffffff0001004000c200c6200004200080210900600860300883300c100423083102111b43ac7ffffffffc003ffc003fffffc000000003ffc3b0ffbc877fe07fb5f83fc1b07e03fe720e7733f0ff3ec83a08721f2287e3f0f001000000000000000000000000000000000fff08022800100c011803e0080401f8088000200007c030100080210040081f818274c7fffffc003ffc000003fffffc000000003ffffffffffffffffffe1fc3f01187f03e4630c6633f8fe3e8c330c631a22c7f3e0fd3dffffff000fff000000ffffffffffff000fffffffffffffffffffa7fffc157fff8f95aff59aeffffafab2dfffac6aafffffa3fc83fffffffffffc000003ffc000000000000003ffffffffffffffff0c631888a318917fffffe1188a232fffffffffe004311004f2cffffffffffff000000fff000ffffff000000ffffffffffffffffe3ffc6333fffa45ffffffa67feaacbfffffffffa25fff52113cc003ffc000003fffffffffffc000003fffffe739ff39ce7fccff27f83f73307e17e842084777f0ff7f08220842137687e3f7f5ff000fff000fffffffffffffffffffffffffffbdeffdef7bff77fdbffffdddffffdfa52fe51ffffffffca29fff284fffffffffc4b0000000003ffc000003ffc003fffffc0000008422842108a111448ffd0044fffe1014bf94489ff289028a7ffca12897ffd484b3dfff000ffffff000000ffffffffffff000fff6b5bfb1ad7fccdfb67fffa377fffafdffffff2affff2f3fffffffffaafffffa3fbcfffffffffc003fffffffffffc000003ffffff7bdf7bdef7deefbb7423ffbb2109fffffffff7680f77fffffffffff768103b7f4d3000fff000000ffffff000fff000000ffffff9ce75ce739d733ac9c00bdccc0005ba000000dd8035dbc0000000005da000adec5fc000000003ffc003fffffffffffffffffffffe5ffe43fcff1ffe4bfffe3f5fffffe1cff9cceffffcfd3fe7ffcff2ffffffeffeb0fffffffff000fff000ffffff00000000000046d1d6f28df388e6d508f722c842277ffffffcca03ccebfffffffffc82040e41977c003ffc003ffffffffc003ffffffffffffffff7fdf7bfef7dfef6fffef7f7ffffee98df98bffffdfef37e5ffcdf1fffffeffb490000fff000000fff000000fff00000000000004c154e209d300a49400b500c000032000000cc8034ca8000000000482000a40977c003ffc003ffffffffc003ffffffffffffffef7bdf7fdefffdef6fbdef777def76efc027c3ff7fffeff84010be21fffeffffb55d000fff000fff000fff000fffffffff000fffad6b6d095b0855bdafffacd57fffca8427e4027ffc22bc8217ff20026ffff12afdf7fffffffffffc003ffffffffffffffc003fffbdefbc677ca377ffbfffbbddffffbb7fffffc9fff28bffffffffffe9bfffd4afa24fff000fff000000000fff000000fff000000421082188428c842414a42220a52a45ffffff20288a243fffffffffa002515213fe7ffffffffffffffffffffffffffc000003fffffffff477e8a77ffffffffffffffffffffffd1fdd613fffffffffff1bf7bb12ff79ffffffffffff000ffffffffffff000000fffef7bef11df209dffefbdeef77def6edffffff07f7480fffffffffff86fdee40bca00000003ffc003ffc0000000000000000000014a524b000208000145294caa294ad5a1082110000410042088210850000021007d9000fffffffffffffff000ffffff000000fffffffffc15b8215bdffffffffffffffe84208447d7504bd08220842146fdae84ae09bffc000000000000003ffc000003fffffc000000000fa91f7a908000000000000005ef7deee0a2bed0bdf77def7ae40945ed4559000fff000fff000fff000ffffff000000fffad6b6d015b0015bdaeb5acd575ad4a800000007d7400bc00000000006fdae00ac2dc000000000003ffc003fffffc003ffffffffc631fe3f8c7ff8fe05f8be4330fe27efc22fc7e3f2fffcf86218fe33e68fe7fdf59e000fff000ffffff000000ffffffffffff00015c575fe2bffe2b5b6d6b509c2b5933f009f0fedbbffabe10042f887962b7ff4bf9fffffffffffffffffffffc000003fffffffffffffffffffffffff6def7ffaff7bf7ffffffff5bbfff7fffffffffffe7f77ffdfa6fffffffffffffff000fff000000ffffff000ffffffffffffffffd35ad72aaad6b57fffffffc6abffcbffffffffff912d5ff53d8ffffffffffffc003fffffc000000003ffffffffffffffffffffff2ce73bf8ff39f37fffffe5599a677fffffffffe5e7f3127ddc7ffffff000fffffffff000000000fffffffffffffffffffffffff9a739dfcbf9cf9bf94dfafd4efff9fffc7f2ffe7f9f9dffe41cc000000000000003ffffffffc000003ffffffe1ffe01fc7f0ffe03f87e3f1ffe1fe0c618cc67f1fc7d1fe3f847f27effe3e7f14f000000000fff000fff000000fffffffffffff93e290df20c7f192bff08fd3ffff88637e62337fc3314df97ff37c37dfff1be556c003ffc003ffc003ffc003fffffc003fffffff5fdb417ec10fef6bad6b3f5feb5ea08410885f5d046f17e1f805f05ffeb827baf7fff000fff000ffffffffffff000ffffffffffafffafff5fffffa5febfbfefffaffffffffff9fcffff7fffffffffffbff9fffeadfffc003ffc003ffc003fffffc003ffffffffd6b5febfad7ffafe95fabecbb2feafffffffffe3f2fffcffffffffffe68fe7fdfa73fff000fff000000fffffffff000000fffffffa7ffa17f5fcbffa4fe9fafe7ffa7fdffffff19fc7f1f7fffffffff9fbff8f9fc3dc000000000003fffffffffffc003fffffffffe3ffe3ffc7ffffe07f8fe7f3ffe3fefc63fcfe7f3fffdffe3f8fff3feffe7fffbeffff000fffffffffffffff000fffffffffffffbbebbfff6ffff5b7bff5bffbffffdffffffffb7ffff57fffffffffffdffffff6ebbffc003ffffffffc003ffc003ffffffffc001ce72cffb9bffb94dcffd4ceefffed5fffffffe9ffffd0ffffffffffed7ffffd4b6ffff000ffffff000ffffff000fffffffffffffb3eab1df62cff5b6bff4aff3ffffcdffffff337fcb357fffffffffb7dfff5bf473c000000003ffffffffc000003ffffffffffffe6f8e7ffcbfffc64effc67f6ffffe6fcdffcbedffffc5ffe5fffff1ff7fffff9ae7fff000fff000fffffffff000000ffffffffffabe9afff4ffff4a596b5bfebf5afdffffffff92cfff57fffffffffff9f59fff7ce3fffffffffffc000003ffffffffc0000000011d479c423c8223df9e73988d239c997fffffc1bcc203afffffffffe018399006fbefffffffffffffff000fffffffffffffff00057d5f7feafffeaf7f7def72bcaf7b77fffffffefbbffebffffffffff962f7ff5bdeffffffffffffc003fffffffffffc003fffffffdffbc57fc92ffffbef7bbfdffbdfb7fffffc5fdd247ffffffffffe5fffb927f5df000fff000fffffffff000ffffffffffffffffdff7dfffbffffbdbef7bdfdffbdfbbf10df2ffdffffbfff87e2ffc7fffbfffede60003fffffffffffc000003fffffc000000003ffffff002e0802d7ffffffffffffffa1082111b4c412a420882108501829a1020c7000000000000ffffff000000000ffffffffff8be18fff0ffff08186319fcbf18f9bf10df2f90cfff17ff87e2ffc7f9f19ffe5460003ffc003ffc000000003fffffc000000000150594002c0002d69a52900502940800000001b4c002a0000000000018298002aa6fff000fff000fff000fff000000ffffff000529492fea4ffea42514a532a8a52b57fffffff828bff43ffffffffff90251ff5361bfffffc003fffffc000000000003fffffc003fffffffffffffffe494a54228a5244fe127e3f12affe2fc5114bf29e44a57fd0500000fff000fff000000000000000000000000ad6b6d015b0015bd821084002084000000000044200088000000000001084000298fffc003ffc000003fffffc000000003ffffffe8fa2857d092fd2924a52bf8fd29f37fffffc44912455fffffffffe5e7d2127dd43ffffff000fff000fff000000000000ffffffffffffffffffffff8a318cfc3f8c78929452a95466199e5fc7f097e179f8c09e5400003ffc003ffc0000000000000000000000001705d7a82f6d02d608421000021000000000211088222000000000000021000011c000000000fff000000000fffffffff0000002948610a5318443127ff20157fff82052fe402affc6220a29fff2002affff3208a60000003ffc003ffc000003fffffc000000003ffffff294e480083ffffffffffffffb5ac211aa4451086aaea31085ab908a902a38fff000fff000000000fffffffff0000000006b50c21ad7308862658c62374c63265ffffff2ab10c063fffffffffaae462601bb6bffffffffc003fffffc003fffffc003ffc003ffd11bfffc4ee89bf2109fff1085c9ffe46bbfe44134bfffe2135edff9088972443000fff000000000fff000000000000fffffffc3f0c25f8453f8c8a318cfc3f0878929452a95466199c5f87e017c179f0809e44f4000000003ffc000003fffffffffffc003ffca52fe4294ff117e49fffe055fffe3e14bf944abfffcbc28a7ffca12abffffe8fa31fff000fff000000000ffffff000000000fff4a53fa1295fc89fa47e8fa2649fa2fdffffff08fc3f0f3fffffffff88a1f8f83ecb3ffc003fffffc000003ffc003fffffc0000018c628c6318a3314d8ffd08ccfffe917fffffc89ff2890fffffffffe897ffd484458000fff000000000fff000ffffff000000000ffe1447fff5110a4feb5acffd421421ffd52affd7659bffff9840107fec22208bbf3ffffffffc003fffffffffffffffffc00000318c618c63186631bffffff8f61cf9dfffffffffffffffffffffffffb1a1cfda6e60fffffffff000000ffffff000000000000000c63186318c6198c6cb39cee21842645ffffff9566699dffffffffff8408404091bf0003fffffc003fffffffffffffffffc0000021084108421044213ffffff0f41cf1dfffffffffffffff690e43da47b1a1cfda6440000fff000000000fff00000000000000000084210421084110848a318cc0100040129452a95466199c0401000100408000083403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000280000000fff000fff000000000000000000000ffffffc000820000ffffffffffffffe8420844000104010822084214000008401100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020a20fff000fff000000000fff0000000000000004210821084208842410842220842245ffffff002008043fffffffff8000404010060000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff908880210c000000000fff000000000000ffffff000000210821084208441123ff00113fff800427e40227fc22008217ff200225fff1200218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0043000000000000000fff000000000000fffffff83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e40c4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f
def wireTable1 : Nat := 0x3fff3af3af3af3af3af3af3af3af3af3af3af3affffffe07fc007fffffffffffffffff83ff83c1fff003f07ffffc1fe1ffffc03f00077d77d77d77d77d77d77d77d77d77d77d77d0001f87e00ffe0f803fff8003fff879f07ff0f87fffff3e007fff80781fffff1fffff93f93f93f93f93f93f93f93f93f93f93f93ffffffffffffffffffffffffffffff8000003ffffffff0000000001ffffffffffff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0ff0000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffdf71f71f71f71f71f71f71f71f71f71f71f701f07fff83fff83fffffffe0f03fe1fffffffffffffffff81e07fe0fe183fffc7fffabbabbabbabbabbabbabbabbabbabbabbabbfffe07ffff03ff07fc1f07ffff07f87ffffffff83c0f0ffffffffffffff0707e3fffe5be5be5be5be5be5be5be5be5be5be5be5bfffffffffffffffff003ffff0001ffffe07fffe00fffffffe003fffff8003fff000d61d61d61d61d61d61d61d61d61d61d61d61f83ff801f0fc1ff803e000003ff8000000000007c000000007e0000001ff800000014254254254254254254254254254254254240007e00003f003e000000000000000001f800000000000001ffc0000000000000005495495495495495495495495495495495490001f80000fc00f803e0000000f8000007e00007c000000007ff0000000f8000000006c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000000063063063063063063063063063063063063000000000000000003e000003ff8000000000007c000001f87e007c001ff80003ffea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ffff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c307e1f801f1fffc1c1f8fffabbabbabbabbabbabbabbabbabbabbabbabbfffe07ffff03ff07fc1f07ffff07f87ffffffff83c0f0ffffffffffffff0707e3ffea82a82a82a82a82a82a82a82a82a82a82a83fff81ffffc0ffc1ff07c1ffffc1fe18000003fe0f03c30000000001fffc1c1f8000f69f69f69f69f69f69f69f69f69f69f69f69ffffffffffffffff03ff00003fff800007e00007fc00000007ff000001fff0003ffc2102102102102102102102102102102102100000000000000003f003ffff0001ff8000003fe00ffff0000000001ff8003fff00037d37d37d37d37d37d37d37d37d37d37d37d0000007e00ffe00003ff00003fff801f07ff0f87ffff03e007fff80781fffff00003d53d53d53d53d53d53d53d53d53d53d53d53fffffffffffffffc0f83e00003e01e7c007c3e1f0fffcf800003e01e003e3fc700077f77f77f77f77f77f77f77f77f77f77f77f0001f87e00ffe0f803fff8003fff879fffffff87fffff3ffffffffff81fffff1c00010010010010010010010010010010010010000000000000000000f80000003e000000000001f0000000000000000003e00000007007007007007007007007007007007007000001f87e00ffe0f80000000000000000000000000000000000000000000000000003dafdafdafdafdafdafdafdafdafdafdafdaffffffffffffffffc0ffc01f0ffffe0001f80001ff000007e1ffc1f01e7ffc038000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00000a40a40a40a40a40a40a40a40a40a40a40a4000000000000000000000000fc0000001f800000000000001ffc000007c00000000f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7fffffffffffffffff03e0f87c3ff87f9ffffff007c3f0f3fffffffff879ff8f8fc003d7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7ffffffffffffffffc0f83e00003e01e7fffffc01f0fc3cfffffffffe0003e3e070005445445445445445445445445445445445440001f80000fc00f803e0f80000f8078000000007c3f0f00000000000000f8f81c002002002002002002002002002002002002003e0f80007c0007c00000000000000000000000000000000000000000000000000000f7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bffffffffffffffff03ff007c3ffff81ffffff007fc0003fffffffff879fff00e0003dbfdbfdbfdbfdbfdbfdbfdbfdbfdbfdbfdbffffffffffffffffc0fffe1f0fffffe001f80001fffc3c07e1ffc1f01e7fffe3fffff94f94f94f94f94f94f94f94f94f94f94f94fffffffffffffffffc00ff83c00007fff81ffff803ffffe07800f83f86000ff1fffc3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec3ec0000000000000003fffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8fff0f90f90f90f90f90f90f90f90f90f90f90f90000000000000000ffff0783ffff807ffffffffffc0f0fe07ffff83f87fff0703fffe43e43e43e43e43e43e43e43e43e43e43e43fffffffffffffffff0001e0f000001ffe07fffe0003c3f81e003e0fe180001c0fff7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd07c1fffe0fffe0ffffffff83ffff87ffffffffffffffffe07ffff83f87fffff1c003dffdffdffdffdffdffdffdffdffdffdffdfffffffffffffffffc0fffe1f0fffffe7fffffc01fffc3cfffffffffe1e7fffe3ffff8fb8fb8fb8fb8fb8fb8fb8fb8fb8fb8fb8fbf83e0001f0001f00ffff07fffffff87ffffffffffc0f0ffffffffffffffff07e3ffe2ce2ce2ce2ce2ce2ce2ce2ce2ce2ce2ce2cfe0f80007c0007c03f0001ffffc01e1ffe07fffe0003c3fffff83ffffffc001f8000840840840840840840840840840840840840f83e0001f0001f0003e0000000f8000000000007c000000000000000000f80000003d9fd9fd9fd9fd9fd9fd9fd9fd9fd9fd9fd9ffffffffffffffffc0f83e1f0ffe1fe000000001f0fc3c07e1f801f01e7fe3e3f000863863863863863863863863863863863863f83e0001f0001f0003e0007c3ff8780000000007c000001f87e007c079ff800e3ffd7517517517517517517517517517517517500007e00003f003e3ff83fe0f03e01fffe07fffff0fffff81e003e0fe183e3fc70000230230230230230230230230230230230230000000000000000000000003f000000000000000000001f87e007c001f0000000014854854854854854854854854854854854840007e00003f003e000000000fc00000000000000000000001f80000007c000000005445445445445445445445445445445445440001f80000fc00f803e0f80000f8078000000007c3f0f00000000000000f8f81ffffe4be4be4be4be4be4be4be4be4be4be4be4bfffffffffffffffff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8fff0fb0fb0fb0fb0fb0fb0fb0fb0fb0fb0fb0fb0000000000000000ffff07fffffff87ffffffffffc0f0ffffffffffffffff07e0003dffdffdffdffdffdffdffdffdffdffdffdfffffffffffffffffc0fffe000fffe1e7fffffc01fffc3cfffffffffe007fffe07ffffbffbffbffbffbffbffbffbffbffbffbffbffffffffffffffffffc1fffffff07fffffffffff83ffffffffffffffffff07fffc0001a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000000ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff8000000000ffffffffffffffe000000007c000000000000000000f8000000010010010010010010010010010010010010000000000000000000f80000003e000000000001f0000000000000000003e0000000840840840840840840840840840840840840f83e0001f0001f0003e0000000f8000000000007c000000000000000000f80003ffff13f13f13f13f13f13f13f13f13f13f13f13fffffffffffffffffffffe0f03fe1f8000003ffffffff0000000001e183fffc7ffff84f84f84f84f84f84f84f84f84f84f84f84fffffffffffffffffc00ffffc0007fe000000ff803fffc0000000007fe000fffffffe03e03e03e03e03e03e03e03e03e03e03e03fffffffffffffffff0001fff0001e18000003fe0003c30000000001ff80001f8ffffe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7ffffffffffffffffffffffffffffffe000000ffffffffc1f87e007c7ffffffffc0035ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ff5ffe0ffe007c3f07fe00fffe1f0fffffe7fffffc01fffc3cfffffffffe1e7fffe3f000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0003ffdfb5fb5fb5fb5fb5fb5fb5fb5fb5fb5fb5fb41f07fff83fff83fffffffe0ffffe1f801f803ffffffff0001ffc001e1fffffc7ffffe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7ffffffffffffffffffe0fffffff87fe000000fffc3fffc1f87e007c7ffff8ffffffdf7df7df7df7df7df7df7df7df7df7df7df7c1f07fff83fff83fffffffe0f03fe1ffffffffffffffffffffffffffe183fffc7fff7c47c47c47c47c47c47c47c47c47c47c47c407c1fffe0fffe0ffffffff83c0ff87e000000ffffffffc0000000007860ffff1fffdf11f11f11f11f11f11f11f11f11f11f11f101f07fff83fff83ffff83fe0f03e01f8000003fff0ffff0000000001e183e3fc7fff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff07c1fffe0fffe0ffffffff83ffff87ffffffffffffffffffffffffff87fffff1fffdf7df7df7df7df7df7df7df7df7df7df7df7c1f07fff83fff83fffffffe0f03fe1ffffffffffffffffffffffffffe183fffc7ffffa7fa7fa7fa7fa7fa7fa7fa7fa7fa7fa7fa7fffffffffffffffffc00ffffff007fe000000ff803fffc1f87e007c7fff00ffffffea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ea8ffff81ffffc0ffc1ff0001ffffc01e18000003fe0003c307e1f801f1fffc001f8ffffd6fd6fd6fd6fd6fd6fd6fd6fd6fd6fd6fd6ffffffffffffffffffe0ffffc0f87ffff81fffffc3fffffff800fffffe0f8ffffffebeebeebeebeebeebeebeebeebeebeebeebeffff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8fffafbafbafbafbafbafbafbafbafbafbafbafbfffe07ffff03ff07ffff07fffffff87ffffffffffc0f0ffffffffffffffff07e3ffffb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7ffffffffffffffffffffffffffffff801f803ffffffff0001ffc001ffffffffffffae9ae9ae9ae9ae9ae9ae9ae9ae9ae9ae9ae9fffe07ffff03ff07ffff07fffffff86007e00ffffc0f0c0007ff0007fffff07e3ffebeebeebeebeebeebeebeebeebeebeebeebeffff81ffffc0ffc1ffffc1fffffffe1fffffffffff03c3fffffffffffffffc1f8ffffdffdffdffdffdffdffdffdffdffdffdffdfffffffffffffffffffe0ffffc0f87fffffffffffc3fffffffffffffffe0f8ffffffea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ffff81ffffc0ffc1ff0001fff0001e1ffffffffe0003c3ffffffffffff80001f8fffa92a92a92a92a92a92a92a92a92a92a92a92fffe07ffff03ff07fc0007ffc000787ff8000ff8000f0ffff8000007fe00007e3ffea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ea6ffff81ffffc0ffc1ff0001fff0001e1ffffffffe0003c3ffffffffffff80001f8fffbbfbbfbbfbbfbbfbbfbbfbbfbbfbbfbbfbbffffe07ffffffff07fc1f07ffff07f87ffffffff83fff0ffffffffffffff07ffe3ffde51e51e51e51e51e51e51e51e51e51e51e501f07fff83fff83fff003fe0f00001fffe07fffe00fffff81e003e0fe18003fc700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffdf51f51f51f51f51f51f51f51f51f51f51f501f07fff83fff83ffff83fe0f03e01fffe07fffff0fffff81e003e0fe183e3fc7000040040040040040040040040040040040040000000000000000003e0000000f8000000000007c000000000000000000f80000003d13d13d13d13d13d13d13d13d13d13d13d13fffffffffffffffc0f83e00003e01e000000001f0fc3c00000000000003e3e07000f6df6df6df6df6df6df6df6df6df6df6df6dffffffffffffffff03fff8003fff878007e00007fff0f00007ff000001ffff81c003c6fc6fc6fc6fc6fc6fc6fc6fc6fc6fc6fc6ffffffffffffffffc000000000000007fffffc00000000fffffffffe000000000000f7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bf7bffffffffffffffff03ff00003fff801ffffff007fc0003fffffffff801fff0003ffff13f13f13f13f13f13f13f13f13f13f13f13ffffffffffffffffff83ffff03e1ff8000003fff0ffff0000000001ff83e3fffffffedfedfedfedfedfedfedfedfedfedfedfedffffffffffffffffffffffffffffffe007e00ffffffffc0007ff0007ffffffffc0001a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc00000057f57f57f57f57f57f57f57f57f57f57f57f0001f80000fc00f803fff8003fff879ffffff007fff0f3fffffffff801ffff81ffffe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7fe7ffffffffffffffffff003ffff0001ffffffffffe00ffffffffffffffff8003fffffff84f84f84f84f84f84f84f84f84f84f84f84fffffffffffffffffc00ffffc0007fe000000ff803fffc0000000007fe000fffc0035bf5bf5bf5bf5bf5bf5bf5bf5bf5bf5bf5bfe0ffe007c3f07fe00fffe1f0fffffe001f80001fffc3c07e1ffc1f01e7fffe3ffff79f79f79f79f79f79f79f79f79f79f79f79f07c1fffe0fffe0fffc00ff83c00007fffffffff803ffffffffffffff86000ff1fffffbffbffbffbffbffbffbffbffbffbffbffbfffffffffffffffffffffffffffffff801f803ffffffff07e1ffc1f1ffffffffffff78478478478478478478478478478478478407c1fffe0fffe0fffc00ff83c00007e000000ff803fffc000000000786000ff1fffffd3fd3fd3fd3fd3fd3fd3fd3fd3fd3fd3fd3fffffffffffffffffffffffffffffffc007c3fffffffff800003e01ffffffffffffce9ce9ce9ce9ce9ce9ce9ce9ce9ce9ce9ce9ffffff81ff001fffffffffffffffffe007e0007ffc00fc0007ff00007ffff00fffff3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3effffffe07fc007fffffffffffffffffffffffc1fff003ffffffffffe1ffffc03f00001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003fff3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3effffffe07fc007fffffffffffffffffffffffc1fff003ffffffffffe1ffffc03ffffcfbcfbcfbcfbcfbcfbcfbcfbcfbcfbcfbcfbffffff81ff001ffffffffffffffffffffffff07ffc00fffffffffff87ffff00fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff81ff001fffffffffffffffffe00000007ffc00fc00000000007ffff00fc000c7cc7cc7cc7cc7cc7cc7cc7cc7cc7cc7cc7c000001f803ff8000000000000000007ffffffe000ffc0ffffffffffe00003fc0fffce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff81ff001fffffffffffffffffe00000007ffc00fc00000000007ffff00fc001d51d51d51d51d51d51d51d51d51d51d51d500007e1f803ff83e00f83e00003e01e7c007c3e1f0fffcf800003e01e003e3fc7fff7d47d47d47d47d47d47d47d47d47d47d47d407c1fffe0fffe0ffffffff83c0ff87ff001f0fffffffffe00000f807860ffff1c003cffcffcffcffcffcffcffcffcffcffcffcfffffffffffffffffc000001f0fc01e07ffffffe000ffc0fffffffffffe7c03ff8000f1ff1ff1ff1ff1ff1ff1ff1ff1ff1ff1ff1fffffffffffffffff000000000000001fffffff8003ff03ffffffffff80000ff00003cefcefcefcefcefcefcefcefcefcefcefceffffffffffffffffc000001f0fc01e07fffffc00000000fffffffffe1e7c00038000f37f37f37f37f37f37f37f37f37f37f37f37ffffffffffffffff0000007c3f00781f001f0f8003ff03ff87e0ffc7f9f00ffe000359f59f59f59f59f59f59f59f59f59f59f59fe0ffe007c3f07fe00f83e1f0ffe1fe000000001f0fc3c07e1f801f01e7fe3e3f00086b86b86b86b86b86b86b86b86b86b86b86bf83e0001f0001f0003ff007c3ffff80007e00007fc00001f87ff07c079fff00e3fff38f38f38f38f38f38f38f38f38f38f38f38ffffffe07fc007fffffffffffffffff80000001fff003f07e1f801f01ffffc03f000f7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff83ff87ff0fffff803e0f87c3ff87f9fffffff87c3fff3fffffffffff9ff8fffc001d7dd7dd7dd7dd7dd7dd7dd7dd7dd7dd7dd7c0007e1f803ff83e00f83e00003e01e7ffffffe1f0fffcffffffffffe003e3fc7000d7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7fd7ff83ff801f0fc1ff803e0f87c3ff87f9ffffff007c3f0f3fffffffff879ff8f8fc003ddfddfddfddfddfddfddfddfddfddfddfddfe0ffe1ffc3ffffe00f83e1f0ffe1fe7c007c3e1f0fffcffe1f83ff1fe7fe3fff000b7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7fb7ff83e007ff0ffff0003ff007c3ffff81fffffff87ffff03fffffffffff9fffffe0000dfcdfcdfcdfcdfcdfcdfcdfcdfcdfcdfcdfc000001f803ff80000ffc0000fffe007ffffffe1ffffc0ffffffffffe07ffffc000087b87b87b87b87b87b87b87b87b87b87b87bf83e0001f0001f0003ff007c3ffff81ffffff007fc0003fffffffff879fff00e0002dfedfedfedfedfedfedfedfedfedfedfedffe0f801ffc3fffc000ffc01f0ffffe07c1ffc3e1ffffc0ffe1fffff1fe7fffff8000b3fb3fb3fb3fb3fb3fb3fb3fb3fb3fb3fb3ff83e007ff0ffff000000007c3f00781fffffff8003ff03fffffffffff9f00ffe3ffd36d36d36d36d36d36d36d36d36d36d36d36c1f07fe003c0003fffffffe0f03fe1fffffffc1fff003ffffffffffe0183fc007fff7df7df7df7df7df7df7df7df7df7df7df7df07c1fffe0fffe0ffffffff83c0ff87ffffffffffffffffffffffffff860ffff1ffff3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3ef3effffffe07fc007fffffffffffffffffffffffc1fff003ffffffffffe1ffffc03ffffff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ff7ffffffffffffffffffffffffffffffff001f0fffffffffff87e0ffc7ffffffffffff383383383383383383383383383383383383fffffe003c0003ffffffffffffffff80000001fff003f00000000000183fc007000b37b37b37b37b37b37b37b37b37b37b37b37f83e007ff0ffff000000007c3f00781f001f0f8003ff03ff87e0ffc7f9f00ffe3ffd3013013013013013013013013013013013001f07fe003c0003fffffffe0f03fe1f80000001fff003f00000000000183fc00700031f31f31f31f31f31f31f31f31f31f31f31f0000007e00ffe000000000000000001fffffff8003ff03ffffffffff80000ff00003c53c53c53c53c53c53c53c53c53c53c53c53fffffffffffffffc000000000000007c007c3e000ffc0f800003e01e00003fc0000c00c00c00c00c00c00c00c00c00c00c00c00ffffff81ff001fff00000000000000000000000000000000000000000000000000020ee0ee0ee0ee0ee0ee0ee0ee0ee0ee0ee0efe0f80007c0007c00000001f0fc01e07fffffc00000000fffffffffe1e7c00038000f23f23f23f23f23f23f23f23f23f23f23f23ffffffffffffffff0000007c3f007800000000000000001f87e007c079f0000e0001c01c01c01c01c01c01c01c01c01c01c01c001f07fff83fff83fc000000000000000000000000000000000000000000000000000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0000003383383383383383383383383383383383383fffffe0000000003ffffffffffffff800000000000000000000000000000000000001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003ffea4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bfff81ffffc0ffc1ff0001fff0001e1ffe07fffe0003c3fffe003fffff80001f8000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00015b55b55b55b55b55b55b55b55b55b55b55b40007e00003f003e00fffe000fffe1e001f80001fffc3c0001ffc000007fffe0700055f55f55f55f55f55f55f55f55f55f55f55f0001f80000fc00f803e0f80000f8079ffffff007c3f0f3fffffffff8000f8f81c0001ec1ec1ec1ec1ec1ec1ec1ec1ec1ec1ec1ec00000000000000000ffc0000fffe007fffffc01ff0000fffffffffe007ffc000000a92a92a92a92a92a92a92a92a92a92a92a92ffc0007fff000000fc00007fc000001ff8000ff8000003fff8000007fe0000003ffc37c37c37c37c37c37c37c37c37c37c37c37c0000000000000003fffffe0f03fe1ffffffffffffffffffffffffffe183fffc700001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003ffc3703703703703703703703703703703703700000000000000003fffffe0f03fe1fffffffffffffffff81e07fe0fe183fffc700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000000ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff8000000000ffffffffffffffe00000000000000000000000000000000000003703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff000000000000000000000001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000000002a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0000000c50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00015115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07
def frontierCount : Nat → Nat → Nat
  | 9, 0 => 15
  | 10, 0 => 341
  | 10, 1 => 12
  | 11, 0 => 253
  | 11, 1 => 230
  | 11, 2 => 81
  | 11, 3 => 6
  | 12, 0 => 25
  | 12, 1 => 34
  | 12, 2 => 34
  | 12, 3 => 17
  | 12, 4 => 3
  | 13, 0 => 3
  | 13, 1 => 4
  | 13, 2 => 4
  | 13, 3 => 4
  | 13, 4 => 4
  | 13, 5 => 1
  | _, _ => 0
def leafCount : Nat → Nat → Nat
  | 9, 0 => 15
  | 10, 0 => 339
  | 10, 1 => 12
  | 11, 0 => 223
  | 11, 1 => 228
  | 11, 2 => 81
  | 11, 3 => 6
  | _, _ => 0
def frontierSlotBits : Nat → Nat → Nat
  | 9, 0 => 104
  | 10, 0 => 114
  | 10, 1 => 104
  | 11, 0 => 124
  | 11, 1 => 114
  | 11, 2 => 104
  | 11, 3 => 94
  | 12, 0 => 114
  | 12, 1 => 114
  | 12, 2 => 114
  | 12, 3 => 104
  | 12, 4 => 94
  | 13, 0 => 104
  | 13, 1 => 104
  | 13, 2 => 104
  | 13, 3 => 104
  | 13, 4 => 104
  | 13, 5 => 94
  | _, _ => 0
def frontierData : Nat → Nat → Nat
  | 9, 0 => 0x151201e1500201421068099000151404803802014210680990004c1201e0380201421068099130161201e038020142106809a000150481e0340111022090099054280481e034011102209009a0541207840038020182209009a0f0160481e034020182209009a0e0160481e038010182209009a000150d01e0340101822090099054340a01e034010182209009a0002c0481e03401018220900990c0160481e034010182209009a0b0160481e034010182209009a0b0280481e034010182209009a
  | 10, 0 => 0x150481e0340101822090099000150a0120780d004060882402686c180120784003930018220680ab1803c0481e8f00e4c0060881a02ac94058120780e8e002018220680ab0e0160481e100022f0060881a02ac3805812078403405c018220680ab1b0380481e10002170060881a02ae34058120780e0085c018220680ab1b0160481e03802740060881a02ac3805812078404c074018220680ab250160481e10002018680881a02ad98058120780e008061a0220680ab1b0160481e03802019ac0881a02ad28058120780e008060881a8c00ab0e0160481e038020182206a2c02ac00000150481e100b44c05c0680990012805812078402d1300181a0268000e0160481e101301700606809a00114058120780e4c05c0181a0269140e0160481e039301700606809b300160481e1000e4c05c0181a026e180581207840039301700606809b000000e1280481e101300141a0264600581207840039e04c02206809b000600f0120780d781300881a026800250160481e100021702206809a2506005812078400085c0881a026c9405812078402d0021702206809b300160481e100b40085c0881a026c150481e820402d0021702206809b05412078408a0b40085c0881a026c0005412078402d0028902206809a05412078402d002172240881a026c150481e100b40085c7402206809b0009405812078404c0060881a0268940e0160481e101300182206809b2506005812078404c0060881a026c380581207908101300182206809b250160481e100b44c0060881a026d1405812078402d1300182206809b860160481e100b44c0060881a026c150481e820402d1300182206809b0541207908100b44c0060881a026c941803c0481e039300182206809b450600f0120780e4c0060881a026c600f0120792c039300182206809b660160481e1000e4c0060881a026e1c0581207840039300182206809b05812078408800e4c0060881a026e1c1803c0481e035300182206809b182180f0120780d4c0060881a026c380581207840781300182206809b000600f0120780d850060881a0268600f0120780d4c2140182206809b180160481e1000e840060881a026c00058120784003a100182206809a058120784003930840060881a026c600f0120780d4c2100182206809b000150481e100b4730060881a026800180160481e039cc0182206809a180160481e1000e730060881a026c150481e100b44c1cc0182206809b180160481e03930730060881a026e0c250160481e100020182206809b830380581207840008060881a026c380581207a08100020182206809b250160481e4b040008060881a026c1504a04078402d0020182206809b054127201e100b4008060881a026c007c0160481e038020182206809a7c094058120780e008060881a026c1504a000780e780020182206809b054127f01e039e0008060881a026c38058120780e770020182206809b000160481e039dc008060881a026815049f80780e2e0020182206809b055f40481e2d130008060881a026df0058120780e4c0020182206809b054127b01e03930008060881a026c15049e80780e4c0020182206809b05412078b403930008060881a026c160481e039dc4c0020182206809b250160481e039e4008060881a026c00058120780e790020182206809a058120780e4c1e4008060881a026c94058120780e6c0020182206809b058120780e781b0008060881a026c160481e039dc6c0020182206809b054125901e10002170060881a026c3805812079180085c0182206809b000160481e46002170060881a0268160481e101180085c0182206809b054127601e03802170060881a026c151201e1000e0085c0182206809b054120784003802170060881a026c380581207840009d40182206809b0e0160481e10002740060881a026dc00e0160481e101300142206809b0e0160481e4b0404c0050881a026c3805812078404c1b00142206809b000380581207840730050881a02683805812078404c1cc0142206809b0003805812079b8008050881a026800000160481e6e002014220680994a0160496407840008050881a026c38058127201e100020142206809b00038058126d00e008050881a02680000016049b4038020142206809900016049bc0780e008050881a0269280584807840038020142206809b4a0160481e1000e008050881a026c3805812079b84c0020142206809b000160481e6e130008050881a02683805812079604c0020142206809b0e016049b403930008050881a026c00058126d00e4c0020142206809a440380481e03930008050881a026dc4058120780e4c0020142206809b0e0160481e03930008050881a026c38058120792c6c0020142206809b0e0160481e6e1b0008050881a026c0005812079b86c0020142206809a0e016049b4039b0008050881a026c00058126d00e6c0020142206809a700160481e039b0008050881a026c16049bc0780e6c0020142206809b05812079b84c1b0008050881a026c16049b4039306c0020142206809b05412078402d130019ac0881a026c60058120780d2e0026a02206809b1803c0481e03402019a80881a026ca4058120780d008066a02206809b0e0160481e10002015a40881a026d14058120780e008056902206809b450160481e03802015a00881a026c38058120780e008056802206809b0f0160481e03802015a00881a026c160481e1000e008056802206809b000600f0120780d0099c0841a026860058125b01e1000e0182106809b180160481e1000e610060841a026c001803c0481e035840182106809a000a4058120780d610060841a0268a4180160481e035840182106809b660940581207840008060841a026c60058125901e100020182106809b000940581207994008060841a026800000160481e6500201821068099250160481e10194008060841a026c000581207840650020182106809a520160481e100b4008060841a026c600581207990038020182106809b180161201e1000e008060841a026d781801207840038020182106809b180160481e1000e008060841a026c00620600481e034020182106809a62178180120780d008060841a026d78290600481e034020182106809b000600f0120780d008060841a026800290160481e034020182106809a29060058120780d008060841a026c38058120780e630020182106809b0e0160481e580b8008060841a026d100e0120780e2e0020182106809b0e0160481e038b8008060841a026c94058120780e610020182106809b620600481e03584008060841a026c60058120780d610020182106809b250160481e03920008060841a026c60058120780e600020182106809b05812078b403980008060841a026d7c5e0600481e038010182106809b00104180120780e004060841a026978250600481e038010182106809b00094058120780e004060841a0268000581207900038010182106809a250160481e2d00e004060841a026c160481e400b4038010182106809b0e0160481e100025d0060841a026c38058120780e005740182106809b450160481e038025c0060841a026c38058120780e009700182106809b0f0160481e038025c0060841a026c160481e1000e009700182106809b00038058125b01e100050841a026954058125b01e1000e0142106809b450160496c07840038050841a026c000e0160481e101200142106809a00114058120780e480050841a0269140e0160481e039200142106809b0003c058120780e480050841a0268000581207840039200142106809a00038058120791c008050841a0268000e0161201e100020142106809a000155a04807840008050841a026800440380481e100020142106809a001480e01207840008050841a026800560160481e100020142106809a560380581207840008050841a026c000e0160481e100020142106809a000151216407840008050841a026958058125901e100020142106809b450160496407840008050841a026c00054125901e100020142106809a0e0160481e47040008050841a026d140e0160481e580020142106809b0e0160481e47160008050841a026c00450160481e570020142106809a00038058120795c008050841a0268000581207840570020142106809a00114058480780e008050841a026800450165301e038020142106809a000380594c0780e008050841a0268000f0165301e038020142106809a00148450120780e008050841a026954440380481e038020142106809b001480e0120780e008050841a026910450380481e038020142106809b001480f0120780e008050841a026800560160481e038020142106809a00154058120780e008050841a026800450160481e038020142106809a56038058120780e008050841a026d140e0160481e038020142106809b5503c058120780e008050841a026c00058120791c038020142106809a540161201e1000e008050841a026d480584807840038020142106809b450161201e1000e008050841a026c000544807840038020142106809a000165301e1000e008050841a0269480581207840038020142106809b450160481e1000e008050841a026c160481e47040038020142106809b0e0160481e47120008050841a026c38058120780e480020142106809b001100e0120780e004050841a026800054120780d0045c0182209009a054280481e034011700608824026c00000150481e034020142106808900015049440780d008050841a022800054120780d340020142106808a054125101e034d0008050841a022c001b0160481e034010142106808a00000058120780d004050841a02246c058120780d004050841a3e008b000160481e0340101421068f8022800054120780e004060841a0293ca054125001e03801018210680a4f2c150481e2d00e004060841a0293cb000150481e0380201821068094d2815049380780e008060841a02534b05412078b40380201821068094d2c380581207840340050841a0290cb1b0380481e10002014210680a432c3805812078404c0050881a0250cb0e0160481e4b0020142206809432c384a01207840008050881a0250cb0e1280481e038010142206809432d24058120780e004050881a0250cb250160481e100020182106809432c94058120780e004060841a0250cb0e0160481e101200142106809432c38058120791c008050841a0250cb440380481e100020142106809432c380581207840008050841a0250cb0e0160481e460020142106809432c000581207918008050841a0250ca0581207840460020142106809432d14058120780e008050841a0250cb440380481e038010142106809432c160481e100b4008060841a024fcb1803c0481e0380201821068093f2ca4058120780e008060841a024fcb05812079080380201821068093f2d04180120780e004060841a024fcb05812079000380101821068093f2c6c180120780d3400201821068d4b1b0380481e038d0008050841a352c6c0e0120780e004050841a3e0d4b1b0600481e034b8008210680a352ca8180120780d008060841a028d4b1b0940481e03801018210680a352c6c0e01207840008050841a028d4b1b0380481e3d001014210680a352c6c0e0123700e004050841a028d4b26016048dc03801014210680a352c6c3c0120780e004050841a028d4b1b0380481e03801014210680a352c6c3b0120780e004050841a028d4b0e0ec0481e03801014210680a352c003b0120780e004050841a028d4a260160481e03801014210680a352c6c3a0123700d004050841a028d4b1b0e4048dc03401014210680a352c6c058123700d004050841a028d4b1b0e40481e03401014210680a352c6c058123800d004050841a028d4b00016048e003401014210680a352816048dc3800d004050841a028d4b05812370d803401014210680a352c6c058120780d004061a02206870b230160481e034d0008060841a1c2c6c058120780d340020182106870b058120780d340021d0060841a1c2c8c058120780d004060841a33070b1b0160481e0340101821068cc1c2c160481e034011d0060841a33070b180160481e03401170220680a1c2cc8058120780d004060881a02870b310160481e03401018220680a1c2cc0058120780d004060881a02870b058120780d004bc018220680a1c2c60058120780d2e0020841a02870b05812078b4038011d0210680a1c2c8c058120780d004b00841a02870b180160481e034012c0210680a1c2c160481e034011d0b00841a02870b1803c0481e03402018210680a1c2cac058120780d008060841a02870b2a0160481e03402018210680a1c2ca4058120780d008060841a02870b058120780d28002018210680a1c2c6c0e0120780e004060841a02870b270160481e03801018210680a1c2c98058120780e004060841a02870b250160481e03801018210680a1c2c160481e2400e004060841a02870b230160487803401018210680a1c2c6c058121e00d004060841a02870b180160487803401018210680a1c2c8c220120780d004060841a02870b1b0880481e03401018210680a1c2c60220120780d004060841a02870b210160481e03401018210680a1c2c80058120780d004060841a02870b058120780d0047c018210680a1c2c1604878034011d0060841a02870b1b0160481e03401014680881a192c60058120780d0045c0881a02458b
  | 10, 1 => 0x58120784003a100182206809a0003c0481e0361001822068099058120780e770020182206809a000160481e101b001422068099000160481e6e0020142206809900016049b4038020142206809905812079b86c0020142206809a058126d00e6c0020142206809a520161201e038020142106809a0e0123700e004050841a028d4a3a0123700d004050841a028d4a390123700d004050841a028d4a
  | 11, 0 => 0x1b0160481e1000e0085c018220680ac180160481e1000e008061a0220680ac0000005412078402d0021702206809a0000005412078402d1300182206809a000600581207840039300182206809b000001803c0481e035300182206809a00094058120780e4c0020182206809b0003805812078400085c0182206809b000000e0160481e101300142206809a00000058120780e6c0020142206809a0e0160481e039306c0020142206809c000160481e039306c0020142206809b00000250160481e100020182106809a00060058120780d610020182106809b00000054125901e100020142106809a000000544807840038020142106809a000000541207840038020142106809a00038058120780e480020142106809b00000440380481e038010142106809a000000e0160481e038010142106809a000380581207840008050841a0250cb00038058120780e004050841a0250cb000160481e2d00e004060841a024fcb0006c0e0120780e004050841a028d4b0006c058123700d004050841a028d4b0006c058120780d004050841a028d4b0008c058120780d004060841a02870b0006c058120780d004060841a02870b00060058120780d004060841a02870b000160481e034011d0060841a02870b4a0160481e1000e00874018220680ac0f0160481e9100e00874018220680ac0e0160481e038b8008061a0220680ac0003c05812078b4039300182206809b0012805812078402d0020182206809b000150481e4b0402d0020182206809b000150481e102282d0020182206809b000000541207a08038020182206809a0003c0581207a28038020182206809b0021805812078b4038020182206809b8612805812078b4038020182206809c0f0160481e8a0b4038020182206809c00038058120780e780020182206809b000150481e8200e780020182206809b000150481e4b00e780020182206809b000150481e4200e780020182206809b000150481e8a00e780020182206809b000380581207a442e0020182206809b000384a0120780e2e0020182206809b00124058120780e2e0020182206809b49038058120780e2e0020182206809c49128058120780e2e0020182206809c000150481e8200e2e0020182206809b4a0160481e4200e2e0020182206809c290160481e9100e2e0020182206809c0541207a089100e2e0020182206809c0e0160481e039e02e0020182206809c0541207a08039e02e0020182206809c0541207908039e02e0020182206809c25060058120780e4c0020182206809c000150481e8200e4c0020182206809b250160481e2d00e4c0020182206809c860160481e2d00e4c0020182206809c0541207a082d00e4c0020182206809c0e0160481e039e04c0020182206809c0541207a08039e04c0020182206809c054120792c039e04c0020182206809c00114058120780e0085c0182206809b45038058120780e0085c0182206809c4503c058120780e0085c0182206809c000150481e8200e0085c0182206809b300160481e1000e0085c0182206809c0541207a081000e0085c0182206809c0f0160481e8a00e0085c0182206809c0e0160481e039e00085c0182206809c0541207a08039e00085c0182206809c0541207a28039e00085c0182206809c00000054120780e009d00182206809a000150481e03802171d00182206809b054120784003802171d00182206809c00000054120780e00a640182206809a000150481e038b800a640182206809b0541207a44038b800a640182206809c000000e0160481e4b0020142206809a000000e1280481e100020142206809a001240e0160481e100020142206809b00038058120792c100020142206809b001140e0160481e910020142206809b00038058120792c910020142206809b001140e1280481e038020142206809b00038861280481e038020142206809b00000700160481e038020142206809a001c0860160481e038020142206809b00124860160481e038020142206809b001c04a0160481e038020142206809b702184a0160481e038020142206809c492184a0160481e038020142206809c001c0058120792c038020142206809b00114058120792c038020142206809b00124058120792c038020142206809b00218058120792c038020142206809b001c00581207840038020142206809b701280581207840038020142206809c700160481e4b040038020142206809c450160481e4b040038020142206809c001280581207a60038020142206809b000000581207a60038020142206809a4a0160481e10260038020142206809c000160481e10260038020142206809b001c00581207a44038020142206809b701240581207a44038020142206809c7003c0581207a44038020142206809c700160481e4b244038020142206809c490160481e4b244038020142206809c000000581207a5c038020142206809a0f0160481e9125c038020142206809c000160481e9125c038020142206809b00038058120792c4c0020142206809b001c0058120780e4c0020142206809b70038058120780e4c0020142206809c70218058120780e4c0020142206809c700160481e4b00e4c0020142206809c860160481e4b00e4c0020142206809c00000054120780e008066b02206809a000150481e03930008066b02206809b05412078b403930008066b02206809c00094180160481e100020182106809b0009405812078402d0020182106809b0011405812078402d0020182106809b000941803c0481e038020182106809b001141803c0481e038020182106809b00000660160481e038020182106809a00198250160481e038020182106809b00198290160481e038020182106809b00094290160481e038020182106809b00198180160481e038020182106809b66094180160481e038020182106809c660a4180160481e038020182106809c250a4180160481e038020182106809c001980581207908038020182106809b000940581207908038020182106809b001140581207908038020182106809b000a40581207908038020182106809b001980581207840038020182106809b660600581207840038020182106809c660160481e42040038020182106809c450160481e42040038020182106809c000600581207a20038020182106809b000000581207a20038020182106809a180160481e10220038020182106809c000160481e10220038020182106809b0019805812078b4038020182106809b6609405812078b4038020182106809c660160481e420b4038020182106809c250160481e420b4038020182106809c000a41803c0481e034020182106809b00000182580481e034020182106809a000600f2580481e034020182106809b000000f2580481e034020182106809a00000002580481e034020182106809900198058120780e2e0020182106809b66038058120780e2e0020182106809c660a4058120780e2e0020182106809c660160481e4200e2e0020182106809c290160481e4200e2e0020182106809c00038058120780e950020182106809b00000058120780e950020182106809a0e0160481e038b8950020182106809c000160481e038b8950020182106809b00000058120780d610020182106809a0003c058120780d00a500182106809b00000058120780d00a500182106809a00038058120780e005740182106809b00000058120780e005740182106809a001140e0160481e100020142106809b000000e0160481e460020142106809a00000000160481e4600201421068099000380581207840460020142106809b000000581207840460020142106809a00000000151201e038020142106809900000520160481e038020142106809a001480581207840038020142106809b0003c058120795c038020142106809b00000058120795c038020142106809a000009303c0481e034020142106809a000000f0160481e034020142106809a00000058120780e480020142106809a0f0160481e8f00e008050841a02a48c000160481e8f00e008050841a02a48b0f0160481e03402170060881a02648c000160481e03402170060881a02648b0f0160481e9100e008050881a02648c000160481e9100e008050881a02648b0f0160481e2d00e008060841a02648c000160481e2d00e008060841a02648b000600f0120780d008060841a02648b000a4058120780d008060841a02648b2903c058120780d008060841a02648c0f0160481e03402940060841a02648c000160481e03402940060841a02648b00114058120780e008050841a02648b4503c058120780e008050841a02648c0f0160481e5700e008050841a02648c000160481e5700e008050841a02648b0024c0f0120780d008050841a02648b0003c058120780d008050841a02648b0e0160481e038d0008050841a0290cc000160481e038d0008050841a0290cb0e0160481e03801170060881a0250cc000160481e03801170060881a0250cb0e0160481e03930008050881a0250cc000160481e03930008050881a0250cb000384a0120780e004050881a0250cb00124058120780e004050881a0250cb49038058120780e004050881a0250cc0e0160481e03801015a40881a0250cc000160481e03801015a40881a0250cb0e0160481e038b8008060841a0250cc000160481e038b8008060841a0250cb00094058120780e004060841a0250cb25038058120780e004060841a0250cc0e0160481e038015d0060841a0250cc000160481e038015d0060841a0250cb00114058120780e008050841a0250cb45038058120780e008050841a0250cc0e0160481e03920008050841a0250cc000160481e03920008050841a0250cb001100e0120780e004050841a0250cb00124058120780e004050881a02640b49038058120780e004050881a02640c00038058120780e004050881a02640b00000058120780e004050881a02640a490160481e9100e004050881a02640c000160481e9100e004050881a02640b00094058120780e004060841a024fcb00000058120780e004060841a024fca250160481e2d00e004060841a024fcc1b0160481e034b8008060841a028d4c000160481e034b8008060841a028d4b1b0160481e2d00e004060841a028d4c000160481e2d00e004060841a028d4b1b0160481e1000e008050841a028d4c000160481e1000e008050841a028d4b00098058120780e004050841a028d4b2606c058120780e004050841a028d4c1b0160481e3d00e004050841a028d4c000160481e3d00e004050841a028d4b00000058123700d004050841a028d4a0006c390120780d004050841a028d4b2306c058120780d004060841a02870c23060058120780d004060841a02870c00000058120780d004060841a02870a230160481e034011d0060841a02870c
  | 11, 1 => 0x160481e039b0008050881a026800058123700d004050841a028d4a000150481e100b40085c0881a02680005412078402d1300182206809a180160481e1000e4c0060881a026c3c05812078b4039300182206809b000600f0120780d4c0060881a02692805812078402d0020182206809b054120792c100b4008060881a026c150481e102282d0020182206809b000150481e8200e008060881a02683c0581207a28038020182206809b860160481e2d00e008060881a026c38058120780e780020182206809b0541207a08039e0008060881a026c150481e4b00e780020182206809b0541207908039e0008060881a026c150481e8a00e780020182206809b0e0160481e910b8008060881a026c384a0120780e2e0020182206809b490160481e038b8008060881a026c150481e8200e2e0020182206809b250160481e03930008060881a026c150481e8200e4c0020182206809b0e0160481e10002170060881a026d14058120780e0085c0182206809b0541207a0803802170060881a026c00054120780e009d00182206809a054120780e0085c740060881a026c00054120780e00a640182206809a054120780e2e002990060881a026c000e0160481e101300142206809a00038058120792c008050881a0268000e1280481e100020142206809a490380581207840008050881a026c38058120792c100020142206809b450380581207a44008050881a026c38058120792c910020142206809b450384a0120780e008050881a026c38861280481e038020142206809b001c0058120780e008050881a0269c0860160481e038020142206809b49218058120780e008050881a026dc04a0160481e038020142206809b700160481e4b00e008050881a026d14058120792c038020142206809b490160481e4b00e008050881a026e18058120792c038020142206809b700160481e1000e008050881a026d280581207a60038020142206809b000160481e9800e008050881a0268160481e10260038020142206809b700160481e9100e008050881a026c000581207a5c038020142206809a0581207a449700e008050881a026c38058120792c4c0020142206809b700160481e03930008050881a026c160481e039306c0020142206809b000150481e03802019ac0881a0268150481e03930008066b02206809b000940581207840008060841a026894180160481e100020182106809b250160481e100b4008060841a026d1405812078402d0020182106809b250600f0120780e008060841a026d141803c0481e038020182106809b00198058120780e008060841a026998250160481e038020182106809b660a4058120780e008060841a026c94290160481e038020182106809b66060058120780e008060841a026d980581207908038020182106809b250160481e4200e008060841a026d140581207908038020182106809b290160481e4200e008060841a026d980581207840038020182106809b180160481e8800e008060841a026c000581207a20038020182106809a05812078408800e008060841a026d9805812078b4038020182106809b290600f0120780d008060841a026c00182580481e034020182106809a1803c960120780d008060841a026c000f2580481e034020182106809a00000960120780d008060841a026598058120780e2e0020182106809b0e0160481e03a54008060841a026c00058120780e950020182106809a058120780e2e254008060841a026c60058120780d610020182106809b000160481e03584008060841a02683c058120780d00a500182106809b000160481e03402940060841a026838058120780e005740182106809b000160481e038015d0060841a0269140e0160481e100020142106809b000150496407840008050841a0268000e0160481e460020142106809a000000581207918008050841a0264380581207840460020142106809b000160481e10118008050841a026800000151201e038020142106809900148058120780e008050841a0268000544807840038020142106809a520160481e1000e008050841a026c000541207840038020142106809a0f0160481e5700e008050841a026c00058120795c038020142106809a0024c0f0120780d008050841a0268000f0160481e034020142106809a0e0160481e03920008050841a026c00058120780e480020142106809a001100e0120780e004050841a0268000e0160481e038010142106809a002830481e034b8008060841a9ee800a0c12078b4038010182106a7ba000120780d340021d0060841a9ee800a0c1207840038020142106a7ba000120780d8e002014220680a9ee81207a3c03930008050881a02a7bb0481e036384c002014220680a9eec120780d2e002018680881a02a7bb0481e1000e008051a0220680a9eec120780d8e002014680881a02a7bb000120780d2e0d0018210680a9ee8000481e034a0008060841a02a7ba0481e8f00e2e002018210680a9eec120780d280b8008060841a02a7bb0481e2d00e34002018210680a9eec120780d280d0008060841a02a7bb0001207a3c2d001018210680a9ee8000481e2400e004060841a02a7ba0481e240b403801018210680a9eec1207840038021d0060841a02a7bb0481e034a000874018210680a9eec1207890038011d0060841a02a7bb000129bc1e8f00e014210680a9ee8000481e1000e340050841a02a7ba0001207a7c03802014210680a9ee81207a7c1000e008050841a02a7bb0481e9f23c03802014210680a9eec0004a6b078d0008050841a02a7ba0481e9f00e34002014210680a9eec1207a44038b8008060881a0267bb0481e2d00e4c00201822068099eec0004a6f0780d170060881a0267ba0481e1000e0085c01822068099eec0004a6f07a44038050881a0267ba00012078400393001422068099ee8000481e4b00e008050881a0267ba0481e4b0400380201422068099eec120792c9100e008050881a0267bb000129ac1e4c00201422068099ee8120792c03930008050881a0267bb0000004a739bc1e03421068099ee40004a7307840038020841a0267ba0000004a739ac1e00421068099ee40004a6f078b4038060841a0267ba00012078402d00201821068099ee8000481e4200e008060841a0267ba0481e420400380201821068099eec12079082d00e008060841a0267bb000129ac1e2e00201821068099ee81207908038b8008060841a0267bb0000004a6f9ac1e01421068099ee4160481e8f00e008050841a02a48b058120780d0085c0182206809922c160481e9100e008050881a02648b0f01604a730780d0082106809922c00058129cc1e034020841a02648a05812078b4038020182106809922c00180120780d008060841a02648a1803c0481e034020182106809922ca4058120780d008060841a02648b058120780d00a500182106809922c3c058129ac1e008050841a02648b0001604a6b078020142106809922914058120780e008050841a02648b058120795c038020142106809922c00930120780d008050841a02648a9303c0481e034020142106809922c3c058120780d008050841a02648b058120780e34002014210680a432c3805a770481e038010141a0250cb000169dc120780e00405068094328160481e03801170060881a0250cb058120780e4c0020142206809432c384a0120780e004050881a0250cb001280481e038010142206809432924058120780e004050881a0250cb058120780e004056902206809432c38058129cc1e038010841a0250cb0001604a730780e00421068094328160481e038b8008060841a0250cb250160481e038010182106809432c160481e038015d0060841a0250cb0e01604a6f0780e0142106809432c00058129bc1e038050841a0250ca0e0160481e100020142106809432c000581207840008050841a0250ca450160481e038020142106809432c160481e03920008050841a0250cb001100481e0380101421068094329100e0120780e004050841a0250cb0e0160481e038010142106809432d24058120780e004050881a02640b0e0160481e038010142206809902c00058120780e004050881a02640a0581207a44038010142206809902c94058120780e004060841a024fcb000160481e0380101821068093f28160481e2d00e004060841a024fcb058120780d2e002018210680a352c160481e2d00e004060841a028d4b058120784003802014210680a352c6c058129ac1e004050841a028d4b0001604a6b07801014210680a35286c0e0120780e004050841a028d4b000380481e03801014210680a352898058120780e004050841a028d4b05812078f403801014210680a352c6c058123700d004050841a028d4b1b0e40481e03401014210680a352c00390120780d004050841a028d4a1b0160481e03401014210680a352c8c058120780d004060841a02870b1b0160481e03401018210680a1c2c60058120780d004060841a02870b000160481e03401018210680a1c28160481e034011d0060841a02870b
  | 11, 2 => 0x5412078402d0021702206809a05412078402d1300182206809a1803c0481e035300182206809a0541207a08038020182206809a054120780e009d00182206809a054120780e00a640182206809a0e0160481e101300142206809a0e0160481e4b0020142206809a0e1280481e100020142206809a700160481e038020142206809a0581207a60038020142206809a0581207a5c038020142206809a058120780e6c0020142206809a054120780e008066b02206809a250160481e100020182106809a660160481e038020182106809a0581207a20038020182106809a182580481e034020182106809a0f2580481e034020182106809a002580481e0340201821068099058120780e950020182106809a058120780d610020182106809a058120780d00a500182106809a058120780e005740182106809a054125901e100020142106809a0e0160481e460020142106809a000160481e46002014210680990581207840460020142106809a000151201e0380201421068099520160481e038020142106809a0544807840038020142106809a0541207840038020142106809a058120795c038020142106809a9303c0481e034020142106809a0f0160481e034020142106809a058120780e480020142106809a440380481e038010142106809a0e0160481e038010142106809aa0c120780d2e0020182106a7baa0c12078b4038010182106a7ba0481e034d0008740182106a7baa0c1207840038020142106a7ba0481e03638008050881a02a7ba0481e034b8340060841a02a7ba0481e034a0008060841a02a7ba0481e8f0b4004060841a02a7ba0481e2400e004060841a02a7ba04a6f07a3c038050841a02a7ba0481e1000e340050841a02a7ba0481e9f00e008050841a02a7ba04a6b078d0008050841a02a7ba04a6f0780d170060881a0267ba04a6f07a44038050881a0267ba0481e1000e4c0050881a0267ba0481e4b00e008050881a0267ba04a6b07930008050881a0267ba000129ce6f0780d0841a0267b904a7307840038020841a0267ba000129ce6b078010841a0267b904a6f078b4038060841a0267ba0481e100b4008060841a0267ba0481e4200e008060841a0267ba04a6b078b8008060841a0267ba000129be6b078050841a0267b9058129cc1e034020841a02648a180120780d008060841a02648a058129ac1e008050841a02648a930120780d008050841a02648a05a770481e038010141a0250ca4a0120780e004050881a0250ca058129cc1e038010841a0250ca058129bc1e038050841a0250ca0581207840008050841a0250ca440120780e004050841a0250ca058120780e004050881a02640a058120780e004060841a024fca058129ac1e004050841a028d4a0e0120780e004050841a028d4a058123700d004050841a028d4a390120780d004050841a028d4a058120780d004060841a02870a
  | 11, 3 => 0x960120780d008060841a0264160481e4600201421068099054480780e008050841a0264129ce6f0780d0841a0267b904a739ac1e00421068099ee4129be6b078050841a0267b9
  | 12, 0 => 0x150481e9100e2e0020182206809b05412078b403930008060881a026c150481e1000e0085c0182206809b4a0160481e1000e008050881a026c3c0581207a44038020142206809b0e0160481e03930008050881a026c600581207840038020182106809b000600f0120780d008060841a026800290160481e034020182106809a29060058120780d008060841a026c38058120780e2e0020182106809b290160481e034b8008060841a026c00250160481e038010182106809a250160481e2d00e004060841a026c000e0160481e100020142106809a00114058120780e008050841a0269140e0160481e038020142106809b4503c058120780e008050841a026d140581207840038020142106809b0f0160481e034020142106809922c00058120780d008050841a02648a0e0160481e038010142106809432c00058120780e004050841a0250ca1b0160481e03401014210680a352c00058120780d004050841a028d4a
  | 12, 1 => 0x541207a44038b8008060881a026c150481e2d00e4c0020182206809b054120784003802170060881a026d280581207840038020142206809b0f0160481e9100e008050881a026c38058120780e4c0020142206809b180160481e1000e008060841a026c001803c0481e034020182106809a000a4058120780d008060841a0268a4180160481e034020182106809b0e0160481e038b8008060841a026ca4058120780d2e0020182106809b00094058120780e004060841a02689405812078b4038010182106809b000380581207840008050841a026800450160481e038020142106809a45038058120780e008050841a026d140f0160481e038020142106809b450160481e1000e008050841a026c00002830481e034010142106a7b9000120780d34002014210680a9ee8000481e8f00e004050841a02a7ba000120780d4c00201422068099ee8000481e034b8008060841a0267ba00012078b40380101821068099ee800000129bc1e034050841a0267b900012078400380201421068099ee800000129ac1e004050841a0267b90f0160481e034020142106809922c00058120780d008050841a02648a0e0160481e038010142106809432c00058120780e004050841a0250ca1b0160481e03401014210680a352c00058120780d004050841a028d4a
  | 12, 2 => 0x541207a44038b8008060881a026c150481e2d00e4c0020182206809b054120784003802170060881a026d280581207840038020142206809b0f0160481e9100e008050881a026c38058120780e4c0020142206809b180160481e1000e008060841a026c001803c0481e034020182106809a000a4058120780d008060841a0268a4180160481e034020182106809b0e0160481e038b8008060841a026ca4058120780d2e0020182106809b00094058120780e004060841a02689405812078b4038010182106809b000380581207840008050841a026800450160481e038020142106809a45038058120780e008050841a026d140f0160481e038020142106809b450160481e1000e008050841a026c00002830481e034010142106a7b9000120780d34002014210680a9ee8000481e8f00e004050841a02a7ba000120780d4c00201422068099ee8000481e034b8008060841a0267ba00012078b40380101821068099ee800000129bc1e034050841a0267b900012078400380201421068099ee800000129ac1e004050841a0267b90f0160481e034020142106809922c00058120780d008050841a02648a0e0160481e038010142106809432c00058120780e004050841a0250ca1b0160481e03401014210680a352c00058120780d004050841a028d4a
  | 12, 3 => 0x1803c0481e034020182106809a290160481e034020182106809a250160481e038010182106809a0e0160481e100020142106809a450160481e038020142106809a002830481e034010142106a7b90481e034d0008050841a02a7ba0481e8f00e004050841a02a7ba0481e03530008050881a0267ba0481e034b8008060841a0267ba0481e2d00e004060841a0267ba000129bc1e034050841a0267b90481e1000e008050841a0267ba000129ac1e004050841a0267b9058120780d008050841a02648a058120780e004050841a0250ca058120780d004050841a028d4a
  | 12, 4 => 0x2830481e034010142106a7b904a6f0780d01421068099ee4129ac1e004050841a0267b9
  | 13, 0 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a
  | 13, 1 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 2 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 3 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 4 => 0x541207840038020142106809a0f0160481e034020142106809a0e0160481e038010142106809a000120780d004050841a0267b9
  | 13, 5 => 0x120780d004050841a0267b9
  | _, _ => 0
def tableData : Nat → Nat → Nat
  | 9, 0 => 0xa0940000b100004200009a00004936ab18308d00880000002b000d1e0c0055243d072a0000009f007900192587061f316d937e12611301998e00725b664e
  | 10, 0 => 0xde1f79e356d990d750000000000000000000000000000000000000000000000000000000000000f850000000a9e4d0003cd2920000000000000007433310d91b1000000a15f93000000d2d000000000f3050619900043f000000000000000000f61000000ae1aca00027100000000000000033d0000001459be457eca000b278b7558f92c5c6ebaa57db2dd6c10008a2000000516000d995f0901ccd4cb22922b000000000000000000000000000000000e86829c88e6ee059d6fc166e0000006bb3d9c26a5bec589e240000691000000000000000000aff000d39667000f880001c9000000000e580007ea96b00001900052d841000000c83000b4d33a32bf19d15000fa23855469a46aa0005240006d7704000617000a210008e4dce000000000e56000000a9f000000abe2f2000000000a4f8350004e12883087709fdeba1390000000003791f99b2f31d8b00068b00000000000062c2ad0790000008f5a61d611810000004b00002954220000000000006a3b33b8900000036100054df4a6f88aae6520541672140900000000000000000000081db06e10211955c1958ff7767a000b29e7d049f91000000000000000000000000000c9d000000000af700000000054ec6700085300000000000018d9b0000000593000000f9f0006da000e41000f9e00000000060d000000000d818e900000000021d6e300000000000000039d00031f000f2200000083b0000000000006a92ce98c34f00000000015d000fcd4bcf3fcf1000000000f9d000000b9d7bdabb0000000000007edb7d7f6560241ab1000000e4b235000f18ca9f0055700000027000059c0000000000005cc0000000000000fdcce53f0000002c2000a37000000000000000000000b8ad5a0008a19800006cd00000000000000003d8196e58c512d30d0f11159755d1c9bf67515bc5692025f0ae9e589de63a9679f23d7500000000027d00000069b000000000000ded000000294d14dda00074b355f16df8bf50000000000008c2000000618e59cfdfe7000000518000db1000000885ed1267000b5700000000000077c000000000000000000000e4e000000000a6e64f5450003910008b54986389b5175f589311d58790cd50f34974f00afa436dd458050000000000000003b5b7e535e890000000000c12f593db1b000000000000577ea1b110000007818ad548000000000000dc93d309dbdd28b715a6c061a97fbf000d92000fa00000000002d1ac9d090000000000000000000000000007dc000000000737000d38edda81ef73c19bcb71000fad7d2594a75bc6000000000000000000000000000000000000000000bf3c770009193e50005fc4787ff000000000000e330001690004a4000000000000000655a5d7a6bad23e78df6dfa99e2e71151dbdfaa00024d000000a43000a51000d3d505000a3900000000000000000076400000000000006d000eb9e280000000005e40005b91ed9cad550000000004ed30754060e2374bf000000f24000000000000abd00000000094a0000000000009f1000f44000f73000000000286571460c6d0000000000004e7b35fb566dce51e1bdb121000000000000000000758000000aeb0000000000000000000000000000000004db9e5000892620665f6b00000000009100000000027fb053f10e5000000000e11697f0f5170000008d1000000000fe11bdad5cbcb59000000000799584e950006e486d000000000f25000000000000000b41000000055c36000cf20000000000000005a8a7351058a00000000000056cd6ecc2b65c0de57f1b343689000000bd10000000000000000004840007090006df000e2937fd7a5473160005b4000000a2b000000000ba1000fd90b5000998000207000000ff3031000df9000a8d000259000500dd5d8d265e1dcd9000000e7a738000000000000000000744c41000949000000a0900000000000000f000109c49000000eeb53600060800000000000000044bbb97b169cc01000000000000000000000000000da5d2181ee1c886d4ecc846c8cf21f000b3f3fd6af85926e000000643fab289d5d925eb600000042e1a5000000000000ee0000085000000000000d69f8600000000000032c0002a10000000004d5d5100000071c
  | 10, 1 => 0x377534900000089002400000000190022000000000000000d0f000000002a0000002b7d00000000478e00006d2c003d005f0000001b0000553b316129000001
  | 11, 0 => 0x62f48da470be8b4bad8ec99a07a2032967f7282a6934200088d0000000000000004a2bd11f309700000088904b1e1a000007de0009ecaed00030e6bf8950000000000000005597e18b100000021825e26a0000000000882d1542a6d3fd0000005110000000000008e9000a2e0cd58912d90520c422679052000000000b157396559fe0006be8b800000051d3d288835a241000000b8b00000000000000000009d000000000000000b47baa000ad59910000000000000002ad000000000246ba17bb4ba28e07834e4ed00000007907319f00000000000061cb2f3ed0000009b68860007150000004be54a2b94e148107bb210000006360000000008dbbaf3910007240000002dd33106a0aebae42100000060345da507bd00000066b24d989786000000000000aa581d0000fa2f9862000949b05229aa10000000603de000336000000ae16538a10000008eb0000635d172b0001b10000004094c6000439b5761e0000006b50000007d3000000000000000000000a460000008bd0a3000000871000031000000000000726a3991a9165a933d7eb0000002c5a09ab14758d13670003b57f90005cc1a50009e02ba77a14500000000000093100000093d0930004695d20006e565f2590000009039900001d00006f1b841ff00000087f60d00020500000000900022c6340000009145b9bab0009115dd1dc00000000000000000000000000000000000000000000069d49a7849879ff16300000064e1694d52350b55b506700000000000000000000000000000000000027100000000083534900000000079206d4c9049000661000000ac83799ad0ee000000000a51a4a0baba5000000000980000000000000000000000000000015000000000000000b888117ea4511ab98c00000079e02da0db3d5c5913325995a15a0aa3a5e93590002be0000000000000000001ed18d0000000000002db00000039d0009a831fb8a5e65cb000b410006490000000000002a200000000000000000068e1f722a000a28000000b4d00026500035c0000003020210b266d971abf55f0000000008af7a227d8600000006230001bd00000041500000000064c87d0000006cd000000000000000000a7d00000015d0007ae0000000000000009fd13f0007900002ed0000000000002a60000000572d60007ed2cab99a5db7f0000000003c17dcb8f0000000000000000000000001e700000000095e89e0000000003cd0003660000000000009f64990917699d1b4999f00000000005e82b577211000000000000000ba21d553521e086289000845bc9000309b7d0000000007c400000000011c00000052958f982000000000000157a950008f70000006d90001753714b1a229f89dd86912806c5657a5a1299d08598e07688b95400029a54ebb90002e20000000000000000000000000000000000000873855950000000000000000000000000009853d91ea000054000583000000000000a89000000929b7100006f000000445000000000899000000000a370005f59e600000000054174f00080e0002e95a71811f90000000000000000000009d94bd76296a000000000b0b0005de00000000000063d737a1003da43182bc52e7935000000000a4e2a1000affb59b95976000b2d0005a17c900042e0003f1000000000000000b860002207f40000009a435b000000000b8d000000000a1600000000000000000000000000000000009f709151851000000000110000000000ac300014b9a65b30000000000007564f92c630100000000069ba1307c8dd2f51040a900057d1330006010c18f500000000000000000094b0000000000006c100068f000000ae795685d00000000086e5ad8c92950000000000000000000339e3bba50618e0000000001c90000008aa000000000abd0006b20617b80000000000550007d5000000000000000962000000a450000000000008b631521d3193658adbbb3a92b27368d578d00000076e000000000000000000000252000276707ac930d9594a6b65000a40000000000000000000a54000000000000ac60000009c500052a00036890180500097986c8290009749e20d9b898a85ef452000000000961000000000000000000000199952000af9000000000139
  | 11, 1 => 0xa832b90af998a996fd0b60000000009e200094729a5be98900000025e00000000000020b0c700000098506f1f9a3048d92e5710000008574450000000000000000000000009310009950002290000000000000002e954175e0005290000000000004ed0003d7186139a5e09d9ad0e57812188414150760005430005d58290008a100085699c5e2a2e73967228e39a24d0000009b70002d20000000005370000000000003e77f33b200012d1929d93a4a960000002ad00000000007fa8d4cb33190b2520845ca0ab72d1b70b55334f100000000064368d38542d0000009fe40b00087d51d00070a7662c50006f10b75ed000721000000000499000a9b62500088c0004fd3665ad0000d2000a9a0002d67fb6cda8c90d0002654508d69d183f00000000000003d00000000000000038d00000059503900000000067e0005b200055b1754938270000000005110007c98930001d50000006a971200000081b18d00000084d00000092300049f000000000000000a820000000000000000000000000550003f500034988ea690004397a100093b5b9000061a394726e53915fb0006550000007c42c6a281f31c98ca3de0000000000000000001ca3560c36d92e27ca8338719ab5395104382209d80000000000000009a40000000b4805000211000000000000000000000000a977d57b10004790001e80000000000000000000000000000000000000000000000000008d4a2f4fe1639cf0004211990008220007ad24100054d0b200004b4510000000000000000002710009790000855c50009f530d8e207971506d3dd8353fd3cb09c4c860d000106000000000a86000a910000000000000000000000000002d10004440000150000004d600056e9a89610006c100093a1be9d43257bda3d69936d50e8ee9dda45a3a5a17e15e1a6a2ca00000000000008e0002051a50000000002f348c00058f6313f19f03a39b67de7c30007ed81d2834c90000000002a200042000000000020f000000000000a5853833d8110003790005e40000003020000d60930000000000003b399350f0002958f20000000000000000000006b50005590008200000005050000000000000002dd00000900000015d0008fe000000000000000a2d1573118e02f90000000000000002a60000000002ee00093d4b3a7900099f00014b9bb92c6613ca33a00000000045d00028f32b1ff18700000000000000000066d16f4e35fa0000000000000000000c18b9a197f59e700000000000096f0a908b0000000004ab000a8e1e13bf00075123634a0004d532c30999d4ea09f53591400000000000000048174578700000000000000000002d0000000000008650000003a6000605000a25a5212827d8f59d6000a422de9e598708250200000000076a000000aa500000000000000000039b00000000000000061978d0000000000000000000000000000006799cd00007820277b0000003520000213ff00000094900007b00000000000000000000036a000000a671f631200000047e75d0008b700095e31a2f500079f000000000000000000709049a213c10009ca00000000059b1ed3817d60005560004b589fa40ab1000000a730002890000000002a1a8a583565314a7551a21d6410009197990000004e569d0000009a65320000000002389440000a39ec5e300046f1459b93d90a8000a460000000003e50000000000000000000000000003190002be00000011c4be0000000974ae0009ee7ab00000000000000000000030100000033e22ca430b80004091100cd0a677513f0000000007f90000000000000000000000001930000008590000000004bd00017b0000003550000007a509045c00048239d000000000057a2baa60000000001a60003cd3653610000000000000000000913329080000000000000009250000000003890009c2000000a810000004e100099a5899912355f989eaa76492b216948a8dd0000008be00000000000000000054f26a5132763d60000d9000000abd181a700000000000000004b10000000003b53e209a000000a0d0007469a94c65fc95500000000096d00051f087a2a9b50f17e76c20000002829c12590000004e00000000000001b135e57d4a51bd313151
  | 11, 2 => 0x34c000000000000003b52d400001ed000000037700000918000000028800000000000000000000000000000000d60d1814005d400000000000000000003610036d003ad00000000000005b7554200000000006340037d4f6f473000001c83d19f3d0c6b96ce6a001d7002510000000000003210000000000af8000002b000006ac00308000000072c0000000c7ce0398000cdba72534000000000000000000000000000000000000000000000001c1d2400001369d521a9ecd000002a40000000000000000000000bd40097400c0400f059900000ede8900000001028d40000000003b60000031add000000000000180000000000000000000ee00000000004a779000000000000000000008e906001ef000d2238000000000000000000000000000b44000000000000000000000d4e40067c00000000000047485001ea0000000000064000016100000000e500241dae177e4d4ea400246a5000009aead6d4000000000000000005588b00374000370000000000155510f2e90039e3c80000000251cd00000000000000000000c94ba000000000000000000006b800c4c0000000000000000000000000000000000000000500003a00000000000000000000000005a4000000000000c5400784000000f60400000003c4000030d0c18c003914b425000cdd6800f08000014550d554067d3f400000000000000000000000000000000000000000000000304000240000202495b1003850021ddaa69000d91ebc318509d5400000000039d002290000078c0000000538000b800cc4001b4000000000000a5400002234cc005755a003192bc0000000000009b00000000000000000009c000000073000454ae0009d000000000000000000003ea111e40069400
  | 11, 3 => 0xe0000100140003a00031420000800a4c80000068000f40000c00000
  | 12, 0 => 0x728000000578000000001dc00785680000000000122d960a84006e001fc00aa4300000008000000cd00065e27962b24f400002104a0000001ac4954b497a001e841c60000001ec000000000000000214d591458000018c25d20000000a85a2980000002a8000000003f49400000000083003840000391b40000003f80000000000873001840000000000000000013c67
  | 12, 1 => 0xa8800007a8da14000071a6800e48c8000000a2bf65a910043400da758000116790000000b6002727d0cd766ae54e4c5cc00781584a004bad6851594cf800101e9e69e00000000162000000000370028376c7608a031ba956aa004e97d80bf630014c60608000000005a56c0077800006da6b7800892f3655000005a9040032aa408df5133400000000000612480214d3
  | 12, 2 => 0xa8800007a8da14000071a6800e48c8000000a2bf65a910043400da758000116790000000b6002727d0cd766ae54e4c5cc00781584a004bad6851594cf800101e9e69e00000000162000000000370028376c7608a031ba956aa004e97d80bf630014c60608000000005a56c0077800006da6b7800892f3655000005a9040032aa408df5133400000000000612480214d3
  | 12, 3 => 0xc63c000000009d0000250000000000009600970049bd84552c7e0000000000000000a30000000076000000000000410078005e009b00823200000000a80000009e0000000031006d91c1793b4aca00a70d9200007300000000b500003a00000000616556853d000000000400009c0000000000c900a900001959b9000000
  | 12, 4 => 0x19000211341
  | 13, 0 => 0x800c001b0402000000046400003c04dd18000001500d391
  | 13, 1 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 2 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 3 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 4 => 0x7403e70803405000004250c0a4405b7c748002114001939a
  | 13, 5 => 0x24103750
  | _, _ => 0
def tableDisplacements : Nat → Nat → Nat
  | 9, 0 => 0x3420400c3000000000141000081003080000000002000000
  | 10, 0 => 0x1000070000000000000000040000002000000040000802000000040003c0000800000000000100000000000000000001000030080000000008010000000006000000000000c0000000000000000000000000000000000000000020000000001000000040000800000000000000001000010000200000000020080000000000090040700005000000000400000000000000000001000000000000000000000000000000004000000000000000000040e00c01000000040000400000000000000800000000100000c040080001c000000000c0000c0001400000000040000004000010040200800000000080000001004000000000000000000040001000008000000000000000000000000000000000000000000000000000000000000010080000000000000000000000000000000000000000000000600000000000000000004000000000000000008000000000003000000000000c00000000000000000000000080000000000000000000001000000000000c0000c00000000080000000000000000000000000000000000000000000080000000000010000000401000000000001000000000000000000000000040300000000000040000c010000000400000000000000001000000000100000000000000300001000000000100000000050040000000000000000000c00000000000000402000000040200403000000000000001000000000000400000000000000000000000000000c010000000c00000010000200001004000000000003004000000100000000000000000001008000080000000000000080100000000000000000000000000040000400004000000000c000000000800000000040000000000000000100000004000000000000
  | 10, 1 => 0x40000000000000000000000000000000000000000
  | 11, 0 => 0x2c00000000040000400000000040000406000020080200000004000000000000000010000000c00000000000000000000000000000401000040000000000004010080000801008000000000401000010000001405000010000000402000000000000007000000040001400008000000000000000000000100004000000000000c00000000080100000000000040200000000000040200000004000000000400000010000000c000000000000004000000000000000000000300000010000000000405000010000000000000020000100001004000000000000004000000002002000000040000002000020080000c000080000400000000000000800004000000000400000000000000402000010040000000000000000000003000010000000000000000000200000000000000000004000000000000001000000000000001000000000700000000000000000400000000040000000008030000000000000000000000800000050040100003000000000000000000000000000000000000040000000000000080000000000000000000c0100001000000000300000008000000000c00004000000000000000000000000000000000000300000000000000000001000010000000000008000000000000000000000000000000000000000000000000000000000000000040000000000050000000000000020000000800000000000000800000000000100000000000000000000000000000000000000010000100000000000000000000000000000100000000000040000000000000000300001000000040000000000020000000000000000000000000000000040000000004000000000c0000000000000000400000000000000000000000010000000000
  | 11, 1 => 0x1400010000040400400000000040200c0900400004000000600c0000000004000080000000000000000000001030000000000000004000000000000004000000000400000000000c00003010000000000000000000000000000018000000000000000030000000000014000000000000000000000000001000020000100000000000040000001004000000100000000000000100800000000000000000008000000100400000000000000000000000040000001000000000100000010010000000000000000000001000000010000100001000000000000000000000000702c0100000004010000300002004000000100000000000100000000008000000000000008000000000000014000000100000000000000000000000000000000003008030000000002000000000001000000000000000400000000000000001000000000000004000000000000801000000000000001000000000000000000000000000000010000000000401000000000000000000010000000800000000000000000000000000000800000000000000400008000000000000000000000100000000000000000000000000000000000004000000000000000030000000000000000040100000000000000000000000010000000000000000000000000008000000000000000000040000000000000000000001004000000000c0000000008000000000c000000000000000000000000000000000000200000000000000000003000010000000000000000000001c00000030000000000000000000000000000010040100000000000000000001000000000001000000000080100000004000000200000000000000000000000000100600001000000080000001000000000000000
  | 11, 2 => 0x40000000000001000000000000000001000000003000000000000000200010000000000000000000000000010000000000040003010040000000000200000000000000000000000000000000000000000000000000000000000000000000040800008000000008000000000000204000000600000000000000000001000000000008000001000000002000000200000000000000000002000000000000000000000000000000000000000040000000000000000040000008000000000040000000000000000000000000000000000000000018000200000000000010000000000000000000000000000000000008000000008000000000000000000000000000000000000000000000000000000000000008000000000040000000000000
  | 11, 3 => 0x0
  | 12, 0 => 0x8000000000004100020000100001000000000020000200000000000000000008002000000000002000008000000000000000
  | 12, 1 => 0x40000608080000000006001000800082020c1810000000000000300000000000000000418000000000004002000008100001020000000
  | 12, 2 => 0x40000608080000000006001000800082020c1810000000000000300000000000000000418000000000004002000008100001020000000
  | 12, 3 => 0xc000040000002000000200000040000300000000000000000000002000000000000000000000000000000000000000000000000000000
  | 12, 4 => 0x8
  | 13, 0 => 0x8402000000000000000
  | 13, 1 => 0x801014010000010000
  | 13, 2 => 0x801014010000010000
  | 13, 3 => 0x801014010000010000
  | 13, 4 => 0x801014010000010000
  | 13, 5 => 0x880
  | _, _ => 0
def tableBuckets : Nat → Nat → Nat
  | 9, 0 => 32
  | 10, 0 => 512
  | 10, 1 => 32
  | 11, 0 => 512
  | 11, 1 => 512
  | 11, 2 => 256
  | 11, 3 => 16
  | 12, 0 => 64
  | 12, 1 => 64
  | 12, 2 => 64
  | 12, 3 => 64
  | 12, 4 => 4
  | 13, 0 => 16
  | 13, 1 => 16
  | 13, 2 => 16
  | 13, 3 => 16
  | 13, 4 => 16
  | 13, 5 => 4
  | _, _ => 1
def tableMultiplier : Nat → Nat → Nat
  | 9, 0 => 1000
  | 10, 0 => 1000
  | 10, 1 => 1000
  | 11, 0 => 1000
  | 11, 1 => 1000
  | 11, 2 => 1000
  | 11, 3 => 1000
  | 12, 0 => 1001
  | 12, 1 => 1001
  | 12, 2 => 1001
  | 12, 3 => 1000
  | 12, 4 => 1002
  | 13, 0 => 1000
  | 13, 1 => 1000
  | 13, 2 => 1000
  | 13, 3 => 1000
  | 13, 4 => 1000
  | 13, 5 => 1000
  | _, _ => 1
def tableSalt (_ _ : Nat) : Nat := 0
def tableBits : Nat → Nat → Nat × Nat
  | 9, 0 => (6, 8)
  | 10, 0 => (10, 12)
  | 10, 1 => (6, 8)
  | 11, 0 => (10, 12)
  | 11, 1 => (10, 12)
  | 11, 2 => (9, 10)
  | 11, 3 => (5, 7)
  | 12, 0 => (7, 9)
  | 12, 1 => (7, 9)
  | 12, 2 => (7, 9)
  | 12, 3 => (7, 8)
  | 12, 4 => (3, 6)
  | 13, 0 => (5, 6)
  | 13, 1 => (5, 6)
  | 13, 2 => (5, 6)
  | 13, 3 => (5, 6)
  | 13, 4 => (5, 6)
  | 13, 5 => (3, 4)
  | _, _ => (1, 1)
def sample (s : Bool) (i : Fin 414) (j : Fin 9) : Bool :=
  bit s i (raw.getD j.val zero)
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
set_option maxRecDepth 20000 in
lemma sample_ok : ∀ (s : Bool) (i : Fin 414), edgeF (sample s i) = s := by decide +kernel
lemma raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := rfl
lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by
      rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]
lemma raw_lt : raw.all (fun a => decide (a.1 ≤ top ∧ a.2 ≤ top)) = true := by decide +kernel
lemma raw_valid : ∀ a ∈ raw, Valid a := by
  intro a ha
  have h := of_decide_eq_true (List.all_eq_true.mp raw_lt a ha)
  exact ⟨valid1_of_le_top h.1, valid1_of_le_top h.2⟩
lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel
lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi, decide_true]
      obtain ⟨b, hb, h⟩ := live_sep l i hi
      have ba : b ≠ a := fun he => hn (he ▸ hb)
      have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
      exact (mem_unionSep true _ _).2 ⟨b, hm, sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi, decide_false]
      exact valid_unionSep (fun x hx => raw_valid x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail
lemma execute_valid (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a) :
    ∀ a ∈ execute gs w, Valid a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (w ++ [gv w g])
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates raw raw_valid
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ raw_valid (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list, sample_ok] at eq
    exact eq
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)
def index9 (key : Nat) (j : Nat) : Nat := (key >>> (9 * j)) &&& 511
def reindexLoop (f : Fin 414 → Fin 414) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 414 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 414 → Fin 414) (x : Nat) : Nat := reindexLoop f x 414
lemma reindexLoop_testBit (f : Fin 414 → Fin 414) (x : Nat) (m j : Nat) :
    (reindexLoop f x m).testBit j =
      if h : j < m ∧ j < 414 then x.testBit (f ⟨j, h.2⟩).val else false := by
  induction m with
  | zero => simp [reindexLoop]
  | succ n ih =>
    unfold reindexLoop
    dsimp only
    by_cases hn : n < 414
    · simp only [hn, dite_true]
      by_cases hx : x.testBit (f ⟨n, hn⟩).val = true
      · simp only [hx, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
        by_cases hj : j = n
        · subst j; simp [hn, hx]
        · have h1 : ¬ (j ≥ n ∧ (1 : Nat).testBit (j - n) = true) := by
            intro ⟨hge, htb⟩
            have hpos : 1 ≤ j - n := by omega
            have hlt2 : 1 < 2 ^ (j - n) := by
              have h2 : 2 ^ 1 ≤ 2 ^ (j - n) := Nat.pow_le_pow_right (by omega) hpos
              omega
            rw [Nat.testBit_lt_two_pow hlt2] at htb; contradiction
          have hbit : (decide (n ≤ j) && (1 : Nat).testBit (j - n)) = false := by
            cases hle : decide (n ≤ j)
            · rfl
            · cases ht : (1 : Nat).testBit (j - n)
              · rfl
              · exact (h1 ⟨of_decide_eq_true hle, ht⟩).elim
          rw [hbit, Bool.or_false]
          by_cases hlt : j < n
          · have hlt' : j < n + 1 := by omega
            have hj414 : j < 414 := by omega
            simp [hlt, hlt', hj414]
          · have hge : ¬ (j < n + 1) := by omega
            simp [hlt, hge]
      · have hxf : x.testBit (f ⟨n, hn⟩).val = false := Bool.eq_false_iff.mpr hx
        simp only [hxf, Bool.false_eq_true, ite_false, ih]
        by_cases hj : j = n
        · subst j; simp [hn, hxf]
        · by_cases hlt : j < n
          · simp [hlt, show j < n + 1 by omega, show j < 414 by omega]
          · simp [hlt, show ¬ (j < n + 1) by omega]
    · simp only [hn, dite_false, ih]
      by_cases hj : j < 414
      · have h1 : j < n := by omega
        have h2 : j < n + 1 := by omega
        simp [hj, h1, h2]
      · simp [hj]
lemma reindex_testBit (f : Fin 414 → Fin 414) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 414 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 414 j
lemma reindex_valid1 (f : Fin 414 → Fin 414) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 414 by omega]
lemma reindex_and (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_and]
lemma reindex_or (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_or]
lemma reindex_bnot (f : Fin 414 → Fin 414) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_zero (f : Fin 414 → Fin 414) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
lemma reindex_top (f : Fin 414 → Fin 414) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 414
  · simp [hj, testBit_top, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_comp (f g : Fin 414 → Fin 414) (x : Nat) :
    reindex f (reindex g x) = reindex (fun j => g (f j)) x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, reindex_testBit, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_id {x : Nat} (hx : Valid1 x) : reindex (fun j => j) x = x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
structure SigHom where
  fn : Sig → Sig
  valid : ∀ a, Valid (fn a)
  hneg : ∀ {a}, Valid a → fn (neg a) = neg (fn a)
  hbin : ∀ d a b, fn (bin d a b) = bin d (fn a) (fn b)
  hzero : fn zero = zero
  hone : fn one = one
  htarget : fn target = target
def pairHom (fp fn : Fin 414 → Fin 414) : SigHom where
  fn a := (reindex fp a.1, reindex fn a.2)
  valid a := ⟨reindex_valid1 fp a.1, reindex_valid1 fn a.2⟩
  hneg ha := Prod.ext (reindex_bnot fp ha.1) (reindex_bnot fn ha.2)
  hbin d a b := by cases d <;> simp [bin, reindex_and, reindex_or]
  hzero := Prod.ext (reindex_zero fp) (reindex_zero fn)
  hone := Prod.ext (reindex_top fp) (reindex_top fn)
  htarget := Prod.ext (reindex_top fp) (reindex_zero fn)
def compHom (h1 h2 : SigHom) : SigHom where
  fn a := h1.fn (h2.fn a)
  valid a := h1.valid (h2.fn a)
  hneg ha := by rw [h2.hneg ha, h1.hneg (h2.valid _)]
  hbin d a b := by rw [h2.hbin, h1.hbin]
  hzero := by rw [h2.hzero, h1.hzero]
  hone := by rw [h2.hone, h1.hone]
  htarget := by rw [h2.htarget, h1.htarget]
def sym1 (j : Fin 414) : Fin 414 := Fin.ofNat 414 (index9 symKey1 j.val)
def sym2 (j : Fin 414) : Fin 414 := Fin.ofNat 414 (index9 symKey2 j.val)
set_option maxRecDepth 20000 in
lemma sym1_invol : ∀ j : Fin 414, sym1 (sym1 j) = j := by decide +kernel
set_option maxRecDepth 20000 in
lemma sym2_invol : ∀ j : Fin 414, sym2 (sym2 j) = j := by decide +kernel
set_option maxRecDepth 20000 in
lemma sym11_eq : ∀ j : Fin 414,
    sym1 (sym2 (sym1 (sym2 (sym1 (sym2 j))))) = sym2 (sym1 (sym2 (sym1 (sym2 (sym1 j))))) := by
  decide +kernel
def hom1 : SigHom := pairHom sym1 sym1
def hom2 : SigHom := pairHom sym2 sym2
abbrev action1 (a : Sig) : Sig := hom1.fn a
abbrev action2 (a : Sig) : Sig := hom2.fn a
lemma action1_invol {a : Sig} (ha : Valid a) : action1 (action1 a) = a := by
  apply Prod.ext <;> dsimp [action1, hom1, pairHom] <;> rw [reindex_comp] <;>
    simpa [sym1_invol] using reindex_id (by first | exact ha.1 | exact ha.2)
lemma action2_invol {a : Sig} (ha : Valid a) : action2 (action2 a) = a := by
  apply Prod.ext <;> dsimp [action2, hom2, pairHom] <;> rw [reindex_comp] <;>
    simpa [sym2_invol] using reindex_id (by first | exact ha.1 | exact ha.2)
lemma action11_swap (a : Sig) :
    action1 (action2 (action1 (action2 (action1 (action2 a))))) =
    action2 (action1 (action2 (action1 (action2 (action1 a))))) := by
  apply Prod.ext <;> dsimp [action1, action2, hom1, hom2, pairHom] <;>
    simp only [reindex_comp] <;>
    exact congrArg (fun f => reindex f _) (funext fun j => (sym11_eq j).symm)
def homG (g : Fin 12) : SigHom :=
  match g.val with
  | 0 => pairHom id id
  | 1 => hom1
  | 2 => hom2
  | 3 => compHom hom1 hom2
  | 4 => compHom hom2 hom1
  | 5 => compHom hom1 (compHom hom2 hom1)
  | 6 => compHom hom2 (compHom hom1 hom2)
  | 7 => compHom hom1 (compHom hom2 (compHom hom1 hom2))
  | 8 => compHom hom2 (compHom hom1 (compHom hom2 hom1))
  | 9 => compHom hom1 (compHom hom2 (compHom hom1 (compHom hom2 hom1)))
  | 10 => compHom hom2 (compHom hom1 (compHom hom2 (compHom hom1 hom2)))
  | _ => compHom hom1 (compHom hom2 (compHom hom1 (compHom hom2 (compHom hom1 hom2))))
abbrev action (g : Fin 12) (a : Sig) : Sig := (homG g).fn a
def invG (g : Fin 12) : Fin 12 :=
  ![0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 10, 11] g
lemma action0_eq {a : Sig} (ha : Valid a) : action 0 a = a :=
  Prod.ext (reindex_id ha.1) (reindex_id ha.2)
lemma action_valid (g : Fin 12) (a : Sig) : Valid (action g a) := (homG g).valid a
lemma action_neg (g : Fin 12) {a : Sig} (ha : Valid a) : action g (neg a) = neg (action g a) :=
  (homG g).hneg ha
lemma action_bin (g : Fin 12) (d : Bool) (a b : Sig) :
    action g (bin d a b) = bin d (action g a) (action g b) := (homG g).hbin d a b
lemma action_zero (g : Fin 12) : action g zero = zero := (homG g).hzero
lemma action_one (g : Fin 12) : action g one = one := (homG g).hone
lemma action_target (g : Fin 12) : action g target = target := (homG g).htarget
lemma action_inv (g : Fin 12) {a : Sig} (ha : Valid a) :
    action (invG g) (action g a) = a := by
  fin_cases g
  · exact (action0_eq (action_valid 0 a)).trans (action0_eq ha)
  · exact action1_invol ha
  · exact action2_invol ha
  · change action2 (action1 (action1 (action2 a))) = a
    rw [action1_invol (hom2.valid a), action2_invol ha]
  · change action1 (action2 (action2 (action1 a))) = a
    rw [action2_invol (hom1.valid a), action1_invol ha]
  · change action1 (action2 (action1 (action1 (action2 (action1 a))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _), action1_invol ha]
  · change action2 (action1 (action2 (action2 (action1 (action2 a))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _), action2_invol ha]
  · change action2 (action1 (action2 (action1 (action1 (action2 (action1 (action2 a))))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol ha]
  · change action1 (action2 (action1 (action2 (action2 (action1 (action2 (action1 a))))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _),
        action2_invol (hom1.valid _), action1_invol ha]
  · change action1 (action2 (action1 (action2 (action1 (action1 (action2 (action1 (action2 (action1 a))))))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol (hom1.valid _), action1_invol ha]
  · change action2 (action1 (action2 (action1 (action2 (action2 (action1 (action2 (action1 (action2 a))))))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _),
        action2_invol (hom1.valid _), action1_invol (hom2.valid _), action2_invol ha]
  · change action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 a))))))))))) = a
    rw [action11_swap]
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol ha]
lemma invG_inv (g : Fin 12) : invG (invG g) = g := by fin_cases g <;> rfl
lemma action_inj {g : Fin 12} {a b : Sig} (ha : Valid a) (hb : Valid b)
    (he : action g a = action g b) : a = b := by
  have := congrArg (action (invG g)) he
  rwa [action_inv g ha, action_inv g hb] at this
lemma action_proper (g : Fin 12) {a : Sig} (ha : proper a) : proper (action g a) := by
  refine ⟨action_valid g a, ?_, ?_⟩
  · intro h0; exact ha.2.1 (action_inj ha.1 valid_zero (h0.trans (action_zero g).symm))
  · intro h1; exact ha.2.2 (action_inj ha.1 valid_one (h1.trans (action_one g).symm))
def rawImage (g : Fin 12) (i : Fin 9) : Sig :=
  raw.getD ((rawPermCodes g >>> (4 * i.val)) &&& 15) zero
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma raw1_eq : ∀ i : Fin 9, raw.getD (perm1 i) zero = action1 (raw.getD i.val zero) := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma raw2_eq : ∀ i : Fin 9, raw.getD (perm2 i) zero = action2 (raw.getD i.val zero) := by
  decide +kernel
def p1 (i : Fin 9) : Fin 9 := Fin.ofNat 9 (perm1 i)
def p2 (i : Fin 9) : Fin 9 := Fin.ofNat 9 (perm2 i)
lemma rawImage_eq (g : Fin 12) (i : Fin 9) : rawImage g i = action g (raw.getD i.val zero) := by
  have h1 : ∀ j : Fin 9, hom1.fn (raw.getD j.val zero) = raw.getD (p1 j).val zero := fun j =>
    (raw1_eq j).symm.trans (by fin_cases j <;> rfl)
  have h2 : ∀ j : Fin 9, hom2.fn (raw.getD j.val zero) = raw.getD (p2 j).val zero := fun j =>
    (raw2_eq j).symm.trans (by fin_cases j <;> rfl)
  fin_cases g
  · have hr0 : rawImage ⟨0, by decide⟩ i = raw.getD i.val zero := by
      unfold rawImage; apply congrArg (fun k => raw.getD k zero); revert i; decide
    exact hr0.trans (action0_eq (valid_getD raw_valid i.val)).symm
  all_goals
    dsimp only [action, homG, compHom]
    simp only [h1, h2]
    unfold rawImage
    apply congrArg (fun k => raw.getD k zero)
    revert i; decide
lemma rawImage_mem (g : Fin 12) (i : Fin 9) : rawImage g i ∈ raw := by
  fin_cases g <;> fin_cases i <;> simp [rawImage, rawPermCodes, raw]
lemma action_raw_subset (g : Fin 12) : raw.toFinset.image (action g) ⊆ raw.toFinset := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [List.mem_toFinset] at hb ⊢
  have hex : ∃ i : Fin 9, raw.getD i.val zero = b := by
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
  obtain ⟨i, rfl⟩ := hex
  rw [← rawImage_eq g i]
  exact rawImage_mem g i
def Feasible (H : SigHom) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ t T, Live m t T ∧ T ⊆ S.image H.fn
lemma feasible_mono {H : SigHom} {k k' : Nat} {S : Finset Sig}
    (h : Feasible H k S) (hk : k ≤ k') : Feasible H k' S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h; exact ⟨m, hm.trans hk, t, T, hl, hs⟩
lemma feasible_subset {H : SigHom} {k : Nat} {S S' : Finset Sig}
    (h : Feasible H k S) (hsub : S.image H.fn ⊆ S'.image H.fn) : Feasible H k S' := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h; exact ⟨m, hm, t, T, hl, hs.trans hsub⟩
lemma neg_rep (w : List Sig) {a : Sig} (hva : Valid a) (ha : a ∈ w) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases hva (Or.inl ha : represented w a) with rfl | rfl | ⟨hm, hp⟩
  · exact Or.inl (Or.inr (fun hh => hh.2.2 neg_laws.1))
  · exact Or.inl (Or.inr (fun hh => hh.2.1 neg_laws.2))
  · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
lemma feasible_pull {H : SigHom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image H.fn).toList (H.fn g) ∨ witness (S.image H.fn).toList (H.fn g))
    (h : Feasible H q S') : Feasible H (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image H.fn).toList ++ [H.fn g] := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩
lemma feasible_free {H : SigHom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image H.fn).toList (H.fn g))
    (h : Feasible H q S') : Feasible H q S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp => hp (live_proper hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb
lemma pull_unary {H : SigHom} {q : Nat} {a : Sig} {U : Finset Sig} (hva : Valid a)
    (h : Feasible H q (insert (neg a) U)) : Feasible H (q + 1) (insert a U) := by
  apply feasible_pull (g := neg a) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hneg hva]
  exact neg_rep _ (H.valid a) (by simp)
lemma pull_binary {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible H q (insert (bin d a b) U)) : Feasible H (q + 1) (insert a (insert b U)) := by
  apply feasible_pull (g := bin d a b) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hbin]
  exact bin_rep _ (H.valid a) (H.valid b) (Or.inl (by simp)) (Or.inl (by simp))
lemma free_unary {H : SigHom} {q : Nat} {a : Sig} {U : Finset Sig} (hva : Valid a)
    (ha : ¬ proper (H.fn a)) (h : Feasible H q (insert (neg a) U)) :
    Feasible H q (insert a U) := by
  apply feasible_free (g := neg a) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rcases operand_cases (H.valid a) (Or.inr ha : represented [] (H.fn a)) with hz | ho | hm
  · exact Or.inr (fun hp => hp.2.2 (by rw [H.hneg hva, hz, neg_laws.1]))
  · exact Or.inr (fun hp => hp.2.1 (by rw [H.hneg hva, ho, neg_laws.2]))
  · simp at hm
lemma free_binary_left {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (ha : ¬ proper (H.fn a)) (h : Feasible H q (insert (bin d a b) U)) :
    Feasible H q (insert a (insert b U)) := by
  apply feasible_free (g := bin d a b) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hbin, bin_comm]
  rcases operand_cases (H.valid a) (Or.inr ha : represented [] (H.fn a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp => hp.2.1 (bin_laws (H.valid b)).2.2.1)
    · rw [(bin_laws (H.valid b)).2.1]; exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(bin_laws (H.valid b)).1]; exact Or.inl (by simp)
    · exact Or.inr (fun hp => hp.2.2 (bin_laws (H.valid b)).2.2.2.1)
  · simp at hm
lemma free_binary_right {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (hb : ¬ proper (H.fn b)) (h : Feasible H q (insert (bin d a b) U)) :
    Feasible H q (insert a (insert b U)) := by
  rw [bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left hb h
lemma feasible_live {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom) :
    Feasible H k S := by
  induction h with
  | stop => refine ⟨0, Nat.le_refl _, 0, {target}, Live.stop, ?_⟩; simp [H.htarget]
  | unary ha _ _ ih => exact pull_unary ha.1 ih
  | binary _ _ _ _ _ ih => exact pull_binary ih
lemma feasible_const {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom)
    (a : Sig) (ha : a ∈ S) (hc : ¬ proper (H.fn a)) :
    ∃ q < k, Feasible H q S := by
  induction h with
  | stop =>
    have ht : a = target := Finset.mem_singleton.mp ha
    exact (hc (by rw [ht, H.htarget]; exact target_proper)).elim
  | @unary k t U b hp _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k, by omega, free_unary hp.1 hc (feasible_live tail H)⟩
    · obtain ⟨q, hq, h⟩ := ih (Finset.mem_insert_of_mem ha)
      exact ⟨q + 1, by omega, pull_unary hp.1 h⟩
  | @binary k t U b c d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k, by omega, free_binary_left hc (feasible_live tail H)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k, by omega, free_binary_right hc (feasible_live tail H)⟩
      · obtain ⟨q, hq, h⟩ := ih (Finset.mem_insert_of_mem hU)
        exact ⟨q + 1, by omega, pull_binary h⟩
lemma not_proper_bin_consts {H : SigHom} {a b : Sig} (d : Bool)
    (hca : ¬ proper (H.fn a)) (hcb : ¬ proper (H.fn b)) :
    ¬ proper (H.fn (bin d a b)) := by
  rw [H.hbin]
  rcases operand_cases (H.valid a) (Or.inr hca : represented [] (H.fn a)) with ha0 | ha1 | hm
  · rw [ha0, bin_comm]
    rcases operand_cases (H.valid b) (Or.inr hcb : represented [] (H.fn b)) with hb0 | hb1 | hm'
    · rw [hb0]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_zero).2.2.1
      · exact fun hp => hp.2.1 (bin_laws valid_zero).2.1
    · rw [hb1]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_one).2.2.1
      · exact fun hp => hp.2.2 (bin_laws valid_one).2.1
    · simp at hm'
  · rw [ha1, bin_comm]
    rcases operand_cases (H.valid b) (Or.inr hcb : represented [] (H.fn b)) with hb0 | hb1 | hm'
    · rw [hb0]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_zero).1
      · exact fun hp => hp.2.2 (bin_laws valid_zero).2.2.2.1
    · rw [hb1]; cases d
      · exact fun hp => hp.2.2 (bin_laws valid_one).1
      · exact fun hp => hp.2.2 (bin_laws valid_one).2.2.2.1
    · simp at hm'
  · simp at hm
lemma feasible_two_consts {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom)
    (a b : Sig) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : ¬ proper (H.fn a)) (hcb : ¬ proper (H.fn b)) :
    ∃ q, q + 2 ≤ k ∧ Feasible H q S := by
  induction h with
  | stop =>
    have e1 := Finset.mem_singleton.mp ha
    have e2 := Finset.mem_singleton.mp hb
    exact (hab (e1.trans e2.symm)).elim
  | @unary k t U c hpc _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | haU
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hab.symm
      obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
      exact ⟨q, by omega, free_unary hpc.1 hca hf⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q, by omega, free_unary hpc.1 hcb hf⟩
      · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
        exact ⟨q + 1, by omega, pull_unary hpc.1 hf⟩
  | @binary k t U c e d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · rcases Finset.mem_insert.mp hb with hbEq | hb1
      · exact (hab hbEq.symm).elim
      · rcases Finset.mem_insert.mp hb1 with rfl | hbU
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H (bin d a b) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hca hcb)
          exact ⟨q, by omega, free_binary_left hca hf⟩
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
          exact ⟨q, by omega, free_binary_left hca hf⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H (bin d b a) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hcb hca)
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with hbEq | hbU
          · exact (hab hbEq.symm).elim
          · obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
            exact ⟨q, by omega, free_binary_right hca hf⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with rfl | hbU
          · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
            exact ⟨q, by omega, free_binary_right hcb hf⟩
          · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
            exact ⟨q + 1, by omega, pull_binary hf⟩
inductive Tag where
  | tNone
  | tDeg3
  | tSpec0
  | tSpec1
  deriving DecidableEq, BEq
instance : LawfulBEq Tag where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | contradiction
  rfl {a} := by cases a <;> rfl
abbrev Wire := Sig × Tag
def Tag.toNat : Tag → Nat
  | .tNone => 0
  | .tDeg3 => 1
  | .tSpec0 => 2
  | .tSpec1 => 3
def tagOfNat : Nat → Tag
  | 0 => .tNone
  | 1 => .tDeg3
  | 2 => .tSpec0
  | _ => .tSpec1
def updUnaryTag (τ : Sig → Tag) (a : Sig) (x : Sig) : Tag :=
  if x = neg a then (if τ a = .tDeg3 then .tSpec1 else .tNone) else τ x
def updAndTag (τ : Sig → Tag) (a b : Sig) (x : Sig) : Tag :=
  if x = bin false a b then (if τ a = .tDeg3 ∨ τ b = .tDeg3 then .tSpec0 else .tNone) else τ x
def updOrTag (τ : Sig → Tag) (a b : Sig) (x : Sig) : Tag :=
  if x = bin true a b then .tNone
  else if x = a ∧ τ a = .tDeg3 then .tSpec0
  else if x = b ∧ τ b = .tDeg3 then .tSpec0
  else τ x
inductive TRestricted : Nat → Nat → Finset Sig → (Sig → Tag) → Prop
  | stop {τ} : TRestricted 0 0 {target} τ
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} {τ : Sig → Tag}
      (ha : proper a) (hf : neg a ∉ insert a U)
      (hr1 : τ a ≠ .tSpec0 ∧ τ a ≠ .tSpec1)
      (hr2 : τ a = .tDeg3 → a ∉ U)
      (tail : TRestricted k t (insert (neg a) U) (updUnaryTag τ a)) :
      TRestricted (k + 1) (t + 1) (insert a U) τ
  | binaryAnd {k t : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin false a b ∉ insert a (insert b U))
      (hra : τ a ≠ .tSpec0 ∧ (τ a ≠ .tNone → a ∉ U))
      (hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U))
      (tail : TRestricted k t (insert (bin false a b) U) (updAndTag τ a b)) :
      TRestricted (k + 1) t (insert a (insert b U)) τ
  | binaryOr {k t : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin true a b ∉ insert a (insert b U))
      (hra : τ a ≠ .tSpec1 ∧ (τ a = .tSpec0 → a ∉ U))
      (hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U))
      (tail : TRestricted k t (insert (bin true a b) U) (updOrTag τ a b)) :
      TRestricted (k + 1) t (insert a (insert b U)) τ
lemma TRestricted.live {k t S τ} (h : TRestricted k t S τ) : Live k t S := by
  induction h with
  | stop => exact Live.stop
  | unary ha hf _ _ _ ih => exact Live.unary ha hf ih
  | binaryAnd ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih
  | binaryOr ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih
def rootTag (a : Sig) : Tag :=
  if a = raw4 ∨ a = raw6 ∨ a = raw7 then .tSpec0
  else if a ∈ raw then .tDeg3
  else .tNone
def rootWires : List Wire :=
  [(raw0, .tDeg3), (raw1, .tDeg3), (raw2, .tDeg3), (raw3, .tDeg3),
   (raw4, .tSpec0), (raw5, .tDeg3), (raw6, .tSpec0), (raw7, .tSpec0), (raw8, .tDeg3)]
def sigsOf (v : List Wire) : List Sig := v.map Prod.fst
def Represents (v : List Wire) (S : Finset Sig) (τ : Sig → Tag) : Prop :=
  (sigsOf v).Nodup ∧ (sigsOf v).toFinset = S ∧ ∀ w ∈ v, w.2 = τ w.1
def droppedW (del : List Sig) (v : List Wire) : List Wire :=
  v.filter (fun w => !(del.contains w.1))
def unionSepW (d : Bool) : List Wire → Nat
  | [] => 0
  | w :: l => sep d w.1 ||| unionSepW d l
def coverageW (d : Bool) (v : List Wire) : Cov :=
  v.foldr (fun w c => covAdd (sep d w.1) c) (0, 0, 0)
lemma sigsOf_droppedW (del : List Sig) (v : List Wire) :
    sigsOf (droppedW del v) = dropped del (sigsOf v) := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    unfold sigsOf droppedW dropped at ih ⊢
    simp only [List.map_cons, List.filter_cons]
    cases del.contains w.1
    · simp only [Bool.not_false, ite_true, List.map_cons, ih]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ih]
lemma unionSepW_eq (d : Bool) (v : List Wire) : unionSepW d v = unionSep d (sigsOf v) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp [unionSepW, unionSep, sigsOf, ih]
lemma coverageW_eq (d : Bool) (v : List Wire) : coverageW d v = coverage d (sigsOf v) := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    change covAdd (sep d w.1) (coverageW d l) = covAdd (sep d w.1) (coverage d (sigsOf l))
    rw [ih]
lemma sigsOf_length (v : List Wire) : (sigsOf v).length = v.length := List.length_map ..
lemma mem_sigsOf_iff {v : List Wire} {a : Sig} {τ : Sig → Tag}
    (ht : ∀ w ∈ v, w.2 = τ w.1) : (a, τ a) ∈ v ↔ a ∈ sigsOf v := by
  constructor
  · intro h; exact List.mem_map.mpr ⟨(a, τ a), h, rfl⟩
  · intro h; obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
    have htag := ht w hw
    have : w = (a, τ a) := Prod.ext heq (by rw [htag, heq])
    rwa [← this]
def tagEq : Tag → Tag → Bool
  | .tNone, .tNone => true
  | .tDeg3, .tDeg3 => true
  | .tSpec0, .tSpec0 => true
  | .tSpec1, .tSpec1 => true
  | _, _ => false
lemma tagEq_iff {a b : Tag} : tagEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [tagEq]
def isNotSpec0 : Tag → Bool | .tSpec0 => false | _ => true
def isNotSpec1 : Tag → Bool | .tSpec1 => false | _ => true
def isNoneTag : Tag → Bool | .tNone => true | _ => false
def isDeg3Tag : Tag → Bool | .tDeg3 => true | _ => false
def sigEq (a b : Sig) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2 b.2
lemma sigEq_iff {a b : Sig} : sigEq a b = true ↔ a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [sigEq, Bool.and_eq_true, Nat.beq_eq, Prod.mk.injEq]
lemma nat_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr fun e => h (Nat.beq_eq.mp e)
def gateAvail (g : Sig) : List Wire → Bool
  | [] => !sigEq g zero && !sigEq g one
  | w :: l => !sigEq w.1 g && gateAvail g l
lemma gateAvail_eq_true {v : List Wire} {g : Sig} (hg : g ∉ sigsOf v) (hp : proper g) :
    gateAvail g v = true := by
  induction v with
  | nil =>
    simp only [gateAvail, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, sigEq_iff]
    exact ⟨hp.2.1, hp.2.2⟩
  | cons w l ih =>
    simp only [sigsOf, List.map_cons, List.mem_cons, not_or] at hg
    simp only [gateAvail, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, sigEq_iff]
    exact ⟨Ne.symm hg.1, ih hg.2⟩
def dropOne (a : Sig) : List Wire → List Wire
  | [] => []
  | w :: l => if sigEq w.1 a then dropOne a l else w :: dropOne a l
lemma dropOne_eq (a : Sig) (v : List Wire) : dropOne a v = droppedW [a] v := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    simp only [dropOne, droppedW, List.filter_cons, List.contains_eq_mem, List.mem_singleton, ih]
    by_cases h : w.1 = a
    · have hs : sigEq w.1 a = true := sigEq_iff.mpr h
      rw [hs]; simp [h]
    · have hs : sigEq w.1 a = false := Bool.eq_false_iff.mpr (fun e => h (sigEq_iff.mp e))
      rw [hs]; simp [h]
def dropTwo (a b : Sig) : List Wire → List Wire
  | [] => []
  | w :: l => if sigEq w.1 a || sigEq w.1 b then dropTwo a b l else w :: dropTwo a b l
lemma dropTwo_eq (a b : Sig) (v : List Wire) : dropTwo a b v = droppedW [a, b] v := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    simp only [dropTwo, droppedW, List.filter_cons, List.contains_eq_mem, List.mem_cons,
      List.not_mem_nil, or_false, ih]
    by_cases h1 : w.1 = a
    · have hs1 : sigEq w.1 a = true := sigEq_iff.mpr h1
      rw [hs1]; simp [h1]
    · have hs1 : sigEq w.1 a = false := Bool.eq_false_iff.mpr (fun e => h1 (sigEq_iff.mp e))
      by_cases h2 : w.1 = b
      · have hs2 : sigEq w.1 b = true := sigEq_iff.mpr h2
        rw [hs1, hs2]; simp [h2]
      · have hs2 : sigEq w.1 b = false := Bool.eq_false_iff.mpr (fun e => h2 (sigEq_iff.mp e))
        rw [hs1, hs2]; simp [h1, h2]
def sep0 (a : Sig) : Nat := Nat.land a.1 (Nat.xor a.2 top)
def sep1 (a : Sig) : Nat := Nat.xor a.1 a.2
lemma sep0_eq (a : Sig) : sep0 a = sep false a := rfl
lemma sep1_eq (a : Sig) : sep1 a = sep true a := rfl
lemma bin_false_eq (a b : Sig) : bin false a b = (Nat.land a.1 b.1, Nat.land a.2 b.2) := rfl
lemma bin_true_eq (a b : Sig) : bin true a b = (Nat.lor a.1 b.1, Nat.lor a.2 b.2) := rfl
structure WSep where
  w : Wire
  p : Nat
  n : Nat
  tg : Tag
  s : Nat
def mkSep0 (w : Wire) : WSep := ⟨w, w.1.1, w.1.2, w.2, sep0 w.1⟩
def mkSep1 (w : Wire) : WSep := ⟨w, w.1.1, w.1.2, w.2, sep1 w.1⟩
def buildSeps0 : List Wire → List WSep × Cov
  | [] => ([], (0, 0, 0))
  | w :: l =>
    let (ls, c) := buildSeps0 l
    let s := sep0 w.1
    (⟨w, w.1.1, w.1.2, w.2, s⟩ :: ls, covAdd s c)
def buildSeps1 : List Wire → List WSep × Cov
  | [] => ([], (0, 0, 0))
  | w :: l =>
    let (ls, c) := buildSeps1 l
    let s := sep1 w.1
    (⟨w, w.1.1, w.1.2, w.2, s⟩ :: ls, covAdd s c)
lemma buildSeps0_eq (v : List Wire) : buildSeps0 v = (v.map mkSep0, coverageW false v) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [buildSeps0, ih, List.map_cons, mkSep0]; rfl
lemma buildSeps1_eq (v : List Wire) : buildSeps1 v = (v.map mkSep1, coverageW true v) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [buildSeps1, ih, List.map_cons, mkSep1]; rfl
structure WAct0 where
  w : Wire
  p : Nat
  n : Nat
  tg : Tag
  s : Nat
  u : Nat
def mkAct0 (uMask : Nat) (w : Wire) : WAct0 :=
  let s := sep0 w.1
  ⟨w, w.1.1, w.1.2, w.2, s, Nat.land uMask s⟩
def buildActs0 (uMask : Nat) : List WSep → List WAct0
  | [] => []
  | a :: l => ⟨a.w, a.p, a.n, a.tg, a.s, Nat.land uMask a.s⟩ :: buildActs0 uMask l
lemma buildActs0_map (uMask : Nat) (v : List Wire) :
    buildActs0 uMask (v.map mkSep0) = v.map (mkAct0 uMask) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [List.map_cons, buildActs0, mkSep0, mkAct0, ih]
structure WAct1 where
  w : Wire
  p : Nat
  n : Nat
  tg : Tag
  s : Nat
  up : Nat
  un : Nat
def mkAct1 (uMask : Nat) (w : Wire) : WAct1 :=
  let s := sep1 w.1
  let u := Nat.land uMask s
  ⟨w, w.1.1, w.1.2, w.2, s, Nat.land u w.1.1, Nat.land u w.1.2⟩
def buildActs1 (uMask : Nat) : List WSep → List WAct1
  | [] => []
  | a :: l =>
    let u := Nat.land uMask a.s
    ⟨a.w, a.p, a.n, a.tg, a.s, Nat.land u a.p, Nat.land u a.n⟩ :: buildActs1 uMask l
lemma buildActs1_map (uMask : Nat) (v : List Wire) :
    buildActs1 uMask (v.map mkSep1) = v.map (mkAct1 uMask) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [List.map_cons, buildActs1, mkSep1, mkAct1, ih]
def fastPair0 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct0) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    Nat.beq (Nat.land a.u b.p) a.u && Nat.beq (Nat.land b.u a.p) b.u &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    r ((g, gt) :: dropTwo a.w.1 b.w.1 v)
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    Nat.beq (Nat.land a.u b.n) 0 && Nat.beq (Nat.land b.u a.n) 0 &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    r ((g, .tNone) :: dropTwo a.w.1 b.w.1 v)
  tryAnd || tryOr
def fastPair1 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct1) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land b.up a.p) b.up &&
    Nat.beq (Nat.land a.un b.n) a.un && Nat.beq (Nat.land b.un a.n) b.un &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    r ((g, gt) :: dropTwo a.w.1 b.w.1 v)
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land b.up a.n) 0 &&
    Nat.beq (Nat.land a.un b.p) 0 && Nat.beq (Nat.land b.un a.p) 0 &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    r ((g, .tNone) :: dropTwo a.w.1 b.w.1 v)
  tryAnd || tryOr
def tryKeeps1 (r : List Wire → Bool) (v : List Wire) (a b : Sig)
    (base sa sb : Nat) (g wa wb : Wire) (ka kb ua ub : Bool) : Bool :=
  let ok0 := ua && ub && Nat.beq base top
  let okA := ka && ub && Nat.beq (Nat.lor base sa) top
  let okB := kb && ua && Nat.beq (Nat.lor base sb) top
  (ok0 || okA || okB) && gateAvail g.1 v &&
    let rest := dropTwo a b v
    ((ok0 && r (g :: rest)) ||
     (okA && r (g :: wa :: rest)) ||
     (okB && r (g :: wb :: rest)))
def tryKeeps2 (r : List Wire → Bool) (v : List Wire) (a b : Sig)
    (base sa sb : Nat) (g wa wb : Wire) (ka kb : Bool) : Bool :=
  let ok0 := Nat.beq base top
  let okA := ka && Nat.beq (Nat.lor base sa) top
  let okB := kb && Nat.beq (Nat.lor base sb) top
  let okAB := ka && kb && Nat.beq (Nat.lor (Nat.lor base sa) sb) top
  (ok0 || okA || okB || okAB) && gateAvail g.1 v &&
    let rest := dropTwo a b v
    ((ok0 && r (g :: rest)) ||
     (okA && r (g :: wa :: rest)) ||
     (okB && r (g :: wb :: rest)) ||
     (okAB && r (g :: wa :: wb :: rest)))
def slow1Pair0 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct0) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    let ua := Nat.beq (Nat.land a.u b.p) a.u
    let ub := Nat.beq (Nat.land b.u a.p) b.u
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb ua ub
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    let ua := Nat.beq (Nat.land a.u b.n) 0
    let ub := Nat.beq (Nat.land b.u a.n) 0
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb ua ub
  tryAnd || tryOr
def slow1Pair1 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct1) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    let ua := Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un
    let ub := Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb ua ub
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    let ua := Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0
    let ub := Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb ua ub
  tryAnd || tryOr
def slow2Pair0 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct0) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    (ka || Nat.beq (Nat.land a.u b.p) a.u) && (kb || Nat.beq (Nat.land b.u a.p) b.u) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    (ka || Nat.beq (Nat.land a.u b.n) 0) && (kb || Nat.beq (Nat.land b.u a.n) 0) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb
  tryAnd || tryOr
def slow2Pair1 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct1) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    (ka || (Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un)) &&
    (kb || (Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un)) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    (ka || (Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0)) &&
    (kb || (Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0)) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb
  tryAnd || tryOr
def scanFast0One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct0) : List WAct0 → Bool
  | [] => false
  | b :: l => fastPair0 r v c a b || scanFast0One r v c a l
def scanFast0 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct0 → Bool
  | [] => false
  | a :: l => scanFast0One r v c a l || scanFast0 r v c l
def scanFast1One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct1) : List WAct1 → Bool
  | [] => false
  | b :: l => fastPair1 r v c a b || scanFast1One r v c a l
def scanFast1 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct1 → Bool
  | [] => false
  | a :: l => scanFast1One r v c a l || scanFast1 r v c l
def scanSlow10One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct0) : List WAct0 → Bool
  | [] => false
  | b :: l => slow1Pair0 r v c a b || scanSlow10One r v c a l
def scanSlow10 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct0 → Bool
  | [] => false
  | a :: l => scanSlow10One r v c a l || scanSlow10 r v c l
def scanSlow11One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct1) : List WAct1 → Bool
  | [] => false
  | b :: l => slow1Pair1 r v c a b || scanSlow11One r v c a l
def scanSlow11 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct1 → Bool
  | [] => false
  | a :: l => scanSlow11One r v c a l || scanSlow11 r v c l
def scanSlow20One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct0) : List WAct0 → Bool
  | [] => false
  | b :: l => slow2Pair0 r v c a b || scanSlow20One r v c a l
def scanSlow20 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct0 → Bool
  | [] => false
  | a :: l => scanSlow20One r v c a l || scanSlow20 r v c l
def scanSlow21One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct1) : List WAct1 → Bool
  | [] => false
  | b :: l => slow2Pair1 r v c a b || scanSlow21One r v c a l
def scanSlow21 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct1 → Bool
  | [] => false
  | a :: l => scanSlow21One r v c a l || scanSlow21 r v c l
def unaryScan0 (lim n : Nat) (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WSep → Bool
  | [] => false
  | a :: l =>
    (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top
      let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) ||
         (okA && r (((gp, gn), gt) :: a.w :: rest)))) ||
    unaryScan0 lim n r v c l
def unaryScan1 (lim n : Nat) (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WSep → Bool
  | [] => false
  | a :: l =>
    (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top
      let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.xor gp gn) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) ||
         (okA && r (((gp, gn), gt) :: a.w :: rest)))) ||
    unaryScan1 lim n r v c l
def binaryMoves (k t len : Nat) (r : List Wire → Bool) (v : List Wire) : Bool :=
  let lim := k - t + 1
  if Nat.beq t 0 then
    let (seps, c) := buildSeps0 v
    let acts := buildActs0 c.2.1 seps
    if Nat.beq len (lim + 1) then scanFast0 r v c acts
    else if Nat.beq len lim then scanSlow10 r v c acts
    else scanSlow20 r v c acts
  else
    let (seps, c) := buildSeps1 v
    let acts := buildActs1 c.2.1 seps
    if Nat.beq len (lim + 1) then scanFast1 r v c acts
    else if Nat.beq len lim then scanSlow11 r v c acts
    else scanSlow21 r v c acts
def unaryMoves (k t len : Nat) (r : List Wire → Bool) (v : List Wire) : Bool :=
  if Nat.beq t 0 then
    let (seps, c) := buildSeps0 v
    unaryScan0 (k - t + 1) (len - 1) r v c seps
  else
    let (seps, c) := buildSeps1 v
    unaryScan1 (k - t + 1) (len - 1) r v c seps
def stepTest (k t : Nat) (v : List Wire) (u b : List Wire → Bool) : Bool :=
  let len := v.length
  if Nat.blt (k + 1) t || Nat.blt (k + 1 - t + 1) len then false else
    (match v with | [w] => sigEq w.1 target | _ => false) ||
    (Nat.blt 0 t && unaryMoves k (t - 1) len u v) ||
    binaryMoves k t len b v
def search : Nat → Nat → List Wire → Bool
  | 0, _, v => match v with | [w] => sigEq w.1 target | _ => false
  | k + 1, t, v => stepTest k t v (search k (t - 1)) (search k t)
def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t
lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h; exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h; exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))
lemma scanFast0One_eq (r v c a l) : scanFast0One r v c a l = l.any (fastPair0 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanFast0One, ih]
lemma scanFast0_eq (r v c l) : scanFast0 r v c l = scanPairs (fastPair0 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanFast0, scanPairs, scanFast0One_eq, ih]
lemma scanFast1One_eq (r v c a l) : scanFast1One r v c a l = l.any (fastPair1 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanFast1One, ih]
lemma scanFast1_eq (r v c l) : scanFast1 r v c l = scanPairs (fastPair1 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanFast1, scanPairs, scanFast1One_eq, ih]
lemma scanSlow10One_eq (r v c a l) : scanSlow10One r v c a l = l.any (slow1Pair0 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow10One, ih]
lemma scanSlow10_eq (r v c l) : scanSlow10 r v c l = scanPairs (slow1Pair0 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow10, scanPairs, scanSlow10One_eq, ih]
lemma scanSlow11One_eq (r v c a l) : scanSlow11One r v c a l = l.any (slow1Pair1 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow11One, ih]
lemma scanSlow11_eq (r v c l) : scanSlow11 r v c l = scanPairs (slow1Pair1 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow11, scanPairs, scanSlow11One_eq, ih]
lemma scanSlow20One_eq (r v c a l) : scanSlow20One r v c a l = l.any (slow2Pair0 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow20One, ih]
lemma scanSlow20_eq (r v c l) : scanSlow20 r v c l = scanPairs (slow2Pair0 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow20, scanPairs, scanSlow20One_eq, ih]
lemma scanSlow21One_eq (r v c a l) : scanSlow21One r v c a l = l.any (slow2Pair1 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow21One, ih]
lemma scanSlow21_eq (r v c l) : scanSlow21 r v c l = scanPairs (slow2Pair1 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow21, scanPairs, scanSlow21One_eq, ih]
lemma unique_and_0 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep0 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo c (sep0 a) (sep0 b))) extra = top) :
    Nat.land (Nat.land c.2.1 (sep0 a)) b.1 = Nat.land c.2.1 (sep0 a) := by
  apply Nat.eq_of_testBit_eq; intro i
  have hh := congrArg (fun z : Nat => z.testBit i) h
  have hx := congrArg (fun z : Nat => z.testBit i) hex
  have h1 := hc.2.2.2.1 i
  by_cases hi : i < 414
  · simp only [sep0, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
      Nat.testBit_and, hi, decide_true, Nat.zero_testBit, Bool.false_eq_true, ite_false] at hh hx ⊢
    revert hh hx h1
    cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
      cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases extra.testBit i <;> simp
  · simp [hc.2.1 i (by omega)]
lemma unique_or_0 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep0 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo c (sep0 a) (sep0 b))) extra = top) :
    Nat.land (Nat.land c.2.1 (sep0 a)) b.2 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have hh := congrArg (fun z : Nat => z.testBit i) h
  have hx := congrArg (fun z : Nat => z.testBit i) hex
  have h1 := hc.2.2.2.1 i
  by_cases hi : i < 414
  · simp only [sep0, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
      Nat.testBit_or, hi, decide_true, Nat.zero_testBit, ite_true] at hh hx ⊢
    revert hh hx h1
    cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
      cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases extra.testBit i <;> simp
  · simp [hc.2.1 i (by omega)]
lemma unique_and_1 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep1 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo c (sep1 a) (sep1 b))) extra = top) :
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.1) b.1 = Nat.land (Nat.land c.2.1 (sep1 a)) a.1 ∧
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.2) b.2 = Nat.land (Nat.land c.2.1 (sep1 a)) a.2 := by
  constructor <;> (
    apply Nat.eq_of_testBit_eq; intro i
    have hh := congrArg (fun z : Nat => z.testBit i) h
    have hx := congrArg (fun z : Nat => z.testBit i) hex
    have h1 := hc.2.2.2.1 i
    by_cases hi : i < 414
    · simp only [sep1, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
        Nat.testBit_and, hi, decide_true, Nat.zero_testBit, Bool.false_eq_true, ite_false] at hh hx ⊢
      revert hh hx h1
      cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
        cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
        cases extra.testBit i <;> simp
    · simp [hc.2.1 i (by omega)])
lemma unique_or_1 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep1 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo c (sep1 a) (sep1 b))) extra = top) :
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.1) b.2 = 0 ∧
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.2) b.1 = 0 := by
  constructor <;> (
    apply Nat.eq_of_testBit_eq; intro i
    have hh := congrArg (fun z : Nat => z.testBit i) h
    have hx := congrArg (fun z : Nat => z.testBit i) hex
    have h1 := hc.2.2.2.1 i
    by_cases hi : i < 414
    · simp only [sep1, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
        Nat.testBit_or, hi, decide_true, Nat.zero_testBit, ite_true] at hh hx ⊢
      revert hh hx h1
      cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
        cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
        cases extra.testBit i <;> simp
    · simp [hc.2.1 i (by omega)])
lemma unaryScan0_mem {lim n : Nat} {r : List Wire → Bool} {v : List Wire} {c : Cov}
    {a : WSep} {l : List WSep} (ha : a ∈ l)
    (hok : (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top; let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) || (okA && r (((gp, gn), gt) :: a.w :: rest)))) = true) :
    unaryScan0 lim n r v c l = true := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [unaryScan0, Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl | hx
    · exact Or.inl hok
    · exact Or.inr (ih hx)
lemma unaryScan1_mem {lim n : Nat} {r : List Wire → Bool} {v : List Wire} {c : Cov}
    {a : WSep} {l : List WSep} (ha : a ∈ l)
    (hok : (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top; let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.xor gp gn) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) || (okA && r (((gp, gn), gt) :: a.w :: rest)))) = true) :
    unaryScan1 lim n r v c l = true := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [unaryScan1, Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl | hx
    · exact Or.inl hok
    · exact Or.inr (ih hx)
lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hrep : Represents v (insert a U) τ) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U)
    (hr1 : τ a ≠ .tSpec0 ∧ τ a ≠ .tSpec1) (hr2 : τ a = .tDeg3 → a ∉ U)
    (l : TRestricted m t (insert (neg a) U) (updUnaryTag τ a))
    (ih : ∀ w : List Wire, Represents w (insert (neg a) U) (updUnaryTag τ a) → r w = true) :
    unaryMoves k t v.length r v = true := by
  obtain ⟨hndS, heS, htag⟩ := hrep
  have hval : ∀ x ∈ sigsOf v, Valid x := by
    intro x hx
    rcases Finset.mem_insert.mp (heS ▸ List.mem_toFinset.mpr hx) with rfl | hxU
    · exact ha.1
    · exact (live_proper l.live x (Finset.mem_insert_of_mem hxU)).1
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_self _ _)
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff htag).mpr ahS
  let rest := droppedW [a] v
  let gTag : Tag := if isDeg3Tag (τ a) then .tSpec1 else .tNone
  let g : Wire := (neg a, gTag)
  let h : List Wire := if a ∈ U then [(a, τ a)] else []
  have hSigsH : sigsOf h = keepOf U [a] := by by_cases hm : a ∈ U <;> simp [h, sigsOf, keepOf, hm]
  obtain ⟨hn, eq⟩ := edit_list (del := [a]) (U := U) hndS (by simp) (by simpa using heS)
  have hSigsHR : sigsOf (h ++ rest) = keepOf U [a] ++ dropped [a] (sigsOf v) := by
    change (h ++ rest).map Prod.fst = _
    rw [List.map_append, show h.map Prod.fst = keepOf U [a] from hSigsH,
      show rest.map Prod.fst = dropped [a] (sigsOf v) from sigsOf_droppedW [a] v]
  have nn : neg a ∉ sigsOf v := fun hm => fresh (heS ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (sigsOf (g :: (h ++ rest))).Nodup := by
    change (neg a :: sigsOf (h ++ rest)).Nodup; rw [hSigsHR]
    exact List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm), hn⟩
  have e : (sigsOf (g :: (h ++ rest))).toFinset = insert (neg a) U := by
    change (neg a :: sigsOf (h ++ rest)).toFinset = _; rw [List.toFinset_cons, hSigsHR, eq]
  have htag' : ∀ w ∈ g :: (h ++ rest), w.2 = updUnaryTag τ a w.1 := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
    · simp only [g, gTag, updUnaryTag, ite_true]; cases τ a <;> rfl
    · have hwV : w ∈ v := by
        rcases List.mem_append.mp hw' with hh | hr
        · by_cases hm : a ∈ U
          · simp only [h, hm, ite_true, List.mem_singleton] at hh; exact hh ▸ ah
          · simp [h, hm] at hh
        · exact List.mem_of_mem_filter hr
      have hwNe : w.1 ≠ neg a := fun heq => nn (heq ▸ List.mem_map_of_mem hwV)
      simp [updUnaryTag, hwNe, htag w hwV]
  have hr := ih _ ⟨hnd, e, htag'⟩
  obtain ⟨ht, hc⟩ := live_size l.live
  rw [← e, List.toFinset_card_of_nodup hnd] at hc
  simp only [sigsOf, List.map_cons, List.map_append, List.length_cons, List.length_append,
    List.length_map] at hc
  have hav : gateAvail (neg a) v = true :=
    gateAvail_eq_true nn (live_proper l.live _ (Finset.mem_insert_self _ _))
  have hns0 : isNotSpec0 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec0]; exact hr1.1 hta
  have hns1 : isNotSpec1 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec1]; exact hr1.2 hta
  have cv := live_cover l.live e
  simp only [sigsOf, List.map_cons, List.map_append, unionSep, union_append] at cv
  have hcv' : (sep (decide (0 < t)) (neg a) ||| unionSep (decide (0 < t)) (sigsOf rest)) |||
      unionSepW (decide (0 < t)) h = top := by
    rw [unionSepW_eq, ← cv]; unfold sigsOf; ac_rfl
  obtain ⟨hlen, hmask⟩ := one_rest (decide (0 < t)) hndS hval ahS
  rw [sigsOf_length, ← sigsOf_droppedW, sigsOf_length] at hlen
  change v.length - 1 = rest.length at hlen
  rw [← sigsOf_droppedW] at hmask
  change takeOne (coverage (decide (0 < t)) (sigsOf v)) (sep (decide (0 < t)) a) =
    unionSep (decide (0 < t)) (sigsOf rest) at hmask
  have hdrop : dropOne a v = rest := dropOne_eq a v
  unfold unaryMoves
  by_cases ht0 : t = 0
  · subst ht0
    have hdt0 : decide (0 < 0) = false := rfl
    rw [hdt0] at hcv' hmask
    simp only [Nat.beq_refl, ite_true, buildSeps0_eq]
    apply unaryScan0_mem (a := mkSep0 (a, τ a)) (List.mem_map_of_mem ah)
    simp only [mkSep0, coverageW_eq]
    change (isNotSpec0 (τ a) && isNotSpec1 (τ a) &&
      let base := Nat.lor (sep false (neg a)) (takeOne (coverage false (sigsOf v)) (sep false a))
      let ka := !isDeg3Tag (τ a) && Nat.ble (v.length - 1 + 2) (k - 0 + 1)
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base (sep false a)) top
      (ok0 || okA) && gateAvail (neg a) v &&
        let rest' := dropOne a v
        ((ok0 && r (g :: rest')) || (okA && r (g :: (a, τ a) :: rest')))) = true
    rw [hmask, hdrop]
    by_cases haU : a ∈ U
    · have hnd3 : (!isDeg3Tag (τ a)) = true := by
        cases hta : τ a <;> simp [isDeg3Tag]; exact hr2 hta haU
      have hlenH : h.length = 1 := by simp [h, haU]
      have hle' : Nat.ble (v.length - 1 + 2) (k - 0 + 1) = true := Nat.ble_eq.mpr (by omega)
      have hcovA : Nat.lor (Nat.lor (sep false (neg a)) (unionSep false (sigsOf rest))) (sep false a) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hrA : r (g :: (a, τ a) :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hnd3, hle', hcovA, Nat.beq_refl, hav, hrA, Bool.true_and, Bool.or_true]
    · have hcov0 : Nat.lor (sep false (neg a)) (unionSep false (sigsOf rest)) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hr0 : r (g :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hcov0, Nat.beq_refl, hav, hr0, Bool.true_and, Bool.true_or]
  · have hbf : Nat.beq t 0 = false := nat_beq_false ht0
    have hdt : decide (0 < t) = true := decide_eq_true (by omega)
    rw [hdt] at hcv' hmask
    simp only [hbf, Bool.false_eq_true, ite_false, buildSeps1_eq]
    apply unaryScan1_mem (a := mkSep1 (a, τ a)) (List.mem_map_of_mem ah)
    simp only [mkSep1, coverageW_eq]
    change (isNotSpec0 (τ a) && isNotSpec1 (τ a) &&
      let base := Nat.lor (sep true (neg a)) (takeOne (coverage true (sigsOf v)) (sep true a))
      let ka := !isDeg3Tag (τ a) && Nat.ble (v.length - 1 + 2) (k - t + 1)
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base (sep true a)) top
      (ok0 || okA) && gateAvail (neg a) v &&
        let rest' := dropOne a v
        ((ok0 && r (g :: rest')) || (okA && r (g :: (a, τ a) :: rest')))) = true
    rw [hmask, hdrop]
    by_cases haU : a ∈ U
    · have hnd3 : (!isDeg3Tag (τ a)) = true := by
        cases hta : τ a <;> simp [isDeg3Tag]; exact hr2 hta haU
      have hlenH : h.length = 1 := by simp [h, haU]
      have hle' : Nat.ble (v.length - 1 + 2) (k - t + 1) = true := Nat.ble_eq.mpr (by omega)
      have hcovA : Nat.lor (Nat.lor (sep true (neg a)) (unionSep true (sigsOf rest))) (sep true a) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hrA : r (g :: (a, τ a) :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hnd3, hle', hcovA, Nat.beq_refl, hav, hrA, Bool.true_and, Bool.or_true]
    · have hcov0 : Nat.lor (sep true (neg a)) (unionSep true (sigsOf rest)) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hr0 : r (g :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hcov0, Nat.beq_refl, hav, hr0, Bool.true_and, Bool.true_or]
lemma bor_l {p q : Bool} (h : p = true) : (p || q) = true := by simp [h]
lemma bor_r {p q : Bool} (h : q = true) : (p || q) = true := by simp [h]
lemma band2 {p q : Bool} (hp : p = true) (hq : q = true) : (p && q) = true := by simp [hp, hq]
lemma tryKeeps1_guard {r v a b base sa sb g wa wb ka kb ua ub}
    (h : tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true) :
    (ua || ub) = true ∧ (ua || ka) = true ∧ (ub || kb) = true := by
  cases ka <;> cases kb <;> cases ua <;> cases ub <;> simp_all [tryKeeps1]
lemma tryKeeps1_0 {r v a b base sa sb g wa wb ka kb ua ub}
    (h1 : ua = true) (h2 : ub = true) (h3 : base = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: dropTwo a b v) = true) :
    tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true := by
  simp only [tryKeeps1, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or]
lemma tryKeeps1_A {r v a b base sa sb g wa wb ka kb ua ub}
    (h1 : ka = true) (h2 : ub = true) (h3 : Nat.lor base sa = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wa :: dropTwo a b v) = true) :
    tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true := by
  simp only [tryKeeps1, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or, Bool.or_true]
lemma tryKeeps1_B {r v a b base sa sb g wa wb ka kb ua ub}
    (h1 : kb = true) (h2 : ua = true) (h3 : Nat.lor base sb = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wb :: dropTwo a b v) = true) :
    tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true := by
  simp only [tryKeeps1, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.or_true]
lemma tryKeeps2_0 {r v a b base sa sb g wa wb ka kb}
    (h3 : base = top) (h4 : gateAvail g.1 v = true) (h5 : r (g :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or]
lemma tryKeeps2_A {r v a b base sa sb g wa wb ka kb}
    (h1 : ka = true) (h3 : Nat.lor base sa = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wa :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h1, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or, Bool.or_true]
lemma tryKeeps2_B {r v a b base sa sb g wa wb ka kb}
    (h1 : kb = true) (h3 : Nat.lor base sb = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wb :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h1, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or, Bool.or_true]
lemma tryKeeps2_AB {r v a b base sa sb g wa wb ka kb}
    (h1 : ka = true) (h2 : kb = true) (h3 : Nat.lor (Nat.lor base sa) sb = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wa :: wb :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.or_true]
lemma fastPair0_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (h3 : Nat.land a.u b.p = a.u) (h4 : Nat.land b.u a.p = b.u)
    (h5 : Nat.lor (Nat.land (Nat.land a.p b.p) (Nat.xor (Nat.land a.n b.n) top)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.land a.p b.p, Nat.land a.n b.n) v = true)
    (h7 : r (((Nat.land a.p b.p, Nat.land a.n b.n),
      if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair0 r v c a b = true := by
  simp only [fastPair0, h1, h2, h3, h4, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.true_or]
lemma fastPair0_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (h3 : Nat.land a.u b.n = 0) (h4 : Nat.land b.u a.n = 0)
    (h5 : Nat.lor (Nat.land (Nat.lor a.p b.p) (Nat.xor (Nat.lor a.n b.n) top)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.lor a.p b.p, Nat.lor a.n b.n) v = true)
    (h7 : r (((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair0 r v c a b = true := by
  simp only [fastPair0, h1, h2, h3, h4, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.or_true]
lemma fastPair1_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (h3a : Nat.land a.up b.p = a.up) (h3b : Nat.land b.up a.p = b.up)
    (h4a : Nat.land a.un b.n = a.un) (h4b : Nat.land b.un a.n = b.un)
    (h5 : Nat.lor (Nat.xor (Nat.land a.p b.p) (Nat.land a.n b.n)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.land a.p b.p, Nat.land a.n b.n) v = true)
    (h7 : r (((Nat.land a.p b.p, Nat.land a.n b.n),
      if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair1 r v c a b = true := by
  simp only [fastPair1, h1, h2, h3a, h3b, h4a, h4b, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.true_or]
lemma fastPair1_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (h3a : Nat.land a.up b.n = 0) (h3b : Nat.land b.up a.n = 0)
    (h4a : Nat.land a.un b.p = 0) (h4b : Nat.land b.un a.p = 0)
    (h5 : Nat.lor (Nat.xor (Nat.lor a.p b.p) (Nat.lor a.n b.n)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.lor a.p b.p, Nat.lor a.n b.n) v = true)
    (h7 : r (((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair1 r v c a b = true := by
  simp only [fastPair1, h1, h2, h3a, h3b, h4a, h4b, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.or_true]
lemma slow1Pair0_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.land a.p b.p) (Nat.xor (Nat.land a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg)
      (Nat.beq (Nat.land a.u b.p) a.u) (Nat.beq (Nat.land b.u a.p) b.u) = true) :
    slow1Pair0 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair0, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.true_or]
lemma slow1Pair0_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.lor a.p b.p) (Nat.xor (Nat.lor a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg)
      (Nat.beq (Nat.land a.u b.n) 0) (Nat.beq (Nat.land b.u a.n) 0) = true) :
    slow1Pair0 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair0, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.or_true]
lemma slow1Pair1_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.land a.p b.p) (Nat.land a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg)
      (Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un)
      (Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un) = true) :
    slow1Pair1 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair1, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.true_or]
lemma slow1Pair1_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.lor a.p b.p) (Nat.lor a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg)
      (Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0)
      (Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0) = true) :
    slow1Pair1 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair1, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.or_true]
lemma slow2Pair0_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ga : (isNoneTag a.tg || Nat.beq (Nat.land a.u b.p) a.u) = true)
    (gb : (isNoneTag b.tg || Nat.beq (Nat.land b.u a.p) b.u) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.land a.p b.p) (Nat.xor (Nat.land a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg) = true) :
    slow2Pair0 r v c a b = true := by
  simp only [slow2Pair0, h1, h2, ga, gb, ht, Bool.true_and, Bool.true_or]
lemma slow2Pair0_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ga : (isNotSpec0 a.tg || Nat.beq (Nat.land a.u b.n) 0) = true)
    (gb : (isNotSpec0 b.tg || Nat.beq (Nat.land b.u a.n) 0) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.lor a.p b.p) (Nat.xor (Nat.lor a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg) = true) :
    slow2Pair0 r v c a b = true := by
  simp only [slow2Pair0, h1, h2, ga, gb, ht, Bool.true_and, Bool.or_true]
lemma slow2Pair1_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ga : (isNoneTag a.tg || (Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un)) = true)
    (gb : (isNoneTag b.tg || (Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un)) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.land a.p b.p) (Nat.land a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg) = true) :
    slow2Pair1 r v c a b = true := by
  simp only [slow2Pair1, h1, h2, ga, gb, ht, Bool.true_and, Bool.true_or]
lemma slow2Pair1_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ga : (isNotSpec0 a.tg || (Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0)) = true)
    (gb : (isNotSpec0 b.tg || (Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0)) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.lor a.p b.p) (Nat.lor a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg) = true) :
    slow2Pair1 r v c a b = true := by
  simp only [slow2Pair1, h1, h2, ga, gb, ht, Bool.true_and, Bool.or_true]
lemma pair_and_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin false a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec0 ∧ (τ a ≠ .tNone → a ∉ U))
    (hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U))
    (l : TRestricted m t (insert (bin false a b) U) (updAndTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin false a b) U) (updAndTag τ a b) → r w = true) :
    let lim := k - t + 1
    let c0 := coverageW false v
    let c1 := coverageW true v
    (t = 0 →
      (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      slow2Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
    (t ≠ 0 →
      (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      slow2Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) := by
  obtain ⟨hndS, heS, htag⟩ := hrep
  have hval : ∀ x ∈ sigsOf v, Valid x := by
    intro x hx
    rcases Finset.mem_insert.mp (heS ▸ List.mem_toFinset.mpr hx) with rfl | hx1
    · exact ha.1
    rcases Finset.mem_insert.mp hx1 with rfl | hxU
    · exact hb.1
    · exact (live_proper l.live x (Finset.mem_insert_of_mem hxU)).1
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff htag).mpr ahS
  have bh : (b, τ b) ∈ v := (mem_sigsOf_iff htag).mpr bhS
  let rest := droppedW [a, b] v
  let gTag : Tag := if isDeg3Tag (τ a) || isDeg3Tag (τ b) then .tSpec0 else .tNone
  let g : Wire := (bin false a b, gTag)
  let h : List Wire := (if a ∈ U then [(a, τ a)] else []) ++ (if b ∈ U then [(b, τ b)] else [])
  have hSigsH : sigsOf h = keepOf U [a, b] := by
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [h, sigsOf, keepOf, haU, hbU]
  obtain ⟨hn, eq⟩ := edit_list (del := [a, b]) (U := U) hndS (by simp [hab]) (by simpa using heS)
  have hSigsHR : sigsOf (h ++ rest) = keepOf U [a, b] ++ dropped [a, b] (sigsOf v) := by
    change (h ++ rest).map Prod.fst = _
    rw [List.map_append, show h.map Prod.fst = keepOf U [a, b] from hSigsH,
      show rest.map Prod.fst = dropped [a, b] (sigsOf v) from sigsOf_droppedW [a, b] v]
  have nn : bin false a b ∉ sigsOf v := fun hm => fresh (heS ▸ List.mem_toFinset.mpr hm)
  have nz : bin false a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (sigsOf (g :: (h ++ rest))).Nodup := by
    change (bin false a b :: sigsOf (h ++ rest)).Nodup; rw [hSigsHR]
    exact List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm), hn⟩
  have e : (sigsOf (g :: (h ++ rest))).toFinset = insert (bin false a b) U := by
    change (bin false a b :: sigsOf (h ++ rest)).toFinset = _; rw [List.toFinset_cons, hSigsHR, eq]
  have htag' : ∀ w ∈ g :: (h ++ rest), w.2 = updAndTag τ a b w.1 := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
    · simp only [g, gTag, updAndTag, ite_true]; cases τ a <;> cases τ b <;> rfl
    · have hwV : w ∈ v := by
        rcases List.mem_append.mp hw' with hh | hr
        · rcases List.mem_append.mp hh with h1 | h2
          · by_cases haU : a ∈ U
            · simp only [haU, ite_true, List.mem_singleton] at h1; exact h1 ▸ ah
            · simp [haU] at h1
          · by_cases hbU : b ∈ U
            · simp only [hbU, ite_true, List.mem_singleton] at h2; exact h2 ▸ bh
            · simp [hbU] at h2
        · exact List.mem_of_mem_filter hr
      have hwNe : w.1 ≠ bin false a b := fun heq => nn (heq ▸ List.mem_map_of_mem hwV)
      simp [updAndTag, hwNe, htag w hwV]
  have hr := ih _ ⟨hnd, e, htag'⟩
  obtain ⟨ht, hc⟩ := live_size l.live
  rw [← e, List.toFinset_card_of_nodup hnd] at hc
  simp only [sigsOf, List.map_cons, List.map_append, List.length_cons, List.length_append,
    List.length_map] at hc
  have hav : gateAvail (bin false a b) v = true :=
    gateAvail_eq_true nn (live_proper l.live _ (Finset.mem_insert_self _ _))
  have hnsa : isNotSpec0 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec0]; exact hra.1 hta
  have hnsb : isNotSpec0 (τ b) = true := by cases htb : τ b <;> simp [isNotSpec0]; exact hrb.1 htb
  have hka : a ∈ U → isNoneTag (τ a) = true := fun hm => by
    cases hta : τ a <;> simp [isNoneTag]; all_goals exact hra.2 (by simp [hta]) hm
  have hkb : b ∈ U → isNoneTag (τ b) = true := fun hm => by
    cases htb : τ b <;> simp [isNoneTag]; all_goals exact hrb.2 (by simp [htb]) hm
  have hdrop : dropTwo a b v = rest := dropTwo_eq a b v
  have cv := live_cover l.live e
  simp only [sigsOf, List.map_cons, List.map_append, unionSep, union_append] at cv
  have hcv' : (sep (decide (0 < t)) (bin false a b) ||| unionSep (decide (0 < t)) (sigsOf rest)) |||
      unionSepW (decide (0 < t)) h = top := by
    rw [unionSepW_eq, ← cv]; unfold sigsOf; ac_rfl
  obtain ⟨hlen, hmask⟩ := two_rest (decide (0 < t)) hndS hval ahS bhS hab
  rw [sigsOf_length, ← sigsOf_droppedW, sigsOf_length] at hlen
  change v.length - 2 = rest.length at hlen
  rw [← sigsOf_droppedW] at hmask
  change takeTwo (coverage (decide (0 < t)) (sigsOf v)) (sep (decide (0 < t)) a) (sep (decide (0 < t)) b) =
    unionSep (decide (0 < t)) (sigsOf rest) at hmask
  have hdisjAB := two_rest_disj (decide (0 < t)) hndS hval ahS bhS hab
  have hdisjBA := two_rest_disj (decide (0 < t)) hndS hval bhS ahS hab.symm
  have hvc := validCov_coverage (decide (0 < t)) hval
  constructor
  · intro ht0; subst ht0
    have hdt0 : decide (0 < 0) = false := rfl
    rw [hdt0] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv0 : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)))
        (unionSepW false h) = top := by simpa [hmask, sep0_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA0 : a ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 a)) b.1 =
        Nat.land (coverage false (sigsOf v)).2.1 (sep0 a) := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_and_0 hvc (by simpa [sep0_eq] using hdisjAB) (by simpa [h, hna, hbU, unionSepW, sep0_eq] using hcv0)
      · exact unique_and_0 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv0)
    have huB0 : b ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 b)) a.1 =
        Nat.land (coverage false (sigsOf v)).2.1 (sep0 b) := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep0 (bin false b a)) (takeTwo (coverage false (sigsOf v)) (sep0 b) (sep0 a)))
          (unionSepW false h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv0
      by_cases haU : a ∈ U
      · exact unique_and_0 hvc (by simpa [sep0_eq] using hdisjBA) (by simpa [h, haU, hnb, unionSepW, sep0_eq] using hcomm)
      · exact unique_and_0 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv0
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      rw [coverageW_eq]
      exact fastPair0_and hnsa hnsb (huA0 hna) (huB0 hnb) htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair0_and hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_A (hka haU) (Nat.beq_eq.mpr (huB0 hbU)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_B (hkb hbU) (Nat.beq_eq.mpr (huA0 haU)) htopB hav hrB
      · have htop : Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_0 (Nat.beq_eq.mpr (huA0 haU)) (Nat.beq_eq.mpr (huB0 hbU)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a)) (sep0 b) = top := by
          have : unionSepW false h = sep0 a ||| sep0 b := by simp [h, haU, hbU, unionSepW, sep0_eq]
          rw [this] at hcv0; exact (Nat.or_assoc _ _ _).trans hcv0
        have hrAB : r (g :: (a, τ a) :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_l (hka haU)) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_0 htop hav hr0)
  · intro ht0
    have hdt : decide (0 < t) = true := decide_eq_true (by omega)
    rw [hdt] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv1 : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)))
        (unionSepW true h) = top := by simpa [hmask, sep1_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA1 : a ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.1) b.1 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.1 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.2) b.2 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.2 := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_and_1 hvc (by simpa [sep1_eq] using hdisjAB) (by simpa [h, hna, hbU, unionSepW, sep1_eq] using hcv1)
      · exact unique_and_1 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv1)
    have huB1 : b ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.1) a.1 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.1 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.2) a.2 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.2 := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep1 (bin false b a)) (takeTwo (coverage true (sigsOf v)) (sep1 b) (sep1 a)))
          (unionSepW true h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv1
      by_cases haU : a ∈ U
      · exact unique_and_1 hvc (by simpa [sep1_eq] using hdisjBA) (by simpa [h, haU, hnb, unionSepW, sep1_eq] using hcomm)
      · exact unique_and_1 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv1
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      have ⟨u1, u2⟩ := huA1 hna; have ⟨v1, v2⟩ := huB1 hnb
      rw [coverageW_eq]
      exact fastPair1_and hnsa hnsb u1 v1 u2 v2 htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair1_and hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_A (hka haU) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact tryKeeps1_B (hkb hbU) (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) htopB hav hrB
      · have htop : Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_0 (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a)) (sep1 b) = top := by
          have : unionSepW true h = sep1 a ||| sep1 b := by simp [h, haU, hbU, unionSepW, sep1_eq]
          rw [this] at hcv1; exact (Nat.or_assoc _ _ _).trans hcv1
        have hrAB : r (g :: (a, τ a) :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair1_and hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_and hnsa hnsb (bor_l (hka haU)) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact slow2Pair1_and hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_and hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_0 htop hav hr0)
lemma pair_or_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin true a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec1 ∧ (τ a = .tSpec0 → a ∉ U))
    (hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U))
    (l : TRestricted m t (insert (bin true a b) U) (updOrTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin true a b) U) (updOrTag τ a b) → r w = true) :
    let lim := k - t + 1
    let c0 := coverageW false v
    let c1 := coverageW true v
    (t = 0 →
      (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      slow2Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
    (t ≠ 0 →
      (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      slow2Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) := by
  obtain ⟨hndS, heS, htag⟩ := hrep
  have hval : ∀ x ∈ sigsOf v, Valid x := by
    intro x hx
    rcases Finset.mem_insert.mp (heS ▸ List.mem_toFinset.mpr hx) with rfl | hx1
    · exact ha.1
    rcases Finset.mem_insert.mp hx1 with rfl | hxU
    · exact hb.1
    · exact (live_proper l.live x (Finset.mem_insert_of_mem hxU)).1
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  let rest := droppedW [a, b] v
  let g : Wire := (bin true a b, .tNone)
  let wa : Wire := (a, if isDeg3Tag (τ a) then .tSpec0 else .tNone)
  let wb : Wire := (b, if isDeg3Tag (τ b) then .tSpec0 else .tNone)
  let h : List Wire := (if a ∈ U then [wa] else []) ++ (if b ∈ U then [wb] else [])
  have hSigsH : sigsOf h = keepOf U [a, b] := by
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [h, wa, wb, sigsOf, keepOf, haU, hbU]
  obtain ⟨hn, eq⟩ := edit_list (del := [a, b]) (U := U) hndS (by simp [hab]) (by simpa using heS)
  have hSigsHR : sigsOf (h ++ rest) = keepOf U [a, b] ++ dropped [a, b] (sigsOf v) := by
    change (h ++ rest).map Prod.fst = _
    rw [List.map_append, show h.map Prod.fst = keepOf U [a, b] from hSigsH,
      show rest.map Prod.fst = dropped [a, b] (sigsOf v) from sigsOf_droppedW [a, b] v]
  have nn : bin true a b ∉ sigsOf v := fun hm => fresh (heS ▸ List.mem_toFinset.mpr hm)
  have nz : bin true a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (sigsOf (g :: (h ++ rest))).Nodup := by
    change (bin true a b :: sigsOf (h ++ rest)).Nodup; rw [hSigsHR]
    exact List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm), hn⟩
  have e : (sigsOf (g :: (h ++ rest))).toFinset = insert (bin true a b) U := by
    change (bin true a b :: sigsOf (h ++ rest)).toFinset = _; rw [List.toFinset_cons, hSigsHR, eq]
  have htag' : ∀ w ∈ g :: (h ++ rest), w.2 = updOrTag τ a b w.1 := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
    · simp [g, updOrTag]
    · rcases List.mem_append.mp hw' with hh | hr
      · rcases List.mem_append.mp hh with h1 | h2
        · by_cases haU : a ∈ U
          · simp only [haU, ite_true, List.mem_singleton] at h1; subst w
            have hneG : a ≠ bin true a b := fun eq' => fresh (eq' ▸ Finset.mem_insert_self _ _)
            have hna0 : τ a ≠ .tSpec0 := fun h0 => hra.2 h0 haU
            simp only [wa, updOrTag, hneG, ite_false]
            cases hta : τ a <;> simp_all [isDeg3Tag]
          · simp [haU] at h1
        · by_cases hbU : b ∈ U
          · simp only [hbU, ite_true, List.mem_singleton] at h2; subst w
            have hneG : b ≠ bin true a b := fun eq' =>
              fresh (eq' ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
            have hnb0 : τ b ≠ .tSpec0 := fun h0 => hrb.2 h0 hbU
            simp only [wb, updOrTag, hneG, hab.symm, false_and, ite_false]
            cases htb : τ b <;> simp_all [isDeg3Tag]
          · simp [hbU] at h2
      · have hwV := List.mem_of_mem_filter hr
        have hnot : w.1 ≠ a ∧ w.1 ≠ b := by
          have hf := (List.mem_filter.mp hr).2
          simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
            List.mem_cons, List.not_mem_nil, or_false, not_or] at hf
          exact hf
        have hneG : w.1 ≠ bin true a b := fun eq' => nn (eq' ▸ List.mem_map_of_mem hwV)
        simp [updOrTag, hneG, hnot.1, hnot.2, htag w hwV]
  have hr := ih _ ⟨hnd, e, htag'⟩
  obtain ⟨ht, hc⟩ := live_size l.live
  rw [← e, List.toFinset_card_of_nodup hnd] at hc
  simp only [sigsOf, List.map_cons, List.map_append, List.length_cons, List.length_append,
    List.length_map] at hc
  have hav : gateAvail (bin true a b) v = true :=
    gateAvail_eq_true nn (live_proper l.live _ (Finset.mem_insert_self _ _))
  have hnsa : isNotSpec1 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec1]; exact hra.1 hta
  have hnsb : isNotSpec1 (τ b) = true := by cases htb : τ b <;> simp [isNotSpec1]; exact hrb.1 htb
  have hka : a ∈ U → isNotSpec0 (τ a) = true := fun hm => by
    cases hta : τ a <;> simp [isNotSpec0]; exact hra.2 hta hm
  have hkb : b ∈ U → isNotSpec0 (τ b) = true := fun hm => by
    cases htb : τ b <;> simp [isNotSpec0]; exact hrb.2 htb hm
  have hdrop : dropTwo a b v = rest := dropTwo_eq a b v
  have cv := live_cover l.live e
  simp only [sigsOf, List.map_cons, List.map_append, unionSep, union_append] at cv
  have hcv' : (sep (decide (0 < t)) (bin true a b) ||| unionSep (decide (0 < t)) (sigsOf rest)) |||
      unionSepW (decide (0 < t)) h = top := by
    rw [unionSepW_eq, ← cv]; unfold sigsOf; ac_rfl
  obtain ⟨hlen, hmask⟩ := two_rest (decide (0 < t)) hndS hval ahS bhS hab
  rw [sigsOf_length, ← sigsOf_droppedW, sigsOf_length] at hlen
  change v.length - 2 = rest.length at hlen
  rw [← sigsOf_droppedW] at hmask
  change takeTwo (coverage (decide (0 < t)) (sigsOf v)) (sep (decide (0 < t)) a) (sep (decide (0 < t)) b) =
    unionSep (decide (0 < t)) (sigsOf rest) at hmask
  have hdisjAB := two_rest_disj (decide (0 < t)) hndS hval ahS bhS hab
  have hdisjBA := two_rest_disj (decide (0 < t)) hndS hval bhS ahS hab.symm
  have hvc := validCov_coverage (decide (0 < t)) hval
  constructor
  · intro ht0; subst ht0
    have hdt0 : decide (0 < 0) = false := rfl
    rw [hdt0] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv0 : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)))
        (unionSepW false h) = top := by simpa [hmask, sep0_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA0 : a ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 a)) b.2 = 0 := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_or_0 hvc (by simpa [sep0_eq] using hdisjAB) (by simpa [h, wa, wb, hna, hbU, unionSepW, sep0_eq] using hcv0)
      · exact unique_or_0 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv0)
    have huB0 : b ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 b)) a.2 = 0 := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep0 (bin true b a)) (takeTwo (coverage false (sigsOf v)) (sep0 b) (sep0 a)))
          (unionSepW false h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv0
      by_cases haU : a ∈ U
      · exact unique_or_0 hvc (by simpa [sep0_eq] using hdisjBA) (by simpa [h, wa, wb, haU, hnb, unionSepW, sep0_eq] using hcomm)
      · exact unique_or_0 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv0
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      rw [coverageW_eq]
      exact fastPair0_or hnsa hnsb (huA0 hna) (huB0 hnb) htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair0_or hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_A (hka haU) (Nat.beq_eq.mpr (huB0 hbU)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_B (hkb hbU) (Nat.beq_eq.mpr (huA0 haU)) htopB hav hrB
      · have htop : Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_0 (Nat.beq_eq.mpr (huA0 haU)) (Nat.beq_eq.mpr (huB0 hbU)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a)) (sep0 b) = top := by
          have : unionSepW false h = sep0 a ||| sep0 b := by simp [h, wa, wb, haU, hbU, unionSepW, sep0_eq]
          rw [this] at hcv0; exact (Nat.or_assoc _ _ _).trans hcv0
        have hrAB : r (g :: wa :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_l (hka haU)) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_0 htop hav hr0)
  · intro ht0
    have hdt : decide (0 < t) = true := decide_eq_true (by omega)
    rw [hdt] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv1 : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)))
        (unionSepW true h) = top := by simpa [hmask, sep1_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA1 : a ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.1) b.2 = 0 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.2) b.1 = 0 := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_or_1 hvc (by simpa [sep1_eq] using hdisjAB) (by simpa [h, wa, wb, hna, hbU, unionSepW, sep1_eq] using hcv1)
      · exact unique_or_1 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv1)
    have huB1 : b ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.1) a.2 = 0 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.2) a.1 = 0 := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep1 (bin true b a)) (takeTwo (coverage true (sigsOf v)) (sep1 b) (sep1 a)))
          (unionSepW true h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv1
      by_cases haU : a ∈ U
      · exact unique_or_1 hvc (by simpa [sep1_eq] using hdisjBA) (by simpa [h, wa, wb, haU, hnb, unionSepW, sep1_eq] using hcomm)
      · exact unique_or_1 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv1
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      have ⟨u1, u2⟩ := huA1 hna; have ⟨v1, v2⟩ := huB1 hnb
      rw [coverageW_eq]
      exact fastPair1_or hnsa hnsb u1 v1 u2 v2 htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair1_or hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_A (hka haU) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact tryKeeps1_B (hkb hbU) (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) htopB hav hrB
      · have htop : Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_0 (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a)) (sep1 b) = top := by
          have : unionSepW true h = sep1 a ||| sep1 b := by simp [h, wa, wb, haU, hbU, unionSepW, sep1_eq]
          rw [this] at hcv1; exact (Nat.or_assoc _ _ _).trans hcv1
        have hrAB : r (g :: wa :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair1_or hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_or hnsa hnsb (bor_l (hka haU)) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact slow2Pair1_or hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_or hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_0 htop hav hr0)
lemma trestricted_congr {k t S τ₁ τ₂} (h : TRestricted k t S τ₁)
    (he : ∀ x ∈ S, τ₁ x = τ₂ x) : TRestricted k t S τ₂ := by
  induction h generalizing τ₂ with
  | stop => exact TRestricted.stop
  | @unary k t U a τ₁ ha hf hr1 hr2 tail ih =>
    have hae := he a (Finset.mem_insert_self _ _)
    refine TRestricted.unary ha hf (hae ▸ hr1) (hae ▸ hr2) (ih ?_)
    intro x hx; unfold updUnaryTag
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp [hae]
    · have hne : x ≠ neg a := fun e => hf (e ▸ Finset.mem_insert_of_mem hxU)
      simp [hne, he x (Finset.mem_insert_of_mem hxU)]
  | @binaryAnd k t U a b τ₁ ha hb hab hf hra hrb tail ih =>
    have hae := he a (Finset.mem_insert_self _ _)
    have hbe := he b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    refine TRestricted.binaryAnd ha hb hab hf (hae ▸ hra) (hbe ▸ hrb) (ih ?_)
    intro x hx; unfold updAndTag
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp [hae, hbe]
    · have hne : x ≠ bin false a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
      simp [hne, he x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))]
  | @binaryOr k t U a b τ₁ ha hb hab hf hra hrb tail ih =>
    have hae := he a (Finset.mem_insert_self _ _)
    have hbe := he b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    refine TRestricted.binaryOr ha hb hab hf (hae ▸ hra) (hbe ▸ hrb) (ih ?_)
    intro x hx; unfold updOrTag
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp
    · have hne : x ≠ bin true a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
      simp [hne, hae, hbe, he x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))]
lemma binary_dispatch {k t : Nat} {a b : Wire} {v : List Wire} {r : List Wire → Bool}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (h1 : let lim := k - t + 1; let c0 := coverageW false v; let c1 := coverageW true v
      (t = 0 →
        (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 a) (mkAct0 c0.2.1 b) = true) ∧
        (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 a) (mkAct0 c0.2.1 b) = true) ∧
        slow2Pair0 r v c0 (mkAct0 c0.2.1 a) (mkAct0 c0.2.1 b) = true) ∧
      (t ≠ 0 →
        (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 a) (mkAct1 c1.2.1 b) = true) ∧
        (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 a) (mkAct1 c1.2.1 b) = true) ∧
        slow2Pair1 r v c1 (mkAct1 c1.2.1 a) (mkAct1 c1.2.1 b) = true))
    (h2 : let lim := k - t + 1; let c0 := coverageW false v; let c1 := coverageW true v
      (t = 0 →
        (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 b) (mkAct0 c0.2.1 a) = true) ∧
        (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 b) (mkAct0 c0.2.1 a) = true) ∧
        slow2Pair0 r v c0 (mkAct0 c0.2.1 b) (mkAct0 c0.2.1 a) = true) ∧
      (t ≠ 0 →
        (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 b) (mkAct1 c1.2.1 a) = true) ∧
        (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 b) (mkAct1 c1.2.1 a) = true) ∧
        slow2Pair1 r v c1 (mkAct1 c1.2.1 b) (mkAct1 c1.2.1 a) = true)) :
    binaryMoves k t v.length r v = true := by
  unfold binaryMoves; dsimp only
  by_cases ht0 : t = 0
  · subst ht0
    simp only [Nat.beq_refl, ite_true, buildSeps0_eq, buildActs0_map]
    have hne0 : mkAct0 (coverageW false v).2.1 a ≠ mkAct0 (coverageW false v).2.1 b :=
      fun e => hne (congrArg WAct0.w e)
    have ⟨hf1, hs11, hs21⟩ := h1.1 rfl
    have ⟨hf2, hs12, hs22⟩ := h2.1 rfl
    by_cases hl1 : v.length = k - 0 + 1 + 1
    · simp only [hl1, Nat.beq_refl, ite_true, scanFast0_eq]
      exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne0 (hf1 hl1) (hf2 hl1)
    · have hb1 : Nat.beq v.length (k - 0 + 1 + 1) = false := nat_beq_false hl1
      simp only [hb1, Bool.false_eq_true, ite_false]
      by_cases hl2 : v.length = k - 0 + 1
      · simp only [hl2, Nat.beq_refl, ite_true, scanSlow10_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne0 (hs11 hl2) (hs12 hl2)
      · have hb2 : Nat.beq v.length (k - 0 + 1) = false := nat_beq_false hl2
        simp only [hb2, Bool.false_eq_true, ite_false, scanSlow20_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne0 hs21 hs22
  · have hbf : Nat.beq t 0 = false := nat_beq_false ht0
    simp only [hbf, Bool.false_eq_true, ite_false, buildSeps1_eq, buildActs1_map]
    have hne1 : mkAct1 (coverageW true v).2.1 a ≠ mkAct1 (coverageW true v).2.1 b :=
      fun e => hne (congrArg WAct1.w e)
    have ⟨hf1, hs11, hs21⟩ := h1.2 ht0
    have ⟨hf2, hs12, hs22⟩ := h2.2 ht0
    by_cases hl1 : v.length = k - t + 1 + 1
    · simp only [hl1, Nat.beq_refl, ite_true, scanFast1_eq]
      exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne1 (hf1 hl1) (hf2 hl1)
    · have hb1 : Nat.beq v.length (k - t + 1 + 1) = false := nat_beq_false hl1
      simp only [hb1, Bool.false_eq_true, ite_false]
      by_cases hl2 : v.length = k - t + 1
      · simp only [hl2, Nat.beq_refl, ite_true, scanSlow11_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne1 (hs11 hl2) (hs12 hl2)
      · have hb2 : Nat.beq v.length (k - t + 1) = false := nat_beq_false hl2
        simp only [hb2, Bool.false_eq_true, ite_false, scanSlow21_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne1 hs21 hs22
lemma binary_found_and {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin false a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec0 ∧ (τ a ≠ .tNone → a ∉ U))
    (hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U))
    (l : TRestricted m t (insert (bin false a b) U) (updAndTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin false a b) U) (updAndTag τ a b) → r w = true) :
    binaryMoves k t v.length r v = true := by
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr ahS
  have bh : (b, τ b) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr bhS
  have h1 := pair_and_found ha hb hab hrep hle fresh hra hrb l ih
  have hrep' : Represents v (insert b (insert a U)) τ :=
    ⟨hrep.1, by rw [Finset.insert_comm b a]; exact hrep.2.1, hrep.2.2⟩
  have hf' : bin false b a ∉ insert b (insert a U) := by rwa [bin_comm false b a, Finset.insert_comm b a]
  have htagEq : ∀ x, updAndTag τ b a x = updAndTag τ a b x := by
    intro x; unfold updAndTag; rw [bin_comm false b a]; simp only [or_comm]
  have l' : TRestricted m t (insert (bin false b a) U) (updAndTag τ b a) := by
    rw [bin_comm false b a]; exact trestricted_congr l (fun x _ => (htagEq x).symm)
  have ih' : ∀ w : List Wire, Represents w (insert (bin false b a) U) (updAndTag τ b a) → r w = true := by
    intro w hw; apply ih w; rw [bin_comm false b a] at hw
    exact ⟨hw.1, hw.2.1, fun x hx => (hw.2.2 x hx).trans (htagEq x.1)⟩
  have h2 := pair_and_found hb ha hab.symm hrep' hle hf' hrb hra l' ih'
  exact binary_dispatch ah bh (fun e => hab (congrArg Prod.fst e)) h1 h2
lemma binary_found_or {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin true a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec1 ∧ (τ a = .tSpec0 → a ∉ U))
    (hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U))
    (l : TRestricted m t (insert (bin true a b) U) (updOrTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin true a b) U) (updOrTag τ a b) → r w = true) :
    binaryMoves k t v.length r v = true := by
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr ahS
  have bh : (b, τ b) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr bhS
  have h1 := pair_or_found ha hb hab hrep hle fresh hra hrb l ih
  have hrep' : Represents v (insert b (insert a U)) τ :=
    ⟨hrep.1, by rw [Finset.insert_comm b a]; exact hrep.2.1, hrep.2.2⟩
  have hf' : bin true b a ∉ insert b (insert a U) := by rwa [bin_comm true b a, Finset.insert_comm b a]
  have htagEq : ∀ x, updOrTag τ b a x = updOrTag τ a b x := by
    intro x; unfold updOrTag; rw [bin_comm true b a]
    by_cases hg : x = bin true a b
    · simp [hg]
    · by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all
  have l' : TRestricted m t (insert (bin true b a) U) (updOrTag τ b a) := by
    rw [bin_comm true b a]; exact trestricted_congr l (fun x _ => (htagEq x).symm)
  have ih' : ∀ w : List Wire, Represents w (insert (bin true b a) U) (updOrTag τ b a) → r w = true := by
    intro w hw; apply ih w; rw [bin_comm true b a] at hw
    exact ⟨hw.1, hw.2.1, fun x hx => (hw.2.2 x hx).trans (htagEq x.1)⟩
  have h2 := pair_or_found hb ha hab.symm hrep' hle hf' hrb hra l' ih'
  exact binary_dispatch ah bh (fun e => hab (congrArg Prod.fst e)) h1 h2
lemma reduced_step {m t S : Nat} {s : Finset Sig} {τ : Sig → Tag} {v : List Wire}
    {u b : List Wire → Bool}
    (h : TRestricted m t s τ) (hb : m ≤ S + 1) (hrep : Represents v s τ)
    (hu : ∀ w, ∀ s' τ', Represents w s' τ' → ∀ l ≤ S, TRestricted l (t - 1) s' τ' → u w = true)
    (hb' : ∀ w, ∀ s' τ', Represents w s' τ' → ∀ l ≤ S, TRestricted l t s' τ' → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h.live
  rw [← hrep.2.1, List.toFinset_card_of_nodup hrep.1, sigsOf_length] at size
  have h1 : Nat.blt (S + 1) t = false := Bool.eq_false_iff.mpr fun e => by rw [Nat.blt_eq] at e; omega
  have h2 : Nat.blt (S + 1 - t + 1) v.length = false := Bool.eq_false_iff.mpr fun e => by rw [Nat.blt_eq] at e; omega
  simp only [stepTest, h1, h2, Bool.or_self, Bool.false_eq_true, ite_false]
  cases h with
  | stop =>
    have p : (sigsOf v).Perm [target] :=
      List.perm_of_nodup_nodup_toFinset_eq hrep.1 (by simp) (by simp [hrep.2.1])
    have eq := List.perm_singleton.mp p
    cases v with
    | nil => simp [sigsOf] at eq
    | cons w rest =>
      simp only [sigsOf, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at eq
      obtain ⟨hw, rfl⟩ := eq
      simp [hw, sigEq_iff]
  | @unary m t U a τ ha hf hr1 hr2 tail =>
    apply Bool.or_eq_true_iff.mpr; left
    apply Bool.or_eq_true_iff.mpr; right
    apply Bool.and_eq_true_iff.mpr
    exact ⟨by simp [Nat.blt_eq], unary_found ha hrep (by omega) hf hr1 hr2 tail (fun w hw => hu w _ _ hw m (by omega) tail)⟩
  | @binaryAnd m t U a b τ ha hb'p hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr; right
    exact binary_found_and ha hb'p hab hrep (by omega) hf hra hrb tail (fun w hw => hb' w _ _ hw m (by omega) tail)
  | @binaryOr m t U a b τ ha hb'p hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr; right
    exact binary_found_or ha hb'p hab hrep (by omega) hf hra hrb tail (fun w hw => hb' w _ _ hw m (by omega) tail)
lemma search_complete {m t : Nat} {S : Finset Sig} {τ : Sig → Tag} (h : TRestricted m t S τ)
    (k : Nat) (hk : m ≤ k) (v : List Wire) (hrep : Represents v S τ) : search k t v = true := by
  induction k generalizing m t S τ v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    cases h
    have p : (sigsOf v).Perm [target] :=
      List.perm_of_nodup_nodup_toFinset_eq hrep.1 (by simp) (by simp [hrep.2.1])
    have eq := List.perm_singleton.mp p
    cases v with
    | nil => simp [sigsOf] at eq
    | cons w rest =>
      simp only [sigsOf, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at eq
      obtain ⟨hw, rfl⟩ := eq
      simp [search, hw, sigEq_iff]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hrep <;>
      exact fun w s' τ' hw l hl hh => ih hh hl w hw
def Impossible (k t : Nat) (v : List Wire) : Prop :=
  ∀ m ≤ k, ∀ S τ, Represents v S τ → ¬ TRestricted m t S τ
lemma exclude_search {k t : Nat} {v : List Wire} (hc : search k t v = false) :
    Impossible k t v := by
  intro m hm S τ hrep h
  exact Bool.false_ne_true (hc.symm.trans (search_complete h k hm v hrep))
lemma exclude_step {k t : Nat} {v : List Wire} {u b : List Wire → Bool}
    (hu : ∀ w, u w = false → Impossible k (t - 1) w)
    (hb : ∀ w, b w = false → Impossible k t w)
    (hc : stepTest k t v u b = false) : Impossible (k + 1) t v := by
  intro m hm S τ hrep h
  have hu' : ∀ w s' τ', Represents w s' τ' → ∀ j ≤ k, TRestricted j (t - 1) s' τ' → u w = true := by
    intro w s' τ' hw j hj r
    cases e : u w
    · exact (hu _ e j hj s' τ' hw r).elim
    · rfl
  have hb' : ∀ w s' τ', Represents w s' τ' → ∀ j ≤ k, TRestricted j t s' τ' → b w = true := by
    intro w s' τ' hw j hj r
    cases e : b w
    · exact (hb _ e j hj s' τ' hw r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hrep hu' hb'))
lemma trestricted_action {k t S τ} (h : TRestricted k t S τ) (g : Fin 12) :
    TRestricted k t (S.image (action g)) (fun x => τ (action (invG g) x)) := by
  induction h with
  | stop => simpa [action_target] using TRestricted.stop
  | @unary k t U a τ ha hf hr1 hr2 tail ih =>
    simp only [Finset.image_insert, action_neg g ha.1] at ih ⊢
    have hinvA : action (invG g) (action g a) = a := action_inv g ha.1
    have hvalU : ∀ y ∈ U, Valid y := fun y hy => (live_proper tail.live y (Finset.mem_insert_of_mem hy)).1
    have hne : neg (action g a) ∉ insert (action g a) (U.image (action g)) := by
      rw [← action_neg g ha.1, ← Finset.image_insert]
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      have hvy : Valid y := by
        rcases Finset.mem_insert.mp hy with rfl | hyU
        · exact ha.1
        · exact hvalU y hyU
      exact hf ((action_inj hvy (valid_neg ha.1) he) ▸ hy)
    have hnaU : a ∉ U → action g a ∉ U.image (action g) := by
      intro hna hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hna ((action_inj (hvalU y hy) ha.1 he) ▸ hy)
    refine TRestricted.unary (action_proper g ha) hne (by simpa [hinvA] using hr1)
      (fun h => hnaU (hr2 (by simpa [hinvA] using h))) ?_
    refine trestricted_congr ih ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · unfold updUnaryTag
      simp only [ite_true]
      rw [← action_neg g ha.1, action_inv g (valid_neg ha.1)]
      simp only [ite_true, hinvA]
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxU
      have hneY : y ≠ neg a := fun e => hf (e ▸ Finset.mem_insert_of_mem hy)
      have hneGY : action g y ≠ neg (action g a) := by
        rw [← action_neg g ha.1]; intro e; exact hneY (action_inj (hvalU y hy) (valid_neg ha.1) e)
      unfold updUnaryTag
      simp only [hneGY, ite_false, action_inv g (hvalU y hy), hneY]
  | @binaryAnd k t U a b τ ha hb hab hf hra hrb tail ih =>
    simp only [Finset.image_insert, action_bin g false a b] at ih ⊢
    have hinvA := action_inv g ha.1
    have hinvB := action_inv g hb.1
    have hvalU : ∀ y ∈ U, Valid y := fun y hy => (live_proper tail.live y (Finset.mem_insert_of_mem hy)).1
    have hne : bin false (action g a) (action g b) ∉
        insert (action g a) (insert (action g b) (U.image (action g))) := by
      rw [← action_bin g false a b, ← Finset.image_insert, ← Finset.image_insert]
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      have hvy : Valid y := by
        rcases Finset.mem_insert.mp hy with rfl | hy1
        · exact ha.1
        rcases Finset.mem_insert.mp hy1 with rfl | hyU
        · exact hb.1
        · exact hvalU y hyU
      exact hf ((action_inj hvy (valid_bin ha.1 hb.1) he) ▸ hy)
    have hnotU (z : Sig) (hvz : Valid z) (hnz : z ∉ U) : action g z ∉ U.image (action g) := by
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hnz ((action_inj (hvalU y hy) hvz he) ▸ hy)
    refine TRestricted.binaryAnd (action_proper g ha) (action_proper g hb)
      (fun e => hab (action_inj ha.1 hb.1 e)) hne
      ⟨by simpa [hinvA] using hra.1, fun h => hnotU a ha.1 (hra.2 (by simpa [hinvA] using h))⟩
      ⟨by simpa [hinvB] using hrb.1, fun h => hnotU b hb.1 (hrb.2 (by simpa [hinvB] using h))⟩ ?_
    refine trestricted_congr ih ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · unfold updAndTag
      simp only [ite_true]
      rw [← action_bin g false a b, action_inv g (valid_bin ha.1 hb.1)]
      simp only [ite_true, hinvA, hinvB]
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxU
      have hneY : y ≠ bin false a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
      have hneGY : action g y ≠ bin false (action g a) (action g b) := by
        rw [← action_bin g false a b]; intro e; exact hneY (action_inj (hvalU y hy) (valid_bin ha.1 hb.1) e)
      unfold updAndTag
      simp only [hneGY, ite_false, action_inv g (hvalU y hy), hneY]
  | @binaryOr k t U a b τ ha hb hab hf hra hrb tail ih =>
    simp only [Finset.image_insert, action_bin g true a b] at ih ⊢
    have hinvA := action_inv g ha.1
    have hinvB := action_inv g hb.1
    have hvalU : ∀ y ∈ U, Valid y := fun y hy => (live_proper tail.live y (Finset.mem_insert_of_mem hy)).1
    have hne : bin true (action g a) (action g b) ∉
        insert (action g a) (insert (action g b) (U.image (action g))) := by
      rw [← action_bin g true a b, ← Finset.image_insert, ← Finset.image_insert]
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      have hvy : Valid y := by
        rcases Finset.mem_insert.mp hy with rfl | hy1
        · exact ha.1
        rcases Finset.mem_insert.mp hy1 with rfl | hyU
        · exact hb.1
        · exact hvalU y hyU
      exact hf ((action_inj hvy (valid_bin ha.1 hb.1) he) ▸ hy)
    have hnotU (z : Sig) (hvz : Valid z) (hnz : z ∉ U) : action g z ∉ U.image (action g) := by
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hnz ((action_inj (hvalU y hy) hvz he) ▸ hy)
    refine TRestricted.binaryOr (action_proper g ha) (action_proper g hb)
      (fun e => hab (action_inj ha.1 hb.1 e)) hne
      ⟨by simpa [hinvA] using hra.1, fun h => hnotU a ha.1 (hra.2 (by simpa [hinvA] using h))⟩
      ⟨by simpa [hinvB] using hrb.1, fun h => hnotU b hb.1 (hrb.2 (by simpa [hinvB] using h))⟩ ?_
    refine trestricted_congr ih ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · unfold updOrTag
      simp only [ite_true]
      rw [← action_bin g true a b, action_inv g (valid_bin ha.1 hb.1)]
      simp only [ite_true]
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxU
      have hvy := hvalU y hy
      have hneY : y ≠ bin true a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
      have hneGY : action g y ≠ bin true (action g a) (action g b) := by
        rw [← action_bin g true a b]; intro e; exact hneY (action_inj hvy (valid_bin ha.1 hb.1) e)
      have eqA : (action g y = action g a) ↔ (y = a) := ⟨action_inj hvy ha.1, congrArg (action g)⟩
      have eqB : (action g y = action g b) ↔ (y = b) := ⟨action_inj hvy hb.1, congrArg (action g)⟩
      unfold updOrTag
      simp only [hneGY, ite_false, action_inv g hvy, hneY, eqA, eqB, hinvA, hinvB]
lemma perm_impossible {k t : Nat} {w z : List Wire} (hp : w.Perm z)
    (hz : Impossible k t z) : Impossible k t w := by
  intro m hm S τ hrep h
  apply hz m hm S τ _ h
  have hpS : (sigsOf w).Perm (sigsOf z) := hp.map Prod.fst
  refine ⟨hpS.nodup_iff.mp hrep.1, ?_, fun x hx => hrep.2.2 x (hp.mem_iff.mpr hx)⟩
  rw [← hrep.2.1]; ext a
  simp only [List.mem_toFinset, hpS.mem_iff]
lemma rotate_impossible {k t : Nat} {w z : List Wire} (g : Fin 12)
    (hp : (w.map (fun x => (action g x.1, x.2))).Perm z)
    (hn : Impossible k t z) : Impossible k t w := by
  intro m hm S τ hrep h
  apply hn m hm (S.image (action g)) (fun x => τ (action (invG g) x)) _ (trestricted_action h g)
  have hval : ∀ x ∈ sigsOf w, Valid x := fun x hx =>
    (live_proper h.live x (hrep.2.1 ▸ List.mem_toFinset.mpr hx)).1
  have hmapS : sigsOf (w.map (fun x => (action g x.1, x.2))) = (sigsOf w).map (action g) := by
    simp [sigsOf, List.map_map, Function.comp_def]
  have hpS : ((sigsOf w).map (action g)).Perm (sigsOf z) := by
    rw [← hmapS]; exact hp.map Prod.fst
  have hndMap : ((sigsOf w).map (action g)).Nodup := by
    apply List.Nodup.map_on _ hrep.1
    intro a ha b hb heq
    exact action_inj (hval a ha) (hval b hb) heq
  refine ⟨hpS.nodup_iff.mp hndMap, ?_, ?_⟩
  · ext a
    simp only [List.mem_toFinset, ← hpS.mem_iff, List.mem_map, Finset.mem_image, ← hrep.2.1]
  · intro x hx
    have hx' := hp.mem_iff.mpr hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx'
    have hvy : Valid y.1 := hval y.1 (List.mem_map_of_mem hy)
    simp [action_inv g hvy, hrep.2.2 y hy]
def recipeHint (a : Sig) : Nat :=
  let p := a.1 % 4294967291
  let q := a.2 % 4294967291
  let b := (p * 31 + q) % recipeBuckets
  let h := Nat.land ((p * 1299710 + q * 1786) % 4294967291) recipeMask
  let d := Nat.land (Nat.shiftRight recipeShift (recipeWidth * b)) recipeMask
  Nat.land (Nat.shiftRight recipeData (recipeEntryBits * Nat.land (h + d) recipeMask)) recipeEntryMask
def recipeStep (rho : Fin 9 → Sig) (op : Nat) (w : List Sig) : List Sig :=
  if Nat.ble op 9 then rho (Fin.ofNat 9 (op - 1)) :: w
  else match w with
  | [] => []
  | a :: t =>
    if Nat.beq op 10 then neg a :: t
    else match t with
    | [] => []
    | b :: r => bin (Nat.beq op 12) a b :: r
def recipeRun (rho : Fin 9 → Sig) : Nat → Nat → List Sig → List Sig
  | 0, _, w => w
  | n + 1, code, w =>
    if Nat.beq code 0 then w else
      recipeRun rho n (Nat.shiftRight code 4) (recipeStep rho (Nat.land code 15) w)
lemma recipeStep_valid (rho : Fin 9 → Sig) (hr : ∀ i, Valid (rho i)) (op : Nat)
    (w : List Sig) (hw : ∀ x ∈ w, Valid x) : ∀ x ∈ recipeStep rho op w, Valid x := by
  unfold recipeStep
  cases h : Nat.ble op 9
  · simp only [Bool.false_eq_true, ite_false]
    cases w with
    | nil => intro x hx; simp at hx
    | cons a t =>
      cases hi : Nat.beq op 10
      · simp only [Bool.false_eq_true, ite_false]
        cases t with
        | nil => intro x hx; simp at hx
        | cons b r =>
          simp only [List.mem_cons]
          rintro x (rfl | hx)
          · exact valid_bin (hw a (by simp)) (hw b (by simp))
          · exact hw x (by simp [hx])
      · simp only [ite_true, List.mem_cons]
        rintro x (rfl | hx)
        · exact valid_neg (hw a (by simp))
        · exact hw x (by simp [hx])
  · simp only [ite_true, List.mem_cons]
    rintro x (rfl | hx)
    · exact hr _
    · exact hw x hx
lemma recipeStep_map (g : Fin 12) (rho : Fin 9 → Sig) (op : Nat) (w : List Sig)
    (hw : ∀ x ∈ w, Valid x) :
    (recipeStep rho op w).map (action g) =
      recipeStep (action g ∘ rho) op (w.map (action g)) := by
  unfold recipeStep
  cases h : Nat.ble op 9
  · simp only [Bool.false_eq_true, ite_false]
    cases w with
    | nil => rfl
    | cons a t =>
      cases hi : Nat.beq op 10
      · simp only [Bool.false_eq_true, ite_false, List.map_cons]
        cases t <;> simp [action_bin]
      · simp [action_neg g (hw a (by simp))]
  · simp
lemma recipeRun_map (g : Fin 12) (rho : Fin 9 → Sig) (hr : ∀ i, Valid (rho i))
    (n code : Nat) (w : List Sig) (hw : ∀ x ∈ w, Valid x) :
    (recipeRun rho n code w).map (action g) =
      recipeRun (action g ∘ rho) n code (w.map (action g)) := by
  induction n generalizing code w with
  | zero => rfl
  | succ n ih =>
    unfold recipeRun
    cases h : Nat.beq code 0
    · simp only [Bool.false_eq_true, ite_false]
      rw [ih _ _ (recipeStep_valid rho hr _ w hw), recipeStep_map g rho _ w hw]
    · simp
def recipeValue (rho : Fin 9 → Sig) (code : Nat) : Sig :=
  (recipeRun rho recipeFuel code []).headD zero
lemma recipeValue_action (g : Fin 12) (rho : Fin 9 → Sig) (hr : ∀ i, Valid (rho i)) (code : Nat) :
    recipeValue (action g ∘ rho) code = action g (recipeValue rho code) := by
  have h := recipeRun_map g rho hr recipeFuel code [] (by simp)
  simp only [List.map_nil] at h
  unfold recipeValue
  rw [← h]
  cases recipeRun rho recipeFuel code [] <;> simp [action_zero]
def sourceSignals (i : Fin 9) : Sig := raw.getD i.val zero
lemma sourceSignals_valid (i : Fin 9) : Valid (sourceSignals i) := valid_getD raw_valid i.val
lemma sourceSignals_image (g : Fin 12) : rawImage g = action g ∘ sourceSignals := by
  funext i; exact rawImage_eq g i
def recipeAction (g : Fin 12) (a : Sig) : Sig :=
  let code := recipeHint a
  if Nat.ble code 9 then
    let idx := Fin.ofNat 9 (code - 1)
    if sigEq (sourceSignals idx) a then rawImage g idx else action g a
  else if sigEq (recipeValue sourceSignals code) a then recipeValue (rawImage g) code
  else action g a
lemma recipeAction_eq (g : Fin 12) : recipeAction g = action g := by
  funext a
  simp only [recipeAction]
  split
  · split
    · rename_i _ h
      rw [sourceSignals_image, Function.comp_apply, sigEq_iff.mp h]
    · rfl
  · split
    · rename_i _ h
      rw [sourceSignals_image, recipeValue_action g sourceSignals sourceSignals_valid, sigEq_iff.mp h]
    · rfl
def wireAt (id : Nat) : Sig :=
  (Nat.land (Nat.shiftRight wireTable0 (414 * id)) top,
   Nat.land (Nat.shiftRight wireTable1 (414 * id)) top)
def unpackState (bits : Nat) : Nat → List Wire
  | 0 => []
  | n + 1 =>
    let entry := Nat.land bits wireEntryMask
    (wireAt (Nat.shiftRight entry 2), tagOfNat (Nat.land entry 3)) ::
      unpackState (Nat.shiftRight bits wireEntryBits) n
def frontierState (k t i : Nat) : List Wire :=
  let slot := frontierSlotBits k t
  let rawBits := Nat.shiftRight (frontierData k t) (slot * i)
  let len := Nat.land rawBits 15
  unpackState (Nat.shiftRight rawBits 4) len
def wireHash (salt : Nat) (w : Wire) : Nat :=
  let h := ((w.1.1 % 1048573) * (65537 + salt) + (w.1.2 % 1048573) * 131 + w.2.toNat * 997 + 317) % 1048573
  (h * h % 1048573) * h % 1048573
def frontierHash (salt : Nat) (v : List Wire) : Nat :=
  (v.foldl (fun s w => s + wireHash salt w) 0) % 1048573
def stamp (k t : Nat) (w : List Wire) : Nat :=
  let h := frontierHash (tableSalt k t) w
  let (width, codeWidth) := tableBits k t
  let lane := h % tableBuckets k t
  let mask := Nat.shiftLeft 1 width - 1
  let d := Nat.land (Nat.shiftRight (tableDisplacements k t) (width * lane)) mask
  let slot := Nat.land (h * tableMultiplier k t % 1048573 + d) mask
  Nat.land (Nat.shiftRight (tableData k t) (codeWidth * slot)) (Nat.shiftLeft 1 codeWidth - 1)
def eraseWire (a : Wire) : List Wire → Option (List Wire)
  | [] => none
  | b :: l =>
    if tagEq a.2 b.2 && sigEq a.1 b.1 then some l
    else match eraseWire a l with
      | none => none
      | some l' => some (b :: l')
lemma eraseWire_perm {a : Wire} {ys ys' : List Wire} (h : eraseWire a ys = some ys') :
    ys.Perm (a :: ys') := by
  induction ys generalizing ys' with
  | nil => simp [eraseWire] at h
  | cons b l ih =>
    unfold eraseWire at h
    split at h
    · rename_i heq
      simp only [Bool.and_eq_true, tagEq_iff, sigEq_iff] at heq
      have hab : a = b := Prod.ext heq.2 heq.1
      injection h with h'; subst h'; subst hab; exact List.Perm.refl _
    · cases he : eraseWire a l with
      | none => simp [he] at h
      | some l' =>
        simp only [he] at h; injection h with h'; subst h'
        exact (List.Perm.cons b (ih he)).trans (List.Perm.swap a b l')
def isPermFast : List Wire → List Wire → Bool
  | [], [] => true
  | a :: l, ys =>
    match eraseWire a ys with
    | none => false
    | some ys' => isPermFast l ys'
  | _, _ => false
lemma isPermFast_perm {xs ys : List Wire} (h : isPermFast xs ys = true) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [isPermFast] at h ⊢
  | cons a l ih =>
    unfold isPermFast at h
    cases he : eraseWire a ys with
    | none => simp [he] at h
    | some ys' =>
      simp only [he] at h
      exact (List.Perm.cons a (ih h)).trans (eraseWire_perm he).symm
def isPermTrans (g : Fin 12) : List Wire → List Wire → Bool
  | [], [] => true
  | a :: l, ys =>
    match eraseWire (recipeAction g a.1, a.2) ys with
    | none => false
    | some ys' => isPermTrans g l ys'
  | _, _ => false
lemma isPermTrans_perm {g : Fin 12} {xs ys : List Wire} (h : isPermTrans g xs ys = true) :
    (xs.map fun x => (action g x.1, x.2)).Perm ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [isPermTrans] at h ⊢
  | cons a l ih =>
    unfold isPermTrans at h
    cases he : eraseWire (recipeAction g a.1, a.2) ys with
    | none => simp [he] at h
    | some ys' =>
      simp only [he] at h
      have ha' : action g a.1 = recipeAction g a.1 := congrFun (recipeAction_eq g).symm a.1
      rw [List.map_cons, ha']
      exact (List.Perm.cons _ (ih h)).trans (eraseWire_perm he).symm
def certificateMatch (k t : Nat) (w : List Wire) : Bool :=
  match stamp k t w with
  | 0 => false
  | n + 1 =>
    let i := n / 12
    let gv := n % 12
    Nat.blt i (frontierCount k t) &&
      let tgt := frontierState k t i
      if Nat.beq gv 0 then isPermFast w tgt
      else isPermTrans (Fin.ofNat 12 gv) w tgt
lemma certificateMatch_ok {k t : Nat} (h : ∀ i < frontierCount k t,
    Impossible k t (frontierState k t i)) {w : List Wire}
    (hw : certificateMatch k t w = true) : Impossible k t w := by
  unfold certificateMatch at hw
  cases hs : stamp k t w with
  | zero => simp [hs] at hw
  | succ n =>
    simp only [hs, Bool.and_eq_true, Nat.blt_eq] at hw
    obtain ⟨hi, hp⟩ := hw
    split at hp
    · exact perm_impossible (isPermFast_perm hp) (h _ hi)
    · exact rotate_impossible (Fin.ofNat 12 (n % 12)) (isPermTrans_perm hp) (h _ hi)
def leafOk (k t i : Nat) : Bool :=
  !search k t (frontierState k t i)
def middleOk (k t i : Nat) : Bool :=
  !stepTest k t (frontierState (k + 1) t i)
    (fun w => !certificateMatch k (t - 1) w) (fun w => !certificateMatch k t w)
def stateOk (k t i : Nat) : Bool :=
  if i < leafCount k t then leafOk k t i else middleOk (k - 1) t i
def rootOk (t : Nat) : Bool :=
  !stepTest 13 t rootWires
    (fun w => !certificateMatch 13 (t - 1) w) (fun w => !certificateMatch 13 t w)
lemma leaf_impossible {k t i : Nat} (h : leafOk k t i = true) :
    Impossible k t (frontierState k t i) := by
  simp only [leafOk, Bool.not_eq_true'] at h
  exact exclude_search h
lemma middle_impossible {k t i : Nat} (ht : t ≤ 6)
    (hp : ∀ t ≤ 6, ∀ i < frontierCount k t, Impossible k t (frontierState k t i))
    (h : middleOk k t i = true) : Impossible (k + 1) t (frontierState (k + 1) t i) := by
  simp only [middleOk, Bool.not_eq_true'] at h
  apply exclude_step _ _ h
  · intro w hw; exact certificateMatch_ok (hp (t - 1) (by omega)) (by simpa using hw)
  · intro w hw; exact certificateMatch_ok (hp t ht) (by simpa using hw)
lemma level_impossible {k : Nat}
    (hp : ∀ t ≤ 6, ∀ i < frontierCount k t, Impossible k t (frontierState k t i))
    (hc : ∀ t ≤ 6, ∀ i < frontierCount (k + 1) t, stateOk (k + 1) t i = true)
    (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount (k + 1) t) :
    Impossible (k + 1) t (frontierState (k + 1) t i) := by
  have h := hc t ht i hi
  unfold stateOk at h
  split at h
  · exact leaf_impossible h
  · exact middle_impossible ht hp (by simpa using h)
def span (p : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => p i && span p n (i + 1)
lemma span_join {p : Nat → Bool} {a i b : Nat}
    (ha : span p a i = true) (hb : span p b (i + a) = true) : span p (a + b) i = true := by
  induction a generalizing i with
  | zero => simpa [span] using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add]
    simp only [span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by rw [show i + 1 + a = i + (a + 1) by omega]; exact hb)⟩
lemma span_ok {p : Nat → Bool} {n i : Nat} (h : span p n i = true) :
    ∀ j, i ≤ j → j < i + n → p j = true := by
  induction n generalizing i with
  | zero => intro j h1 h2; omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro j h1 h2
    by_cases he : j = i
    · exact he ▸ h.1
    · exact ih h.2 j (by omega) (by omega)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f9_0_0 : span (stateOk 9 0) 15 0 = true := by decide +kernel
theorem f9_all_0 : span (stateOk 9 0) 15 0 = true := f9_0_0
theorem f9_all_1 : span (stateOk 9 1) 0 0 = true := rfl
theorem f9_all_2 : span (stateOk 9 2) 0 0 = true := rfl
theorem f9_all_3 : span (stateOk 9 3) 0 0 = true := rfl
theorem f9_all_4 : span (stateOk 9 4) 0 0 = true := rfl
theorem f9_all_5 : span (stateOk 9 5) 0 0 = true := rfl
theorem f9_all_6 : span (stateOk 9 6) 0 0 = true := rfl
lemma f9Checked (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 9 t) : stateOk 9 t i = true := by
  interval_cases t
  · exact span_ok f9_all_0 i (Nat.zero_le i) hi
  · exact span_ok f9_all_1 i (Nat.zero_le i) hi
  · exact span_ok f9_all_2 i (Nat.zero_le i) hi
  · exact span_ok f9_all_3 i (Nat.zero_le i) hi
  · exact span_ok f9_all_4 i (Nat.zero_le i) hi
  · exact span_ok f9_all_5 i (Nat.zero_le i) hi
  · exact span_ok f9_all_6 i (Nat.zero_le i) hi
lemma f9Impossible (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 9 t) :
    Impossible 9 t (frontierState 9 t i) := by
  have h := f9Checked t ht i hi
  have hlt : i < leafCount 9 t := by
    interval_cases t
    · exact hi
    all_goals simp [frontierCount] at hi
  simpa [stateOk, hlt] using leaf_impossible (by simpa [stateOk, hlt] using h)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_0 : span (stateOk 10 0) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_25 : span (stateOk 10 0) 25 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_50 : span (stateOk 10 0) 25 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_75 : span (stateOk 10 0) 25 75 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_100 : span (stateOk 10 0) 25 100 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_125 : span (stateOk 10 0) 25 125 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_150 : span (stateOk 10 0) 25 150 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_175 : span (stateOk 10 0) 25 175 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_200 : span (stateOk 10 0) 25 200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_225 : span (stateOk 10 0) 25 225 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_250 : span (stateOk 10 0) 25 250 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_275 : span (stateOk 10 0) 25 275 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_300 : span (stateOk 10 0) 25 300 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_0_325 : span (stateOk 10 0) 16 325 = true := by decide +kernel
theorem f10_all_0 : span (stateOk 10 0) 341 0 = true := (@span_join (stateOk 10 0) 175 0 166 (@span_join (stateOk 10 0) 75 0 100 (@span_join (stateOk 10 0) 25 0 50 f10_0_0 (@span_join (stateOk 10 0) 25 25 25 f10_0_25 f10_0_50)) (@span_join (stateOk 10 0) 50 75 50 (@span_join (stateOk 10 0) 25 75 25 f10_0_75 f10_0_100) (@span_join (stateOk 10 0) 25 125 25 f10_0_125 f10_0_150))) (@span_join (stateOk 10 0) 75 175 91 (@span_join (stateOk 10 0) 25 175 50 f10_0_175 (@span_join (stateOk 10 0) 25 200 25 f10_0_200 f10_0_225)) (@span_join (stateOk 10 0) 50 250 41 (@span_join (stateOk 10 0) 25 250 25 f10_0_250 f10_0_275) (@span_join (stateOk 10 0) 25 300 16 f10_0_300 f10_0_325))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f10_1_0 : span (stateOk 10 1) 12 0 = true := by decide +kernel
theorem f10_all_1 : span (stateOk 10 1) 12 0 = true := f10_1_0
theorem f10_all_2 : span (stateOk 10 2) 0 0 = true := rfl
theorem f10_all_3 : span (stateOk 10 3) 0 0 = true := rfl
theorem f10_all_4 : span (stateOk 10 4) 0 0 = true := rfl
theorem f10_all_5 : span (stateOk 10 5) 0 0 = true := rfl
theorem f10_all_6 : span (stateOk 10 6) 0 0 = true := rfl
lemma f10Checked (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 10 t) : stateOk 10 t i = true := by
  interval_cases t
  · exact span_ok f10_all_0 i (Nat.zero_le i) hi
  · exact span_ok f10_all_1 i (Nat.zero_le i) hi
  · exact span_ok f10_all_2 i (Nat.zero_le i) hi
  · exact span_ok f10_all_3 i (Nat.zero_le i) hi
  · exact span_ok f10_all_4 i (Nat.zero_le i) hi
  · exact span_ok f10_all_5 i (Nat.zero_le i) hi
  · exact span_ok f10_all_6 i (Nat.zero_le i) hi
lemma f10Impossible (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 10 t) :
    Impossible 10 t (frontierState 10 t i) :=
  level_impossible f9Impossible (f10Checked) t ht i hi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_0 : span (stateOk 11 0) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_25 : span (stateOk 11 0) 25 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_50 : span (stateOk 11 0) 25 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_75 : span (stateOk 11 0) 25 75 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_100 : span (stateOk 11 0) 25 100 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_125 : span (stateOk 11 0) 25 125 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_150 : span (stateOk 11 0) 25 150 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_175 : span (stateOk 11 0) 25 175 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_200 : span (stateOk 11 0) 25 200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_225 : span (stateOk 11 0) 25 225 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_0_250 : span (stateOk 11 0) 3 250 = true := by decide +kernel
theorem f11_all_0 : span (stateOk 11 0) 253 0 = true := (@span_join (stateOk 11 0) 125 0 128 (@span_join (stateOk 11 0) 50 0 75 (@span_join (stateOk 11 0) 25 0 25 f11_0_0 f11_0_25) (@span_join (stateOk 11 0) 25 50 50 f11_0_50 (@span_join (stateOk 11 0) 25 75 25 f11_0_75 f11_0_100))) (@span_join (stateOk 11 0) 75 125 53 (@span_join (stateOk 11 0) 25 125 50 f11_0_125 (@span_join (stateOk 11 0) 25 150 25 f11_0_150 f11_0_175)) (@span_join (stateOk 11 0) 25 200 28 f11_0_200 (@span_join (stateOk 11 0) 25 225 3 f11_0_225 f11_0_250))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_0 : span (stateOk 11 1) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_25 : span (stateOk 11 1) 25 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_50 : span (stateOk 11 1) 25 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_75 : span (stateOk 11 1) 25 75 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_100 : span (stateOk 11 1) 25 100 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_125 : span (stateOk 11 1) 25 125 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_150 : span (stateOk 11 1) 25 150 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_175 : span (stateOk 11 1) 25 175 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_200 : span (stateOk 11 1) 25 200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_1_225 : span (stateOk 11 1) 5 225 = true := by decide +kernel
theorem f11_all_1 : span (stateOk 11 1) 230 0 = true := (@span_join (stateOk 11 1) 125 0 105 (@span_join (stateOk 11 1) 50 0 75 (@span_join (stateOk 11 1) 25 0 25 f11_1_0 f11_1_25) (@span_join (stateOk 11 1) 25 50 50 f11_1_50 (@span_join (stateOk 11 1) 25 75 25 f11_1_75 f11_1_100))) (@span_join (stateOk 11 1) 50 125 55 (@span_join (stateOk 11 1) 25 125 25 f11_1_125 f11_1_150) (@span_join (stateOk 11 1) 25 175 30 f11_1_175 (@span_join (stateOk 11 1) 25 200 5 f11_1_200 f11_1_225))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_2_0 : span (stateOk 11 2) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_2_25 : span (stateOk 11 2) 25 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_2_50 : span (stateOk 11 2) 25 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_2_75 : span (stateOk 11 2) 6 75 = true := by decide +kernel
theorem f11_all_2 : span (stateOk 11 2) 81 0 = true := (@span_join (stateOk 11 2) 50 0 31 (@span_join (stateOk 11 2) 25 0 25 f11_2_0 f11_2_25) (@span_join (stateOk 11 2) 25 50 6 f11_2_50 f11_2_75))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f11_3_0 : span (stateOk 11 3) 6 0 = true := by decide +kernel
theorem f11_all_3 : span (stateOk 11 3) 6 0 = true := f11_3_0
theorem f11_all_4 : span (stateOk 11 4) 0 0 = true := rfl
theorem f11_all_5 : span (stateOk 11 5) 0 0 = true := rfl
theorem f11_all_6 : span (stateOk 11 6) 0 0 = true := rfl
lemma f11Checked (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 11 t) : stateOk 11 t i = true := by
  interval_cases t
  · exact span_ok f11_all_0 i (Nat.zero_le i) hi
  · exact span_ok f11_all_1 i (Nat.zero_le i) hi
  · exact span_ok f11_all_2 i (Nat.zero_le i) hi
  · exact span_ok f11_all_3 i (Nat.zero_le i) hi
  · exact span_ok f11_all_4 i (Nat.zero_le i) hi
  · exact span_ok f11_all_5 i (Nat.zero_le i) hi
  · exact span_ok f11_all_6 i (Nat.zero_le i) hi
lemma f11Impossible (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 11 t) :
    Impossible 11 t (frontierState 11 t i) :=
  level_impossible f10Impossible (f11Checked) t ht i hi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f12_0_0 : span (stateOk 12 0) 25 0 = true := by decide +kernel
theorem f12_all_0 : span (stateOk 12 0) 25 0 = true := f12_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f12_1_0 : span (stateOk 12 1) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f12_1_25 : span (stateOk 12 1) 9 25 = true := by decide +kernel
theorem f12_all_1 : span (stateOk 12 1) 34 0 = true := (@span_join (stateOk 12 1) 25 0 9 f12_1_0 f12_1_25)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f12_2_0 : span (stateOk 12 2) 25 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f12_2_25 : span (stateOk 12 2) 9 25 = true := by decide +kernel
theorem f12_all_2 : span (stateOk 12 2) 34 0 = true := (@span_join (stateOk 12 2) 25 0 9 f12_2_0 f12_2_25)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f12_3_0 : span (stateOk 12 3) 17 0 = true := by decide +kernel
theorem f12_all_3 : span (stateOk 12 3) 17 0 = true := f12_3_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f12_4_0 : span (stateOk 12 4) 3 0 = true := by decide +kernel
theorem f12_all_4 : span (stateOk 12 4) 3 0 = true := f12_4_0
theorem f12_all_5 : span (stateOk 12 5) 0 0 = true := rfl
theorem f12_all_6 : span (stateOk 12 6) 0 0 = true := rfl
lemma f12Checked (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 12 t) : stateOk 12 t i = true := by
  interval_cases t
  · exact span_ok f12_all_0 i (Nat.zero_le i) hi
  · exact span_ok f12_all_1 i (Nat.zero_le i) hi
  · exact span_ok f12_all_2 i (Nat.zero_le i) hi
  · exact span_ok f12_all_3 i (Nat.zero_le i) hi
  · exact span_ok f12_all_4 i (Nat.zero_le i) hi
  · exact span_ok f12_all_5 i (Nat.zero_le i) hi
  · exact span_ok f12_all_6 i (Nat.zero_le i) hi
lemma f12Impossible (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 12 t) :
    Impossible 12 t (frontierState 12 t i) :=
  level_impossible f11Impossible (f12Checked) t ht i hi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f13_0_0 : span (stateOk 13 0) 3 0 = true := by decide +kernel
theorem f13_all_0 : span (stateOk 13 0) 3 0 = true := f13_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f13_1_0 : span (stateOk 13 1) 4 0 = true := by decide +kernel
theorem f13_all_1 : span (stateOk 13 1) 4 0 = true := f13_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f13_2_0 : span (stateOk 13 2) 4 0 = true := by decide +kernel
theorem f13_all_2 : span (stateOk 13 2) 4 0 = true := f13_2_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f13_3_0 : span (stateOk 13 3) 4 0 = true := by decide +kernel
theorem f13_all_3 : span (stateOk 13 3) 4 0 = true := f13_3_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f13_4_0 : span (stateOk 13 4) 4 0 = true := by decide +kernel
theorem f13_all_4 : span (stateOk 13 4) 4 0 = true := f13_4_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f13_5_0 : span (stateOk 13 5) 1 0 = true := by decide +kernel
theorem f13_all_5 : span (stateOk 13 5) 1 0 = true := f13_5_0
theorem f13_all_6 : span (stateOk 13 6) 0 0 = true := rfl
lemma f13Checked (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 13 t) : stateOk 13 t i = true := by
  interval_cases t
  · exact span_ok f13_all_0 i (Nat.zero_le i) hi
  · exact span_ok f13_all_1 i (Nat.zero_le i) hi
  · exact span_ok f13_all_2 i (Nat.zero_le i) hi
  · exact span_ok f13_all_3 i (Nat.zero_le i) hi
  · exact span_ok f13_all_4 i (Nat.zero_le i) hi
  · exact span_ok f13_all_5 i (Nat.zero_le i) hi
  · exact span_ok f13_all_6 i (Nat.zero_le i) hi
lemma f13Impossible (t : Nat) (ht : t ≤ 6) (i : Nat) (hi : i < frontierCount 13 t) :
    Impossible 13 t (frontierState 13 t i) :=
  level_impossible f12Impossible (f13Checked) t ht i hi
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root_0 : rootOk 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root_1 : rootOk 1 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root_2 : rootOk 2 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root_3 : rootOk 3 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root_4 : rootOk 4 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root_5 : rootOk 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem root_6 : rootOk 6 = true := by decide +kernel
lemma rootChecked (t : Nat) (ht : t ≤ 6) : rootOk t = true := by
  interval_cases t
  · exact root_0
  · exact root_1
  · exact root_2
  · exact root_3
  · exact root_4
  · exact root_5
  · exact root_6
lemma rootImpossible (t : Nat) (ht : t ≤ 6) : Impossible 14 t rootWires := by
  have h := rootChecked t ht
  simp only [rootOk, Bool.not_eq_true'] at h
  apply exclude_step _ _ h
  · intro w hw; exact certificateMatch_ok (f13Impossible (t - 1) (by omega)) (by simpa using hw)
  · intro w hw; exact certificateMatch_ok (f13Impossible t ht) (by simpa using hw)
end Main2331

namespace Contract

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom, List.foldl_cons, ← wiresFrom, ih]
    simp [step]
    omega

theorem getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom, List.foldl_cons, ← wiresFrom, ih _ (by simp [step]; omega)]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_eq (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp

theorem getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def normG (g : Gate) : Gate :=
  { op := g.op, inputs := if g.op.eval [false] = true then g.inputs.take 1 else g.inputs }

theorem normG_eval (g : Gate) (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2) (f : ℕ → Bool) :
    (normG g).op.eval ((normG g).inputs.map f) = g.op.eval (g.inputs.map f) := by
  obtain ⟨op, ins⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := h.1
  rcases hop with rfl | rfl | rfl
  · simp [normG, GateOp.eval]
  · simp [normG, GateOp.eval]
  · cases ins <;> simp [normG, GateOp.eval]

theorem normG_ok (g : Gate) (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    g.inputs.length ≤ 2) :
    ((normG g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (normG g).inputs.length ≤ 2) ∧
    ((normG g).op = GateOp.not → (normG g).inputs.length ≤ 1) := by
  obtain ⟨op, ins⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := h.1
  rcases hop with rfl | rfl | rfl
  · exact ⟨⟨Or.inl rfl, by simpa [normG, GateOp.eval] using h.2⟩, by simp [normG]⟩
  · exact ⟨⟨Or.inr (Or.inl rfl), by simpa [normG, GateOp.eval] using h.2⟩, by simp [normG]⟩
  · refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normG, GateOp.eval]
    · simp [normG, GateOp.eval]

theorem wiresFrom_normG (gs : List Gate)
    (hok : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ w : List Bool, wiresFrom (gs.map normG) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have hg := hok g List.mem_cons_self
    have s1 : wiresFrom ((g :: gs).map normG) w = wiresFrom (gs.map normG) (step w (normG g)) := rfl
    have s2 : wiresFrom (g :: gs) w = wiresFrom gs (step w g) := rfl
    have hs : step w (normG g) = step w g := by
      dsimp [step]
      rw [normG_eval g hg]
    rw [s1, s2, hs, ih (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))]

def shiftWire (x7 : Bool) (w : ℕ) : ℕ :=
  if w = 9 then (if x7 then 0 else 9)
  else if 10 ≤ w then w - 1
  else w

def transGate (x7 : Bool) (g : Gate) : Gate :=
  if 0 ∈ g.inputs ∧ 9 ∈ g.inputs then
    match g.op with
    | GateOp.and => ⟨GateOp.or, []⟩
    | _ => ⟨GateOp.and, []⟩
  else
    ⟨g.op, g.inputs.map (shiftWire x7)⟩

theorem transGate_ok (x7 : Bool) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (transGate x7 g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
    (transGate x7 g).inputs.length ≤ 2 := by
  unfold transGate
  split_ifs
  · cases g.op <;> simp
  · exact ⟨h.1, by simpa using h.2⟩

theorem transGate_mem0 (x7 : Bool) (g : Gate) :
    (transGate x7 g).inputs.contains 0 = true →
    ([0, 9].any fun w => g.inputs.contains w) = true := by
  unfold transGate
  split_ifs with h09
  · cases g.op <;> simp
  · intro hm
    rw [List.contains_iff_mem, List.mem_map] at hm
    obtain ⟨w, hw, hsw⟩ := hm
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, List.contains_iff_mem]
    unfold shiftWire at hsw
    by_cases hw9 : w = 9
    · subst hw9; exact Or.inr hw
    · rw [if_neg hw9] at hsw
      by_cases hw10 : 10 ≤ w
      · rw [if_pos hw10] at hsw; omega
      · rw [if_neg hw10] at hsw; subst hsw; exact Or.inl hw

theorem filter_map_length_le {α β : Type} (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ a, q (f a) = true → p a = true) (l : List α) :
    ((l.map f).filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases hq : q (f a) = true
    · have hp := h a hq
      simp only [hq, hp, ↓reduceIte, List.length_cons]
      omega
    · have hqf : q (f a) = false := Bool.eq_false_iff.mpr hq
      simp only [hqf, Bool.false_eq_true, ↓reduceIte]
      by_cases hp : p a = true
      · simp only [hp, ↓reduceIte, List.length_cons]; omega
      · have hpf : p a = false := Bool.eq_false_iff.mpr hp
        simp only [hpf, Bool.false_eq_true, ↓reduceIte]; exact ih

theorem two_mem_eq (l : List ℕ) (hlen : l.length ≤ 2) (h0 : 0 ∈ l) (h9 : 9 ∈ l) :
    l = [0, 9] ∨ l = [9, 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · cases h0
  · simp only [List.mem_singleton] at h0 h9; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0 h9
    rcases h0 with ha0 | hb0 <;> rcases h9 with ha9 | hb9
    · omega
    · subst ha0; subst hb9; exact Or.inl rfl
    · subst hb0; subst ha9; exact Or.inr rfl
    · omega
  · simp at hlen

def Rel (x7 b0 : Bool) (k : ℕ) (w1 w2 : List Bool) : Prop :=
  w1.length = 10 + k ∧ w2.length = 9 + k ∧
  w1.getD 0 false = b0 ∧ w1.getD 9 false = !b0 ∧
  (∀ i, 1 ≤ i → i < 9 → w2.getD i false = w1.getD i false) ∧
  (∀ j < k, w2.getD (9 + j) false = w1.getD (10 + j) false) ∧
  (x7 = false → w2.getD 0 false = b0) ∧
  (x7 = true → w2.getD 0 false = !b0)

theorem rel_init (x7 : Bool) (x8 : Fin 9 → Bool) :
    Rel x7 (x8 0) 0 (List.ofFn x8 ++ [!x8 0])
      (List.ofFn fun i : Fin 9 => if i = 0 then x7 != x8 0 else x8 i) := by
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.getD_append _ _ _ _ (by simp)]
    simp
  · have hsn := getD_snoc_eq (List.ofFn x8) (!x8 0)
    rwa [List.length_ofFn] at hsn
  · intro i hi1 hi9
    rw [List.getD_append _ _ _ _ (by simp [hi9])]
    have hne : (⟨i, hi9⟩ : Fin 9) ≠ 0 := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    have h1 : (List.ofFn fun j : Fin 9 => if j = 0 then x7 != x8 0 else x8 j).getD i false =
        (if (⟨i, hi9⟩ : Fin 9) = 0 then x7 != x8 0 else x8 ⟨i, hi9⟩) := by
      rw [List.getD_eq_getElem _ _ (by simp [hi9]), List.getElem_ofFn]
    have h2 : (List.ofFn x8).getD i false = x8 ⟨i, hi9⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp [hi9]), List.getElem_ofFn]
    rw [h1, h2]
    simp [hne]
  · intro j hj; cases hj
  · intro hx7; subst hx7; simp
  · intro hx7; subst hx7; simp

theorem rel_step (x7 b0 : Bool) (k : ℕ) (w1 w2 : List Bool) (g : Gate)
    (hrel : Rel x7 b0 k w1 w2)
    (hg_ok : (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (g.op = GateOp.not → g.inputs.length ≤ 1))
    (hcond : (x7 = true → 0 ∉ g.inputs) ∧ (x7 = false → 9 ∈ g.inputs → 0 ∈ g.inputs)) :
    Rel x7 b0 (k + 1) (step w1 g) (step w2 (transGate x7 g)) := by
  obtain ⟨hl1, hl2, hw0, hw9, hmid, hprev, hf0, ht0⟩ := hrel
  have heval_eq : (transGate x7 g).op.eval
      ((transGate x7 g).inputs.map fun i => w2.getD i false) =
      g.op.eval (g.inputs.map fun i => w1.getD i false) := by
    unfold transGate
    split_ifs with h09
    · have hnot_not : g.op ≠ GateOp.not := by
        intro hn
        have hl := hg_ok.2 hn
        rcases hinp : g.inputs with _ | ⟨a, _ | ⟨b, _⟩⟩
        · rw [hinp] at h09; exact List.not_mem_nil h09.1
        · rw [hinp] at h09; simp only [List.mem_singleton] at h09; omega
        · rw [hinp] at hl; simp at hl
      have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg_ok.1.1
      have hl_eq := two_mem_eq g.inputs hg_ok.1.2 h09.1 h09.2
      rcases hop with hop | hop | hop
      · rw [hop]
        rcases hl_eq with hin | hin <;> rw [hin] <;>
          simp only [List.map_cons, List.map_nil, hw0, hw9] <;> cases b0 <;> rfl
      · rw [hop]
        rcases hl_eq with hin | hin <;> rw [hin] <;>
          simp only [List.map_cons, List.map_nil, hw0, hw9] <;> cases b0 <;> rfl
      · exact (hnot_not hop).elim
    · simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro w hw
      simp only [Function.comp_apply, shiftWire]
      by_cases hw_eq9 : w = 9
      · subst hw_eq9
        rw [if_pos rfl]
        cases hx7 : x7
        · exfalso
          exact h09 ⟨hcond.2 hx7 hw, hw⟩
        · simp only [↓reduceIte, ht0 hx7, hw9]
      · rw [if_neg hw_eq9]
        by_cases hw10 : 10 ≤ w
        · rw [if_pos hw10]
          by_cases hwk : w < 10 + k
          · have hjk : w - 10 < k := by omega
            have h1 : w - 1 = 9 + (w - 10) := by omega
            have h2 : w = 10 + (w - 10) := by omega
            rw [h1, hprev (w - 10) hjk, ← h2]
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · rw [if_neg hw10]
          by_cases hw_eq0 : w = 0
          · subst hw_eq0
            cases hx7 : x7
            · rw [hf0 hx7, hw0]
            · exact (hcond.1 hx7 hw).elim
          · exact hmid w (by omega) (by omega)
  let v := g.op.eval (g.inputs.map fun i => w1.getD i false)
  have hs1 : step w1 g = w1 ++ [v] := rfl
  have hs2 : step w2 (transGate x7 g) = w2 ++ [v] := by dsimp [step]; rw [heval_eq]
  rw [hs1, hs2]
  refine ⟨by simp [hl1]; omega, by simp [hl2]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [getD_snoc_ne _ _ _ (by omega)]; exact hw0
  · rw [getD_snoc_ne _ _ _ (by omega)]; exact hw9
  · intro i hi1 hi9
    rw [getD_snoc_ne _ _ _ (by omega), getD_snoc_ne _ _ _ (by omega)]
    exact hmid i hi1 hi9
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [getD_snoc_ne _ _ _ (by omega), getD_snoc_ne _ _ _ (by omega)]
      exact hprev j hlt
    · have e2 : 9 + j = w2.length := by omega
      have e1 : 10 + j = w1.length := by omega
      rw [e2, getD_snoc_eq, e1, getD_snoc_eq]
  · intro hx7
    rw [getD_snoc_ne _ _ _ (by omega)]; exact hf0 hx7
  · intro hx7
    rw [getD_snoc_ne _ _ _ (by omega)]; exact ht0 hx7

theorem rel_wiresFrom (x7 b0 : Bool) (gs : List Gate) :
    ∀ (k : ℕ) (w1 w2 : List Bool),
      Rel x7 b0 k w1 w2 →
      (∀ g ∈ gs, (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) →
      (∀ g ∈ gs, (x7 = true → 0 ∉ g.inputs) ∧ (x7 = false → 9 ∈ g.inputs → 0 ∈ g.inputs)) →
      Rel x7 b0 (k + gs.length) (wiresFrom gs w1) (wiresFrom (gs.map (transGate x7)) w2) := by
  induction gs with
  | nil =>
    intro k w1 w2 hrel _ _
    simpa [wiresFrom] using hrel
  | cons g gs ih =>
    intro k w1 w2 hrel hok hcond
    have h1 := rel_step x7 b0 k w1 w2 g hrel (hok g List.mem_cons_self) (hcond g List.mem_cons_self)
    have h2 := ih (k + 1) (step w1 g) (step w2 (transGate x7 g)) h1
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hcond g' (List.mem_cons_of_mem _ hg'))
    simpa [wiresFrom, Nat.add_assoc, add_comm 1] using h2

theorem single_filter_disj {α : Type} (p : α → Bool) (l : List α)
    (hlen : (l.filter p).length ≤ 1) (a b : α) (ha : a ∈ l) (hb : b ∈ l)
    (hpa : p a = true) (hpb : p b = true) (q : α → Prop) (hqa : q a) (hqb : ¬ q b) : False := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    rw [List.filter_cons] at hlen
    by_cases hpx : p x = true
    · simp only [hpx, ↓reduceIte, List.length_cons] at hlen
      have h0 : xs.filter p = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hnone : ∀ y ∈ xs, p y ≠ true := by
        intro y hy hpy
        have hm : y ∈ xs.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
        rw [h0] at hm; cases hm
      rcases List.mem_cons.mp ha with rfl | haxs
      · rcases List.mem_cons.mp hb with rfl | hbxs
        · exact hqb hqa
        · exact hnone b hbxs hpb
      · exact hnone a haxs hpa
    · have hpxf : p x = false := Bool.eq_false_iff.mpr hpx
      simp only [hpxf, Bool.false_eq_true, ↓reduceIte] at hlen
      rcases List.mem_cons.mp ha with rfl | haxs
      · rw [hpa] at hpxf; cases hpxf
      · rcases List.mem_cons.mp hb with rfl | hbxs
        · rw [hpb] at hpxf; cases hpxf
        · exact ih hlen haxs hbxs

end Contract

open PEqualNP.Outside.L_meta_2309_aux.Contract PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem contract : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = !x4 (0 : Fin (9 : ℕ))) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x6 : ℕ) => x5.inputs.contains x6) x2).length ≤ (1 : ℕ) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Bool), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size < x1.size ∧ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (0 : ℕ)) x6.gates).length ≤ (1 : ℕ) ∧ ∀ (x8 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x6 fun (x9 : Fin (9 : ℕ)) => if x9 = (0 : Fin (9 : ℕ)) then x7 != x8 (0 : Fin (9 : ℕ)) else x8 x9 := by
  intro x1 x2_in hfan hw9 hflt
  dsimp only [x2_in] at hflt
  obtain ⟨gs, out⟩ := x1
  cases gs with
  | nil =>
    exfalso
    have h0 := hw9 (fun _ => false)
    have hl : (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = false :=
      List.getD_eq_default _ _ (by simp)
    change (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = true at h0
    rw [hl] at h0
    cases h0
  | cons g0 tail =>
    have hsz_pos : 0 < ({ gates := g0 :: tail, output := out } : Circuit).size := by
      change 0 < (g0 :: tail).length; simp
    have hw_g0 : ∀ x : Fin 9 → Bool,
        step (List.ofFn x) g0 = List.ofFn x ++ [!x 0] := by
      intro x
      have h9 := hw9 x
      change (wiresFrom tail (step (List.ofFn x) g0)).getD 9 false = !x 0 at h9
      rw [getD_wiresFrom_lt tail _ 9 (by simp [step])] at h9
      have hl : (List.ofFn x).length = 9 := List.length_ofFn
      have hsn : (step (List.ofFn x) g0).getD 9 false =
          g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) := by
        have h0 := getD_snoc_eq (List.ofFn x)
          (g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false))
        rwa [List.length_ofFn] at h0
      rw [hsn] at h9
      dsimp [step]
      rw [h9]
    let x2 := tail.map normG
    have htail_fan : ∀ g ∈ tail,
        g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hfan g (List.mem_cons_of_mem _ hg)
    have hx2_ok : ∀ g ∈ x2,
        (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
        (g.op = GateOp.not → g.inputs.length ≤ 1) := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact normG_ok g' (htail_fan g' hg')
    have hw_eq : ∀ x : Fin 9 → Bool,
        ({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x) =
          wiresFrom x2 (List.ofFn x ++ [!x 0]) := by
      intro x
      change wiresFrom tail (step (List.ofFn x) g0) = _
      rw [hw_g0 x, wiresFrom_normG tail htail_fan]
    by_cases hout9 : out < 9
    · refine ⟨⟨[], out⟩, false, (by intro g hg; cases hg), hsz_pos, (by simp), ?_⟩
      intro x8
      change (({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x8)).getD out false =
        (List.ofFn fun x9 : Fin 9 => if x9 = 0 then false != x8 0 else x8 x9).getD out false
      rw [hw_eq x8, getD_wiresFrom_lt x2 _ out (by simp; omega),
        List.getD_append _ _ _ _ (by simp [hout9])]
      congr 1
      ext i
      by_cases hi0 : i = 0
      · subst hi0; simp
      · simp [hi0]
    · by_cases hout_eq9 : out = 9
      · subst hout_eq9
        refine ⟨⟨[], 0⟩, true, (by intro g hg; cases hg), hsz_pos, (by simp), ?_⟩
        intro x8
        rw [show circuitFun 9 { gates := g0 :: tail, output := 9 } x8 = !x8 0 from hw9 x8]
        change (!x8 0) = (List.ofFn fun x9 : Fin 9 => if x9 = 0 then true != x8 0 else x8 x9).getD 0 false
        simp
      · by_cases hout_ge : 10 + x2.length ≤ out
        · refine ⟨⟨[], 9⟩, false, (by intro g hg; cases hg), hsz_pos, (by simp), ?_⟩
          intro x8
          change (({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x8)).getD out false =
            (List.ofFn fun x9 : Fin 9 => if x9 = 0 then false != x8 0 else x8 x9).getD 9 false
          rw [hw_eq x8, List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
            List.getD_eq_default _ _ (by simp)]
        · let x7 : Bool := decide (∃ g ∈ x2, 9 ∈ g.inputs ∧ 0 ∉ g.inputs)
          have hflt' : (x2.filter (fun g => [0, 9].any fun w => g.inputs.contains w)).length ≤ 1 := hflt
          have hcond : ∀ g ∈ x2, (x7 = true → 0 ∉ g.inputs) ∧
              (x7 = false → 9 ∈ g.inputs → 0 ∈ g.inputs) := by
            intro g hg
            refine ⟨?_, ?_⟩
            · intro hx7 h0g
              obtain ⟨g9, hg9, h9in, h0not⟩ := of_decide_eq_true hx7
              have p_g : ([0, 9].any fun w => g.inputs.contains w) = true := by
                simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
                  List.contains_iff_mem]
                exact Or.inl h0g
              have p_g9 : ([0, 9].any fun w => g9.inputs.contains w) = true := by
                simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
                  List.contains_iff_mem]
                exact Or.inr h9in
              exact single_filter_disj _ x2 hflt' g g9 hg hg9 p_g p_g9
                (fun z => 0 ∈ z.inputs) h0g h0not
            · intro hx7 h9g
              by_contra h0not
              have ht : x7 = true := decide_eq_true ⟨g, hg, h9g, h0not⟩
              rw [hx7] at ht; cases ht
          let x6 : Circuit := ⟨x2.map (transGate x7), out - 1⟩
          have hx6_fan : FanInTwo x6 := by
            intro g hg
            obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
            exact transGate_ok x7 g' (hx2_ok g' hg').1
          have hx6_sz : x6.size < ({ gates := g0 :: tail, output := out } : Circuit).size := by
            change (x2.map (transGate x7)).length < (g0 :: tail).length
            simp [x2]
          have hx6_flt : (x6.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 :=
            (filter_map_length_le (transGate x7)
              (fun g => [0, 9].any fun w => g.inputs.contains w)
              (fun g => g.inputs.contains 0)
              (transGate_mem0 x7) x2).trans hflt'
          refine ⟨x6, x7, hx6_fan, hx6_sz, hx6_flt, ?_⟩
          intro x8
          have hrel := rel_wiresFrom x7 (x8 0) x2 0
            (List.ofFn x8 ++ [!x8 0])
            (List.ofFn fun i : Fin 9 => if i = 0 then x7 != x8 0 else x8 i)
            (rel_init x7 x8) hx2_ok hcond
          have hj_lt : out - 10 < 0 + x2.length := by omega
          have hprev := hrel.2.2.2.2.2.1 (out - 10) hj_lt
          have e1 : 10 + (out - 10) = out := by omega
          have e2 : 9 + (out - 10) = out - 1 := by omega
          rw [e1, e2] at hprev
          change (({ gates := g0 :: tail, output := out } : Circuit).wires (List.ofFn x8)).getD out false =
            (wiresFrom (x2.map (transGate x7))
              (List.ofFn fun i : Fin 9 => if i = 0 then x7 != x8 0 else x8 i)).getD (out - 1) false
          rw [hw_eq x8, hprev]

namespace Samples
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2309_aux.Main2331
def flip (x : Fin 9 → Bool) (i : Fin 9) := if i=0 then !(x 0) else x i
abbrev base := PEqualNP.Outside.L_meta_2309_aux.Main2331.raw
def inputs : List Sig := neg raw0 :: base.tail
theorem valid_inputs : ∀ a∈inputs, Valid a := by
  intro a h
  rcases List.mem_cons.mp h with rfl|ht
  · exact valid_neg (raw_valid _ (by simp [PEqualNP.Outside.L_meta_2309_aux.Main2331.raw]))
  · exact raw_valid _ (List.mem_of_mem_tail ht)
theorem coords (s : Bool) (i : Fin 414) :
    List.ofFn (flip (sample s i)) = inputs.map (bit s i) := by
  have signed (x : Fin 9 → Bool) : List.ofFn (flip x) = (!(x 0)) :: (List.ofFn x).tail := by
    rw [List.ofFn_succ (f := flip x),List.ofFn_succ (f := x)]
    simp [flip]
  rw [signed,sample_list]
  change (!(bit s i raw0)) :: _ = bit s i (neg raw0) :: _
  rw [bit_neg _ _ (raw_valid raw0 (by simp [PEqualNP.Outside.L_meta_2309_aux.Main2331.raw]))]
  rfl

lemma signed_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn (flip x)) = edgeF x) : target ∈ execute C.gates inputs := by
  let w := execute C.gates inputs
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates inputs valid_inputs
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates inputs).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ valid_inputs (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [coords, sample_ok] at eq
    exact eq
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)
theorem required {v : List Sig} (val : ∀ a∈v, Valid a)
    (all : v.all (fun a => unionSep true (v.erase a) != top) = true)
    {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ v) : v.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp all a hr
  have cov : unionSep true (v.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi, decide_true]
      obtain ⟨b,hb,h⟩ := live_sep l i hi
      have ba : b ≠ a := fun e => hn (e ▸ hb)
      exact (mem_unionSep true _ _).2 ⟨b,(List.mem_erase_of_ne ba).mpr (hs _ hb),
        sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi,decide_false]
      exact valid_unionSep (fun x hx => val x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail

end Samples

namespace Cert
open PEqualNP.Outside.L_meta_2309_aux.Main2331
-- The tag propagation argument follows L-meta-2331 with arbitrary truth table projections.
def Tight (i : SigHom) (k : Nat) (S : Finset Sig) : Prop :=
  ∀ q, q + 1 < k → ¬ Feasible i q S
def Slack (i : SigHom) (k : Nat) (S : Finset Sig) : Prop :=
  ∀ q, q + 2 < k → ¬ Feasible i q S
def WireTagOk (k : Nat) (S : Finset Sig) (a : Sig) : Tag → Prop
  | .tNone => True
  | .tDeg3 => ∃ i : SigHom, i.fn a = zero ∧ Slack i k S
  | .tSpec0 => ∃ i : SigHom, i.fn a = zero ∧ Tight i k S
  | .tSpec1 => ∃ i : SigHom, i.fn a = one ∧ Tight i k S
def TagOk (k : Nat) (S : Finset Sig) (τ : Sig → Tag) : Prop :=
  ∀ a ∈ S, WireTagOk k S a (τ a)
lemma wireTagOk_unary_step {k : Nat} {U : Finset Sig} {a x : Sig} {tg : Tag} (hva : Valid a)
    (h : WireTagOk (k + 1) (insert a U) x tg) : WireTagOk k (insert (neg a) U) x tg := by
  cases tg with
  | tNone => trivial
  | tDeg3 =>
    obtain ⟨i, hp, hs⟩ := h
    exact ⟨i, hp, fun q hq hf => hs (q + 1) (by omega) (pull_unary hva hf)⟩
  | tSpec0 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_unary hva hf)⟩
  | tSpec1 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_unary hva hf)⟩
lemma wireTagOk_binary_step {k : Nat} {U : Finset Sig} {a b x : Sig} {d : Bool} {tg : Tag}
    (h : WireTagOk (k + 1) (insert a (insert b U)) x tg) :
    WireTagOk k (insert (bin d a b) U) x tg := by
  cases tg with
  | tNone => trivial
  | tDeg3 =>
    obtain ⟨i, hp, hs⟩ := h
    exact ⟨i, hp, fun q hq hf => hs (q + 1) (by omega) (pull_binary hf)⟩
  | tSpec0 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_binary hf)⟩
  | tSpec1 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_binary hf)⟩
lemma restrict_live {k t S τ} (h : Live k t S) (ht : TagOk k S τ) : TRestricted k t S τ := by
  induction h generalizing τ with
  | stop => exact TRestricted.stop
  | @unary k t U a ha hf tail ih =>
    have hta := ht a (Finset.mem_insert_self _ _)
    have hr1 : τ a ≠ .tSpec0 ∧ τ a ≠ .tSpec1 := by
      constructor <;> intro heq <;> rw [heq] at hta
      · obtain ⟨i, hp0, hti⟩ := hta
        have hz : ¬ proper (i.fn a) := fun hp => hp.2.1 hp0
        have ho : ¬ proper (i.fn (neg a)) := fun hp =>
          hp.2.2 (by rw [i.hneg ha.1, hp0, neg_laws.1])
        obtain ⟨q, hq, hfe⟩ := feasible_const tail i (neg a) (Finset.mem_insert_self _ _) ho
        exact hti q (by omega) (free_unary ha.1 hz hfe)
      · obtain ⟨i, hp1, hti⟩ := hta
        have ho : ¬ proper (i.fn a) := fun hp => hp.2.2 hp1
        have hz : ¬ proper (i.fn (neg a)) := fun hp =>
          hp.2.1 (by rw [i.hneg ha.1, hp1, neg_laws.2])
        obtain ⟨q, hq, hfe⟩ := feasible_const tail i (neg a) (Finset.mem_insert_self _ _) hz
        exact hti q (by omega) (free_unary ha.1 ho hfe)
    have hr2 : τ a = .tDeg3 → a ∉ U := by
      intro heq haU
      rw [heq] at hta
      obtain ⟨i, hp0, hsl⟩ := hta
      have hz : ¬ proper (i.fn a) := fun hp => hp.2.1 hp0
      have ho : ¬ proper (i.fn (neg a)) := fun hp =>
        hp.2.2 (by rw [i.hneg ha.1, hp0, neg_laws.1])
      have hne : neg a ≠ a := fun e => by rw [e] at hf; exact hf (Finset.mem_insert_self _ _)
      obtain ⟨q, hq, hfe⟩ := feasible_two_consts tail i (neg a) a
        (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem haU) hne ho hz
      exact hsl q (by omega) (free_unary ha.1 hz hfe)
    have ht' : TagOk k (insert (neg a) U) (updUnaryTag τ a) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxU
      · unfold updUnaryTag; simp only [ite_true]
        split
        · rename_i hd3
          rw [hd3] at hta
          obtain ⟨i, hp0, hsl⟩ := hta
          have hz : ¬ proper (i.fn a) := fun hp => hp.2.1 hp0
          refine ⟨i, by rw [i.hneg ha.1, hp0]; exact neg_laws.1, ?_⟩
          intro q hq hfe; exact hsl q (by omega) (free_unary ha.1 hz hfe)
        · trivial
      · have hne : x ≠ neg a := fun e => hf (e ▸ Finset.mem_insert_of_mem hxU)
        unfold updUnaryTag; simp only [hne, ite_false]
        exact wireTagOk_unary_step ha.1 (ht x (Finset.mem_insert_of_mem hxU))
    exact TRestricted.unary ha hf hr1 hr2 (ih ht')
  | @binary k t U a b d ha hb hab hf tail ih =>
    have hta := ht a (Finset.mem_insert_self _ _)
    have htb := ht b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    cases d with
    | false =>
      have sideAnd : ∀ {x y : Sig} (hx : Valid x) (hy : Valid y) (hxy : x ≠ y)
          (hfx : bin false x y ∉ insert x (insert y U))
          (tail' : Live k t (insert (bin false x y) U))
          (htx : WireTagOk (k + 1) (insert x (insert y U)) x (τ x)),
          τ x ≠ .tSpec0 ∧ (τ x ≠ .tNone → x ∉ U) := by
        intro x y _ _ _ hfx tail' htx
        constructor
        · intro heq; rw [heq] at htx
          obtain ⟨i, hp0, hti⟩ := htx
          have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
          have hg0 : ¬ proper (i.fn (bin false x y)) := fun hp =>
            hp.2.1 (by rw [i.hbin, hp0, bin_comm]; exact (bin_laws (i.valid y)).2.2.1)
          obtain ⟨q, hq, hfe⟩ := feasible_const tail' i (bin false x y) (Finset.mem_insert_self _ _) hg0
          exact hti q (by omega) (free_binary_left hz hfe)
        · intro hne hxU
          cases htxc : τ x with
          | tNone => exact hne htxc
          | tSpec0 =>
            rw [htxc] at htx
            obtain ⟨i, hp0, hti⟩ := htx
            have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
            obtain ⟨q, hq, hfe⟩ := feasible_const tail' i x (Finset.mem_insert_of_mem hxU) hz
            exact hti q (by omega) (free_binary_left hz hfe)
          | tSpec1 =>
            rw [htxc] at htx
            obtain ⟨i, hp1, hti⟩ := htx
            have ho : ¬ proper (i.fn x) := fun hp => hp.2.2 hp1
            obtain ⟨q, hq, hfe⟩ := feasible_const tail' i x (Finset.mem_insert_of_mem hxU) ho
            exact hti q (by omega) (free_binary_left ho hfe)
          | tDeg3 =>
            rw [htxc] at htx
            obtain ⟨i, hp0, hsl⟩ := htx
            have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
            have hg0 : ¬ proper (i.fn (bin false x y)) := fun hp =>
              hp.2.1 (by rw [i.hbin, hp0, bin_comm]; exact (bin_laws (i.valid y)).2.2.1)
            have hne' : bin false x y ≠ x := fun e => by rw [e] at hfx; exact hfx (Finset.mem_insert_self _ _)
            obtain ⟨q, hq, hfe⟩ := feasible_two_consts tail' i (bin false x y) x
              (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hxU) hne' hg0 hz
            exact hsl q (by omega) (free_binary_left hz hfe)
      have hra := sideAnd ha.1 hb.1 hab hf tail hta
      have hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U) :=
        sideAnd hb.1 ha.1 hab.symm (by rwa [bin_comm, Finset.insert_comm])
          (by rwa [bin_comm]) (by rwa [Finset.insert_comm])
      have ht' : TagOk k (insert (bin false a b) U) (updAndTag τ a b) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxU
        · unfold updAndTag; simp only [ite_true]
          split
          · rename_i hd
            rcases hd with hda | hdb
            · rw [hda] at hta
              obtain ⟨i, hp0, hsl⟩ := hta
              have hz : ¬ proper (i.fn a) := fun hp => hp.2.1 hp0
              refine ⟨i, by rw [i.hbin, hp0, bin_comm]; exact (bin_laws (i.valid b)).2.2.1, ?_⟩
              intro q hq hfe; exact hsl q (by omega) (free_binary_left hz hfe)
            · rw [hdb] at htb
              obtain ⟨i, hp0, hsl⟩ := htb
              have hz : ¬ proper (i.fn b) := fun hp => hp.2.1 hp0
              refine ⟨i, by rw [i.hbin, hp0]; exact (bin_laws (i.valid a)).2.2.1, ?_⟩
              intro q hq hfe; exact hsl q (by omega) (free_binary_right hz hfe)
          · trivial
        · have hne : x ≠ bin false a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
          unfold updAndTag; simp only [hne, ite_false]
          exact wireTagOk_binary_step (ht x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)))
      exact TRestricted.binaryAnd ha hb hab hf hra hrb (ih ht')
    | true =>
      have sideOr : ∀ {x y : Sig}
          (tail' : Live k t (insert (bin true x y) U))
          (htx : WireTagOk (k + 1) (insert x (insert y U)) x (τ x)),
          τ x ≠ .tSpec1 ∧ (τ x = .tSpec0 → x ∉ U) := by
        intro x y tail' htx
        constructor
        · intro heq; rw [heq] at htx
          obtain ⟨i, hp1, hti⟩ := htx
          have ho : ¬ proper (i.fn x) := fun hp => hp.2.2 hp1
          have hg1 : ¬ proper (i.fn (bin true x y)) := fun hp =>
            hp.2.2 (by rw [i.hbin, hp1, bin_comm]; exact (bin_laws (i.valid y)).2.2.2.1)
          obtain ⟨q, hq, hfe⟩ := feasible_const tail' i (bin true x y) (Finset.mem_insert_self _ _) hg1
          exact hti q (by omega) (free_binary_left ho hfe)
        · intro heq hxU; rw [heq] at htx
          obtain ⟨i, hp0, hti⟩ := htx
          have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
          obtain ⟨q, hq, hfe⟩ := feasible_const tail' i x (Finset.mem_insert_of_mem hxU) hz
          exact hti q (by omega) (free_binary_left hz hfe)
      have hra := sideOr tail hta
      have hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U) :=
        sideOr (by rwa [bin_comm]) (by rwa [Finset.insert_comm])
      have ht' : TagOk k (insert (bin true a b) U) (updOrTag τ a b) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxU
        · unfold updOrTag; simp only [ite_true]; trivial
        · have hne : x ≠ bin true a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
          unfold updOrTag; simp only [hne, ite_false]
          by_cases hxa : x = a ∧ τ a = .tDeg3
          · simp only [hxa]
            obtain ⟨rfl, hd3⟩ := hxa
            rw [hd3] at hta
            obtain ⟨i, hp0, hsl⟩ := hta
            have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
            refine ⟨i, hp0, fun q hq hfe => hsl q (by omega) (free_binary_left hz hfe)⟩
          · simp only [hxa, ite_false]
            by_cases hxb : x = b ∧ τ b = .tDeg3
            · simp only [hxb]
              obtain ⟨rfl, hd3⟩ := hxb
              rw [hd3] at htb
              obtain ⟨i, hp0, hsl⟩ := htb
              have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
              refine ⟨i, hp0, fun q hq hfe => hsl q (by omega) (free_binary_right hz hfe)⟩
            · simp only [hxb, ite_false]
              exact wireTagOk_binary_step (ht x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)))
      exact TRestricted.binaryOr ha hb hab hf hra hrb (ih ht')

end Cert

namespace Cert
open PEqualNP.Outside.L_meta_2309_aux.Main2331
def pick (m : Nat) (r i : Fin 414) := if m.testBit i.val then i else r
def side (m r a : Nat) := (m &&& a) ||| (if a.testBit r then bnot m else 0)
theorem side_eq {m : Nat} (hm : Valid1 m) (r : Fin 414) (a : Nat) :
    side m r.val a = reindex (pick m r) a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [reindex_testBit]
  by_cases h : j<414
  · simp only [h,dite_true,side,Nat.testBit_or,Nat.testBit_and,pick]
    cases ha : a.testBit r.val <;> cases hj : m.testBit j <;> simp [ha,hj,testBit_bnot hm,h]
  · have mj := hm j (by omega)
    simp only [h,dite_false,side,Nat.testBit_or,Nat.testBit_and,mj,Bool.false_and,Bool.false_or]
    cases ha : a.testBit r.val <;> simp [ha,testBit_bnot hm,h]

def H (m : Sig) (r s : Fin 414) (vm : Valid m) : SigHom :=
  let proj := pairHom (pick m.1 r) (pick m.2 s)
  let fast := fun a : Sig => (side m.1 r.val a.1,side m.2 s.val a.2)
  have eq : fast = proj.fn := by funext a; exact Prod.ext (side_eq vm.1 r _) (side_eq vm.2 s _)
  {proj with
    fn := fast
    valid := eq ▸ proj.valid
    hneg := by intro a ha; rw [eq]; exact proj.hneg ha
    hbin := by intro d a b; rw [eq]; exact proj.hbin _ _ _
    hzero := eq ▸ proj.hzero
    hone := eq ▸ proj.hone
    htarget := eq ▸ proj.htarget}

def Bad (k : Nat) (v : List Sig) := ∀ m≤k, ∀ t S, Live m t S → (∀ a∈S,a∈v) → False
def essential (v : List Sig) := v.all (fun a => unionSep true (v.erase a) != top)
def good (v : List Sig) := v.all (fun a => a.1 ≤ top && a.2 ≤ top)
def tagFn (ws : List Wire) (a : Sig) := ((ws.lookup a).getD .tNone)
def projectedOK (pr : SigHom) (ws child : List Sig) :=
  ws.all fun a => let b := pr.fn a; b == zero || b == one || child.contains b

theorem bound_of (pr : SigHom) (parent child : List Sig) (k : Nat) (h : Bad k child)
    (chk : projectedOK pr parent child = true) : ¬Feasible pr k parent.toFinset := by
  rintro ⟨m,hm,t,S,hl,ss⟩
  apply h m hm t S hl
  intro a ha
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (ss ha)
  have p := live_proper hl _ ha
  have test := List.all_eq_true.mp chk x (List.mem_toFinset.mp hx)
  simpa [p.2.1,p.2.2] using test

theorem valid_of {w : List Sig} (g : good w=true) {a : Sig} (ha : a∈w) : Valid a := by
  have le := List.all_eq_true.mp g a ha
  simp only [Bool.and_eq_true,decide_eq_true_eq] at le
  exact ⟨valid1_of_le_top le.1,valid1_of_le_top le.2⟩

theorem size_bad (k : Nat) (w : List Sig) (g : good w=true) (e : essential w=true)
    (small : k+1 < w.toFinset.card) : Bad k w := by
  intro m hm t S hl sub
  have eq := PEqualNP.Outside.L_meta_2309_aux.Samples.required (fun _ => valid_of g) e hl sub
  have sz := (live_size hl).2
  rw [←eq] at sz
  omega

theorem detag (k : Nat) (ws : List Wire) (w : List Sig) (hw : sigsOf ws = w)
    (every : ∀ p∈ws, WireTagOk k w.toFinset p.1 p.2)
    (matchTags : ∀ p∈ws, p.2=tagFn ws p.1) : TagOk k w.toFinset (tagFn ws) := by
  intro a ha
  rw [←hw] at ha
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha : _∈sigsOf ws)
  rw [←matchTags p hp]
  exact every p hp

theorem finished (k : Nat) (ws : List Wire) (w : List Sig) (hw : sigsOf ws = w)
    (g : good w=true) (e : essential w=true) (nd : w.Nodup)
    (mt : ∀ p∈ws, p.2=tagFn ws p.1)
    (ev : ∀ p∈ws, WireTagOk k w.toFinset p.1 p.2)
    (tests : ∀ t, t+w.length≤k+1 → Impossible k t ws) : Bad k w := by
  intro m hm t S hl sub
  have eq := PEqualNP.Outside.L_meta_2309_aux.Samples.required (fun _ => valid_of g) e hl sub
  subst S
  have sz := (live_size hl).2
  rw [List.toFinset_card_of_nodup nd] at sz
  have okk := detag k ws w hw ev mt
  have shrink {j l : Nat} {s : Finset Sig} {a : Sig} {b : Tag} (le : j≤l) (h : WireTagOk l s a b) :
      WireTagOk j s a b := by
    cases b with
    | tNone => trivial
    | _ => obtain ⟨pr,hp,hlow⟩ := h; exact ⟨pr,hp,fun q hq => hlow q (by omega)⟩
  apply tests t (by omega) m hm _ _ ⟨hw ▸ nd,by rw [hw],mt⟩
  exact restrict_live hl (fun a ha => shrink hm (okk a ha))

theorem slack_of {k : Nat} {w : List Sig} {a : Sig} (pr : SigHom) (pz : pr.fn a=zero)
    (b : ¬ Feasible pr (k-3) w.toFinset) : WireTagOk k w.toFinset a .tDeg3 :=
  ⟨pr,pz,fun q hq f => b (feasible_mono f (by omega))⟩
theorem zero_of {k : Nat} {w : List Sig} {a : Sig} (pr : SigHom) (pz : pr.fn a=zero)
    (b : ¬ Feasible pr (k-2) w.toFinset) : WireTagOk k w.toFinset a .tSpec0 :=
  ⟨pr,pz,fun q hq f => b (feasible_mono f (by omega))⟩
theorem one_of {k : Nat} {w : List Sig} {a : Sig} (pr : SigHom) (pz : pr.fn a=one)
    (b : ¬ Feasible pr (k-2) w.toFinset) : WireTagOk k w.toFinset a .tSpec1 :=
  ⟨pr,pz,fun q hq f => b (feasible_mono f (by omega))⟩
end Cert

namespace Cert.Compact
open PEqualNP.Outside.L_meta_2309_aux.Main2331
def coords (mask : Nat) := (List.range 9).filter fun i => !mask.testBit i
def maskVal (mask : Nat) : Sig :=
  let a : Sig := (List.range 9).foldl (fun (p : Sig) i => if mask.testBit i then
    (p.1 &&& bnot (raw.getD i zero).1,p.2 &&& bnot (raw.getD i zero).2) else p) (top,top)
  (a.1 &&& top,a.2 &&& top)
def firstBit (n : Nat) : Fin 414 := Fin.ofNat 414 (((n &&& (n-1)) ^^^ n).log2)
def proj (mask : Nat) : SigHom :=
  H (maskVal mask) (firstBit (maskVal mask).1) (firstBit (maskVal mask).2)
    ⟨valid1_of_le_top Nat.and_le_right,valid1_of_le_top Nat.and_le_right⟩
def wire (signed : Bool) (mask i : Nat) : Sig :=
  (proj mask).fn (if signed && i=0 then neg raw0 else raw.getD i zero)
def full (signed : Bool) (mask : Nat) := (coords mask).map (wire signed mask)
def tg (tags i : Nat) := tagOfNat ((tags >>> (2*i)) &&& 3)
def ws (s : Bool) (m tags : Nat) : List Wire := (coords m).map fun i => (wire s m i,tg tags i)
def next (m i : Nat) := m ||| (1 <<< i)
def budget (k : Nat) (t : Tag) := if t=.tDeg3 then k-3 else k-2
def polarity (t : Tag) := if t=.tSpec1 then one else zero
def shape (s : Bool) (m tags : Nat) := good (full s m) && essential (full s m) &&
  decide (full s m).Nodup && (ws s m tags).all (fun p => p.2 == tagFn (ws s m tags) p.1)
def geometry (s : Bool) (m tags : Nat) := (coords m).all fun i =>
  tg tags i == .tNone || (((proj (next m i)).fn (wire s m i) == polarity (tg tags i)) &&
    projectedOK (proj (next m i)) (full s m) (full s (next m i)))
theorem fromRows (s : Bool) (m k tags : Nat) (sh : shape s m tags=true) (geom : geometry s m tags=true)
    (lower : ∀ i∈coords m, tg tags i ≠ .tNone → Bad (budget k (tg tags i)) (full s (next m i)))
    (checks : ∀ t, t + (full s m).length ≤ k+1 → Impossible k t (ws s m tags)) : Bad k (full s m) := by
  simp only [shape,Bool.and_eq_true,decide_eq_true_eq] at sh
  apply finished k (ws s m tags) _ (by simp [sigsOf,ws,full,List.map_map,Function.comp_def])
    sh.1.1.1 sh.1.1.2 sh.1.2 _ _ checks
  · intro p hp
    exact beq_iff_eq.mp (List.all_eq_true.mp sh.2 p hp)
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have geo := List.all_eq_true.mp geom i hi
    cases ht : tg tags i with
    | tNone => trivial
    | tDeg3 =>
      have need := lower i hi (by simp [ht])
      simp only [ht,budget,ite_true] at need
      simp [ht,polarity] at geo
      exact slack_of (proj (next m i)) geo.1 (bound_of _ _ _ _ need geo.2)
    | tSpec0 =>
      have need := lower i hi (by simp [ht])
      simp [ht,budget] at need
      simp [ht,polarity] at geo
      exact zero_of (proj (next m i)) geo.1 (bound_of _ _ _ _ need geo.2)
    | tSpec1 =>
      have need := lower i hi (by simp [ht])
      simp [ht,budget] at need
      simp [ht,polarity] at geo
      exact one_of (proj (next m i)) geo.1 (bound_of _ _ _ _ need geo.2)

structure Row where
  signed : Bool
  mask : Nat
  k : Nat
  tags : Nat
def Row.goal (r : Row) := Bad r.k (full r.signed r.mask)
def children (get : Nat → Row) (link : Nat → Nat → Nat) (idx : Nat) :=
  let r := get idx
  (coords r.mask).all fun i => tg r.tags i == .tNone ||
    let j := link idx i
    decide (j < idx) && (get j).signed == r.signed && (get j).mask == next r.mask i &&
      (get j).k == budget r.k (tg r.tags i)
end Cert.Compact

namespace Cache
open PEqualNP.Outside.L_meta_2309_aux.Main2331
structure Table where
  count : Nat → Nat → Nat
  locate : Nat → Nat → List Wire → Nat
  state : Nat → Nat → Nat → List Wire
def hit (D : Table) (k t : Nat) (w : List Wire) :=
  if D.count k t = 0 then false else
    match D.locate k t w with
    | 0 => false
    | n+1 => Nat.blt n (D.count k t) && isPermFast w (D.state k t n)
theorem hit_sound (D : Table) {k t : Nat} {w : List Wire}
    (all : ∀ i<D.count k t, Impossible k t (D.state k t i))
    (h : hit D k t w = true) : Impossible k t w := by
  unfold hit at h
  split at h
  · contradiction
  · cases e : D.locate k t w with
    | zero => simp [e] at h
    | succ i =>
      simp only [e,Bool.and_eq_true,Nat.blt_eq] at h
      exact perm_impossible (isPermFast_perm h.2) (all _ h.1)

def run (D : Table) : Nat → Nat → List Wire → Bool
  | 0,t,w => search 0 t w
  | k+1,t,w => stepTest k t w
      (fun u => !hit D k (t-1) u && run D k (t-1) u)
      (fun u => !hit D k t u && run D k t u)

theorem run_sound (D : Table) (k t : Nat) (w : List Wire)
    (below : ∀ j<k, ∀ u≤t, ∀ i<D.count j u, Impossible j u (D.state j u i))
    (h : run D k t w = false) : Impossible k t w := by
  induction k generalizing t w with
  | zero => exact exclude_search h
  | succ k ih =>
    have one (u : Nat) (hu : u ≤ t) (v : List Wire)
        (vok : (!hit D k u v && run D k u v) = false) : Impossible k u v := by
      cases e : hit D k u v
      · apply ih u v (fun j hj r hr => below j (by omega) r (by omega))
        simpa [e] using vok
      · exact hit_sound D (below k (by omega) u hu) e
    exact exclude_step (one _ (by omega)) (one _ (by omega)) h

def cells (D : Table) (k t : Nat) :=
  span (fun i => !run D k t (D.state k t i)) (D.count k t) 0

theorem usable (D : Table) (cap fuel : Nat) (checks : ∀ k<cap, ∀ t≤fuel, cells D k t=true) :
    ∀ k<cap, ∀ t≤fuel, ∀ i<D.count k t, Impossible k t (D.state k t i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk t ht i hi
    apply run_sound D k t _
    · intro j hj u hu
      exact ih j hj (by omega) u (by omega)
    · have v := span_ok (checks k hk t ht) i (Nat.zero_le _) (by simpa using hi)
      simpa using v
end Cache

namespace P16
open PEqualNP.Outside.L_meta_2309_aux.Cache PEqualNP.Outside.L_meta_2309_aux.Main2331
def field (x bits i : Nat) := (x >>> (bits*i)) &&& (2^bits-1)
def recipeDataS : Nat := 0xac6200000ac9600ccc9632000ba2b93000bb62a3000ba3b92000ba6b9200000ca62000ba6b93000bb62a9000bb63a900000ac6300000ac9200000ac9300000ab6200000ab9200000ab6300000ab930000cc6320000cc9320000cc9620000cc9630000000a90000000a20000000a30000000a60000bc3260000bc9620000bc3290000bc96300000ca2600000ca2900000ca3600000ca3900000ca6300000ca9200000ca93000000c3200000ca2300000ca3200000ca6900000ca9600000ba2600000ba2900000ba3600000ba3900000ba6200000ba6300000ba9200000ba93000000b62000000b63000000b92000000b930000cb6230000cb6290000cb9320000cb936000000c96bcb962c63bc62cb963bc93cb962bc92cb96300bcb639200bcb629300bcb936200bcb926300bcb632900b9cb6230bbac96320bb96ac3200cbc923100cbc632400cbc623700bcb327900bcb328600cbc932800cbc629800cbc936700cbc639100bcb967200bcb9683000acc632000acc932000acc962000acc96300cbb632900cbb932600cbb963200cbb96230000cb6320000cb9230000cb9260000cb9280000cb6370000cb639000bab326000bab329000bab962000bab96300000ba2300000ba3200000ba6900000ba9600cb96b320000cb6240000cb931000bac326000bac329000bac962000bac96300bcb329600bcb326900bcb963200bcb96230000bc6230000bc6290000bc6320000bc6390000bc9230000bc9260000bc9320000bc93600000ab3200000ab960000cb9610000cb9640000cb9670000cb9680000cb3210000cb3240000cb3270000cb3280000cb9620000cb9630000cb3290000cb32600bbc639200bb63c9200bc62b9300bbc936200bbc963200bb96c32000000b32000000b96000bb96a2000bb96a3000ba6b32000ba9b320000bb9320000bb6320000bb9620000bb96300ccb928200bcb928600ccb967600bcb637200ccb968900bcb928300ccb637300bcb637900bcb321200ccb321900bcb324300ccb324600bcb327200ccb327600bcb328300ccb3289000000c6200ccb968200bcb9686000000003000000c9200ccb964200bcb9649000000007000000009000000c6300ccb961300bcb9616000000008000000004000000002000000001000000006000000c9300ccb967300bcb9679
def source (i : Fin 9) := (PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.proj 16).fn (raw.getD i.val zero)
def wire (j : Nat) : Wire := ((recipeRun source 9 (field recipeDataS 36 (j/4)) []).headD zero,tagOfNat (j%4))
def decode (x : Nat) : Nat → List Wire
  | 0 => []
  | n+1 => wire (x &&& 1023) :: decode (x >>> 10) n
def rawPart (x : Nat) := (List.finRange 9).filterMap fun i => let q := field x 3 i.val; if q=0 then none else some (source i,tagOfNat (q-1))
def atState (data size i : Nat) := let q := field data size i; decode (q >>> 31) ((q >>> 27) &&& 15) ++ rawPart q
def locateIn (shifts slots B M sbits ibits : Nat) (v : List Wire) :=
  let h := frontierHash 0 v
  let d := field shifts sbits (h%B)
  let z := field slots (ibits+4) ((h/B+d)%M)
  if z >>> ibits = h%13+1 then z &&& (2^ibits-1) else 0
def a7_0 : Nat := 0x98461106430190e61084019600643f83c0106032182fa0e0041860860bd83407861b2190320c014196c000bb82c0986580190ea0a004180c860b98240886430190de0701a186c8043501204065b018204008001860860b
def d7_0 : Nat := 0x28
def h7_0 : Nat := 0x95009321270000d4ab003c0000d64a3829a2
def a8_0 : Nat := 0x102096c864b0000100096c864b00000fe096c864b00000fc096c864b00000fa096c864b00000f8096c864b00000f6096c864b00000f4096c864b00000f2096c864b00000f0096c864bb016876196c8608b0168721960860bae16874196c8043ae16870190c8643ac1607e186c8648ac16078180c864baa1607c196c004baa1607a1960064b821d874196c8048821d870190c8648821d0721960804b821c8701900864b00000ee096c864b00000ec096c864b001d848116c864800168ea116c8648001d04a116c804b00168e8116c804b001307c116c804b001307a1160864b001a066116c064b00168e61160864b000b8e41160864b001c8481160864b000a8e2110c864b001c04a110c864b00168e0110c864b001387e116c86480013878110c864b001a864106c864b00160de110c864b000f044110c864b001b066116c860b001b864116c864300100381160864b00160dc1160864b00160da116c864800000d81160864b00088d6110c864b00168c4116c864300168c2116c860b00160c0116c064b4e308be190c860b4a300be190c064bbc120ba1860864b002e858106c864b00000d4096c864b00000d2096c864b00000d0096c864b00000ce096c864b003305a106c864b00168ca116c064b00160c8116c864300160c6116c860b001306e116c8643001306c116c860b001a062116c064b001a04a116c064b001a048116c064b001386e116c8643001386c116c860b001a860106c864b001a84a106c864b001a848106c864b001b060116c860b001b862116c8643001506c116c860b0014868116c064b001406a106c864b001a0a8116c064b001a8a8106c864b002a06e116c8643002a06c116c860b001d84c116c8648001d04e116c804b0013070110c864b001c84e1160864b001287e116c8648001287a1160864b001207c116c804b0012078110c864b001d04c116c804b00130c4116c864300130bc1160864b00130721160864b001306a106c864b001a04e116c064b001c04e110c864b00138c2116c860b00138be110c864b00128c0116c064b00128be110c864b001286c116c860b001287c116c804b0012878110c864b002f0481160864b001207e116c8648001206e116c8643001207a1160864b00120ba106c864b0013068116c064b001386a106c864b001286e116c8643001206c116c860b002e05a116c064b002d85a106c864b002d058116c8643002c858116c860b002c05a116c860b002b85a116c8643002b058106c864b002a858116c064b00130a6116c804b00000a8096c864b00138a4116c8648002984a116c804b00120a4116c8648001a058116c064b001686e116c8643001686c116c860b001a858106c864b00000a2096c864b00000a0096c864b000009e096c864b000009c096c864b000009a096c864b0000098096c864b0000096096c864b0000094096c864b0000092096c864b0000090096c864b000008e096c864b000008c096c864b000008a096c864b0000088096c864b0000086096c864b0000084096c864b0000082096c864b0000080096c864b001607e116c8648001607c116c804b001607a1160864b0016078110c864b001d85a116c8648001d05a116c804b00168721160864b0016870110c864b001606e116c8643001606c116c860b001686a106c864b001a05a116c064b0000066096c864b0000064096c864b0000062096c864b0000060096c864b000005e096c864b000005c096c864b000005a096c864b0000058096c864b0000056096c864b0000054096c864b0000052096c864b0000050096c864b000004e096c864b000004c096c864b000004a096c864b0000048096c864b
def d8_0 : Nat := 0x1031c00000480420800001400000450061c20400023850801c50414420000430000030890c5b460000010810000090001c20100001003400030c30c10c314c000044
def h8_0 : Nat := 0x6a17700002337a5131a4a2424a41161522079815147980000002498971a884662b88f54713d19d58eb9c5776b0730000000000b13a39a7d000d0852fc281401a6112000000868000621000b6300079500000000000051f00087900000000055618727c0005a20007ad350b01d3400000025c000000000000967000462b1b96c46fa3800072d76e4ab124a86b2568c98547ec83517b10974b7343bc6460bb5565755e21500026b00077a72c000a37b654aa148a44aaf00040c91c6acb22a8a00000000058d55144300036a145d4cb20b03518c04572b80c89190c9994d606d0fda033f59f60d37f89ba1eb0a459209b84d1d875329d7b832aa929e1603b1223166411c3c44178bd5d805b6d15a5a782e00000000000097600075f000b4e888154000a4b00000016100000000019446989a727000a19b93d2617852a000000935a9200043663a15325b38217100040ec96702991000b4f7584a33ae43e51a000000000000
def a8_1 : Nat := 0x988604c32d80c07290a09861b0190e61880a0cb60301c82e814186c060b9c8400830d90c07210601061b0182e50dc820c360321c81b104186c060b
def d8_1 : Nat := 0x710
def h8_1 : Nat := 0x662483d70081b2380000b500
def a9_0 : Nat := 0xd08808b603258006a44841b2192c00a021c22d90c960045142116c864b001248808b643258009044845b2192c00880d822d90c16004393e116c864b002244308b64325801121b845b2190c002604c22d90c960013014116c864b000980f08b643258004c01045b2192c00260d420d90c96001a04e116c064b340b4350c3603258004e07845b2192c002700822d90c960013826116c864b0009c0a08b643258004a07845b2192c002500822d90c960012826116c864b000940a08b643258002612045b2192c004511022d90c960007848116c864b000900208b643258004805045b2192c004711822d90c960029004116c8648000943608b643058006e12045b2190cdc2c0d832d90c06004b05a116c864b002942608b643258014a12845b2192c00a409822d90c96005204e116c864b002902408b643258012816045b2192c00a309822d90c96005184a116c864b0028c2408b643258014c13845b2192c00a609422d90c960053048116c864b000e82608b640258007413845b2012c00260e422c10c960013070110c864b000e42708b04325800700984432192c003809c22190c96002984a116c804b0004c3d08b043258004e2f84432192c002517c22190c9600130bc1160864b001782408b04325800a413845b21920005209022d90c900001078110c864b000fc2508b643240007e12045b2192000250f822d90096001287a1160864b000943c08864325800481f045b2012c00240f422c10c960012078110c864b00000b904b643258012445045b0192c009e0b422d90c960048910106c864ba50b4970cb64305800005c025b2192c00002dc12d90c960048112116c064b0023c87083643258013616845b2192e902d25c32d90c86000016c096c864b002388a08b643218016a16045b2192c00002d012d90c960046912116c860ba30b0820c3643258000059825b2192c008c22022d90c860000164096c864b002602c08b64325d305841065b0192c002d2c022d90c960016962116c864b002c02c08b643258015e16045b2192c003b22822d90c90001d10e116c804b000e48a08b04325800724384582192c003822822190c96001c10e110c864b002285e08b04325801141f845b21920008a0f422c10c960045078110c864b0017c8708864325800bc4384582192c00870f822d90096004387a1160864b002482d08b643258012216845b2192c008f0b422d90c960047058116c864b002342c08b643258011816045b2192c008b0b022d90c965a440be190c864b2d2245e0cb043258011429045b21920005f22422190c97102f858190c864b002205e08b043258011023845b2192c008811822d90c960022912116c864b001108908b64325c48bc1606582192c002c27c22d90c96004e85a116c864b002702d08b643258013216045b2192cb43b22832d90c905a1d90e196c86482d0e88a0cb640259687443865b2012cb43421c32d80c965a1a114196c064b2d0e48a0cb04325968724386582192cb43822832190c965a1c10e190c864b2d0d48a0c3643259686a43861b2192e282c0dc32d90c87141607e196c86488a0b03e0cb64025c50581e86582192e1c2c0d832d90c170e1607e196c8648870b0370cb64321c38581f065b2012e1c2c0f432c10c967616868196c06483b0b4350c3643241d05a1a065b0012ce82d0d430d9009668168721960064b340b4380c8603259686841065b0192ce42d0d430c10c96701686a180c864b2d0d4820c3643258000043025b2192c000021012d90c972e1606e196c8643970b0360cb643059f8581b865b21900fc2c0d832d90c106e1607c196c8043370b03c0c8643219b0581e86582182cd82c0f032190c16001695c116c864b000b4ac08b643258005a55845b2192c00ae0b022d90c960056858116c864b002b02c08b643258015616045b2192c003b22422d90c90001d110116c804b000e88908b64025800724404582192c002d2a822d90c960016952116c864b000b4a808b643258015416045b2192c00a90b022d90c960029910116c804b0014c8908b640258015016045b2192c008814822d90c90004407e116c8648002203e08b64025801101e84582192c008914822d90c90004487e116c8648002243e08b64025801121e04432192c00a70b022d90c96000014a096c864b00000a404b643258000051825b2192c000029812d90c965a4b826196c86432d25c020cb643058011423845b2192c008810c22d90c960044892116c864b0021c4508b643258011422045b2192c004822022d90c962616104196c064b001188708b643258105841061b2192c00a50b422d90c96005205a116c864b0028c2c08b64325800681a841b0192c00370d822d90c060049058116c864b002442c08b643258011e16045b2192c008e0b422d90c96004685a116c864b002302d08b643258011616845b2192c000028812d90c960000142096c864b00000a004b64325800004f825b2192cec2d0e432c10c907616870190c86483a0b4390cb040259d05a1c06432012ce42d0e032010c960024890116c864b0009c6108b64305800c22f84432192c002518022d80c9600300be110c864b001885e08b04325800bc2e84582192c002417420d90c960021884116c864b3f0b03e0cb640241f8581e865821920fc2c0f032190c907c1607a1960804b3e0b03c0c8640259e8581e06402192c00260d022d80c96001386a106c864b000943708b64321800481b045b2182c00410ec22d90c900020874116c804b001043908b04325800821c04432192c00400fc22d90c90002007c116c804b001003d08b04325800801e04432192c00340d422d80c965a1a112196c064b2d0e4890cb04325968704406432192cb43522030d90c965a09814196c064b2d03c020c3643258981e16065b2190e202c0dc32d90c871016078190c864b890b0360cb64305c48581e86582192c28020b032d90c16001b86c116c86430004c5f08864325800262f04582192c005f00822190c96002f0041160864b001042608b643258008213845b2192c004009422d90c960020048116c864b000ec0f08b643240007405045b2012c000f0f822d90096000507e116c86482d0ec880cb643241687644865b21920b43a22032d900965a1d112196c804b2d0d0880cb60325968724406582192c003800822190c965a1c112190c864b2d0d4890c364325800261e04432192e202c0fc32d90c91101606c196c860b880b03e0cb64025c40581e86582192e242c0fc32d90c91121606e196c8643890b03e0cb64025c48581e06432192c00020f422c10c960020858116c864b000b44008b64325800681c84582192c00380d422190c96001b878110c864b000d83d08b04325800681a845b2192c00370d822d90c96001d86a116c8648000e83408b640258000031025b2192c000018412d90c9600000c0096c864b000005d04b643258007e1b045b2192000370f822d90096000013c096c864b000009d04b64325800004e025b2192c000026c12d90c960000134096c864b000009904b64325800004c025b2192c002d11022d90c96001688c116c864b001142c08b643258008e16045b2192cb41303c32d90c865a05004196c860b130282c0cb603258780416061b2192c002d18422d90c160030058116c064b3b0b4260cb643241d85a13865b21920e82d09832d90096741684e196c804b260b4390cb043259305a1c06432192c982d0d430d90c96681684e196c064b390b4270cb043259c05a1386432192cfc2c09432d90c907e16048196c8648250b0360cb64305928581f065b2012c942c0f432c10c964a16078190c864b370b0240cb64321920581f065b2012c902c0f432c10c964816078190c864b000d00a08b603258001e1b845b2190c000a0d822d90c1600000b0096c864b000005704b64325800002b025b2192c000015412d90c96001a0721160064b000e035080643258006e1e04432190c00360f422c10c16002085a116c864b001002c08b64325800761a045b01920003b0d420d90c90001d068116c004b000e83508364025800681c04430192c00390d420c10c96001f86e116c8640000fc3608b643040006e1f045b2010c00370f422c10c86001b07c116c800b000d83c088643058006809845b0192c000011c12d90c960000092096c864b000d402083643258000021825b2192c000011412d90c960016890116c864b000b44208b643258000022025b2192c00490b022d90c96000986e116c8643000004804b643258000021025b2192c00020d822d90c16000008c096c864b0010c2c08b64325a085a1a065b0192d042d0d430d90c96801606e196c8643400b0360cb64305800761a045b21920003a0d422d90096001a070110c864b000e43508b043258007e1b845b2192000370f422c10c96001b07c116c804b000d83c08864325800004b825b2192c000020812d90c964c16868196c064b270b4350c364325928581b865b2190c902c0d832d90c16001a058116c064b000d42c083643258005a1b845b2190c002d0d822d90c160000068096c064b000003704b64321800001a821b2192c00000d812d90c16001c81e1160864b000e00a08864325800a601045b2012c001314822d90c90000787a1160864b000283c088643258004c44045b2192c002621c22d90c960013914116c864b0009c8908b643258004a43845b2192c002522422d90c960045048116c864b002202408b64325800be0504432192c000f17822c10c96001d826116c8648000e80208b640258005a29845b2012c002d17c22190c9600168bc1160864b000b45208b64324000a616045b2012c00130fc22d90c90002f858110c864b001782c08b04325800a416045b2192000020f822d900968216876196c8648410b43a0cb64025a085a1c86582192d042d0e032190c96801607e196c8648400b03e0cb64025a00581e86582192d002c0f032190c96001d858116c8648000e82c08b640258004c45045b2192c00390b022c10c96001c058110c864b0009c8708b643258000013025b2192c000009c12d90c96001687e116c8648000b43e08b640258005a1e84582192c002d0f022190c960012914116c864b000002504b643258004843845b2192c000009012d90c96000012c096c864b000009504b64325800004a025b2192c000024c12d90c960000068096c864b000003504b64325800001b025b2192c002609c22d90c96001304a116c864b0009c2508b643258004c12045b2192c002709022d90c960012848116c864b000009204b643258000048825b2192c000024012d90c96000011e096c864b000008e04b643258000046825b2192c000023012d90c960000116096c864b000ec3808864324000741c84582012c003f0f422c10c90001f078110c804b000ec3908b04324000741c04432012c003f0f022190c90001f07a1160804b000ec3a08b64024000721c04402192c003f0f822d90090001e8781100864b2d0d02c0cb603259686a16061b2192cb42c0dc32d90c865a1606c196c860b2d0ec2c0cb643241687416065b2012cb4390b032c10c965a1c058190c864b2d0b03f0cb64324168581f065b2012cb42c0f432c10c965a16078190c864b001602d08b64305800ae16845b2190c00560b020d90c96002a858116c064b000988908b643258004e44045b2192c002522022d90c960012112116c864b000002b04b643258000015025b2192c00000a412d90c960000050096c864b000002f04b643258000017025b2192c00000c012d90c960000062096c864b000003304b643258000019025b2192c002d11c22d90c96001688a116c864b000b04408b643258008c16045b2192c000004c12d90c960000014096c864b000000f04b643258000001025b2192c002d12422d90c960016886116c864b001202c08b643258005821045b2192c000022812d90c960000112096c864b000008804b643258000043825b2192c00260b022d90c960013858116c864b000b42508b643258005a12045b2192c00260b422d90c96001385a116c864b000942c08b643258004816045b2192c00000b412d90c960000058096c864b
def d9_0 : Nat := 0x4618000028000a1400422000000c00000400c004400000438020000600200008400200408210a0410000042c51040010c000004008008000010600e1800820420850c000d0110250c00432000841c300200700300300300b0453000000020431c00021401400430400000000050402c01010000010410000011c20000002815410040061120800010d80410c028104300900008218010100104b04000200005c18000504520408408000208000000008301d00024504000101300400108000014304002d1400072003470c00001430470c2003040040
def h9_0 : Nat := 0x25e200018df00000000000000746400021c0000000000000004aa000119a0001d36000242ed06d57c14b9474433102013ff41563e400000030f298ee4e2000154e00021f182200000000000b8e492f2581df742f555d84cc000d4b000000015bc3174000965ad4cc7a800000035848320000a240000d4400000000000b87d104a8dc8cf531c0000000000000110947e40000000000a74d14d1444000863c477000000000004b6b300d760000000303849357ec40b0002c5100000005252dd1886c0004456085c0fec5a130f40fc7c00000000d78a71400000019f55068e2157098652678000313a8291060ddf0000cce000000000000008286437a76ac630000000c16d810476cd4f201c00091a29bd95c0974b1ad587d57982ba3fa83131480000000000488e1021856582c1cecfc15e40006078000b4e800028bc0000001c9d00000004889882282356170305b6d817433223400048ca4fbc09e44757bb1c7b5aa928479800000004750002dd700005a74395c9200000000000000d5d71a2d342d26000304955111dc14ee49e652d8dcb21104063b180d0003559934a547939000018380000000573654d4f7a8d34b500024da65010e826de12560f74eac25cdca35700000002c53d24480422a581f00025eb854989c779501d20bd62da35508b82d199554600000000ce60000000000358644740000000000000000055ecc48542ecc263b6a36d809a0f5665142608a512410880148c4988d82d8b79376059d7800007719cba73eac9a0003044445d8a84155c09000296b000000026295b2c1f1e11a7e8000247c000000143900008890000000b737219285c83c449ca1d4151c8167b2da100004c5000000097cc45f677663091a4000141ac460000000c65000078f00005360000719e8c93810000b28c87e000102c5219d6f27d2e13801a84c46ec55425c59e4000000000000000000000d0d084f0000479d8505210002cfd279e071862506c85b19d8173000016fcd2300018500000000826ec8c00000000000000000000093c66330001de9d85a0cdd31859174e2c80589800000000000000000000000086be9b0a23f1560001e25278d84552ac51b439c0000001da8000093d182a54521b4000b4af63553cec870002981568d8afa1ee0f4831000000008f6a048e06a0948d3b2b1d6e92c261ec64cc6a000189800014e0000000034d31d50002564a60c00096e187f95280000000000a3b8000736cd72a0a30d6d6409ab583520717058f827648b197fe82a36b583036955a9162f55ad6c6c1c66921a093ae021144c00090d8000266d13ed0934d925968e181e357d9544cd427f9cbea4884a770b6d0c6749803208ee03789288a66ce83a0002cb2d8e209913472278561d1ed2ef12417db57f774250e80ef530a1e9cf026f9ce9d77ac41b2905fc812d80ab10e11a7170955675113cc5a51cf35b6c4a564b168a421566148081971c9d9d88689f888e91ce718060044521850001466c4aa9e8c8a3162000198e0000000b5ea929000352d820ee1000031cb740c000b02000000011c8a57c950815a43ea5dc601c69b062c45944d20d4000756e10ab2fe43234c54efc051ca0b2cee12a2b6496000294648ad461b29506f1601a18c52217e18b05bab00b458b04ed8c71d98b9941e9c0355f0f582b985e130696315059fdd19099c3014811d058e2a775a095d7b49670002817b63610f5526a1c56e400058a591c00029ac000000018b850000021371098c57000159f37cb198c32adc9627edaeb29a6205434000c0e05aaa4c800042f00006784000d70c00094d40002825c7dc50e8e3b4e65ef000288e000306e7404000000150553785b4d7124cb00014b866d54d70000000d65c000583353f00014a2
def a9_1 : Nat := 0xbc12d90c96000005c096c864b3f0b0370cb643201f8581e064321920dc2c0f432c10c866c16078190c860b3e0b03d0cb040258014a16845b2190c00a40b422d90c160051858116c064b002982c083643259608041061b0192cfc2c0f832d900907e1607a196086483e0b03c0c8640259e8581e06402192e942c0fc32d90c814a1606c196c8603a50b03d0cb04321d20581f065b2002e902c0f032190c174a16078190c8643a40b03f0cb64304520581e86582182c00950b422d90c16004a058116c064b0024c2c083643259691409865b0190cb48700830d90c171409858196c0643870082c0c3643059607e41061b01920b03720830d80c86581f104186c004b2c0f4820c300325960784106030192c00a50ac22d90c860052054116c860b0028c2908b603258014c14041b2192c002c2ec20d80c974a16104186c0643a40b0820c360305800005d025b2192c000022812d90c960000112096c864b000008704b643258000007825b2192c000022012d90c960000104096c864b002942408b643218014812845b2182c00a309c22d80c96005304c106c864b002942608b643218014813045b2182c00a409c22d90c16005184a116c064b0028c2408b603258014c12841b2192c00a609020d90c960000026096c864b000000a04b643258000001025b2192c00a509422d90c860052048116c860b0028c2608b603258014c13841b2192c00000b412d90c960000058096c864b
def d9_1 : Nat := 0x52010131021020811000029111123010040
def h9_1 : Nat := 0x1a18000000018cc00000b2a000005b472c00312210000aa344603000c8ad4d3fb048d702c1d13090c006392762b609b190000035b80063d0da50b2f83f85e538009624480038468348e57000b7a6715f000b1546c808003340000000071691800142000000d8000d1ca945500051e8c89e591d13898003451192b15d214000eaec3d0d180ce090644
def a9_2 : Nat := 0x1f87c116c8048003e0f022190096007a1e04402192ec0dc820c360321d81b104186c060bb03f20830d80c91607c41061b0012ec0f4820c300325d81e104180c064b
def d9_2 : Nat := 0x0
def h9_2 : Nat := 0xa10053c20000a9b800570000c6559400
def a10_0 : Nat := 0x12e41045b2192e5c8808b64325cb912116c864b8820822d90c971241045b2192e948208b64325d2104116c864ba325c22d90c974c4b845b2192e5c8a08b64325c5104116c864b8720822d90c972e07845b2192e5c0a08b6432587904116c864b0a20822d90c974a51845b2192e94a608b64325d2146116c864ba429822d90c974a4b845b2192e909708b64325d1904116c864ba620822d90c962601045b2192e280f08b64325c5014116c864b0a21c22d90c972e09845b2192e5c0208b6432589904116c864b0220822d90c974a05045b2192e900f08b64325d181e116c864ba602822d90c974a01045b2192e901308b64325d1804116c864ba604c22d90c971007845b2192e240a08b64325d2948116c864ba329822d90c962644045b2192c4c8908b64325c4004116c864b8900822d90c974a44845b2192e948708b64325d2110116c864ba322022d90c974643845b2192e988a08b64325d3112116c864b8a04c22d90c970e01045b2192e941308b64325d281e116c864ba402822d90c974605045b2192e980f08b64325d3004116c864b002a812d90c960054825b2192c00a804b643258014e096c864ba522822d90c974843845b2192e8c8a08b64325d2910116c864ba322422d90c974c44045b2192c4c0f08b6432589814116c864b0f00822d90c961401045b2192c4c0f08b6432189814116c064b0f00820d90c961401045b2182e288708b64325c4112116c864b8a14c22d900970e29045b2192000ae04b643258015a096c864b002b012d90c960055825b2192c009504b6432580128096c864b0024c12d90c96001a025b0192c0035043643258006e096c8643000d812d90c165a4b845b2192cb08208b6432580140096c864b0028412d90c96004f825b2192c006104b64325800c0096c864b0018812d90c96002e825b2192c00b004b6432580162096c864b002f012d90c960057825b2192e280208b643258990e116c864b8a09422d90c970e13845b2192e1c2408b64325c5110116c864b8a22422d90c971043845b2192e205f08864325c48bc1160864b8802822d90c961e44845b2192c009204b643258011e096c864b0023812d90c960045825b2192c009104b6432580120096c864b0023412d90c960046025b2192cb40f08b6432587858116c864b0a0b022d90c960020825b2192c004004b6432596904116c864b970b022d90c974a16845b2192e902d08b64325d1858116c864ba60b022d90c971013845b2192e202508b64325c484c116c864b8909022d90c965a09845b2192cb40208b6432589858116c864b020b022d90c96001a025b2192c003504b643258006e096c864b000d812d90c974a16045b2192e902c08b64325d185a116c864b0011412d90c960022025b2192c004704b643258008c096c864b0012412d90c960024025b2192c004304b6432580084096c864b0014c12d900960029025b21920b43408b603259686a106c864b2c0dc22d90c86581b045b2182c003b04b6432400074096c804b000fc12d90c90001f025b2012c000000b6432596914116c864b2d21c22d90c971416045b2192e1c2c08b64325800720960864b000e012190c96001e82582192c003c0486432596868116c864b2d0d422d90c96581b845b2192cb03608b64325800be090c864b0017812c10c965a44045b2192cb48908b64325c4058116c864b890b022d90c965a20845b2192cb04008b643259684c116c864b2d09c22d90c965812845b2192cb02408b64325968721160864b2d0e022190c96581e84582192cb03c0886432596876116c86482d0e822d90096581f845b21920b03e08b640258004c096c864b0009c12d90c960012825b2192c002404b6432596858116c864b
def d10_0 : Nat := 0x138803100220900609d60000a0284020140000c000000700020000003bc0310143002a004960884497b80200020000c028006000020008338040284c00980410002
def h10_0 : Nat := 0xd34129000a7b11400000096a00000058a6af00018b00024826085075cb20a1fb058788cbc9b77c249c6239eb53c59b02d4a1c69b938e7cd619d7719f146b2b20f0000000008cc00000000000000060ecab3647b04bb95d136681a75954d63d5150bb32443c4bc04bb56ce66b98546812a640000000128000dd152481c1ba7a0cc8a5a66d7666c7856000000cb617100069d000000000caa00068c10d000113c96595c3d4a9d7a000000000b877a826952c000cb1000a8f907327d97358630726b17ba5c015d0b3c67257f37965e00042f00000089a000000000d257c9a45000573cd371baa445ba4421e12d165b909a2000000000000c473885bc000b0611d5942ae43ebc443a61ab395bd531000bad00000000077e00066f280abe000000000508000000000a0a3c0d4ea2100033bb38acf28d841d7da4f43f1b720c9b431699c9989529229a1a183c585f9bfb2376e637242a742911a300049200042e000984000a822c32352c27ac4ca8120008b3000d89000000000a7600000000096c0006571b8000000310000215da7b331b2386270383967509000000d938110000003619c1d99b550008d224d94c703ca6
def a10_1 : Nat := 0x5205a116c864ba325c22d80c974c4b841b2192e94a608364321d2146116c060ba30b022d90c974c16045b2192cb49708b64325d2946116c0643a429820d90c172e07845b2192e5c1308b64325cb814116c864b9700822d90c961e41045b2192e900f08b64325d181e116c864ba529822d90c962641045b2192c288208b6432581104116c864ba529022d90c971205045b0192e240a08b64305d2814116c864ba500822d90c974809845b2192e908808b64325d1910116c864ba300822d90c974c09845b2192e980a08b64325c5026116c064b8a04c22d90c871443845b2192c4c0f08b6432587804116c864b8700820d90c970e01045b2182e949708b64321d2912116c864ba521c22d90c97484b845b2182e8c8208b60325d190e116c864ba620820d90c974c45045b2192e988908b6432589814116c864b0a00822d90c962601045b2192e8ca608b6432587912116c864ba529022d90c074653041b0192e200a08b64325d2946116c864ba428c22d90c974853045b2192e948208b64321d2104116c860ba403c22d90c174607845b0192e901308b64305d1804116c064ba30b422d90c974a16045b2192e902c08b64325c5004116c864b1321c22d90c974a05045b2190e940208b64321d3026106c864ba528c22d90c874a53045b2190e94a308b60325d294c106c864ba428c22d90c174853045b2182e90a308b60325d214c106c864b8a22022d90c971043845b2192e94a408b64321d2948116c860ba329822d80c974653041b2192cb08208b643259681e116c864b970b022d90c961e16045b2192e288908b64325c4814116c060b2d25c22d90c874844045b2182e8c8808b60325d2912116c8643a521c22d90c874845045b2182e8c8708b60325d3114106c864ba622420d90c965a4b845b2182e281308b603218981e116c86430f00820d90c970e01041b2182e900208b64305d1826116c064b2d20822d90c962605045b0192c280208b64305d2826116c8643a503c22d90c874805045b2182e8c0a08b60325d3004106c864b2c20820d90c965841045b0192c282c08b6432596826116c864b2d00822d90c962616045b2192c082c08b64325d2914116c8643a522022d90c874844845b2182e908708b64305d1914116c064ba322422d80c974c44041b2192e98870836432580154096c864b002a412d90c960054025b2192c00a704b6432596910116c864b880b022d90c965a44845b2192cb48a08b643259690e116c864b890b022d90c971416045b2192e1c2c08b643258007e096c8648000f012190c96001f025b2012c004004b6432596858116c864b2c09422d90c965812045b2192cb0820836032596868116c064b2d0d420d90c974616845b0192e982d08364325d285a116c8643a40b422d90c174616045b0192e982c0836432580000016c864ba50b022d90c874816045b2182cb43b08b6432416874116c804b2d0e422c10c965a1c04432192c002604b643258004e096c864b0009412d90c960012025b2192cb03708b643219606c116c860b2c0fc22d90c90581f045b2012cb03d08b0432596078110c864b
def d10_1 : Nat := 0x8c80080220100298805184c10888400142084410000300c02180c00006000080383440984010020000420000731800081541042808825
def h10_1 : Nat := 0xd2661b97858444bb290007936a70000002a0b0764c00000099d000476000a7b2120006740002ac00000000000017155150db70b169a963611038300093b36094800000034d238b9e33ea15265935000b032796410004b000031f1a2c7520b22a69879095892244e83a000d33000000d690005aa52576d00047fd674ad90f1a616c000d81d34000000000000c0998851489900050e3a342b172000d1e48b47d79572f77ea8f21adae95d792873904d6841985fd5777ac6246e342b0a21c000c9146a121a4f863db195985300000058e70800012475b75535449c0000008af000b3d000000000000b9400078a447ca418666b65ab807500008a818937786477c244230000297711000c4612eb13b9f29bd2c185287506327256b05717b23a011a563cc1da4a52d345000502000837000ca113f00034999636fb6622023243900000025e38d10cb40000000000682000000000b9ac31a5c2aba5258c000000228000000961118943
def a10_2 : Nat := 0x52914116c8643a422422d90c174843845b2182e8c8a08b60325d310e106c864ba502822d90c874a01045b2190e901308b64305d1804116c064ba604c20d90c960055025b2192c00a904b6432580150096c864b0029c12d90c965a4b845b2182cb49708b6432196104106c864b2c20822d80c974a44845b2190e948708b64321d2114116c860ba321c22d80c974c45041b2192e988908364325c5026116c06438902822d80c170e01041b2182c4c0f08b6432187804106c864b1302822d80c961401045b2182c000000b64325d285a116c8643a40b422d90c174616845b0192e982d08364325d1858116c064ba60b020d90c974a16045b2190e902c08b643059607e116c86482c0f822d90096581e84582192cb03c088643258004c096c864b0009c12d90c960012825b2192c002404b6432596104106c064b
def d10_2 : Nat := 0x2092018023010e0090129840100000
def h10_2 : Nat := 0x12366800da1c3955472bc006b125b168659e91dc04b1b46929299a75179825477b66762cd359cf2048cb3ac2b20e20011c00304001d2001a11a8000000092671cb80057c0000000000db000004ac0034c0092950
def a10_3 : Nat := 0x5841041b0192e94a408b64301d2946116c0643a529820d90c874851845b0182e90a608364305d194c106c064b8a04c22d80c871205045b0182e1c020836430580000016c864b
def d10_3 : Nat := 0x290
def h10_3 : Nat := 0x2b47d87aa442860000000071997300a5
def a11_0 : Nat := 0x41025b2192c3c12d90c9614096c864ba504b64325d2025b2192e8c12d90c974c096c864b1304b6432581025b2192e2812d90c970e096c864b8804b64325c4825b2192cb412d90c9658096c864b
def d11_0 : Nat := 0x2a39
def h11_0 : Nat := 0xbf006300367ab7ce79742c00d89bdd00210015b20000
def a11_1 : Nat := 0x51825b0192e9810d90c9748096c860ba504b64321c1025b2192e9412d90c9748096c864ba604b64325d1825b2192c3c12d90c9614096c864b1304b6432581025b2192e2012d90c9712096c864b8a04b64325c3825b2192cb412d90c9658096c864b
def d11_1 : Nat := 0x822030070
def h11_1 : Nat := 0x18b6739bcac5a8323b3604e96ea400ebb788dcd11000031400208000000
def a11_2 : Nat := 0x52825b2192e9812d90c9748096c864ba304b6432587825b2192e8c12d80c9748096c860ba60436432589825b2192c0812d90c974a096c86438204b6432585025b2192e2012d90c9714096c864b8904b64325c3825b2192cb412d90c9658096c864b
def d11_2 : Nat := 0x822030070
def h11_2 : Nat := 0x1896a373b2c5ab32bcb525398e9c00f0b408dcd0d000031e00208000000
def a11_3 : Nat := 0x2d04b64325d8096c864b
def d11_3 : Nat := 0x0
def h11_3 : Nat := 0xb89
def count : Nat → Nat → Nat
  | 7,0 => 12
  | 8,0 => 177
  | 8,1 => 8
  | 9,0 => 572
  | 9,1 => 70
  | 9,2 => 9
  | 10,0 => 211
  | 10,1 => 177
  | 10,2 => 49
  | 10,3 => 11
  | 11,0 => 15
  | 11,1 => 19
  | 11,2 => 19
  | 11,3 => 2
  | _,_ => 0
def state : Nat → Nat → Nat → List Wire
  | 7,0 => atState a7_0 58
  | 8,0 => atState a8_0 60
  | 8,1 => atState a8_1 59
  | 9,0 => atState a9_0 61
  | 9,1 => atState a9_1 61
  | 9,2 => atState a9_2 59
  | 10,0 => atState a10_0 51
  | 10,1 => atState a10_1 51
  | 10,2 => atState a10_2 51
  | 10,3 => atState a10_3 51
  | 11,0 => atState a11_0 41
  | 11,1 => atState a11_1 41
  | 11,2 => atState a11_2 41
  | 11,3 => atState a11_3 39
  | _,_ => fun _ => []
def locate : Nat → Nat → List Wire → Nat
  | 7,0 => locateIn d7_0 h7_0 6 18 3 4
  | 8,0 => locateIn d8_0 h8_0 88 241 6 8
  | 8,1 => locateIn d8_1 h8_1 4 12 3 4
  | 9,0 => locateIn d9_0 h9_0 286 773 6 10
  | 9,1 => locateIn d9_1 h9_1 35 99 4 7
  | 9,2 => locateIn d9_2 h9_2 4 16 1 4
  | 10,0 => locateIn d10_0 h10_0 105 287 5 8
  | 10,1 => locateIn d10_1 h10_1 88 239 5 8
  | 10,2 => locateIn d10_2 h10_2 24 67 5 6
  | 10,3 => locateIn d10_3 h10_3 5 16 2 4
  | 11,0 => locateIn d11_0 h11_0 7 22 3 4
  | 11,1 => locateIn d11_1 h11_1 9 26 4 5
  | 11,2 => locateIn d11_2 h11_2 9 26 4 5
  | 11,3 => locateIn d11_3 h11_3 1 3 1 2
  | _,_ => fun _ => 0
def tab : Table := ⟨count,locate,state⟩
def check (k t n j : Nat) := span (fun i => !run tab k t (state k t i)) n j
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7_0_0 : check 7 0 12 0=true := by decide +kernel
theorem yes7_0 : cells tab 7 0=true := c7_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_0_0 : check 8 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_0_28 : check 8 0 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_0_56 : check 8 0 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_0_84 : check 8 0 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_0_112 : check 8 0 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_0_140 : check 8 0 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_0_168 : check 8 0 9 168=true := by decide +kernel
theorem yes8_0 : cells tab 8 0=true := (@span_join _ 84 0 93 (@span_join _ 28 0 56 c8_0_0 (@span_join _ 28 28 28 c8_0_28 c8_0_56)) (@span_join _ 56 84 37 (@span_join _ 28 84 28 c8_0_84 c8_0_112) (@span_join _ 28 140 9 c8_0_140 c8_0_168)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_1_0 : check 8 1 8 0=true := by decide +kernel
theorem yes8_1 : cells tab 8 1=true := c8_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_0 : check 9 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_28 : check 9 0 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_56 : check 9 0 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_84 : check 9 0 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_112 : check 9 0 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_140 : check 9 0 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_168 : check 9 0 28 168=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_196 : check 9 0 28 196=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_224 : check 9 0 28 224=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_252 : check 9 0 28 252=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_280 : check 9 0 28 280=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_308 : check 9 0 28 308=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_336 : check 9 0 28 336=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_364 : check 9 0 28 364=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_392 : check 9 0 28 392=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_420 : check 9 0 28 420=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_448 : check 9 0 28 448=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_476 : check 9 0 28 476=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_504 : check 9 0 28 504=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_532 : check 9 0 28 532=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_560 : check 9 0 12 560=true := by decide +kernel
theorem yes9_0 : cells tab 9 0=true := (@span_join _ 280 0 292 (@span_join _ 140 0 140 (@span_join _ 56 0 84 (@span_join _ 28 0 28 c9_0_0 c9_0_28) (@span_join _ 28 56 56 c9_0_56 (@span_join _ 28 84 28 c9_0_84 c9_0_112))) (@span_join _ 56 140 84 (@span_join _ 28 140 28 c9_0_140 c9_0_168) (@span_join _ 28 196 56 c9_0_196 (@span_join _ 28 224 28 c9_0_224 c9_0_252)))) (@span_join _ 140 280 152 (@span_join _ 56 280 84 (@span_join _ 28 280 28 c9_0_280 c9_0_308) (@span_join _ 28 336 56 c9_0_336 (@span_join _ 28 364 28 c9_0_364 c9_0_392))) (@span_join _ 84 420 68 (@span_join _ 28 420 56 c9_0_420 (@span_join _ 28 448 28 c9_0_448 c9_0_476)) (@span_join _ 28 504 40 c9_0_504 (@span_join _ 28 532 12 c9_0_532 c9_0_560)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_1_0 : check 9 1 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_1_28 : check 9 1 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_1_56 : check 9 1 14 56=true := by decide +kernel
theorem yes9_1 : cells tab 9 1=true := (@span_join _ 28 0 42 c9_1_0 (@span_join _ 28 28 14 c9_1_28 c9_1_56))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_2_0 : check 9 2 9 0=true := by decide +kernel
theorem yes9_2 : cells tab 9 2=true := c9_2_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_0 : check 10 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_28 : check 10 0 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_56 : check 10 0 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_84 : check 10 0 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_112 : check 10 0 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_140 : check 10 0 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_168 : check 10 0 28 168=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_196 : check 10 0 15 196=true := by decide +kernel
theorem yes10_0 : cells tab 10 0=true := (@span_join _ 112 0 99 (@span_join _ 56 0 56 (@span_join _ 28 0 28 c10_0_0 c10_0_28) (@span_join _ 28 56 28 c10_0_56 c10_0_84)) (@span_join _ 56 112 43 (@span_join _ 28 112 28 c10_0_112 c10_0_140) (@span_join _ 28 168 15 c10_0_168 c10_0_196)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_0 : check 10 1 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_28 : check 10 1 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_56 : check 10 1 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_84 : check 10 1 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_112 : check 10 1 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_140 : check 10 1 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_168 : check 10 1 9 168=true := by decide +kernel
theorem yes10_1 : cells tab 10 1=true := (@span_join _ 84 0 93 (@span_join _ 28 0 56 c10_1_0 (@span_join _ 28 28 28 c10_1_28 c10_1_56)) (@span_join _ 56 84 37 (@span_join _ 28 84 28 c10_1_84 c10_1_112) (@span_join _ 28 140 9 c10_1_140 c10_1_168)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_2_0 : check 10 2 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_2_28 : check 10 2 21 28=true := by decide +kernel
theorem yes10_2 : cells tab 10 2=true := (@span_join _ 28 0 21 c10_2_0 c10_2_28)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_3_0 : check 10 3 11 0=true := by decide +kernel
theorem yes10_3 : cells tab 10 3=true := c10_3_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_0 : check 11 0 15 0=true := by decide +kernel
theorem yes11_0 : cells tab 11 0=true := c11_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_0 : check 11 1 19 0=true := by decide +kernel
theorem yes11_1 : cells tab 11 1=true := c11_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_0 : check 11 2 19 0=true := by decide +kernel
theorem yes11_2 : cells tab 11 2=true := c11_2_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_3_0 : check 11 3 2 0=true := by decide +kernel
theorem yes11_3 : cells tab 11 3=true := c11_3_0
theorem known : ∀ k<12, ∀ t≤5, ∀ i<tab.count k t, Impossible k t (tab.state k t i) := by
  apply usable
  intro k hk t ht
  interval_cases k <;> interval_cases t
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes7_0
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes8_0
  · exact yes8_1
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes9_0
  · exact yes9_1
  · exact yes9_2
  · rfl
  · rfl
  · rfl
  · exact yes10_0
  · exact yes10_1
  · exact yes10_2
  · exact yes10_3
  · rfl
  · rfl
  · exact yes11_0
  · exact yes11_1
  · exact yes11_2
  · exact yes11_3
  · rfl
  · rfl
end P16

namespace P1
open PEqualNP.Outside.L_meta_2309_aux.Cache PEqualNP.Outside.L_meta_2309_aux.Main2331
def field (x bits i : Nat) := (x >>> (bits*i)) &&& (2^bits-1)
def recipeDataS : Nat := 0xc320000c830000c960000c970000c720000c860000c620000c870000b9300cc87400cc63200cc76200cc86200cc96200cc87200cc87300cc87600c7c9800cc94200cc64300cc74300cc98400000a300000a900cc93200cc96300cc97300cc98300000a400cc98200cc7630000c9300bb94300cc84200cc7640000c42cb43c950000c640000c74ccb94530000c8400bc82300bc7690000c4300cc9530000c940000b430000b9400bc95400bc534bcc9534cbc95430000005000000600bc9270000c98000000700000030000c820000c9200b6c980000c95000000200bc6380000c730000009000000800000040000c530000c6300bc7320000c76
def source (i : Fin 9) := (PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.proj 1).fn (raw.getD i.val zero)
def wire (j : Nat) : Wire := ((recipeRun source 7 (field recipeDataS 28 (j/4)) []).headD zero,tagOfNat (j%4))
def decode (x : Nat) : Nat → List Wire
  | 0 => []
  | n+1 => wire (x &&& 511) :: decode (x >>> 9) n
def rawPart (x : Nat) := (List.finRange 9).filterMap fun i => let q := field x 3 i.val; if q=0 then none else some (source i,tagOfNat (q-1))
def atState (data size i : Nat) := let q := field data size i; decode (q >>> 31) ((q >>> 27) &&& 15) ++ rawPart q
def locateIn (shifts slots B M sbits ibits : Nat) (v : List Wire) :=
  let h := frontierHash 0 v
  let d := field shifts sbits (h%B)
  let z := field slots (ibits+4) ((h/B+d)%M)
  if z >>> ibits = h%13+1 then z &&& (2^ibits-1) else 0
def a6_0 : Nat := 0x542811490010008c28171860025800182203190d82000044060019003240d08c401420010240d0602e142008024030441c00210002103010060021400200
def d6_0 : Nat := 0x8
def h6_0 : Nat := 0x8800009641b5930000977412
def a7_0 : Nat := 0x2c09490250005c129204a170a845240142c1508a48028002a09490050
def d7_0 : Nat := 0x2
def h7_0 : Nat := 0x7800042836d280
def a8_0 : Nat := 0xc8700619490210c8681418490250e00c3019490210c068141849025068302019093240101c00194032506028201869025818080e194d821000902e114900580000460949025000584411498050005842114d005000004009490250007c2e116900500078061169021800283a104d825000643611490250006c3011490250000006094902500000140949025000703611490210006c3410490250000030094932500000320949325000642c1149025000602e1149025000642e114900500058301149005000002a09490050
def d8_0 : Nat := 0xa2000f101c0000403
def h8_0 : Nat := 0x8a0aca4443bac400a358001fac623e31446d6c6a00000ab000000000338aa008d0e6d301ce194f68f69800016a
def a9_0 : Nat := 0x7c096d3250007a0949b2580078094db25800760969b25800740949b2580072096d32580070096d3250006e096db250006c096d3250903811493058703e1169305088341149b0508434114d3050006a0949325800680949b2500066094d3250006409693250c41411490250c00611490250005e09493258005c0949b250005a094d3250005809693250345011693258a000114db250a03410493250ac0611490250ac14114902500054096932580052094db2500c5011490250a014114902509006114902580c3e116902508814114982508414114d02507014114902500c34114902509018114932400844114832501c42114132507c20110932503414116902583006114902580c00114d82500c20116902500814114982501c14114d0250700611490250681411490250004e094932506430114932500000014932503020116932586406114902506014114902503406116902582800114d82503014114902580c04114982500c0e114d02502820116902503418116932403420110932580800114c32501c001141b2509014114902580c44114982500c42114d02507c1411690250004c09693258004a094db2507006114902106814104902500c2c11490250282e11490250003c09693258003a094db2506414114902500c3011490250003609490250002c09490250002e09490250
def d9_0 : Nat := 0x20cc12000103a41220000000200487000202048408c0300107
def h9_0 : Nat := 0x406cfd5f30fba60021a28c141942cad07d14c524c31cd782a348caa710000001ca0006580019bd56b22973a1b265111ee2700045c000000000034eb3aca4ae592b12000224d834699600227d10b3389211cac11baa4c7000001aca4d0c169394605ba270250c0000000000126d05b5a002da93800053aa620264cf0063aaf366e7d22bb1908308006370004ec00000000000003b6c3c00083000
def a9_1 : Nat := 0x3609490250
def d9_1 : Nat := 0x0
def h9_1 : Nat := 0x9
def a9_2 : Nat := 0x3609490250
def d9_2 : Nat := 0x0
def h9_2 : Nat := 0x9
def a10_0 : Nat := 0x8e094932588c096932508a0949b25088094d325086094d3258840969b25062094932506009493250820949b25880096d32507e0949325056094932504809493258440949b25042094d32503e09693250380949325034094932501809493258040949b2500e094d325020096932501a0969325800094db25050094932503209493250300949325006094902501409490250
def d10_0 : Nat := 0x31800d8230
def h10_0 : Nat := 0x366231eeb00214015c0033b36c421dc89200b0800ba00001d00139338000157001c5ec4a383e930221aa99e62d
def a10_1 : Nat := 0x6008493250c412926420d02524c942804a49928560949305064129264a0c02524c940304a481281409490250
def d10_1 : Nat := 0x6
def h10_1 : Nat := 0x79374600006445a81223b10000
def a10_2 : Nat := 0xc129204a1409490250
def d10_2 : Nat := 0x0
def h10_2 : Nat := 0x6b40
def count : Nat → Nat → Nat
  | 6,0 => 8
  | 7,0 => 5
  | 8,0 => 29
  | 9,0 => 83
  | 9,1 => 1
  | 9,2 => 1
  | 10,0 => 29
  | 10,1 => 9
  | 10,2 => 2
  | _,_ => 0
def state : Nat → Nat → Nat → List Wire
  | 6,0 => atState a6_0 64
  | 7,0 => atState a7_0 47
  | 8,0 => atState a8_0 56
  | 9,0 => atState a9_0 48
  | 9,1 => atState a9_1 38
  | 9,2 => atState a9_2 38
  | 10,0 => atState a10_0 40
  | 10,1 => atState a10_1 39
  | 10,2 => atState a10_2 37
  | _,_ => fun _ => []
def locate : Nat → Nat → List Wire → Nat
  | 6,0 => locateIn d6_0 h6_0 4 13 1 4
  | 7,0 => locateIn d7_0 h7_0 2 8 1 3
  | 8,0 => locateIn d8_0 h8_0 14 40 5 5
  | 9,0 => locateIn d9_0 h9_0 41 113 5 7
  | 9,1 => locateIn d9_1 h9_1 1 2 1 1
  | 9,2 => locateIn d9_2 h9_2 1 2 1 1
  | 10,0 => locateIn d10_0 h10_0 14 40 3 5
  | 10,1 => locateIn d10_1 h10_1 4 13 2 4
  | 10,2 => locateIn d10_2 h10_2 1 3 1 2
  | _,_ => fun _ => 0
def tab : Table := ⟨count,locate,state⟩
def check (k t n j : Nat) := span (fun i => !run tab k t (state k t i)) n j
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c6_0_0 : check 6 0 8 0=true := by decide +kernel
theorem yes6_0 : cells tab 6 0=true := c6_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c7_0_0 : check 7 0 5 0=true := by decide +kernel
theorem yes7_0 : cells tab 7 0=true := c7_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_0_0 : check 8 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c8_0_28 : check 8 0 1 28=true := by decide +kernel
theorem yes8_0 : cells tab 8 0=true := (@span_join _ 28 0 1 c8_0_0 c8_0_28)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_0 : check 9 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_28 : check 9 0 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_56 : check 9 0 27 56=true := by decide +kernel
theorem yes9_0 : cells tab 9 0=true := (@span_join _ 28 0 55 c9_0_0 (@span_join _ 28 28 27 c9_0_28 c9_0_56))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_1_0 : check 9 1 1 0=true := by decide +kernel
theorem yes9_1 : cells tab 9 1=true := c9_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_2_0 : check 9 2 1 0=true := by decide +kernel
theorem yes9_2 : cells tab 9 2=true := c9_2_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_0 : check 10 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_28 : check 10 0 1 28=true := by decide +kernel
theorem yes10_0 : cells tab 10 0=true := (@span_join _ 28 0 1 c10_0_0 c10_0_28)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_0 : check 10 1 9 0=true := by decide +kernel
theorem yes10_1 : cells tab 10 1=true := c10_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_2_0 : check 10 2 2 0=true := by decide +kernel
theorem yes10_2 : cells tab 10 2=true := c10_2_0
theorem known : ∀ k<11, ∀ t≤4, ∀ i<tab.count k t, Impossible k t (tab.state k t i) := by
  apply usable
  intro k hk t ht
  interval_cases k <;> interval_cases t
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes6_0
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes7_0
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes8_0
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes9_0
  · exact yes9_1
  · exact yes9_2
  · rfl
  · rfl
  · exact yes10_0
  · exact yes10_1
  · exact yes10_2
  · rfl
  · rfl
end P1

namespace Cuts
open PEqualNP.Outside.L_meta_2309_aux.Cache PEqualNP.Outside.L_meta_2309_aux.Main2331
def field (x bits i : Nat) := (x >>> (bits*i)) &&& (2^bits-1)
def recipeDataS : Nat := 0xbc6210000cac4220000cac4240000c2ac620000c6ac620000cac9220000cac9290000cac6330000cac6360000cac9330000cac9390000cac6440000cac6460000cac2140000cac2190000cac3140000c9ac310000cac4130000cac6130000cac9130000cac6140000cac9140000cac61900000bc32100000bc9610000cac4210000cac64100000aca1300000aca1900000000a300000000a90000bac9120cccc96321000bc64c32000bc43c42000bc96c42000bc43c62000bc94c62000bc93c92000bc93c63000bc94c64000bc43c21000bc21c63000bc64c21000bc96c21000bc31c42000bc31c62000bc31c64000bc41c32000bc41c62000bc41c96000bc61c32000bc61c42000bc61c92000bc61c94000bc42c91000bc62c91000bc64c9100000bc92100000bc631000000ac320000cac3210000bac32100000cc4320000acc4320000b1ac620000cac9210000abc431000000ac430000cac4310000cac63100000cc943000000ac930000acc94300000cc964000000ac640000acc964000000ac94000000ac960000abc9410000cac9410000cac9610000bac96100000aba14000bc94c21000bc41c92000bc41c63000bc61c43000bc42c63000bc64c92000bc64c63000cbc3216000cbc9216000cbc4312000cbc4316000cbc6312000cbc9412000cbc9416000cbc9612000000ac420000bac421000000ac620000bac4310000bac9310000bac6410000bac94100000aba1300000aba1900000aca14000bc32c42000bc92c420000bc43a10000bc94a10000bc93a1000bc96c640000000b41000bc21c93000bc61c9300000bc43100000bc9410000cc32a10000ca1c620000cc96a10000bc32a10000bc63a10000bc96a10000bc92a1000cbc4216000cbc9312000cbc64120000abc3210000acc4210000acc6210000abc9210000bac9210000abc6310000bac6310000cac9310000acc6410000abc9610000000b310000000b910000c8ac310000cac91700ca1cc43200ccc632a100ca1cc93200ccc642a100ccc942a100ccc962a100ca1cc64300ca1cc94300ccc963a100ccc964a100000bc42100000bc6410000acc3210000cac423000000ac920000acc431000000ac630000cac9340000cac6490000acc9410000acc961000000ba13000000ba19000bc92c62000bc63c620000abc4210000acc9210000acc6310000abc64100000cc63200000cc962000bc41c93000cbc931500000bc9310000000c320000000c960000cc42a10000cc92a10000cc43a10000cc63a10000cba1630000cc64a10000cc94a10000cba16900000cc43100000cc941000ccc6432000ccc943200000cc932000ccc964200000cc942000ccc964300000cc64300000cc963000ccc4321000ccc9421000ccc6431000ccc9431000ccc9641000ccc9632000000ca12000000ca16000000ba14000000ac31000000ac910000abc6210000cc93a10000000c31000000ca130000000c410000000c91000000ca19000000ac410000000c2100000cc32100000cc92100000cc63100000cc9310000000c6100000cc961000ccc9321000ccc963100000cc42100000cc641000ccc6321000ccc9621000ccc64210000cac9270000c8ac6300000aba1200000cc621000bc43c92000bc93c62000bc92c63000bc94c63000bc93c42000bc64c9300000000a20000000c940000000c6400000000a400000000a60000000c420000000c43000000000100000cc6420000000c620000000c920000000c930000000c6300000bb613000bbc9213000bbc9413000bbc4319000bbc6319000baca139000baca19300accc932100accc943100accc96310000c3ba120000c4ba120000c5ba120000c7ba120000c8ba120000c9ba120000cba1650000cba1670000cba1680000cba164bc32bc94a1bc92bc43a1bc43bc96a1bc63bc94a100bcc642a100cba1c62300cba1c62700cba1c62800cba1c62900000bb3120000000b21000bbc931200000bb413000bbc6213000bbc641300000bb91400000bb9160000000b61000bbc9316000bbc4219000bbc621900bbc43a1200bbc63a1200bbc93a1200bbc64a1200bbc94a1200bbc96a1200bbc42a1300bba1c62300bbc64a1300b4bc32a100bba1c62400bbc63a1400bbc93a1400b6bc32a100bbc42a1600bbc92a1600b6bc43a100bbc93a1600b6bc94a100bbc42a1900bba1c62900bbc64a190000bac2160000bac4120000bac6120000b6ac31000bcc93140000bac416bbc64a1c32bc42bc63a1bbc93a1c42bc42bc96a1bc62bc43a1bbc93a1c62bc62bc94a1bbc64a1c92bbc64a1c93000bbc4213000bbc9314000bbc641900cc3ac62100cc4ac62100cc9ac6210bbc931c420bbc641c930000acc931000000ac210000bac31200000aba16000000ac610000bac9160000bba1420000bba1620000bba1640000bc42a1000000ba120000bc64a1000000ba16000caba123000caba124000caba126000caba129000caba162000caba163000caba164000caba1690000bba1320000b2ba190000bba1630000b4ba190000b6ba19000000ca1400cba1c6250000cba1620000c6ba12bcac927c92bc63c8ac630000c1ac620000000009000000000800000000070000000005000000000400000000030000000002000000000600000000a10000ba1c62
def source (i : Fin 9) := if i=0 then neg raw0 else raw.getD i.val zero
def wire (j : Nat) : Wire := ((recipeRun source 10 (field recipeDataS 40 (j/4)) []).headD zero,tagOfNat (j%4))
def decode (x : Nat) : Nat → List Wire
  | 0 => []
  | n+1 => wire (x &&& 2047) :: decode (x >>> 11) n
def rawPart (x : Nat) := (List.finRange 9).filterMap fun i => let q := field x 3 i.val; if q=0 then none else some (source i,tagOfNat (q-1))
def atState (data size i : Nat) := let q := field data size i; decode (q >>> 31) ((q >>> 27) &&& 15) ++ rawPart q
def locateIn (shifts slots B M sbits ibits : Nat) (v : List Wire) :=
  let h := frontierHash 0 v
  let d := field shifts sbits (h%B)
  let z := field slots (ibits+4) ((h/B+d)%M)
  if z >>> ibits = h%13+1 then z &&& (2^ibits-1) else 0
def a9_0 : Nat := 0x884106208408a1b0d000000310010401a6d348000000000440049b6d340000000010fe136d34d80000000043f04db4db400002d80103c1a6c34900000000043e84db4db40000000010f8136db4d00000000043d84db4d340000000010f4136d34d00000000043c84db4d360000000010f0136d36d00000000043b84db6d3400000001e04c126db4900000ec00410069b4d0600003a8010401a6d30980000e800410069b41260000398010401a6134980000e40041006834d26000038801040186d349800001c0040f069b6d2000003680103c1a6db0900000e00040f069b612400003780103c1a61b4900000dc0040f06836d2400000086d03e1a6db0900000000043604db4db60000000010d6136d36d80000000043504db6db40000000010d2136db6d000000000434049b6da60000338010001a6db41800001e00400069b61260000330010001a61b4980000ca0040006836d26000032001000186db49800000000431849b4d360000310010001a6db4800000000043084db4d36000000001040126d348800000000430049b4db40000000010be126db4d80000000042f049b6db40000000010ba136d36900000000042e04db6d2400002d8010001a6c34980000000042d04db6d3400000000103c126cb4900000000042c84db4da60000000010b0136db4980000000042b849b4db60000000010ac126db4d80000000042a84db4d360000000010a8126db6980000000042984db4da60000000010a4136db49800000000428849b4db60000000010a0126db4d800000000427849b6db400000000109c126d36d800000000426849b6da6000000001098126db6d00000000042584db4db4000000001094126db4d800000000424849b6da6000000001090136db49800000000423849b6db400000000108c136db4d00000000042284db6da4000000001088136d36980000000042184db6d26000000001084136db69000000000420849b6d26000000001050126d34d800000000420049b4da600000000107e126db4980000000041f049b6d3400000082a07b1b6d30d00000000041e049b6da400000000104a136db4900000000041d849b6db6000000001074126db6d80000000041c84db4db6000000001070136db6980000000041b849b6db600000000106c136db4d80000000041a84db6da6000000001068136db6980000000041984db6db4000000001064126d36d80000000041884db4db4000000001060136db69000000000417849b6d3600000000105c126db6980000000041684db6d26000000001058136d36d80000000041584db6db4000000001054136d34d00000000a414049b4d36000000027002126db4900000000981284db6d24000000001048126d369800000000411849b6d26000000001044126db69000002000007869b61a600000000103c126db49800000000410049b4d3600000000103c126db4d000000000410049b4da600000000103c126db69000000000410049b6d26000000001040136d34980000000040f04db6d24000000001042126d369800000000410049b4d2600000000103e126db6900000000040f049b6d2400000000103a126d34d80000000040e049b4da6000000001036126db4980000000040d04db4d26000000001032126db4980000000040c049b6d3400000000102e126db6900000000040b04db6d24000000010000126db6980000000040a849b4d36000000001028136d349800000000409849b6d34000000001024136d36900000000040884db6d2400000001001e126d869800000203800069b6d2000000080d0001a6c34980000000040604d84d26000000001016120db4d000000000405049b6d26000000001000126db498
def d9_0 : Nat := 0x40840121c00004000840600c4020860008673d143200000800108441084490040000001084a218000
def h9_0 : Nat := 0x540d8a17ab44a61000000000a3c000d3092100000000000047c00027e342469354880000387000845816359406000000771a7526dd53525000a88986b3700045772e75846a766d6542a928431478515214c0921b912000b50000179c0800060a57d23b53e60f722d7fd4e239c5663d63892fb0717491071e12d00076fb01b4600013f000d1c98400000000063ac2b672641336a2053424a35c11975e76300081810d30300035f181000d13a0e73394c427000c77a4d81a000489000000a4f370332743862a17c68905102000b52885000c29d1db5115545d276683c73b6b000111582000000000a3562600034962331f66e000000000000000000b48b2466cd60b0400045b50c66410b000000b67c5a847d2cc4bb7b000
def a9_1 : Nat := 0x4188f10e186d3001000002044608e0c36180880888106208438a1b4c000044208310420450d86800022044108c116286c30108dd022084608b14361800c5684106208408a1b0c006274408310421c50d860020021440882106206c3601
def d9_1 : Nat := 0x4
def h9_1 : Nat := 0xd6947833c70055b2a15900
def a9_2 : Nat := 0x20c478870c369800c4082126186d30018312420430d868030820848861b0d006084808b0c361808c088c11c186c3011
def d9_2 : Nat := 0x30
def h9_2 : Nat := 0x2e0000db944f6200
def a10_0 : Nat := 0x1920045886db6d260005900118e1a6db4d8001540404186db4db600455081106236db4180002029c4086db6db400408088102226db0d80102022c4188db6c26000080840001a6db698010202104188db6da000408084102226c36d80102020c41081b4db600408081104236db6100114e20c40881b6d360000093f1961b6db6d8000023444606db6db6000008be1161b6db6d80000222088869b4db033000888042226d36c000000004ae849b6db6000008cc2681b6db6d800002220ae069b4c36000008881721b6db6d800000004ad84db6da6000008d010e1b6db6d8000022046b069b0d36000000012b4126db6d8000022109b86db6db6000000012b2136db6980000220cac061b4d36000008812ae1b6db4100000220492069b0db40044581f196236c36900000222cab06db6c240000088b2181b6c3690011542ac52889b4d060045508114a226db418010202a44108db4c34000000010ea126d30990000000436849b6c24404538a8140206db4900114e20c50081b6d26000008a41161a6db6d80000227010869b4da60000089c1021a6db6d8000022706586db6da60000089410e1a6db6d8000022504606db6da6000008a310e1b6d36d80000228c4586db6da6000000012aa126d36d80014a00487869b4db6000008a51741a6db6d8000022949b86db4db6000000012a8126db4d800000004a9849b6da6000008a52681b6db6980014a0048706db4da6000000012a4136db4980000229054869b4db6000008a41401a6db4d80000227055869b4db60000089c1401a6db698000022705406db4da6000008941561a6db4d80000225054869b6da6000008941501b6db4980000228c5486db4da6000008a31401b6db4980000229461069b4db6000008a51441a6db4d8000022944d869b6da6000008a51821b6d3698000022944f86db6d26000008c21961b6db6d00000228844069b6db6000008a21181b6db6d0000022844406db4db6000008a11161b6db6d000000004a8849b4db6000008ab10a1a6db6d8000022ac5e06db4db6000000012a0126db4d800000004a7849b6db4000008ab2681b6db6d00000230850069b6db4000008c21501b6d36d00000228854869b6db4000008a11521b6d36d0000022ac4d869b6db4000008ab1821b6d36d00000226c0f869b6da40000089b1981a6db6d80000226c4186db6da6000008c11981b6d36d8000023044206db6da6000008c11021b6db6d000000004a7049b4db6000008a91a21a6db6d8000022a45f06db4db60000000129a126db698000022a46806db6da6000008a91721b6db6d0001520048686db4db400000001298136db6900000226c5406db6da4000008c11401b6db6900000227c4406db6da60000089f10e1b6db6d000000004a5849b6d36000008a027e1a6db6d800000004a5049b6da6000008a01781b6db69800000004a484db6d260005000121e1a6db6d0000022809b86db6db400000001290136db690001400048706db6da4000008a827e1b6d36d800000004a384db4da6000008a810a1b6db69800000004a304db6d26000008a81741b6db6d000000004a284db6da4000008a427e1a6d36d80000229068869b6d36000008a417c1b6d34d80000239040869b6db60000089c27e1a6d36d80000227042869b6da60000089c1781b6d36980000225068869b6d360000089410a1a6db698000022506806db6d26000008842881b6db48000002210a1869b0d36000008a317c1b6d34d80000228c5e06db4da6000008a31a01b6db4980000220c8406db4db6000008831c61b6db698000023089f869b4db6000008c21741a6db6d0000023089b86db4db4000008a21a21a6db4d8000022885d069b6db4000008a21721b6db4d0000022048386db6db4000008a126e1b6d36d00000226c42869b6da60000089b1741a6db6d00000226c9a06db6da4000008c11781b6d3698000023049b86db4db4000008c12681b6db6900000227c6806db6d260000089f1721b6db4d00000227c9a06db6da40005280114e1b6d34980014000455069b6d340000000117c136d34d9000000045c84db6d3440408112152226d30900119850844089b4db000000001282126d34d800002330a0069b4d3600466088236226d36c00000246c40869b6db60000091b27e1a6d36d80111046c4188db4da00044411b10e226d30d8000022209f069b4db600444087274226d30d80000000456849b6d260008c8010001a6db4980110846440889b0d360000088427a1a6db498000000046a04db4d260000000112e13613498000000049e04db4d260044188226c206d34d80000220c9986db6da6000000011be126d36d00010e0049d869b4db40044393a104236d3610000000049c849b4db40044388226c236d36100000000469849b6d340000000112c120db4d0000000049c049b6d340044088226c236db4100110222c99889b0db40000093626e1b6d36d0011044d846081b4db40000088226a1b6d36d00110423098881b4db4000009332681b6db690011164cc4608db6c240000088b2641b6db690011162309888db6c24004458cb260236c3690000000046d84db4da40004600125e1b6d3690000000049704db4da4000000011b4136db490000000049684db6d24000008cb2581b6db490000020a46586db6d26000008291461b6d3498000022944a869b4d26000008ab14c1a6d36d00000229861069b4db4000008a61821b6d36900000000495849b4da4000008a61501b6d36900000209866069b6d36000008261441a6db4d00000228013869b6d2400444021106236d36808100222c0f889b0db4000528012041a6db4d80014a0048686db4d3600000001254136d36980014a0048086db6d26000528011601a6d36980015200481869b4db600000001252136d3698001520048006db4da600000001250126db6d00015200481069b6db4000548012021b6db690000022c050069b6da4000500012061a6db4d8001400048006db6d260000000124e126db6d0001400048686db6d34000590aa14e1b6d34d8001640405386db4da6000550101621a6db6d0001542c45386db6d340000088118c1a6db4100000220c38861b4d26000008882201b6d36800000000493049b6db600000001124136db4d8000000049284db6da60000088b2481a6c36d0000c400455069b4d36000550012161a6d36d0000000043b049b4d064000000118c126db411002160045386db4da40002d80114e1b6db4900000000438841b4d2640000001186106db4910000236444069b4db6000008d91081a6db4d80000236445869b6db4000558011601a6d36d0000023604406db4da6000008d81081b6db498000023604586db6da400000001246126db4d8000000049104db6d2600441882142206d34d80000000490849b4db600000001240126db6d0000000048f849b6d3600440882142236db410000000048f04db4da60000000123a136db690000000048e04db6d26000528011541a6d34d8001400045386db6d2400000001234126d3698000000047c04db4d2600000001230126d36d0000000047b049b6d340000000122a136d36900000246c42869b6da6000008882341a6d36980000246442869b6da6000008e017c1b6d34d8000023805e06db4da6000008e01a01b6db4980000221c8c069b4db4000008de1a21a6db4d8000023785d069b6db4000008de1721b6db4d0000022088b86db4d340000088b22c1a6db690000022308a86db4da4000008291021a6db4d8000000048a049b4d34000008af1501b6d34d0000022ac5706db4d34000008a61981a6d36d8000022984186db4da6000008a61021a6db6d0000022986586db6da4000008261061b6db498000000048984db4d24000008a50521a6d3498000022ac57869b4d34000008a004c1a6db490000022a05706db4d24000009120201a6d36900000232840869b6db6000008c91021b6db4d8000023204186db4db6000008c71061b6db4d8000023144186db6da6000008c41021b6db6d0000020405f06db4db6000008101721b6db6d00000000488849b4db000000001220136d3680001100048686db4db6000000011ae136db480000000046b049b0d360004200121e1a6db6d8001080048706db6da60000090d1161b6db6d0000000048604db0da4000590011e41a6d34d8000022a868869b6d06400008aa1c81a6d36d80000242c4106db4db4000588011e21b6db4900000229c68061b6d26400008a71c61b6db690000000048504db4d360005280103e1a6db6980000000410849b4da64000000103e126db6910014000410869b6da600000001212136db4d00000222084069b4c3600442083104206db4c10110820c4088db0d3040442081104236c34190110620840881b6d064000088b20e1b6db0900014a00459069b4d20400500011621a6c3491000022c842069b6d20400008aa1981a6d3419000022a840869b6d04400008b11081a6c34990000229c41861b4d26400008a7196186db4910015400444069b4db6000550011081a6db4d8011542ac57889b4d04000538011081b6db4980014e0044586db6da4004538a815c206d3490001642a842069b6d300000000120c126d34d8001642a858869b6d360000000120a126db498001642c45386db6d26000008880ea1a6d30980000222c36869b6c24000588a71081b6c3498000000048204db6d24000009031161a6db6d80011000481069b6db6000440012021b6db698000024004586db6da600000001164126d3499001642a855869b4d06000590aa14a1a6d34c00000000407049b6d20400790010201a6d36d00000000408049b4da4400080011e21b6d3690010202a442089b6c2600000001162126db4910016229c54061b6d24000588a71401b6c34900000000406849b0d2640000001042126d3698000022704106db4db6000008a31021b6db4d8000022945c86db6d360000082014a1a6d3498000022905406db4d36000008a31561b6d34d8000022884186db6d36000558010421a6d36d8000022ac6806db6d360005580103e1a6db6d0000022885406db6d34000008ab13e1b6db4d0000022c066069b4db6000008b01041b6d36d0000022c06586db6da40000000103e126db6900000226c4106db6db40000089f1981b6db4d8000022805f06db6d360000081e1401a6db490000022a06886db6d36000540010421b6d3698001500040f86db6da4000000011fe126db698000000047f04db4d36000000011fa126db698001980047e069b4d36000440011f61a6d3698001080047d069b6d26000418011f21b6d34980000220c7c06db4d26000408011ee1a6db4d0000022047b069b6d34000000011ea136d34d0001160047a069b6da4000658011e61b6db4900015400440869b6d04000080011161a6db0900014e00441861b4d26000008291161a6db698000020a45406db4d26000008af1061b6d34d8000022bc6586db6d34000008ab1e01a0d34d0000022ac13069b6d34000008261101a6db698000022b86606db4d36000008ae1021b6db4d0000022a07786d84d24000008f21101a6d36d8000020406686db4db4000008f11161b6db6900000208054869b4da6000008201401a6db4980014a0040f069b6d26000008b01061b6d3698000022c040869b6db40005480103c1a6db690000022086706db4134000000011e0120d34d0000000047784d84d24000000011dc126d36d80000000476849b6d36000000011d8136d34d80000000475849b6da6000000011d4136d3698000000047484db6d26000590aa1021a6db418001642a808069b4db62c8008b1108226c34800000000474049b6db4000000011ce136d36d0000000047304db6d34000550101981a6d3618001540405386db4db4004550cc110226d3600000000047284db6da4000080b114e1b6db6900002029c65861b6da4000588a7106186db4980114e32c45881b0da40006600103e1a6db6d8000020844106db4db6000008211961b6db6980111020c4088db6db000441881116236c36d8001040040f86db6db4000008b21281a6db480000000045604db4d344000081010a1a6db099000022c44a069b0d26000008201561a6d34d8000020805406db4d260005580103c1a6db4d0000020785406db6d24000008e41041b6d36d8000022106686db6d36000008821c61b6db6d00000000410049b4d26400558011541a6d34110015200408069b4c244000000103c126db4910015000453861b4d24400660011c41a6d34d80000222070869b4db6004440831c0236d36800110820c7008db6d20004420811bc226c34d80110638041081b4d36000438011be1a6d36d0011023784108db6d04004408de116226c36d0000022086e86db4db40000088b1b81b6db690001180046d86db4da4000658011b41b6db490000020a452069b4d36000008291381a6d3698000020a455869b4d36000000af1b2126d34d0000022bc54869b4db4000008a915c1b6d3690000020984d869b6da40000082613e1b6db490000020985406db6d24000000ae1b0136d34900000208440869b6db6000008841ae1b6db480000022106b069b0d360004180103e1b6db698000020804106db4d36000008201161a6db698000020804606db4da6000008201961b6db4980000207866069b6d360000081e1101a6db6980000207843869b6db40000081e1041b6db4d0000020784606db6da4000008a10541b6d34d00102022066089b4c30000008bc1021b6db6d80000220c5d06db6db62c8008b1108226c34810000000455049b4d34400550101521a6d30d00015404055869b4d84000080a7150186d36900002029c5486db4c240000000114e136d34910000208040869b6d36000008941041b6db4d8000022945086db4d36000008a11081b6db4d80015600400069b6d36000008a11401b6db4d0000020784186db6d26000540010001b6db4980000220c66861b4d360000088119a1b6db410000023345086db4d34000440011aa1a6d3698001060046a06db4d26000408011a61a6db4d00011600469069b6da4000008291521a6d3698000022bc45869b6db4000008af1841a6d36d0000022a413069b6da4000008ae1101b6d3698000022b86086db4da40000000110e126d36d0000000044604db4da4000000ca154126d36d80000221007069b6d20000008aa1a21a6db418000003145384db6da4000008c41161b6db0900000204068869b6db6000008101a01b6db6980000221006869b0d26000008a71a0186db4980000200043869b6db6000008001041b6db4d8000020004606db6da6000008aa1481a6d3418000022a84a069b6d36000008a713e186db4900000229c4a06db6d260000000119e136d36d00000000460049b6db64000000117e136d36d9000000045e84db6da640000001176136db6d1000000046704db413400459084102226c34c0011622104188db0d200000088819a1b6d36d8000023344586db6db4000410010541b6d34d0000022bc44069b4db6000008ae1161b6db6900000000466049b4d3600000001196136db490b200221000089b6d202c400884000226c3498b200229410089b4d202c4008a003c226c3490000023244206db6d2000000001194126d3698000000046484db4d26000008c71081a6c34d8000022b04406db4db6000008ac1081b6db4d8000022b04586db6db4000550101081a6db6d80000000464049b4db40000000118e126db4d0000000043b049b4d060000000118c126db4100115420444089b6d86000008aa10a1a6db6d8011542204188db4db000455084106236db4c00000000462849b6da4000080a71081b6db698000000046204db4da400408088104236d30d80102022c4108db6c34000000010e2106d34980114e20c45881b6da600000001186106db4900000229c4286db6da600453884102236c34d80114e2044588db0db400444087104236d30180110423045881b6c34000008aa1441a6db410000020404e069b4c26000008101361a6db0900000229c51861b4d26000008a514c1a6d3698000022bc5086db4d34000008a61401a6db690000022b85086db4d3400000001184126d36d0000000046084db4da400442000106236db4800110800040889b0d36000548010001a6db698000022945706db4d26000008af1401a6db4d00110620843881b4d8600440882118206db6100110222c4608db0c3400000001164126d34980000000458849b6d24000008940001a6db4980000000455849b4d3400000001150136d34900015404044069b4c36000550101161a6db0d00002029c4406db4c26000080a71161b6db090000000043a849b4c26000000010da126db0900000000460049b6db60000000117e136d36d8000000045984db6d36000008be1101b6d36c0000000045e84db6da6000008bc104186d36d8000000045d84db6db4000008ba1041b6db610000022e44586db0db400000001170126d36d8000000045b84db4da60000000116c126db6d0000000045a84db4db400000001168136db690000000045984db6d36400528011641a6d34800014000458869b0d24000008a515e1a6d34d80000029858049b4da4000008a015c1b6db490000000044104db4d3400455081108226c34180115420445889b0d8400453883110206d36800114e20c42081b6d20000008101281a6db6980000000400049b6d2640000001152126d3690000020a450069b6d26000008a504c1a6db498000022984e069b4da6000008a61361a6db690000000044184db4d2600000001102126db4d0000022144106db6db600000001054136d34d0000020a44a069b6d26000008af1081a6db4d8000022bc52069b4d36000008af1441a6db4d0000020984a069b6d26000008ae1081b6db498000022b85186db4d26000008ae13e1b6db4900000000444049b4da600000001116126db690000022b041861b4d36000000ac020136d36d0000022b04086db6d04000550101021a6db6100002029c41861b4da600444081104236db6180110620845881b6db60004200115a1a6db4980000000407049b6d2000408088106236d30800102022c40889b0c340000000101a126c34980000204042869b6c2600000001154126d34d00000000408049b4da40000000114e136d3490000000045604db4d34000558011541a6d34100015200408069b4c240005400114e186d34900111020c41081b4db000442083104206db4c0011082044108db0d0600440882116236c36100000229842069b6da600000001108126db4980000000452849b4d2600000001148126d34d8000000045184db4d2600000001144126db4d0000000045084db4d3400000001140126db490000000044f84db6d240000000111e136d36d8000000044704db6db400000001014126db4980000221440869b0db6000008851061b6db680000000044f04db4d360000000113a136db4d0000000044e049b4da600000001136126db6900110820c4088db0d3000441882102206db418000000044d049b6d3600000001132136db4980000000410049b4d260000000103c126db490000000044c049b6da60000088312e1b613498000022044b06836d340000000112a126d34980000000413849b6d2400000001128126db4980000000400049b6d2600000010000126db698000000a410049b4d260000002603c126db490
def d10_0 : Nat := 0x10020200690000229400308e00142012040000861842001c0500000080571004608580604023002900402194000080200004a8520c80000000300a8a2100600c00081e0009000908101040084001081d21402384ee0012018c00100000800410164080a700162000209000006464004c500000000ee00027080a11b42100043080478002102a8000000880030806108c400042300c01001610e923104001902110020d84272ec49208003802000001085427044008043107002066720000000e010400080a3080600010010061004220806830001018133c4007003e18000a840310001009400984000000
def h10_0 : Nat := 0x97e94fbd583117c44347a556961b4350d8293c6a77b130d75d320557000285200012e46906d230000000491c00000018f468c0827d81f19d33e55f600021ac000000000000000000000a6cc00000005588228000000263b0000000da1cd5d000000000000000002ac600016be00021b7c82400000000000000000b47144d000328a0000000a900ec5000344aa4d8000179c6e7a450000424f25400009c8a2d8df8d77e6c2c66d57c0002e7dc90c000739000000030eb0000984dac8000a504000000000066a09d21232a2c31cd6d39aa4000c53221921c8000cb41a83d63400015cc000c93caeb00024af00015ce00006326bc1515a8d19ed8300000964800046ac00000011de000000000004e300020d000032b6d3dd90e0000000c19200b00019538ad0000ab0ee6b50cc00027c904438ddcd6150000085a8000b4f8000b048000b5b8000000000061d325f000000000025e614dc9c00002c9750b4000000000064a40002480000a600000ca70000c03f06ec09a2670002edf000000000015a73376d00b1940007234000424400025535f0d888000000000093a5ecd00032760000000000000000000000000c7100012c1b884e3f22b800089400000003172699a85300022acbb1e86d907c89cd9cd44bc346c55d0aad28c9840000000000a968000d578000000040338aa14d3b7a8ef920c000d92e83780300000000000c18deea8b504a593061350002d8a549e58b58496001712c8f4a4341b959202478180000002c5678910c344e5e3100032ce5088000000104f94740000001967789a9870000000a109c78d7560ad29636630000000440f1888b8d22fd6b46d27a3229db1034bad945d56578c45f105da759238a44103ac0719a24f028f11fe60232aa483800020fe420c46c8e0aba5282d9a4e14574c432500b66ac2626e5cbbed3462b0e014971da122f76d7742a015a6c9e8900015424a90000000000000000000000000985c00038b86a715be28464f5021281692d6b250e110c0d617b9b1ea12f1e8b24799b8556d2256769d9136fe8b477bf045765ca5e00029933b2ec5b5b74828a5e800058cec99839d6bb2a8c9db0000000d07222da694000da6986a9abed99a6ec00000014de2a858a6a4b000087a0000a5d285d757f5f171fe8c400026d18b6f2469404e3db964ec87aeae48767d8f2c5a28f8675924cd0bde23aa4ec5c595ecc6163b02b77fcecc183682556891d422776787a3c8e5aa7c000575d86c65f86a665c6839b6592b112031cdc85400000008a7d5e4000d2df28e83e91663215a6f70168cd88a107b32054df30d4d4700000008af4ee00000ddc00000006a1a0840001cb10000000000000000025e4772ec13b74400041ae54a0000000000281d00030c70000ab30001aa2000099592aae1d95b06910000ad8c78910792f8000994b4b3000000000000000001ea00000000c822699b5b455143b8d0f702481a0000000107a0db90e2ee13b01df336d400084e96e8590a13c000000043f180d641191220db034000000000000007332c4100020ed722254b916a53800031b94525a1a94ba1cc70e99be22480000000e6c19e8000dad55e136c0000828c00016eb4fe79c0000d9e5a97634a49a3a58000c6d80002b5450b45e3109b9c527b47f61bc000000091f0000780841440288d93ac29839719d9000014010001d2f0000000000343d753edd90000e49939800098aed891b70ed6851186800000007bbb4d583d400000000000002d7082d76369a360ca114582ca065a6224eccc5168dd98854aa1ea3a058f747d93215a5e4d72436956566c962218c7739768a8b7e6a20716061373d84a10000000196c0000002a9b718049500011ebd8fb106882eda0643204eaab800017760d821d654500000000000000000367200000000000000b89d1654b13105a69ac04c50d018b7d723a0001d4e9aa221696a99d841fa9505209aedb3ab22959f320f17eccb82518edac1184476252eb939ba8b0b4c658181f5e1f435f0ff208f119b4874a2c15c44983f4c62484313016180000000000471492ab325ecf1b6567e20b860a121d5a4d87100656f5d7f292ac6f365068865dddb11796dc161861eec2eeeb71a024675afd12655adc431ae1c8927426394059db416151cad0f302900022456a9400000000003780c8b0002a1892a40000000000ba4b10dd3cd9ec32c9c31932f1e9d369eec88d6102180f6ca533f011a8449f747261cf519a69861c2d9e7994925127c6bca17ac3b6a7acc2db8b12b56be5ae31a65229388a3896a715c7370d9ca26e133c958e0471e6e94a5f6048566aa6d15d8000c94c000d282513000000000028763492df4a42041035ec0004458000816543e293ac9e0000000000000014600002830000755651192e5548770b1fca3398d35632d3f00024ec0000000ca140000000681871ca74998000052ad6ad446b4a482fe854d58aaabc955e6499fd9c3a58f050
def a10_1 : Nat := 0x1642a840869b6d06000590aa1081a6db4c00000000465049b4da600000001192136d34980116421040889b0d30000550101101a6d30d80015404045869b6c34000550101981a6d36180015404040869b6d8400000001190126d36d00000000463849b6d34004550cc110226d36000115420442089b0d06000080a7106186d36980002029c65861b6da4000080a71101b6d30980002029c4586db6c2400408088198226d30c00102022c40889b0c340040808b196236c30900016229c41861b6d26000588a71081b6c34980114e20c44081b4da000453883108206db4800114e32c45881b0da4000008b21281a6db4800000032084049b4db4000008aa1481a6d3418000003108384db4da4000008b11281a6c34980000229c4f861b6d24000000a9000126db698000005c454849b4c2640000170150106d3499000005bc54849b4c344000016e150106d34d1000002acb6849b4d84400000ab2d8126db411000002acb584db4d04400000a92d4126db091000002a4b484db4c2440000168150106db49100000500b3849b4d360000011a1c8126d36980000045871849b6da40000012c2cc136db49000000004b2849b4da600000001054136d34d000000004b2049b6da400046e101521a6d3081002c384054869b4c044000088ad421b6d30d00000000495849b4da40000008111e136db6190000020c47041b6db64000000012a0a6d34990000000013829b6d2440000001040126d3498000000040f049b6d24000009631561a6d34100000244854869b4c2400000962150186d3490000003244204db6d20400000c8110126d30d90000031c42049b0d36400000ac106106d34d9000002b04084db6d04400000aa1a2126db419000022a851069b6d04000000c4116136db0910000004042849b6c26400008101381a6d3098000020404d869b6c24000000a71a0106db4990000229c51861b4d2600000001148126d34d8000000045184db4d2600000001184126d36d00000000451049b6d3400000001182136d3690000000044f84db6d2400000118210126d36d0000004548384db4da4000000a5156126d34d8000002ac54849b4db4000000a9150136d3690000002805404db6d24000528011641a6d34800015600455069b4d04000548010201a6d30900015000453861b4d2400000029040126d3498000000980f049b6d240000000005e0a6db4d90000000017029b6da64000000005a0b6db4990000000058029b4da4400000011dc126d36d80000000476849b6d36000000011d8136d34d80000000475849b6da6000000011d2136db498000000047384db4db4000000011cc136db4d0000000047284db6da400444083104206d36c00111020c4388db4c3000444087104236d30180110820c41081b6d3000442083102236c34c0011082044108db0d0600441882102206db4180110220846081b6d8400440882116236c36100110222c4608db0c340044108c116206db0d00000008052849b4d260000001e140126db4908dd0220846081b6d806374088b118236c30c18dd0423045881b6c3062b42083104206db0c18ad082044108db0c0662b41882102206db01989d1020c41081b0db06274408310e236c30c189d1021c4108db0c066274188210e206c36190011baa855869b4d00400b0ea7150186d341100115aa855869b4c04400456a7150186d309100113aa855869b0d0440044ea7150186c3491002c1aa855861b4d04400000b2128126db481000000006682db4d34400000aa148126d3419000002a851049b6d0440000010136126db0910000029c51841b4d26400000a713e106db4910000000081829b4d36400000002000b6d34990000000081029b6d34400000002020b6db4910000033044049b4db040000088106136d36810000022043849b4c3640000084106136db4810000021040849b0d3640000083104106d34d90000021c4104db4d8440000081104136db4110000020445849b0db44000008b118136db0910000022c6584db0da44000008311e106d36c18810620840881b6d8060c41081116206c3619000002044704db0d8440000001180126db6d8000000045f84db4db60000000117a136db698000000045d84db6db400000001170126d36d8000000044d049b6d360000000116e136d3698000000044c84db6d260000000116c126db6d0000000045a04db6da4000000000140a6db4990000000020829b6d26400000000500a6d34d90000000020029b4da64000000007e0a6db49900000000af82db4d264000000007c0a6db4d1000000001e029b6da44000000004a0b6db4910010a2044186db0db04005e082102186db619001062085d061b6d86400000011d4136d36980000000474049b6db4000000a5164126d34810000028058849b0d24400000000580b6d36d90000021c4784db4c06400000000560b6db6d10000023047041b6c3440000001166136db4d8000000044a849b4d260000000104e126db490000002c800049b6d20000000b1000126c3498000002c810049b4d20000000b103c126c3490000000045084db4d34000000001420b6d34d1000002ac55049b4d04400000a9020126d3091000002a053841b4d2440000001014126db4980010a2044106db0d8640042883104186db6c1000000000e829b4d36400000000380a6d3699000000000d829b6d26400000000340b6d3499000000000c829b6d26400000000300a6db4d1000000000b829b6da44000000002c0b6db491000000045a84db4db42204188210e206d30018110423045881b0c044000000113c136d34d8000000044e84db6d34000000000420a6d3699000000000f829b6da4400000000400a6d3499000000000f029b6d2461041882102206c3401000000004f02db4d364000000013a0b6db4d100000000af02db6d36400000000000a6db499
def d10_1 : Nat := 0x3200c0010c8020446004e00000300000004800200488c0012c0000400000004942700c0e010c15802208082a04480046a084062a48720c0108002500c200c2010402080027c020
def h10_1 : Nat := 0x650890ad827374ec9b3a556a942119d1e000000000000ade000b3564327490d92213e000728000000d8f000000000b68000446000000b2463cb2195d54759ed6b876963000000000000000000000c8c7e40001e248727db0e5880000004a4dc6b3ac1a1a15076b1848000db3000000486294000000611000b09000a3b88e0000000003a6000000000bda00058967275ca92ab7c4174c7272369c85e3000000c31000000000dc500000000099959a13fdbb89d000000c7f897561253d6fa2a0006803d6cb5b2b4bd15f177d7a3a024b7a8000b5547c4d499574a2d1b0a91c271a2c2d77acdba1ce9afc75a57b5696500028b88d81fcdf6b62bf000525000179101000426423a96b2f7ae000000c5b000ccd00000099cc7b0009db000000954000ca2adc000000a3d000cbcac3a6dc7ede1a7895e2620003409029c9258b60a440003050000005150000000000000000005c16dd1d2cb99b24045d9d84593d20d5aa14349434d6e2b40007be2520000008033854a7198881883c1bb30bd0000000ccb6c422966c10b000412d4dd70d510001cf0007086598335b8a641c21c7c91337c18b4fd389cc3106c08ab545c6728a20c613b06ca9439b2d6ca6d5b82db031d73269f32e0008aa9e0aa38161ad9d3269d6671770f
def a10_2 : Nat := 0x7029b6d20400000000ec0a6d34190000000036829b6c244000000001a0a6c34990000000038821b4d2640446f61d15a26d30000111bd8744e89b0d0000446e8ad13a26c30800111ba2bb0681b4c2000446e89ec1a06c3480012c3a2b44e89b0c04004b0e8aec1a06d3010012c3a27b0681b0d0400445689ec1a06c30900000020c47841b4db040000088126136d30c10000021c4784db4c0640000083124106db4c1000002104884db0d3040000081124136c34190000020849841b4d8640000082122106db4190000020848041b6d844000008111c136c36110000022c4804db0c344000008c11c106db0d10000000407049b6d20000000010ec126d34180000000463049b6d04000000010ea126d30980000000436849b6c240000000101a126c34980000000438841b4d2600000001186106db4900000045055049b4d040000012b020126d30900000044c53841b4d240000017d2f8126d3081000005ecbd049b0d20400001792f0106d3481000005dcbb049b0d04400001752e8106d3411000005ccb9049b0c246204188210e206d30018410620840881b0d006044108c116206c3011
def d10_2 : Nat := 0x2010612190b100011423049
def h10_2 : Nat := 0x2040058323c9e24a5f25d3ec7a229b32d9130a4457622524006b24348506bba6d003698609945454b4b1387c000012a9154ac6a6800156000000000000000739de3ac00470d0730e63340000000
def a11_0 : Nat := 0x22c855869b4d36404080ab0d369b68808b11501b6db491011542a434da6da20229c5486db4da4404410be0db69a6c808821721b6db4d10114a0a434da69320228013069b6d244000096709369a6c800011c8126d3699000025f824db69320000471849b6da44000096609b6da48808b21401a6db4990102028034db6d22022c452869b6d264000094409b69a4c80001210126d36d10000250c24db69a2000048384db4da44045908b0d36db4c808b21181b6d36990116432c36db6932022c466069b6d36404588880d36db4c808a510e1a6d36d90114a20434db69b20229445869b6da64045288c0db69b4c808a51961b6db4990115622034da6db2022ac42069b6d364045588b0d36db68808ab1181b6d36d10115221034db6d32022a440869b6db4404500cc0d36da6c808a01101a6db6990114020c36db69320228043869b6db44045008c0db6db48808a81101b6d36990115021036db6932022a04386db4db44045408b0db6db48808cb2601b6db4910115428034db69a22000458869b6da4404538a50db69a4c808872741a6d36d10111046c34da6d320221c9f869b4db6004439370db69b680088c26e1b6d36d0011184d036db6d200221c84069b4db4004461070db69b480088226c1b6d34d10115432c36db69a20229c5006db6d24404538cc0db69a6c808ab1061b6d34d90115632c36db69a2022a06606db4d36404540810db6da68808b210e1a6d36d90116223036db6d22022ac61069b4db4004540c10db69b48008cc2ce1a6d34d80119659836db6920022a44106db4db4400008ab09369a6880001152126d3691000022a026da6922023309f869b4db6004438ba0d36db680088226e1b6d36d0011182f036da6d300232c9a06db6da42a8008a70db69a68808871841a6d36d00111830436da6d20022108c869b6d266c8008a70db69a4cd50011621a6db4d10115629034da69b0022ac51069b6d34004540a30db69a4c008a813e1b6db4900115423036da6da20229c4386db4db4404548c20d369b68008a91821b6d36900119829034da69b00220ca206db4d26004409430d36da680000119a136d34d10119627c36db69200233068869b6d36004660be0db69a6c008cb1a01b6db498011962e436db69a0022a44e069b4da60045489b0d36db48008831c01b6d34990110237834db69a2022944106db4d36404500820db6da68808881c81a6d3698011642a036da6930022a84186db4d36404588ab0d36da68008a71021b6db4d10116420836da69b2022c44106db6d34404590870d369b6c008b11181b6db690011104fc34da6db00220c5f06db4d36004418d00db6da4c008811a21a6db4d8011022e834db6da0022045c86db6d34004410be0db69a6c008821721b6db4d0011164d036db6d200204040869b6db4404080cb0db6db48808b21521a6d3698011622a434db6d216400458869b6d26404590810d36da6c808b11061b6db499011542a036da69a00220c5186db4d26004408a20d36da68008b21181b6d36980116432c36db6930022c466069b6d36004588870d36db68008842fc1a6db4980119822c34db6db2023304606db4db64044409c0d369b4c008881961b6db6990110821c34db6db2022104606db6da6404438cb0db6db688088b1361a6db6900116420836da69b0022a84606db4db4004588820db6da68008a710e1b6d36d00000250824da69b2000049804db6d244000090609369a6c8000120a126db4990000241026db6922022c45406db6d240045508b0d36db68808a71101b6d36990115628436da69a0022a05086db4d34004440bc0db69b4c0088b1741a6db6d00115432c36db69a00229c6606db4d360045289c0d369b4c008a01361a6db6900000223026da6d22000049b04db4d34404528a30db69a4c008a01441a6db4d00119832c36db69b3620045386db6d24400008c209369b6880001182136d36910000246c24da6d320000499849b6da46a8008100d369b688800114e1b6d36910114a29034da69b0022804f86db6d240045908b0d36db4c008b11101a6db6980111021434db6d300222c42869b6da6004528940d36da4c008a01281a6db4980110825034db6930000049d049b4db44000093109b69b4880001194126d36990000232426da69320000464049b4db4400008c70936da6880001188136d3691010202ac34da6da0020405406db4da4004418870db69b6c808811181b6db6d10000233024da69b2000046584db6d24404080840d36db4c808aa1521a6d36d00114e2a436da6d200222040869b6db64044188b0db6db4c80001232126db4980110834036db6930022c852869b4d20404588a00d361a4880001284126d34d80000246c24da6d30000049d049b4db4000009330936db4800001262136d3690000024c026db69216400408069b4da6040008b10d36db48008101521a6d30910110428436da69a00000444049b4da64000088b0936db48808b21401a6db4980102020836da6da2022c452869b6d260000088309b69a4c80001102126db4d10115421034db69b20000483049b4d36000009050936da4c590011621a6db4980000241026db6920000047004db4d26400008de0936da68808a7150186d34910000229024da69b2000044e049b4da6400008a309b69a4c80001144126db4d10000226c24db6d22000044f84db6d244000097e0936da4c0088219a1b6d34d00116420434db69b00204066069b4db6004080cb0db6db48008b11061b6db4980000259c24da69b000004b304db6d242c8008a70db69a4c550011621a6db4d00110620436db69b2000044104db4d34404420850d36db4c000b2154126d34d90016229c26db69236400455069b4d362c4008a70db6da48008aa1101a6d36d90000229824da6d220233044069b4db0404458cb0db61b4880001108126db499000020a424da69300000413049b6d24000008ac09b69a6880001232126db4990115433034da68320229c65861b6d246a8008100d369b685500114e1b6d34d01000229c36da6d20000045084db4d344000094409b69a4c008871041b6d36110000250c24db69a00220846061b4db4404080a50d369b4c008101401a6db6900000242024da6da0000048384db4da4000008ca09369b4c00001190126d36d00000231424db6d20000049b04db4d34004550a00d36da68008a714a1b6d3498001642a824da69b0002c45384db6d24000008c909b69a4c0000127e126d36d8000024dc26da6da0000049a04db6da40005501009369b68808aa14a1a6d34d80002029c26da6d220204045869b6c24404538a00db6da48008841041b6db4d90102020836da6da0000044a049b6d264000093f09369b6c8000126e136d36d1000024d026db6d22022204186db4da04044088b0d361b688000115e126d34d1000022b826da6922022c842069b6d20404588840d361a4c800011c8126d36980000238c24db6d20000047004db4d260044393a0d369b68000011bc126db4d0011184c436da6d20022a840869b6d04404538830c369a4c808cc2841a6d34d8011964c036db6920023304606db4db6004438cb0db6db680088810e1a6d30d90111623036db6122022a84186db4d360045508b0d36db68008a71101b6d36980114e20436db69a0000045e04db4da6400008ba0936db68808ab1181b6d36d00115021c36da6da00000459049b4d26400008b10936da48808a914c1a6d36900119832c36db69b0022204106db4db64044108b0db6db68808aa1981a6d34180114e32c30db6920020404186db4da6004080810d36db6800001184126d36d00000230426da6d20000045f04db4d36000008bc09b69b4c00001174126db6d0000022e426db69a0022ac6586db6d34004540cc0db69a6c0000114c126d3690000022f826da69b2000045c84db6d34404558830db69a6c008ab1501b6d34d00115020436db69a0022104186db6d20404420810d361a6c800011a2126db4d90000234026db6932022208d869b4da6004411360db69a680088b2661a6db690000020a424da69320000413049b6d24404421190d36da4c00001020126d36910000234424db69b0000046804db6d26004558af0d369a68008a815c1b6d3490011542ac34da68200229c54061b4d24004418870db69b6c008811181b6db6d00114a21c34da6db0022804606db6da4004590a50d369a40008b11401a6c34900115233034da6db0022a46586db6da4004558a90d369b68008a91501b6d36900000221424db6d320220c41061b4d36404408820db6da08808a50521a6d34980114009834db6920022944606db4da6004500870d36db6800001154126d34d10000229c26da6922002a808049b4db4000080a709b69b48008ab1101a6d36d80115022c36db6d200000457849b4d34000008ae09b69a48008cc1161a6db6d80111032c36db6d300204054869b4c240045588b0d36db68008a81101b6d36980116221034d869300221043869b6db60044208c0db6db4c008a91061b6d36980115220434db6da0022a844069b4db6000008ac09b69a68008a51961b6db4980114a2a434da6d30022a450069b6da4004500cc0d36da6c008a51501b6d34980115628034db69a00000452049b4d360000089f09b6da48008a51561a6d34d8011402a036db6920000045184db4d26000008a20936da680000119a136d34d00115420434db68200229c41861b4d26004528810d36da6c008a51161a6db6980114022034db6d30022804186db6d26004550840d36da6c008a71081b6db4980000228426da69a00221c4106db4d840044108c0c369b68008a91041b6d36d00114a20836da69b0022ac42069b6d36004500820db6da68008a81081b6db4980102022034da61300204045869b6c24004528a00d36da4c00001138126d36980000226c24db6d200204089069b4da4004548840d36db4c0088810e1a6d30d80111623036db61200220c7006db4d26004408de0d36da68008831021b6db4d8000022c024da6d200233044069b4db0004458cb0db61b4800001040126d34990000207824db69220204042069b6da6004528200d369a4c008a003c1a6db490000023c824da69a0000047884db4d24004420820db6da6c008881021a6db6d80110622c36db6d300000442849b6da6000008000936da4c80883104186d34d80110220836db6820022204106db4db60044108b0db6db68008881061b6d36800110222c34d86da0022104186db6d20004420810d361a6c008840001a6db4980000225024db69300000410049b4d260000081e0936da4800001000126db498
def d11_0 : Nat := 0x62080248000080a0034400008101d8000000000010054a01d000002000401200000352200c0048402020021280001c00330000800008000094a6780042881408860180170800008140008080940028045081010144001822100000040d180002807210063b00a0000200004058484034a0000410844148000118030804100400000421242018ca000ca008801280200802100000680a0
def h11_0 : Nat := 0x255ac3dcece30698e65a5adebbac4a0000000000001ad50000000001990000442c000000000000000000074d6e70e9540611d9cd40000000000001c70eb40000002732379376b9ba81adb57719c9c49773c44dca39d22bb700014e289125ece10000cd20003d2484eb34000255196133c8983bd3b70000000b72dafc000000aec10f09a48d69d2ab5c8ad42813bc6800006f01ea4b85cc20000005bca1120000000cdd198fe26a241f5e0fb2d999c43400000021f61a3032e5f9e73175f96545c4120d21d892074980029a60003528000d44000944645b7980000000000000000da31a6720945545db285ad9b6800008d88d60008b3000055c00000000005e2000529c09f6bedc55ba5c748c03d000038161535aeacd80000000000006e540013119d180000000007b5d905e20dd32a944b000134eadc1468001af6000000000000069880000000000006ed0000000a0f80000000007ee80017c000014a232c000000827662ef11833340c6c73240004cb598d092ab7653b49b0a20001bf000052f1705c9e20c000a7ed236cf458cac00005d8304867c291606e99269000000014340004b6800000056300065c95bc4f8a618002ce1a80595400ce396fa9944b4306f3bc3abeaface861c6466e525f71e1775a84400000037bcd9e02e56a0004d62c6a89c1524d527060009bfd80400000078c0000a812db86cd022e43b341c21136fa32f91156e8888afaab07936ab94000d8fa0e6874c2dbd780024c40000003a76a740000001450001079682a6b49ff97500000035e8a9e614d9a80011c7665144f12d00718ac4ff66d2c200041e00000000000000001a2e3b2c03842cb567a580000000001c0974a0ea0006dd5dd914d8ba311c345ac3a1d64966e6704ed4236be9c0014864a600032b3a547190002f199dfd732ef800170933b6704000f97b4551c603d7c03a9e5f4fad42c3920003460a7b95aad7400094f3b1269a50f9c3ceb8000000000b7ea646cb8000c6fdf55db1add62800012874e4166c46cf67a202620eb2e1c2bc9e6cd24000cb20002ae531312b000394b0e55b647e00030309e3000563a331ba90003b200000002bdb495a532c55bc000299ef770001719e5f07f00018840007b2000000079e0007dd93cc001b6e842c76c89e000d7448fea06000000648c0000000004422d6227aba13dbe6c8751cbe361c8cf2599aada8d15970000016a000138f82bc90e82179dc362d410de3bf00045cc0000000005b3a88068d35b3810000f19a04882dc2a4e0a8645c4b1a76965c0909eb9095cc30cf9a5d8e700031905d35da939aec1c455a1833692b13f9485093aae205b3bc7564ca15102b00008c5516000c8bad1f70a000677ace648e7c9732d0bde252a0780d77237aafe171000320d5abcaf00011664bd2ad4e2878894d7983abed1ec14d13602a0040000005600a3d0b07a0a91110980cacfaf219eb9de0002932cb6b0f0001c28000000
def a11_1 : Nat := 0xa4146136d34d9528ab1421b6d34d8000a213e136db4d1500a81421b6db4d0660d11101a6db6c1660be1101b6d36c16608810a1a6db6c1660881781b6d36c14413f1061b6d36c1440851061b6db6814408510e1a6db0d9440bc104186d36d94408317c1b6d36c1440831a01b6db681440871741a6db0d94408726e1b6d30d900088286126db6d94408217c1b6d36c10017e104136db4d9420d11061b6db4c1420851061b6db681420851021a6c36d94208317c1b6db4c1420811721b6c34d900144116136db699418bc104186d36d9418d0104186db4d941882172186db4d94393f1041b6d3619438ba1041b6db611408d11041b6db419408d11161a6c36d94088217c1b6db4194088226e1b6db6114088b10a1a6c36d94088b2681b6c36d1410be118186d36d9410b91161b6c36d14108c178186d36d94108c268186db6d1458851961b6c3699458ba1961b6c36d14588c1781b6db0994588c26e1b6db0d1458cb1a01b6c3699458cb1721b6c36d1008b210e1a6d36d8008b21961b6db498008b11981a6db4d8008b11181b6db690008cc27e1a6d36d8008841a21a6db4d8008841a01b6db4980088727e1a6d36d80088726e1b6d36d00088217c1b6d34d8008821721b6db4d00088b1741a6db6d00088c2681b6db690008cb2681b6db690000aa152126d36d100010156126d36d100010150136d36910001014e136d3691000b114e136db491000a7152136d36910008dd44126db4c146eab1521a6d36c00008dd3e136db48146ea01501b6db48046ea81161b6db6810008de6e136d36c146e871041b6d36010008de68136db68146e8b1961b6c3681b0ea91501b6d3610b0ea01501b6db410b0ea81161b6db61100161d78136d3619b0e881061b6d360100161da0136db419b0e831161b6db61900161e68136db6110008ad48126d30d90008ad46136d30990008ad44126db0d10008ad3e136db0910008ada2126db0d90008ada0136db09900089d48126c34d900089d46136c349944ea51561a6c34d844eab1101a6c36d944ea91501b6c369000089e7e126c36d944ecc1101a6c36c100089e6e136c36d144e82118186c36d1b06a5156186d34d8b06ab152186d36d0b06ab110186d36d900160e7e106d36d900160da2106db4d9b0688102186db6d900160d74106db6d1b0681116186c36d1000a5266126db699000a5262136d3699000a6104136d36d1000a0236126db699000a0274126db6d1000a0262136db69100142116126db6d90011b138126d36990011b27e126d36d90011b178136d369900088260136db699001191a2126db4d9001191a0136db49900084274126db6d900084262136db699000e0288136d34990013a184126d36d1000de286126db4d10013617c136d34d90013626e136d36d100136172136db4d100133136126db69100133174126db6d100133268136db69100131182136d369100001156126d34d100001150136d3491b0e010201a6d3610456011541a6d30d04560114e1b6d3090b0601020186d36900000115e126d34d146f61d961b6db40146e8ad501b6d308146e89d561a6c34c146e89d501b6c348146e89d0e1a6c36c146f60d02186db4c1b0e8ad081a6db019b0e8ad061b6d3019b0e89d061b6c341945689d561a6c30d145689d061b6c309945760d08186db09944f60d98186c34d944f60d0e186c36d1000a417c136d34d9660a41101a6d36c1660881381a6d36c14409c1061b6d36814409c10e1a6d30d9440831461b6d3681440871841a6d30d9420941061b6db481420941021a6c34d900084288136db481420831461b6db48100084286126c34d9420811441a6c34d900144102136db4d9000a317c136d34d9418a3104186d34d900083286136db4d9438c21041b6d3611438821421b6d3611000a2172136db4d1408a21041b6db411408a21161a6c36d14088b1361a6c36d1410a1118186d36d14108c182186d36d14589b1181b6db0914589b1961b6c36914588c1821b6db091458cb13e1b6c36910009f172136db4d1008b21041b6d34d8008b21161a6db698008b21181b6d3698008aa1181b6d36d0008aa1961b6db4d0008b11101a6db698008b110e1a6db6d0008b11041b6db4d0008a71981b6d34d8008a710e1b6d36d0008cc1a21a6db4d8008cc17c1b6d34d8008871741a6db6d00088c1781b6d3698008cb1a01b6db498008cb1721b6db4d0008a71401b6db4900088219a1b6d34d00013619a136d34d10000114c126d369100161e36126d36190008ae6c136d30d100160e66106db69100010104136d36d1008841281a6db49846ea91041b6d36c1b0e841061b6db40144ea91041b6c36d1b0684102186c34d900029146136d3499000a6184126d36d1000a6182136d369100026144126db4d100119104136db4d90008426c136db4d900083274136d36d900081262136db6d100001164126d349900001162126db49100001118136d3691b0e0114e1b6d341000961d181b6d361000889d181b6c3690b0601154186d34d000960d0e186d36d00008dd54126d34c10008dc20126d36810088dd521a6d36810088dd041b6d34c100961d521a6d361100089c20126c369100089d4e136c349100889d521a6c369100960d52186d369146f61d501b6d340146e89d521a6c36810008dc4c126db4810008de6c136d34c100161d4c126d361100161c4c126db41100161e66126db6110008ac52126d30990008ac4c126db09144f60d56186c34d100089c52126c349900089e6c136c34d100160c52106d349900160d4c106d369100160e36106d36990088dec39a6d34000088dd159a6d30800088dd139a6c34800088dec1986d348000961d159a6d301000961d139a6c341000961ec1986d34100088ad139a6c30900088aec1986d309000889ec1986c34900088dec39a6d34010088dd139a6c34810088dec1986d348100961d159a6d301100961d139a6c341100961ec1986d34110088aec1986d309100889ec1986c3491000a4142136d34d9000a2142136db4d1000a113e136db4d10088810a1a6db6980088410a1a6db6980088b10a1a6db698000b2162126db499008b21081a6db481008a51461b6d3498008a91841a6d36d0008a91821b6d3690008a01441a6db4d0008cc1481a6d34d8008881381a6d36980088b1361a6db690008cb13e1b6db49000161d36126db6110008ad7c136d30d90008ad72136db0d100089d38126c369900160d38106d3699000a51bc126db4d9000af118136d36d1000ab1c0136d34d9000a91c0136d3699000a91bc126db6d1000a01c0136db499000ae10e136d36d1000a81bc136db4d10011b104136d36d900088274126d30d90008826c136d36d90013a104136d36110008726c136d361100136118106d36d100136116136db6d100082262106d36d100082266136db6d100133118136db0910008b262136db0910008dd4e136d348100161c20126d361100089d54126c34d100160c20106d36910008dd4c126d36810008de66126db68100161e32126db41900089d4c126c369100089e36126c369900160c4c106db49100160e32106db499528811041b6db4195288b1181b6db099558841061b6db4c15588b1181b6db0d1548841061b6db681548841021a6c36d954883104186d36d9548811041b6db6115008810e1a6db0d950083104186db4d95408810e1b6d30d9540841021b6c34d94208310e1b6db6c1420811181b6c36d9420871041b6db61942082118186db6d9000cd142136d34d1000a117c136d34d9000a1172136db4d10088317c1b6d34d8008811a21a6db4d8008811741a6db6d0008811721b6db4d0000b2156126d34d8000b2140126db4990001014a126d369900010140126db691000b114a126db499000b1150136db490008cc2ce1a6d34d80088810e1a6d30d900883104186d34d9008871841a6d36d0008811041b6db4110088b1181b6db0910088c1821b6d3690008cb2cc1b6db49046ea91501b6d368044eab1521a6c36d0558a914c1a6d36d0000ab232126db4d9548a61501b6d3690000a8232136db4990014227e126d36d9001421a2126db4d90014217c136d34d90011b106136d3681000881bc126db6d900119106136db48100119102126c34d9000e0116136db6990013a27e126d36d90013a174126db6d100081266126c36d100131178136d36990013126e136d36d100131268136db691001301a0136db49900130172136db4d100130268136db69100001154126d34d100001020126d36910000114e136d34910088dd021a6db4c10088dd961b6db48100961d061b6d341900961d961b6db4110008ad54126d30d10008ad4e136d30910088ad981a6d30d90088ad061b6d30990088ad021a6db0d10088ad041b6d30d10088ad961b6db09100889d981a6c34d900889d061b6c349900960d98186d34d900960d02186db4d100001262136d369146f61d161a6db60146e8ad041b6d30c10008dd5e126d34c10008ddbc126db4c100161dc0136d341945689d041b6c30d10008ad5c136d30910008ae32126db0990008adc0136d30990008adbc126db0d144f60d10186c369900089d5c136c349100089dc0136c349900160dbc106db4d14388219a1b6d36114088219a1b6db411410cd118186d36d15900114e1b6d3498550011621a6db4d0000b2102126db4d900010106136d369900010102126db6d100010196136db691000b1106136db499008832881b6d3498008812861a6db4d000029148126d34d9528291561a6d34d80002613e136db491500261501b6db490000881c0136d3681000841c0136db481000de116126c36d100001152126d369100001104136d34d100160d54106d34d10008dd5c136d348100089d5e126c34d100160d5e106d34d1440bc10e1b6d30d94388217c1b6d3619410b9118186db6d1458ba1181b6db0d100001184126d36d10088b1c61a6db6900008dd74126db6c100161d0a126db61900160d0a106db6990088ad041b6d30d000889d0e1a6c36d000001052126d34990000104c126db491000e4102126db6d9590010201a6d3698080011621a6db690000aa106136d34d9000a7102136db4d1008831461b6d3498008811441a6db4d000029196136db499000ab14c126d36d1000a6150136d369100026198126db4d90011b102126db6d9000e0146136d349900083266136db699000de144126db4d100001284126d34d900001236126d369900001266126db69100001260136db491008aa1061b6d34d8008a71021b6db4d0000aa140126db4d1008a51381a6d3698008ab1841a6d36d0008a01361a6db690008a81821b6d3690008cc1101a6d36c1008881061b6d3681008811161a6c36d1008821421b6d34d00088b1961b6c369100029102126db4d9000a6198126d36d9000a6106136d3699000a6102126db6d1000a6196136db69100026106136db499661421101a6d36c1660882361a6d36c14411b1061b6d36814411b10e1a6d30d9440872741a6d30d9001192fc126db499421191061b6db481421191021a6c34d94188226c186d34d94393a1041b6d36114388226c1b6d36114088226c1b6db4114088b2661a6c36d141136118186d36d14108c262186d36d1459331181b6db0914588c2621b6db091458cb2601b6c36910088ad981a6d30d80088ad961b6db0900088dd401a6db4810088dd161a6db68100961d4a1a6d341900961d401a6db41100961d101a6d361900961d161a6db6110088ad4a1a6d30990088ad401a6db09100889d4a1a6c349900889d101a6c369900960d4a186d349900960d40186db49100960d10186d369900960d16186db69146e89d041b6c34c1590011541a6d34d8008101041b6d36d05880114e1b6db490000aa152126d36d0000aa116126db6d1000a7152136d3690000a7110136d3699000012ce126d34d8000012cc136db4900008dd72136db4c10008ad42136d30d100089d7c136c34d9528ab15e1a6d34d8000a9232126db699500a815c1b6db490000e010e136d36d9000e0102136db4d9000831bc136db4d9000de118136db6d100001198126d34d900001196136db491000011c0136d3499528ab1401a6db4d8528ab1501b6d34d8528a91501b6d3698528a01501b6db498558a91401a6db6d0558a01501b6db4d0590011621a6db49800010156126d36d000010150136d3690000011c8126d369800001288136d349800001210126d36d000001286126db4d0000011c6126db6900000120e136d3690558af1521a6d36d0548a815c1b6d36900088dd041b6d34c0550010201a6d36d05500114e1b6d34d00800114e1b6d369000029138126d3699000af150136d34d1000ab15c136d34d100026136126db691000e017c136d34d9000e0178136d3699000e01a0136db499000de1a2126db4d9000de174126db6d1000de172136db4d100001106136d349900001102126db4d10000126c136d34d1000a4152126d36d9000a4140126db4d9000a4116126db6d90009c156126d36d80009c140126db6990009c150136d36990009c102126db6d900094156126db4d900094152126db69900094150136db4990009410e126db6d900094118136db699000a3152136d3699000a3140136db499000a310e136d36d9000a3116136db699000a5184126d36d9000a5144126db4d9000a5136126db699000a5182136d3699000a513e136db499000a5174126db6d9000a526e136d36d9000a5268136db699000c2140126db6d1000c2150136d36d1000c2108126db6d9000c2106136d36d9000c2196136db6d1000a2152126db6d1000a2110126db6d9000a2118136db6d1000a1152136d36d0000a1110136d36d9000a1116136db6d1000ab136126db6d1000ab182136d36d1000ab10a126db6d9000ab178136d36d9000ab268136db6d10009b150136db6900009b198126db6d90009b106136db699000c1140136db691000c1198136d36d9000c1108136db699000c1102136db6d1000a913e136db691000a917c136d36d9000a9172136db6d10009f110136db6990009f10e136db6d1000a027e126db6d9000a0178136db699000a026e136db6d1000a827e136d36d9000a810a136db699000a8174136db6d10013f196136db6d9000d1118136db6d9000be116136db6d9000cc268136db6d900088172136db6d9000d010e136db6d90008426e136db6d941882142186d34d9408821421b6db411008cc1181b6d36d8008871961b6db6d00008dd42136d34c100089d42136c34d10011b10a126db6990011910a126db6990008326c106d34d90008126c136db4110013310a126db6990088dd961b6db48000961d961b6db41000889d981a6c34d800960d98186d34d80088dd561a6d34c000961d501b6d341000889d501b6c349000960d56186d34d0000e0104106d34d9000de104136db411008101081a6db698008cc1161a6db6d8008cc1961b6db4d8008881961b6db6980088410e1a6db6d8008841181b6db698008a510e1a6d36d8008a51181b6d3698008a91381a6d3698008a91361a6db690008a010e1a6db6d0008a01181b6db69000029156126d34d8000af106136d34d9000af196136db4d100026150136db490000ae198136d34d9000ae102136db4d10088dd501b6d348000961d521a6d36100088ad561a6d30d00088ad501b6d309000889d561a6c34d00009c156126d36d9000a1152136d36d10009b150136db691000a91a2126db6d9000a91a0136db69900010108126db699000a7140136db491008a51481a6d34d8008ab1421b6d34d000001142136d34d1008a013e1b6db490008a81421b6d34d0000012fc126db49800029116126db69900026110126db69900001110126d369900001116126db6910008319a106d34d90008119a136db411000aa14a126d34d8000a7140136db49000029150136d3499000ab04c126db4d10088dd021a6db4c000961d101a6d361800961d061b6d34180088ad061b6d30980088ad021a6db0d000889d061b6c349800960d02186db4d000960d16186db6900088dd521a6d368000889d521a6c36900008419a136db4d9000af184126d36d1000a6150136d3690000ae182136d369100001232126db499528ab1521a6d36d8558a91501b6d36d0548a01501b6db690008b21021a6db4d8008aa1161a6db6d0008101981a6d36d8008101961b6db690008b11061b6db498008a71101b6d3698008a51961b6db498008ab1481a6d34d8008ab1441a6db4d0008a01981a6db4d8008a81461b6d3498008a813e1b6db490000af152126d36d1000a915c136d3691000e4104136d36d9000821c6136db6d1008842fc1a6db4980000119a136d34d000029156126d34d9000af116126db6d100026150136db491000ae110136d3699440831c01b6d3681420831c01b6db481420811bc1a6c34d9418e0104186d34d9408de1041b6db411408de1161a6c36d1008a51041b6d34d8008ab1181b6d36d0008a01041b6db4d0008a810e1b6d36d0008841061b6db481008841021a6c34d946e82118186d36c144e871041b6c3611000af152126d36d0000a915c136d369000961d161a6db61000960d10186d369800961d081a6db4190088ad081a6db09900960d08186db499000b2154126d34d8008101061b6d3698008101021a6db6d0000b114e136db490008a51281a6db498008a51161a6db698008a01281a6db498008a01101a6db69846e8b1181b6db081456841061b6db081456841021a6c30d945683104186d30d9456811041b6db01100961d4a1a6d341800960d40186db4900000114c126d3690008aa1561a6d3410008a7150186d3490000af110126d36d9000ae116136db6910000114a126d3499000a4150136d34d9000a4196136db4d90009c104136d36d9000a3156136d34d9000a5172136db4d9000a2150136db4d1000a2106136db4d9000ab13e136db4d1000ab1a0136db4d90009b104136db6d10009f198136db4d9000a017c136db4d9000a81a2136db4d90000020c0a6d34d90000020a0a6db499000002080b6db491008a91981a6d36d8008a91961b6db69046e811161a6c36c144e881061b6c368100029152126d3699000af142136d34d1000a904c126db691000ae142136d34d10088dd161a6db68000889d101a6c36980008819a136d36d9000cd116136db6d1008aa1101a6d36d8008aa1081a6db4d8008a71081b6db498008a71161b6db690008101521a6d3090008a91041b6d36d046e811041b6db40146e811181b6db6c1456831021b6db0d944e83104186c34d944e8310e1b6c36d90088dd401a6db48000961d401a6db4100088ad4a1a6d30980088ad401a6db09000889d4a1a6c349800960d4a186d3498000001640a6d3499000001620a6db491008881021a6db6d8008831161b6db698008a51021a6db4d8008ab1961b6db4d0008a91061b6d3698008a01061b6db498008a81981b6d34d8456841041b6db0d9000aa110126d36d9000a7116136db69100001148126d34d900001146136d3499008ab1161a6db6d000001144126db4d10000113e136db491008a81101b6d36980000127e126d36d900001268136db6910000115e126d34d00000115c136d3490000a514c126d3699000a6140126db69100001284126d34d800001274126d36d000001262136d369000001260136db490440831021b6db6c1418811161b6c36d9008aa1981a6d3418008a7196186db490000001940a6d36990000018a0a6db691008ab1061b6d34d8008a81021b6db4d000961d081a6db41800960d08186db498000a5142136d34d9000a1108136db4d9000aa198126d3419000a7196106db49100001052126d34980000104c126db490000b2108126db481000b1108126c3499008ab1501b6d34d0000a515c136d3499000af140126db4d1000aa108126db4d9000a7108136db499000a515e126d34d8000a015c136db49000094104136db4d90000120c126d34d80000120a126db49800001208136db49000001178136d369900001174126db6d10000126e136d36d10088ad081a6db098000a515e126d34d9000a6138126d3699000a6136126db691000a015c136db49100001108126db499000001920b6d3499000001900a6d36d10000018e0a6db4d1000001880b6d3691008ab1101a6d36d8008a81161b6db69000083174136db6d9000aa020126d36d00001014e136d369000029128126db49900026128126db499000001520a6d3691000be110136d36c1000b9116136c36d1008a51521a6d3698008a51501b6d3498008ab1521a6d36d0008ab1401a6db4d0008a91401a6db690008a91501b6d36900000117c136d34d900001172136db4d146e821161b6db6c144e881041b6c36d900029140126db499000a504c126db499000af148126d34d9000af144126db4d1000ae146136d3499000ae13e136db4910000014a0a6d3499000001560a6d34d1000001400a6db491000001500b6d3491000001540a6d34d10000014e0b6d349100001138126d369900001136126db691000b214a126d3481008b214a1a6d3480000b1140126c3491008b11401a6c3490000af108126db4d9000ae108136db499000001700a6d36d90000016e0b6d36990000016c0a6db6d10000016a0b6d36d1000001680b6db691008841041b6db4d80088310e1b6d36d8008811181b6db6d0008ab1081a6db4d8008a81081b6db498000001980a6d34d9000001960b6db49100001236126d36980000126c136d34d000001266126db69000001194126d369800001192136d349800001190126d36d00000118e126db4d000001158136d34d00000118a126db69000001188136d3690000aa102126db41100010110126d309900010116126db091000a7106106d3499008aa1021a6db410008a7106186d3498000a6108126db699008101101a6d3098008101161a6db090008831021b6db4d800001232126db498000011c0136d3498000011bc126db4d0008a51561a6d34d8008a01501b6db4900000010e0a6d36d1000001180b6d3691000011a2126db4d9000011a0136db499008a51401a6db498008cc1101a6d36c0008881041b6d36d8008871041b6d361000882118186d36d00088b1961b6c36900088810e1a6d30d80088b1181b6db090000bc104106d36d9000ba104136db611000001580b6d34d1008b21081a6db480008b11081a6c34980000110a126db699000001800a6db6d90000017e0b6d36d90000017a0b6db699000001760b6db6d10000127e126d36d800001268136db69000010152126d3091008a91081a6db698000aa156126d3411000a7150106d3491000001060b6d3499000001020a6db4d1000001300a6db6990000126e136d36d0000001100a6d3699000001080a6db499000001160a6db6914408310e1b6d30c14088b1181b6c30d1440811041b6db61941882116186db6d900001184126d36d000001182136d3690000001340a6db4d9000001320b6db49900001178136d369800001174126db6d04188210e186d361940882118186db611000001660b6db4d900085102126c36d900085106136db68100085104136db6d9008881061b6d3680008811161a6c36d000001138126d369800001136126db690008841061b6db480008841021a6c34d800883104186d34d8008811041b6db410000001040b6d34d1000011a2126db4d80000117c136d34d80000110a126db698000011a0136db49800001172136db4d000001148126d34d800001146136d349800001144126db4d00000113e136db49000001128126db4990000013c0b6d34d90000013a0b6db4d100001128126db498420831021b6c34c142083104186db4c1420811041b6c3419440871041b6d30194108c116186db0d144083104186d36c1408821161b6c361141882102186db41900001142136d34d00008312e136134990008112c120db4d10000011e0b6d36d90000011c0b6db6d1000000400a6d34990000003c0a6db49100001040126d34980000103c126db490000000000a6db49900001000126db498
def d11_1 : Nat := 0x800000030140000801000620061800001000017c007004116140500400010010500c0900000c0009ce40000500800000030280100801004270000000002004000040b0000100003008010000e8a4034e808000160080004c0001401000cf00a340040000037000010000000c000041d02c001e4010054c0250b508000154f00400000000081000800004070180401c311cc7e0400a000000001a02801000180680912001001f9014040001b000000000100000028001a01900829014020400004405038000001500401000000000000a0000401004010040600051000010000000833000017e0024700500004004000dc00008001cc000a8070001400c1c0185d000000000004400000e300000000000000300807000000500000190000010000000000018070000213c0087c0000403000120000000400008050040b0dc000000401c020100000025008010000134c000487c0003200003004000045c000050043a06400000000004400002004010083100000014000001f004020dc02018050059c01c00004000040000000018100600000400000000000000013000004c8220ec02000004493600c01024000040100000010010010a000000040102401000000100c0d403001b702c03040003080035000044050001d01817174030740006000000180000100627018030041402e260340000062584030a801008040040000404029c57ec000004101000000000000101c000600079c0100400000000240100002000007240324404010000000000c000080b01400010040000000002010010080000184658aa00002000090640100000000020000100029114010116f8a4083101c000000000100019084001400000021004180000201800000008140b00000004030c93a01c1f0000a0140001000000050080400000004000c4590200e
def h11_1 : Nat := 0x322000000000000b0d200029b5800000010f7000020ca7508905e57ee429000089640000000311a0002c8153b8240442944f9b89a309baad68604b47c32caf400000a56922a00011e40000b5110570000343000000000000000000004482ce58000000000000000b83744e80cc00053ea00000000dd5c2ca37606b37047c411d8384c6c0004901000000020fc1b8f00000000000000000000001ce8abf4c348000000042f746e6857507499220000000249c800000000000000293100008674000599e216f26ad1bf800056fc29fd469d0bed7a3ae871f14242c0cda87a593a9d0b76987a40000000000102b8000334e00000000ceab0fb539a00000000000d425a1fc000000000000001922a9ae000000024fd00000001a7f0d1d8000d38c00000000000d0a800000004059d341a0480000000000107ec00012a150ec00000000000a83e000153f13bf2384440c0000000d210000181b800036020000000000000016f94d7180008618000000000000000000000000000000e8240002129534e871000031e381300001cb50b60b6992592a061b3790360000000000097e48af68b4893b818562e90c3ca87b5b189e710e5c25a13840da963da0a935000024a1424675538ad88e952c6708600000006222c35e00000006b77c2b200000005190a0aac37c50d0000c6580000d4600000000000000039a9000103721e90000a1ec00015a4242360bcce34c39cbacb79a4ac74b062d212d62ee9464383e54330358000634900000002a17000000000002d544b52b3186c8d8d95be3a8408978c3d421f667f64bb5c3d906b5282460d7d4a0dd83528e00000000b587903c0001b2d00000000d3b6be00000833f43b8000a45a000058a0000342848c61ff586f0000c2fde0162a632ae000000000000001305800000000000412e141d3ffa4640000000118b1004e01e4d5123c00018778000000084580000000434f569b8c5c000093da684276c47e8000000000029352a780000a03400060ea21640000000203f17ae00000000000128e0000000000054ce0001919800000000000000088c0000e5680000000000000024e9e244000000000000000000060f36156a7a00004f040000000a033847a92e000000000000000000000000002c3d80000000c59a4b89b67000082ce5430000138a0000000000000000000000000010744b328188000b2aa00000000000179e0002c97cbd9b08000000002bee0001207dc628000000086b400000000000804c836d0f40001621d526800082f60000000000090e085460c722c900016c240000000000000000006c2d000000000000000c55800021a080000001a0864a60000000000000000000000000009ccd04e814c00000000b0b00006344000631f960ac4900004132500d6588d62b3f671080001d90e9970000000047f29300000000319c0000621ea046218c937000049b08230000664400018696858000000000003893000000000002c0900000000c7d0000000025040000000814600000005bf90000000000000000000e19dd14980900016dec4cc000000012a170411aab0000664e9c93bb70000edb00000000352ca0ad4622c080000000351f8000806a00031d3c0c10000000000011b5b66220ee9a2bb5ad2248b3c0000000000000030d28000a15200000001b3975460000000604400012d744f7c20b00000001507800000018e18000000000000000000000000012ba800000000000eac000020d853690384dc08000c2a96e78000312d000000000001302519a000117f0000c04cc8c203f341943048b749993299000000000000000380a0003438cbeb85796ab8000419ca62b6e6c00000000000000000068d90000000354c239822ac8b080000000338000000000a13765d0f0b471a1fe000000020fb6b2000002aaa1658000000000000001c100000c47c4a2000000018e310e60000857600000004b8b000000000000000630963550050000000000021e7000047deabb80000000474600004a5000000010aca9dde85117f685251c74092131e000000000000000000000000002328cdea8f8da820000e9840001852000000000000000a37500c15578000000000024a30c28784830889fabc0d85756f58dfeebfcd3d42fb49f6324fd7978f1a9a1e353d786eab75fc095397894ef21ca4b80821d0e931be8958318dadca03ce37176bd8dc24804b9aa6d10d5a19aa330701082a91890965961eec34d804003a4b72be196f22d59572aa4f5330ad0978e625d9d4ca90c513609d0504943834389c1cf34a6836f0e56dd31602e94a7092f1621aef17bdacecdb7225fa2da41770d6093826b1489a1a31ab753fe4884482b21b2615885b0b7d064d7ab20aa50709e493b4c73c4db39458215018d5a04b4a81aea5b3423a12a27274afe09b6057609250ce8889ab39084e78712aabe911d79062d3a6ae0c8162466a1aa0839400ef30470589ec236e6ef1883c01675b269a484882c62c7a5fd524d35034406c1283a2bfa82674b0712ee86ed77d83a207308b674c90b91d7e0af1b84ee2018cc8a52800840b744c999a906565c85065ba5273f46dec100a91964accf1deec8b9146ca33a8146178c3102c7252c592c21232a3849f23e7b7eec4775edc05a705f23de108b07842974d9a4e74ae5739582b04e419be2780ebc986e8a25629a8a065c23b16224aa94100b11893120e68acdea13a95d0c31c934a3a8757da30e425514071fe2f6a91bea9591376ccd9db622a363b4ae34c6c095d01682f68b0b311d24f30285256041d6c269021495085681cf0574a7883d47c260e4ce4d17c501f45234935b85837843f34eceaff633f4bc31ca9b2fb169032e8359329c2efb01d5efaa9a34e442898f3a01d85e66b87128e10d87558d1143e2a9c430704fd49a3adb653b0a5dc0a50293549afc4d6e2a7cd63d8a7f1d74a73c4f6805e43468efb85eed8f4bc9a0541614ec8d843a57953c86c100e3a4e164886ce8eba89f747c8040d15bb55463548188d8e02273fa2f26427aba6a514ebee812284c9090a61560a39e875ad4f9845211bfd4864ed660f081a8239866c9f84ad44704cd6d9956b903347408cc64d8e28722e3e49d9c16e460c622094063d365372239d38a1dc65ec406213aa2488142486060da20883e0cda54c5526bc1ceea95022c17eb2518538d93185fa4fb20d0c56a8dbb75e8bb2cc04861d47b0d8a96724046630e5d29cea42631f042519ce5396871149314f1396875c525ccc666896a3f2c4d486f541d9516c182c85c85083caa4134dc9913338f8cda950515e84ef0bad42992a754502dd261622d310e4ece8832d8b8572f4b6660330d0b1e3700256fd881342a890497acb75913ae85d4dc28edb03cc3c9c362b54160e4952c00a18122fb2f61dbe32a293c1a763132a167367d68120bd0bf375af0096103a35c4407891d8f62b7911ea62c705a91f2b3ad0805176db5f14dd62f199a61df5279a18a546d0a7d61d904ad1c99edc5cc43cd4fbe8a86626cd655d121c1b3e82c0e045a8ee7806c4ae0431b2b80fb0f29147b2108763a892055c36596aead2f072c2e986512dd9c6d6923b3a8eda9dd058055864a7d68bb100c25f2470f5e289eb211348bb1dcc4349071245d9606a23b1c9afa2c8a612180b6464606a138a91146dbda09d2f410ad43b2c838a35a71282ed8863a6fa67aad9283ac17591e14d44807115f54c0a5418b86b6d1842a7774352a5a943b2b9e00ac952d5a38b6accae263645ea9b49645319c46930ac88d1bbd3324461b1ea485c115f87b988b423a9568000000053e4
def a11_2 : Nat := 0x8de6e136d36c10008de68136db68100161d0a126db61900161e68136db61100089e7e126c36d900160e7e106d36d900160d0a106db6990088dd021a6db4c000961d061b6d34180088ad061b6d30980088ad021a6db0d000889d061b6c34980088dd521a6d36800088dd401a6db48000961d4a1a6d341800961d401a6db4100088ad4a1a6d30980088ad401a6db09000889d4a1a6c349800960d4a186d349800960d40186db49046f61d501b6d340146e8ad561a6d30c146e8ad501b6d308146e89d561a6c34c146f60d56186d34c1b0e8ad501b6d301145689d501b6c309145760d56186d30d144f60d56186c34d10088dec39a6d34000088dd159a6d30800088dd139a6c34800088dec1986d348000961d159a6d301000961d139a6c341000961ec1986d34100088ad139a6c30900088aec1986d309000889ec1986c34900008dd9a136d34c10008ad9a136d30d100089d9a136c34d100142110126d36c1000cc236126d36c10011b106136d3681000881c0136d368100088274126d30d900119106136db48100119102126c34d9000841c0136db481000841bc126c34d9000e0104106d34d90008326c106d34d90013a104136d36110008726c136d3611000de104136db4110008126c136db41100081266126c36d100082262106d36d100133118136db09100133196136c36910008b262136db0910008ddbc126db4c100161dc0136d34190008adc0136d30990008adbc126db0d100089dc0136c349900160dbc106db4d10088dd561a6d34c00088dd501b6d348000961d501b6d34100088ad561a6d30d00088ad501b6d309000889d561a6c34d000889d501b6c349000960d56186d34d00008dd36126db6810008dd72136db4c100161d28126db41900161d36126db61100161d78136d361900161da0136db4190008ada2126db0d90008ad7c136d30d90008ada0136db0990008ad72136db0d100089d38126c369900089d7c136c34d900089d78136c369900160d28106db49900160d36106db69100160da2106db4d900160d74106db6d10000120c126d34d80000120a126db49800001158136d34d000001208136db4900000020c0a6d34d90000020a0a6db499000002080b6db491000001980a6d34d9000001100a6d3699000001080a6db4990000010e0a6d36d1000001040b6d34d1000001160a6db691000001180b6d3691000001960b6db4910008dd5e126d34c10008dd5c136d34810008ad5e126d30d10008ad5c136d309100089d5e126c34d100089d5c136c349100001194126d369800001192136d349800001190126d36d00000118e126db4d00000118a126db69000001188136d36900008dd84126d36c10008dd44126db4c10008dd82136d36810008dd3e136db48100161d46136d341900161d3e136db4110008ad48126d30d90008ad46136d30990008ad44126db0d100089d48126c34d900089d46136c349900089d84126c36d100089d82136c369100160d48106d34d900160d84106d36d100160d44106db4d10000014a0a6d3499000001520a6d3691000001400a6db491000b2154126d34d8000aa020126d36d00001014e136d3690000b114e136db490000b2108126db481000aa198126d3419000aa102126db41100010110126d309900010116126db091000a7106106d3499000a7196106db4910000127e126d36d800001268136db69046eab1521a6d36c046ea91501b6d368046ea01501b6db48046e871041b6d360146e811041b6db40146e811161a6c36c146e82118186d36c146e8b1181b6db08146e8b1961b6c3681b0ea91501b6d3610b0ea01501b6db410b0e881061b6d3601b0e841061b6db401b0e8b1181b6db011b0e8b1961b6c3611456a51561a6d30d8456a01501b6db090456841061b6db081456841021a6c30d945683104186d30d9456811041b6db01144ea51561a6c34d844eab1521a6c36d044ea91501b6c369044ecc1101a6c36c144e881061b6c368144e8810e1a6c30d944e83104186c34d944e871041b6c361144e82118186c36d1b06a5156186d34d8b06ab152186d36d0b06cc110186d36c1b068810e186d30d9b0684102186c34d9b0681116186c36d10000119a136d34d0000011c0136d3498000011bc126db4d0000011a2126db4d80000117c136d34d800001178136d3698000011a0136db49800001174126db6d000001172136db4d0000001940a6d3699000001920b6d3499000001900a6d36d10000018a0a6db691000001880b6d369100001138126d369800001128126db49800001136126db690000001060b6d3499000001020a6db4d1000001560a6d34d1000001500b6d34910000115e126d34d00000115c136d349000001148126d34d800001146136d349800001184126d36d000001144126db4d000001182136d36900000113e136db490000be110136d36c100085102126c36d900085106136db681000bc104106d36d9000ba104136db611000b9116136c36d1008b21081a6db480008aa1981a6d3418008aa1021a6db410008101101a6d3098008101161a6db090008b11081a6c3498008a7106186d3498008a7196186db490008b214a1a6d3480008b11401a6c34900008dd42136d34c100089d42136c34d1000b214a126d3481000b1140126c34910009c156126d36d8000a1152136d36d00009b150136db690008cc1101a6d36c0008881061b6d36800088810e1a6d30d8008841061b6db480008841021a6c34d800883104186d34d8008871041b6d3610008811041b6db410008811161a6c36d000882118186d36d00088b1181b6db0900088b1961b6c3690008aa1561a6d3410008101521a6d3090008a7150186d34900008ad42136d30d1000001800a6db6d90000017e0b6d36d90000017a0b6db699000001760b6db6d1000001700a6d36d9000001340a6db4d90000016e0b6d3699000001320b6db4990000016c0a6db6d1000001680b6db69100001142136d34d0000aa156126d341100010152126d3091000a7150106d3491000001660b6db4d90000016a0b6d36d144083104186d36c14408310e1b6d30c1440871041b6d301942083104186db4c1420831021b6c34c1420811041b6c34194188210e186d361941882102186db41940882118186db611408821161b6c36114088b1181b6c30d14108c116186db0d10000013c0b6d34d90000013a0b6db4d1
def d11_2 : Nat := 0xc0018402994620140a02c43304c00102e61c071d9ea080b40240158481000290000601010288200bc460ac00000600000003020b80140800101001401e00014000800284010048209003084000000100c00000a00000010020
def h11_2 : Nat := 0x15c6bd2df00000001b48d1321e236492f52f092473c0ee4850154381bfb51f8a035cc904000000000000000000000060e583a63e94322b8000271a241b900016faa8a3b41a226e1122609f53ca3ac7ec26890907aa1511cb42870046b51eddc126dd5d1bd74e9213630ea90d28e4cd85e04a23321c42c9245a272deb60187e1ee000a7952bd0ababf0000ab046200061c0000c7f70d00000009e06ef000000000000065e80000016a95119835d37811268e85a864b1a125398c000a0300010c00012e6976a824000ee2000000000089f00038d8001118000341f14d6f123360889100002108000001654000517456b429780c3624080004200001d4e000000339482182ed39800242f705687000216924f00000019a60001618ba000109d000386300d2c1d12cc0c84142822361a2ca2000d1249bf1dc2cc87e63fecbf61a40c931284c407271eb51dd400042e51f74162a51428000e0925e76500015b9852c65ab6481cc65341125608b834833c420000cad66f800312ca56000000106b48d000403d10e80a0004c300016b125413e59b6000000000156662c00058cdc7a8ce58edb0b519510a62d0f1c1065881b8c4b1aea05526ea719baa787298c6f0afaab93f40accc02a285829deceb24782da1400002769508c59cf32aaa16ac7c000862d51d3224d600000000000000009630001dec000c5dc206d9a00000000000000000000002cdd90a00000000000005810000001a1bb4c333c00100100061a64d400067d943d004a430005419c5e000b8e63ce5152ec1270a0d10051e26ac125527ab673200010ff2b73748000000000000000218eeda00042f2dd600000029f1018b17b45d426d204be3593b27132f1500000010b4c8e
def a11_3 : Nat := 0x46f61d159a6d300146f61d139a6c340146f61ec1986d340146e8ad139a6c308146e8aec1986d308146e89ec1986c3481b0e8ad139a6c3011b0e8aec1986d3011b0e89ec1986c341145689ec1986c30910000011b8a6d3481000002c38a6d3411000001158a6d3091000001138a6c3491000002c1886d34910088dec39a6d34000088dd159a6d30800088dd139a6c34800088dec1986d348000961d159a6d301000961d139a6c341000961ec1986d34100088ad139a6c30900088aec1986d309000889ec1986c3490
def d11_3 : Nat := 0x200010114
def h11_3 : Nat := 0x2aeb182ba88400c4634006700312c32e004335e002b5cc0159c580000d5184cb0cd80058cd254
def a12_0 : Nat := 0x455849b4d3462a026da6923152126d369188709369b6844604db4da4221c24da6da3118136d36918a00936da48c66049b4d36232c26db6921198126d34d98b209369a4c458849b6d2422ac24da69a1150136d34908b209369a4cc58849b6d24620c26da6933102126db4d188809369b4cc45849b6da462a424da6d21104136d34d188209b69a68000829b4d24604024da6d23154126d34d08a709b69a4844184db4d26220424db69a1108126db4998aa09369a68c5384db4d24604024da6d21110126d369888b0936db48452849b4d26228024db6921108126db498
def d12_0 : Nat := 0x2009216190010120200
def h12_0 : Nat := 0x9e31e43a3a48a9ea053586775d166ad999597c304a26e0bb10002858f54a9400342002e3a7e900000000000002090000000000389017634589b24000dcb540055a13
def a12_1 : Nat := 0x587b0641b4d0451bd8320da690361d15926d301145760c8369848d8752849b4d066c1a8020db69228ad98126d30d9456cb09b6d848d876584db6d046c1b3020da69b28dd15926d308145689c9361848d874604db4d846c1a1c20da6da28dd0e126d36c1b0e8809369b0ca274604db0da4513d8320d8692361d40126db411456a50936984ca2b50049b6c246c1a9420da69328dd96136db481b0e840936da0ca2766049b0d3651ba2724d869028dd40126db48144ea509361a4ca2b55849b4c34515aa026da61228dd56126d34c1b0ea809b69a08a275404db0d246c1aac20da69a361d06136d3419b0e8b0936db08d8344041b4da651baa424da6d0289d52126c369146ea809b69a40a2755849b0d34513a1c24d86da28ad08126db0994568309b6984ca2b40849b6c3451ba0424db698289d06136c34994568209b69868a2744049b0da640223724da690001113926c349046e8209b69a60a274104db0d3440222b24da6120012c3926d341000960c8369a482ac54849b4db41522a026da6d20a5156126d34d8500a809b6da482ac4604db4db455021c26da6da2cc118136d36d9438cb09b6db68a9443849b4db655233024da6db2a0118136db691660cb09b6da6ca944604db4da655622c24db6da2a010e126db6d15408809b69b4caac6584db6d3455033026da69b2a9106136d3699548810936db68a946584db6d2655622024da6db2a0198126db4d95408b09b6db48b3045849b6db651032c26db6d32ab106136d34d95408109b6da6880446e49b4d2040222724d869228410e126db6d94208c09b6db4ca9445849b6da654022024db6d32a5102126db4d95008309b6da4ca9454849b4da655228024db6d22ab108126db4d95408409b6da4c80084029b4db440041c16da6d22002880b6d3499001430536da68804b0e49b4d0440258320da6922a5140126db4990088ac9369848aac54849b4db45522a026da6d22a9108126db699008aa09369a688045384db4d2454a2a026da6932ab140126db4d1558a809b69a6880459049b4d264022c424db6922001c80a6d3699000e30536db4880408049b4da454a2ac24da69b2a0150136db491410a109b69a68800a1029b4d364004c016db6922001840a6d36d1000c105b69b48aa44104db4db454a20826da69b2a0104136db4d10013f05369b6c8009a02db6da450433426da69a28310e136d36d94088c09b6db688009d029b4db44004c416da6d22cc284126d34d96593009b6da4880443849b4db440223026da6d2201156126d34d1008a809b69a488008d829b4da64004cc14db6d22cc110126d36c1458cb09b61b4880068829b6d364002f016da6d32001a00b6db499000ba0536db6880454849b4da440027014da6d32001360a6db691000a405369a6c8004f82db6d2440028814db69a287274126d36d14613109b69b488005f02db4d364002e416db69a288102126db6d94188b09b6db4caa453049b4da44004d816da69a201198126d34d9008cb09b6da48a9414849b4d2654009824db692201104136d34d1000b205369a4c80058829b6d2440046414db693284232126db4994188109b6da6ca2043849b4c3651623026db612288236126d36994388209b69b08a0846041b4db440028416da69a284104136db4d9000cd05b69a6880443849b4db400223026da6d2001106136d34994113609b69a688007002db4d2640037814db69a201110126d36990088b0936db4880466049b4d3600232c26db6920ab15e126d34d1000940536da4ca204184db4da050222c24d86da20010a0a6db699008b209369a4c2104184db6d2050820424d869b2000200a6d3691008a509369a4c80450049b6d2440029814da6d2201152126d36900088209b69a6800055029b4d3440029c16da692201110126d36980088b0936db4800000829b4d2440000004da692201156126d34d0008a809b69a4800455049b4d3400229c26da692083104106d34d94088209b6da08a0c7004db4d2650237824db69a288104136d36d94108b09b6db6880014829b4d2640009814db692201106136d3498008810936da6800057829b4d344002b816da692201020126d3690008840936da4c80452849b4d2600228024db692001108126db498
def d12_1 : Nat := 0xa1005233104310c00000410000600401080010840119002100210842009820004060082000004504022b4e50002c101a6000a10002b90420704040016013c00004243800900c00
def h12_1 : Nat := 0x78e000000000bc4a733d3825a5d793d6a1572b03d934363e14dd64336000a1f0005db722baaa2dcb7d5600000010868a000b186b147d63b8041558af000491d40297c1668092f270dae97cb6e91a9a929200000095348dbbe000000000000a2b18f9e333c000d488c58a30000000006d16947469e799f7841529038098acb54ba20003980009965abbc8921605da18583b61b45e0000630615c4b390dde738469b14676c4400040d23d000000000cd280ad5b35f43929e235a0b401ad79b3b0e17adb881b7347412b2c6c000c6051389536b62ebb5b6d00051d9c60000005ba487251000000000000000000000000666b78849dd5ca5000000dd8c4f000bd02101425e4726000000000162d029e51d6d195684bb2a882c429447d5a00000025e49953f79c00000000070f777617c3300037200000000037bde6000381000de100028c650000745000000ac90000003e29cf2c00003c3a063a6cd4000682165620d9a28b571563531bbc8cc5a085ca377b9b891672df19d2dad1e6dd3883619cb5bfa830002ce9c21ca57414a22ac7fb4cac774e00000000000047e20c00033a2590007bd000b326a47861dc000cadb75324207a28a1cd11000000c124cd59bb6fd277798850000000000004c1000000b239a7
def a12_2 : Nat := 0x6608c09b69b6ca1c6584db6db459822c24db6db2cc196136db4d9440cb09b6db4ca1043849b6db650823026db6d3361ec1906d341144f60c8361a48a3744e49b0d2051bd8320da690361d15926d301145760c8369848a3745649b4c20515a2724d86122a510e126d36d95288c09b69b4ca8043849b6db454023026db6d228ad98126d30d9456cb09b6d848a946584db6d2654033024db69b28dd0e126d36c1b0e8c09b69b08a274604db0da46c1a1c20da6da20110e126d36d10088c09b69b48aa466049b4db655623026da6da2a810e136d36d1b0ea509369a0cd8350041b6d2451bb2c26db690361d96136db41144ecc09361a6cd8366041b4d3654a22c24db6d32a0110126db69900961c9369a0880445649b4c2440258320da6922a5102126db4d95488309b69b4ca804184db6d2640223724da690201113926c3491008ab09369a688045404db4d2454a20826da69b2a0104136db4d1b0e8809369b0ca2743849b0db455622c24db6da2a8110136d3699b0ea00936da08d8352841b4d2651ba8024db69028ad4a126d3099456a00936d848a2752849b0d2651baac24da698289d50136c3491558cb09b6da68aa06604db4d3651020424db6db283116136db699b0e8b0936db08d8344041b4da651baa424da6d0361d08126db419456ab09369868a2b5404db4c24513aa424d86d2361d50136d3411b06ab08369a68a3740849b6d306c3a0c26da68328ad06136d3099456810936d868a274184db0d2655620c26da69b2a8102136db4d10088dc9369a40004b0e49b4d0400222b24da612001113926c349000960c8369a482ac54849b4db45522a026da6d2201198126d34d9008cb09b6da488044104db4d3451baa026da690289d56126c34d15488209b69b688044184db4d264022a424da6d228dd16126db6814568209b69868a2744049b0da6515a1024db6132ab150136d34d15588809369b6caa04584db6da451ba0826da698289d04136c34d1558840936da6caa04204db6d2654a2a026da6932ab140126db4d1528a909369b4caa450049b6da440222024da6d3201116126db691528ab09369a6ca805404db6d2459822024da6d828b196136c3691548840936db4ca9455849b4d361402a026db6920a5140126db499558a909369b682a45404db4da400229424da693201140126db4910088709369b680044604db4da40022c824da693001162126db4900014205369a6c8009802db6d244002c814da6932001620a6db491008840936da4c8009d029b4db44004c416da6d2201198126d34d8008cb09b6da4800000009b4d2450621c26da6db281118136db6d10013f05369b6c8009a02db6da450820826db69b201156126d34d0008a809b69a4820c4084db6d3650e20826da6c2282118106d36d10088209b69a6822043849b4c3651623026db6122001840a6d36d1000c105b69b4880455049b4d3400229c26da69200014c0a6d3691000aa05369a688005382db4d2440204024da6d20001380a6d36990009b0536db48a204104db4db650422c26db6da2000200a6d36910002905369a4c80013029b6d2440029014da69b2001460b6d3499000a20536da688004f82db6d2440220c26da693001102126db4d04408309b69b40a0445849b0db440034414db69b2001a00b6db4994208309b6da40a1040849b0d364002bc14da69a20015c0b6d3491000bc05b69b4c8005d029b6db44004d816da69a2002360a6d3699001330536db488004a029b6d2640021414db6d3201110126d36980088b0936db480007002db4d2640037814db69a2002320a6db499000be05b69a6c8005c82db6d3440229424da693001140126db4904188208369a6ca044104db6d0440221024db6930001420b6d34d1
def d12_2 : Nat := 0x80008e23840300c0120400015030080200c40330a02086b0004500340300400800002465100210002101020102281006510802084412800740c850240103003
def h12_2 : Nat := 0x88a35813b1290009c1000b8852fc67c7085298cc3f24982353cb817170005ae81e0005b7256b4700000000098075da4d6c9000639a8e000000216000000d89d14b7d472351b31543c533874b629d35fd0d23a4a198454536cb9600082c000000b8587e88fb650000000000000000009a8332b97ab311a0000003b10000002b00000006090005959bd1c4b754276a2d4fd1179e2cbd2d8bc2c3d984541a00000009ccc93cbab6087a34a906da7859a41c73dbb2b26a3c4c1be228240c086aac9171289b3b5db9203b4b15ed9a27476f1a62ca3783abc2ea2490bd3d5b8d05492a1562ad6428b63380e0007368509ac11d57f301b185c00002760003902a9a356bf00000000060a00000096a55748247cc3084456b000000499000000000925000679000d94a0f25c000000d1ca8d8553afc1fb139610000003c64c713e000dc2000aa4622107000a5a000000000421d46000402bad72065b98600029f00071b000000000b0c1191429c8269337b38766b4826e0005b4000a3400077b0009c516292b0000006770000007a556da9c18322664ed10d04363771000d68000
def a12_3 : Nat := 0x446e49b4d2040258724da682201115926d309100889c9361a48804b0641b4d2451ba1c24da6d828dd04136d34c146e8b0936db40a374604db4da051bb2c26db690361d10126d3619b0e840936da0cd8745849b6d846c3a3026da6c2361d96136db411456cc0936986ca2b42049b6c26515a0826da61a28ad96136db09144ecc09361a6ca2744049b0da6513a1c24d86da289d04136c34d144e8c09b61b48d8366041b4d366c1a2020da6d3360d0e106d36d146e8ac9369840a3744e49b0d2051bd8320da690361d15926d3011b0e89c9361a08d87b0641b4d04515a2724d861228aec1906d309144f60c8361a48a3750049b6d206c3a9424da683361d40126db411456a50936984ca2752849b0d26513aa424d86d2360d4a106d3499b06a00836da48a3740849b6d306c3a0c26da68328ad06136d3099456810936d868a274184db0d2640233024da69b001110126d3698008840936da4c00443849b4db400220826da69a001116126db6900088c09b69b480046584db6d2400223724da6900012c3926d34100088ac936984800444e49b0d2400258320da69208dd56126d34c146ea809b69a40d875404db4d04515aac24da61a28ad50136d309144eab09361a68a275404db0d246c1aac20da69a20114a126d3498008a00936da480009f829b4db640021414db6d32002680b6db6910088309b69a4c00440849b6d3400027014da6d32001280a6db4990009b0536db4880068829b6d364002f816da69b2001780b6d3699000d005b6da4c8005d029b6db44002e416db69a201156126d34d0008a809b69a4829455849b4d361562a424da6da0a9150136d3690500a809b6da4800052029b4d3640028c16da6932001840a6d36d1000a20536da688006082db4da440027c16db6922cc110126d36c14408309b69b40a2043849b4c3650820c26db690284102126c34d94188208369a6ca1c4104db4d8450220826db682281116126c36d14108c08369b68a2c4604db6c2451632c26d86d22001420b6d34d1
def d12_3 : Nat := 0x100003302b063030b1300103001205221243310130020651010600
def h12_3 : Nat := 0x6bd0004c80000000000051504bb400000134a7d85c9b953000000aaaa758736400000885790005af24060c985b95c40018cee50012a707d6e2c2c2e0b000dbc8f000106138d99aa3bfd500019a800b70e42958000000032d8cc71284800168bc69004d1d6a63704004dc001328670000000005680000029525acdd920036b8002ce0000063b13f839f7aac70fb816ec4770a000000000014ea90e9d9546daac426c3d62b22ad099e713461ea95d66ec896c6d6003246d248c001efc0282828d89cd1b6709000000b303a40036d21ba5744181
def a12_4 : Nat := 0x237b0e49b4d0051ba2b24da61028dd13926c348146f60c8369a40d8745649b4c046c3a2724d8682361ec1906d341145689c9361848a2bb0641b4c24513d8320d869220111b926d348000961c9369a0800445649b4c2400222724d86920012c1906d3490
def d12_4 : Nat := 0x70
def h12_4 : Nat := 0x18dc5a002300642d00009b351600006e21af00b2570099
def a13_0 : Nat := 0x829b4d2420a6d3491
def d13_0 : Nat := 0x0
def h13_0 : Nat := 0x19980
def a13_1 : Nat := 0xb0e29b4d046c1886d349145629b4c2451b8a6d348144e29b0d245980a6d34d96582db6d2450e0a6d36d14602db4da45560a6d34d15402db4d245520a6d369152829b4d265400a6db4914182db4d265020a6db4d144029b4da65160a6db69142029b6d265040b6d34d100829b4d240020a6d3491
def d13_1 : Nat := 0x461d800000000
def h13_1 : Nat := 0x4800968004b229b6522487876c400b0b4001820016628d3b3cacbccc00d18009600
def a13_2 : Nat := 0xb0e29b4d046c1886d349145629b4c2451b8a6d348144e29b0d245980a6d34d96582db6d2450e0a6d36d14602db4da45520a6d369144029b4da65160a6db69152829b4d265400a6db49155829b4d345500b6d349142029b6d264020a6d34914182db4d265020a6db4d14102db4d344020a6d3490
def d13_2 : Nat := 0x461d800000000
def h13_2 : Nat := 0x4c009400057219b6522483876c400b0b20018a0013e28d3b3cacbcd800d10009a00
def a13_3 : Nat := 0xb0e29b4d046c1886d349146e29b4d205138a6c349145629b4c244020a6d349166029b4d365960b6db49143829b4db45180b6d369154829b4da44020a6d349052829b4d265400a6db49155829b4d345500b6d349144029b4da65160a6db6914182db4d265020a6db4d142029b6d265040b6d34d1
def d13_3 : Nat := 0x28009000
def h13_3 : Nat := 0x128128025792004d90713d84355f640009f14d1001a76800ca99a5c0000684444c
def a13_4 : Nat := 0x810536da6880829b4d242ac14da69a3500b6d3491
def d13_4 : Nat := 0x0
def h13_4 : Nat := 0x25809425200
def a13_5 : Nat := 0x46e29b4d206c38a6d341145629b4c245138a6c3491b0621b4d244020a6d3490
def d13_5 : Nat := 0x20
def h13_5 : Nat := 0x24c301880649a03700
def count : Nat → Nat → Nat
  | 9,0 => 138
  | 9,1 => 9
  | 9,2 => 6
  | 10,0 => 752
  | 10,1 => 228
  | 10,2 => 46
  | 11,0 => 483
  | 11,1 => 1077
  | 11,2 => 287
  | 11,3 => 25
  | 12,0 => 39
  | 12,1 => 231
  | 12,2 => 204
  | 12,3 => 111
  | 12,4 => 15
  | 13,0 => 2
  | 13,1 => 22
  | 13,2 => 22
  | 13,3 => 22
  | 13,4 => 4
  | 13,5 => 6
  | _,_ => 0
def state : Nat → Nat → Nat → List Wire
  | 9,0 => atState a9_0 78
  | 9,1 => atState a9_1 85
  | 9,2 => atState a9_2 63
  | 10,0 => atState a10_0 74
  | 10,1 => atState a10_1 74
  | 10,2 => atState a10_2 74
  | 11,0 => atState a11_0 63
  | 11,1 => atState a11_1 64
  | 11,2 => atState a11_2 64
  | 11,3 => atState a11_3 64
  | 12,0 => atState a12_0 45
  | 12,1 => atState a12_1 53
  | 12,2 => atState a12_2 53
  | 12,3 => atState a12_3 53
  | 12,4 => atState a12_4 53
  | 13,0 => atState a13_0 34
  | 13,1 => atState a13_1 42
  | 13,2 => atState a13_2 42
  | 13,3 => atState a13_3 42
  | 13,4 => atState a13_4 41
  | 13,5 => atState a13_5 42
  | _,_ => fun _ => []
def locate : Nat → Nat → List Wire → Nat
  | 9,0 => locateIn d9_0 h9_0 69 187 5 8
  | 9,1 => locateIn d9_1 h9_1 4 13 1 4
  | 9,2 => locateIn d9_2 h9_2 3 12 2 3
  | 10,0 => locateIn d10_0 h10_0 376 1016 5 10
  | 10,1 => locateIn d10_1 h10_1 114 313 5 8
  | 10,2 => locateIn d10_2 h10_2 23 64 4 6
  | 11,0 => locateIn d11_0 h11_0 241 654 5 9
  | 11,1 => locateIn d11_1 h11_1 538 1454 10 11
  | 11,2 => locateIn d11_2 h11_2 143 389 5 9
  | 11,3 => locateIn d11_3 h11_3 12 34 3 5
  | 12,0 => locateIn d12_0 h12_0 19 53 4 6
  | 12,1 => locateIn d12_1 h12_1 115 312 5 8
  | 12,2 => locateIn d12_2 h12_2 102 276 5 8
  | 12,3 => locateIn d12_3 h12_3 55 153 4 7
  | 12,4 => locateIn d12_4 h12_4 7 23 1 4
  | 13,0 => locateIn d13_0 h13_0 1 3 1 2
  | 13,1 => locateIn d13_1 h13_1 11 30 5 5
  | 13,2 => locateIn d13_2 h13_2 11 30 5 5
  | 13,3 => locateIn d13_3 h13_3 11 30 3 5
  | 13,4 => locateIn d13_4 h13_4 2 6 1 3
  | 13,5 => locateIn d13_5 h13_5 3 10 2 3
  | _,_ => fun _ => 0
def tab : Table := ⟨count,locate,state⟩
def check (k t n j : Nat) := span (fun i => !run tab k t (state k t i)) n j
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_0 : check 9 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_28 : check 9 0 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_56 : check 9 0 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_84 : check 9 0 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_0_112 : check 9 0 26 112=true := by decide +kernel
theorem yes9_0 : cells tab 9 0=true := (@span_join _ 56 0 82 (@span_join _ 28 0 28 c9_0_0 c9_0_28) (@span_join _ 28 56 54 c9_0_56 (@span_join _ 28 84 26 c9_0_84 c9_0_112)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_1_0 : check 9 1 9 0=true := by decide +kernel
theorem yes9_1 : cells tab 9 1=true := c9_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c9_2_0 : check 9 2 6 0=true := by decide +kernel
theorem yes9_2 : cells tab 9 2=true := c9_2_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_0 : check 10 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_28 : check 10 0 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_56 : check 10 0 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_84 : check 10 0 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_112 : check 10 0 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_140 : check 10 0 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_168 : check 10 0 28 168=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_196 : check 10 0 28 196=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_224 : check 10 0 28 224=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_252 : check 10 0 28 252=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_280 : check 10 0 28 280=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_308 : check 10 0 28 308=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_336 : check 10 0 28 336=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_364 : check 10 0 28 364=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_392 : check 10 0 28 392=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_420 : check 10 0 28 420=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_448 : check 10 0 28 448=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_476 : check 10 0 28 476=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_504 : check 10 0 28 504=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_532 : check 10 0 28 532=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_560 : check 10 0 28 560=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_588 : check 10 0 28 588=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_616 : check 10 0 28 616=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_644 : check 10 0 28 644=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_672 : check 10 0 28 672=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_700 : check 10 0 28 700=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_0_728 : check 10 0 24 728=true := by decide +kernel
theorem yes10_0 : cells tab 10 0=true := (@span_join _ 364 0 388 (@span_join _ 168 0 196 (@span_join _ 84 0 84 (@span_join _ 28 0 56 c10_0_0 (@span_join _ 28 28 28 c10_0_28 c10_0_56)) (@span_join _ 28 84 56 c10_0_84 (@span_join _ 28 112 28 c10_0_112 c10_0_140))) (@span_join _ 84 168 112 (@span_join _ 28 168 56 c10_0_168 (@span_join _ 28 196 28 c10_0_196 c10_0_224)) (@span_join _ 56 252 56 (@span_join _ 28 252 28 c10_0_252 c10_0_280) (@span_join _ 28 308 28 c10_0_308 c10_0_336)))) (@span_join _ 196 364 192 (@span_join _ 84 364 112 (@span_join _ 28 364 56 c10_0_364 (@span_join _ 28 392 28 c10_0_392 c10_0_420)) (@span_join _ 56 448 56 (@span_join _ 28 448 28 c10_0_448 c10_0_476) (@span_join _ 28 504 28 c10_0_504 c10_0_532))) (@span_join _ 84 560 108 (@span_join _ 28 560 56 c10_0_560 (@span_join _ 28 588 28 c10_0_588 c10_0_616)) (@span_join _ 56 644 52 (@span_join _ 28 644 28 c10_0_644 c10_0_672) (@span_join _ 28 700 24 c10_0_700 c10_0_728)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_0 : check 10 1 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_28 : check 10 1 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_56 : check 10 1 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_84 : check 10 1 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_112 : check 10 1 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_140 : check 10 1 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_168 : check 10 1 28 168=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_196 : check 10 1 28 196=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_1_224 : check 10 1 4 224=true := by decide +kernel
theorem yes10_1 : cells tab 10 1=true := (@span_join _ 112 0 116 (@span_join _ 56 0 56 (@span_join _ 28 0 28 c10_1_0 c10_1_28) (@span_join _ 28 56 28 c10_1_56 c10_1_84)) (@span_join _ 56 112 60 (@span_join _ 28 112 28 c10_1_112 c10_1_140) (@span_join _ 28 168 32 c10_1_168 (@span_join _ 28 196 4 c10_1_196 c10_1_224))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_2_0 : check 10 2 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c10_2_28 : check 10 2 18 28=true := by decide +kernel
theorem yes10_2 : cells tab 10 2=true := (@span_join _ 28 0 18 c10_2_0 c10_2_28)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_0 : check 11 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_28 : check 11 0 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_56 : check 11 0 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_84 : check 11 0 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_112 : check 11 0 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_140 : check 11 0 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_168 : check 11 0 28 168=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_196 : check 11 0 28 196=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_224 : check 11 0 28 224=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_252 : check 11 0 28 252=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_280 : check 11 0 28 280=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_308 : check 11 0 28 308=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_336 : check 11 0 28 336=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_364 : check 11 0 28 364=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_392 : check 11 0 28 392=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_420 : check 11 0 28 420=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_448 : check 11 0 28 448=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_0_476 : check 11 0 7 476=true := by decide +kernel
theorem yes11_0 : cells tab 11 0=true := (@span_join _ 252 0 231 (@span_join _ 112 0 140 (@span_join _ 56 0 56 (@span_join _ 28 0 28 c11_0_0 c11_0_28) (@span_join _ 28 56 28 c11_0_56 c11_0_84)) (@span_join _ 56 112 84 (@span_join _ 28 112 28 c11_0_112 c11_0_140) (@span_join _ 28 168 56 c11_0_168 (@span_join _ 28 196 28 c11_0_196 c11_0_224)))) (@span_join _ 112 252 119 (@span_join _ 56 252 56 (@span_join _ 28 252 28 c11_0_252 c11_0_280) (@span_join _ 28 308 28 c11_0_308 c11_0_336)) (@span_join _ 56 364 63 (@span_join _ 28 364 28 c11_0_364 c11_0_392) (@span_join _ 28 420 35 c11_0_420 (@span_join _ 28 448 7 c11_0_448 c11_0_476)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_0 : check 11 1 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_28 : check 11 1 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_56 : check 11 1 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_84 : check 11 1 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_112 : check 11 1 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_140 : check 11 1 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_168 : check 11 1 28 168=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_196 : check 11 1 28 196=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_224 : check 11 1 28 224=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_252 : check 11 1 28 252=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_280 : check 11 1 28 280=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_308 : check 11 1 28 308=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_336 : check 11 1 28 336=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_364 : check 11 1 28 364=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_392 : check 11 1 28 392=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_420 : check 11 1 28 420=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_448 : check 11 1 28 448=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_476 : check 11 1 28 476=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_504 : check 11 1 28 504=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_532 : check 11 1 28 532=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_560 : check 11 1 28 560=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_588 : check 11 1 28 588=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_616 : check 11 1 28 616=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_644 : check 11 1 28 644=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_672 : check 11 1 28 672=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_700 : check 11 1 28 700=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_728 : check 11 1 28 728=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_756 : check 11 1 28 756=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_784 : check 11 1 28 784=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_812 : check 11 1 28 812=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_840 : check 11 1 28 840=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_868 : check 11 1 28 868=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_896 : check 11 1 28 896=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_924 : check 11 1 28 924=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_952 : check 11 1 28 952=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_980 : check 11 1 28 980=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_1008 : check 11 1 28 1008=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_1036 : check 11 1 28 1036=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_1_1064 : check 11 1 13 1064=true := by decide +kernel
theorem yes11_1 : cells tab 11 1=true := (@span_join _ 532 0 545 (@span_join _ 252 0 280 (@span_join _ 112 0 140 (@span_join _ 56 0 56 (@span_join _ 28 0 28 c11_1_0 c11_1_28) (@span_join _ 28 56 28 c11_1_56 c11_1_84)) (@span_join _ 56 112 84 (@span_join _ 28 112 28 c11_1_112 c11_1_140) (@span_join _ 28 168 56 c11_1_168 (@span_join _ 28 196 28 c11_1_196 c11_1_224)))) (@span_join _ 140 252 140 (@span_join _ 56 252 84 (@span_join _ 28 252 28 c11_1_252 c11_1_280) (@span_join _ 28 308 56 c11_1_308 (@span_join _ 28 336 28 c11_1_336 c11_1_364))) (@span_join _ 56 392 84 (@span_join _ 28 392 28 c11_1_392 c11_1_420) (@span_join _ 28 448 56 c11_1_448 (@span_join _ 28 476 28 c11_1_476 c11_1_504))))) (@span_join _ 280 532 265 (@span_join _ 140 532 140 (@span_join _ 56 532 84 (@span_join _ 28 532 28 c11_1_532 c11_1_560) (@span_join _ 28 588 56 c11_1_588 (@span_join _ 28 616 28 c11_1_616 c11_1_644))) (@span_join _ 56 672 84 (@span_join _ 28 672 28 c11_1_672 c11_1_700) (@span_join _ 28 728 56 c11_1_728 (@span_join _ 28 756 28 c11_1_756 c11_1_784)))) (@span_join _ 140 812 125 (@span_join _ 56 812 84 (@span_join _ 28 812 28 c11_1_812 c11_1_840) (@span_join _ 28 868 56 c11_1_868 (@span_join _ 28 896 28 c11_1_896 c11_1_924))) (@span_join _ 56 952 69 (@span_join _ 28 952 28 c11_1_952 c11_1_980) (@span_join _ 28 1008 41 c11_1_1008 (@span_join _ 28 1036 13 c11_1_1036 c11_1_1064))))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_0 : check 11 2 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_28 : check 11 2 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_56 : check 11 2 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_84 : check 11 2 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_112 : check 11 2 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_140 : check 11 2 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_168 : check 11 2 28 168=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_196 : check 11 2 28 196=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_224 : check 11 2 28 224=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_252 : check 11 2 28 252=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_2_280 : check 11 2 7 280=true := by decide +kernel
theorem yes11_2 : cells tab 11 2=true := (@span_join _ 140 0 147 (@span_join _ 56 0 84 (@span_join _ 28 0 28 c11_2_0 c11_2_28) (@span_join _ 28 56 56 c11_2_56 (@span_join _ 28 84 28 c11_2_84 c11_2_112))) (@span_join _ 84 140 63 (@span_join _ 28 140 56 c11_2_140 (@span_join _ 28 168 28 c11_2_168 c11_2_196)) (@span_join _ 28 224 35 c11_2_224 (@span_join _ 28 252 7 c11_2_252 c11_2_280))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c11_3_0 : check 11 3 25 0=true := by decide +kernel
theorem yes11_3 : cells tab 11 3=true := c11_3_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_0_0 : check 12 0 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_0_28 : check 12 0 11 28=true := by decide +kernel
theorem yes12_0 : cells tab 12 0=true := (@span_join _ 28 0 11 c12_0_0 c12_0_28)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_1_0 : check 12 1 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_1_28 : check 12 1 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_1_56 : check 12 1 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_1_84 : check 12 1 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_1_112 : check 12 1 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_1_140 : check 12 1 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_1_168 : check 12 1 28 168=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_1_196 : check 12 1 28 196=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_1_224 : check 12 1 7 224=true := by decide +kernel
theorem yes12_1 : cells tab 12 1=true := (@span_join _ 112 0 119 (@span_join _ 56 0 56 (@span_join _ 28 0 28 c12_1_0 c12_1_28) (@span_join _ 28 56 28 c12_1_56 c12_1_84)) (@span_join _ 56 112 63 (@span_join _ 28 112 28 c12_1_112 c12_1_140) (@span_join _ 28 168 35 c12_1_168 (@span_join _ 28 196 7 c12_1_196 c12_1_224))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_2_0 : check 12 2 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_2_28 : check 12 2 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_2_56 : check 12 2 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_2_84 : check 12 2 28 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_2_112 : check 12 2 28 112=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_2_140 : check 12 2 28 140=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_2_168 : check 12 2 28 168=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_2_196 : check 12 2 8 196=true := by decide +kernel
theorem yes12_2 : cells tab 12 2=true := (@span_join _ 112 0 92 (@span_join _ 56 0 56 (@span_join _ 28 0 28 c12_2_0 c12_2_28) (@span_join _ 28 56 28 c12_2_56 c12_2_84)) (@span_join _ 56 112 36 (@span_join _ 28 112 28 c12_2_112 c12_2_140) (@span_join _ 28 168 8 c12_2_168 c12_2_196)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_3_0 : check 12 3 28 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_3_28 : check 12 3 28 28=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_3_56 : check 12 3 28 56=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_3_84 : check 12 3 27 84=true := by decide +kernel
theorem yes12_3 : cells tab 12 3=true := (@span_join _ 56 0 55 (@span_join _ 28 0 28 c12_3_0 c12_3_28) (@span_join _ 28 56 27 c12_3_56 c12_3_84))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c12_4_0 : check 12 4 15 0=true := by decide +kernel
theorem yes12_4 : cells tab 12 4=true := c12_4_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13_0_0 : check 13 0 2 0=true := by decide +kernel
theorem yes13_0 : cells tab 13 0=true := c13_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13_1_0 : check 13 1 22 0=true := by decide +kernel
theorem yes13_1 : cells tab 13 1=true := c13_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13_2_0 : check 13 2 22 0=true := by decide +kernel
theorem yes13_2 : cells tab 13 2=true := c13_2_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13_3_0 : check 13 3 22 0=true := by decide +kernel
theorem yes13_3 : cells tab 13 3=true := c13_3_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13_4_0 : check 13 4 4 0=true := by decide +kernel
theorem yes13_4 : cells tab 13 4=true := c13_4_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem c13_5_0 : check 13 5 6 0=true := by decide +kernel
theorem yes13_5 : cells tab 13 5=true := c13_5_0
theorem known : ∀ k<14, ∀ t≤6, ∀ i<tab.count k t, Impossible k t (tab.state k t i) := by
  apply usable
  intro k hk t ht
  interval_cases k <;> interval_cases t
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes9_0
  · exact yes9_1
  · exact yes9_2
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes10_0
  · exact yes10_1
  · exact yes10_2
  · rfl
  · rfl
  · rfl
  · rfl
  · exact yes11_0
  · exact yes11_1
  · exact yes11_2
  · exact yes11_3
  · rfl
  · rfl
  · rfl
  · exact yes12_0
  · exact yes12_1
  · exact yes12_2
  · exact yes12_3
  · exact yes12_4
  · rfl
  · rfl
  · exact yes13_0
  · exact yes13_1
  · exact yes13_2
  · exact yes13_3
  · exact yes13_4
  · exact yes13_5
  · rfl
end Cuts

namespace Cert.Compact
open PEqualNP.Outside.L_meta_2309_aux.Main2331
def judge (r : Row) (t : Nat) (w : List Wire) :=
  if r.mask=16 ∧ r.k=12 ∧ t≤5 ∧ r.signed=false then PEqualNP.Outside.L_meta_2309_aux.Cache.run PEqualNP.Outside.L_meta_2309_aux.P16.tab r.k t w
  else if r.mask=1 ∧ r.k=11 ∧ t≤4 ∧ r.signed=false then PEqualNP.Outside.L_meta_2309_aux.Cache.run PEqualNP.Outside.L_meta_2309_aux.P1.tab r.k t w
  else search r.k t w
theorem judge_sound (r : Row) (t : Nat) (w : List Wire) (h : judge r t w=false) : Impossible r.k t w := by
  unfold judge at h
  split at h
  · rename_i branch
    obtain ⟨_,hk,ht,_⟩ := branch
    exact PEqualNP.Outside.L_meta_2309_aux.Cache.run_sound PEqualNP.Outside.L_meta_2309_aux.P16.tab r.k t w (fun j hj u hu => PEqualNP.Outside.L_meta_2309_aux.P16.known j (by omega) u (by omega)) h
  · split at h
    · rename_i branch
      obtain ⟨_,hk,ht,_⟩ := branch
      exact PEqualNP.Outside.L_meta_2309_aux.Cache.run_sound PEqualNP.Outside.L_meta_2309_aux.P1.tab r.k t w (fun j hj u hu => PEqualNP.Outside.L_meta_2309_aux.P1.known j (by omega) u (by omega)) h
    · exact exclude_search h
def checkRow (get : Nat → Row) (link : Nat → Nat → Nat) (idx : Nat) :=
  let r := get idx
  let v := full r.signed r.mask
  let w := ws r.signed r.mask r.tags
  shape r.signed r.mask r.tags &&
    (if r.k+1 < v.length then true else
     geometry r.signed r.mask r.tags && children get link idx &&
     (List.range (r.k+2-v.length)).all fun t => !judge r t w)
theorem rows_sound (get : Nat → Row) (link : Nat → Nat → Nat) (lim : Nat)
    (ok : ∀ i<lim, checkRow get link i=true) : ∀ i<lim, (get i).goal := by
  intro idx
  induction idx using Nat.strong_induction_on with
  | ind idx ih =>
    intro hi
    have chk := ok idx hi
    simp only [checkRow,Bool.and_eq_true] at chk
    split at chk
    · rename_i short
      have sh := chk.1
      simp only [shape,Bool.and_eq_true,decide_eq_true_eq] at sh
      apply size_bad _ _ sh.1.1.1 sh.1.1.2
      rwa [List.toFinset_card_of_nodup sh.1.2]
    · simp only [Bool.and_eq_true] at chk
      apply fromRows _ _ _ _ chk.1 chk.2.1.1
      · intro i hm tagged
        have c := List.all_eq_true.mp chk.2.1.2 i hm
        simp only [Bool.or_eq_true,beq_iff_eq] at c
        have c := c.resolve_left tagged
        simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at c
        have prev := ih _ c.1.1.1 (by omega)
        change Bad _ (full _ _) at prev
        simpa only [c.1.1.2,c.1.2,c.2] using prev
      · intro t ht
        have inside : t ∈ List.range ((get idx).k+2-(full (get idx).signed (get idx).mask).length) := List.mem_range.mpr (by omega)
        apply judge_sound
        simpa using List.all_eq_true.mp chk.2.2 t inside
end Cert.Compact

namespace Cert.Compact.Data
open PEqualNP.Outside.L_meta_2309_aux.Main2331
def rows : Nat := 0x4a993101a1963081692530212820b0202aa42e01a8912c41a9892c1168a22c0929982c0515812c0222862a8182922981849929414a2529214a822909612628a191982885a905283105146920501168a054046830151128220a98270122a2268128602641292026211a882611888825414a8825110aa225090a882505a08224c1a0862491a0922489a08824852020e461a8082431282124290820e425a48224192860240d682424220255238108542341205122c1112122a1115422851904223100002209804521c1411521a141522189414821850404e1614451214945082131052121290950210d900520b15000e0a56050208d0000205100002045000020150a882102a0822082a08220420a88200600001f8108001f4108201f2108201f0920001ec100201ea100001e9120201e8900001e8528001e5108001e3128001e1980001dc180081d9100001d8900081d850000dd6180081d5100001d4908081d4500081d3100201d2908081d2500001d1908001d0da0001ce1a0001cc580001cb120201ca90000dca580081c9520001c8da0001c7160111c6320001c3908081c3519101c2728001c1d10211ea018045e3041041da004049d6004085d3005201d2806101d2290005cb050009ca410121ca260111c6264005c3854041c3219101c2600001bc100001b1100001ab100001a610000198d0410196300001939500018a7000018990000182d00001a8200001a4200001a220000198200001942000019220000190a000018a20000188600001862000018460000182a000018260000180e000017c1000017a10000179100001789000017850000176100001751000017490000173100001719000016e1000016d1000016c5000016b1000016a500001699000016950000168d0000167100001639000015e1000015c9000015c5000015b1000015a9000015a5000015990000158d000015710000156900001563000015590000154d000015390000152d0000151d000014b9000014b5000014ad000014a70000149d0000143d000016b00000156200001538000014a60000126300001127000010730000106700001037000013a000001330000012a4000012620000123800001232000011e0000011b0000011a8000011a4000011a2000011680000113200001126000010b8000010b200001072000010660000103a0000103600000ea700000de300000da700000d73
def links : Nat := 0xc400cfcecdbeccbc00d0cf00bbcbbab9ca00c1cdcbb700c9b5b40000c8c70000c60000c500c4c3c2c1c0aa0000c2bfbb00b79d009c00c0beba9db600b39b00aabdb900b5b300b20000bcb89cb49bb20000009a9998b10000970000b000aead008fac00b00000a9a88900a600af008a00a585a483009400a8a500a38180009300a7a4a20000a10091a8007d00a07a9f00ac87007c9f789e0000aba3a076000074730000006e6d006c6b006a706e000000690068676f6c69000000650064006a67660064006300000096959461930000009600929190008e00009592005f8d0000000094915f008c0000000061908d8c008b000095008a0086008400006100898582007f000000008884817f007e000000878380007e0000928a00007d00007c00908900007b005a78008f8800007a5a0077008e87000079007700000086000000760000758c827b00000074000000817a0000740059000000790000730000728b7f5a007400007100007e77005971000000566a670000644d000000000062494847460000006200454443000000620000403f003e00004900400060003c000046003e3c3a390000004260380000370000000000000000000000620000003600353400490000360033323100470000353230005e004600003431005e00000000360000002d005d430035002d2b002a004200332e00005c00000000322d005c00280000005e2a28270000006033000000002625003c310000000000005b395e00002422000000000000000000000000000000000000000000000000000000000000000055545300520000585500005100005000575400004f00004e000000504e4c004b000000000000000000000000004a000000000000000049000042000000000047000041000000004a0000000000000000000000003d00000000000000000000000000470000003b00000000000000000000000000443f00000000000000003d00000000000000413b0000000000004a00000000000000004800000000003000000000000000000000000000000000002f000000000000000000002c4400000000002b00000000000000000000000000340000002a000000000000000029000000000000002900000000003100000028000000000000000000000000002f0000000000004036000000000000003e34000000000000003d00000000000000000032000000260000000000000000000000233a0000000000220000002f00000000000000382e000000000000001c2c0000001a001900002900000000000000000025000000210000001b231900180000000027220000000000000017000000200015000016200000001300121700001100000f00000000110000000c001f0000100000001e000b00000f0c001e00000000000d1f000b000000201000000000000008150e0000000000001d000d00000008001d00141f00000007000600131e09000000000005120b08000000050000000a1d060004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000030100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def get (i : Nat) : Row :=
  let r := rows >>> (32*i)
  ⟨r.testBit 0,(r >>> 1) &&& 511,(r >>> 10) &&& 15,(r >>> 14) &&& 262143⟩
def link (j i : Nat) := (links >>> (72*j + 8*i)) &&& 255
def verify := checkRow get link
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b0 : span verify 12 0=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b12 : span verify 12 12=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b24 : span verify 12 24=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b36 : span verify 12 36=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b48 : span verify 12 48=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b60 : span verify 12 60=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b72 : span verify 12 72=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b84 : span verify 12 84=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b96 : span verify 12 96=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b108 : span verify 12 108=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b120 : span verify 12 120=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b132 : span verify 12 132=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b144 : span verify 12 144=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b156 : span verify 6 156=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b162 : span verify 5 162=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b167 : span verify 5 167=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b172 : span verify 4 172=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b176 : span verify 5 176=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b181 : span verify 6 181=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b187 : span verify 6 187=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b193 : span verify 4 193=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b197 : span verify 1 197=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b198 : span verify 1 198=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b199 : span verify 1 199=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b200 : span verify 1 200=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b201 : span verify 2 201=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b203 : span verify 2 203=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b205 : span verify 2 205=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b207 : span verify 2 207=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b209 : span verify 1 209=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b210 : span verify 1 210=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b211 : span verify 1 211=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b212 : span verify 1 212=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b213 : span verify 1 213=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b214 : span verify 1 214=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b215 : span verify 1 215=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b216 : span verify 1 216=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b217 : span verify 1 217=true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem b218 : span verify 1 218=true := by decide +kernel
theorem allRows : span verify 219 0=true := (@span_join _ 187 0 32 (@span_join _ 108 0 79 (@span_join _ 48 0 60 (@span_join _ 24 0 24 (@span_join _ 12 0 12 b0 b12) (@span_join _ 12 24 12 b24 b36)) (@span_join _ 24 48 36 (@span_join _ 12 48 12 b48 b60) (@span_join _ 12 72 24 b72 (@span_join _ 12 84 12 b84 b96)))) (@span_join _ 54 108 25 (@span_join _ 24 108 30 (@span_join _ 12 108 12 b108 b120) (@span_join _ 12 132 18 b132 (@span_join _ 12 144 6 b144 b156))) (@span_join _ 10 162 15 (@span_join _ 5 162 5 b162 b167) (@span_join _ 4 172 11 b172 (@span_join _ 5 176 6 b176 b181))))) (@span_join _ 22 187 10 (@span_join _ 13 187 9 (@span_join _ 10 187 3 (@span_join _ 6 187 4 b187 b193) (@span_join _ 1 197 2 b197 (@span_join _ 1 198 1 b198 b199))) (@span_join _ 3 200 6 (@span_join _ 1 200 2 b200 b201) (@span_join _ 2 203 4 b203 (@span_join _ 2 205 2 b205 b207)))) (@span_join _ 5 209 5 (@span_join _ 2 209 3 (@span_join _ 1 209 1 b209 b210) (@span_join _ 1 211 2 b211 (@span_join _ 1 212 1 b212 b213))) (@span_join _ 2 214 3 (@span_join _ 1 214 1 b214 b215) (@span_join _ 1 216 2 b216 (@span_join _ 1 217 1 b217 b218))))))
theorem known : ∀ i<219, (get i).goal := rows_sound get link _ (fun i hi => span_ok allRows i (Nat.zero_le _) (by simpa using hi))
theorem s2 : Bad 11 (full true 2) := known 210 (by decide)
theorem s4 : Bad 11 (full true 4) := known 211 (by decide)
theorem s8 : Bad 11 (full true 8) := known 212 (by decide)
theorem s16 : Bad 12 (full true 16) := known 216 (by decide)
theorem s32 : Bad 11 (full true 32) := known 213 (by decide)
theorem s64 : Bad 12 (full true 64) := known 217 (by decide)
theorem s128 : Bad 12 (full true 128) := known 218 (by decide)
theorem s256 : Bad 11 (full true 256) := known 214 (by decide)
theorem p16 : Bad 12 (full false 16) := known 215 (by decide)
theorem p1 : Bad 11 (full false 1) := known 209 (by decide)
end Cert.Compact.Data

namespace Cert.Compact
open PEqualNP.Outside.L_meta_2309_aux.Main2331
def orbit (m : Nat) (v : Fin 9) := compHom (proj m) (homG (gOfV v))
theorem orbit_bound (m k : Nat) (v : Fin 9) (b : Bad k (full false m))
    (check : projectedOK (proj m) raw (full false m)=true) : ¬ Feasible (orbit m v) k raw.toFinset := by
  intro f
  apply bound_of _ _ _ _ b check
  obtain ⟨j,hj,t,S,hl,sub⟩ := f
  refine ⟨j,hj,t,S,hl,?_⟩
  intro x hx
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub hx)
  exact Finset.mem_image_of_mem _ (action_raw_subset (gOfV v) (Finset.mem_image_of_mem _ ha))
theorem orbit_zero (m : Nat) (v : Fin 9) (h : (proj m).fn (rawImage (gOfV v) v)=zero) :
    (orbit m v).fn (raw.getD v.val zero)=zero := by
  change (proj m).fn (action (gOfV v) _)=zero
  rw [←rawImage_eq]
  exact h

theorem ordinary (small : Bad 12 (full false 16)) (large : Bad 11 (full false 1)) : Bad 14 raw := by
  apply finished 14 rootWires raw rfl (by decide +kernel) (by decide +kernel) raw_nd (by decide +kernel)
  · intro p hp
    simp only [rootWires,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact slack_of (orbit 1 0) (orbit_zero 1 0 (by decide +kernel)) (orbit_bound 1 _ 0 large (by decide +kernel))
    · exact slack_of (orbit 1 1) (orbit_zero 1 1 (by decide +kernel)) (orbit_bound 1 _ 1 large (by decide +kernel))
    · exact slack_of (orbit 1 2) (orbit_zero 1 2 (by decide +kernel)) (orbit_bound 1 _ 2 large (by decide +kernel))
    · exact slack_of (orbit 1 3) (orbit_zero 1 3 (by decide +kernel)) (orbit_bound 1 _ 3 large (by decide +kernel))
    · exact zero_of (orbit 16 4) (orbit_zero 16 4 (by decide +kernel)) (orbit_bound 16 _ 4 small (by decide +kernel))
    · exact slack_of (orbit 1 5) (orbit_zero 1 5 (by decide +kernel)) (orbit_bound 1 _ 5 large (by decide +kernel))
    · exact zero_of (orbit 16 6) (orbit_zero 16 6 (by decide +kernel)) (orbit_bound 16 _ 6 small (by decide +kernel))
    · exact zero_of (orbit 16 7) (orbit_zero 16 7 (by decide +kernel)) (orbit_bound 16 _ 7 small (by decide +kernel))
    · exact slack_of (orbit 1 8) (orbit_zero 1 8 (by decide +kernel)) (orbit_bound 1 _ 8 large (by decide +kernel))
  · intro t ht
    exact rootImpossible t (by change t+9≤15 at ht; omega)

def signedTags : Nat := 108116
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem top0 : PEqualNP.Outside.L_meta_2309_aux.Cache.run PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 0 (ws true 0 signedTags)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem top1 : PEqualNP.Outside.L_meta_2309_aux.Cache.run PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 1 (ws true 0 signedTags)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem top2 : PEqualNP.Outside.L_meta_2309_aux.Cache.run PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 2 (ws true 0 signedTags)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem top3 : PEqualNP.Outside.L_meta_2309_aux.Cache.run PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 3 (ws true 0 signedTags)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem top4 : PEqualNP.Outside.L_meta_2309_aux.Cache.run PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 4 (ws true 0 signedTags)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem top5 : PEqualNP.Outside.L_meta_2309_aux.Cache.run PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 5 (ws true 0 signedTags)=false := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem top6 : PEqualNP.Outside.L_meta_2309_aux.Cache.run PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 6 (ws true 0 signedTags)=false := by decide +kernel
theorem signed (c1 : Bad 11 (full true 2)) (c2 : Bad 11 (full true 4)) (c3 : Bad 11 (full true 8)) (c4 : Bad 12 (full true 16)) (c5 : Bad 11 (full true 32)) (c6 : Bad 12 (full true 64)) (c7 : Bad 12 (full true 128)) (c8 : Bad 11 (full true 256)) : Bad 14 PEqualNP.Outside.L_meta_2309_aux.Samples.inputs := by
  have same : PEqualNP.Outside.L_meta_2309_aux.Samples.inputs = full true 0 := by decide +kernel
  rw [same]
  apply fromRows true 0 14 signedTags (by decide +kernel) (by decide +kernel)
  · intro i hi tagged
    have bound : i<9 := List.mem_range.mp (List.mem_of_mem_filter hi)
    interval_cases i
    · exact (tagged (by decide +kernel)).elim
    · exact c1
    · exact c2
    · exact c3
    · exact c4
    · exact c5
    · exact c6
    · exact c7
    · exact c8
  · intro t ht
    change t+9≤15 at ht
    have bound : t ≤ 6 := by omega
    interval_cases t
    · exact PEqualNP.Outside.L_meta_2309_aux.Cache.run_sound PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 0 _ (fun k hk u hu => PEqualNP.Outside.L_meta_2309_aux.Cuts.known k hk u (by omega)) top0
    · exact PEqualNP.Outside.L_meta_2309_aux.Cache.run_sound PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 1 _ (fun k hk u hu => PEqualNP.Outside.L_meta_2309_aux.Cuts.known k hk u (by omega)) top1
    · exact PEqualNP.Outside.L_meta_2309_aux.Cache.run_sound PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 2 _ (fun k hk u hu => PEqualNP.Outside.L_meta_2309_aux.Cuts.known k hk u (by omega)) top2
    · exact PEqualNP.Outside.L_meta_2309_aux.Cache.run_sound PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 3 _ (fun k hk u hu => PEqualNP.Outside.L_meta_2309_aux.Cuts.known k hk u (by omega)) top3
    · exact PEqualNP.Outside.L_meta_2309_aux.Cache.run_sound PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 4 _ (fun k hk u hu => PEqualNP.Outside.L_meta_2309_aux.Cuts.known k hk u (by omega)) top4
    · exact PEqualNP.Outside.L_meta_2309_aux.Cache.run_sound PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 5 _ (fun k hk u hu => PEqualNP.Outside.L_meta_2309_aux.Cuts.known k hk u (by omega)) top5
    · exact PEqualNP.Outside.L_meta_2309_aux.Cache.run_sound PEqualNP.Outside.L_meta_2309_aux.Cuts.tab 14 6 _ (fun k hk u hu => PEqualNP.Outside.L_meta_2309_aux.Cuts.known k hk u (by omega)) top6
end Cert.Compact

end PEqualNP.Outside.L_meta_2309_aux

theorem PEqualNP.Outside.L_meta_2309 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 ≤ (1 : ℕ) → False := by
  dsimp only
  intro C fan first correct size readers
  obtain ⟨D,b,df,smaller,_,corresponds⟩ := PEqualNP.Outside.L_meta_2309_aux.contract C fan first readers
  cases b with
  | false =>
    have works : PEqualNP.MetaComplexity.circuitFun 9 D = PEqualNP.Outside.L_meta_2309_aux.Main2331.edgeF := by
      funext x
      have e : (fun i : Fin 9 => if i=0 then false != x 0 else x i) = x := by
        funext i
        by_cases hi : i=0 <;> simp [hi]
      have q := corresponds x
      rw [e,correct] at q
      exact q.symm
    have reaches := PEqualNP.Outside.L_meta_2309_aux.Main2331.circuit_target D df (fun x => congrFun works x)
    obtain ⟨k,t,S,hk,live,sub⟩ := PEqualNP.Outside.L_meta_2309_aux.Main2331.extract D.gates _ PEqualNP.Outside.L_meta_2309_aux.Main2331.raw_valid df reaches
    have limit : D.gates.length ≤ 14 := by change D.size ≤ 14; omega
    exact PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.ordinary PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.p16 PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.p1 k (hk.trans limit) t S live sub
  | true =>
    have works : ∀ x, D.eval (List.ofFn (PEqualNP.Outside.L_meta_2309_aux.Samples.flip x)) = PEqualNP.Outside.L_meta_2309_aux.Main2331.edgeF x := by
      intro x
      have e : (fun i : Fin 9 => if i=0 then true != x 0 else x i) = PEqualNP.Outside.L_meta_2309_aux.Samples.flip x := by
        funext i
        by_cases hi : i=0 <;> simp [PEqualNP.Outside.L_meta_2309_aux.Samples.flip,hi]
      have q := corresponds x
      rw [e,correct] at q
      exact q.symm
    have reaches := PEqualNP.Outside.L_meta_2309_aux.Samples.signed_target D df works
    obtain ⟨k,t,S,hk,live,sub⟩ := PEqualNP.Outside.L_meta_2309_aux.Main2331.extract D.gates _ PEqualNP.Outside.L_meta_2309_aux.Samples.valid_inputs df reaches
    have limit : D.gates.length ≤ 14 := by change D.size ≤ 14; omega
    exact PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.signed PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.s2 PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.s4 PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.s8 PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.s16 PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.s32 PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.s64 PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.s128 PEqualNP.Outside.L_meta_2309_aux.Cert.Compact.Data.s256 k (hk.trans limit) t S live sub
