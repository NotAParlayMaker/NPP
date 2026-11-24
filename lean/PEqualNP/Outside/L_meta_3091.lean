import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3091_aux
namespace Research.Basis1868
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
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
lemma perm_impossible {k t : Nat} {w z : List Wire} (hp : w.Perm z)
    (hz : Impossible k t z) : Impossible k t w := by
  intro m hm S τ hrep h
  apply hz m hm S τ _ h
  have hpS : (sigsOf w).Perm (sigsOf z) := hp.map Prod.fst
  refine ⟨hpS.nodup_iff.mp hrep.1, ?_, fun x hx => hrep.2.2 x (hp.mem_iff.mpr hx)⟩
  rw [← hrep.2.1]; ext a
  simp only [List.mem_toFinset, hpS.mem_iff]
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
end Research.Basis1868

namespace Research.Conflict1868
open Research.Basis1868

abbrev I := Fin 414
abbrev P (a : Sig) (p : I) := bit true p a
abbrev N (a : Sig) (n : I) := bit false n a
def D (p n : I) (a : Sig) : Prop := P a p ≠ N a n
def op (d x y : Bool) : Bool := if d then x || y else x && y

lemma bop (s i d a b) : bit s i (bin d a b) = op d (bit s i a) (bit s i b) := bit_bin s i d a b
lemma d_bin {d p n a b} (hd : D p n (bin d a b)) : D p n a ∨ D p n b := by
  by_contra! hn
  apply hd
  unfold P N
  rw [bop,bop]
  exact congrArg₂ (op d) (not_ne_iff.mp hn.1) (not_ne_iff.mp hn.2)

lemma d_neg {p n a} (hv : Valid a) : D p n (neg a) ↔ D p n a := by
  unfold D P N
  rw [bit_neg _ _ hv,bit_neg _ _ hv]
  cases bit true p a <;> cases bit false n a <;> decide

lemma pair_sep {k t S} (hl : Live k t S) (p n : I) : ∃ a ∈ S, D p n a := by
  induction hl with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [D,P,N,bit,target,testBit_top,p.isLt]
  | unary ha _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨_, Finset.mem_insert_self _ _, (d_neg ha.1).mp h⟩
    · exact ⟨_, Finset.mem_insert_of_mem hc, h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rcases d_bin h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc),h⟩

def Unique (p n : I) (S : Finset Sig) (a : Sig) := ∀ c ∈ S, D p n c → c = a
def Mark (p n : I) (S : Finset Sig) (a : Sig) :=
  D p n a ∧ (∃ m, Unique p m S a) ∧ ∃ q, Unique q n S a
def Edge (S : Finset Sig) (a b : Sig) :=
  ∃ p n, Mark p n S a ∧ Mark p n S b

lemma unique_diff {k t z U p n} (h : Live k t (insert z U)) (hu : ∀ c ∈ U, ¬ D p n c) :
    D p n z := by
  obtain ⟨c,hc,hd⟩ := pair_sep h p n
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hd
  · exact (hu c hc hd).elim

lemma transUnique {p n a z S U} (h : Unique p n S a) (hu : U ⊆ S) (ha : a ∉ U) :
    Unique p n (insert z U) z := by
  intro c hc hd
  rcases Finset.mem_insert.mp hc with h | hc
  · exact h
  · exact (ha (h c (hu hc) hd ▸ hc)).elim

lemma bin_unique_keep {d p n a b c U} (h : Unique p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Unique p n (insert (bin d a b) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · rcases d_bin hd with h' | h'
    · exact (hna (h _ (Finset.mem_insert_self _ _) h').symm).elim
    · exact (hnb (h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h').symm).elim
  · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) hd

lemma neg_unique_keep {p n a c U} (h : Unique p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Unique p n (insert (neg a) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · exact (hna (h _ (Finset.mem_insert_self _ _) ((d_neg hv).mp hd)).symm).elim
  · exact h _ (Finset.mem_insert_of_mem hu) hd

lemma bin_mark_keep {d p n a b c U} (h : Mark p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Mark p n (insert (bin d a b) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,bin_unique_keep hm hna hnb⟩,q,bin_unique_keep hq hna hnb⟩

lemma neg_mark_keep {p n a c U} (h : Mark p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Mark p n (insert (neg a) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,neg_unique_keep hm hna hv⟩,q,neg_unique_keep hq hna hv⟩

lemma neg_mark_move {p n a U} (h : Mark p n (insert a U) a)
    (ha : a ∉ U) (hv : Valid a) : Mark p n (insert (neg a) U) (neg a) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a U := Finset.subset_insert _ _
  exact ⟨(d_neg hv).mpr hd,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩

lemma mix : ∀ (d ap an bp bn al ar : Bool), ap ≠ an →
    op d ap bp ≠ op d al bp → op d ar bn ≠ op d an bn →
    bp = bn ∧ op d ap bp ≠ op d an bn := by decide +kernel

lemma bin_mark_move {k t d p n a b U} (tail : Live k t (insert (bin d a b) U))
    (h : Mark p n (insert a (insert b U)) a) (ha : a ∉ U) (hab : a ≠ b) :
    ¬ D p n b ∧ Mark p n (insert (bin d a b) U) (bin d a b) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a (insert b U) := fun _ hc => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc)
  have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have bm : P b p = N b m := not_ne_iff.mp (fun h => hab (hm _ hb h).symm)
  have bq : P b q = N b n := not_ne_iff.mp (fun h => hab (hq _ hb h).symm)
  have zm := unique_diff tail (p := p) (n := m) (fun c hc h => ha (hm c (sub hc) h ▸ hc))
  have zq := unique_diff tail (p := q) (n := n) (fun c hc h => ha (hq c (sub hc) h ▸ hc))
  change bit true p (bin d a b) ≠ bit false m (bin d a b) at zm
  change bit true q (bin d a b) ≠ bit false n (bin d a b) at zq
  rw [bop,bop] at zm zq
  change op d (P a p) (P b p) ≠ op d (N a m) (N b m) at zm
  change op d (P a q) (P b q) ≠ op d (N a n) (N b n) at zq
  rw [← bm] at zm
  rw [bq] at zq
  have hh := mix _ _ _ _ _ _ _ hd zm zq
  refine ⟨fun h => h hh.1,⟨?_,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩⟩
  unfold D P N
  rw [bop,bop]
  exact hh.2


def Colored (S : Finset Sig) (k : Nat) :=
  ∃ f : Sig → Nat, (∀ x ∈ S, f x < k) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Edge S x y → f x ≠ f y

lemma transfer {S T R : Finset Sig} {k : Nat} (lift : Sig → Sig) (h : Colored T k)
    (hm : ∀ x ∈ S, x ∉ R → lift x ∈ T)
    (he : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ R → y ∉ R → Edge S x y →
      lift x ≠ lift y ∧ Edge T (lift x) (lift y)) : Colored S (k + R.card) := by
  classical
  obtain ⟨f,bound,dist⟩ := h
  let g := Fintype.equivFin (↥R)
  let get (x : Sig) := if hx : x ∈ R then k + (g ⟨x,hx⟩).val else f (lift x)
  refine ⟨get,?_,?_⟩
  · intro x hx
    by_cases hxr : x ∈ R
    · simp only [get,dite_eq_left hxr,Nat.add_lt_add_iff_left]
      simpa using (g ⟨x,hxr⟩).isLt
    · simp only [get,dite_eq_right hxr]
      have := bound _ (hm _ hx hxr)
      omega
  · intro x hx y hy hxy ex hf
    by_cases hxr : x ∈ R <;> by_cases hyr : y ∈ R
    · simp only [get,dite_eq_left hxr,dite_eq_left hyr,Nat.add_right_inj] at hf
      exact hxy (congrArg Subtype.val (g.injective (Fin.ext hf)))
    · simp only [get,dite_eq_left hxr,dite_eq_right hyr] at hf
      have := bound _ (hm _ hy hyr)
      omega
    · simp only [get,dite_eq_right hxr,dite_eq_left hyr] at hf
      have := bound _ (hm _ hx hxr)
      omega
    · obtain ⟨ne,edge⟩ := he _ hx _ hy hxy hxr hyr ex
      simp only [get,dite_eq_right hxr,dite_eq_right hyr] at hf
      exact dist _ (hm _ hx hxr) _ (hm _ hy hyr) ne edge hf

lemma unary_col {k U a} (hv : Valid a) (fresh : neg a ∉ insert a U)
    (col : Colored (insert (neg a) U) k) :
    ∃ l, Colored (insert a U) l ∧ l + (insert a U).card ≤ k + (insert (neg a) U).card := by
  let R := ({a} : Finset Sig) ∩ U
  let f (x : Sig) := if x = a then neg a else x
  have mem (x) (hx : x ∈ insert a U) (_ : x ∉ R) : f x ∈ insert (neg a) U := by
    by_cases e : x = a
    · simp [f,e]
    · simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left e)
  have keep (x p n) (hxr : x ∉ R) (mx : Mark p n (insert a U) x) :
      Mark p n (insert (neg a) U) (f x) := by
    by_cases e : x = a
    · subst x
      have ha : a ∉ U := by simpa [R] using hxr
      simpa [f] using neg_mark_move mx ha hv
    · simpa [f,e] using neg_mark_keep mx e hv
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy hxr hyr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n hxr mx,keep y p n hyr my⟩
    by_cases ex : x = a <;> by_cases ey : y = a
    · exact (hxy (ex.trans ey.symm)).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : neg a ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> simp [R,ha,Finset.card_insert_of_notMem] <;> omega

lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,Nat.and_comm,Nat.or_comm]

lemma binary_col {k t u U a b d} (hab : a ≠ b) (fresh : bin d a b ∉ insert a (insert b U))
    (tail : Live k t (insert (bin d a b) U)) (col : Colored (insert (bin d a b) U) u) :
    ∃ l, Colored (insert a (insert b U)) l ∧
      l + (insert a (insert b U)).card ≤ u + (insert (bin d a b) U).card + 1 := by
  let R := ({a,b} : Finset Sig) ∩ U
  let z := bin d a b
  let f (x : Sig) := if x = a ∨ x = b then z else x
  have mem (x) (hx : x ∈ insert a (insert b U)) (_ : x ∉ R) : f x ∈ insert z U := by
    by_cases e : x = a ∨ x = b
    · simp [f,e]
    · have hU : x ∈ U := by simpa [not_or.mp e |>.1,not_or.mp e |>.2] using hx
      simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem hU
  change z ∉ insert a (insert b U) at fresh
  have left (p n) (ea : a ∉ R) (ma : Mark p n (insert a (insert b U)) a) :=
    bin_mark_move tail ma (by simpa [R] using ea) hab
  have right (p n) (eb : b ∉ R) (mb : Mark p n (insert a (insert b U)) b) :
      ¬ D p n a ∧ Mark p n (insert z U) z := by
    have ha : b ∉ U := by simpa [R] using eb
    rw [Finset.insert_comm] at mb
    rw [bin_swap d a b] at tail
    simpa only [z,bin_swap d b a] using bin_mark_move tail mb ha hab.symm
  have keep (x p n) (xr : x ∉ R) (mx : Mark p n (insert a (insert b U)) x) :
      Mark p n (insert z U) (f x) := by
    by_cases ea : x = a
    · subst x; simpa [f] using (left p n xr mx).2
    by_cases eb : x = b
    · subst x; simpa [f] using (right p n xr mx).2
    simpa [f,ea,eb,z] using bin_mark_keep (d := d) mx ea eb
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy xr yr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n xr mx,keep y p n yr my⟩
    by_cases ex : x = a ∨ x = b <;> by_cases ey : y = a ∨ y = b
    · rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
      · exact (hxy rfl).elim
      · exact ((left p n xr mx).1 my.1).elim
      · exact ((right p n xr mx).1 my.1).elim
      · exact (hxy rfl).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
    simp [R,ha,hb,hab,Finset.card_insert_of_notMem] <;> omega

theorem live_colored {k t S} (l : Live k t S) : ∃ n, Colored S n ∧ n + S.card + t ≤ k + 2 := by
  induction l with
  | stop =>
    refine ⟨1,⟨fun _ => 0,by simp,?_⟩,by simp⟩
    intro x hx y hy hn
    simp only [Finset.mem_singleton] at hx hy
    exact (hn (hx.trans hy.symm)).elim
  | unary ha hf _ ih =>
    obtain ⟨k,hk,hb⟩ := ih
    obtain ⟨u,hu,size⟩ := unary_col ha.1 hf hk
    exact ⟨u,hu,by omega⟩
  | binary _ _ hab hf tail ih =>
    obtain ⟨k,hk,hb⟩ := ih
    obtain ⟨u,hu,size⟩ := binary_col hab hf tail hk
    exact ⟨u,hu,by omega⟩

end Research.Conflict1868

namespace Research.Mono1868
open Research.Basis1868

abbrev I := Fin 414
abbrev P (a : Sig) (p : I) := bit true p a
abbrev N (a : Sig) (n : I) := bit false n a
def pos (x y : Bool) : Prop := x = true ∧ y = false
def D (p n : I) (a : Sig) : Prop := pos (P a p) (N a n)
def op (d x y : Bool) : Bool := if d then x || y else x && y

lemma bop (s i d a b) : bit s i (bin d a b) = op d (bit s i a) (bit s i b) := bit_bin s i d a b
lemma bor : ∀ (d ap an bp bn : Bool), pos (op d ap bp) (op d an bn) → pos ap an ∨ pos bp bn := by
  unfold pos; decide +kernel
lemma d_bin {d p n a b} (hd : D p n (bin d a b)) : D p n a ∨ D p n b := by
  unfold D P N at hd
  rw [bop,bop] at hd
  exact bor _ _ _ _ _ hd
lemma pair_sep {k t S} (hl : Live k t S) (ht : t = 0) (p n : I) : ∃ a ∈ S, D p n a := by
  induction hl with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [D,pos,P,N,bit,target,testBit_top,p.isLt]
  | unary => omega
  | binary ha hb _ _ _ ih =>
    obtain ⟨c,hc,h⟩ := ih ht
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rcases d_bin h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc),h⟩

def Unique (p n : I) (S : Finset Sig) (a : Sig) := ∀ c ∈ S, D p n c → c = a
def Mark (p n : I) (S : Finset Sig) (a : Sig) :=
  D p n a ∧ (∃ m, Unique p m S a) ∧ ∃ q, Unique q n S a
def Edge (S : Finset Sig) (a b : Sig) :=
  ∃ p n, Mark p n S a ∧ Mark p n S b

lemma unique_diff {k t z U p n} (h : Live k t (insert z U)) (ht : t=0) (hu : ∀ c ∈ U, ¬ D p n c) :
    D p n z := by
  obtain ⟨c,hc,hd⟩ := pair_sep h ht p n
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hd
  · exact (hu c hc hd).elim

lemma transUnique {p n a z S U} (h : Unique p n S a) (hu : U ⊆ S) (ha : a ∉ U) :
    Unique p n (insert z U) z := by
  intro c hc hd
  rcases Finset.mem_insert.mp hc with h | hc
  · exact h
  · exact (ha (h c (hu hc) hd ▸ hc)).elim

lemma bin_unique_keep {d p n a b c U} (h : Unique p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Unique p n (insert (bin d a b) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · rcases d_bin hd with h' | h'
    · exact (hna (h _ (Finset.mem_insert_self _ _) h').symm).elim
    · exact (hnb (h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h').symm).elim
  · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) hd

lemma bin_mark_keep {d p n a b c U} (h : Mark p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Mark p n (insert (bin d a b) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,bin_unique_keep hm hna hnb⟩,q,bin_unique_keep hq hna hnb⟩

lemma mix : ∀ (d ap an bp bn al ar bm bq : Bool), pos ap an →
    ¬ pos bp bm → ¬ pos bq bn →
    pos (op d ap bp) (op d al bm) → pos (op d ar bq) (op d an bn) →
    ¬ pos bp bn ∧ pos (op d ap bp) (op d an bn) := by unfold pos; decide +kernel

lemma bin_mark_move {k t d p n a b U} (tail : Live k t (insert (bin d a b) U)) (ht : t = 0)
    (h : Mark p n (insert a (insert b U)) a) (ha : a ∉ U) (hab : a ≠ b) :
    ¬ D p n b ∧ Mark p n (insert (bin d a b) U) (bin d a b) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a (insert b U) := fun _ hc => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc)
  have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have bm : ¬ pos (P b p) (N b m) := fun h => hab (hm _ hb h).symm
  have bq : ¬ pos (P b q) (N b n) := fun h => hab (hq _ hb h).symm
  have zm := unique_diff tail ht (p := p) (n := m) (fun c hc h => ha (hm c (sub hc) h ▸ hc))
  have zq := unique_diff tail ht (p := q) (n := n) (fun c hc h => ha (hq c (sub hc) h ▸ hc))
  unfold D P N at zm zq
  rw [bop,bop] at zm zq
  have hh := mix _ _ _ _ _ _ _ _ _ hd bm bq zm zq
  refine ⟨hh.1,⟨?_,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩⟩
  unfold D P N
  rw [bop,bop]
  exact hh.2


def Colored (S : Finset Sig) (k : Nat) :=
  ∃ f : Sig → Nat, (∀ x ∈ S, f x < k) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Edge S x y → f x ≠ f y

lemma transfer {S T R : Finset Sig} {k : Nat} (lift : Sig → Sig) (h : Colored T k)
    (hm : ∀ x ∈ S, x ∉ R → lift x ∈ T)
    (he : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ∉ R → y ∉ R → Edge S x y →
      lift x ≠ lift y ∧ Edge T (lift x) (lift y)) : Colored S (k + R.card) := by
  classical
  obtain ⟨f,bound,dist⟩ := h
  let g := Fintype.equivFin (↥R)
  let get (x : Sig) := if hx : x ∈ R then k + (g ⟨x,hx⟩).val else f (lift x)
  refine ⟨get,?_,?_⟩
  · intro x hx
    by_cases hxr : x ∈ R
    · simp only [get,dite_eq_left hxr,Nat.add_lt_add_iff_left]
      simpa using (g ⟨x,hxr⟩).isLt
    · simp only [get,dite_eq_right hxr]
      have := bound _ (hm _ hx hxr)
      omega
  · intro x hx y hy hxy ex hf
    by_cases hxr : x ∈ R <;> by_cases hyr : y ∈ R
    · simp only [get,dite_eq_left hxr,dite_eq_left hyr,Nat.add_right_inj] at hf
      exact hxy (congrArg Subtype.val (g.injective (Fin.ext hf)))
    · simp only [get,dite_eq_left hxr,dite_eq_right hyr] at hf
      have := bound _ (hm _ hy hyr)
      omega
    · simp only [get,dite_eq_right hxr,dite_eq_left hyr] at hf
      have := bound _ (hm _ hx hxr)
      omega
    · obtain ⟨ne,edge⟩ := he _ hx _ hy hxy hxr hyr ex
      simp only [get,dite_eq_right hxr,dite_eq_right hyr] at hf
      exact dist _ (hm _ hx hxr) _ (hm _ hy hyr) ne edge hf

lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,Nat.and_comm,Nat.or_comm]

lemma binary_col {k t u U a b d} (hab : a ≠ b) (fresh : bin d a b ∉ insert a (insert b U))
    (tail : Live k t (insert (bin d a b) U)) (ht : t=0) (col : Colored (insert (bin d a b) U) u) :
    ∃ l, Colored (insert a (insert b U)) l ∧
      l + (insert a (insert b U)).card ≤ u + (insert (bin d a b) U).card + 1 := by
  let R := ({a,b} : Finset Sig) ∩ U
  let z := bin d a b
  let f (x : Sig) := if x = a ∨ x = b then z else x
  have mem (x) (hx : x ∈ insert a (insert b U)) (_ : x ∉ R) : f x ∈ insert z U := by
    by_cases e : x = a ∨ x = b
    · simp [f,e]
    · have hU : x ∈ U := by simpa [not_or.mp e |>.1,not_or.mp e |>.2] using hx
      simp only [f,ite_eq_right e]
      exact Finset.mem_insert_of_mem hU
  change z ∉ insert a (insert b U) at fresh
  have left (p n) (ea : a ∉ R) (ma : Mark p n (insert a (insert b U)) a) :=
    bin_mark_move tail ht ma (by simpa [R] using ea) hab
  have right (p n) (eb : b ∉ R) (mb : Mark p n (insert a (insert b U)) b) :
      ¬ D p n a ∧ Mark p n (insert z U) z := by
    have ha : b ∉ U := by simpa [R] using eb
    rw [Finset.insert_comm] at mb
    rw [bin_swap d a b] at tail
    simpa only [z,bin_swap d b a] using bin_mark_move tail ht mb ha hab.symm
  have keep (x p n) (xr : x ∉ R) (mx : Mark p n (insert a (insert b U)) x) :
      Mark p n (insert z U) (f x) := by
    by_cases ea : x = a
    · subst x; simpa [f] using (left p n xr mx).2
    by_cases eb : x = b
    · subst x; simpa [f] using (right p n xr mx).2
    simpa [f,ea,eb,z] using bin_mark_keep (d := d) mx ea eb
  have h := transfer (R := R) f col mem (by
    intro x hx y hy hxy xr yr ⟨p,n,mx,my⟩
    refine ⟨?_,p,n,keep x p n xr mx,keep y p n yr my⟩
    by_cases ex : x = a ∨ x = b <;> by_cases ey : y = a ∨ y = b
    · rcases ex with rfl | rfl <;> rcases ey with rfl | rfl
      · exact (hxy rfl).elim
      · exact ((left p n xr mx).1 my.1).elim
      · exact ((right p n xr mx).1 my.1).elim
      · exact (hxy rfl).elim
    · simp only [f,ite_eq_left ex,ite_eq_right ey]
      exact fun eq => fresh (eq ▸ hy)
    · simp only [f,ite_eq_right ex,ite_eq_left ey]
      exact fun eq => fresh (eq ▸ hx)
    · simpa [f,ex,ey] using hxy)
  refine ⟨_,h,?_⟩
  have hf : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  rw [Finset.card_insert_of_notMem hf]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;>
    simp [R,ha,hb,hab,Finset.card_insert_of_notMem] <;> omega

theorem live_colored {k t S} (l : Live k t S) (ht : t=0) : ∃ n, Colored S n ∧ n + S.card + t ≤ k + 2 := by
  induction l with
  | stop =>
    refine ⟨1,⟨fun _ => 0,by simp,?_⟩,by simp⟩
    intro x hx y hy hn
    simp only [Finset.mem_singleton] at hx hy
    exact (hn (hx.trans hy.symm)).elim
  | unary => omega
  | binary _ _ hab hf tail ih =>
    obtain ⟨k,hk,hb⟩ := ih ht
    obtain ⟨u,hu,size⟩ := binary_col hab hf tail ht hk
    exact ⟨u,hu,by omega⟩

end Research.Mono1868

namespace Research.ColorSearch1868
open Research.Basis1868
abbrev Signs := List (Sig × Nat)

def paint (n : Nat) : Signs → (Nat → Nat) → Bool
  | [], _ => true
  | x::xs, bins =>
    (List.range n).any fun i => ((bins i &&& x.2) == 0) &&
      paint n xs (fun j => if i=j then bins j ||| x.2 else bins j)

lemma paint_ok {n xs} (bins : Nat → Nat) (f : Sig → Nat) (nd : (xs.map Prod.fst).Nodup)
    (bd : ∀ x ∈ xs, f x.1 < n) (ok : ∀ x ∈ xs, bins (f x.1) &&& x.2 = 0)
    (sep : ∀ x ∈ xs, ∀ y ∈ xs, x.1 ≠ y.1 → f x.1 = f y.1 → x.2 &&& y.2 = 0) :
    paint n xs bins = true := by
  induction xs generalizing bins with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hn,hnd⟩ := List.nodup_cons.mp nd
    apply List.any_eq_true.mpr
    refine ⟨f x.1,List.mem_range.mpr (bd _ (by simp)),Bool.and_eq_true_iff.mpr ⟨by
      simp only [beq_iff_eq]; exact ok _ (by simp),?_⟩⟩
    apply ih _ hnd (fun a ha => bd a (List.mem_cons_of_mem _ ha)) _ (fun a ha b hb =>
      sep a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    intro y hy
    have hy' := List.mem_cons_of_mem x hy
    by_cases e : f x.1 = f y.1
    · have ne : x.1 ≠ y.1 := fun eq => hn (List.mem_map.mpr ⟨y,hy,eq.symm⟩)
      simp [e,Nat.and_or_distrib_right,ok y hy',sep x (List.mem_cons_self ..) y hy' ne e]
    · simpa [e] using ok y hy'

end Research.ColorSearch1868
namespace Research.Grid1868
open Research.Basis1868

abbrev Ix := Fin 256
def coord (side : Bool) (i : Nat) := if side then i / 16 * 16 else i % 16
def ix (s : Bool) (i : Ix) : Fin 414 := ⟨coord s i.val,by unfold coord; cases s <;> have := i.isLt <;> simp <;> omega⟩

def hop (n mask x : Nat) : Nat := (x ||| ((x <<< n) &&& (mask <<< n))) ||| ((x >>> n) &&& mask)
def safe (s : Bool) (n mask : Nat) : Prop :=
  ∀ i : Ix, (((mask <<< n).testBit i.val = true → n ≤ i.val ∧ coord s (i.val-n) = coord s i.val) ∧
    (mask.testBit i.val = true → i.val+n < 256 ∧ coord s (i.val+n) = coord s i.val))
instance (s n m) : Decidable (safe s n m) := by unfold safe; infer_instance

lemma hop_sound {s n mask x} (ok : safe s n mask) (gain : Nat → Prop)
    (base : ∀ i : Ix, x.testBit i.val = true → gain (coord s i.val)) (i : Ix)
    (h : (hop n mask x).testBit i.val = true) : gain (coord s i.val) := by
  simp only [hop,Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with (h | ⟨ha,hm⟩) | ⟨ha,hm⟩
  · exact base i h
  · obtain ⟨hi,co⟩ := (ok i).1 hm
    rw [Nat.testBit_shiftLeft] at ha
    have hab : x.testBit (i.val - n) = true := by simpa [hi] using ha
    let j : Ix := ⟨i.val-n,by have := i.isLt; omega⟩
    exact co ▸ base j hab
  · obtain ⟨bound,co⟩ := (ok i).2 hm
    rw [Nat.testBit_shiftRight] at ha
    let j : Ix := ⟨i.val+n,bound⟩
    exact co ▸ base j (by simpa [j,Nat.add_comm] using ha)
def m0 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
lemma s0 : safe true 1 m0 := by decide +kernel
def m1 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
lemma s1 : safe true 2 m1 := by decide +kernel
def m2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
lemma s2 : safe true 4 m2 := by decide +kernel
def m3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
lemma s3 : safe true 8 m3 := by decide +kernel
def m4 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
lemma s4 : safe false 16 m4 := by decide +kernel
def m5 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
lemma s5 : safe false 32 m5 := by decide +kernel
def m6 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
lemma s6 : safe false 64 m6 := by decide +kernel
def m7 : Nat := 0xffffffffffffffffffffffffffffffff
lemma s7 : safe false 128 m7 := by decide +kernel
def row (x : Nat) := (hop 8 m3 (hop 4 m2 (hop 2 m1 (hop 1 m0 x))))
lemma row_sound (x : Nat) (gain : Nat → Prop) (base : ∀ i : Ix, x.testBit i.val = true → gain (coord true i.val)) (i : Ix) (h : (row x).testBit i.val = true) : gain (coord true i.val) := by
  exact (hop_sound s3 gain (hop_sound s2 gain (hop_sound s1 gain (hop_sound s0 gain base)))) i h
def col (x : Nat) := (hop 128 m7 (hop 64 m6 (hop 32 m5 (hop 16 m4 x))))
lemma col_sound (x : Nat) (gain : Nat → Prop) (base : ∀ i : Ix, x.testBit i.val = true → gain (coord false i.val)) (i : Ix) (h : (col x).testBit i.val = true) : gain (coord false i.val) := by
  exact (hop_sound s7 gain (hop_sound s6 gain (hop_sound s5 gain (hop_sound s4 gain base)))) i h
def unit (side : Bool) : Nat := if side then 0x1000100010001000100010001000100010001000100010001000100010001 else 0xffff
lemma unit_coord : ∀ (s : Bool) (i : Ix), (unit s).testBit i.val = true → coord s i.val = i.val := by decide +kernel

def pick (s yes : Bool) (a : Sig) := let bits := if s then a.1 else a.2
  (if yes then bits else bits ^^^ top) &&& unit s

def spread (s yes : Bool) (a : Sig) :=
  if s then row (pick s yes a) else col (pick s yes a)

lemma spread_sound (s yes : Bool) (a : Sig) (i : Ix) (h : (spread s yes a).testBit i.val = true) :
    bit s (ix s i) a = yes := by
  let gain (n : Nat) := (if s then a.1 else a.2).testBit n = yes
  have initial (j : Ix) (hb : (pick s yes a).testBit j.val = true) : gain (coord s j.val) := by
    simp only [pick,Nat.testBit_and,Bool.and_eq_true] at hb
    rw [unit_coord s j hb.2]
    unfold gain
    have bound : j.val < 414 := by have := j.isLt; omega
    cases yes
    · simpa [Nat.testBit_xor,testBit_top,bound] using hb.1
    · exact hb.1
  change gain (coord s i.val)
  cases s
  · exact col_sound _ gain initial i h
  · exact row_sound _ gain initial i h

end Research.Grid1868

namespace Research.Board1868
open Research.Basis1868
def mult : List (Sig × Nat) → Sig
  | [] => zero
  | o::l => let (atLeastOne,atLeastTwo) := mult l
            (atLeastOne ||| o.2,atLeastTwo ||| (atLeastOne &&& o.2))
end Research.Board1868

namespace Research.LinearWide1868
open Research.Basis1868 Research.Board1868
def maskLo (n : Nat) := (1 <<< n)-1
def tileUnit (n count : Nat) := maskLo (n*count) / maskLo n
def lanes := tileUnit 32 414
def topGrid := maskLo (32*414)
def shiftPart (width x : Nat) := (x ||| (x <<< (31*width))) &&& (maskLo width * tileUnit (32*width) (512/width))
def spreadP (x : Nat) : Nat :=
  shiftPart 1 ( shiftPart 2 ( shiftPart 4 ( shiftPart 8 ( shiftPart 16 ( shiftPart 32 ( shiftPart 64 ( shiftPart 128 ( shiftPart 256 (x)))))))))
def orL (s x : Nat) := x ||| (x <<< s)
def orR (s x : Nat) := x ||| (x >>> s)
def growP (x : Nat) := orL 1 (orL 2 (orL 4 (orL 8 (orL 16 (x)))))
def growN (x : Nat) := orL 32 (orL 64 (orL 128 (orL 256 (orL 512 (orL 1024 (orL 2048 (orL 4096 (orL 8192 (x))))))))) &&& topGrid
def rowStep (s x : Nat) := Research.Grid1868.hop s (maskLo s * tileUnit (2*s) (13248/(2*s))) x
def fillR (x : Nat) := rowStep 1 (rowStep 2 (rowStep 4 (rowStep 8 (rowStep 16 (x)))))
def fillC (x : Nat) := growN ((orR 32 (orR 64 (orR 128 (orR 256 (orR 512 (orR 1024 (orR 2048 (orR 4096 (orR 8192 (x)))))))))) &&& maskLo 32)
def diff (signed : Bool) (a : Sig) :=
  let p := growP (spreadP a.1)
  let n := growN (a.2 &&& maskLo 32)
  (a,if signed then p ^^^ n else p &&& (topGrid ^^^ n))
end Research.LinearWide1868

namespace Research.Linear1868
def Linear (f : Nat → Nat) := f 0 = 0 ∧ ∀ x y, f (x ||| y) = f x ||| f y
lemma linId : Linear id := ⟨rfl,fun _ _ => rfl⟩
lemma linAnd (mask : Nat) : Linear (fun x => x &&& mask) :=
  ⟨by simp,fun _ _ => Nat.and_or_distrib_right ..⟩
lemma linLeft (n : Nat) : Linear (fun x => x <<< n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_shiftLeft,Nat.testBit_or]
    by_cases e : n ≤ j <;> simp [e]
lemma linRight (n : Nat) : Linear (fun x => x >>> n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp [Nat.testBit_shiftRight,Nat.testBit_or]
lemma linOr {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f x ||| g x) :=
  ⟨by simp [hf.1,hg.1],fun x y => by dsimp only; rw [hf.2,hg.2]; ac_rfl⟩
lemma linComp {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f (g x)) :=
  ⟨by dsimp only; rw [hg.1,hf.1],fun _ _ => by dsimp only; rw [hg.2,hf.2]⟩

lemma trunc_succ (x n : Nat) : x % 2^(n+1) = (x % 2^n) ||| (if x.testBit n then 2^n else 0) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow,Nat.testBit_or]
  cases e : x.testBit n <;> by_cases h : j=n <;> by_cases lt : j<n <;>
    simp_all [Nat.testBit_two_pow, show (j < n+1) ↔ j<n ∨ j=n by omega] <;> omega
lemma imagesTrunc {f : Nat→Nat} (hl : Linear f) (x j) (n : Nat) :
    (f (x % 2^n)).testBit j = true ↔ ∃ i < n, x.testBit i = true ∧ (f (2^i)).testBit j = true := by
  induction n with
  | zero => simp [Nat.mod_one,hl.1]
  | succ n ih =>
    rw [trunc_succ,hl.2,Nat.testBit_or,Bool.or_eq_true,ih]
    by_cases bit : x.testBit n = true
    · simp only [bit,↓reduceIte]
      constructor
      · rintro (⟨i,hi,hb,hv⟩|h)
        · exact ⟨i,by omega,hb,hv⟩
        · exact ⟨n,by omega,bit,h⟩
      · rintro ⟨i,hi,hb,hv⟩
        by_cases e : i=n
        · exact Or.inr (e ▸ hv)
        · exact Or.inl ⟨i,by omega,hb,hv⟩
    · simp only [bit,↓reduceIte,hl.1,Nat.zero_testBit,Bool.false_eq_true,or_false]
      constructor
      · rintro ⟨i,hi,hb,hv⟩; exact ⟨i,by omega,hb,hv⟩
      · rintro ⟨i,hi,hb,hv⟩
        have ne : i ≠ n := fun e => bit (e ▸ hb)
        exact ⟨i,by omega,hb,hv⟩
lemma images {f : Nat→Nat} (hl : Linear f) {x n} (lim : x < 2^n) (j) :
    (f x).testBit j = true ↔ ∃ i < n, x.testBit i = true ∧ (f (2^i)).testBit j = true := by
  simpa [Nat.mod_eq_of_lt lim] using imagesTrunc hl x j n
end Research.Linear1868

namespace Research.WProof1868
open Research.Basis1868 Research.LinearWide1868 Research.Linear1868
def pRead (x : Nat) := growP (spreadP x)
def nRead (x : Nat) := growN (x &&& maskLo 32)
def rMask (r : Nat) := maskLo 32 <<< (32*r)
def cMask (c : Nat) := lanes <<< c
def wTop := maskLo 13248
end Research.WProof1868
namespace Research.WProof1868
open Research.Basis1868 Research.LinearWide1868 Research.Linear1868
lemma linOL (d) : Linear (orL d) := linOr linId (linLeft d)
lemma linOR (d) : Linear (orR d) := linOr linId (linRight d)
lemma linShift (d) : Linear (shiftPart d) := by
  unfold shiftPart
  exact linComp (f := fun x => x &&& _) (g := fun x => x ||| (x <<< (31*d))) (linAnd _) (linOL _)
lemma linRowStep (s) : Linear (rowStep s) :=
  linOr (linOr linId (linComp (linAnd _) (linLeft s))) (linComp (linAnd _) (linRight s))
lemma linGrowP : Linear growP := by
  unfold growP
  iterate 4 apply linComp (linOL _)
  exact linOL _
lemma linGrowN : Linear growN := by
  unfold growN
  apply linComp (linAnd _)
  iterate 8 apply linComp (linOL _)
  exact linOL _
lemma pLin : Linear pRead := by
  apply linComp linGrowP
  unfold spreadP
  iterate 8 apply linComp (linShift _)
  exact linShift _
lemma nLin : Linear nRead := linComp (f := growN) (g := fun x => x &&& maskLo 32) linGrowN (linAnd _)
lemma rLin : Linear fillR := by
  unfold fillR
  iterate 4 apply linComp (linRowStep _)
  exact linRowStep _
lemma cLin : Linear fillC := by
  unfold fillC
  apply linComp linGrowN
  apply linComp (linAnd _)
  iterate 8 apply linComp (linOR _)
  exact linOR _

lemma rowMaskBit (r i : Nat) : (rMask r).testBit i = true ↔ i/32 = r := by
  simp only [rMask,maskLo,Nat.one_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one]
  by_cases le : 32*r ≤ i <;> simp [le] <;> omega
lemma validBound {x} (h : Valid1 x) : x < 2^414 := by
  have eq : x % 2^414 = x := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < 414
    · simp [hj]
    · simp [hj,h j (by omega)]
  rw [← eq]
  exact Nat.mod_lt _ (by decide)
lemma topBitW (i) : wTop.testBit i = decide (i<13248) := by
  unfold wTop maskLo
  rw [Nat.one_shiftLeft,Nat.testBit_two_pow_sub_one]

def Sub (x y : Nat) := ∀ i, x.testBit i = true → y.testBit i = true
lemma linMono {f} (h : Linear f) {x y} (s : Sub x y) : Sub (f x) (f y) := by
  have e : x ||| y = y := by
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_or]
    cases hx : x.testBit i <;> simp [hx,s i]
  intro i hi
  have e' := congrArg (fun w : Nat => w.testBit i) (h.2 x y)
  simp [e,Nat.testBit_or,hi] at e'
  exact e'
lemma fromRow {f x mask i} (h : Linear f) (hm : mask.testBit i = true)
    (hc : f (wTop ^^^ mask) &&& mask = 0)
    (bx : Sub x wTop) (found : (f x).testBit i = true) :
    ∃ j, x.testBit j = true ∧ mask.testBit j = true := by
  by_contra! hn
  have incl : Sub x (wTop ^^^ mask) := by
    intro j hj
    simp [Nat.testBit_xor,bx j hj,hn j hj]
  have hit := linMono h incl i found
  have bad := congrArg (fun w : Nat => w.testBit i) hc
  simp [Nat.testBit_and,hit,hm] at bad
end Research.WProof1868
namespace Research.WProof1868
open Research.Basis1868 Research.LinearWide1868 Research.Linear1868
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pulsePos : ∀ i : Fin 414, pRead (2^i.val) = rMask i.val := by decide +kernel
end Research.WProof1868
namespace Research.WProof1868
open Research.Basis1868 Research.LinearWide1868 Research.Linear1868
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pulseNeg : ∀ i : Fin 414, nRead (2^i.val) = (if i.val<32 then cMask i.val else 0) := by decide +kernel
end Research.WProof1868
namespace Research.WProof1868
open Research.Basis1868 Research.LinearWide1868 Research.Linear1868
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pulseLanes : ∀ r : Fin 414, (lanes >>> (32*r.val)) &&& maskLo 32 = 1 := by decide +kernel
end Research.WProof1868
namespace Research.WProof1868
open Research.Basis1868 Research.LinearWide1868 Research.Linear1868
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pulseR : ∀ i : Fin 414, fillR (wTop ^^^ rMask i.val) &&& rMask i.val = 0 := by decide +kernel
end Research.WProof1868
namespace Research.WProof1868
open Research.Basis1868 Research.LinearWide1868 Research.Linear1868
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma pulseC : ∀ i : Fin 32, fillC (wTop ^^^ cMask i.val) &&& cMask i.val = 0 := by decide +kernel
end Research.WProof1868
namespace Research.WProof1868
open Research.Basis1868 Research.LinearWide1868 Research.Linear1868
abbrev Ix := Fin 13248
abbrev I := Fin 414
def posAt (i : Ix) : I := ⟨i.val/32,by have := i.isLt;omega⟩
def negAt (i : Ix) : I := ⟨i.val % 32,by omega⟩
lemma laneAt (i : Ix) : lanes.testBit i.val = decide (i.val % 32 = 0) := by
  have e := congrArg (fun x : Nat => x.testBit (i.val % 32)) (pulseLanes (posAt i))
  have es : 32*(i.val/32) + i.val % 32 = i.val := by omega
  have le : i.val % 32 < 32 := by omega
  change (((lanes >>> (32*(i.val/32))) &&& maskLo 32).testBit (i.val % 32)) = _ at e
  simp only [maskLo,Nat.one_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one,
    es,le,decide_true,Bool.and_true] at e
  rw [e]
  apply Bool.eq_iff_iff.mpr
  exact Nat.testBit_one_eq_true_iff_self_eq_zero.trans decide_eq_true_iff.symm
lemma colMaskBit {c : Nat} (hc : c<32) (i : Ix) : (cMask c).testBit i.val = true ↔ i.val % 32 = c := by
  unfold cMask
  rw [Nat.testBit_shiftLeft]
  by_cases le : c ≤ i.val
  · simp only [le,decide_true,Bool.true_and]
    have q : i.val-c < 13248 := by have := i.isLt; omega
    rw [laneAt ⟨_,q⟩,decide_eq_true_eq]
    change (i.val-c) % 32=0 ↔ i.val % 32=c
    omega
  · simp [le]
    omega
lemma pReadBit {a} (val : Valid1 a) (i : Ix) : (pRead a).testBit i.val = a.testBit (posAt i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images pLin (validBound val)]
  constructor
  · rintro ⟨j,le,h,yes⟩
    rw [pulsePos ⟨j,le⟩] at yes
    change a.testBit (i.val/32) = true
    rwa [(rowMaskBit j i.val).mp yes]
  · intro h
    exact ⟨_,(posAt i).isLt,h,by rw [pulsePos (posAt i)];exact (rowMaskBit ..).mpr rfl⟩
lemma nReadBit {a} (val : Valid1 a) (i : Ix) : (nRead a).testBit i.val = a.testBit (negAt i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images nLin (validBound val)]
  constructor
  · rintro ⟨j,le,h,yes⟩
    rw [pulseNeg ⟨j,le⟩] at yes
    by_cases lt : j<32
    · simp only [lt,↓reduceIte] at yes
      change a.testBit (i.val % 32) = true
      rwa [(colMaskBit lt i).mp yes]
    · simp [lt] at yes
  · intro h
    refine ⟨_,(negAt i).isLt,h,?_⟩
    rw [pulseNeg (negAt i)]
    have lt : (negAt i).val < 32 := Nat.mod_lt _ (by decide)
    simp only [lt,↓reduceIte]
    exact (colMaskBit lt i).mpr rfl

def DS (signed : Bool) (p n : I) (a : Sig) :=
  if signed then Research.Conflict1868.D p n a else Research.Mono1868.D p n a
lemma diffBit (s : Bool) {a} (va : Valid a) (i : Ix) :
    (diff s a).2.testBit i.val = true ↔ DS s (posAt i) (negAt i) a := by
  have top : topGrid.testBit i.val = true := by change wTop.testBit i.val = true;rw [topBitW];exact decide_eq_true i.isLt
  cases s
  · change (pRead a.1 &&& (topGrid ^^^ nRead a.2)).testBit i.val = true ↔ a.1.testBit (posAt i).val = true ∧ a.2.testBit (negAt i).val = false
    simp [Nat.testBit_and,Nat.testBit_xor,pReadBit va.1,nReadBit va.2,top]
  · change (pRead a.1 ^^^ nRead a.2).testBit i.val = true ↔ a.1.testBit (posAt i).val ≠ a.2.testBit (negAt i).val
    simp [Nat.testBit_xor,pReadBit va.1,nReadBit va.2]
end Research.WProof1868
namespace Research.WProof1868
open Research.Basis1868 Research.LinearWide1868 Research.Linear1868
open Research.Board1868 (mult)
abbrev Sign := Sig × Nat
def signs (d : Bool) (v : List Sig) := v.map (diff d)
lemma multiOne {v : List Sign} {a} (ha : a ∈ v) (i) (hit : a.2.testBit i = true) :
    (mult v).1.testBit i = true := by
  induction v with
  | nil => cases ha
  | cons z l ih =>
    change ((mult l).1 ||| z.2).testBit i = true
    rw [Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl|hh
    · exact Or.inr hit
    · exact Or.inl (ih hh)
lemma multiTwo {v : List Sign} {a b} (ha : a∈v) (hb : b∈v) (ne : a ≠ b) (i)
    (x : a.2.testBit i = true) (y : b.2.testBit i = true) : (mult v).2.testBit i = true := by
  induction v with
  | nil => cases ha
  | cons z l ih =>
    change ((mult l).2 ||| ((mult l).1 &&& z.2)).testBit i = true
    rw [Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true]
    rcases List.mem_cons.mp ha with ea|hal
    · subst a
      rcases List.mem_cons.mp hb with eb|hbl
      · exact (ne eb.symm).elim
      · exact Or.inr ⟨multiOne hbl i y,x⟩
    · rcases List.mem_cons.mp hb with eb|hbl
      · subst b
        exact Or.inr ⟨multiOne hal i x,y⟩
      · exact Or.inl (ih hal hbl)

def once (v : List Sign) := (mult v).1 ^^^ (mult v).2
def focus (v : List Sign) (a : Sign) := a.2 &&& once v &&& wTop
def entryW (v : List Sign) (a : Sign) : Sign :=
  let u := focus v a
  (a.1,a.2 &&& fillR u &&& fillC u &&& wTop)
def U (d : Bool) (p n : I) (v : List Sig) (a : Sig) := ∀ c ∈ v, DS d p n c → c=a
def M (d : Bool) (p n : I) (v : List Sig) (a : Sig) :=
  DS d p n a ∧ (∃ j,U d p j v a) ∧ ∃ j,U d j n v a
lemma focusValid {v a} : Sub (focus v a) wTop := by
  intro i hi; simp only [focus,Nat.testBit_and,Bool.and_eq_true] at hi;exact hi.2
lemma singleD {d v} (valid : ∀ a∈v,Valid a) {a} (ha : a∈v) (i : Ix)
    (hit : (focus (signs d v) (diff d a)).testBit i.val = true) : U d (posAt i) (negAt i) v a := by
  intro b hb db
  by_contra ne
  have ga : diff d a ∈ signs d v := List.mem_map_of_mem ha
  have gb : diff d b ∈ signs d v := List.mem_map_of_mem hb
  have neq : diff d a ≠ diff d b := fun e => ne (congrArg Prod.fst e).symm
  simp only [focus,Nat.testBit_and,Bool.and_eq_true,once,Nat.testBit_xor] at hit
  have hi := multiOne ga i.val hit.1.1
  have hh := multiTwo ga gb neq i.val hit.1.1 ((diffBit d (valid b hb) i).mpr db)
  simp [hi,hh] at hit
lemma fromMark {d v} (valid : ∀ a∈v,Valid a) {a} (ha : a∈v) (i : Ix)
    (hit : (entryW (signs d v) (diff d a)).2.testBit i.val = true) : M d (posAt i) (negAt i) v a := by
  let u := focus (signs d v) (diff d a)
  simp only [entryW,Nat.testBit_and,Bool.and_eq_true] at hit
  have hr := fromRow rLin ((rowMaskBit (posAt i).val i.val).mpr rfl) (pulseR (posAt i)) (focusValid (v := signs d v) (a := diff d a)) hit.1.1.2
  have nc : (negAt i).val < 32 := Nat.mod_lt _ (by decide)
  have hn := fromRow cLin ((colMaskBit nc i).mpr rfl) (pulseC ⟨(negAt i).val,nc⟩) (focusValid (v := signs d v) (a := diff d a)) hit.1.2
  refine ⟨(diffBit d (valid a ha) i).mp hit.1.1.1,?_,?_⟩
  · obtain ⟨j,hj,jr⟩ := hr
    have b : j<13248 := of_decide_eq_true (topBitW j ▸ focusValid j hj)
    have e : posAt ⟨j,b⟩ = posAt i := Fin.ext ((rowMaskBit ..).mp jr)
    exact ⟨negAt ⟨j,b⟩,e ▸ singleD valid ha ⟨j,b⟩ hj⟩
  · obtain ⟨j,hj,jn⟩ := hn
    have b : j<13248 := of_decide_eq_true (topBitW j ▸ focusValid j hj)
    have e : negAt ⟨j,b⟩ = negAt i := Fin.ext ((colMaskBit nc ⟨j,b⟩).mp jn)
    exact ⟨posAt ⟨j,b⟩,e ▸ singleD valid ha ⟨j,b⟩ hj⟩

def entries (d : Bool) (v : List Sig) := let g := signs d v; g.map (entryW g)
lemma entries_fst (d) (v) : (entries d v).map Prod.fst = v := by
  simp [entries,signs,entryW,diff,Function.comp_def]
lemma memSig {d v a} (ha : a ∈ entries d v) : a.1 ∈ v := by
  rw [← entries_fst d v];exact List.mem_map_of_mem ha
lemma edgeWitness {d v} (valid : ∀ a∈v,Valid a) {x y} (hx : x∈entries d v) (hy : y∈entries d v)
    (cl : x.2 &&& y.2 ≠ 0) : ∃ p n,M d p n v x.1 ∧ M d p n v y.1 := by
  obtain ⟨zx,az,rfl⟩ := List.mem_map.mp hx
  obtain ⟨ax,mx,rfl⟩ := List.mem_map.mp az
  obtain ⟨zy,bz,rfl⟩ := List.mem_map.mp hy
  obtain ⟨ay,my,rfl⟩ := List.mem_map.mp bz
  obtain ⟨j,jh⟩ := Nat.exists_testBit_of_ne_zero cl
  rw [Nat.testBit_and,Bool.and_eq_true] at jh
  have h := jh.1
  simp only [entryW,Nat.testBit_and,Bool.and_eq_true,topBitW] at h
  let i : Ix := ⟨j,of_decide_eq_true h.2⟩
  exact ⟨posAt i,negAt i,fromMark valid mx i jh.1,fromMark valid my i jh.2⟩
end Research.WProof1868










namespace Research.Dag1868
open Research.Basis1868
structure Pack where
  width : Nat
  data : Array Nat
def Pack.at' (p : Pack) (i : Nat) : Nat :=
  let word := p.data[i/64]?.getD 0
  (word >>> (i % 64*p.width)) &&& (2^p.width-1)

structure Dag where
  size : Nat
  moves : Pack
  costs : Pack
  offsets : Pack
  edges : Pack

def budget (tab : Dag) (i : Nat) := tab.costs.at' i / 8
def nots (tab : Dag) (i : Nat) := tab.costs.at' i % 8
end Research.Dag1868

namespace Research.Sym1868
open Research.Basis1868
def Good (H J : SigHom) (a : Sig) := Valid a ∧ J.fn (H.fn a) = a
variable {H J : SigHom}
lemma goodNeg {a} (h : Good H J a) : Good H J (neg a) :=
  ⟨valid_neg h.1,by rw [H.hneg h.1,J.hneg (H.valid a),h.2]⟩
lemma goodBin {a b} (ha : Good H J a) (hb : Good H J b) {d} : Good H J (bin d a b) :=
  ⟨valid_bin ha.1 hb.1,by rw [H.hbin,J.hbin,ha.2,hb.2]⟩
lemma inj {a b} (ha : Good H J a) (hb : Good H J b) (e : H.fn a = H.fn b) : a=b := by
  rw [← ha.2,← hb.2,e]
lemma properH {a} (ga : Good H J a) (ha : proper a) : proper (H.fn a) :=
  ⟨H.valid a,fun e => ha.2.1 (ga.2.symm.trans ((congrArg J.fn e).trans J.hzero)),
    fun e => ha.2.2 (ga.2.symm.trans ((congrArg J.fn e).trans J.hone))⟩
lemma inverse {a} (ha : Good H J a) : J.fn (H.fn a) = a := ha.2
lemma presNeg {a} (ha : Good H J a) : H.fn (neg a) = neg (H.fn a) := H.hneg ha.1

lemma transform {k t S τ} (h : TRestricted k t S τ) (good : ∀ a∈S,Good H J a) :
    TRestricted k t (S.image H.fn) (fun x => τ (J.fn x)) := by
  induction h with
  | stop => simpa [H.htarget] using TRestricted.stop
  | @unary k t U a τ ha hf hr1 hr2 tail ih =>
    have ga := good a (Finset.mem_insert_self ..)
    simp only [Finset.image_insert, presNeg ga] at ih ⊢
    have hinvA : J.fn (H.fn a) = a := inverse ga
    have hvalU : ∀ y ∈ U, Good H J y := fun y hy => good _ (Finset.mem_insert_of_mem hy)
    have hne : neg (H.fn a) ∉ insert (H.fn a) (U.image (H.fn)) := by
      rw [← presNeg ga, ← Finset.image_insert]
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      have hvy : Good H J y := by
        rcases Finset.mem_insert.mp hy with rfl | hyU
        · exact ga
        · exact hvalU y hyU
      exact hf ((inj hvy (goodNeg ga) he) ▸ hy)
    have hnaU : a ∉ U → H.fn a ∉ U.image (H.fn) := by
      intro hna hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hna ((inj (hvalU y hy) ga he) ▸ hy)
    refine TRestricted.unary (properH ga ha) hne (by simpa [hinvA] using hr1)
      (fun h => hnaU (hr2 (by simpa [hinvA] using h))) ?_
    refine trestricted_congr (ih (fun x hx => (Finset.mem_insert.mp hx).elim (fun e => e ▸ goodNeg ga) (hvalU x))) ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · unfold updUnaryTag
      simp only [ite_true]
      rw [← presNeg ga, inverse (goodNeg ga)]
      simp only [ite_true, hinvA]
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxU
      have hneY : y ≠ neg a := fun e => hf (e ▸ Finset.mem_insert_of_mem hy)
      have hneGY : H.fn y ≠ neg (H.fn a) := by
        rw [← presNeg ga]; intro e; exact hneY (inj (hvalU y hy) (goodNeg ga) e)
      unfold updUnaryTag
      simp only [hneGY, ite_false, inverse (hvalU y hy), hneY]
  | @binaryAnd k t U a b τ ha hb hab hf hra hrb tail ih =>
    have ga := good a (Finset.mem_insert_self ..)
    have gb := good b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    simp only [Finset.image_insert, H.hbin false a b] at ih ⊢
    have hinvA := inverse ga
    have hinvB := inverse gb
    have hvalU : ∀ y ∈ U, Good H J y := fun y hy => good _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
    have hne : bin false (H.fn a) (H.fn b) ∉
        insert (H.fn a) (insert (H.fn b) (U.image (H.fn))) := by
      rw [← H.hbin false a b, ← Finset.image_insert, ← Finset.image_insert]
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      have hvy : Good H J y := by
        rcases Finset.mem_insert.mp hy with rfl | hy1
        · exact ga
        rcases Finset.mem_insert.mp hy1 with rfl | hyU
        · exact gb
        · exact hvalU y hyU
      exact hf ((inj hvy (goodBin ga gb) he) ▸ hy)
    have hnotU (z : Sig) (hvz : Good H J z) (hnz : z ∉ U) : H.fn z ∉ U.image (H.fn) := by
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hnz ((inj (hvalU y hy) hvz he) ▸ hy)
    refine TRestricted.binaryAnd (properH ga ha) (properH gb hb)
      (fun e => hab (inj ga gb e)) hne
      ⟨by simpa [hinvA] using hra.1, fun h => hnotU a ga (hra.2 (by simpa [hinvA] using h))⟩
      ⟨by simpa [hinvB] using hrb.1, fun h => hnotU b gb (hrb.2 (by simpa [hinvB] using h))⟩ ?_
    refine trestricted_congr (ih (fun x hx => (Finset.mem_insert.mp hx).elim (fun e => e ▸ goodBin ga gb) (hvalU x))) ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · unfold updAndTag
      simp only [ite_true]
      rw [← H.hbin false a b, inverse (goodBin ga gb)]
      simp only [ite_true, hinvA, hinvB]
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxU
      have hneY : y ≠ bin false a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
      have hneGY : H.fn y ≠ bin false (H.fn a) (H.fn b) := by
        rw [← H.hbin false a b]; intro e; exact hneY (inj (hvalU y hy) (goodBin ga gb) e)
      unfold updAndTag
      simp only [hneGY, ite_false, inverse (hvalU y hy), hneY]
  | @binaryOr k t U a b τ ha hb hab hf hra hrb tail ih =>
    have ga := good a (Finset.mem_insert_self ..)
    have gb := good b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    simp only [Finset.image_insert, H.hbin true a b] at ih ⊢
    have hinvA := inverse ga
    have hinvB := inverse gb
    have hvalU : ∀ y ∈ U, Good H J y := fun y hy => good _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
    have hne : bin true (H.fn a) (H.fn b) ∉
        insert (H.fn a) (insert (H.fn b) (U.image (H.fn))) := by
      rw [← H.hbin true a b, ← Finset.image_insert, ← Finset.image_insert]
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      have hvy : Good H J y := by
        rcases Finset.mem_insert.mp hy with rfl | hy1
        · exact ga
        rcases Finset.mem_insert.mp hy1 with rfl | hyU
        · exact gb
        · exact hvalU y hyU
      exact hf ((inj hvy (goodBin ga gb) he) ▸ hy)
    have hnotU (z : Sig) (hvz : Good H J z) (hnz : z ∉ U) : H.fn z ∉ U.image (H.fn) := by
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hnz ((inj (hvalU y hy) hvz he) ▸ hy)
    refine TRestricted.binaryOr (properH ga ha) (properH gb hb)
      (fun e => hab (inj ga gb e)) hne
      ⟨by simpa [hinvA] using hra.1, fun h => hnotU a ga (hra.2 (by simpa [hinvA] using h))⟩
      ⟨by simpa [hinvB] using hrb.1, fun h => hnotU b gb (hrb.2 (by simpa [hinvB] using h))⟩ ?_
    refine trestricted_congr (ih (fun x hx => (Finset.mem_insert.mp hx).elim (fun e => e ▸ goodBin ga gb) (hvalU x))) ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · unfold updOrTag
      simp only [ite_true]
      rw [← H.hbin true a b, inverse (goodBin ga gb)]
      simp only [ite_true]
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxU
      have hvy := hvalU y hy
      have hneY : y ≠ bin true a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
      have hneGY : H.fn y ≠ bin true (H.fn a) (H.fn b) := by
        rw [← H.hbin true a b]; intro e; exact hneY (inj hvy (goodBin ga gb) e)
      have eqA : (H.fn y = H.fn a) ↔ (y = a) := ⟨inj hvy ga, congrArg (H.fn)⟩
      have eqB : (H.fn y = H.fn b) ↔ (y = b) := ⟨inj hvy gb, congrArg (H.fn)⟩
      unfold updOrTag
      simp only [hneGY, ite_false, inverse hvy, hneY, eqA, eqB, hinvA, hinvB]
lemma rotate {k t : Nat} {w z : List Wire} (hk : ∀ a ∈ sigsOf w, Good H J a)
    (hp : (w.map (fun x => (H.fn x.1, x.2))).Perm z)
    (hn : Impossible k t z) : Impossible k t w := by
  intro m hm S τ hrep h
  apply hn m hm (S.image (H.fn)) (fun x => τ (J.fn x)) _ (transform h (fun a ha => hk a (List.mem_toFinset.mp (hrep.2.1 ▸ ha))))
  have hval : ∀ x ∈ sigsOf w, Valid x := fun x hx =>
    (live_proper h.live x (hrep.2.1 ▸ List.mem_toFinset.mpr hx)).1
  have hmapS : sigsOf (w.map (fun x => (H.fn x.1, x.2))) = (sigsOf w).map (H.fn) := by
    simp [sigsOf, List.map_map, Function.comp_def]
  have hpS : ((sigsOf w).map (H.fn)).Perm (sigsOf z) := by
    rw [← hmapS]; exact hp.map Prod.fst
  have hndMap : ((sigsOf w).map (H.fn)).Nodup := by
    apply List.Nodup.map_on _ hrep.1
    intro a ha b hb heq
    exact inj (hk a ha) (hk b hb) heq
  refine ⟨hpS.nodup_iff.mp hndMap, ?_, ?_⟩
  · ext a
    simp only [List.mem_toFinset, ← hpS.mem_iff, List.mem_map, Finset.mem_image, ← hrep.2.1]
  · intro x hx
    have hx' := hp.mem_iff.mpr hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx'
    have hvy : Good H J y.1 := hk y.1 (List.mem_map_of_mem hy)
    simp [inverse hvy, hrep.2.2 y hy]
end Research.Sym1868

namespace Research.Orbit1868
open Research.Basis1868
open Research.Sym1868 Research.Dag1868
def moved (H : SigHom) (w : Wire) : Wire := (H.fn w.1,w.2)
def rowsGood (H J : SigHom) (v : List Wire) := ∀ w ∈ v, Good H J w.1
def kept (ai bi op drop : Nat) : Nat → List Wire → List Wire
  | _,[] => []
  | idx,q::v =>
    let rest := kept ai bi op drop (idx+1) v
    if idx=ai && drop.testBit 0 || idx=bi && drop.testBit 1 then rest else
    if op=2 && (idx=ai || idx=bi) && q.2==.tDeg3 then (q.1,.tSpec0)::rest else q::rest

lemma kept_map (H : SigHom) (a b op d) (v : List Wire) (i) :
    (kept a b op d i v).map (moved H) = kept a b op d i (v.map (moved H)) := by
  induction v generalizing i with
  | nil => rfl
  | cons q l ih =>
    simp only [List.map_cons,kept]
    by_cases h : (i=a && d.testBit 0 || i=b && d.testBit 1) = true
    · simp only [h,↓reduceIte,ih]
    · simp only [h,↓reduceIte]
      have ht : (moved H q).2 = q.2 := rfl
      rw [ht]
      simp only [Bool.false_eq_true,↓reduceIte]
      by_cases hh : (op=2 && (i=a || i=b) && q.2==.tDeg3) = true <;> simp [hh,moved,ih]
lemma kept_good {H J} (a b op d) {v : List Wire} (good : rowsGood H J v) (i) :
    rowsGood H J (kept a b op d i v) := by
  induction v generalizing i with
  | nil => intro x hx; cases hx
  | cons q l ih =>
    have gl : rowsGood H J l := fun w hw => good w (List.mem_cons_of_mem _ hw)
    have gq := good q (List.mem_cons_self ..)
    have gt := ih gl (i+1)
    intro x hx
    simp only [kept] at hx
    split at hx
    · exact gt x hx
    · split at hx <;> rcases List.mem_cons.mp hx with rfl|hh <;> first | exact gq | exact gt x hh

def defW : Wire := (zero,.tNone)
def change (v : List Wire) (code : Nat) : List Wire :=
  let ai := code &&& 15
  let bi := (code >>> 4) &&& 15
  let op := (code >>> 8) &&& 3
  let drop := (code >>> 10) &&& 3
  let a := v.getD ai defW
  let b := v.getD bi defW
  let z := if op=0 then neg a.1 else bin (op==2) a.1 b.1
  let tag := if op=0 && a.2 == .tDeg3 then Tag.tSpec1 else
    if op=1 && (a.2==.tDeg3 || b.2==.tDeg3) then Tag.tSpec0 else Tag.tNone
  (z,tag) :: kept ai bi op drop 0 v

lemma goodDef (H J : SigHom) : Good H J defW.1 := ⟨valid_zero,by change J.fn (H.fn zero) = zero; rw [H.hzero,J.hzero]⟩
lemma goodGet {H J v} (hg : rowsGood H J v) (j : Nat) : Good H J ((v.getD j defW).1) := by
  induction v generalizing j with
  | nil => exact goodDef _ _
  | cons a v ih =>
    cases j with
    | zero => exact hg a (by simp)
    | succ k => exact ih (fun c hc => hg c (List.mem_cons_of_mem _ hc)) k

lemma mapGet (H : SigHom) (v : List Wire) (i : Nat) :
    (v.map (moved H)).getD i defW = moved H (v.getD i defW) := by
  induction v generalizing i with
  | nil => apply Prod.ext <;> simp [moved,defW,H.hzero]
  | cons a v ih => cases i with | zero => rfl | succ n => exact ih n

lemma change_map {H J v} (hg : rowsGood H J v) (code : Nat) :
    (change v code).map (moved H) = change (v.map (moved H)) code := by
  simp only [change,List.map_cons,mapGet,kept_map]
  congr 1
  apply Prod.ext
  · simp only [moved]
    split <;> first | exact H.hneg (goodGet hg _).1 | exact H.hbin _ _ _
  · rfl
lemma change_good {H J v} (hg : rowsGood H J v) (code : Nat) : rowsGood H J (change v code) := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl|hh
  · dsimp only
    split <;> first | exact goodNeg (goodGet hg _) | exact goodBin (goodGet hg _) (goodGet hg _)
  · exact kept_good _ _ _ _ hg _ w hh

def build (tab : Dag) (root : List Wire) : Nat → Nat → List Wire
  | 0,_ => root
  | fuel+1,i => if i+1=tab.size then root else
    let cell := tab.moves.at' i
    change (build tab root fuel (cell >>> 12)) cell

lemma build_eq {H J root} (hg : rowsGood H J root) (tab : Dag) (fuel i) :
    (build tab root fuel i).map (moved H) = build tab (root.map (moved H)) fuel i ∧
    rowsGood H J (build tab root fuel i) := by
  induction fuel generalizing i with
  | zero => exact ⟨rfl,hg⟩
  | succ fuel ih =>
    simp only [build]
    split
    · exact ⟨rfl,hg⟩
    · obtain ⟨e,g⟩ := ih (tab.moves.at' i >>> 12)
      exact ⟨(change_map g _).trans (congrArg (fun x => change x _) e),change_good g _⟩

structure Frame where
  seed : Nat → List Wire
  H : Nat → SigHom
  J : Nat → SigHom
  agree : ∀ g, (seed g).map (moved (H g)) = seed 0
  closed : ∀ g, rowsGood (H g) (J g) (seed g)

def st (tab : Dag) (f : Frame) (i g : Nat) := build tab (f.seed g) 15 i
lemma rotateState {tab f i k t} (h : Impossible k t (st tab f i 0)) (g : Nat) :
    Impossible k t (st tab f i g) := by
  obtain ⟨e,d⟩ := build_eq (f.closed g) tab 15 i
  rw [f.agree g] at e
  apply rotate (H := f.H g) (J := f.J g) _ (e ▸ List.Perm.refl _) h
  intro a ha
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
  exact d w hw
def choices (tab : Dag) (i t : Nat) : List Nat :=
  let j := tab.offsets.at' i
  let limit := tab.offsets.at' (i+1)
  ((List.range (limit-j)).map (fun a => tab.edges.at' (j+a))).filter (fun c => nots tab (c/4) == t)
def groupOld (tab : Dag) (f : Frame) (i t : Nat) := (choices tab i t).map (fun c => st tab f (c/4) (c % 4))
def validChild (tab : Dag) (i k t : Nat) :=
  (choices tab i t).all (fun c => decide (c/4 < i) && budget tab (c/4) == k)
open Research.WProof1868
end Research.Orbit1868

namespace Research.Free1868
open Research.Basis1868
open Research.Conflict1868

def flip (s : Bool) (a : Sig) := if s then neg a else a
def sign (a : Sig) := bit true 0 a
def can (a : Sig) := flip (sign a) a

lemma neg2 (a : Sig) : neg (neg a) = a := by
  obtain ⟨u,v⟩ := a
  simp [neg,bnot,Nat.xor_assoc]

lemma flip2 (s a) : flip s (flip s a) = a := by cases s <;> simp [flip,neg2]
lemma flipFalse (a) : flip false a = a := rfl
lemma flipTrue (a) : flip true a = neg a := rfl
lemma vf {a} (s) (h : Valid a) : Valid (flip s a) := by cases s <;> first | exact h | exact valid_neg h
lemma vc {a} (h : Valid a) : Valid (can a) := vf _ h

lemma sign_neg {a} (h : Valid a) : sign (neg a) = !sign a := bit_neg true 0 h
lemma can_neg {a} (v : Valid a) : can (neg a) = can a := by
  unfold can
  rw [sign_neg v]
  cases sign a <;> simp [flip,neg2]
lemma can_flip {a} (s) (v : Valid a) : can (flip s a) = can a := by
  cases s with
  | false => rfl
  | true => exact can_neg v
lemma can2 {a} (v : Valid a) : can (can a) = can a := can_flip _ v
lemma recover (a) : flip (sign a) (can a) = a := flip2 _ _
lemma ncan (a) : flip (!sign a) (can a) = neg a := by
  unfold can
  cases sign a <;> simp [flip,neg2]
lemma can_zero : can zero = zero := by decide +kernel
lemma can_one : can one = zero := by decide +kernel
lemma flipProper (s) {a} (ha : proper a) : proper (flip s a) := by
  cases s
  · exact ha
  · refine ⟨valid_neg ha.1,?_,?_⟩
    · intro h
      exact ha.2.2 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.1))
    · intro h
      exact ha.2.1 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.2))
lemma canProper {a} (h : proper a) : proper (can a) := flipProper _ h

lemma sameClass {a b} (h : can a = can b) : a = b ∨ a = neg b := by
  have ha := recover a
  rw [h] at ha
  unfold can at ha
  cases ea : sign a <;> cases eb : sign b <;> simp [ea,eb,flip,neg2] at ha <;> aesop

lemma bin_neg_self (d : Bool) {a} (h : Valid a) :
    bin d a (neg a) = (if d then one else zero) := by
  have op {x : Nat} (hx : Valid1 x) :
      x &&& bnot x = 0 ∧ x ||| bnot x = top := by
    constructor <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      simp only [Nat.testBit_and,Nat.testBit_or,testBit_bnot hx,testBit_top,Nat.zero_testBit] <;>
      by_cases hj : j < 414
    all_goals first | (rw [hx j (by omega)] <;> simp [hj]) | (cases x.testBit j <;> simp [hj])
  cases d
  · exact Prod.ext (op h.1).1 (op h.2).1
  · exact Prod.ext (op h.1).2 (op h.2).2

lemma distinctClass {d a b} (ha : proper a) (hab : a ≠ b) (hg : proper (bin d a b)) :
    can a ≠ can b := by
  intro h
  rcases sameClass h with e | e
  · exact hab e
  · have eb : b = neg a := by rw [e,neg2]
    rw [eb,bin_neg_self _ ha.1] at hg
    cases d
    · exact hg.2.1 rfl
    · exact hg.2.2 rfl

def blend (d s t : Bool) (a b : Sig) := can (bin d (flip s a) (flip t b))

inductive BL : Nat → Finset Sig → Prop where
  | stop : BL 0 {can target}
  | step {k U a b d s t} (ha : proper a) (hb : proper b)
      (ac : can a = a) (bc : can b = b) (hab : a ≠ b)
      (fresh : blend d s t a b ∉ insert a (insert b U))
      (tail : BL k (insert (blend d s t a b) U)) : BL (k+1) (insert a (insert b U))

lemma compress {k t S} (l : Live k t S) :
    ∃ j T, j+t ≤ k ∧ BL j T ∧ T ⊆ S.image can := by
  induction l with
  | stop => exact ⟨0,_,by omega,BL.stop,by simp⟩
  | @unary k t U a ha _ _ ih =>
    obtain ⟨j,T,le,h,sub⟩ := ih
    refine ⟨j,T,by omega,h,?_⟩
    simpa only [Finset.image_insert,can_neg ha.1] using sub
  | @binary k t U a b d ha hb hab _ tail ih =>
    obtain ⟨j,T,le,h,sub⟩ := ih
    let g := bin d a b
    let z := can g
    let w := insert (can a) (insert (can b) (U.image can))
    have hsource : (insert a (insert b U)).image can = w := by simp [w]
    rw [hsource]
    have hs : T ⊆ insert z (U.image can) := by simpa [g,z] using sub
    by_cases need : z ∈ T ∧ z ∉ w
    · have hu : T.erase z ⊆ U.image can := by
        intro c hc
        exact (Finset.mem_insert.mp (hs (Finset.mem_of_mem_erase hc))).resolve_left (Finset.ne_of_mem_erase hc)
      have hp : proper g := live_proper tail _ (Finset.mem_insert_self ..)
      have nz := distinctClass ha hab hp
      have id : blend d (sign a) (sign b) (can a) (can b) = z := by
        simp [blend,recover,z,g]
      have out : BL j (insert (blend d (sign a) (sign b) (can a) (can b)) (T.erase z)) := by
        rw [id,Finset.insert_erase need.1]; exact h
      have fresh : blend d (sign a) (sign b) (can a) (can b) ∉ insert (can a) (insert (can b) (T.erase z)) := by
        rw [id]
        intro zz
        apply need.2
        simp only [Finset.mem_insert] at zz ⊢
        simp only [w,Finset.mem_insert]
        exact zz.imp_right (fun e => e.imp_right (fun h => hu h))
      refine ⟨j+1,_,by omega,BL.step (canProper ha) (canProper hb) (can2 ha.1) (can2 hb.1) nz fresh out,?_⟩
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hu)
    · refine ⟨j,T,by omega,h,?_⟩
      intro c hc
      rcases Finset.mem_insert.mp (hs hc) with rfl | hU
      · exact Classical.byContradiction (fun hn => need ⟨hc,hn⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU)


lemma BL.forms {k S} (l : BL k S) : ∀ a ∈ S, proper a ∧ can a = a := by
  induction l with
  | stop => simpa using And.intro (canProper target_proper) (can2 valid_target)
  | step ha hb ca cb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨⟨ha,ca⟩,⟨hb,cb⟩,fun a h => ih _ (Finset.mem_insert_of_mem h)⟩

lemma neg_ne {a} (hv : Valid a) : neg a ≠ a := by
  intro h
  have eq := sign_neg hv
  rw [h] at eq
  cases e : sign a <;> simp [e] at eq

def Present (n : Nat) (S : Finset Sig) := ∃ t, Live (n+t) t S

lemma insertFlip {n a U} (s : Bool) (ha : proper a)
    (hf : s = true → neg a ∉ insert a U) (h : Present n (insert (flip s a) U)) :
    Present n (insert a U) := by
  cases s
  · exact h
  · obtain ⟨t,hl⟩ := h
    exact ⟨t+1,by simpa [Nat.add_assoc] using Live.unary ha (hf rfl) hl⟩

lemma BL.expand {j S} (l : BL j S) : Present j S := by
  induction l with
  | stop =>
    have eq : can target = neg target := by decide +kernel
    rw [eq]
    have hf : neg (neg target) ∉ insert (neg target) (∅ : Finset Sig) := by
      rw [neg2]; simp [Ne.symm (neg_ne valid_target)]
    have t : Live 0 0 (insert (neg (neg target)) ∅) := by rw [neg2]; exact Live.stop
    exact ⟨1,Live.unary (flipProper true target_proper) hf t⟩
  | @step k U a b d s t ha hb ca cb ne fresh tail ih =>
    let x := flip s a
    let y := flip t b
    let g := bin d x y
    let z := can g
    change z ∉ insert a (insert b U) at fresh
    change Present k (insert z U) at ih
    have cx : can x = a := (can_flip s ha.1).trans ca
    have cy : can y = b := (can_flip t hb.1).trans cb
    have vg : Valid g := valid_bin (vf _ ha.1) (vf _ hb.1)
    have zu : z ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have canonU (c) (hc : c ∈ U) : can c = c := (tail.forms c (Finset.mem_insert_of_mem hc)).2
    have gz : proper z := (tail.forms _ (Finset.mem_insert_self ..)).1
    have hg : proper g := recover g ▸ flipProper (sign g) gz
    have go := insertFlip (sign g) hg (by
      intro act h
      rcases Finset.mem_insert.mp h with gg | inu
      · exact neg_ne vg gg
      · have zz : z = neg g := by change flip (sign g) g = _; rw [act]; rfl
        exact zu (zz ▸ inu)) ih
    have xy : x ≠ y := fun eq => ne (cx.symm.trans ((congrArg can eq).trans cy))
    have gfresh : g ∉ insert x (insert y U) := by
      intro h
      rcases Finset.mem_insert.mp h with hh | h
      · have za : z = a := (congrArg can hh).trans cx
        exact fresh (Finset.mem_insert.mpr (Or.inl za))
      rcases Finset.mem_insert.mp h with hh | inu
      · have zb : z = b := (congrArg can hh).trans cy
        exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl zb)))
      · apply zu
        change can g ∈ U
        rwa [canonU g inu]
    obtain ⟨negCount,live⟩ := go
    have go2 : Present (k+1) (insert x (insert y U)) := by
      refine ⟨negCount,?_⟩
      convert Live.binary (flipProper s ha) (flipProper t hb) xy gfresh live using 1 <;> omega
    have nap : neg a ∉ U := by
      intro hh
      have eq := canonU (neg a) hh
      rw [can_neg ha.1,ca] at eq
      exact neg_ne ha.1 eq.symm
    have nbp : neg b ∉ U := by
      intro hh
      have eq := canonU (neg b) hh
      rw [can_neg hb.1,cb] at eq
      exact neg_ne hb.1 eq.symm
    have xa := insertFlip s ha (U := insert y U) (fun _ hh => by
      rcases Finset.mem_insert.mp hh with eq | hh
      · exact neg_ne ha.1 eq
      rcases Finset.mem_insert.mp hh with eq | hh
      · exact ne (ca.symm.trans ((can_neg ha.1).symm.trans ((congrArg can eq).trans cy)))
      · exact nap hh) go2
    rw [Finset.insert_comm] at xa
    rw [Finset.insert_comm]
    apply insertFlip t hb _ xa
    intro act hh
    rcases Finset.mem_insert.mp hh with eq | hh
    · exact neg_ne hb.1 eq
    rcases Finset.mem_insert.mp hh with eq | hh
    · exact ne ((cb.symm.trans ((can_neg hb.1).symm.trans ((congrArg can eq).trans ca))).symm)
    · exact nbp hh

lemma freeColors {k S} (h : BL k S) : ∃ n, Colored S n ∧ n+S.card ≤ k+2 := by
  obtain ⟨t,hl⟩ := h.expand
  obtain ⟨n,c,b⟩ := live_colored hl
  exact ⟨n,c,by omega⟩

end Research.Free1868
namespace Research.FreeSearch1868
open Research.Basis1868
open Research.Conflict1868 Research.Free1868

lemma negFlip (u : Bool) (a : Sig) : neg (flip u a) = flip (!u) a := by
  cases u <;> simp [Research.Free1868.flip,neg2]
lemma deM {a b} (ha : Valid a) (hb : Valid b) :
    neg (bin true a b) = bin false (neg a) (neg b) := by
  apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i
  · change (bnot (a.1 ||| b.1)).testBit i = ((bnot a.1) &&& (bnot b.1)).testBit i
    simp only [testBit_bnot (valid1_or ha.1 hb.1),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.1,testBit_bnot hb.1]
    by_cases e : i < 414 <;> simp [e]
  · change (bnot (a.2 ||| b.2)).testBit i = ((bnot a.2) &&& (bnot b.2)).testBit i
    simp only [testBit_bnot (valid1_or ha.2 hb.2),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.2,testBit_bnot hb.2]
    by_cases e : i < 414 <;> simp [e]

lemma flipBlend {a b} (ha : Valid a) (hb : Valid b) (d s t : Bool) :
    ∃ u v, blend false u v a b = blend d s t a b := by
  cases d
  · exact ⟨s,t,rfl⟩
  · refine ⟨!s,!t,?_⟩
    unfold blend
    rw [← negFlip,← negFlip,← deM (vf s ha) (vf t hb),can_neg (valid_bin (vf s ha) (vf t hb))]
lemma blend_symm (d s t a b) : blend d s t a b = blend d t s b a := by unfold blend; rw [bin_comm]

def keep (a b : Sig) (u v : Bool) (c : Sig) := (c != a || u) && (c != b || v)
def next (v : List Sig) (a b z : Sig) (l r : Bool) := z :: v.filter (keep a b l r)
def oneB (v : List Sig) (go : List Sig → Bool) (a b : Sig) (s t : Bool) :=
  let z := blend false s t a b
  z != zero && !(v.contains z) &&
  ([false,true].any fun l => [false,true].any fun r => go (next v a b z l r))
def pairB (v : List Sig) (go : List Sig → Bool) (a b : Sig) :=
  [false,true].any fun s => [false,true].any fun t => oneB v go a b s t

lemma coverageB {k v} (l : BL k v.toFinset) : unionSep true v = top := by
  obtain ⟨u,h⟩ := l.expand
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_top]
  by_cases hi : i < 414
  · simp only [hi,decide_true]
    obtain ⟨a,ha,hh⟩ := live_sep h i hi
    exact (mem_unionSep true _ _).2 ⟨a,List.mem_toFinset.mp ha,sep_weaken _ (live_proper h a ha).1 i hi hh⟩
  · simp only [hi,decide_false]
    exact valid_unionSep (fun a ha => (l.forms a (List.mem_toFinset.mpr ha)).1.1) i (by omega)

def baseTest (v : List Sig) := v == [can target]

lemma tailState {a b z : Sig} {U : Finset Sig} {v : List Sig} (nd : v.Nodup)
    (rep : v.toFinset = insert a (insert b U)) (fresh : z ∉ insert a (insert b U)) :
    let w := next v a b z (decide (a ∈ U)) (decide (b ∈ U))
    w.Nodup ∧ w.toFinset = insert z U := by
  classical
  dsimp only
  have ff : (v.filter (keep a b (decide (a ∈ U)) (decide (b ∈ U)))).toFinset = U := by
    ext c
    simp only [List.mem_toFinset,List.mem_filter,keep,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,bne_iff_ne]
    have mem : c ∈ v ↔ c = a ∨ c = b ∨ c ∈ U := by rw [← List.mem_toFinset,rep]; simp
    rw [mem]
    by_cases ea : c = a <;> by_cases eb : c = b <;> simp_all
  constructor
  · apply List.nodup_cons.mpr
    exact ⟨fun h => fresh (rep ▸ List.mem_toFinset.mpr (List.mem_of_mem_filter h)),nd.filter _⟩
  · simpa only [next,List.toFinset_cons,ff]

lemma anyBool {f : Bool → Bool} (a) (h : f a = true) : [false,true].any f = true :=
  List.any_eq_true.mpr ⟨a,by cases a <;> simp,h⟩

end Research.FreeSearch1868
namespace Research.Cuts1868
open Research.Basis1868
open Research.Conflict1868 Research.Free1868 Research.FreeSearch1868
lemma oneStep {k S} (l : BL k S) (m : Nat) (hm : k ≤ m+1) (v : List Sig) (nd : v.Nodup)
    (rep : v.toFinset = S) (go : List Sig → Bool)
    (hyp : ∀ w, w.Nodup → ∀ j ≤ m, BL j w.toFinset → go w = true) :
    (baseTest v || scanPairs (pairB v go) v) = true := by
  cases l with
  | stop =>
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v; simp [baseTest]
  | @step j U a b d s t ha hb ca cb hab fresh tail =>
    let z := blend d s t a b
    apply Bool.or_eq_true_iff.mpr; right
    have va : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (u w : Bool) (id : blend false u w x y = z)
        (eqS : v.toFinset = insert x (insert y U)) : pairB v go x y = true := by
      apply anyBool u
      apply anyBool w
      have nz : z ≠ zero := (tail.forms _ (Finset.mem_insert_self ..)).1.2.1
      have nv : z ∉ v := fun h => fresh (rep ▸ List.mem_toFinset.mpr h)
      have nn : !(v.contains z) = true := by simpa using nv
      simp only [oneB,id,Bool.and_eq_true,bne_iff_ne]
      refine ⟨⟨nz,nn⟩,?_⟩
      apply anyBool (decide (x∈U))
      apply anyBool (decide (y∈U))
      have fr : z ∉ insert x (insert y U) := fun hh => nv (List.mem_toFinset.mp (eqS ▸ hh))
      obtain ⟨nw,pw⟩ := tailState nd eqS fr
      exact hyp _ nw j (by omega) (pw ▸ tail)
    obtain ⟨u,w,id⟩ := flipBlend ha.1 hb.1 d s t
    apply scanPairs_complete _ va vb hab
    · exact yes a b u w id rep
    · exact yes b a w u ((blend_symm false w u b a).trans id) (by rwa [Finset.insert_comm b a])



def excluded (k : Nat) (v : List Sig) := ∀ n ≤ k, ¬ BL n v.toFinset
end Research.Cuts1868
namespace Research.Guard3400
open Research.Basis1868
open Research.Free1868 Research.FreeSearch1868 Research.Cuts1868 Research.Conflict1868
open Research.WProof1868 Research.LinearWide1868
open Research.Board1868 (mult)
open Research.ColorSearch1868 (paint paint_ok)

def grid (k : Nat) (v : List Sig) : Bool :=
  (((mult (signs true v)).1 &&& wTop) == wTop) &&
    paint (k+2-v.length) (Research.WProof1868.entries true v) (fun _ => 0)

lemma grid_ok {k m v} (hm : m≤k) (nd : v.Nodup) (h : BL m v.toFinset) :
    grid k v = true := by
  obtain ⟨t,l⟩ := h.expand
  have val : ∀ a∈v, Valid a := fun a ha => (h.forms _ (List.mem_toFinset.mpr ha)).1.1
  have psep (p n : Fin 414) : ∃ a∈v, DS true p n a := by
    obtain ⟨a,ha,hd⟩ := pair_sep l p n
    exact ⟨a,List.mem_toFinset.mp ha,by simpa [DS] using hd⟩
  obtain ⟨n,⟨f,bd,ok⟩,le⟩ := freeColors h
  have sz : v.toFinset.card=v.length := List.toFinset_card_of_nodup nd
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply beq_iff_eq.mpr
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and,topBitW]
    by_cases hi : i<13248
    · let z : Ix := ⟨i,hi⟩
      obtain ⟨a,ha,hd⟩ := psep (posAt z) (negAt z)
      have hit := multiOne (List.mem_map_of_mem (f := diff true) ha) i ((diffBit true (val a ha) z).mpr hd)
      simpa [hi,signs] using hit
    · simp [hi]
  · apply paint_ok _ f
    · rwa [Research.WProof1868.entries_fst]
    · intro x hx
      have := bd _ (List.mem_toFinset.mpr (memSig hx))
      omega
    · simp
    · intro x hx y hy ne eq
      by_contra hh
      obtain ⟨p,q,h1,h2⟩ := edgeWitness val hx hy hh
      apply ok _ (List.mem_toFinset.mpr (memSig hx)) _ (List.mem_toFinset.mpr (memSig hy)) ne _ eq
      exact ⟨p,q,by simpa [DS,M,U,Research.Conflict1868.Mark,Research.Conflict1868.Unique] using h1,by simpa [DS,M,U,Research.Conflict1868.Mark,Research.Conflict1868.Unique] using h2⟩

def fast (k : Nat) (v : List Sig) : Bool :=
  decide (v.length≤k+1) && (unionSep true v == top) && grid k v
lemma fast_ok {n k v} (nd : v.Nodup) (h : BL n v.toFinset) (nk : n ≤ k) : fast k v = true := by
  obtain ⟨t,l⟩ := h.expand
  have sz := live_size l
  rw [List.toFinset_card_of_nodup nd] at sz
  simp only [fast,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  exact ⟨⟨by omega,coverageB h⟩,grid_ok nk nd h⟩

def go (k : Nat) (blocked : List (List Sig)) (v : List Sig) : Bool :=
  fast k v && !blocked.any (fun w => decide (w.toFinset=v.toFinset))
lemma resolve {k : Nat} {v : List Sig} {blocked : List (List Sig)}
    (nd : v.Nodup) (prior : ∀ w ∈ blocked, excluded k w)
    (hc : (baseTest v || scanPairs (pairB v (go k blocked)) v) = false) : excluded (k+1) v := by
  intro n hn l
  have yes := oneStep l k hn v nd rfl (go k blocked) (by
    intro w dw j jk h
    simp only [go,Bool.and_eq_true]
    refine ⟨fast_ok dw h jk,?_⟩
    simp only [Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨b,hb,he⟩ := List.any_eq_true.mp hh
    exact prior b hb j jk ((of_decide_eq_true he) ▸ h))
  rw [hc] at yes
  contradiction

end Research.Guard3400


namespace Research.Moves3400
open Research.Basis1868
open Research.Free1868 Research.Sym1868 Research.Cuts1868
def SignFixed (H : SigHom) := ∀ a, sign (H.fn a)=sign a
lemma flip_map (H : SigHom) (s : Bool) {a : Sig} (ha : Valid a) :
    H.fn (flip s a)=flip s (H.fn a) := by cases s <;> first | rfl | exact H.hneg ha
lemma can_map {H : SigHom} (fix : SignFixed H) {a : Sig} (ha : Valid a) :
    H.fn (can a)=can (H.fn a) := by unfold can; rw [fix a,flip_map H _ ha]
lemma blend_map {H : SigHom} (fix : SignFixed H) {a b : Sig} (ha : Valid a) (hb : Valid b) (d s t) :
    H.fn (blend d s t a b)=blend d s t (H.fn a) (H.fn b) := by
  unfold blend
  rw [can_map fix (valid_bin (vf s ha) (vf t hb)),H.hbin,flip_map H _ ha,flip_map H _ hb]
lemma goodFlip {H J : SigHom} {a} (h : Good H J a) (s : Bool) : Good H J (flip s a) := by
  cases s <;> first | exact h | exact goodNeg h
lemma goodBlend {H J : SigHom} {a b} (ha : Good H J a) (hb : Good H J b) (d s t) :
    Good H J (blend d s t a b) := goodFlip (goodBin (goodFlip ha s) (goodFlip hb t)) _
lemma mapBL {H J : SigHom} (fix : SignFixed H) {k S} (l : BL k S) (hs : ∀ a∈S,Good H J a) :
    BL k (S.image H.fn) := by
  induction l with
  | stop => simpa only [Finset.image_singleton,can_map fix target_proper.1,H.htarget] using (BL.stop : BL 0 {can target})
  | @step k U a b d s t ha hb ca cb ne fresh tail ih =>
    have ga := hs a (Finset.mem_insert_self ..)
    have gb := hs b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have gu (x) (h : x∈U) : Good H J x := hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have gz := goodBlend ga gb d s t
    have ez := blend_map fix ha.1 hb.1 d s t
    have ht := ih (by simpa only [Finset.forall_mem_insert] using And.intro gz gu)
    rw [Finset.image_insert,ez] at ht
    rw [Finset.image_insert,Finset.image_insert]
    apply BL.step (properH ga ha) (properH gb hb) _ _ (fun e => ne (inj ga gb e)) _ ht
    · rw [← can_map fix ha.1,ca]
    · rw [← can_map fix hb.1,cb]
    · rw [← ez,← Finset.image_insert,← Finset.image_insert]
      intro h
      obtain ⟨x,hx,xe⟩ := Finset.mem_image.mp h
      exact fresh (inj (hs x hx) gz xe ▸ hx)
lemma fixed (p n : Fin 414 → Fin 414) (z : p 0=0) : SignFixed (pairHom p n) := by
  intro a
  change (reindex p a.1).testBit 0=a.1.testBit 0
  rw [reindex_testBit]
  simp [z]
lemma move {v w : List Sig} {k : Nat} (H J : SigHom) (fix : SignFixed H)
    (equal : (v.map H.fn).toFinset=w.toFinset)
    (inverse : v.all (fun a => decide (J.fn (H.fn a)=a))=true)
    (old : excluded k w) : excluded k v := by
  intro m hm l
  have h := mapBL (J:=J) fix l (fun a ha => ⟨(l.forms a ha).1.1,
    of_decide_eq_true (List.all_eq_true.mp inverse a (List.mem_toFinset.mp ha))⟩)
  have eq : v.toFinset.image H.fn=(v.map H.fn).toFinset := by
    ext x; simp
  rw [eq,equal] at h
  exact old _ hm h
end Research.Moves3400
open Research.Basis1868 Research.Free1868 Research.FreeSearch1868 Research.Cuts1868 Research.Dag1868 Research.Moves3400
namespace Research.MonoCheck1868
open Research.Basis1868
open Research.Grid1868 Research.Mono1868

def xmask (a : Sig) : Nat := (spread true true a) &&& (spread false false a)
def same (a : Sig) : Nat := (spread true false a) ||| (spread false true a)

lemma xmask_sound {a} (i : Ix) (h : (xmask a).testBit i.val = true) : D (ix true i) (ix false i) a := by
  simp only [xmask,Nat.testBit_and,Bool.and_eq_true] at h
  exact ⟨spread_sound _ _ _ _ h.1,spread_sound _ _ _ _ h.2⟩

lemma same_sound {a} (i : Ix) (h : (same a).testBit i.val = true) : ¬ D (ix true i) (ix false i) a := by
  simp only [same,Nat.testBit_or,Bool.or_eq_true] at h
  rintro ⟨hp,hn⟩
  rcases h with h | h
  · exact Bool.noConfusion (hp.symm.trans (spread_sound _ _ _ _ h))
  · exact Bool.noConfusion (hn.symm.trans (spread_sound _ _ _ _ h))

abbrev Signs := List (Sig × Nat)

def allSame (a : Sig) : Signs → Nat
  | [] => 2^256-1
  | (c,m)::cs => if c = a then allSame a cs else m &&& allSame a cs

def marks (v : Signs) (a : Sig) :=
  let uniq := allSame a v
  (xmask a &&& row uniq) &&& col uniq

lemma allSame_sound {a} (i : Ix) {v : Signs} (hv : ∀ w ∈ v, w.2 = same w.1)
    (h : (allSame a v).testBit i.val = true) :
    Unique (ix true i) (ix false i) (v.map Prod.fst).toFinset a := by
  intro c hc hd
  obtain ⟨w,hw,ew⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
  rw [← ew] at hd ⊢
  clear hc ew c
  induction v with
  | nil => simp at hw
  | cons y ys ih =>
    obtain ⟨b,m⟩ := y
    by_cases e : b = a
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact e
      · apply ih (fun z hz => hv z (List.mem_cons_of_mem _ hz)) _ hw
        simpa [allSame,e] using h
    · have hs : m.testBit i.val = true ∧ (allSame a ys).testBit i.val = true := by
        simpa [allSame,e,Nat.testBit_and] using h
      rcases List.mem_cons.mp hw with rfl | hw
      · have eq := hv (b,m) (by simp)
        change m = same b at eq
        exact (same_sound i (eq ▸ hs.1) hd).elim
      · exact ih (fun z hz => hv z (List.mem_cons_of_mem _ hz)) hs.2 hw

lemma marks_sound {v : Signs} (hv : ∀ w ∈ v, w.2 = same w.1) {a} (i : Ix)
    (hh : (marks v a).testBit i.val = true) :
    Mark (ix true i) (ix false i) (v.map Prod.fst).toFinset a := by
  simp only [marks,Nat.testBit_and,Bool.and_eq_true] at hh
  refine ⟨xmask_sound i hh.1.1,?_,?_⟩
  · let G (k : Nat) := ∃ (p m : I), p.val = k ∧ Unique p m (v.map Prod.fst).toFinset a
    have h := row_sound _ G (fun j hj => ⟨ix true j,ix false j,rfl,allSame_sound j hv hj⟩) i hh.1.2
    obtain ⟨p,m,ep,hm⟩ := h
    have eq : p = ix true i := Fin.ext ep
    exact ⟨m,eq ▸ hm⟩
  · let G (k : Nat) := ∃ (q n : I), n.val = k ∧ Unique q n (v.map Prod.fst).toFinset a
    have h := col_sound _ G (fun j hj => ⟨ix true j,ix false j,rfl,allSame_sound j hv hj⟩) i hh.2
    obtain ⟨q,n,en,hn⟩ := h
    have eq : n = ix false i := Fin.ext en
    exact ⟨q,eq ▸ hn⟩

def entries (v : List Sig) : Signs :=
  let signs := v.map fun a => (a,same a)
  v.map fun a => (a,(2^256-1) &&& marks signs a)

lemma entries_fst (v : List Sig) : (entries v).map Prod.fst = v := by simp [entries,Function.comp_def]
lemma eBound {v : List Sig} {a} (ha : a ∈ entries v) {i : Nat} (h : a.2.testBit i = true) : i < 256 := by
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
  simp only [Nat.testBit_and,Bool.and_eq_true] at h
  have q := h.1
  rw [Nat.testBit_two_pow_sub_one] at q
  exact of_decide_eq_true q

lemma eMark {v : List Sig} {z} (hz : z ∈ entries v) (i : Ix) (h : z.2.testBit i.val = true) :
    Mark (ix true i) (ix false i) v.toFinset z.1 := by
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
  simp only [Nat.testBit_and,Bool.and_eq_true] at h
  have hl : ∀ u ∈ v.map (fun a => (a,same a)), u.2 = same u.1 := by
    intro u hu
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
    rfl
  have hm := marks_sound hl i h.2
  simpa [List.map_map,Function.comp_def] using hm

lemma eEdge {v : List Sig} {x y} (hx : x ∈ entries v) (hy : y ∈ entries v)
    (h : x.2 &&& y.2 ≠ 0) : Edge v.toFinset x.1 y.1 := by
  obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero h
  rw [Nat.testBit_and,Bool.and_eq_true] at hi
  let j : Ix := ⟨i,eBound hx hi.1⟩
  exact ⟨ix true j,ix false j,eMark hx j hi.1,eMark hy j hi.2⟩

end Research.MonoCheck1868
namespace Research.MonoSearch1868
open Research.Basis1868
open Research.Mono1868 Research.MonoCheck1868
open Research.ColorSearch1868 (paint paint_ok)

def colorTest (k t : Nat) (v : List Wire) : Bool :=
  paint (k + 2 - t - v.length) (entries (sigsOf v)) (fun _ => 0)

lemma colorTest_ok {k m t S τ} {v : List Wire} (hm : m ≤ k)
    (rep : Represents v S τ) (l : Live m t S) (ht : t=0) : colorTest k t v = true := by
  obtain ⟨n,⟨f,b,d⟩,le⟩ := live_colored l ht
  have eq := rep.2.1
  have len : S.card = v.length := by rw [← eq,List.toFinset_card_of_nodup rep.1]; simp [sigsOf]
  have mem {x} (hx : x ∈ entries (sigsOf v)) : x.1 ∈ S := by
    rw [← eq,← entries_fst (sigsOf v)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,rfl⟩)
  apply paint_ok _ f
  · rw [entries_fst]
    exact rep.1
  · intro x hx
    have := b _ (mem hx)
    omega
  · simp
  · intro x hx y hy hxy ef
    by_contra nm
    have he := eEdge hx hy nm
    rw [eq] at he
    exact d _ (mem hx) _ (mem hy) hxy he ef

end Research.MonoSearch1868
open Research.Basis1868
open Research.Dag1868 Research.Orbit1868
namespace Research.TinyOrbit3091
def test (k t : Nat) (v : List Wire) := if t=0 then (unionSep false (sigsOf v)==top) && Research.MonoSearch1868.colorTest k t v else true
lemma test_ok {k m t S τ w} (hm : m≤k) (rep : Represents w S τ) (l : Live m t S) : test k t w=true := by
  by_cases z : t=0
  · subst t
    have covers : unionSep false (sigsOf w)=top := by
      apply Nat.eq_of_testBit_eq;intro j;rw [testBit_top]
      by_cases hj : j<414
      · simp only [hj,decide_true]
        obtain ⟨a,ha,hh⟩:=live_sep l j hj
        exact (mem_unionSep false _ _).2 ⟨a,List.mem_toFinset.mp (rep.2.1 ▸ ha),hh⟩
      · simp only [hj,decide_false];apply valid_unionSep _ j (by omega)
        intro a ha;exact (live_proper l _ (rep.2.1 ▸ List.mem_toFinset.mpr ha)).1
    simp [test,covers,Research.MonoSearch1868.colorTest_ok hm rep l rfl]
  · simp [test,z]
def go (k t : Nat) (old : List (List Wire)) (w : List Wire) := !old.any (fun z => isPermFast w z) && test k t w
lemma cut {k t old} (prev : ∀ w ∈ old, Impossible k t w) (v) (h : go k t old v=false) : Impossible k t v := by
  intro m hm S τ rep l
  have pc:=test_ok hm rep l.live
  simp only [go,pc,Bool.and_true,Bool.not_eq_false'] at h
  obtain ⟨u,hu,per⟩:=List.any_eq_true.mp h
  exact perm_impossible (isPermFast_perm per) (prev u hu) m hm S τ rep l
lemma expand {k t v oldU oldB} (hu : ∀ w∈oldU,Impossible k (t-1) w) (hb : ∀ w∈oldB,Impossible k t w)
    (term : stepTest k t v (go k (t-1) oldU) (go k t oldB)=false) : Impossible (k+1) t v := exclude_step (cut hu) (cut hb) term
def check (tab : Dag) (f : Frame) (i : Nat) :=
  let k := budget tab i - 1
  let t := nots tab i
  0 < budget tab i && validChild tab i k (t-1) && validChild tab i k t &&
    !stepTest k t (st tab f i 0) (go k (t-1) (groupOld tab f i (t-1))) (go k t (groupOld tab f i t))

lemma certify {tab f} (h : ∀ i < tab.size, check tab f i = true) {i} (hi : i < tab.size) :
    Impossible (budget tab i) (nots tab i) (st tab f i 0) := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    let k := budget tab i - 1
    let t := nots tab i
    have hh := h i hi
    change ((0 < budget tab i && validChild tab i k (t-1) && validChild tab i k t) && _) = true at hh
    simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at hh
    obtain ⟨⟨⟨pos,cu⟩,cb⟩,num⟩ := hh
    have helper (nt : Nat) (hc : validChild tab i k nt = true) (w) (hw : w ∈ groupOld tab f i nt) : Impossible k nt w := by
      obtain ⟨c,hm,rfl⟩ := List.mem_map.mp hw
      obtain ⟨lt,eq⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hc c hm)
      have ci := of_decide_eq_true lt
      have ke := (beq_iff_eq.mp eq)
      have ne : nots tab (c/4) = nt := beq_iff_eq.mp (List.mem_filter.mp hm).2
      apply rotateState
      simpa [ke,ne] using ih (c/4) ci (by omega)
    have hk : budget tab i = k+1 := by dsimp [k]; omega
    rw [hk]
    exact expand (helper _ cu) (helper _ cb) num
end Research.TinyOrbit3091
open Research.Basis1868 Research.Free1868 Research.Moves3400
namespace Research.Expr3091
inductive Form where
  | raw (i : Fin 9)
  | merge (a b : Bool) (x y : Form)
def value (seeds : Fin 9 → Sig) : Form → Sig
  | .raw i => seeds i
  | .merge s t x y => blend false s t (value seeds x) (value seeds y)
lemma valueValid {seeds : Fin 9 → Sig} (hv : ∀ i,Valid (seeds i)) (q : Form) : Valid (value seeds q) := by
  induction q with
  | raw i => exact hv i
  | merge s t x y ih jh => unfold value blend can;exact vf _ (valid_bin (vf s ih) (vf t jh))
lemma movedValue {seeds bt : Fin 9 → Sig} {h : SigHom} (fix : SignFixed h) (hv : ∀ i,Valid (seeds i))
    (base : ∀ i,h.fn (seeds i)=bt i) (q : Form) : h.fn (value seeds q)=value bt q := by
  induction q with
  | raw i => exact base i
  | merge s t x y ih jh => simp only [value,blend_map fix (valueValid hv x) (valueValid hv y),ih,jh]
end Research.Expr3091
open Research.Basis1868 Research.Free1868 Research.FreeSearch1868 Research.Cuts1868 Research.Dag1868 Research.Moves3400
namespace Research.Book3091
structure Book where
  size : Nat
  count : Nat
  signal : Nat → Sig
  shapes : Pack
  levels : Pack
  ranges : Pack
  links : Pack
  shifts : Pack
  dests : Pack
  shiftsId : Pack
  hom : Nat → SigHom
  fixes : ∀ i, SignFixed (hom i)
def atSig (b : Book) (i : Nat) := b.signal i
def decode : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,c => (c &&& 511)::decode n (c >>> 9)
def ids (b : Book) (i : Nat) := let c:=b.shapes.at' i;decode (c &&& 15) (c >>> 4)
def state (b : Book) (i : Nat) := (ids b i).map (atSig b)
def bank (b : Book) (i h : Nat) := let l:=b.ranges.at' (16*i+h); (List.range (b.ranges.at' (16*i+h+1)-l)).map (fun j => b.links.at' (l+j))
def subs (b : Book) (i : Nat) := (List.range 16).flatMap (bank b i)
def hash (s : Sig) := (s.1 ^^^ (s.2 >>> 7)) % 16
def candidates (b : Book) (i : Nat) (w : List Sig) := (bank b i (hash (w.headD zero))).map (state b)
def go (b : Book) (i k : Nat) (v : List Sig) := Research.Guard3400.go k (candidates b i v) v
lemma resolve {b i k v} (nd : v.Nodup) (prior : ∀ c∈subs b i, excluded k (state b c))
    (hh : (baseTest v || scanPairs (pairB v (go b i k)) v)=false) : excluded (k+1) v := by
  intro n hn l
  have yes := oneStep l k hn v nd rfl (go b i k) (by
    intro w dw j jk h
    simp only [go,Research.Guard3400.go,Bool.and_eq_true];refine ⟨Research.Guard3400.fast_ok dw h jk,?_⟩
    simp only [Bool.not_eq_true'];apply Bool.eq_false_iff.mpr;intro z
    obtain ⟨old,ho,eq⟩:=List.any_eq_true.mp z
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp ho
    have hs : c∈subs b i := List.mem_flatMap.mpr ⟨hash (w.headD zero),List.mem_range.mpr (Nat.mod_lt _ (by decide)),hc⟩
    exact prior c hs j jk ((of_decide_eq_true eq) ▸ h))
  rw [hh] at yes;contradiction
def shifted (b : Book) (p i : Nat) := b.shiftsId.at' (p*b.count+i)
def checkSig (b : Book) (j : Nat) := let i:=j / b.count;let x:=j % b.count;
  shifted b i x == 511 || (b.hom i).fn (atSig b x) == atSig b (shifted b i x)
def check (b : Book) (i : Nat) := let k:=b.levels.at' i;let p:=b.shifts.at' i;let q:=b.dests.at' i
  if p=0 then decide (0 < k) && (subs b i).all (fun j => decide (j < i) && b.levels.at' j==k-1) && decide (state b i).Nodup &&
    !(baseTest (state b i) || scanPairs (pairB (state b i) (go b i (k-1))) (state b i))
  else decide (q < i) && b.levels.at' q==k && (ids b i).all (fun x => decide (x < b.count) && decide (shifted b p x < b.count) && shifted b p (shifted b p x)==x) &&
    decide (((ids b i).map (shifted b p)).toFinset=(ids b q).toFinset)
lemma proof {b : Book} (lim : b.count<511) (shift : ∀ i<b.size,b.shifts.at' i<4)
    (sig : ∀ j<4*b.count,checkSig b j=true) (cert : ∀ i<b.size,check b i=true) {i} (hi : i<b.size) : excluded (b.levels.at' i) (state b i) := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    let k:=b.levels.at' i;let p:=b.shifts.at' i;let q:=b.dests.at' i
    have v:=cert i hi
    by_cases no : p=0
    · simp only [check,show b.shifts.at' i=0 from no,ite_true,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at v
      obtain ⟨⟨⟨pos,links⟩,nd⟩,test⟩:=v
      have sub (j) (hj : j∈subs b i) : excluded (k-1) (state b j) := by
        have h:=List.all_eq_true.mp links j hj
        simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
        exact h.2 ▸ ih j h.1 (by omega)
      have ex:=resolve nd sub test
      have e : b.levels.at' i-1+1=b.levels.at' i := by omega
      rwa [e] at ex
    · simp only [check,show b.shifts.at' i≠0 from no,ite_false,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at v
      obtain ⟨⟨⟨lt,ke⟩,iv⟩,eq⟩:=v
      have mp {x} (hx : x < b.count) (hs : shifted b p x < b.count) : (b.hom p).fn (atSig b x)=atSig b (shifted b p x) := by
        have hp:=shift i hi
        have lt : p*b.count+x<(p+1)*b.count := by rw [Nat.add_mul,one_mul];omega
        have max : (p+1)*b.count≤4*b.count := Nat.mul_le_mul_right _ (by dsimp [p];omega)
        have z:=sig (p*b.count+x) (lt_of_lt_of_le lt max)
        have size : 0 < b.count := by omega
        have index : (p*b.count+x)/b.count=p := by rw [Nat.mul_comm p,Nat.mul_add_div size,Nat.div_eq_of_lt hx,Nat.add_zero]
        simp [checkSig,index,Nat.mul_add_mod,size,Nat.div_eq_of_lt hx,Nat.mod_eq_of_lt hx,show shifted b p x≠511 by omega] at z
        exact z
      have acts (x) (m : x∈ids b i) : (b.hom p).fn (atSig b x)=atSig b (shifted b p x) ∧ (b.hom p).fn (atSig b (shifted b p x))=atSig b x := by
        have a:=List.all_eq_true.mp iv x m;simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at a
        have e : (b.hom p).fn (atSig b (shifted b p x))=atSig b (shifted b p (shifted b p x)) := mp a.1.2 (by change shifted b p (shifted b p x)<b.count;rw [show shifted b p (shifted b p x)=x from a.2];exact a.1.1)
        exact ⟨mp a.1.1 a.1.2,e.trans (congrArg _ a.2)⟩
      apply move (b.hom p) (b.hom p) (b.fixes p) _ _ (ke ▸ ih q lt (by omega))
      · have mh : ((state b i).map (b.hom p).fn)=((ids b i).map (shifted b p)).map (atSig b) := by
          simp only [state,List.map_map];apply List.map_congr_left;intro x hx;exact (acts x hx).1
        rw [mh];change _=((ids b q).map (atSig b)).toFinset
        have idmap (u : List Nat) : (u.map (atSig b)).toFinset=u.toFinset.image (atSig b) := by ext x;simp
        rw [idmap,idmap,eq]
      · apply List.all_eq_true.mpr;intro s hs;obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hs
        exact decide_eq_true ((congrArg (b.hom p).fn (acts x hx).1).trans (acts x hx).2)
end Research.Book3091

namespace Research.Frames1868
open Research.Basis1868 Research.Sym1868
def read9 (v : Nat) (j : Fin 414) : Fin 414 := Fin.ofNat 414 ((v >>> (j.val*9)) &&& 511)
def makeH (v : Nat × Nat) := pairHom (read9 v.1) (read9 v.2)
end Research.Frames1868


namespace Research.PinRows3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Research.Basis1868 Research.Free1868 Research.FreeSearch1868
def sliceRaw : List Sig := [(0x3c7d6fd7dfebfdbfd7ddb7f3aafaded5ffafafb338aab6cffaad7fcaabfcfec6abeaaedb1d2aabce751f8c5ed8577bbf7e6a7daf,0x3c7d6bd7dfebb1bed7ddb6d3aafad8d5fdad29b338aab6ce7aad77caab34b4c6abea28cb1d2aebce351f8c5ed0577bbd7e6a79a7),(0x33060c70fdefeeddfe77ddbb79be27ae89bbbcba46e3dc79889baa2f9871cfa7862ee4899888b494c8260833680884484493004b,0x202042000004601200209284000072a00128408044148310002880410414b010404c40000801410480000212808844000900048),(0x374f992cbef7bdeefdb7baeef9d9d8f691dddb4e391dba7e111db0d66669b6f866571a29e1115a49005890b040911f200a445183,0x4d09041003a1029411a0c20800c8c4008d00023808304a000510c22220b4c0224200090100420800188010401113000a004082),(0x378bb628aff5fe7febeecfedd57d3f2bffd7d7ccc7554f37fd52ffb555fb7f3955f5573ce2d557b7fee07fadbfe9cc63819f97d9,0x3782b628a7f45e7d6bee4f2dd57d372bfb52d7ccc7554f31fd52af3555db4b3955b5d734e2d515b7fae07fa9bfe8cc63819f9758),(0x33e83096bfde7fc3ffcf001f8787fffe7f87fe61fe7879e07f807f9e1e1f801fffe181e007ff85200b088408a4041000b1008805,0x0),(0x3a52efbdff7bdf777d7beb76fe69a77b266eeab6869eeb99a266c93a678e3b66789a9a561a22201260613140371ac79280100631,0x200840800104c41282209241401232a0202c2048600491180020810048a0b205010921000000010406030002700840280100600),(0x17c789637fe9bfd8ffc7e671fb7ea6dfaf833e7ebe304a2cffb01e1e6a2a06a00006062acc801dbb3335c8101233207c3a13b13,0x160309237f699fc8fec764717b5e001fac833e7eb820482cfd801e1e6a2a06a00002060ac4801cbb3335c8001233203c1211b12),(0x397277e2fbff63fe73fc7f98e7cff593fd784df9f59c834537fc8661f94541940000198553301cee810767c58908c0251d6c5075,0x393272e2ebec02bc43cc5618e3ce1411fd700df94194820437f88621d94540140000098452301ce6810747c588084025156c1074),(0x1fcefa57fbdf7bbbebbf5dd7e7659dd4677755d1967759e4467545d99965dd9991d6516644448001490c244426421cd0e3822c5,0x1c49054809200210118090280208d4042500101020300c00255008080414808808000200004800040080444004018c0e002084)]
def slice_sample (s : Bool) (i : Fin 414) (j : Fin 9) : Bool :=
  bit s i (sliceRaw.getD j.val zero)
lemma slice_sample_ok : ∀ (s : Bool) (i : Fin 414), edgeF (slice_sample s i) = s := by decide +kernel
lemma slice_raw_id : List.ofFn (fun j : Fin 9 => sliceRaw.getD j.val zero) = sliceRaw := rfl
lemma slice_sample_list (s i) : List.ofFn (slice_sample s i) = sliceRaw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => sliceRaw.getD j.val zero)).map (bit s i) := by
      rw [List.map_ofFn]; rfl
    _ = _ := by rw [slice_raw_id]
lemma slice_raw_lt : sliceRaw.all (fun a => decide (a.1 ≤ top ∧ a.2 ≤ top)) = true := by decide +kernel
lemma slice_raw_valid : ∀ a ∈ sliceRaw, Valid a := by
  intro a ha
  have h := of_decide_eq_true (List.all_eq_true.mp slice_raw_lt a ha)
  exact ⟨valid1_of_le_top h.1, valid1_of_le_top h.2⟩
lemma slice_raw_nd : sliceRaw.Nodup := by unfold sliceRaw; decide +kernel
lemma slice_every_input : sliceRaw.all (fun a => unionSep true (sliceRaw.erase a) != top) = true := by decide +kernel
lemma slice_necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ sliceRaw) : sliceRaw.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp slice_every_input a hr
  have cov : unionSep true (sliceRaw.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi, decide_true]
      obtain ⟨b, hb, h⟩ := live_sep l i hi
      have ba : b ≠ a := fun he => hn (he ▸ hb)
      have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
      exact (mem_unionSep true _ _).2 ⟨b, hm, sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi, decide_false]
      exact valid_unionSep (fun x hx => slice_raw_valid x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail

def canonicalInputs := sliceRaw.map can
lemma canonValid {a} (ha : a ∈ canonicalInputs) : Valid a := by
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ha
  exact vc (slice_raw_valid u hu)
lemma canonRequired : canonicalInputs.all (fun a => unionSep true (canonicalInputs.erase a) != top) = true := by decide +kernel
lemma canonical_needed {j T} (hl : BL j T) (sub : T ⊆ canonicalInputs.toFinset) : T = canonicalInputs.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  by_contra hn
  have bad := List.all_eq_true.mp canonRequired a (List.mem_toFinset.mp ha)
  obtain ⟨u,h⟩ := hl.expand
  have eq : unionSep true (canonicalInputs.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi,decide_true]
      obtain ⟨b,hb,hh⟩ := live_sep h i hi
      have ne : b ≠ a := fun e => hn (e ▸ hb)
      exact (mem_unionSep true _ _).2 ⟨b,(List.mem_erase_of_ne ne).mpr (List.mem_toFinset.mp (sub hb)),
        sep_weaken _ (live_proper h b hb).1 i hi hh⟩
    · simp only [hi,decide_false]
      exact valid_unionSep (fun x hx => canonValid (List.mem_of_mem_erase hx)) i (by omega)
  simp [eq] at bad

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in

lemma pinnedOn : ∀ (s : Bool) (i : Fin 414), (slice_sample s i 0 || slice_sample s i 3) = true := by decide +kernel
end Research.PinRows3091
open Research.Basis1868 Research.Cuts1868 Research.FreeSearch1868
open Research.Basis1868 Research.Cuts1868 Research.FreeSearch1868
namespace Research.Book3091
lemma scanAll {α : Type} {v : List α} {g : α → α → Bool} (d : α)
    (no : ∀ i j, i<j → j<v.length → g (v.getD i d) (v.getD j d)=false) : scanPairs g v=false := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    have front : v.any (g a)=false := by
      apply Bool.eq_false_iff.mpr;intro hh;obtain ⟨b,hb,h⟩:=List.any_eq_true.mp hh
      obtain ⟨j,hj,rfl⟩:=List.getElem_of_mem hb
      have z:=no 0 (j+1) (by omega) (by simpa)
      change g a (v.getD j d)=false at z;rw [List.getD_eq_getElem _ _ hj,h] at z;contradiction
    rw [scanPairs,front,Bool.false_or]
    apply ih;intro i j ij jv;exact no (i+1) (j+1) (by omega) (by simpa)
def slim (b : Book) (i : Nat) := let k:=b.levels.at' i; b.shifts.at' i==0 && decide (0<k) &&
    (subs b i).all (fun j=> decide (j < i) && b.levels.at' j==k-1) && decide (state b i).Nodup && !baseTest (state b i)
def unit (b : Book) (i x y : Nat) := let v:=state b i;!(pairB v (go b i (b.levels.at' i-1)) (v.getD x zero) (v.getD y zero))
lemma regroup {b i} (cheap : slim b i=true) (rows : ∀ x y,x<y → y<(state b i).length → unit b i x y=true) : check b i=true := by
  simp only [slim,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,Bool.not_eq_true'] at cheap
  obtain ⟨⟨⟨⟨shift,pos⟩,kids⟩,nd⟩,start⟩ := cheap
  have pairs := scanAll (v := state b i) (g := pairB (state b i) (go b i (b.levels.at' i-1))) zero (fun x y hx hy => by simpa only [unit,Bool.not_eq_true'] using rows x y hx hy)
  simp [check,shift,pos,kids,nd,start,pairs]
end Research.Book3091

namespace Research.FOrbit3091
open Research.Basis1868 Research.Free1868 Research.Sym1868 Research.Moves3400 Research.Book3091 Research.Expr3091
def selectRow (word : Nat) (i : Fin 414) : Fin 414 := Fin.ofNat 414 ((word >>> (9*i.val)) &&& 511)
def h1 := pairHom (selectRow 0x2c1600f0d9dd743859dfad396349a2364934ea4da9ed156ad09b8c678a21349cb044b0406fb7cbd5eeef76bcde2eb72b8dd2e76fb85aed96db75aacd67b45a6c762b2d92bf5eb0d82b75aaed72b159abd5aab54a954ea350a7d2e994da75269545a351e9141a150e893fa04f2773e9ece26f3a9ccd267369acc25f3298cba5b2b964a655259349e512290c92471f90472371e8ec5e31198d45227168ac421f1288c32170e86c26150883c1a0b018140e08fd7f3fe00fb7e3e5f4f87bbd1e6f67abc1def278badd8ed773a5d4e57339dd0e471b85c4df70371b6de6eb61aeda6cb51a6d66ab419ed268b359ccc65b1d90c9653198ac260b1186be5eb017eba5caf176b55b2dd70b35a2bd60b1592b55caa54ab156a55329d50a352285449e4ea813e9a4ca7136964aa612e9248a51269047a31168e46a2514854321d1083421fd0081411f4fc7b3e1e0ee7a3c9d0e6763a9c0de72389b8da090c87c6c3f30854b22f0a884ce490217876251d0acca581b8985e1b190c4a0512791c200617128c010270047227218204804340a07a031096c8a402b8ac24232a94ca4132a92c1c021b050343e22158b8411a18c760c350143a0b0c8a4361824034c62a040d41448078341c200e00cd813039303c40050b08c00) (selectRow 0x1008058442804078082a010381c120d0180418040385010070a82c12050181c2a0e0400408020084c180c060301806008100407010500e130305012020a818180c060300e1401020280703008180c060300c070603028070381004150a0301814038082801048180413040240206038182a040a8202613040100206010080c080382428140381c28010a01c280c06030180c060040c080101002090101c28070a00c0a12058240c0c060102a01048180415030100407010500c040a8281c10068400a0a058500e070a04c10030283414140380404140304c1008098102a040a81002040a81c28070483822070a0201013010080803070281a040a8100409008180408030240411018040c090102404070a01c2814038080c100902c0a0a0700c1a03070281a11088342203070281a0f0a0280a03058280610058142403068401c0d09040240b02814200d0504816100283c000f0001c0009008241a130605420140102018120205026130503824150780c0c020682c2a1503810060609830201002004140d0880400090401c28110480c060607844240d048380a020a0200a02088500407070281000070040c0c03014000b038040e040502c2a14040402212078341c0c0280c0c13038241604050040400)
lemma f1 : SignFixed h1 := fixed _ _ (by decide +kernel)
def h2 := pairHom (selectRow 0x2bf5f1a80dd97138da5fed69533da00349b5aa6d79f5196ed19d18276a411ca03039afc0af97dbd5eef179bb5deeb73ba5c6e56fb85b2d76eb6daad169b359ec965b158ec161af57eb55bae576b159ab55ea955a9d4aa151a7d369d4ba65269546a2d228f42a0d12873fa04ee793d9f4e675379c4d66d339a4be6131994b65d29954ae592692ca24f239248645208fc763d1b8e46635178c4562d138a446250f884361d0b864261507844160d0280c1206ff803f5fcf97d3edf8f77c3cde8f57b3c5e4ef783b5dceb763a5d4e774395cce37237dc0e171375bcdb6e365b4d76c355acd36a345a4cf683399acb663218eca64b158cc36230584bd5f2fd80b95d2ed78b75c2d56cb35a2c564af582b55cab562a554a652aa14ea15128d489d4f27d409b4e26534974c2552c934a245248f4822d188d47225148642a210e8441a05047f401ecf87d3f1e4f4773c1d4ec733a1c4e46f381b4dc012a8b0063f06100161b2002040523181c262e2982838181208c362f2d9808e4e1e9401a1a12928620d288248845218846e63340a89e36040c84e15208280a260c8e8923b0c970906a018f80c141c8d096572b0102661010481e592a9305e5807040082810878560e0e8409067328d88c3b2f0a46a151587cd800) (selectRow 0x1008080440e150001808090a05002030682418150a01c101402040021206850080a040242a060484c180c060301802048540c140301c28130101c020602008180c060302807030200e1401018180c060300414060300e140a0540c040383018070a0180e09008080c130400412020a00808150202026130405412020301804080a0040e070a0500e09038500e0c06030180c060240408030541201030500e1403834240508004040c060540809008080c04010540c140301c041502038140b0182c240e0801c28140384c100d0900c1c070a0240c070104c1008098540815020541215020500e14008282214038201013030182a0d050380615020540c01048080c08010040c11068240401030040c14038500e070a018040b02840240e05034060d0503806110880c220d05038060003838240d080381a0b080480a0d0182c14030282c0a1009048160307014200b090001e00078501e010480406130601016070302018050a81c2613070280a040003404060184008040a0541a0209830160b0a8241c03088241e01040500e11008341a02000440a030082824060382024060881c0c1405038100f05024040c010481e100a02428150704008070402c22050000c140c0903404130a0042015070240c0f)
lemma f2 : SignFixed h2 := fixed _ _ (by decide +kernel)
def h3 := pairHom (selectRow 0x2c36109029db7337d99fcd494b45a40a48b52a4d99e51d6ccf9c1267aa31a4943045b0c0ef97dbddeaed77bc5e6eb71b95cee970b7db6dd6bb65aacf66b4da2c563b2596bd5fb0586b95dad56eb358ab55ea955a954ea151a7d32974ea6d2a9347a45168d43a250685409fcf67d3b9e4de71399d4ce69359b4c6652f984b65d2a94cb25727944964d219148e491f9046e391d8f4622f1a8cc4e29158b43e21118942e190d8742a1307844160d038240604fe7ec01fefa7cbf1f6f77c3d5ecf37a3bde0f1793b1d6ee76ba9d2e672ba1cee372381bee270b6db8dd6f35db0d96d34da8d56b33da0d1693359ccb6632594c7643158cc16130d88bf602f57cbb5e2e574b65aae16eb459ac15eb258ab95aa9552ad58a7542954ca250a91469f502753c994d26d38954b25d30914924d288f482351c8b462291287442150c8342200fe82409f0f67e3e9dcf0793d1cce8753b1bce071391b4dc461780814681001038190204c18310a81c104b1900c1618208d032551d1249c471e9441c292e128a40e281b04e39218ecae151f8509e2b0994c88631200c3c560d96cc0210d894201f050a0982a2288c5c37131001067160d41e6517818aa5806920803e1d8146c0d0e92020612c8ac02212f06824631b1a81200) (selectRow 0x2613090440e150002408060a050040a0701818150a01c2614020480410070500803098182a0903020180c0603018010305412140481c28080081c040902004180c0603028070484c0e1400824180c060300214060300e140a05412040383018070a0240e06010041208098080c010a00408150204c1008098540c010482402130a0080e070a0500e06038500e0c06030180c060180213048540c02048500e1403838200b09008020c0605408060100412040085412140481c021502034060505014200d0901c281403820260e080281a070a0181207008202613040540815020540c15020500e140100c22140384c2608048242a0e018341415020541202030041213008081211070180202048081214038500e070a024020505848200d01838140e01834141108828220e01834140003834200e090341c0509040160e05014060a058141612080400a0a0682c2405080001e00078501e02030081408060100a070484c180b0a81c10080680c16040003802090504808040a0541c01040300a050a8181a0a088181e02098500e11010381c0100044160a0100c20090384c20090881c121401834260f01818020c008401e120a018281506848080709814220b00028060c0803802080a008241506818120f)
lemma f3 : SignFixed h3 := fixed _ _ (by decide +kernel)
def hom (i : Nat) : SigHom := if i=1 then h1 else if i=2 then h2 else h3
lemma fixedAll (i : Nat) : SignFixed (hom i) := by
  unfold hom
  split
  · exact f1
  · split
    · exact f2
    · exact f3
def seeds : Fin 9 → Sig := ![(0x3829028201402402822480c5505212a0050504cc7554930055280355403013954155124e2d554318ae073a127a8844081958250,0x382942820144e412822492c5505272a0252d64cc75549318552883554cb4b395415d734e2d51431cae073a12fa8844281958658),(0xcf9f38f02101122018822448641d85176444345b91c2386776455d0678e305879d11b7667774b6b37d9f7cc97f77bb7bb6cffb4,0x3dfdfbdfffffb9fedffdf6d7bffff8d5ffed7bf7fbbeb7cefffd77fbefbeb4fefbfb3bffff7febefb7ffffded7f77bbfff6fffb7),(0x8b066d34108421102484511062627096e2224b1c6e24581eee24f299996490799a8e5d61eeea5b6ffa76f4fbf6ee0dff5bbae7c,0x3fb2f6fbeffc5efd6bee5f3df7ff373bff72fffdc7f7cfb5fffaef3ddddf4b3fddbdfff6feffbdf7ffe77fefbfeeecfff5ffbf7d),(0x87449d7500a0180141130122a82c0d40028283338aab0c802ad004aaa0480c6aa0aa8c31d2aa848011f80524016339c7e606826,0x87d49d7580ba1829411b0d22a82c8d404ad283338aab0ce02ad50caaa24b4c6aa4a28cb1d2aea48051f80564017339c7e6068a7),(0xc17cf694021803c0030ffe0787800018078019e0187861f807f8061e1e07fe0001e7e1ff8007adff4f77bf75bfbefff4eff77fa,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),(0x5ad1042008420888284148901965884d9911549796114665d9936c59871c499876565a9e5dddfed9f9ecebfc8e5386d7feff9ce,0x3dff7bf7ffefb3bed7ddf6dbebfedcd5fdfd3dfb79ffb6ee7ffdf7effb75f4dfafef6defffffffefbf9fcfffd8ff7bfd7feff9ff),(0x3e838769c801640270038198e04815920507cc18141cfb5d3004fe1e195d5f95ffff9f9d5337fe244ccca37efedccdf83c5ec4ec,0x3e9fcf6dc8096603701389b8e84a1ffe0537cc18147dfb7d3027fe1e195d5f95ffffdf9f53b7fe344ccca37ffedccdfc3edee4ed),(0x68d881d04009c018c03806718300a6c0287b2060a637cbac803799e06babe6bffffe67aaccfe3117ef8983a76f73fdae293af8a,0x6cd8d1d1413fd43bc33a9e71c31ebee028ff206be6b7dfbc80779de26babfebfffff67badcfe3197ef8b83a77f7bfdaea93ef8b),(0x3e03105a8042084441440a228189a622b9888aa2e6988a61bb98aba26669a22666e29ae99bbbb7ffeb6f3dbbbd9bde32f1c7dd3a,0x3fe3b6fab7f6dffdefee7f6fd7fdf72bfbdaffefefdfcff3ffdaaff7f7fbeb7f77f7fffdffffb7fffbff7fbbbffbfe73f1ffdf7b)]
lemma seedValid : ∀ i,Valid (seeds i) := by
  have all : ∀ i,(seeds i).1≤top ∧ (seeds i).2≤top := by decide +kernel
  intro i;exact ⟨valid1_of_le_top (all i).1,valid1_of_le_top (all i).2⟩
def perms : Fin 4 → Fin 9 → Fin 9 := ![![3,8,5,0,4,2,6,7,1],![0,5,8,3,4,1,7,6,2],![3,2,1,0,4,8,7,6,5],![3,8,5,0,4,2,6,7,1]]
lemma seedMove : ∀ p : Fin 4,∀ i,(hom p.val).fn (seeds i)=seeds (perms p i) := by decide +kernel
def e0 : Form := .raw 0
def e1 : Form := .raw 1
def e2 : Form := .raw 2
def e3 : Form := .raw 3
def e4 : Form := .raw 4
def e5 : Form := .raw 5
def e6 : Form := .raw 6
def e7 : Form := .raw 7
def e8 : Form := .raw 8
def e9 : Form := .merge false false e0 e1
def e11 : Form := .merge false true e0 e1
def e10 : Form := .merge true false e0 e1
def e12 : Form := .merge true true e0 e1
def e13 : Form := .merge false false e0 e2
def e248 : Form := .merge false true e0 e2
def e14 : Form := .merge true false e0 e2
def e249 : Form := .merge true true e0 e2
def e15 : Form := .merge true true e0 e3
def e16 : Form := .merge false false e0 e4
def e250 : Form := .merge false true e0 e4
def e17 : Form := .merge true false e0 e4
def e251 : Form := .merge true true e0 e4
def e252 : Form := .merge false false e0 e5
def e129 : Form := .merge false true e0 e5
def e253 : Form := .merge true false e0 e5
def e130 : Form := .merge true true e0 e5
def e18 : Form := .merge false false e0 e6
def e254 : Form := .merge false true e0 e6
def e19 : Form := .merge true false e0 e6
def e255 : Form := .merge true true e0 e6
def e131 : Form := .merge false false e0 e7
def e256 : Form := .merge false true e0 e7
def e132 : Form := .merge true false e0 e7
def e257 : Form := .merge true true e0 e7
def e20 : Form := .merge false false e0 e8
def e258 : Form := .merge false true e0 e8
def e21 : Form := .merge true false e0 e8
def e259 : Form := .merge true true e0 e8
def e78 : Form := .merge false false e1 e2
def e260 : Form := .merge false true e1 e2
def e79 : Form := .merge true false e1 e2
def e303 : Form := .merge true true e1 e2
def e22 : Form := .merge false false e1 e3
def e23 : Form := .merge false true e1 e3
def e111 : Form := .merge true false e1 e3
def e89 : Form := .merge true true e1 e3
def e24 : Form := .merge false false e1 e4
def e320 : Form := .merge false true e1 e4
def e25 : Form := .merge true false e1 e4
def e321 : Form := .merge true true e1 e4
def e26 : Form := .merge false false e1 e5
def e322 : Form := .merge false true e1 e5
def e27 : Form := .merge true false e1 e5
def e323 : Form := .merge true true e1 e5
def e324 : Form := .merge false false e1 e6
def e90 : Form := .merge false true e1 e6
def e325 : Form := .merge true false e1 e6
def e91 : Form := .merge true true e1 e6
def e294 : Form := .merge false false e1 e7
def e326 : Form := .merge false true e1 e7
def e295 : Form := .merge true false e1 e7
def e327 : Form := .merge true true e1 e7
def e92 : Form := .merge false false e1 e8
def e328 : Form := .merge false true e1 e8
def e93 : Form := .merge true false e1 e8
def e329 : Form := .merge true true e1 e8
def e330 : Form := .merge false false e2 e3
def e332 : Form := .merge false true e2 e3
def e331 : Form := .merge true false e2 e3
def e333 : Form := .merge true true e2 e3
def e28 : Form := .merge false false e2 e4
def e307 : Form := .merge false true e2 e4
def e29 : Form := .merge true false e2 e4
def e350 : Form := .merge true true e2 e4
def e263 : Form := .merge false false e2 e5
def e365 : Form := .merge false true e2 e5
def e264 : Form := .merge true false e2 e5
def e366 : Form := .merge true true e2 e5
def e367 : Form := .merge false false e2 e6
def e369 : Form := .merge false true e2 e6
def e368 : Form := .merge true false e2 e6
def e370 : Form := .merge true true e2 e6
def e371 : Form := .merge false false e2 e7
def e373 : Form := .merge false true e2 e7
def e372 : Form := .merge true false e2 e7
def e374 : Form := .merge true true e2 e7
def e375 : Form := .merge false false e2 e8
def e377 : Form := .merge false true e2 e8
def e376 : Form := .merge true false e2 e8
def e378 : Form := .merge true true e2 e8
def e34 : Form := .merge false false e3 e4
def e339 : Form := .merge false true e3 e4
def e35 : Form := .merge true false e3 e4
def e308 : Form := .merge true true e3 e4
def e36 : Form := .merge false false e3 e5
def e358 : Form := .merge false true e3 e5
def e37 : Form := .merge true false e3 e5
def e393 : Form := .merge true true e3 e5
def e394 : Form := .merge false false e3 e6
def e396 : Form := .merge false true e3 e6
def e395 : Form := .merge true false e3 e6
def e397 : Form := .merge true true e3 e6
def e398 : Form := .merge false false e3 e7
def e400 : Form := .merge false true e3 e7
def e399 : Form := .merge true false e3 e7
def e401 : Form := .merge true true e3 e7
def e402 : Form := .merge false false e3 e8
def e404 : Form := .merge false true e3 e8
def e403 : Form := .merge true false e3 e8
def e405 : Form := .merge true true e3 e8
def e41 : Form := .merge false false e4 e5
def e42 : Form := .merge false true e4 e5
def e341 : Form := .merge true false e4 e5
def e413 : Form := .merge true true e4 e5
def e43 : Form := .merge false false e4 e6
def e44 : Form := .merge false true e4 e6
def e309 : Form := .merge true false e4 e6
def e414 : Form := .merge true true e4 e6
def e45 : Form := .merge false false e4 e7
def e46 : Form := .merge false true e4 e7
def e344 : Form := .merge true false e4 e7
def e415 : Form := .merge true true e4 e7
def e47 : Form := .merge false false e4 e8
def e48 : Form := .merge false true e4 e8
def e312 : Form := .merge true false e4 e8
def e418 : Form := .merge true true e4 e8
def e422 : Form := .merge false false e5 e6
def e424 : Form := .merge false true e5 e6
def e423 : Form := .merge true false e5 e6
def e425 : Form := .merge true true e5 e6
def e359 : Form := .merge false false e5 e7
def e426 : Form := .merge false true e5 e7
def e360 : Form := .merge true false e5 e7
def e427 : Form := .merge true true e5 e7
def e386 : Form := .merge false false e5 e8
def e428 : Form := .merge false true e5 e8
def e387 : Form := .merge true false e5 e8
def e429 : Form := .merge true true e5 e8
def e430 : Form := .merge false false e6 e7
def e432 : Form := .merge false true e6 e7
def e431 : Form := .merge true false e6 e7
def e433 : Form := .merge true true e6 e7
def e434 : Form := .merge false false e6 e8
def e436 : Form := .merge false true e6 e8
def e435 : Form := .merge true false e6 e8
def e437 : Form := .merge true true e6 e8
def e438 : Form := .merge false false e7 e8
def e440 : Form := .merge false true e7 e8
def e439 : Form := .merge true false e7 e8
def e441 : Form := .merge true true e7 e8
def e38 : Form := .merge true true e3 e9
def e63 : Form := .merge false true e6 e9
def e66 : Form := .merge true true e6 e9
def e40 : Form := .merge true false e3 e10
def e137 : Form := .merge true true e3 e11
def e164 : Form := .merge false false e2 e12
def e167 : Form := .merge true false e2 e12
def e80 : Form := .merge true false e3 e12
def e179 : Form := .merge false false e4 e12
def e188 : Form := .merge true false e4 e12
def e205 : Form := .merge false false e5 e12
def e208 : Form := .merge true false e5 e12
def e214 : Form := .merge false false e6 e12
def e217 : Form := .merge true false e6 e12
def e221 : Form := .merge false false e7 e12
def e223 : Form := .merge true false e7 e12
def e228 : Form := .merge false false e8 e12
def e230 : Form := .merge true false e8 e12
def e237 : Form := .merge true true e3 e13
def e238 : Form := .merge false false e4 e13
def e239 : Form := .merge false true e4 e13
def e246 : Form := .merge false false e8 e13
def e247 : Form := .merge false true e8 e13
def e379 : Form := .merge true false e3 e14
def e380 : Form := .merge true true e3 e14
def e240 : Form := .merge false false e4 e14
def e241 : Form := .merge false true e4 e14
def e244 : Form := .merge false true e7 e14
def e245 : Form := .merge true true e7 e14
def e381 : Form := .merge false false e8 e14
def e382 : Form := .merge false true e8 e14
def e543 : Form := .merge false true e1 e248
def e169 : Form := .merge true true e1 e248
def e550 : Form := .merge true true e3 e248
def e558 : Form := .merge false true e4 e248
def e568 : Form := .merge true true e4 e248
def e584 : Form := .merge false true e5 e248
def e586 : Form := .merge true true e5 e248
def e592 : Form := .merge false true e6 e248
def e594 : Form := .merge true true e6 e248
def e598 : Form := .merge false true e7 e248
def e600 : Form := .merge true true e7 e248
def e604 : Form := .merge false true e8 e248
def e606 : Form := .merge true true e8 e248
def e406 : Form := .merge false false e2 e15
def e634 : Form := .merge false false e4 e15
def e636 : Form := .merge false true e4 e15
def e642 : Form := .merge false false e6 e15
def e647 : Form := .merge true false e6 e15
def e654 : Form := .merge false false e7 e15
def e659 : Form := .merge true false e7 e15
def e666 : Form := .merge false false e8 e15
def e668 : Form := .merge false true e8 e15
def e313 : Form := .merge false true e2 e16
def e682 : Form := .merge true true e3 e16
def e787 : Form := .merge false false e8 e16
def e788 : Form := .merge false true e8 e16
def e419 : Form := .merge false true e2 e17
def e712 : Form := .merge true true e3 e17
def e818 : Form := .merge false false e8 e17
def e916 : Form := .merge false true e8 e17
def e1042 : Form := .merge false true e1 e250
def e190 : Form := .merge true true e1 e250
def e479 : Form := .merge false true e2 e250
def e1030 : Form := .merge true true e2 e250
def e674 : Form := .merge true true e3 e250
def e1031 : Form := .merge false true e5 e250
def e1032 : Form := .merge true true e5 e250
def e1034 : Form := .merge false true e6 e250
def e1035 : Form := .merge true true e6 e250
def e1036 : Form := .merge false true e7 e250
def e1037 : Form := .merge true true e7 e250
def e1039 : Form := .merge false true e8 e250
def e1040 : Form := .merge true true e8 e250
def e1059 : Form := .merge false false e1 e251
def e1061 : Form := .merge true false e1 e251
def e345 : Form := .merge false false e2 e251
def e572 : Form := .merge true false e2 e251
def e774 : Form := .merge true false e3 e251
def e1063 : Form := .merge false false e5 e251
def e1065 : Form := .merge true false e5 e251
def e1067 : Form := .merge false false e6 e251
def e1068 : Form := .merge true false e6 e251
def e1069 : Form := .merge false false e7 e251
def e1070 : Form := .merge true false e7 e251
def e1072 : Form := .merge false false e8 e251
def e1073 : Form := .merge true false e8 e251
def e1216 : Form := .merge false true e1 e18
def e215 : Form := .merge true true e1 e18
def e644 : Form := .merge true true e3 e18
def e649 : Form := .merge true true e3 e254
def e1614 : Form := .merge false true e3 e79
def e1620 : Form := .merge true true e3 e79
def e1680 : Form := .merge false false e0 e303
def e1686 : Form := .merge true false e0 e303
def e1687 : Form := .merge false false e3 e303
def e1699 : Form := .merge true false e3 e303
def e1707 : Form := .merge false false e4 e303
def e1716 : Form := .merge true false e4 e303
def e1731 : Form := .merge false false e5 e303
def e1733 : Form := .merge true false e5 e303
def e1739 : Form := .merge false false e6 e303
def e1741 : Form := .merge true false e6 e303
def e1745 : Form := .merge false false e7 e303
def e1747 : Form := .merge true false e7 e303
def e1751 : Form := .merge false false e8 e303
def e1753 : Form := .merge true false e8 e303
def e99 : Form := .merge false false e4 e22
def e100 : Form := .merge false true e4 e22
def e101 : Form := .merge false false e5 e22
def e83 : Form := .merge false false e4 e23
def e84 : Form := .merge false true e4 e23
def e304 : Form := .merge false false e5 e23
def e318 : Form := .merge false true e3 e25
def e319 : Form := .merge true true e3 e25
def e2018 : Form := .merge false true e0 e320
def e189 : Form := .merge true true e0 e320
def e862 : Form := .merge false true e2 e320
def e863 : Form := .merge true true e2 e320
def e193 : Form := .merge false true e3 e320
def e864 : Form := .merge true true e3 e320
def e866 : Form := .merge false true e5 e320
def e869 : Form := .merge true true e5 e320
def e870 : Form := .merge false true e6 e320
def e871 : Form := .merge true true e6 e320
def e872 : Form := .merge false true e7 e320
def e873 : Form := .merge true true e7 e320
def e874 : Form := .merge false true e8 e320
def e875 : Form := .merge true true e8 e320
def e2053 : Form := .merge false false e0 e321
def e2059 : Form := .merge true false e0 e321
def e2067 : Form := .merge false false e2 e321
def e2068 : Form := .merge true false e2 e321
def e2062 : Form := .merge false false e3 e321
def e2074 : Form := .merge true false e3 e321
def e2078 : Form := .merge false false e5 e321
def e2079 : Form := .merge true false e5 e321
def e2084 : Form := .merge false false e6 e321
def e2085 : Form := .merge true false e6 e321
def e2088 : Form := .merge false false e7 e321
def e2089 : Form := .merge true false e7 e321
def e2092 : Form := .merge false false e8 e321
def e2093 : Form := .merge true false e8 e321
def e1889 : Form := .merge false true e0 e26
def e206 : Form := .merge true true e0 e26
def e1166 : Form := .merge false true e3 e27
def e2152 : Form := .merge true true e3 e27
def e1894 : Form := .merge false true e7 e27
def e1895 : Form := .merge true true e7 e27
def e2213 : Form := .merge false false e3 e323
def e2217 : Form := .merge true false e3 e323
def e2258 : Form := .merge false true e3 e325
def e1872 : Form := .merge true true e3 e325
def e67 : Form := .merge false false e0 e91
def e2306 : Form := .merge true false e0 e91
def e2316 : Form := .merge false false e2 e91
def e2319 : Form := .merge true false e2 e91
def e2309 : Form := .merge false false e3 e91
def e1876 : Form := .merge true false e3 e91
def e1942 : Form := .merge false false e4 e91
def e2047 : Form := .merge true false e4 e91
def e2353 : Form := .merge false false e5 e91
def e2200 : Form := .merge true false e5 e91
def e2359 : Form := .merge false false e7 e91
def e2361 : Form := .merge true false e7 e91
def e2365 : Form := .merge false false e8 e91
def e2367 : Form := .merge true false e8 e91
def e2393 : Form := .merge false true e3 e295
def e2399 : Form := .merge true true e3 e295
def e2408 : Form := .merge false true e5 e295
def e2411 : Form := .merge true true e5 e295
def e2424 : Form := .merge false true e0 e326
def e224 : Form := .merge true true e0 e326
def e2458 : Form := .merge false false e3 e327
def e2464 : Form := .merge true false e3 e327
def e1435 : Form := .merge false true e6 e92
def e1436 : Form := .merge true true e6 e92
def e2520 : Form := .merge false true e3 e93
def e2526 : Form := .merge true true e3 e93
def e2566 : Form := .merge false false e0 e329
def e2572 : Form := .merge true false e0 e329
def e2580 : Form := .merge false false e2 e329
def e2583 : Form := .merge true false e2 e329
def e2575 : Form := .merge false false e3 e329
def e2593 : Form := .merge true false e3 e329
def e1943 : Form := .merge false false e4 e329
def e2052 : Form := .merge true false e4 e329
def e2617 : Form := .merge false false e5 e329
def e2619 : Form := .merge true false e5 e329
def e2623 : Form := .merge false false e6 e329
def e2625 : Form := .merge true false e6 e329
def e2627 : Form := .merge false false e7 e329
def e2629 : Form := .merge true false e7 e329
def e569 : Form := .merge false true e0 e307
def e950 : Form := .merge true true e3 e307
def e953 : Form := .merge false true e6 e307
def e958 : Form := .merge false true e8 e307
def e978 : Form := .merge false false e2 e308
def e986 : Form := .merge false false e8 e308
def e1971 : Form := .merge false true e0 e309
def e1977 : Form := .merge true true e0 e309
def e4016 : Form := .merge false true e1 e309
def e2342 : Form := .merge true true e1 e309
def e1978 : Form := .merge false true e2 e309
def e1980 : Form := .merge true true e2 e309
def e1981 : Form := .merge false true e3 e309
def e1982 : Form := .merge true true e3 e309
def e1984 : Form := .merge false true e5 e309
def e1985 : Form := .merge true true e5 e309
def e1986 : Form := .merge false true e7 e309
def e1987 : Form := .merge true true e7 e309
def e1989 : Form := .merge false true e8 e309
def e1991 : Form := .merge true true e8 e309
def e4050 : Form := .merge false false e0 e414
def e4056 : Form := .merge true false e0 e414
def e4064 : Form := .merge false false e1 e414
def e4067 : Form := .merge true false e1 e414
def e4070 : Form := .merge false false e2 e414
def e4071 : Form := .merge true false e2 e414
def e4059 : Form := .merge false false e3 e414
def e4078 : Form := .merge true false e3 e414
def e4083 : Form := .merge false false e5 e414
def e4084 : Form := .merge true false e5 e414
def e4087 : Form := .merge false false e7 e414
def e4088 : Form := .merge true false e7 e414
def e4091 : Form := .merge false false e8 e414
def e4092 : Form := .merge true false e8 e414
def e1546 : Form := .merge false true e0 e312
def e1013 : Form := .merge false true e2 e312
def e1016 : Form := .merge true true e3 e312
def e1019 : Form := .merge false true e6 e312
def e4644 : Form := .merge false false e0 e433
def e4652 : Form := .merge true false e0 e433
def e4655 : Form := .merge false false e3 e433
def e4673 : Form := .merge true false e3 e433
def e533 : Form := .merge true true e3 e381
def e1223 : Form := .merge false false e4 e215
def e1905 : Form := .merge true true e0 e304
def e2105 : Form := .merge false false e2 e206
def e2111 : Form := .merge false false e4 e206
def e2125 : Form := .merge false false e8 e206
def e2497 : Form := .merge false false e4 e1436
set_option maxRecDepth 120000 in
def terms : Array Form := #[e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,e20,e21,e22,e23,e24,e25,e26,e27,e28,e29,e34,e35,e36,e37,e38,e40,e41,e42,e43,e44,e45,e46,e47,e48,e63,e66,e67,e78,e79,e80,e83,e84,e89,e90,e91,e92,e93,e99,e100,e101,e111,e129,e130,e131,e132,e137,e164,e167,e169,e179,e188,e189,e190,e193,e205,e206,e208,e214,e215,e217,e221,e223,e224,e228,e230,e237,e238,e239,e240,e241,e244,e245,e246,e247,e248,e249,e250,e251,e252,e253,e254,e255,e256,e257,e258,e259,e260,e263,e264,e294,e295,e303,e304,e307,e308,e309,e312,e313,e318,e319,e320,e321,e322,e323,e324,e325,e326,e327,e328,e329,e330,e331,e332,e333,e339,e341,e344,e345,e350,e358,e359,e360,e365,e366,e367,e368,e369,e370,e371,e372,e373,e374,e375,e376,e377,e378,e379,e380,e381,e382,e386,e387,e393,e394,e395,e396,e397,e398,e399,e400,e401,e402,e403,e404,e405,e406,e413,e414,e415,e418,e419,e422,e423,e424,e425,e426,e427,e428,e429,e430,e431,e432,e433,e434,e435,e436,e437,e438,e439,e440,e441,e479,e533,e543,e550,e558,e568,e569,e572,e584,e586,e592,e594,e598,e600,e604,e606,e634,e636,e642,e644,e647,e649,e654,e659,e666,e668,e674,e682,e712,e774,e787,e788,e818,e862,e863,e864,e866,e869,e870,e871,e872,e873,e874,e875,e916,e950,e953,e958,e978,e986,e1013,e1016,e1019,e1030,e1031,e1032,e1034,e1035,e1036,e1037,e1039,e1040,e1042,e1059,e1061,e1063,e1065,e1067,e1068,e1069,e1070,e1072,e1073,e1166,e1216,e1223,e1435,e1436,e1546,e1614,e1620,e1680,e1686,e1687,e1699,e1707,e1716,e1731,e1733,e1739,e1741,e1745,e1747,e1751,e1753,e1872,e1876,e1889,e1894,e1895,e1905,e1942,e1943,e1971,e1977,e1978,e1980,e1981,e1982,e1984,e1985,e1986,e1987,e1989,e1991,e2018,e2047,e2052,e2053,e2059,e2062,e2067,e2068,e2074,e2078,e2079,e2084,e2085,e2088,e2089,e2092,e2093,e2105,e2111,e2125,e2152,e2200,e2213,e2217,e2258,e2306,e2309,e2316,e2319,e2342,e2353,e2359,e2361,e2365,e2367,e2393,e2399,e2408,e2411,e2424,e2458,e2464,e2497,e2520,e2526,e2566,e2572,e2575,e2580,e2583,e2593,e2617,e2619,e2623,e2625,e2627,e2629,e4016,e4050,e4056,e4059,e4064,e4067,e4070,e4071,e4078,e4083,e4084,e4087,e4088,e4091,e4092,e4644,e4652,e4655,e4673]
def term (i : Nat) := terms[i]?.getD (.raw 0)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def book : Book := ⟨910,392,fun i => value seeds (term i),⟨93,#[0x602008038180a0301400001d0180401c0c050180a00000320c04010070301405000001c8602008038180a02800003903008038180a0301400001c818080200e060280a00000750c0200e060280c0500000158602007030140602800000a83010038180a03014000005218080200c050180a00000280c04010060280c05000001386020080381406028000009830100401c0a03014000004a18080200e060180a00000240c04010070300c05000000f8602008038180a028000007830100401c0c05014000003a18080200e060280e000001c0c04010070301407000007206010070301404008000037db60802810060200c00001b21c0401c0c050180600000280e03c10060280c03000000f0701e08038180a01800003643008038180a030140000054180781c0c050180a00000260c03c10070280c05000000f8601e08038180a0280000070300f0401c0c0501c000019408038180a0401006000002a130380e050180803000002c89010070300c0401800000a8480e03818060200c000005024070200c030100600000240f8381007030080300000150781c07030140401800001643808038180a0300c00000501c070200c050180600000240e03810070300c03000000f0701c08038180a01800001643008038180a030140000054180701c0c050180a00000260c03810070280c05000000f8601c08038180a0280000070300e0401c0c0501c00000ae2a038180a0301006000002a130340e050180803000002b09010070300c0401800000a8480d03818060200c000005024068200c030100600000570f8200e060280803000001207c1a08038180401800000a83c0d038180a0200c00000d620068200e060200600000570e0200e060280c0300000140701a0803014060180000090380d0401c0c0300c000003c1c068200e060280600000560c0200e060280c0500000150601a0703014060280000098300d0401c0a03014000003e18068200e060280a000001c0c0341007030140700000178581a08038180a048,0x45c3008038180a030140000054290c0180a0301002000002a140600c050180801000001509c30070280c0400800004e83007030140602004000004c180401c0a030100200001350c0200e06028080100000990601007030140600800004c03008038180a030140000056260c01c0a0301002000002a130600e050180801000001489830080280c0400800000a04c18040140602004000004c250c0200e03010020000026120601007018080100000190a83007030140400800000c84c180401c0a0200400000722a0c01c0c050100200000391306010070280801000007c0600e060280c0400800003dc300803814060200400001ec180401c0c050100200000cf0c0200e060280c05000000e0601007030140600800000a83a18038180a03004000004c1d0c0200e050180200000580e06010070301407000002b0703008038180a038000009c38180401c0a03004000004c1c0c0200e050180200000250e06010070300c0100000120703008038180600800001dc3008038180a02004000022808038180a0301002000010e0e0200c05018040100000840a80e060280c0400800004203808038180a03004000020a18038180a030100200001010c0200e05018080100000718601007030140400800003243008038180a0300400001f2110401c0c050180600000270f84410070280803000001307c2208038140401800003e0220703014060200c00001ec110401c0c050100600000da0e0441007030140300000158702207030140601800000a83811038180a0300c00000521c088200c050180600000280e04410060280c03000001387022080381406018000009838110401c0a0300c0000054190881c0c050180a000001f0c84410070301405000000e0642208038180a03800000a83011038180a03014000004c18088200e050180a000001f0c04410070301405000000e0602208038180a038000007c2208038180a0200c0000038110401c0c050180600000280e04010060280c03000007684010070300c04018,0x4203e08038180a0200400001c6240401c0c020080200000c9120200e060180401000001509c22070280c0401800000a84c1103814060200c00001b42a0881c0c050100600000fa0881c0c050180803000001587c2207030140401800000a83e11038180a0200c00000521f088200c050100600000280f84410060280803000001287c2208038180401800000903e110401c0c0200c00000541d0881c0c0501806000001f0e8441007030140300000108702208038180a018000008038110401c0c0500c000004a1c088200e060180600000240e04410070300c03000000f8702208038180a018000007838110401c0c0500c000003817088200e0602806000001c0b0441007030140300000150780e06028080200800000783808038180a01004000005411038180a0301006000002a130400e050180803000001389020080380c04018000009848100401c060200c00001c8240401c0c030100600000e41204010070300803000001207c2008038180401800000a83c10038180a0200c00000481e080200e06010060000075120200e060180803000001207420080381806018000009038100401c0c0300c000003c1c080200e060280600000240c84010070300c05000007386010070301406028000008430100401c0c05014000004018080200e060280a00000180b84010070301405000000c0582008038180a028000039048080381804010040000054180781c0c050100200000260c03c10070280801000000e0601e08038180a0080000070220f0401c0c0500c000003010078200e060280a00000d91501c0c05018080300000150981e070280c040180000364480803818060200c00000481f078200e0601006000002a0f03c0e06028080300000120701e080381806018000059810070280c0401004000029c08038180a0301006000014d0401c0c050200c0300000798980e05018080200800000a8300703014060200400001fa180401c0a030100200000fc0c0200e060280801000007d86010070301406008,0xa04c240400c04010040000050260e0200a0300802000014f038180a04018080300000778a80e05018080200800003b454070300c040100400000922a038180a020080200000ed0f8200e060100401000007887010060280c0200800003b4380803818060100400000921c0401c0c050080200000471501c0c050180803000002387c10070301404018000011c3808038180a0300c0000054260c81c0a03010020000028120641006018080100000140703208030140600800003a45418038180a0301400001ce2a0c01c0c050180a000002a128600e060180801000001509030070300c0400800000a048180401806020040000054210c01c0c050100200000261086010070280801000001508030070301404008000009840180401c0a0200400000561f0c01c0c0501002000002a0f8600e060280801000001487c3008030140400800000a03e18040180a02004000004e1f0c0200e050100200000260f86010070280801000001287c3008038180400800000903e180401c0c02004000003e180401c0c0501002000002a0f0600e060280801000001307830080381404008000007c3a180401c0c0500400000641c0c0200e060280200000390e0601007030140100000108703008038180a008000008038180401c0c0500400000561c0c01c0c0501802000002a0e0600e060280c0100000148703008030140600800000a03818040180a03004000003e1c0c0200e0602802000001e0e0601007030140100000968200e06028100401800000cc3008038180a020040000054180b81c0c050100200000260c05c10070280801000000e0602e08038180a00800000e4540703014040100400000721c0401c0c0500802000003a0c0200e06028080100000150602c070301404008000009830160401c0a020040000038180b0200e060280200000260c05410070280c05000000e0602a08038180a038000009830140401c0a030140000038180a0200e060280e000010c1501c0a030100401000008507010070300c02008,0x4c038100703014080300c800741c08038180a0401806400380e0401c0c050200c0320019070200e060281006029000c03810070301408030148005c1c08038180a0401006400b60803014080301004012005a040180a040180802009002e8200e0602810060200c80170100703014080301006400ae08038180a040180803200560401c0c050200c0401900158340e0602810060200c800a81a0703014080301006400520d040180a04018080320028068200c050200c040190013834100702810060200c800981a08038140803010064004a0d0401c0c04018080320024068200e060200c04019002a8200e0602810060200c801541a08038180a0401006400420d0401c0c05020080320020068200e060281004019000f834100703014080200c800781a08038180a04010064001c08038180a0401808032006c068200e0602810060190035834100703014080300c800741a08038180a0401806400380d0401c0c050200c0320019068200e060281006029000c03410070301408030148005c1a08038180a04010064002c0d0401c0c0502008032006a068200e0602810060190017834100703014080300c801541007030140802008024001c0d0401c0c050200c0320054038180a040180802009002981c0c050200c040100480144100602810060200802400a00803014080301004012004f0401c0a04018080200900268200e050200c04010048013010070301006020080240094080381808030100401200460401c0c05018080200900228200e060280c0401004800c41007030140802008024008608038180a040180401200420401c0c050200c0200900208200e060281004010048008c1007030140802008024002c08038180a04010040120017050200e06028100400900168200e050200c0401004800b01007028100602008024004408038180a04010040120000ba8a80e060280c0400800004c4540703014060200c00000542603814060200802000002a148980a03010040100000150a04c050180802008,0x13040100702810060200c80390100703014080301006401c8100401c0c0502008032001f080200e060281004019000f040100703014080200c801d41007030140803010064003a100401c0c050200c032001c080200e060281006019003c040100703014060200c800642008038180a040180a4000018080200e060280c0500018080200e060280c04019000c04010070301408030148039010070301408020080240030100401c0c05018080120011080200e060280c04019006e83c100702810060200c8036c1e0803814080301006401b408038180a040180803200d90401c0c050200c04019001383c100702810060200c800981e0803814080301006400100703014080301004012000f0401c0c050200802009000f83c100703014080200c800781e08038180a04010064015e08038180a0401808032001d078200e060281006019000e03c100703014080300c800641e08038180a040180a400300f0401c0c050200c05200dd0401c0a040180802009006d8200e050200c0401004803600e0602810060200802401ae070301408030100401200d6040180a040180802009006a8200c050200c040100480350100702810060200802401a6080381408030100401200d20401c0c04018080200900688200e060200c0401004803381007030140602008024019a08038180a030100401200cc0401c0c05020080200900220200e060281006020048032c1007030140803010024013e08038180a0401808032009e0401c0c050200c04019002d838100602810060200c801681c0803014080301006400b208038180a040180803200580401c0c050200c0401900158380e0602810060200c800a81c0703014080301006400520e040180a04018080320028070200c050200c040190013838100702810060200c800981c08038140803010064004a0e0401c0c04018080320024070200e060200c040190010838100703014080200c8007c1c08038180a04010064003c0e0401c0c05020080320099070200e060281006019,0x983008038140602004000983008038140803010024004c180401c0c050180801200250c0200e060200c0400900120601007030100602004800c83008038180a040100240072180401c0c050200801200710c0200e060280c04009000e86010070301408030048000038180401c0c050180200038180401c0c050200c012002a0c01c0c050180802009001306010070280c0401004800703008038180a030080240032180401c0c050180801201230401c0a04018080200900910200e050200c040100480484100703010060200802402400803818080301004012011f0401c0c050180802009008f0200e060280c04010048046c1007030140803010064023408038180a040180803201190401c0c050200802009008c0200e0602810040100480378100703014080200802401b808038180a0401004012004e0401c0c050200c0400900898200e060281006020048043410070281006020080240218080381408030100401200d00401c0c050200c0200900448200e06028100601004801843808038180a03008024021208038180a040180801201080401c0c050200c0400900810200e050200c040100480404100702810060200802401c608038180a040100401200fe0401c0c050200c0200900648200e06028100601004801201007030140803010024020e08038180a040180801200600c0200e060280c040090013844100702810060200c80098220803814080301006401ca08038180a040180803200da088200e0602810040190039044100703014060200c800003e110401c0c05010060003e110401c0c050200803200b40401c0c050200c040190038844100703014060200c800742208038180a0401806400001c088200e060280c030001c088200e060280c04019000e044100703014080300c800642208038180a040180a40030110401c0c050200c052001e0401c0c050200802009000f8441007030140401004800702208038180a03008024002208038180a04018080320027080200e050200c04019,0xac0200e060281006010048055c100703014080300802402aa08038180a0401808032002e0401c0c050200c0401900940200e0602810040100480550100703014080200802402a608038180a040100401201520401c0c05020080200900960200c050200c0401004804ac100602810060200802402a008038180a040100401201120401c0c05020080200900258200e0602810060200c804a8100703014080301006402980703014080301004012014b038180a04018080200900a50200c050200c04010048052410060281006020080240290080381408030100401201470401c0a04018080200900a30200e060200c0401004805141007030100602008024028808038180a040100401201410401c0c05020080200900a18200e06028100601004805081007030140803008024028008038180a0401808032013f0401c0c050200c04019007a01c0c050200c0401004803cc0e0602810060200802401e4080301408030100401200f1040180a04018080200900780200e050200c0401004803bc100702810060200802401dc080381808030100401200ed0401c0c040180802009003c09810070280c0401004803b01007030140802008024009208038180a040100401200eb0401c0c050200c0200900750200e060281006010048011c1007030140803010064027808038180a040180803200180401c0c050200c0400900158640e06028100602004800a43208030140803010024005019040180a040180801200270c8200e050200c040090013064100702810060200480094320803818080301002400ee190401c0c050200801200760c8200e060281004009000e8641007030140803004801dc100703014080200802400ec08038180a040100401200190401c0c050200c0400900158600e06028100602004801d03008038180a0301002400002a0c01c0c0501808010002a0c01c0c050200c0400900148601006028100602004800a03008030140803010024004e180401c0a040180801200730c0200e060280c04009,0x700200c050200c04010048037c1006028100602008024013a08038180a0401808032009c0401c0c050200c040190010038100703014080200c80034100703014080301006401080e0401c0c050200c0320016070200e06028100401900c28200e0602810060200c806101007030140803010064030208030140803010040120180040180a04018080200900be0200e06028100601004805ec100703014080300802402f408038180a040180801201790401c0c050200c0400900bb8200e0602810060200c805d81007030140803010064005227040140803010040120139040180a040180802009009c0200c050200c0401004800981007028100602008024026608038180a040180401201320401c0c050200c0200900ac8200e06028100602004805d41007030140803010024026208038180a040180803201300401c0c050200c0401900138200e050200c0401004800a44c08028100602008024005026040140803010040120027130200e05018080200900ba0200c050200c0401004805cc100602810060200802402e4080381408030100401201710401c0a040180802009009f0200e060280c0401004804bc100703014060200802402da08038180a0401804012016c0401c0c050200c0200900b50200e0602810060200c805a4100703014080301006402d008038180a040100401201670401c0c050200802009008b0200e050200c040100480454100702810060200802402ca08038180a040100401201640401c0c05020080200900290200e0602810060200c8058c100703014080301006402c4080381808030100401201610401c0c04018080200900b00200e060281004010048057c100703014080200802402bc0703014080301004012015d038180a04018080200900ae0200c050200c04010048056c100602810060200802402a20803818080301004012015a0401c0c040180802009009e8200e060280c0401004804b81007030140602008024025208038180a040100401201560401c0c050200802009,0x858200e060200c040100480428100703010060200802400c22a038180a030100401200e60401c0c050200802009003087c1007030140401004804180e06028100602008024020a07030140803010040120104040180a04018080200900818200c050200c040100480400100703010060200802401fe08038180803010040120060120200e060180802009007a8200e0602810060200c803a41007030140803010064002008038180a0401808032002b0881c0c050200c04019003a044100703014060200c800005411038180a03010060005411038180a0401808032002a088200e060280c040190014844100602810060200c800a02208030140803010064004a110401c0c04018080320024088200e060200c040190010844100703014080200c800802208038180a04010064003e110401c0c0501808032001e088200e060281004019000b844100703014080200c800582208038180a04010064005411038180a030100401200e80401c0c050200c0401900738200e0602810060200c800ac2007030140803010064005410038180a04018080320029080200c050200c040190014040100602810060200c800942008038180803010064010e100401c0c050180803200001204010070300c040180012040100703010060200c800902008038180a030100640042100401c0c05020080320020080200e060281004019000b840100703014080200c800582008038180a040100640048100401c0c030100401200da0401c0c050200802009001383c1007028100401004800981e0803814080200802400320f0401c0c05020080120018078200e060281004009000883c100703014080200c800401e08038180a0401006401c408038180a040180803200e10401c0c050200c04019007003c100602810060200c8037c1e0803014080301006400560f038180a0401808032002a0781c0c050200c04019001483c100602810060200c800a01e08030140803010064004a0f0401c0c04018080320024078200e060200c04019,0x13870100702810060100480098380803814080300802402e00803818080301004012016f0401c0c04018080200900b70200e06028100401004805ac100703014080200802400421a0401c0c040100401200781501c0c050180802009003c07c1007030140401004801e03808038180a03008024005419038180a040180801200240c8200e060200c0400900108641007030140802004800803208038180a04010024003e190401c0c0502008012001e0c8200e060281004009000e0641007030140803004800a83008038180a030100240042180401c0c050200801200200c0200e06028100400900390601007030140602004800003e180401c0c05010020003e180401c0c0501808012001f0c0200e060281004009000f0601007030140802004800703008038180a03010024003e180401c0c050100401200700401c0c05020080200900190200e060281004010048009c2e08038140802008024004c170401c0a0401004012001b0b8200e060281004009000d05c1007030140802004800642e08038180a040100240030170401c0c0502008012003b0401c0c050200802009001c8200e060281004010048009c2c08038140802008024004c160401c0a040100401200380b0200e060281004009001b8581007030140802004800642c08038180a040100240030160401c0c05020080120127038180a040180802009009301c0c050200c040100480494100602810060200802402480803014080301004012011d0401c0c050200802009008e0200e06028100401004800c02c08038180a04010024005e160401c0c050200801200270a8200e050200c040190013054100702810060200c800642a08038180a040180a40030150401c0c050200c05200270a0200e050200c040190013050100702810060200c800dc28070301408030100640032140401c0c050200c05200180a0200e060281006029008881c0c050200c0401004804400e06028100602008024021e0803014080301004012010e040180a040180802009,0x180401c0c050200c0401005378200e06028100602008028c01007030140803010040145e08038180a04018080200a650401c0c050200c0401005320200e060281006020080284c1007030140803010040142408038180a04018080200a610401c0c050200c0401005300200e06028100602008028002208038180a04018080322208038180a04018080200a00080200e0602810060200c880200e06028100602008028001e08038180a04018080321e08038180a04018080200a5f0401c0c050200c04010052f0200e06028100602008028001c08038180a04018080321c08038180a04018080200a00068200e0602810060200c868200e06028100602008028301007030140803010040141608038180a04018080200a0a0401c0c050200c0401005048200e06028100602008028030e08038180a040100401201860401c0c05020080200900c181c0c050200c0401004806080e0602810060200802402fe0803818080301004012017e0401c0c04018080200900be8200e06028100401004805e0100703014080200802400562703814080301004012002a1381c0a040180802009001409c10050200c0401004804ec0e060281006020080240274070301408030100401201370401c0c040180802009009b0200e060200c0401004801cc5407030140602008024026a08038180a040100401201340401c0c05020080200900158980e050200c0401004801d04c0803814060200802400002a1301c0a0301004010002a1301c0a040180802009001509810070280c0401004800a84c07030140602008024004e250401c0803010040120026128200e040180802009001389010070200c0401004800984808038100602008024004e210401c0a04010040120026108200e05020080200900138801007028100401004800984008038140802008024004e1f0401c0a040100401200260f8200e05020080200900138781007028100401004800983c08038140802008024004e1d0401c0a040180401200260e8200e050200c02009,0x6c0401c0c050200c0401005358200e0602810060200802a28100703014080301004014e208038180a04018080200a000e8200e060281006010048e8200e06028100602008028003808038180a04018040123808038180a04018080200a850401c0c050200c0401005420200e0602810060200802a0c1007030140803010040150408038180a04018080200a800401c0c050200c04010053d0200e06028100602008028d010070301408030100401400170401c0c050200802009170401c0c050200c04010051e0200e06028100602008028002c08038180a04010040122c08038180a04018080200a6a0401c0c050200c0401005348200e06028100602008029a010070301408030100401400150401c0c050200c04019150401c0c050200c040100500050100703014080301006450100703014080301004014ce08038180a04018080200a660401c0c050200c0401005200200e06028100602008028fc1007030140803010040147c08038180a04018080200a3d0401c0c050200c0401005318200e0602810060200802988100703014080301004014000f0401c0c050200802009c00401c0c050200c04010055f0200e0602810060200802af41007030140803010040156208038180a04018080200a00138200e050200c0401004938200e06028100602008029cc10070301408030100401400260401c0a040180802009260401c0c050200c0401005408200e06028100602008028e01007030140803010040146e08038180a04018080200a7f0401c0c050200c04010053f0200e06028100602008029b8100703014080301004014da08038180a04018080200a360401c0c050200c04010051a8200e06028100602008029f4100703014080301004014f808038180a04018080200a7b0401c0c050200c04010050d8200e0602810060200802868100703014080301004014f208038180a04018080200a780401c0c050200c04010050006410070301408030100246410070301408030100401400180401c0c050200c04009,0xba0401c0c050200c04010055c8200e0602810060200802a341007030140803010040151808038180a04018080200ab80401c0c050200c04010055b8200e0602810060200802ad81007030140803010040156a08038180a04018080200ab30401c0c050200c0401005000ac0e06028100602008024ac100703014080301004014e808038180a04018080200a001501c0c050200c0401004950200e0602810060200802ac81007030140803010040140029040180a040180802009290401c0c050200c0401005440200e06028100602008028005008030140803010040125008038180a04018080200ab00401c0c050200c0401005000941007030100602008024941007030140803010040150e08038180a04018080200a00120200e060200c0401004920200e0602810060200802ab81007030140803010040155a08038180a04018080200aac0401c0c050200c0401005558200e0602810060200802aa81007030140803010040155208038180a04018080200aa80401c0c050200c0401005538200e0602810060200802a981007030140803010040154a08038180a04018080200aa40401c0c050200c0401005518200e0602810060200802a881007030140803010040151608038180a04018080200a00108200e06028100401004908200e06028100602008028004008038180a04010040124008038180a04018080200a720401c0c050200c0401005430200e06028100602008028003e08038180a04010040123e08038180a04018080200a000f0200e060281004010048f0200e0602810060200802a6c1007030140803010040153408038180a04018080200a990401c0c050200c04010054c0200e0602810060200802a5c1007030140803010040152c08038180a04018080200a950401c0c050200c04010054a0200e0602810060200802a4c1007030140803010040152408038180a04018080200a910401c0c050200c0401005480200e0602810060200802a3c1007030140803010040151c08038180a04018080200a,0x1007030140803010040139008038180a04018080200ac70401c0c050200c0401005630200e0602810060200802b141007030140803010040158808038180a04018080200ac30401c0c050200c0401005610200e0602810060200802b041007030140803010040157e08038180a04018080200abc0401c0c050200c04010055d8200e0602810060200802a841007030140803010040154008038180a04018080200a]⟩,⟨4,#[0x8888888888888888888888888888888888888888888888888888888888888888,0x8888888888888888888888888888888888888888888888888888888888888888,0x8888888888888888888888888888888888888888888888888888888888888888,0x8888888888888888888888888888888888888888888888888888888888888888,0x9999999999999999999999999999999999999999999999999999999999988888,0x9999999999999999999999999999999999999999999999999999999999999999,0x9999999999999999999999999999999999999999999999999999999999999999,0x9999999999999999999999999999999999999999999999999999999999999999,0x9999999999999999999999999999999999999999999999999999999999999999,0x9999999999999999999999999999999999999999999999999999999999999999,0x9999999999999999999999999999999999999999999999999999999999999999,0xaaaaaaaaaaaaaaaaaaaaaaaaaa99999999999999999999999999999999999999,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xbaaaaaaaaaaaaa]⟩,⟨11,#[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200400801002004008010020040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xe01c0380600c0180300600c0100200300600c01002004008010020040080100200400801002004008010020040080100200400400801002004008010020040080100200400801002004008010020040080100200400801,0x1a0340680d01a0340680d0180300600c0180300600c0180300600c0180300600c0180300600c0180300600c01602c0580b01602c048090120240400800e01c0380700e01c0380700e01c0380700e01c0380700e01c03807,0x22044088110220440780f01e03c0780f01e03c0780f01e03c0780f01e03c0780f01e0380700d01a0340680d01a0340680d01a0340680d01a0340680d01a0340680d01a0340680d01a0340680d01a0340680d01a0340680d,0x2604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604809012024048090120240480901202404809012,0x340680d01a0340680d01a0340680d01a0340680d01a0320640c8190320640c8190320640c8180300600c0180300600c0180300600c0180300600c0180300600c0180300600c01702e05c0b81702e0540a01302604c09813,0x4208410821042084108210420841082104208410821040080100200400800f01e03c0780f01e03a0740e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700d81b0360680d01a0340680d01a,0x4c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0901202304608c1182304408811022044088108210420841082104208410821,0x540a81502a0540a81502a0540a01402704e09c1302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c09813026,0x600c0180300600c0180300600c0180300600c0180300600c0180300600c0180300600c0180300600c01803005c0b81702e05c0b81682d05a0b41602c0560ac1582b0560ac1582b0560ac1582b0560ac1582b0560ac1582b,0x680d01a0340680d01a0340680d01a0340680d01a0340660cc198330660cc190320640c8190320640c8190320640c8190320640c8190320640c4188300600c0180300600c0180300600c0180300600c0180300600c018030,0x760ec1d83b0760ec1d83b0760ec1d83b0760ec1d83b0740e81d03a0740e81d03a0740e81d0390720e41c8390720e41c8390720e41c8390720e41c8390720e41c8390700e01c0380700e01c0380700d81a8340680d01a034,0x8210420841082104208410821042084108210420841080100200400801001f83f07e0fc1f83f07c0f81e83d07a0f41e83d07a0f41e83d07a0f41e83d07a0f41e83d07a0f41e83d07a0f41e03c0780ec1d83b0760ec1d83b,0x88110220440881102204408811022044088110220440881102204408811022044088110220440881102204408610c2184308610c21042084104208410821042084108210420841082104208410821042084108210420841,0x8a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a11422044088110220440881102204408811022044,0x8a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a11422845,0x8a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a11422845,0x8a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a1142284508a11422845,0x9a1342684d09a1342604c0981302584b0941282504a0941282504a0941282504a0941282504a0941282504a092124248490921242484909211c2384608c1182284508a1142284508a1142284508a1142284508a11422845,0xa4148290520a4148288510a2144288510a2144288510a2144288510a2144288510a21402804f09e13c2784f09e13c2784f09e13c2784f09e13c2784f09e13c2784f09e13c2784f09e13c2784f09e13c2784f09e13c2784f,0xaa1542a8550aa1542a8550aa1542a8550aa1542a8550a81502a0540a81502a0540a81502a0530a614c298530a614c298530a614c298530a614c298530a614c298530a614c298530a614c298530a614c298530a614c29853,0xb41682d05a0b41682d05a0b41682d05a0b41682d05a0b21642c8590b21642c8590b21642c8590b21642c8590b21642c8590b21642c8590b21642c8590b21642c8590b01602c0580b01602b8570ae1582b0550aa1542a855,0xd41a8350690d21a4340680d0198328630c21842f85e0ba1742e85d0ba1742e05c0b81702e05c0b81702e05c0b81702e05c0b41682d05a0b41682d05a0b41682d05a0b41682d05a0b41682d05a0b41682d05a0b41682d05a,0xf21e43c8790f21e43c0780f01e03c0780f01e03c0780ee1dc3b8770ee1dc3b0760ec1d83b0760ec1d83b0760ec1d03a0720e01bc3786e0da1b43686d0da1b43606c0d81ac3586b0d61ac3586b0d61ac3506a0d41a83506a,0x10c2184308610c2184288510a2104208310620c4188310420841082104208408811022044088110220440881100200400801002003f87f0fe1fc3f87f0fe1fc3f87f0fc1f83f07e0fc1f83e07c0f81f03d87b0f41e83d07a,0x120240480901202404788f11e23c4788e11c2384708e11a2344688d11a2344608c1182304608c1182304608c11622c4588b11622c4508a1142284508a1142284508a112224448891122244388710e21c4388710e21c43887,0x1302604c0981302604c0981302604c0981302604c0981302604c09812e25c4b89712e25c4b89712c2584b09612c2584b09612c2584b09612c2504a09312624c4989312424849092124248488911222444889112224448891,0x15a2b4568ac1582ac550aa1542a4540a614a294518a2144288510a2144288510a21442805009f13e27c4f89f13e27c4f89e13c2784f09e13c2704e09b13626c4d09a1342684d09a1342684d09a1342644c8981302604c098,0x1742e85d0ba1742e85d0ba1722e05c0b716e2dc5b8b716e2dc5b8b716e2dc5b8b716e2d45a8b41682d05a0b41682cc598b31662c4588b11602c0578af15c2b8570ae15c2b8570ae15c2b8570ae15c2b8570ae15c2b8570ae,0x192324648c9192324648c9192320640c718e318630c618c318630c618c318630c618c318630c618c318630c618a314628c418830c610c2184304600be17a2f45d8ba1742e85d0ba1742e85d0ba1742e85d0ba1742e85d0ba,0x1a4348690d21a4348690d21a4340680cf19e33c678cf19c338670ce19c338670ce19c330660cb19632c658cb19632c658cb19632c658cb19632c658cb19632c658cb19632c658cb19632c658cb196328650c9192324648c9,0x1b03606c0d81b03606b8d71ae35c6b8d71ae35c6b8d71ae35c6b8d71ae35c6b8d71ae35c6b8d71ae35c6b8d71ae35c6b8d71ae35c6b8d71ae35c6b8d71ae35c6b8d71ae35c6b8d61ac3586b0d61aa3546a0d31a6348690d2,0x1b83706e0dc1b83706e0dc1b83706e0dc1b83706e0dc1b636c6d8db1b636c6d8db1b636c6d8db1b636c6d8db1b43686d0da1b43686c8d91b23646c8d91b23646c8d91b23646c8d91b23646c8d91b23646c8d91b23646c8d9,0x1c8390720e41c8390720e41c8390720e41c8390720e41c638c718e31c638c708e11c2384700e01be37c6f8df1be37c6f8df1be37c6f8df1be37c6f8df1be37c6f8df1be37c6f8df1be37c6f8df1be3746e8dc1b83706e0dc,0x1ca394728e51ca394728e51ca394728e51ca394728e51ca394728e51ca394728e51ca394728e51ca394728e51ca394728e51ca394728e51ca394728e41c8390720e41c8390720e41c8390720e41c8390720e41c8390720e4,0x1cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61ca394728e51ca394728e51ca394728e51ca394728e5,0x1cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e6,0x1cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e6,0x1d83ac758eb1d63ac758eb1d63ac750ea1d43a8750ea1d43a4748e91d23a4748e91d23a4740e81d03a0738e71cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e6,0x214428851092124248490921241c8390620c4188290520a410821022003f87f0fd1f83f07e0fc1f83f07d8fb1f63ec7d8f91f23e47b8f71ee3d87a8f31e43c8780ef1de3b8770ee1dc3b8770ee1dc3b8768ed1da3b4760ec,0x23e47c8f91e23c4788f11e23c4708d91a2344688c9192324648c91822e45c8b91722e4588b11522a4548a1142284508a11322644c89913226448891102204408790f21e43c8790e21c4388710e21a4308610b21642c8510a,0x2744e09c1362684cc999322624c4989312624c4981302604c09812e25c4b89612c2584a89492824c49892924248490921242484909212424849092124248490921242484909212324648c91923246484909202404808f91f,0x29e53ca794e29c538a714e29c530a614b29652ca514a294528a5149292524a4148290518a314528a514a2144288510a214328650ca1943286504a09402805009f93f27e4fc9f93e27c4f89f13e27a4f09e13b2764ec9d13a,0x2de5bcb796e2dc5b8b716e2dc5b0b616b2d65acb516a2d45a8b51692d25a4b49692d05a0b39662cc594b29652ca58cb19612be578af15d2b8570ae15c2b8570ad95b2b656cad9592b2564ab9572ae554aa1532a2544a814f,0x2e05c0b81702e05c0b81702e05c0b81702e05c0b81702de5bcb796f2de5bcb796f2de5bcb796f2de5bcb796f2de5bcb796f2de5bcb796f2de5bcb796f2de5bcb796f2de5bcb796f2de5bcb796f2de5bcb796f2de5bcb796f,0x2e45c8b91722e45c8b91722e45c8b91712e25c4b89712e25c4b89712e25c4b89712e25c4b89712e25c4b89712e05c0b81702e05c0b81702e05c0b81702e05c0b81702e05c0b81702e05c0b81702e05c0b81702e05c0b8170,0x2ea5d4ba9752ea5d4ba9752ea5d4ba9752ea5d4ba9752ea5d4ba9752ea5d4ba9752ea5d4ba9752ea5d4ba9752ea5d4ba9752ea5d4ba1742e85ccb99732e65ccb99732e65ccb99732e65ccb99732e65ccb99732e65ccb9973,0x2fa5f4be97d2fa5f4be97d2fa5f4be97d2fa5f4be97d2fa5f4be97d2fa5f4be97d2fa5ecbd97a2f45e8bd17a2f45e8bd17a2f45e8bd17a2f45e8bd17a2f45e8bd17a2f45e8bd1792f25e4bc9792f25dcbb9762ec5d8ba975,0x300600c0180300600c0180300600c017f2fe5fcbf97f2fe5fcbf97f2fe5fcbf97f2fe5fcbf97f2fe5fcbf97f2fe5fcbf97f2fe5fcbf97f2fe5f8bf17d2fa5f4be97d2fa5f4be97d2fa5f4be97d2fa5f4be97d2fa5f4be97d,0x30c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318530a614c298530a614c298530a614c298530a614c298530a614c298530a614c2984308610c2184308608c1181302604c0981,0x310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e61cc398730e618c318630c618c3186,0x310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188,0x310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188,0x310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188,0x316624c4989312620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188310620c4188,0x318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c,0x318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c,0x318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c,0x318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c,0x318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c,0x318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c,0x318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c,0x31a634c698d31a634c698d318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c318630c618c,0x31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d,0x31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d,0x31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d,0x32664cc999332664cc999332664cc999332664cc9993324648c9192324648c9192324648c9191322644c8991320640c8190320640c798f31e638c718d31a634c698d31a634c698d31a634c698d31a634c698d31a634c698d,0x32c658cb19632c658cb19632c658cb19632c658cb19632c658cb19632c658cb19632c658cb19532a654ca99532a654ca99532a654ca99532a654ca994328650ca19432664cc999332664cc999332664cc999332664cc9993,0x332664cc999332664cc999332664cc999332664cc999330660cc198330660cc198330660cc19732e65ccb99732e65ccb99732e65ccb99732e65ccb99732e65ccb99732c658cb19632c658cb19632c658cb19632c658cb196,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x33e678cf19e33c678cf19e33c678ce99d33a670ce19c338670cd99b334668cd19a334668cd19a334668cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999332664cc999,0x39a724e49c6388704df9be37a6ecdc9b73686d0d89b03606bcd79af35c6b8d71ae35c6b8d71ae35c6b8d71ae3586a8d49a835069cd39a734c694d19a1342684d01a0340680d01a0340680d01a033e67ccf99f33e67ccf99f,0x3fe7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8ff1fe3fc7f8fe1fb3f27e4fc9f93f07e0f91f03e07c0f81f03da7acf51e73ce788f09e13c0770ed1d83ac754e91d13a0740e81cf39e73ce79cf39e73ce79cf39e73ce71ce,0x47e8f51ea3a4708d918a3045e8b515a2744a89511a2244288510a2143e87d0ea1d43a8750ea1d43a8750ea1d4348650c21542a8450820f41e83105a0840c8190220340480900a0140280500a01402801001ff3fe7fcff9ff,0x51ca394728d51aa314528a514a1942a82500a013f27d4f89f13d2794ee9dd3b2764ea9d538a6f4de9b536a6d4d89ad352664cc9853025e4ba95d2aa5049c93925a4949292524a4848e9192324648c9112224348490921242,0x526a4d49a93526a4d49a93526a4d49a93526a4d49a93526a4d49a93526a4d49a93526a4d49a93524a4949292524a4949292524a4949292524a4949292524a4949292522a4548a91520a4148290520a414829051ea3d47a8f,0x560ab9572ad55aab1562ac558aa954aa8550aa1532a6548a91522a2544a89512a2540a754d298530a614c29852ea5d4ba9752ea5d4ba9752ca594aa9552aa554aa9552aa554aa94528a514a294528a5149a93526a4d49a93,0x616c2d85308610c2183b0660ac09802fe5fabf17caf85eabd17a2f05dcbb575aea5d2b9d72ae35c2b856fade5b8b6d6dadb5b6b6d6dadb5b6b6d6cad95b2b656cad95b2b5d6bad159eb31652c9590b0960abb572ae559ab0,0x650ca194328650ca19432864ec999332664cc9993326648c8d91b23646c8d91b23646c8d90b21642c8590b21642c819031f63cc758eb1d63ac758e31c638c6d8db1b636c6d8cb1762ec598b31662ac5188b0e61ac318630c,0x66ccd99b334668cd19a334664cc19732c658cad9532a654ca99532a654ca99532a654ca99532a654ca99532a652ca594b29652ca594b29650ca194328650ca194328650ca194328650ca194328650ca194328650ca194328,0x680d01a0340680d01a034067ecf99f33e67ccf99f33e67ccf99f33d67acf59eb3c678cf19e33c678cf19e33c676ced9d33a674ce99d33a672ce59c338670ce19c338670ce19c338670ce19c338670ce19c338670ce19c338,0x6aed5dabb576aed5dabb576aed5dabb556aad55aab556aad55a9b516a2d45a8b516a0d3da6349690d1da3b4768cd19a334668cd19a334668cd19a2344688d11a2344688d11a1b42684d09a1342684d09a0b41680d01a0340,0x746e85d0b9d736e65cbb9672ae4dc8b9071ce39c5b8a714e29c538a714e29c538a714e29c538a714e29c4b8970ee1dc3385708e11c1b82702e01bfb7d6f8dedbcb786eadcdb9b6f6dadadb4b686ced95b1b5d6b6d6dad358,0x76eedddb3b576aed5dabb5768ecdd9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766ecdd8baf75ceb5d6bad758eadd4ba674ae91d23a4,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x76eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7,0x45e8b71562844187b0d61742784505e043f27cef89e3bb776eedddbbb776eedddbbb776eedddbbb776eedddbbb7]⟩,⟨10,#[0x7c1c0841e0681508420074190781f0501d0601c06c130641a0601705013058150340904805040040480f02c110380800c110400c01c0e03c0a0080d0300602c0a0040901c0801805008010100300000,0x2702d1089b1049a0fc400fc990f439260050ec3a25c3e2583c254940c8310c02d0d4370d02f0b8380cc360b0930b08e0ac2722c2a2342523024228282242a08c880a42809c2408c260942205c2006c16,0x2dc552c4b8150b61484214cb1108b22a8512c0af2a4ab110ae120ad2b04d13c4c2ac5012c4e124481283f1144411c4629ca823ca710c42298342903328ca50eca20e8a10c0432802f2789a27c392742e,0x36065310d7364610b460110d234cd518cd135862350ce320cb334c7330c63285f178c116cc01085d29cbf16c5c164582f8572f43f16059168571544c2f0461504b2ec512e8432e456114b4124b32b0b5,0x1e8771e4781ec7a1bc1530c03244253a4c539c6d1c8331c446384621cc75370661d8740c8e0184ed1c83137c603acec1c43d33cda1c06f0f0d91b8c91b4691a8681b06b0b86836c67198da190c224023,0x210f63e8f43ccf50fcde1a0831e8f13c07a3c85f17c38398d620c761fc812088320070058ee01092098ea3bce81b8ed0dcec11ce53547d1f0dd19c751f836390d41f8740d4eb38cd31f4730d0e218c7c,0x4b1374a12748530475324bd26491224cd2e471314651a4550f45d0e44d124311145118425164410d42d084250a4190541c7a40878411031dc74404733fcfe40087218fd34085210f83f0403e4f73ec7a,0x8fd25561578e953549545715b56959559555795d5394d4ed514ea3d5163a465505323c50d3c5123b5093f4f63952238529475053e5014f52d46525384653947d2548d1e465364d12d4ad2a4a52046d35,0x5cd7a94e5f969345f97d955766065895e565c2609517c5e25b94a5d602595dd7b5e65e5fe5c5c57292a515c2465b1619216e905695a2495b5628f2405956f59d6390a479116b599649156a90e3e57d60,0xa0da1a05949da759c59665674666789dd9b66a7a9e59865d8598d919ce719a570642676196d532689c98c9998e9958d6258861e6a98a6e9b66c64d8b9918a9c19263e6f9ad7092e5060d82985845d574,0x712ae705c06e2a76ddc76fdbe6f5b9aadc670d94a8e9d5d1b1a95b2a55b46ce9b6b5aa6b9a9a45aba4db0a42946be8fa49ac6a1a7a391ba35a6695a468d9c9fd9d9f9819f27b67d9ea028268a7d68184,0x78ab8765d8785de76de3751cd6c53c73a855d92093562aceb461a8aacab1abdd1732b5742b072dd373dd2729b1a79c9a59ba4edbca11755cd7147e4c585c8ab5b16ed85a26acaaaa9aa1b6a99b5709c5,0x8421183a0f82e0d8320a811fd815fc81a02822018260081e037f9ff7edfa7e1f97d9f5a81f77d29f7c9f3ae69ca91ea795eb791c87a1e97c5ee7b1f07bded79de6751dd75577771d676ab775eb6781df,0x8aed9b5ad48a62c8aada6fdbe6cea151acca1d7f4ba4e5aac873eca64a8bb1ac4afa21a6623b46d0b3e2076ec2b02d3b4a226f6ce882bc85ebd85abaaee1e8721a87e1d86e19862158529884a86a5e13,0xd6f58d3729c8f1dbdaeeba2378dae4b96e08bee18ba308c6deb7ee38d2e28d6238ce32706a251ecda21804be4f5aec9742cb64e8cb1ec5afedba6adcb0ec1b762a8822d88226702d889227b5e25b5628,0xc5b15da360d4b4cd2342cf334c3b03caafad7b4fd3b47d173fcef3acd70bbfb62d734bcbaefe2f88c6f19e0f7fddb75c6314c4f6bd9761d4f49d0f41cf737c4b0fc1f04caefbc838ae177add370dbf6e,0xbc6f0ba757d5b11c3706c0b01bf37cd9f66cc722bd6f4e0379c26fdca327be35dd5754c16e7d8f5fd4750d2b46d1339ce336c2b8ce1f82def77dc76ddb364d6b33cb72cc92f7e2786e131adfb73dcb17,0xc3300bff3ec4330cbeedbb378d6708be71ee077ddab69d0332c9b25c871fbcef2baeeab9b1c]⟩,⟨2,#[0x0,0x0,0x9557d55bd6ab9555d565fa7aa5550000,0x67faaeb6fd7ffeaaaeabeaaaaaaaa555,0x3ff,0x0,0x0,0x0,0x5aea0000000000000000000000000000,0x569555595555faa555555fa6faad5555,0xafffadfabfaaaaaaaaaaaaaaa9555555,0xaffff7ffffff55ffffa,0x9aaaaadaaa9555555600000000000000,0x5555fff555555ffaafffffaaabaaaaa5,0x3fffd75]⟩,⟨10,#[0x0,0x0,0x158581684e13451158491145515049114501241d0304a11c450c0140083f0fc42104360d43b0e8300bc2f0f8380dc2f0c8100700b060060b0260a423090280a82909c240a02600000000000000000000,0x1cc73214822007f14c6b1b069204521a8761c8661c06e19c601c416084040444a11c4c12c4e1345013c420dc41120651901f03c6118063188440b42206c19068130400502407020010781f0380f1745c,0x7b1e47a1d073,0x0,0x0,0x0,0x5815f4390a4a5094211e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x6759c6799163d9865d9b66996655946314c6118a62d8961d8864d92619855092760d7c509276097a4d1795e1805fd765dd755cd7450526505265c56d5ad6a5916359d66429655bd6e591635ad6a58961,0x70dc28661885e164fdc662db871dbc52d33629796ddb45293267989609875e1b26215053149521404fd3e4f5364d1314c12448d22485ae6b5b06bdaa6a51c46d4952145511314c1234b52c6819f689a1,0x8de368c6308ce328be2e741c188a2789a298a1c08962473ddb6fdbe6cdbd749d170dc251d464bd2e64d926017f749d1,0xc4710c1303c0b01c02ffba6e7ba2e6c4706bbeedbb2eebaeeabf6efbbaedbb2ebbaafbbeaf9be2e9ba2e7b9af10000000000000000000000000000000000000000000000000000000000000000000000,0xc2f0ac2708c3f0ec370cc1302c0703c02ffc6317c5b15c5313c1302c0703c02ffba6e8b9ee6beefabe6f8beefabe6f8bbeeebb6ecbaeeabdef6bd6f4bcef2c1f06c1b05c2f0ac2708c3f0ec370cc4b11,0x30fc370ec330bc270ac231abfafdbf6fc]⟩,⟨9,#[0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x35ae973ffffffffea1507ffffff0e8704e26148a03218fffffffff0f878562a3d7fc4a24ffffc1c0d200fc221007854283e1e98cc4020301c0204018200a00ffffffffffffffffff,0xffffdd071447fce9ff5e2d96bff1bffcbe5e32990ce6605024c260349a3ffffffffffee9ffb9ffffffffffffffffffffffffffffff00fffffffffffffffe130903017ffffffffe8e,0x3f1b8daf5ffac5647970fffffffffffffffffffffffffffffc602fffffffffffffffffffffffffffffffffffff408e0fa7cffffe20733c7ffffffffffd1fff5c2dd1a8cff86d6087,0xffffd69ffffffffffffffffffffffffcb0752b7fffee471ffd5edd6dffdc1ff6fb69b3ffffffffffffffffff11fffffffffffffe0bffffffffffffffffffff5f2fffe6fff8d86a7f,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffda08986c321f0e84c22170a7fbf9930280c12064883c1bffffffbe5f5ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffe9ffffffffffffffffffffffffffffffffffffffffffffffff,0x17fffffff128904e26148a0562a4e7ffffff0884032184ca603a1c07037ffff5429c3e1e0785c2c8541a1104050301c1004000040403ffffffffffffffffffffffffffffffffffff,0xffa4520381b8c3ffffffffd54a9ffffce4861a0f3fe3bffffc66321d0e7ffffffffffffffffffffffffffd9fff7b7fffffffffffffffffffffe5e2e15cac6c35a5d2c5f2c9613a6a,0xfffffffffff994c813097fffffffffffffffff9c062233dffc361a1b0d4fa7c3f9f8dc6dfffffffffff9e7ffffff980180a05827ffff49a492a944dffd1471fffffffffff984f09e,0xffffdf1fffffffffffffb95cdffffffffffffffffffffffb6bffffffffffffffffffffff24fffffffffcb7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffd95fffffffffff90c82472292c924f26ffffe371a8ec73fffffffffffffffffffffffffffffffffffffef9fffffffffffffffffffffffffffffffe10ed7891fffffffffdefff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x138983a1c717fc1c0d088404a244d260562afffffffff5228c3e1e0788440ae56ab15601038180404000141003c2e130f86fffffffffffffffffffffffffffffffffffffffffffff,0xffffd4ca5fffffffff5122fffffffffffffffffffffffffffffffffffffffffffffe2fff7e7ffffffffffffffffffffffffffffdce80ffb1185ffffba7febbfffffffff0c8605228,0xff994c8130917ffffffffffffffff86ffe1afffffffffffffffffffffffffff2f7fffffffffffffffffffffe386431986c1ffffd6674ffffffe7839fffffffffb1d8bfffffffffff,0x1cfffffffff88ffffffffffffffffffffffffffffffffffffffffffffffffffffffffe7f371f8da363e8d4f9fffffffffff187fffffffffffffff3cfffffffff830160a04fffffff,0xffffffffffffffffffffffffffffffffffff24ffffffffffffffffffffffffffffffffffffffffffffffffffffffffdde4776fffffffffffffffffffffffff7effdf7ffffffc65ff,0xfffffffffffffffffffffffffffffffe77fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffacdd7ffff99cca63309bcda6b34ffffffffffffffffff,0xfffffffffbd5e7ffffbe5eeef7fbf60f0576bede275fffffffff6db65aae16fb4dbad7ff]⟩,hom,fixedAll⟩
def cheapSig (j : Nat) := let p:=j/book.count;let x:=j % book.count;shifted book p x==511 || value (fun i => seeds (perms (Fin.ofNat 4 p) i)) (term x)==atSig book (shifted book p x)
set_option maxHeartbeats 0 in
set_option maxRecDepth 120000 in
lemma realize (j : Nat) (hj : j<4*book.count) (good : cheapSig j=true) : checkSig book j=true := by
  let p:=j/book.count;let x:=j % book.count
  have small : p<4 := by dsimp [p];apply (Nat.div_lt_iff_lt_mul (by decide +kernel)).mpr;exact hj
  let a : Fin 4 := ⟨p,small⟩
  have eq : Fin.ofNat 4 p=a := Fin.ext (Nat.mod_eq_of_lt small)
  change (shifted book p x==511 || value (fun i => seeds (perms (Fin.ofNat 4 p) i)) (term x)==atSig book (shifted book p x))=true at good
  rw [eq] at good
  have set := movedValue (fixedAll p) seedValid (seedMove a) (term x)
  change (shifted book p x==511 || (hom p).fn (value seeds (term x))==atSig book (shifted book p x))=true
  rwa [set]
end Research.FOrbit3091

namespace Research.SmallMono3091
open Research.Basis1868 Research.Dag1868 Research.Orbit1868 Research.Sym1868 Research.Frames1868
def r : List Sig := [(0xffff000000000000000000000000ffff0000ffff00000000ffff000000000000000000000000ffff0000ffff00000000ffff,0x3972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972b972),(0x3fffffff00000000000000000000ffff0000000000000000ffffffff00000000000000000000ffff0000000000000000ffffffff,0x4894489448944894489448944894489448944894489448944894489448944894489448944894489448944894489448944894489),(0x3fff00000000000000000000ffff0000000000000000ffffffff00000000000000000000ffff0000000000000000ffffffff0000,0x11229122912291229122912291229122912291229122912291229122912291229122912291229122912291229122912291229122),(0xffff0000000000000000ffff0000ffff0000000000000000ffff0000000000000000ffff0000ffff00000000,0xe9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d4e9d),(0xffffffff0000000000000000000000000000000000000000ffffffff000000000000,0x0),(0xffff0000ffff00000000ffff000000000000000000000000ffff0000ffff00000000ffff00000000000000000000,0x2854285428542854285428542854285428542854285428542854285428542854285428542854285428542854285428542854285),(0xffff0000000000000000ffff000000000000000000000000ffff0000000000000000ffff000000000000000000000000,0xb168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b168b16),(0xffffffff0000000000000000000000000000000000000000ffffffff0000000000000000000000000000,0x2c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c582c58),(0xffffffffffff000000000000000000000000000000000000ffffffffffff000000000000000000000000000000000000,0x30603060306030603060306030603060306030603060306030603060306030603060306030603060306030603060306030603060)]
def roots : List Wire := r.map (fun a => (a,.tNone))
def map0 : List (Nat × Nat) := [(0x33b9ccde6b3398cbe5b2b94c9e4b2390c7e3b1b8cc5e2b1388c3e1b0b84c1e0b0380bfdfafb7cbddeaf378bbddaeb74b9dcae370b7dbadb6cb5daad368b3d9acb64b1d8ac360afd7abb5cadd6ab358abd5aab54a9d4aa350a7d3a9b4ca5d2a9348a3d1a8b44a1d0a83409fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200,0x33b9ccde6b3398cbe5b2b94c9e4b2390c7e3b1b8cc5e2b1388c3e1b0b84c1e0b0380bfdfafb7cbddeaf378bbddaeb74b9dcae370b7dbadb6cb5daad368b3d9acb64b1d8ac360afd7abb5cadd6ab358abd5aab54a9d4aa350a7d3a9b4ca5d2a9348a3d1a8b44a1d0a83409fcfa7b3c9dcea73389bcda6b3499cca633097cba5b2c95caa532893c9a4b2491c8a43208fc7a3b1c8dc6a33188bc5a2b1489c4a231087c3a1b0c85c2a130883c1a0b0481c0a03007fbf9fafc7dbe9f2f87bbd9eaf479bc9e2f077bb9daec75ba9d2e873b99cae471b89c2e06fb79badc6db69b2d86bb59aad469b49a2d067b399acc65b2992c863b198ac461b0982c05faf97abc5dae972b85bad96ab459ac962b057ab95aac55aa952a853a994aa451a8942a04fa793a9c4da6932984ba592a9449a49229047a391a8c45a29128843a190a8441a0902803f9f8fa7c3d9e8f2783b9d8ea74399c8e270379b8da6c359a8d26833998ca6431988c2602f978ba5c2d968b2582b958aa5429948a250279389a4c259289248239188a442190882401f8f87a3c1d8e872381b8d86a34198c86230178b85a2c158a85228138984a241188842200f8783a1c0d86832180b8582a14098482210078381a0c058281208038180a04018080200),(0x140a05028140a05028140a05028140a028140a05028140a05028140a05028140a050381c0e070381c0e070381c0e070381c0e07008040201008040201008040201008040201010080402010080402010080402010080402030180c06030180c06030180c06030180c060582c160b0582c160b0582c160b0582c160b0402010080402010080402010080402010080000000000000000000000000000000000000201008040201008040201008040201008040180c06030180c06030180c06030180c060304824120904824120904824120904824120905028140a05028140a05028140a05028140a028140a05028140a05028140a05028140a050381c0e070381c0e070381c0e070381c0e07008040201008040201008040201008040201010080402010080402010080402010080402030180c06030180c06030180c06030180c060582c160b0582c160b0582c160b0582c160b0402010080402010080402010080402010080000000000000000000000000000000000000201008040201008040201008040201008040180c06030180c06030180c06030180c060304824120904824120904824120904824120905028140a05028140a05028140a05028140a028140a05028140a05028140a05028140a050,0x205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00030000205020080606000040a040100c0c00),(0x20100804020100804020100804020101008040201008040201008040201008040204020100804020100804020100804020100805028140a05028140a05028140a05028140a028140a05028140a05028140a05028140a050582c160b0582c160b0582c160b0582c160b030180c06030180c06030180c06030180c060381c0e070381c0e070381c0e070381c0e070482412090482412090482412090482412090180c06030180c06030180c06030180c060302010080402010080402010080402010080400000000000000000000000000000000000000804020100804020100804020100804020101008040201008040201008040201008040204020100804020100804020100804020100805028140a05028140a05028140a05028140a028140a05028140a05028140a05028140a050582c160b0582c160b0582c160b0582c160b030180c06030180c06030180c06030180c060381c0e070381c0e070381c0e070381c0e070482412090482412090482412090482412090180c06030180c06030180c06030180c06030201008040201008040201008040201008040000000000000000000000000000000000000080402010080402010080402010080402010100804020100804020100804020100804020,0x400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605018140400020040c03028080004008180605),(0x140a05028140a05028140a05028140a048241209048241209048241209048241209030180c06030180c06030180c06030180c060080402010080402010080402010080402010000000000000000000000000000000000000381c0e070381c0e070381c0e070381c0e070402010080402010080402010080402010080582c160b0582c160b0582c160b0582c160b0100804020100804020100804020100804020180c06030180c06030180c06030180c0603020100804020100804020100804020100804028140a05028140a05028140a05028140a0505028140a05028140a05028140a05028140a048241209048241209048241209048241209030180c06030180c06030180c06030180c060080402010080402010080402010080402010000000000000000000000000000000000000381c0e070381c0e070381c0e070381c0e070402010080402010080402010080402010080582c160b0582c160b0582c160b0582c160b0100804020100804020100804020100804020180c06030180c06030180c06030180c0603020100804020100804020100804020100804028140a05028140a05028140a05028140a0505028140a05028140a05028140a05028140a0482412090482412090482412090482412090,0x6000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c00040300404050101406000201802020280c0004030040405)]
def perm0 : List (List Nat) := [[0,1,2,3,4,5,6,7,8],[0,5,8,3,4,1,7,6,2],[3,2,1,0,4,8,7,6,5],[3,8,5,0,4,2,6,7,1]]
def hom0 (i : Fin 4) := makeH (map0.getD i.val (0,0))
def seed0 (i : Fin 4) := (perm0.getD i.val []).map (fun j => roots.getD j defW)
lemma seed0_base : seed0 0 = roots := by decide +kernel
lemma agrees0 : ∀ i : Fin 4, (seed0 i).map (moved (hom0 i)) = seed0 0 := by decide +kernel
lemma close0 (i : Fin 4) : rowsGood (hom0 i) (hom0 i) (seed0 i) := by
  have a : ∀ z : Fin 4, (seed0 z).all (fun w => decide (w.1.1 ≤ top ∧ w.1.2 ≤ top ∧ (hom0 z).fn ((hom0 z).fn w.1) = w.1)) = true := by decide +kernel
  intro w hw
  obtain ⟨a,b,e⟩ := of_decide_eq_true (List.all_eq_true.mp (a i) w hw)
  exact ⟨⟨valid1_of_le_top a,valid1_of_le_top b⟩,e⟩
def frame0 : Frame where
  seed g := seed0 (Fin.ofNat 4 g)
  H g := hom0 (Fin.ofNat 4 g)
  J g := hom0 (Fin.ofNat 4 g)
  agree g := agrees0 _
  closed g := close0 _
def table : Dag := ⟨540,⟨22,#[0x31d808c26022ff894bfe852ff9d4bee252fba14bee752fb850b66022d3814b0e852bf894afe852b9458aea642ba950ade052b7a10ace052a289ca8a1529d810a5e152979d0a5e5429289ca4a042778149360224b80892e2824689c8fe2423fa108fe6423b8908ee8423b9908de24237a108de6423794c8ca2723190c85e25217a1485e752138a083e641a385868e1519f84c66e1519b84853e060df89037e740df99031e0509f89415e340579d015e54,0x5c785971e965c7a196fe955bb9916de855b38556ce955b39d569e0159b99566e5256b8655ae1756b8595ae1556b84d59e1956785d59e1656785559e1355d8195760355d8095760155785d54e1755385954e1554f85953e1554f8514fe0653b8194ce075338194ce0551f81947e0551381944e0551381142e0550746140e944e385137e134a180d27a274838151fd1847b45d19a1446588d12d014378150cd1742f458fbe053d285ceed073b3418dce04,0x6318118c60362f8558be9562fa1589a7462699188a1862281588e84621a118550761685185a846169d185a6461695185e5361590d84d0861399183a1860e81583e7460f9518365460d94d83e4360782581e0760781981e0560781180e1960341d7de015f78257de085f78157de035f398d7ba185ef8517b6145efa117b6845ef9917b6645ed80d7b6535ed9497be425eb8557ae955eb9d579a055e681179a645e6951796825e5909786535e19c972e96,0x6db819b6e056db80dade746b341da92176a481da92066a49d9a92046a4951a96036a480da92126a4809a92726a4949a92426a2815a86826a19c9a865269fa11a7e7469f991a7e5469f90da7e4269b995a6e5268785da1e14683a11a0e4267d40d9bd0266781999e0566781199e0266342196e0165b82196e0765b81596e0465b80d96e0265780595e0965781d95e0565780d916016438058ea1863ba158e685637a558ce156318558ce85631a158ce75,0x78f825e3e0578f80de3e0278b811e2e02787815e1e1478780ddb20776c80dd9e8576085dd82167609d9d8205760855d820375fa15d7e7575a995d5e65752861d4e84753991d3e9574f9d5d2e9574b9d5d1e75743a55cfd0873fa55cfe75738815ce204738851ce254739809ce202737991cde5473341dc9603725809c7a1871a85dc6a1571980dc660271341dc4e9571394dc3e9570f94dc2e9570b9d5c2e536ffa59bfe866f3a55bce536e9811b6e07,0x8149c60526181458605251815906052418168c605a2181488604a0981281604a95812a1604a75812996046648119520466381194e0465281290a04a32811a46046818119c604651809a460263180782601a0980782201e0780781a01e0580781201e0380680e016918058c5fe6077fb815fea057f9815fe6037f9805fde087f7815fce067ef461f9d187e341df35077cd805eee197b5619eda657ad619eba657ad805e95867a6995e5d07796a4de5a63,0x83a9960e68283998a0e65283781e0de0683681a0de058378060c5978329da0ca74831a060aa6482990e0a202828a0a0a26282990a0a2818289c60a25182b9060aa418299060a22182794a08e0782381208e0382394e08e028168220520881481e0528781481a0528681461a05205814a16051858145d60526581681205204816a12052848169d205a6481499205a548149520526381594e05643814a0a0526281594a0525281590a0520181440605281,0x86480e17d0785e41e1750785ea1617a7585c98e16a09859a6216a8585a9d614a7384f82613a0984f8221359784f81a13a7684f81613e0484f80e13a0384f80612a7584981212293849a4a126828495ca12d018494061020884081e1028784081610265843a1210a848429d210e64842992106648429521060384080e10202840a0a1026284094a10e4284190a0fa0983e8220fa0683fa560f69583f9d60fe5383e94e0f69283da0a0f66283a8160ea75,0x21b27686e9921b26486ca061b27186c5c61b26186c5861b25186c5461b64186c9061b22186c4861b26086c5821b64086c9021b14086c8c21b13086d8821b22086c4821b21086c44219a75]⟩,⟨7,#[0x8102040810204081020408102040810204081020408102040810204081020408102040810204081020408101c3870e1c3870e1c3870e1c38,0x9122448912244891224489122448912244891220408102040810204081020408102040810204081020408102040810204081020408102040,0x9122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448,0x9122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448,0x9122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448912244891224489122448,0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142848912244891224489122448912244891224489122448,0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850,0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850,0xc162c58b162c58b162c58b162c58b162c58b162c58b162c50]⟩,⟨11,#[0x3c0780e81c0360680c81802a0540a0130260480881001c0340600c01802c0580a01202404809012024048090120240480901001c0300500800c000000000000000000000000000000000000000000000000000000000000,0x5c0b81702e05c0b81702e05c0b81702e05c0b81702e05c0b81702e05c0b81602804c0901202404809012024048090120240480901202404809012023044088110220420801002004007c0f81f03e07c0f81f03c0780f01e,0x15629c528a21402744d09812a2444808e116218420810fc1d0390710e21b4358670ca18c2f05c0b81702e05c0b816c2d05a0b41682d05a0b21542885109a12c238470880fc1d8390720e01b83606a0cc1802f05c0b81702e,0x1bc3786f0de1b636c6c0d81b035c6b8d31a634c698d21a433c678cd19a330660cc198330660cc198330660cc198330660cb19632c658cb19632c658cb19632c658cb19632c658cb19631c628c317e2f85f0ba1742d85a0b0,0x244488911222444889091e23a4748e11c2324648c9192304608c1182304608990f21642c8590b216428851052043fc7f8fc1f63ec7b8f71ee3dc7b0f31e03b4768ec1d83ac738e41c2384708e01be3786f0de1bc3786f0de,0x36c6d8d89af34867cc9990320640c718a310618c11813005fcbf17a2f45e8bc9792f25dcbb9772ea5d0ba1722e05b8b716c2d6598b095e2a0524a113d2724e49c9372684cc999302604c09692d2544a89512724e49491922,0x55eab9572ab552a9d52aa3542a754ea9d53aa694b294522a3d45a86508a01372654be9752ca584ac9592925048690d21a434849091f23d4788d5182304508990da1541c819021fa3e47c8f19dc3b676ce59c9380700dd1b7,0x7e6f6decbd67a2f35e4bc8790f1de33c677eef1dd3b3766ebdd43a8742e7dcc395728e49c6b8d712e19c137b6eedcdb736a6b0d49a6b3b66acc59632263cc698a310612bdd78aed5d8ba16ead85a2b15612bc572ad15a2b3,0x59baa154299d2ba273fe7fcfc9d934668caf9352163d4738e715a2844788f11e0dc0680d011fcbf5]⟩,⟨12,#[0x4c06005c05805405004c04a03803e04a04203804804404003c03803703403403002c02b02c02402802402002001d01501b01d01c01801401c01801401c01801401000300b01000c00300000b00b00c00c00c008004000008004000008004000,0xc80b80c40c00bc0bb0b80a005705403e03d0b80b40b00ac0940810500a80a00ac0a809c03a0a40810980900a009c09809004c09409003c08c03e08408007c05008407806c06008807406805c08408007c07006405807807407006c068064054,0x420ad0f40e80850480f80f00e40440850510ec0e007d0400f40f00ec0dc0a40e80e40e00dc0cc0930c806f04f0a809f0c009f09c0bc0670640950940b809006f0d80b406f04a0950d40c40cc0bb0600d00c80b405c0570c00a80d00bc0580cc,0x581281160e70fb1281240f90f31201180ea0e90f60e90a61200aa0a908607a11c1181141041180ce0cd1140c90620830ae05211010910410c1040e90db10c0f50db0780841080b70601040cd0961000fc0f80d80880850840ad07c0fc0d0067,0x18818717318418017c16b0d60d517812e12d17417016c16816315b12016416015f15c15815415014c14c14814814414414114014008813811c0e10ff13812a10c0ea0dd13c0ea08b0741380ff0ed07007c13413012c11610813005f05c12c0d3,0x1ec1e81e41e01dc1d01d81d41d01cc1b81cc1c81b41c41b01c01ac1bc1a81a81cc1c81c41c01bc1b81b41b01ac1a81941931901a41a31a019f19c19b1981741531500b20b108f08c17813613511f11c11311019418b18818318016f16c19018c,0x28c28828428027c1a827827421020427026c26826426025c22025825425024c24824424023c23823423022c22822421c20c22222021e21c21a21821621421221020e20c2082041a81fc1e42001f81f01e01f41e82001dc1fc1f81f41d41ec1f0,0x3002fc2f829c2592142f42f02ec2dc2bc2a42982972e82e42df2dc2b82af2ac29729423b23822322020b2082e02dc2d82d42b429021c1d82d02cc2c82c42c02bc2b82b42af2a427925c2342121ef1cd2b02ac2a82a42a029c29829429023020e,0x36436035c20b35835435034c34834434033c33833433032c3243102f42df2cc25422c21e30c25032831c3143082f02d82c824c23b2282163243183042d42a92483213002ec2e82c42a021a32031c3182e42c024422421831424031030c308304,0x3e83e43e03dc3d83d43d03cc3c83c43c03bc3b838d3112db2541f33b43b03ac3a83882f52d729222c3a43a039c39839439038c3881fd1e41d51d038538138038438037d37837c3783743243213202e02a92a827927825925822322237036c368,0x42c3b02ce2bd4284243ac42041c4183a82aa41241441040e38c20440c40838835535340434135b34734f34d35934b4003fc3f83f43f13a139c3973963953943e93c83c13c03243dd3bc3f03a53963903ec3b93b02cd2b63d53ac3b43a93a82e2,0x46446246043c41530b3091fb1f945e45c45a4583923904544482a62a54444414403b432645044c44142842040c31229e24b2281fe4302f62f529a29944841c31b2ed2a22241ea44444043c43842c4244183072f12562321e640822e22c434430,0x3012442031f51dc4b44b04a845c3f239c4ac4463172404a94a84594583984a44a049c46644f43a3d032b2fd23c4984944623cc49048c43c3c448844242341a3c02584844464263bc48047c47842e3b82cb23447647447247046e46c46a468466,0x4724504343e42f94db4c84763e04c446a42b3dc4d74bc46c3d832b4ac4874683d44db4d84d74d44a34a049b49849349048748447c45024f24c1e31e04d04b445a4593a73a44d04b04a945e3a04cc4c84c44c04bc4b849c49448c48847841131f,0x26c45433d32d33526852752451f51c51351045452852051850c5245204f83ff36b33126451c5185144f440336f33927026051050c4f03fb36733d27048b41c3234e050550450850450027b25d4fc4f84f44f04ec4e94e84e44e04dd4dc4cc4a4,0x57c57857457056c5685644b34b24b14b04c34b856055c55855455355054f54c53c53853353050b5084824814374343ef3ec2b22b12772745485445402d22d153c47a4792c22c14544482c62c55395385025005344ad4c753052c5284fc3f7363,0x66065c65865465064c64864464063c63863463062c62862462061c61861461060c6086046005fc5f85f45f05ec5e85e45e05dc5c35ae5695d85d45d05cc5c85c45c05bc5b85b45b05ac5a85a45a059c59859559056956459459058c588584580,0x6e46e06de6dc65b6596d86d46d06cc62b5a159c6c96c86c46c16c06bc6b96b86b56b46b16b06ad6ac6a86a56a46a16a069d69c69969864d64c6236225bf5be6956945d55d459959869169068c68968868568468168067c67867467066c668664,0x73c73873472771a6fd6b66a469c6946866476315ec5d35c55b073072c72872472071c71871471070c7087046f06a064e64362d60e5e85d65b67047027006fe6fc6fa6f86f66f46f26f069a69865f65d5e25e05de5dc5aa5a86ee6ec6ea6e86e6,0x5fc7d066b5f87cc7c87c47c07bc7b87b47b07ac7a87a478c6db6676555f47a17a079c79879579479179078d78c7887847477467287097086f56f46be6a867e61f61e5f15f05da78077c77877477076c76876476075c75875475074c748744740,0x71c7037006cb6c863e63d63b6385ce5cd5cb5c87da7d975b75872e72d6376347f87f47f07ec7e87e47e079779473e73d7307137106b36b06166156126116036005ba5b97e07dc7d87d47d27b979077b77174272c70c6f86d56ba6ac67365161a,0x84384284184083f83e83d83c83983883583483383283183082f82e82d82c82a82882682482282081c81881781681581481381281181080f80e80d80c80b80a8098088078068058048007ff7fc7ed7e87d77d47a37a076676576376075f75c71f,0x86886586486186085d85c85b85a85985885785685585485385285185084f84e84d84c84a848846844]⟩⟩
def cover (i : Nat) := Research.TinyOrbit3091.check table frame0 i
end Research.SmallMono3091
namespace Research.Cost3091

abbrev Rank := Research.Cuts1868.excluded 11 Research.PinRows3091.canonicalInputs
end Research.Cost3091
namespace Research.CostMetric3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Research.Basis1868 Research.Free1868 Research.PinRows3091

def budgetWitness (w : List Sig) (z : Sig) (v : Bool) : Prop :=
    (∃ a ∈ w, proper a ∧ z = neg a) ∨
    (v = true ∧ ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

lemma pullBudget {v : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ budgetWitness w z v) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' + t ≤ k + t' + v.toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨hv,d, a, b, ha, hb, pa, pb, hab, eq⟩)
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
        exact ⟨k+1, t+1, _, by omega, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
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
        exact ⟨k+1, t, _, by simp [hv]; omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
end Research.CostMetric3091
namespace Research.CostMetric3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Research.Basis1868 Research.Free1868 Research.PinRows3091 Research.Cuts1868
def novel (w : List Sig) (g : Gate) := !(w.map can).contains (can (gv w g))
def novelCost : List Gate → List Sig → Nat
| [], _ => 0
| g::gs,w => (novel w g).toNat + novelCost gs (w++[gv w g])
lemma newBudget {w : List Sig} (hw : ∀ a∈w,Valid a) (g : Gate) (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ budgetWitness w (gv w g) (novel w g) := by
  by_cases pc : novel w g = true
  · simpa [budgetWitness,pc,witness] using gate_rep hw g h
  have hm : can (gv w g) ∈ w.map can := by
    simpa [novel] using pc
  obtain ⟨a,ha,e⟩ := List.mem_map.mp hm
  rcases sameClass e.symm with eq|eq
  · exact Or.inl (Or.inl (eq ▸ ha))
  · rcases operand_cases (hw a ha) (Or.inl ha : represented w a) with az|ao|⟨_,ap⟩
    · exact Or.inl (Or.inr (by rw [eq,az,neg_laws.1]; exact fun h => h.2.2 rfl))
    · exact Or.inl (Or.inr (by rw [eq,ao,neg_laws.2]; exact fun h => h.2.1 rfl))
    · exact Or.inr (Or.inl ⟨a,ha,ap,eq⟩)
lemma extractNew (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ t+novelCost gs w ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp [novelCost], Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pullBudget ht (newBudget hw g (legal g (by simp))) hs
    exact ⟨l, u, T, by simp only [novelCost]; cases he : novel w g <;> simp [he] at hl ⊢ <;> omega, hu, hT⟩
theorem novelScore (checked : excluded 11 canonicalInputs) (C : Circuit) (fan : FanInTwo C)
    (agree : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) = edgeF x) :
    12 ≤ novelCost C.gates (sliceRaw++[one]) := by
  let v := sliceRaw++[one]
  let w := execute C.gates v
  have val : ∀ a∈v, Valid a := by
    intro a h
    rcases List.mem_append.mp h with ha|ha
    · exact slice_raw_valid _ ha
    · exact List.mem_singleton.mp ha ▸ valid_one
  have hwv : ∀ a∈w, Valid a := execute_valid C.gates v val
  have hp (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero)=s := by
    rw [← b_read]
    change ((execute C.gates v).map _).getD C.output false = s
    rw [execute_bits _ _ _ _ val (fun g hg => (fan g hg).1)]
    have ev := agree (slice_sample s i)
    rw [pinnedOn, slice_sample_ok,slice_sample_list] at ev
    change C.eval (v.map (bit s i)) = s
    simpa [v,List.map_append,bit_one] using ev
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro j
      rw [target,testBit_top]
      by_cases hi : j < 414
      · simpa [bit,hi] using hp true ⟨j,hi⟩
      · rw [hvout.1 j (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro j
      by_cases hi : j < 414
      · simpa [bit,target] using hp false ⟨j,hi⟩
      · rw [hvout.2 j (by omega)]; exact (Nat.zero_testBit j).symm
  have rep := get_rep w C.output
  rw [et] at rep

  obtain ⟨k,t,S,bound,live,sub⟩ := extractNew C.gates v val fan
    (rep.resolve_right (fun hn => hn target_proper))
  have raw : ∀ a ∈ S, a ∈ sliceRaw := by
    intro a ha
    rcases List.mem_append.mp (sub _ ha) with h|h
    · exact h
    · exact ((live_proper live a ha).2.2 (List.mem_singleton.mp h)).elim
  obtain ⟨j,T,cost,program,small⟩ := compress live
  have inclusion : T ⊆ canonicalInputs.toFinset := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (small hz)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,raw a ha,rfl⟩)
  rw [canonical_needed program inclusion] at program
  by_contra! low
  change k ≤ t+novelCost C.gates (sliceRaw++[one]) at bound
  exact checked j (by omega) program
end Research.CostMetric3091
namespace Research.CostMetric3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Research.Cost3091
open Research.Basis1868

def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false
lemma isNot_iff {g : Gate} : isNot g=true ↔ g.op=.not := by cases g with | mk op ins => cases op <;> simp [isNot]
end Research.CostMetric3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Research.Basis1868
open Research.CostMetric3091
namespace Research.NegPin3091

def run (gs : List Gate) (w : List Bool) := gs.foldl (fun u (g : Gate) => u ++ [g.op.eval (g.inputs.map (fun i => u.getD i false))]) w
lemma run_snoc {gs : List Gate} (w : List Bool) : ∃ tail, run gs w = w ++ tail := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map (fun i => w.getD i false))
    obtain ⟨t,ht⟩ := ih (w++[b])
    exact ⟨b::t,ht.trans (by simp)⟩
lemma offOutput {C : Circuit} (agree : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x++[x 0 || x 3])=edgeF x) : C.output ≠ 9 := by
  intro ho
  let x := fun i : Fin 9 => i == 0
  let w := List.ofFn x ++ [x 0 || x 3]
  have hx := agree x
  change (run C.gates w).getD C.output false = edgeF x at hx
  obtain ⟨t,ht⟩ := run_snoc (gs := C.gates) w
  rw [ho,ht,List.getD_append _ _ _ _ (show 9 < w.length by simp [w])] at hx
  have yes : w.getD 9 false = true := by decide +kernel
  have no : edgeF x = false := by decide +kernel
  rw [yes,no] at hx
  contradiction

abbrev legal (g : Gate) := g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
end Research.NegPin3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Research.Basis1868 Research.Free1868 Research.CostMetric3091 Research.PinRows3091
namespace Research.Rigidity3091
abbrev Cst (a : Sig) := a=zero ∨ a=one
abbrev Seen (w : List Sig) (a : Sig) := can a ∈ w.map can
lemma seenConst {w} (h : one∈w) {a} (hc : Cst a) : Seen w a := by
  have cv := List.mem_map_of_mem (f := can) h
  rcases hc with rfl|rfl
  · simpa only [Seen,can_zero,can_one] using cv
  · exact cv
lemma seenGet {w : List Sig} (h : one∈w) (i : Nat) : Seen w (w.getD i zero) := by
  by_cases hi : i<w.length
  · rw [List.getD_eq_getElem _ _ hi];exact List.mem_map_of_mem (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)];exact seenConst h (Or.inl rfl)
lemma seenBin {w : List Sig} (valid : ∀ a∈w,Valid a) (h : one∈w) (d : Bool) (i j : Nat)
    (c : Cst (w.getD i zero) ∨ Cst (w.getD j zero)) : Seen w (bin d (w.getD i zero) (w.getD j zero)) := by
  have aux (a b : Sig) (ha : Valid a) (sa : Seen w a) (z : Cst b) : Seen w (bin d a b) := by
    obtain ⟨e1,e2,e3,e4,_,_⟩ := bin_laws ha
    rcases z with rfl|rfl <;> cases d <;> first | rwa [e1] | rwa [e2] | rw [e3];exact seenConst h (Or.inl rfl) | rw [e4];exact seenConst h (Or.inr rfl)
  rcases c with c|c
  · rw [bin_comm];exact aux _ _ (valid_getD valid j) (seenGet h j) c
  · exact aux _ _ (valid_getD valid i) (seenGet h i) c
lemma noNovelNot {w : List Sig} (valid : ∀ a∈w,Valid a) (h : one∈w) {g : Gate} (op : g.op=.not) : novel w g=false := by
  have seen : Seen w (gv w g) := by
    obtain ⟨o,ins⟩ := g; change o=.not at op; subst o
    cases ins with
    | nil => exact seenConst h (Or.inr neg_laws.1)
    | cons i l =>
      change can (neg (w.getD i zero)) ∈ w.map can
      rw [can_neg (valid_getD valid i)];exact seenGet h i
  simpa [novel,Seen] using seen
def gateVal (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map (fun i => w.getD i false))
lemma changed {w : List Sig} {u v : List Bool} (g : Gate) (fan : g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2)
    (valid : ∀ a∈w,Valid a) (oneIn : one∈w) (rel : ∀ i, u.getD i false≠v.getD i false → Cst (w.getD i zero))
    (nov : novel w g=false → isNot g=true)
    (diff : gateVal g u≠gateVal g v) : Cst (gv w g) := by
  have noCopy (seen : Seen w (gv w g)) (op : isNot g=false) : False := by
    have ne : novel w g=false := by simpa [novel,Seen] using seen
    rw [op] at nov
    exact Bool.false_ne_true (nov ne)
  obtain ⟨op,xs⟩ := g
  rcases fan with ⟨hop,hlen⟩
  rcases (show op=GateOp.and ∨ op=.or ∨ op=.not from hop) with rfl|rfl|rfl
  all_goals cases xs with
    | nil => exact (diff rfl).elim
    | cons i xs => ?_
  · cases xs with
    | nil => exact (noCopy (by simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws (valid_getD valid i)).1] using seenGet oneIn i) rfl).elim
    | cons j xs =>
      obtain rfl : xs=[] := List.length_eq_zero_iff.mp (by change (i::j::xs).length≤2 at hlen; simp only [List.length_cons] at hlen; omega)
      have hs : u.getD i false≠v.getD i false ∨ u.getD j false≠v.getD j false := by by_contra! h;exact diff (show GateOp.and.eval [u.getD i false,u.getD j false] = GateOp.and.eval [v.getD i false,v.getD j false] by rw [h.1,h.2])
      exact (noCopy (by simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws (valid_getD valid j)).1] using seenBin valid oneIn false i j (hs.imp (rel i) (rel j))) rfl).elim
  · cases xs with
    | nil => exact (noCopy (by simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws (valid_getD valid i)).2.1] using seenGet oneIn i) rfl).elim
    | cons j xs =>
      obtain rfl : xs=[] := List.length_eq_zero_iff.mp (by change (i::j::xs).length≤2 at hlen; simp only [List.length_cons] at hlen; omega)
      have hs : u.getD i false≠v.getD i false ∨ u.getD j false≠v.getD j false := by by_contra! h;exact diff (show GateOp.or.eval [u.getD i false,u.getD j false] = GateOp.or.eval [v.getD i false,v.getD j false] by rw [h.1,h.2])
      exact (noCopy (by simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws (valid_getD valid j)).2.1] using seenBin valid oneIn true i j (hs.imp (rel i) (rel j))) rfl).elim
  · have di : u.getD i false≠v.getD i false := by intro eq;exact diff (congrArg Bool.not eq)
    change Cst (neg (w.getD i zero))
    rcases rel i di with e|e
    · right;rw [e,neg_laws.1]
    · left;rw [e,neg_laws.2]
end Research.Rigidity3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Research.Basis1868 Research.PinRows3091 Research.CostMetric3091
namespace Research.Rigidity3091
lemma finalTarget (C : Circuit) (fan : FanInTwo C)
    (agree : ∀ x : Fin 9 → Bool,C.eval (List.ofFn x++[x 0 || x 3])=edgeF x) :
    (execute C.gates (sliceRaw++[one])).getD C.output zero=target := by
  let v := sliceRaw++[one]
  let w := execute C.gates v
  have val : ∀ a∈v, Valid a := by
    intro a h
    rcases List.mem_append.mp h with ha|ha
    · exact slice_raw_valid _ ha
    · exact List.mem_singleton.mp ha ▸ valid_one
  have hwv : ∀ a∈w, Valid a := execute_valid C.gates v val
  have hp (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero)=s := by
    rw [← b_read]
    change ((execute C.gates v).map _).getD C.output false = s
    rw [execute_bits _ _ _ _ val (fun g hg => (fan g hg).1)]
    have ev := agree (slice_sample s i)
    rw [pinnedOn, slice_sample_ok,slice_sample_list] at ev
    change C.eval (v.map (bit s i)) = s
    simpa [v,List.map_append,bit_one] using ev
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro j
      rw [target,testBit_top]
      by_cases hi : j < 414
      · simpa [bit,hi] using hp true ⟨j,hi⟩
      · rw [hvout.1 j (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro j
      by_cases hi : j < 414
      · simpa [bit,target] using hp false ⟨j,hi⟩
      · rw [hvout.2 j (by omega)]; exact (Nat.zero_testBit j).symm
  exact et
end Research.Rigidity3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Research.Basis1868 Research.PinRows3091 Research.CostMetric3091
namespace Research.Rigidity3091
structure Record where
  gate : Gate
  before : List Sig
def trace : List Gate → List Sig → List Record
  | [], _ => []
  | g::gs,w => ⟨g,w⟩ :: trace gs (w++[gv w g])
def extra (r : Record) := !(isNot r.gate) && !(novel r.before r.gate)
def starts (r : Record) := ∃ u v : List Bool, u.length=r.before.length ∧ v.length=r.before.length ∧
  (∀ i,u.getD i false ≠ v.getD i false → Cst (r.before.getD i zero)) ∧
  gateVal r.gate u ≠ gateVal r.gate v ∧ ¬Cst (gv r.before r.gate)
lemma traceData (gs : List Gate) (w : List Sig) (valid : ∀ a∈w,Valid a) (oneIn : one∈w)
    (fan : ∀ g∈gs,Research.NegPin3091.legal g) : ∀ r∈trace gs w,
    (∀ a∈r.before,Valid a) ∧ one∈r.before ∧ Research.NegPin3091.legal r.gate := by
  induction gs generalizing w with
  | nil => simp [trace]
  | cons g gs ih =>
    intro r mem
    rcases List.mem_cons.mp mem with rfl|h
    · exact ⟨valid,oneIn,fan g (by simp)⟩
    · apply ih _ _ (List.mem_append_left _ oneIn) (fun a ha => fan a (List.mem_cons_of_mem _ ha)) r h
      intro a ha;rcases List.mem_append.mp ha with hm|hm
      · exact valid a hm
      · exact List.mem_singleton.mp hm ▸ gv_valid valid g
lemma startsExtra {r : Record} (val : ∀ a∈r.before,Valid a) (oneIn : one∈r.before) (fan : Research.NegPin3091.legal r.gate)
    (s : starts r) : extra r=true := by
  obtain ⟨u,v,_,_,rel,di,nc⟩ := s
  have contra := fun (h : novel r.before r.gate=false → isNot r.gate=true) => nc (changed r.gate fan val oneIn rel h di)
  cases a : isNot r.gate <;> cases b : novel r.before r.gate <;> simp [extra,a,b] at *
lemma extraCount (gs : List Gate) (w : List Sig) (valid : ∀ a∈w,Valid a) (oneIn : one∈w) :
    (trace gs w).countP extra + gs.countP isNot + novelCost gs w = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have valid' : ∀ a∈w++[gv w g],Valid a := by
      intro a ha;rcases List.mem_append.mp ha with ha|ha
      · exact valid a ha
      · exact List.mem_singleton.mp ha ▸ gv_valid valid g
    have old := ih _ valid' (List.mem_append_left _ oneIn)
    have avoid := fun (h : isNot g=true) => noNovelNot valid oneIn (isNot_iff.mp h)
    simp only [trace,List.countP_cons,novelCost,List.length_cons]
    cases a : isNot g <;> cases b : novel w g <;> simp [extra,a,b] at * <;> omega
lemma oneRecord {q : List Record} {r s : Record} (b : q.countP extra ≤ 1) (rmem : r∈q) (smem : s∈q) (rflag : extra r=true) (sflag : extra s=true) : r=s := by
  have len : (q.filter extra).length≤1 := by rwa [←List.countP_eq_length_filter]
  have r' := List.mem_filter.mpr ⟨rmem,rflag⟩
  have s' := List.mem_filter.mpr ⟨smem,sflag⟩
  cases h : q.filter extra with
  | nil => simp [h] at r'
  | cons a l =>
    have e : l=[] := List.length_eq_zero_iff.mp (by rw [h,List.length_cons] at len;omega)
    rw [e] at h
    simpa [h] using (List.mem_singleton.mp (h ▸ r')).trans (List.mem_singleton.mp (h ▸ s')).symm
lemma noStart {gs : List Gate} {w : List Sig} {u v : List Bool}
    (legal : ∀ g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2)
    (valid : ∀ a∈w,Valid a) (oneIn : one∈w)
    (absent : ∀ r∈trace gs w,¬starts r)
    (uw : u.length = w.length) (vw : v.length = w.length)
    (rel : ∀ i, u.getD i false≠v.getD i false → Cst (w.getD i zero)) :
    ∀ i, (Research.NegPin3091.run gs u).getD i false≠(Research.NegPin3091.run gs v).getD i false → Cst ((execute gs w).getD i zero) := by
  induction gs generalizing w u v with
  | nil => exact rel
  | cons g gs ih =>
    let w' := w++[gv w g]
    have valid' : ∀ a∈w',Valid a := by
      intro a ha;rcases List.mem_append.mp ha with ha|ha
      · exact valid a ha
      · exact List.mem_singleton.mp ha ▸ gv_valid valid g
    have oneIn' : one∈w' := List.mem_append_left _ oneIn
    have hd := absent ⟨g,w⟩ (List.mem_cons_self ..)
    have tl (r) (hr : r∈trace gs w') : ¬starts r := absent r (List.mem_cons_of_mem _ hr)
    let u' := u++[gateVal g u]
    let v' := v++[gateVal g v]
    change ∀ i, (Research.NegPin3091.run gs u').getD i false≠(Research.NegPin3091.run gs v').getD i false → Cst ((execute gs w').getD i zero)
    apply ih (fun a ha => legal a (List.mem_cons_of_mem _ ha)) valid' oneIn' tl (by simp [u',w',uw]) (by simp [v',w',vw])
    intro i dif
    by_cases low : i<w.length
    · dsimp only [u',v'] at dif
      rw [List.getD_append _ _ _ _ (show i<u.length by omega),List.getD_append _ _ _ _ (show i<v.length by omega)] at dif
      change Cst ((w++[_]).getD i zero);rw [List.getD_append _ _ _ _ low];exact rel i dif
    · by_cases eq : i=w.length
      · have h1 : u'.getD i false=gateVal g u := by change (u++[_]).getD i false=_;rw [show i=u.length by omega];simp [List.getD]
        have h2 : v'.getD i false=gateVal g v := by change (v++[_]).getD i false=_;rw [show i=v.length by omega];simp [List.getD]
        rw [h1,h2] at dif
        have hh : w'.getD i zero=gv w g := by rw [eq];simp [w',List.getD]
        rw [hh];by_contra nc;exact hd ⟨u,v,uw,vw,rel,dif,nc⟩
      · rw [List.getD_eq_default _ _ (by simp [u'];omega),List.getD_eq_default _ _ (by simp [v'];omega)] at dif
        contradiction
theorem gateway {C : Circuit} (fan : FanInTwo C)
    (agree : ∀ x : Fin 9 → Bool,C.eval (List.ofFn x++[x 0 || x 3])=edgeF x)
    (different : ∀ j : Fin 9,∃ x : Fin 9 → Bool,C.eval (List.ofFn x++[x j]) ≠ edgeF x) :
    ∃ r∈trace C.gates (sliceRaw++[one]),starts r := by
  let w := sliceRaw++[one]
  have valid : ∀ a∈w, Valid a := by
    intro a ha;rcases List.mem_append.mp ha with ha|ha
    · exact slice_raw_valid a ha
    · exact List.mem_singleton.mp ha ▸ valid_one
  have oneIn : one∈w := by simp [w]
  by_contra! hn
  obtain ⟨x,wrong⟩ := different 0
  let u := List.ofFn x++[x 0]
  let v := List.ofFn x++[x 0 || x 3]
  have differentOut : (Research.NegPin3091.run C.gates u).getD C.output false≠(Research.NegPin3091.run C.gates v).getD C.output false := fun e => wrong (e.trans (agree x))
  have prior : ∀ i,u.getD i false≠v.getD i false → Cst (w.getD i zero) := by
    intro i dif
    by_cases low : i<9
    · exact False.elim (dif (by change (List.ofFn x++[_]).getD i false=(List.ofFn x++[_]).getD i false; rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]))
    · by_cases eq : i=9
      · subst i;exact Or.inr rfl
      · rw [List.getD_eq_default _ _ (by simp [u];omega),List.getD_eq_default _ _ (by simp [v];omega)] at dif
        contradiction
  have fin := noStart fan valid oneIn hn (by simp [u,w];rfl) (by simp [v,w];rfl) prior C.output differentOut
  change Cst ((execute C.gates (sliceRaw++[one])).getD C.output zero) at fin
  rw [finalTarget C fan agree] at fin
  exact fin.elim target_proper.2.1 target_proper.2.2

end Research.Rigidity3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Research.Basis1868 Research.PinRows3091 Research.CostMetric3091
namespace Research.Rigidity3091
def boolOp (d : Bool) : GateOp := if d then .or else .and
lemma gvTwo (w : List Sig) (val : ∀ a∈w,Valid a) (d : Bool) (i j : Nat) :
    gv w ⟨boolOp d,[i,j]⟩=bin d (w.getD i zero) (w.getD j zero) := by
  cases d <;> simp only [boolOp,gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,ite_false,ite_true,Bool.false_eq_true,(bin_laws (valid_getD val j)).1,(bin_laws (valid_getD val j)).2.1]
lemma gvOne (w : List Sig) (val : ∀ a∈w,Valid a) (d : Bool) (i : Nat) :
    gv w ⟨boolOp d,[i]⟩=w.getD i zero := by
  cases d <;> simp only [boolOp,gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,ite_false,ite_true,Bool.false_eq_true,(bin_laws (valid_getD val i)).1,(bin_laws (valid_getD val i)).2.1]
lemma binCst (d : Bool) {a b : Sig} (ca : Cst a) (cb : Cst b) : Cst (bin d a b) := by
  rcases ca with rfl|rfl <;> rcases cb with rfl|rfl <;> cases d <;> first | exact Or.inl (by decide +kernel) | exact Or.inr (by decide +kernel)
lemma seenNotFresh {w : List Sig} {g : Gate} (s : Seen w (gv w g)) : novel w g≠true := by simpa [novel,Seen] using s
abbrev useful (r : Record) := novel r.before r.gate=true ∨ starts r
abbrev pairShape (w : List Sig) (g : Gate) (i j : Nat) := i≠j ∧ i<w.length ∧ j<w.length ∧
  ¬(Cst (w.getD i zero) ∧ Cst (w.getD j zero)) ∧
  (novel w g=true → ¬Cst (w.getD i zero) ∧ ¬Cst (w.getD j zero))
lemma pairGood (w : List Sig) (val : ∀ a∈w,Valid a) (oneIn : one∈w) (d : Bool) (i j : Nat)
    (h : useful ⟨⟨boolOp d,[i,j]⟩,w⟩) : pairShape w ⟨boolOp d,[i,j]⟩ i j := by
  let g : Gate := ⟨boolOp d,[i,j]⟩
  have seenIf (c : Cst (w.getD i zero) ∨ Cst (w.getD j zero)) : Seen w (gv w g) := by
    rw [gvTwo w val d i j];exact seenBin val oneIn d i j c
  have snd (n : novel w g=true) : ¬Cst (w.getD i zero) ∧ ¬Cst (w.getD j zero) :=
    ⟨fun ci => seenNotFresh (seenIf (Or.inl ci)) n,fun cj => seenNotFresh (seenIf (Or.inr cj)) n⟩
  have out (a : Nat) (hi : ¬a<w.length) : Cst (w.getD a zero) := Or.inl (List.getD_eq_default _ _ (by omega))
  rcases h with yes|s
  · have nc := snd yes
    refine ⟨?_,by_contra fun hi => nc.1 (out i (by simpa using hi)),by_contra fun hj => nc.2 (out j (by simpa using hj)),fun c => nc.1 c.1,snd⟩
    intro e;subst j
    apply seenNotFresh (g := ⟨boolOp d,[i,i]⟩) _ yes
    rw [gvTwo w val d i i]
    cases d <;> first | rw [(bin_laws (valid_getD val i)).2.2.2.2.1];exact seenGet oneIn i | rw [(bin_laws (valid_getD val i)).2.2.2.2.2];exact seenGet oneIn i
  · obtain ⟨u,v,uw,vw,rel,di,nc⟩ := s
    change u.length=w.length at uw
    change v.length=w.length at vw
    have ch : u.getD i false≠v.getD i false ∨ u.getD j false≠v.getD j false := by
      by_contra! h';exact di (show (boolOp d).eval [u.getD i false,u.getD j false]=(boolOp d).eval [v.getD i false,v.getD j false] by rw [h'.1,h'.2])
    have z : ¬(Cst (w.getD i zero) ∧ Cst (w.getD j zero)) := fun c => nc ((gvTwo w val d i j).symm ▸ binCst d c.1 c.2)
    have within (a : Nat) (hh : u.getD a false≠v.getD a false) : a<w.length := by
      by_contra bad;exact hh (by rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)])
    refine ⟨?_,?_,?_,z,snd⟩
    · intro e;subst j;exact ch.elim (fun h => z ⟨rel i h,rel i h⟩) (fun h => z ⟨rel i h,rel i h⟩)
    · by_contra bad;have hj := ch.resolve_left (fun hh => bad (within i hh));exact z ⟨out i bad,rel j hj⟩
    · by_contra bad;have hi := ch.resolve_right (fun hh => bad (within j hh));exact z ⟨rel i hi,out j bad⟩
lemma shapeOf {w : List Sig} (val : ∀ a∈w,Valid a) (oneIn : one∈w) {g : Gate} (fan : Research.NegPin3091.legal g)
    (hn : isNot g=false) (hu : useful ⟨g,w⟩) : ∃ i j,g.inputs=[i,j] ∧ pairShape w g i j := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨d,rfl⟩ : ∃ d : Bool, op=boolOp d := by
    rcases fan.1 with h|h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
    · have e : op=.not := h; subst op;contradiction
  cases ins with
  | nil =>
    rcases hu with nov|⟨u,v,_,_,_,di,_⟩
    · apply False.elim (seenNotFresh _ nov);cases d <;> first | exact seenConst oneIn (Or.inl rfl) | exact seenConst oneIn (Or.inr rfl)
    · exact (di rfl).elim
  | cons i ins =>
    cases ins with
    | nil =>
      rcases hu with nov|⟨u,v,_,_,rel,di,nc⟩
      · apply False.elim (seenNotFresh _ nov);rw [gvOne w val d i];exact seenGet oneIn i
      · have h : u.getD i false≠v.getD i false := fun e => di (show (boolOp d).eval [u.getD i false]=(boolOp d).eval [v.getD i false] by rw [e])
        exact (nc ((gvOne w val d i).symm ▸ rel i h)).elim
    | cons j ins =>
      obtain rfl : ins=[] := List.length_eq_zero_iff.mp (by have l := fan.2; change (i::j::ins).length≤2 at l;simp only [List.length_cons] at l;omega)
      exact ⟨i,j,rfl,pairGood w val oneIn d i j hu⟩
end Research.Rigidity3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Research.Basis1868 Research.CostMetric3091
namespace Research.NegPin3091
def typed (n : Bool) (w : List Sig) (z : Sig) : Prop :=
  (n=true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (n=false ∧ ∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
lemma binaryRep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ typed false w (bin d a b) := by
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
  exact Or.inr (Or.inr ⟨rfl, d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
lemma gateRep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ typed (isNot g) w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ typed true w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨rfl, a, hm, hp, rfl⟩)
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
      · simpa only [isNot,gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := typed false w (w.getD i zero)) (get_rep w i)
      · simpa only [isNot,gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := typed false w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [isNot,gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            binaryRep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [isNot,gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            binaryRep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
lemma pullTyped {n : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ typed n w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', t' ≤ t+n.toNat ∧ k'+t+n.toNat ≤ k+t'+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, by cases n <;> simp <;> omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨rfl, a, ha, hp', eq⟩ | ⟨rfl, d, a, b, ha, hb, pa, pb, hab, eq⟩)
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
        exact ⟨_, _, _, by simp, by simp; omega, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
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
        exact ⟨_, _, _, by simp, by simp; omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, by cases n <;> simp <;> omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
end Research.NegPin3091
open Research.Basis1868
namespace Research.SmallMono3091
lemma neutral {k t S} (h : Live k t S) : TRestricted k t S (fun _ => .tNone) := by
  induction h with
  | stop => exact TRestricted.stop
  | @unary k t U a ha hf tail ih =>
    apply TRestricted.unary ha hf (by decide) (by simp)
    have e : updUnaryTag (fun _ => .tNone) a=fun _ => .tNone := by funext x;simp [updUnaryTag]
    rwa [e]
  | @binary k t U a b d ha hb ne hf rest ih =>
    cases d with
    | false =>
      apply TRestricted.binaryAnd ha hb ne hf (by simp) (by simp)
      have e : updAndTag (fun _ => .tNone) a b=fun _ => .tNone := by funext x;simp [updAndTag]
      rwa [e]
    | true =>
      apply TRestricted.binaryOr ha hb ne hf (by simp) (by simp)
      have e : updOrTag (fun _ => .tNone) a b=fun _ => .tNone := by funext x;simp [updOrTag]
      rwa [e]
end Research.SmallMono3091
namespace Research.RowMono3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · change l₁.all id = true → l₂.all id = true
    simp only [List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · change l₁.any id = true → l₂.any id = true
    simp only [List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

def rows : List ℕ := [3,6,12,17,24,33,42,50,66,69,104,116,132,138,160,201,208,261,264,276,288,320,385,402]

end Research.RowMono3091
namespace Research.RowMono3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
lemma eval_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool) (len : x.length=y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true := by
  exact wiresFrom_mono C.gates (fun g hg => by simpa using (hm g hg).1) x y len hle C.output


end Research.RowMono3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Research.Basis1868 Research.NegPin3091 Research.CostMetric3091
namespace Research.SmallMono3091
def fresh (w : List Sig) (g : Gate) := let z := gv w g; z != zero && z != one && !w.contains z
def fee : List Gate → List Sig → Nat
  | [],_ => 0
  | g::gs,w => (fresh w g).toNat+fee gs (w++[gv w g])
lemma discounted (gs : List Gate) (w : List Sig) (hw : ∀ a∈w,Valid a)
    (legal : ∀ g∈gs,Research.NegPin3091.legal g) (mono : ∀ g∈gs,isNot g=false)
    (hout : target∈execute gs w) : ∃ k S,k≤fee gs w ∧ Live k 0 S ∧ ∀ a∈S,a∈w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by rfl,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha;rcases List.mem_append.mp ha with ha|ha
      · exact hw a ha
      · exact List.mem_singleton.mp ha ▸ gv_valid hw g
    obtain ⟨k,S,hk,hl,sub⟩ := ih _ hw' (fun a h => legal a (by simp [h])) (fun a h => mono a (by simp [h])) hout
    cases fr : fresh w g with
    | false =>
      refine ⟨k,S,by simpa [fee,fr] using hk,hl,?_⟩
      intro a ha
      rcases (show a∈w ∨ a=gv w g by simpa using sub a ha) with ha'|rfl
      · exact ha'
      · have hp := live_proper hl _ ha
        by_contra hm
        simp [fresh,hp.2.1,hp.2.2,hm] at fr
    | true =>
      have rep := gateRep hw g (legal g (by simp))
      rw [mono g (by simp)] at rep
      obtain ⟨l,t,T,ht,hn,he,hs⟩ := pullTyped hl rep sub
      have e : t=0 := by simpa using ht
      subst t
      exact ⟨l,T,by simp [fee,fr];simp at hn;omega,he,hs⟩
def sample (s : Bool) (i : Fin 414) (j : Fin 9) := bit s i (r.getD j.val zero)
lemma sampleEdge : ∀ s i,edgeF (sample s i)=s := by decide +kernel
lemma samplePin : ∀ i,(sample false i 0 || sample false i 3)=true := by decide +kernel
lemma inputRow (s i) : List.ofFn (sample s i)=r.map (bit s i) := by
  have er : List.ofFn (fun j : Fin 9 => r.getD j.val zero)=r := rfl
  calc
    _ = (List.ofFn (fun j : Fin 9 => r.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn];rfl
    _ = _ := congrArg _ er
def base := r++[one]
lemma baseValid : ∀ a∈base,Valid a := by
  have cert : base.all (fun a => decide (a.1≤top ∧ a.2≤top))=true := by decide +kernel
  intro a ha;have h := of_decide_eq_true (List.all_eq_true.mp cert a ha);exact ⟨valid1_of_le_top h.1,valid1_of_le_top h.2⟩
lemma rowIncrease {C : Circuit} (hm : Monotone2 C) (x : Fin 9 → Bool) (z : Bool) :
    C.eval (List.ofFn x++[z])=true → C.eval (List.ofFn x++[true])=true := by
  apply Research.RowMono3091.eval_mono C hm _ _ (by simp)
  intro i hi
  by_cases h : i<9
  · rw [List.getD_append _ _ _ _ (by simpa)] at hi ⊢
    exact hi
  · by_cases e : i=9
    · subst i;simp [List.getD]
    · rw [List.getD_eq_default _ _ (by simp;omega)] at hi;contradiction
lemma finalTarget {C : Circuit} (fan : FanInTwo C) (hm : Monotone2 C)
    (agree : ∀ x : Fin 9 → Bool,C.eval (List.ofFn x++[x 0||x 3])=edgeF x) :
    (execute C.gates base).getD C.output zero=target := by
  let w:=execute C.gates base
  have hp (s) (i : Fin 414) : bit s i (w.getD C.output zero)=s := by
    rw [←b_read]
    change ((execute C.gates base).map _).getD C.output false=s
    rw [execute_bits _ _ _ _ baseValid (fun g hg => (fan g hg).1)]
    have good := agree (sample s i)
    rw [sampleEdge] at good
    change C.eval (base.map (bit s i))=s
    rw [base,List.map_append,←inputRow]
    simp only [List.map_cons,List.map_nil,bit_one]
    cases s with
    | false => rwa [samplePin] at good
    | true => exact rowIncrease hm _ _ good
  have good := valid_getD (execute_valid C.gates base baseValid) C.output
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq;intro i;rw [target,testBit_top]
    by_cases hi : i<414
    · simpa [bit,hi] using hp true ⟨i,hi⟩
    · rw [good.1 i (by omega)];simp [hi]
  · apply Nat.eq_of_testBit_eq;intro i
    by_cases hi : i<414
    · simpa [bit,target] using hp false ⟨i,hi⟩
    · rw [good.2 i (by omega)];exact (Nat.zero_testBit i).symm
def witness : Fin 9 → Fin 414 := ![0,1,16,33,49,81,96,113,144]
lemma uniqueRow : ∀ a b : Fin 9,(bit true (witness a) (r.getD b.val zero) && !bit false (witness a) (r.getD b.val zero))=true → a=b := by decide +kernel
lemma allInitial {k S} (live : Live k 0 S) (sub : ∀ a∈S,a∈base) : S=r.toFinset := by
  have sr (a) (h : a∈S) : a∈r := by
    rcases List.mem_append.mp (sub a h) with m|m
    · exact m
    · exact ((live_proper live a h).2.2 (List.mem_singleton.mp m)).elim
  have lookup : List.ofFn (fun j : Fin 9 => r.getD j.val zero)=r := rfl
  ext v;rw [List.mem_toFinset];refine ⟨sr v,?_⟩
  intro h;rw [←lookup,List.mem_ofFn] at h;obtain ⟨j,rfl⟩:=h
  obtain ⟨a,ha,hd⟩ := Research.Mono1868.pair_sep live rfl (witness j) (witness j)
  have memb := sr a ha;rw [←lookup,List.mem_ofFn] at memb;obtain ⟨j',rfl⟩ :=memb
  change bit true (witness j) (r.getD j'.val zero)=true ∧ bit false (witness j) (r.getD j'.val zero)=false at hd
  have e := uniqueRow j j' (by rw [hd.1,hd.2];rfl)
  exact e ▸ ha
lemma lower (cert : Impossible 12 0 roots) {C : Circuit} (fan : FanInTwo C) (hm : Monotone2 C)
    (agree : ∀ x : Fin 9 → Bool,C.eval (List.ofFn x++[x 0||x 3])=edgeF x) : 13≤fee C.gates base := by
  have hout := get_rep (execute C.gates base) C.output
  rw [finalTarget fan hm agree] at hout
  have noNot (g) (hg : g∈C.gates) : isNot g=false := by
    obtain h|h := (show g.op=.and ∨ g.op=.or from (hm g hg).1) <;> simp [isNot,h]
  obtain ⟨k,S,hk,hl,hs⟩ := discounted C.gates base baseValid fan noNot (hout.resolve_right (fun h => h target_proper))
  obtain rfl : S=r.toFinset := allInitial hl hs
  by_contra low
  apply cert k (by omega) _ (fun _ => .tNone) _ (neutral hl)
  refine ⟨?_,?_,?_⟩
  · have hn : r.Nodup := by decide +kernel
    simpa [roots,sigsOf,Function.comp_def] using hn
  · simp [roots,sigsOf,Function.comp_def]
  · intro w hw;obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw;rfl
end Research.SmallMono3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Research.Basis1868
open Research.Rigidity3091 Research.NegPin3091 Research.CostMetric3091
namespace Research.SmallMono3091
abbrev rawSeen (w : List Sig) (a : Sig) := a∈w ∨ Cst a
lemma rawGet (w : List Sig) (i : Nat) : rawSeen w (w.getD i zero) := by
  by_cases lo : i<w.length
  · exact Or.inl (by rw [List.getD_eq_getElem _ _ lo];exact List.getElem_mem lo)
  · exact Or.inr (Or.inl (List.getD_eq_default _ _ (by omega)))
lemma rawBin {w : List Sig} (valid : ∀ a∈w,Valid a) (d : Bool) (i j : Nat)
    (c : Cst (w.getD i zero) ∨ Cst (w.getD j zero)) : rawSeen w (bin d (w.getD i zero) (w.getD j zero)) := by
  have aux (a b : Sig) (ha : Valid a) (sa : rawSeen w a) (z : Cst b) : rawSeen w (bin d a b) := by
    obtain ⟨e1,e2,e3,e4,_,_⟩ := bin_laws ha
    rcases z with rfl|rfl <;> cases d <;> first | rwa [e1] | rwa [e2] | rw [e3];exact Or.inr (Or.inl rfl) | rw [e4];exact Or.inr (Or.inr rfl)
  rcases c with c|c
  · rw [bin_comm];exact aux _ _ (valid_getD valid j) (rawGet w j) c
  · exact aux _ _ (valid_getD valid i) (rawGet w i) c
lemma rawOff {w g} (h : rawSeen w (gv w g)) : fresh w g=false := by
  rcases h with h|h|h <;> simp [fresh,h]
lemma freeRead {w : List Sig} (valid : ∀ a∈w,Valid a) {g : Gate} (fan : legal g) (non : isNot g=false)
    (h : ∃ i∈g.inputs,Cst (w.getD i zero)) : fresh w g=false := by
  apply rawOff
  obtain ⟨op,ins⟩ := g
  obtain ⟨d,rfl⟩ : ∃ d : Bool, op=boolOp d := by
    rcases fan.1 with h|h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
    · have e : op=.not := h;subst op;contradiction
  cases ins with
  | nil => obtain ⟨i,hi,_⟩ := h;contradiction
  | cons i tl =>
    cases tl with
    | nil => rw [gvOne w valid d i];exact rawGet w i
    | cons j tl =>
      obtain rfl : tl=[] := List.length_eq_zero_iff.mp (by have l:=fan.2;change (i::j::tl).length≤2 at l;simp only [List.length_cons] at l;omega)
      rw [gvTwo w valid d i j];apply rawBin valid;obtain ⟨a,h,ca⟩ := h
      rcases (show a=i ∨ a=j by simpa using h) with rfl|rfl
      · exact Or.inl ca
      · exact Or.inr ca
lemma startFree {r : Record} (valid : ∀ a∈r.before,Valid a) (fan : legal r.gate) (non : isNot r.gate=false) (s : starts r) : fresh r.before r.gate=false := by
  apply freeRead valid fan non
  obtain ⟨u,v,_,_,rel,dif,_⟩ := s
  by_contra! hn
  apply dif;unfold gateVal;congr 1
  apply List.map_congr_left;intro i hi;by_contra no;exact (rel i no).elim (hn i hi).1 (hn i hi).2
def unbilled (r : Record) := !(fresh r.before r.gate)
lemma tally (gs : List Gate) (w : List Sig) : (trace gs w).countP unbilled+fee gs w=gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => have old:=ih (w++[gv w g]);cases e : fresh w g <;> simp [trace,List.countP_cons,unbilled,fee,e] <;> omega
lemma onlyOne {α : Type} {q : List α} {f : α → Bool} {a b : α} (h : q.countP f≤1) (ha : a∈q) (hb : b∈q) (fa : f a=true) (fb : f b=true) : a=b := by
  have len : (q.filter f).length≤1 := by rwa [←List.countP_eq_length_filter]
  have a' := List.mem_filter.mpr ⟨ha,fa⟩
  have b' := List.mem_filter.mpr ⟨hb,fb⟩
  cases e : q.filter f with
  | nil => simp [e] at a'
  | cons i t =>
    have eq : t=[] := List.length_eq_zero_iff.mp (by rw [e,List.length_cons] at len;omega)
    rw [eq] at e
    exact (List.mem_singleton.mp (e ▸ a')).trans (List.mem_singleton.mp (e ▸ b')).symm
lemma pinTrace {w : List Sig} (lo : 9<w.length) (p : w.getD 9 zero=one) (gs : List Gate) : ∀ r∈trace gs w,r.before.getD 9 zero=one := by
  induction gs generalizing w with
  | nil => simp [trace]
  | cons g gs ih =>
    intro r hr;rcases List.mem_cons.mp hr with rfl|h
    · exact p
    · exact ih (by simp;omega) (by rw [List.getD_append _ _ _ _ lo];exact p) _ h
lemma traceGates (gs : List Gate) (w : List Sig) : (trace gs w).map Record.gate=gs := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [trace,ih]
lemma readBound {t : List Record} {f : Record → Bool} {i : Nat} (hd : ∀ r∈t,r.gate.inputs.count i≤(f r).toNat) : (t.flatMap (fun r => r.gate.inputs)).count i≤t.countP f := by
  induction t with
  | nil => simp
  | cons r t ih =>
    have h:=hd r (by simp)
    have b:=ih (fun s hs => hd s (List.mem_cons_of_mem _ hs))
    cases e : f r <;> simp [List.countP_cons,e] at * <;> omega
end Research.SmallMono3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Research.Basis1868
open Research.Rigidity3091 Research.NegPin3091 Research.CostMetric3091
namespace Research.SmallMono3091
lemma monoGateway {C : Circuit} (fan : FanInTwo C) (hm : Monotone2 C)
    (agree : ∀ x : Fin 9 → Bool,C.eval (List.ofFn x++[x 0 || x 3])=edgeF x)
    (different : ∀ j : Fin 9,∃ x : Fin 9 → Bool,C.eval (List.ofFn x++[x j]) ≠ edgeF x) :
    ∃ s∈trace C.gates base,starts s := by
  by_contra! hn
  obtain ⟨x,wrong⟩ := different 0
  let u := List.ofFn x++[x 0]
  let v := List.ofFn x++[x 0 || x 3]
  have differentOut : (Research.NegPin3091.run C.gates u).getD C.output false≠(Research.NegPin3091.run C.gates v).getD C.output false := fun e => wrong (e.trans (agree x))
  have prior : ∀ i,u.getD i false≠v.getD i false → Cst (base.getD i zero) := by
    intro i dif
    by_cases low : i<9
    · exact False.elim (dif (by change (List.ofFn x++[_]).getD i false=(List.ofFn x++[_]).getD i false; rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]))
    · by_cases eq : i=9
      · subst i;exact Or.inr rfl
      · rw [List.getD_eq_default _ _ (by simp [u];omega),List.getD_eq_default _ _ (by simp [v];omega)] at dif
        contradiction
  have fin := noStart fan baseValid (show one∈base by simp [base]) hn (by simp [u,base];rfl) (by simp [v,base];rfl) prior C.output differentOut
  change Cst ((execute C.gates base).getD C.output zero) at fin
  rw [Research.SmallMono3091.finalTarget fan hm agree] at fin
  exact fin.elim target_proper.2.1 target_proper.2.2

lemma countPair {i j : Nat} (ne : i≠j) (a : Nat) : [i,j].count a≤1 := by
  by_cases h : i=a <;> by_cases h' : j=a <;> simp_all
lemma monoEnd (cert : Impossible 12 0 roots) {C : Circuit} (fan : FanInTwo C) (hm : Monotone2 C) (size : C.size=14)
    (agree : ∀ x : Fin 9 → Bool,C.eval (List.ofFn x++[x 0 || x 3])=edgeF x)
    (different : ∀ j : Fin 9,∃ x : Fin 9 → Bool,C.eval (List.ofFn x++[x j]) ≠ edgeF x)
    (reads : 2≤(C.output::C.gates.flatMap Gate.inputs).count 9) : False := by
  let T := trace C.gates base
  have paid := lower cert fan hm agree
  have count := tally C.gates base
  have bound : T.countP unbilled≤1 := by change C.gates.length=14 at size;dsimp only [T];omega
  have known (q) (hq : q∈T) := traceData C.gates base baseValid (by simp [base]) fan q hq
  have mapped : T.map Record.gate=C.gates := traceGates ..
  have non (q) (hq : q∈T) : isNot q.gate=false := by
    have mem := List.mem_map_of_mem (f := Record.gate) hq
    rw [mapped] at mem
    obtain h|h := (show q.gate.op=.and ∨ q.gate.op=.or from (hm _ mem).1) <;> simp [isNot,h]
  obtain ⟨q,hq,qs⟩ := monoGateway fan hm agree different
  have free : unbilled q=true := by simp [unbilled,startFree (known q hq).1 (known q hq).2.2 (non q hq) qs]
  have b := readBound (t := T) (i := 9) (f := unbilled) (by
    intro s hs
    by_cases mem : 9∈s.gate.inputs
    · have pin := pinTrace (w := base) (by decide +kernel) (by rfl) C.gates s hs
      have fr := freeRead (known s hs).1 (known s hs).2.2 (non s hs) ⟨9,mem,Or.inr pin⟩
      have flag : unbilled s=true := by simp [unbilled,fr]
      obtain rfl := onlyOne bound hs hq flag free
      obtain ⟨i,j,ins,pair⟩ := shapeOf (known s hs).1 (known s hs).2.1 (known s hs).2.2 (non s hs) (Or.inr qs)
      rw [ins,flag];exact countPair pair.1 9
    · simp [List.count_eq_zero.mpr mem])
  have m : T.flatMap (fun a => a.gate.inputs)=C.gates.flatMap Gate.inputs := by rw [←mapped,List.flatMap_map]
  rw [m] at b
  have off := offOutput agree
  simp [List.count_cons,off] at reads
  omega
end Research.SmallMono3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Research.Basis1868
open Research.Rigidity3091 Research.NegPin3091 Research.CostMetric3091 Research.SmallMono3091
namespace Research.OneNot3091
lemma execLen (gs : List Gate) (w : List Sig) : (execute gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [execute]
  | cons g gs ih => change (execute gs (w++[_])).length=_;rw [ih];simp;omega
lemma execTail (gs : List Gate) (w : List Sig) : ∃ t,execute gs w=w++t := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih => obtain ⟨t,h⟩:=ih (w++[gv w g]);exact ⟨gv w g::t,h.trans (by simp)⟩
lemma traceSplit {r : Record} {gs : List Gate} {w : List Sig} (h : r∈trace gs w) :
    ∃ l t,gs=l++r.gate::t ∧ r.before=execute l w := by
  induction gs generalizing w with
  | nil => cases h
  | cons g gs ih =>
    rcases List.mem_cons.mp h with rfl|hh
    · exact ⟨[],gs,rfl,rfl⟩
    · obtain ⟨l,t,eq,b⟩ := ih hh
      exact ⟨g::l,t,congrArg (g::·) eq,b⟩
lemma recordTail {r : Record} {gs : List Gate} {w : List Sig} (h : r∈trace gs w) :
    ∃ tail,execute gs w=r.before++gv r.before r.gate::tail := by
  obtain ⟨l,t,hg,he⟩ := traceSplit h
  rw [hg,he];change ∃ tail,(l++r.gate::t).foldl _ w=_;rw [List.foldl_append]
  obtain ⟨tail,e⟩ := execTail t (execute l w++[gv (execute l w) r.gate]);exact ⟨tail,e.trans (by simp)⟩
lemma recordLimits {r : Record} {gs : List Gate} {w : List Sig} (h : r∈trace gs w) : w.length≤r.before.length ∧ r.before.length<w.length+gs.length := by
  obtain ⟨l,t,hg,he⟩ := traceSplit h;rw [he,hg,execLen,List.length_append,List.length_cons];omega
lemma recordCell {r : Record} {gs : List Gate} {w : List Sig} (h : r∈trace gs w) :
    (execute gs w).getD r.before.length zero=gv r.before r.gate := by
  obtain ⟨t,ht⟩:=recordTail h;rw [ht];simp [List.getD]
lemma cellConstant {r : Record} {gs : List Gate} {w : List Sig} (h : r∈trace gs w) {i : Nat} (c : Cst ((execute gs w).getD i zero)) : Cst (r.before.getD i zero) := by
  by_cases lo : i<r.before.length
  · obtain ⟨t,e⟩:=recordTail h;rw [e,List.getD_append _ _ _ _ lo] at c;exact c
  · exact Or.inl (List.getD_eq_default _ _ (by omega))
lemma totalCount {l : List Nat} {n} (h : ∀ a∈l,a<n) : ∑ i∈Finset.range n,l.count i=l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have aa := h a (by simp)
    have j := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simp only [List.count_cons,List.length_cons]
    trans ∑ i∈Finset.range n,(l.count i + if a=i then 1 else 0)
    · apply Finset.sum_congr rfl;intro i hi;by_cases e : a=i <;> simp [e]
    · rw [Finset.sum_add_distrib,j];simp [Finset.mem_range,aa]
lemma excessEq {l : List Nat} {n} (h : ∀ a∈l,a<n) (cov : ∀ i<n,i∈l) :
    (∑ i∈Finset.range n,(l.count i-1))+n=l.length := by
  have e : n=∑ _i∈Finset.range n,(1 : Nat) := by simp
  calc
    _ = ∑ i∈Finset.range n,(l.count i-1+1) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = ∑ i∈Finset.range n,l.count i := by
      apply Finset.sum_congr rfl;intro i hi;have p := List.count_pos_iff.mpr (cov i (Finset.mem_range.mp hi));omega
    _ = _ := totalCount h
lemma twoLength {gs : List Gate} (h : ∀ g∈gs,g.inputs.length=2) : (gs.flatMap Gate.inputs).length=2*gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have a:=h g (by simp);have e:=ih (fun k hk => h k (List.mem_cons_of_mem _ hk));simp [a,e];omega
end Research.OneNot3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Research.Basis1868
open Research.Rigidity3091 Research.NegPin3091 Research.CostMetric3091 Research.SmallMono3091 Research.PinRows3091
namespace Research.OneNot3091
def initial := sliceRaw++[one]
lemma initialValid : ∀ a∈initial,Valid a := by
  intro a h;rcases List.mem_append.mp h with h|h
  · exact slice_raw_valid a h
  · exact List.mem_singleton.mp h ▸ valid_one
abbrev regs (C : Circuit) := trace C.gates initial
abbrev negRec (r : Record) := isNot r.gate
lemma negs (C : Circuit) : (regs C).countP negRec=C.gates.countP isNot := by
  rw [←traceGates C.gates initial,List.countP_map];rfl
lemma readsEq (C : Circuit) : ((regs C).flatMap (fun r => r.gate.inputs))=C.gates.flatMap Gate.inputs := by
  have m:=traceGates C.gates initial; rw [←m,List.flatMap_map]
lemma recordOK {C : Circuit} (fan : FanInTwo C) {r : Record} (hr : r∈regs C) : (∀ a∈r.before,Valid a) ∧ one∈r.before ∧ legal r.gate :=
  traceData C.gates initial initialValid (by simp [initial]) fan r hr
lemma noNewOfConst {r : Record} (val : ∀ a∈r.before,Valid a) (oneIn : one∈r.before) (fan : legal r.gate) (n : isNot r.gate=false)
    (nov : novel r.before r.gate=true) {i} (hi : i∈r.gate.inputs) : ¬Cst (r.before.getD i zero) := by
  obtain ⟨a,b,ins,h⟩:=shapeOf val oneIn fan n (Or.inl nov)
  have h' := h.2.2.2.2 nov
  rw [ins] at hi;rcases (show i=a ∨ i=b by simpa using hi) with rfl|rfl
  · exact h'.1
  · exact h'.2
structure Layout (C : Circuit) where
  bridge : Record
  member : bridge∈regs C
  crossed : starts bridge
  bound : (regs C).countP extra≤1
  usefulAll : ∀ r∈regs C,negRec r=false → useful r
  onlyFree : ∀ r∈regs C,negRec r=false → novel r.before r.gate=false → r=bridge
lemma layout (rank : Research.Cost3091.Rank) {C : Circuit} (fan : FanInTwo C) (size : C.size=14)
    (agree : ∀ x : Fin 9 → Bool,C.eval (List.ofFn x++[x 0||x 3])=edgeF x)
    (different : ∀ j : Fin 9,∃ x : Fin 9 → Bool,C.eval (List.ofFn x++[x j]) ≠ edgeF x)
    (oneNot : C.gates.countP isNot=1) : Nonempty (Layout C) := by
  have cost:=novelScore rank C fan agree
  have tally:=extraCount C.gates initial initialValid (by simp [initial])
  have bound : (regs C).countP extra≤1 := by change C.gates.length=14 at size;change 12≤novelCost C.gates initial at cost;dsimp only [regs];omega
  obtain ⟨q,hq,qs⟩ := gateway fan agree different
  have rd:=recordOK fan hq
  have free := startsExtra rd.1 rd.2.1 rd.2.2 qs
  have uniq (s) (hs : s∈regs C) (n : negRec s=false) (abs : novel s.before s.gate=false) : s=q := by
    exact oneRecord bound hs hq (by simp [extra,n,abs,negRec] at *) free
  refine ⟨⟨q,hq,qs,bound,?_,uniq⟩⟩
  intro s hs hn
  cases e : novel s.before s.gate
  · exact Or.inr (uniq s hs hn e ▸ qs)
  · exact Or.inl e
lemma inputs2 {C : Circuit} (fan : FanInTwo C) (a : Layout C) {r : Record} (hm : r∈regs C) (n : negRec r=false) : ∃ i j,r.gate.inputs=[i,j] ∧ pairShape r.before r.gate i j := by
  have d:=recordOK fan hm
  exact shapeOf d.1 d.2.1 d.2.2 n (a.usefulAll r hm n)
lemma constantBridge {C : Circuit} (fan : FanInTwo C) (a : Layout C) {r : Record} (hr : r∈regs C) (n : negRec r=false) {i} (hi : i∈r.gate.inputs) (c : Cst (r.before.getD i zero)) : r=a.bridge := by
  have d:=recordOK fan hr
  apply a.onlyFree r hr n;apply Bool.eq_false_iff.mpr;intro fresh;exact noNewOfConst d.1 d.2.1 d.2.2 n fresh hi c
lemma pinAt {C : Circuit} {r : Record} (hr : r∈regs C) : r.before.getD 9 zero=one := pinTrace (w := initial) (by decide +kernel) rfl C.gates r hr
lemma readLimit {C : Circuit} (fan : FanInTwo C) (a : Layout C) {r : Record} (hr : r∈regs C) (n : negRec r=false) : r.gate.inputs.count 9≤(extra r).toNat := by
  by_cases h : 9∈r.gate.inputs
  · have eq := constantBridge fan a hr n h (Or.inr (pinAt hr))
    have d:=recordOK fan a.member
    have flag := startsExtra d.1 d.2.1 d.2.2 a.crossed
    have flag' : extra r=true := eq ▸ flag
    rw [flag']
    obtain ⟨i,j,ins,p⟩:=inputs2 fan a hr n
    rw [ins];exact countPair p.1 9
  · simp [List.count_eq_zero.mpr h]
end Research.OneNot3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Research.Basis1868
open Research.Rigidity3091 Research.NegPin3091 Research.CostMetric3091 Research.SmallMono3091 Research.PinRows3091
namespace Research.OneNot3091
lemma shapeNot {xs : List Nat} (le : xs.length≤2) (pin : 9∈xs) (maxi : ∀ i∈xs,i≤24)
    (narrow : xs.length=2 → ¬∀ i∈xs,i<24) : xs=[9] ∨ xs=[9,24] ∨ xs=[24,9] := by
  cases xs with
  | nil => contradiction
  | cons i t =>
    cases t with
    | nil =>
      obtain rfl : 9=i := by simpa using pin
      exact Or.inl rfl
    | cons j t =>
      obtain rfl : t=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at le;omega)
      have mi:=maxi i (by simp);have mj:=maxi j (by simp)
      have outside := narrow rfl
      rcases (show 9=i ∨ 9=j by simpa using pin) with rfl|rfl
      · right;left;have ej : j=24 := by by_contra ne;exact outside (by simpa using (by omega : j<24))
        simp [ej]
      · right;right;have ei : i=24 := by by_contra ne;exact outside (by simpa using (by omega : i<24))
        simp [ei]
lemma common (rank : Research.Cost3091.Rank) {C : Circuit} (fan : FanInTwo C) (size : C.size=14)
    (agree : ∀ x : Fin 9 → Bool,C.eval (List.ofFn x++[x 0||x 3])=edgeF x)
    (different : ∀ j : Fin 9,∃ x : Fin 9 → Bool,C.eval (List.ofFn x++[x j]) ≠ edgeF x)
    (oneNot : C.gates.countP isNot=1) (indices : ∀ g∈C.gates,∀ i∈g.inputs,i≤24)
    (all : ∀ i<24,i∈C.output::C.gates.flatMap Gate.inputs)
    (budget : 9+1+∑ i∈Finset.range 24,((C.output::C.gates.flatMap Gate.inputs).count i-1)≤14)
    (reads : 2≤(C.output::C.gates.flatMap Gate.inputs).count 9) : False := by
  obtain ⟨a⟩ := layout rank fan size agree different oneNot
  let T := regs C
  let refs := C.output::C.gates.flatMap Gate.inputs
  have hlen : C.gates.length=14 := size
  have ilen : initial.length=10 := rfl
  have outSig := Research.Rigidity3091.finalTarget C fan agree
  change (execute C.gates initial).getD C.output zero=target at outSig
  have boundedOutput : C.output<24 := by
    by_contra bad;rw [List.getD_eq_default _ _ (by rw [execLen,ilen,hlen];omega)] at outSig;exact target_proper.2.1 outSig.symm
  have mapT : T.map Record.gate=C.gates := traceGates ..
  have negCount : T.countP negRec=1 := (negs C).trans oneNot
  obtain ⟨n,hn,mark⟩ := List.countP_pos_iff.mp (show 0<T.countP negRec by omega)
  have uniq (s) (hs : s∈T) (v : negRec s=true) : s=n := onlyOne (by omega) hs hn v mark
  have gmem (s) (hs : s∈T) : s.gate∈C.gates := mapT ▸ List.mem_map_of_mem (f := Record.gate) hs
  have gpre (g) (hg : g∈C.gates) : ∃ s∈T,s.gate=g := by rw [←mapT] at hg;exact List.mem_map.mp hg
  have flatreads : 2≤(T.flatMap (fun s=>s.gate.inputs)).count 9 := by rw [readsEq];simpa [offOutput agree] using reads
  have touches : 9∈n.gate.inputs := by
    by_contra never
    have v:=readBound (t := T) (i := 9) (f := extra) (by
      intro s hs;cases em : negRec s with
      | false => exact readLimit fan a hs em
      | true => obtain rfl:=uniq s hs em;simp [List.count_eq_zero.mpr never])
    have lim:=a.bound;change T.countP extra≤1 at lim;omega
  have shape := shapeNot (recordOK fan hn).2.2.2 touches (indices _ (gmem n hn)) (by
    intro pair low
    have positional (s) (hs : s∈T) : s.gate.inputs.length=2 ∧ ∀ i∈s.gate.inputs,i<24 := by
      cases m : negRec s with
      | true => obtain rfl:=uniq s hs m;exact ⟨pair,low⟩
      | false =>
        obtain ⟨i,j,eq,p⟩:=inputs2 fan a hs m
        have b := (recordLimits hs).2;rw [ilen,hlen] at b
        rw [eq];refine ⟨rfl,?_⟩;intro k hk;rcases (show k=i ∨ k=j by simpa using hk) with rfl|rfl <;> have := p.2.1 <;> have := p.2.2.1 <;> omega
    have m (g) (hg : g∈C.gates) : g.inputs.length=2 ∧ ∀ i∈g.inputs,i<24 := by obtain ⟨s,hs,rfl⟩:=gpre g hg;exact positional s hs
    have exactCount:= excessEq (l := refs) (n := 24) (by
      intro i hi;rcases List.mem_cons.mp hi with rfl|inps
      · exact boundedOutput
      · obtain ⟨g,hg,h⟩ := List.mem_flatMap.mp inps;exact (m g hg).2 i h) all
    have ln := twoLength (fun g hg => (m g hg).1)
    have rr : refs.length=29 := by simp [refs,ln,hlen]
    change 9+1+∑ i∈Finset.range 24,(refs.count i-1)≤14 at budget;omega)
  have cnt : n.gate.inputs.count 9=1 := by rcases shape with e|e|e <;> rw [e] <;> decide +kernel
  have someBin : ∃ s∈T,negRec s=false ∧ 9∈s.gate.inputs := by
    by_contra! hnob
    have bb:=readBound (t := T) (i := 9) (f := negRec) (by
      intro s hs;cases m : negRec s with
      | false => simp [List.count_eq_zero.mpr (hnob s hs m),m]
      | true => obtain rfl:=uniq s hs m;rw [cnt];decide)
    omega
  obtain ⟨s,hs,nn,s9⟩ := someBin
  have sq:=constantBridge fan a hs nn s9 (Or.inr (pinAt hs))
  let ix := n.before.length
  have lim:=recordLimits hn;rw [ilen,hlen] at lim
  have distinct : ix≠9 := by dsimp only [ix];omega
  have nx : Cst (gv n.before n.gate) := by
    have op := isNot_iff.mp mark
    have wr := pinAt hn
    have hi : n.before.getD 24 zero=zero := List.getD_eq_default _ _ (by omega)
    rcases shape with e|e|e <;> simp only [gv,op,e,List.map_cons,List.map_nil,List.headD_cons,wr,hi,neg_laws] <;> first | exact Or.inl rfl | exact Or.inr rfl
  have fc : Cst ((execute C.gates initial).getD ix zero) := by change Cst ((execute C.gates initial).getD n.before.length zero);rw [recordCell hn];exact nx
  have noout : ix≠C.output := by intro e;rw [e,outSig] at fc;exact fc.elim target_proper.2.1 target_proper.2.2
  have hit := (List.mem_cons.mp (all ix (by dsimp only [ix];omega))).resolve_left noout
  obtain ⟨g,hg,gi⟩ := List.mem_flatMap.mp hit
  obtain ⟨t,ht,rfl⟩ := gpre g hg
  have nb : negRec t=false := by
    apply Bool.eq_false_iff.mpr;intro m;obtain rfl:=uniq t ht m
    have ni : ix<24 := lim.2
    rcases shape with e|e|e <;> rw [e] at gi <;> simp [distinct,show ix≠24 by omega] at gi
  have c:=cellConstant ht fc
  have tq:=constantBridge fan a ht nb gi c
  have eq : t=s := tq.trans sq.symm
  rw [eq] at gi c
  obtain ⟨i,j,ins,p⟩:=inputs2 fan a hs nn
  rw [ins] at gi s9
  have hix : ix=i ∨ ix=j := by simpa using gi
  have h9 : 9=i ∨ 9=j := by simpa using s9
  have c9 : Cst (s.before.getD 9 zero) := Or.inr (pinAt hs)
  rcases hix with rfl|rfl <;> rcases h9 with e|e <;> first | exact (distinct e.symm).elim | exact p.2.2.2.1 ⟨c,e ▸ c9⟩ | exact p.2.2.2.1 ⟨e ▸ c9,c⟩
end Research.OneNot3091
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Research.Basis1868
open Research.CostMetric3091 Research.SmallMono3091 Research.OneNot3091
namespace Research.Full3091
lemma matchCount {gs : List Gate} (fan : ∀ g∈gs,Research.NegPin3091.legal g) :
    (gs.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length=gs.countP isNot := by
  rw [←List.countP_eq_length_filter];apply List.countP_congr;intro g hg
  have h := (fan g hg).1
  rcases (show g.op=.and ∨ g.op=.or ∨ g.op=.not from h) with e|e|e <;> simp only [isNot,e] <;> decide +kernel
lemma combined (rank : Research.Cost3091.Rank) (small : Impossible 12 0 roots) (C : Circuit) (fan : FanInTwo C) (size : C.size=14)
    (indices : C.output≤10+C.size ∧ ∀ g∈C.gates,∀ i∈g.inputs,i≤10+C.size)
    (all : ∀ i<10+C.size,i∈C.output::C.gates.flatMap Gate.inputs)
    (budget : 9+(C.gates.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length + ∑ i∈Finset.range (10+C.size),((C.output::C.gates.flatMap Gate.inputs).count i-1)≤C.size)
    (reads : 2≤(C.output::C.gates.flatMap Gate.inputs).count 9)
    (different : ∀ j : Fin 9,∃ x : Fin 9 → Bool,C.eval (List.ofFn x++[x j]) ≠ edgeF x) :
    ∃ x : Fin 9 → Bool,C.eval (List.ofFn x++[x 0 || x 3])≠edgeF x := by
  by_contra! agree
  have limit : C.gates.countP isNot≤1 := by
    have cost:=novelScore rank C fan agree
    have t:=Research.Rigidity3091.extraCount C.gates initial initialValid (by simp [initial])
    obtain ⟨q,hq,hs⟩:=Research.Rigidity3091.gateway fan agree different
    have data:=recordOK fan hq
    have marked:=Research.Rigidity3091.startsExtra data.1 data.2.1 data.2.2 hs
    have positive : 0<(regs C).countP Research.Rigidity3091.extra := List.countP_pos_iff.mpr ⟨q,hq,marked⟩
    change 12≤novelCost C.gates initial at cost
    dsimp only [regs] at positive
    change C.gates.length=14 at size
    omega
  by_cases m : C.gates.countP isNot=0
  · have hm : Monotone2 C := by
      intro g hg
      have n := List.countP_eq_zero.mp m g hg
      obtain ⟨h,k⟩:=fan g hg;refine ⟨?_,k⟩
      rcases (show g.op=.and ∨ g.op=.or ∨ g.op=.not from h) with e|e|e
      · exact Or.inl e
      · exact Or.inr e
      · exact (n (isNot_iff.mpr e)).elim
    exact monoEnd small fan hm size agree different reads
  · have n : C.gates.countP isNot=1 := by omega
    rw [matchCount fan,n,size] at budget;rw [size] at all indices
    exact common rank fan size agree different n indices.2 all budget reads
end Research.Full3091


namespace Research.SmallMono3091
open Research.Basis1868
end Research.SmallMono3091
namespace Research.SmallMono3091
open Research.Basis1868 Research.Dag1868 Research.Orbit1868
abbrev j (i a b : Nat) := @span_join cover a i b
set_option maxHeartbeats 0 in
lemma total : span cover 540 0=true := (j 0 270 270 (j 0 135 135 (j 0 65 70 (j 0 30 35 (j 0 15 15 (j 0 5 10 (by decide +kernel) (j 5 5 5 (by decide +kernel) (by decide +kernel))) (j 15 5 10 (by decide +kernel) (j 20 5 5 (by decide +kernel) (by decide +kernel)))) (j 30 15 20 (j 30 5 10 (by decide +kernel) (j 35 5 5 (by decide +kernel) (by decide +kernel))) (j 45 10 10 (j 45 5 5 (by decide +kernel) (by decide +kernel)) (j 55 5 5 (by decide +kernel) (by decide +kernel))))) (j 65 35 35 (j 65 15 20 (j 65 5 10 (by decide +kernel) (j 70 5 5 (by decide +kernel) (by decide +kernel))) (j 80 10 10 (j 80 5 5 (by decide +kernel) (by decide +kernel)) (j 90 5 5 (by decide +kernel) (by decide +kernel)))) (j 100 15 20 (j 100 5 10 (by decide +kernel) (j 105 5 5 (by decide +kernel) (by decide +kernel))) (j 115 10 10 (j 115 5 5 (by decide +kernel) (by decide +kernel)) (j 125 5 5 (by decide +kernel) (by decide +kernel)))))) (j 135 65 70 (j 135 30 35 (j 135 15 15 (j 135 5 10 (by decide +kernel) (j 140 5 5 (by decide +kernel) (by decide +kernel))) (j 150 5 10 (by decide +kernel) (j 155 5 5 (by decide +kernel) (by decide +kernel)))) (j 165 15 20 (j 165 5 10 (by decide +kernel) (j 170 5 5 (by decide +kernel) (by decide +kernel))) (j 180 10 10 (j 180 5 5 (by decide +kernel) (by decide +kernel)) (j 190 5 5 (by decide +kernel) (by decide +kernel))))) (j 200 35 35 (j 200 15 20 (j 200 5 10 (by decide +kernel) (j 205 5 5 (by decide +kernel) (by decide +kernel))) (j 215 10 10 (j 215 5 5 (by decide +kernel) (by decide +kernel)) (j 225 5 5 (by decide +kernel) (by decide +kernel)))) (j 235 15 20 (j 235 5 10 (by decide +kernel) (j 240 5 5 (by decide +kernel) (by decide +kernel))) (j 250 10 10 (j 250 5 5 (by decide +kernel) (by decide +kernel)) (j 260 5 5 (by decide +kernel) (by decide +kernel))))))) (j 270 135 135 (j 270 65 70 (j 270 30 35 (j 270 15 15 (j 270 5 10 (by decide +kernel) (j 275 5 5 (by decide +kernel) (by decide +kernel))) (j 285 5 10 (by decide +kernel) (j 290 5 5 (by decide +kernel) (by decide +kernel)))) (j 300 15 20 (j 300 5 10 (by decide +kernel) (j 305 5 5 (by decide +kernel) (by decide +kernel))) (j 315 10 10 (j 315 5 5 (by decide +kernel) (by decide +kernel)) (j 325 5 5 (by decide +kernel) (by decide +kernel))))) (j 335 35 35 (j 335 15 20 (j 335 5 10 (by decide +kernel) (j 340 5 5 (by decide +kernel) (by decide +kernel))) (j 350 10 10 (j 350 5 5 (by decide +kernel) (by decide +kernel)) (j 360 5 5 (by decide +kernel) (by decide +kernel)))) (j 370 15 20 (j 370 5 10 (by decide +kernel) (j 375 5 5 (by decide +kernel) (by decide +kernel))) (j 385 10 10 (j 385 5 5 (by decide +kernel) (by decide +kernel)) (j 395 5 5 (by decide +kernel) (by decide +kernel)))))) (j 405 65 70 (j 405 30 35 (j 405 15 15 (j 405 5 10 (by decide +kernel) (j 410 5 5 (by decide +kernel) (by decide +kernel))) (j 420 5 10 (by decide +kernel) (j 425 5 5 (by decide +kernel) (by decide +kernel)))) (j 435 15 20 (j 435 5 10 (by decide +kernel) (j 440 5 5 (by decide +kernel) (by decide +kernel))) (j 450 10 10 (j 450 5 5 (by decide +kernel) (by decide +kernel)) (j 460 5 5 (by decide +kernel) (by decide +kernel))))) (j 470 35 35 (j 470 15 20 (j 470 5 10 (by decide +kernel) (j 475 5 5 (by decide +kernel) (by decide +kernel))) (j 485 10 10 (j 485 5 5 (by decide +kernel) (by decide +kernel)) (j 495 5 5 (by decide +kernel) (by decide +kernel)))) (j 505 15 20 (j 505 5 10 (by decide +kernel) (j 510 5 5 (by decide +kernel) (by decide +kernel))) (j 520 10 10 (j 520 5 5 (by decide +kernel) (by decide +kernel)) (j 530 5 5 (by decide +kernel) (by decide +kernel))))))))
lemma done : Impossible 12 0 roots := by
  have h : ∀ i<table.size,Research.TinyOrbit3091.check table frame0 i=true := fun i hi => span_ok total i (by omega) hi
  have v := Research.TinyOrbit3091.certify h (i := 539) (by decide +kernel)
  have hk : budget table 539=12 := by decide +kernel
  have ht : nots table 539=0 := by decide +kernel
  have he : st table frame0 539 0=roots := by decide +kernel
  simpa only [hk,ht,he] using v
end Research.SmallMono3091
namespace Research.FOrbit3091
open Research.Book3091 Research.Basis1868 Research.Cuts1868 Research.PinRows3091
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma hSigAll : span cheapSig 1568 0=true := (@span_join cheapSig 792 0 776 (@span_join cheapSig 396 0 396 (@span_join cheapSig 198 0 198 (@span_join cheapSig 88 0 110 (@span_join cheapSig 44 0 44 (@span_join cheapSig 22 0 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 44 22 (by decide +kernel) (by decide +kernel))) (@span_join cheapSig 44 88 66 (@span_join cheapSig 22 88 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 132 44 (by decide +kernel) (@span_join cheapSig 22 154 22 (by decide +kernel) (by decide +kernel))))) (@span_join cheapSig 88 198 110 (@span_join cheapSig 44 198 44 (@span_join cheapSig 22 198 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 242 22 (by decide +kernel) (by decide +kernel))) (@span_join cheapSig 44 286 66 (@span_join cheapSig 22 286 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 330 44 (by decide +kernel) (@span_join cheapSig 22 352 22 (by decide +kernel) (by decide +kernel)))))) (@span_join cheapSig 198 396 198 (@span_join cheapSig 88 396 110 (@span_join cheapSig 44 396 44 (@span_join cheapSig 22 396 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 440 22 (by decide +kernel) (by decide +kernel))) (@span_join cheapSig 44 484 66 (@span_join cheapSig 22 484 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 528 44 (by decide +kernel) (@span_join cheapSig 22 550 22 (by decide +kernel) (by decide +kernel))))) (@span_join cheapSig 88 594 110 (@span_join cheapSig 44 594 44 (@span_join cheapSig 22 594 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 638 22 (by decide +kernel) (by decide +kernel))) (@span_join cheapSig 44 682 66 (@span_join cheapSig 22 682 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 726 44 (by decide +kernel) (@span_join cheapSig 22 748 22 (by decide +kernel) (by decide +kernel))))))) (@span_join cheapSig 396 792 380 (@span_join cheapSig 198 792 198 (@span_join cheapSig 88 792 110 (@span_join cheapSig 44 792 44 (@span_join cheapSig 22 792 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 836 22 (by decide +kernel) (by decide +kernel))) (@span_join cheapSig 44 880 66 (@span_join cheapSig 22 880 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 924 44 (by decide +kernel) (@span_join cheapSig 22 946 22 (by decide +kernel) (by decide +kernel))))) (@span_join cheapSig 88 990 110 (@span_join cheapSig 44 990 44 (@span_join cheapSig 22 990 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 1034 22 (by decide +kernel) (by decide +kernel))) (@span_join cheapSig 44 1078 66 (@span_join cheapSig 22 1078 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 1122 44 (by decide +kernel) (@span_join cheapSig 22 1144 22 (by decide +kernel) (by decide +kernel)))))) (@span_join cheapSig 198 1188 182 (@span_join cheapSig 88 1188 110 (@span_join cheapSig 44 1188 44 (@span_join cheapSig 22 1188 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 1232 22 (by decide +kernel) (by decide +kernel))) (@span_join cheapSig 44 1276 66 (@span_join cheapSig 22 1276 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 1320 44 (by decide +kernel) (@span_join cheapSig 22 1342 22 (by decide +kernel) (by decide +kernel))))) (@span_join cheapSig 88 1386 94 (@span_join cheapSig 44 1386 44 (@span_join cheapSig 22 1386 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 1430 22 (by decide +kernel) (by decide +kernel))) (@span_join cheapSig 44 1474 50 (@span_join cheapSig 22 1474 22 (by decide +kernel) (by decide +kernel)) (@span_join cheapSig 22 1518 28 (by decide +kernel) (@span_join cheapSig 22 1540 6 (by decide +kernel) (by decide +kernel))))))))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma hRunAll : span (check book) 909 0=true := (@span_join (check book) 453 0 456 (@span_join (check book) 225 0 228 (@span_join (check book) 111 0 114 (@span_join (check book) 54 0 57 (@span_join (check book) 27 0 27 (@span_join (check book) 12 0 15 (@span_join (check book) 6 0 6 (@span_join (check book) 3 0 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 6 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 12 9 (@span_join (check book) 3 12 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 18 6 (by decide +kernel) (@span_join (check book) 3 21 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 12 27 15 (@span_join (check book) 6 27 6 (@span_join (check book) 3 27 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 33 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 39 9 (@span_join (check book) 3 39 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 45 6 (by decide +kernel) (@span_join (check book) 3 48 3 (by decide +kernel) (by decide +kernel)))))) (@span_join (check book) 27 54 30 (@span_join (check book) 12 54 15 (@span_join (check book) 6 54 6 (@span_join (check book) 3 54 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 60 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 66 9 (@span_join (check book) 3 66 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 72 6 (by decide +kernel) (@span_join (check book) 3 75 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 81 15 (@span_join (check book) 6 81 9 (@span_join (check book) 3 81 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 87 6 (by decide +kernel) (@span_join (check book) 3 90 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 96 9 (@span_join (check book) 3 96 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 102 6 (by decide +kernel) (@span_join (check book) 3 105 3 (by decide +kernel) (by decide +kernel))))))) (@span_join (check book) 57 111 57 (@span_join (check book) 27 111 30 (@span_join (check book) 12 111 15 (@span_join (check book) 6 111 6 (@span_join (check book) 3 111 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 117 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 123 9 (@span_join (check book) 3 123 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 129 6 (by decide +kernel) (@span_join (check book) 3 132 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 138 15 (@span_join (check book) 6 138 9 (@span_join (check book) 3 138 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 144 6 (by decide +kernel) (@span_join (check book) 3 147 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 153 9 (@span_join (check book) 3 153 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 159 6 (by decide +kernel) (@span_join (check book) 3 162 3 (by decide +kernel) (by decide +kernel)))))) (@span_join (check book) 27 168 30 (@span_join (check book) 12 168 15 (@span_join (check book) 6 168 6 (@span_join (check book) 3 168 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 174 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 180 9 (@span_join (check book) 3 180 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 186 6 (by decide +kernel) (@span_join (check book) 3 189 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 195 15 (@span_join (check book) 6 195 9 (@span_join (check book) 3 195 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 201 6 (by decide +kernel) (@span_join (check book) 3 204 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 210 9 (@span_join (check book) 3 210 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 216 6 (by decide +kernel) (@span_join (check book) 3 219 3 (by decide +kernel) (by decide +kernel)))))))) (@span_join (check book) 114 225 114 (@span_join (check book) 57 225 57 (@span_join (check book) 27 225 30 (@span_join (check book) 12 225 15 (@span_join (check book) 6 225 6 (@span_join (check book) 3 225 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 231 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 237 9 (@span_join (check book) 3 237 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 243 6 (by decide +kernel) (@span_join (check book) 3 246 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 252 15 (@span_join (check book) 6 252 9 (@span_join (check book) 3 252 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 258 6 (by decide +kernel) (@span_join (check book) 3 261 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 267 9 (@span_join (check book) 3 267 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 273 6 (by decide +kernel) (@span_join (check book) 3 276 3 (by decide +kernel) (by decide +kernel)))))) (@span_join (check book) 27 282 30 (@span_join (check book) 12 282 15 (@span_join (check book) 6 282 6 (@span_join (check book) 3 282 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 288 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 294 9 (@span_join (check book) 3 294 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 300 6 (by decide +kernel) (@span_join (check book) 3 303 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 309 15 (@span_join (check book) 6 309 9 (@span_join (check book) 3 309 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 315 6 (by decide +kernel) (@span_join (check book) 3 318 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 324 9 (@span_join (check book) 3 324 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 330 6 (by decide +kernel) (@span_join (check book) 3 333 3 (by decide +kernel) (by decide +kernel))))))) (@span_join (check book) 57 339 57 (@span_join (check book) 27 339 30 (@span_join (check book) 12 339 15 (@span_join (check book) 6 339 6 (@span_join (check book) 3 339 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 345 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 351 9 (@span_join (check book) 3 351 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 357 6 (by decide +kernel) (@span_join (check book) 3 360 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 366 15 (@span_join (check book) 6 366 9 (@span_join (check book) 3 366 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 372 6 (by decide +kernel) (@span_join (check book) 3 375 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 381 9 (@span_join (check book) 3 381 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 387 6 (by decide +kernel) (@span_join (check book) 3 390 3 (by decide +kernel) (by decide +kernel)))))) (@span_join (check book) 27 396 30 (@span_join (check book) 12 396 15 (@span_join (check book) 6 396 6 (@span_join (check book) 3 396 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 402 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 408 9 (@span_join (check book) 3 408 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 414 6 (by decide +kernel) (@span_join (check book) 3 417 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 423 15 (@span_join (check book) 6 423 9 (@span_join (check book) 3 423 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 429 6 (by decide +kernel) (@span_join (check book) 3 432 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 438 9 (@span_join (check book) 3 438 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 444 6 (by decide +kernel) (@span_join (check book) 3 447 3 (by decide +kernel) (by decide +kernel))))))))) (@span_join (check book) 228 453 228 (@span_join (check book) 114 453 114 (@span_join (check book) 57 453 57 (@span_join (check book) 27 453 30 (@span_join (check book) 12 453 15 (@span_join (check book) 6 453 6 (@span_join (check book) 3 453 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 459 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 465 9 (@span_join (check book) 3 465 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 471 6 (by decide +kernel) (@span_join (check book) 3 474 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 480 15 (@span_join (check book) 6 480 9 (@span_join (check book) 3 480 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 486 6 (by decide +kernel) (@span_join (check book) 3 489 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 495 9 (@span_join (check book) 3 495 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 501 6 (by decide +kernel) (@span_join (check book) 3 504 3 (by decide +kernel) (by decide +kernel)))))) (@span_join (check book) 27 510 30 (@span_join (check book) 12 510 15 (@span_join (check book) 6 510 6 (@span_join (check book) 3 510 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 516 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 522 9 (@span_join (check book) 3 522 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 528 6 (by decide +kernel) (@span_join (check book) 3 531 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 537 15 (@span_join (check book) 6 537 9 (@span_join (check book) 3 537 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 543 6 (by decide +kernel) (@span_join (check book) 3 546 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 552 9 (@span_join (check book) 3 552 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 558 6 (by decide +kernel) (@span_join (check book) 3 561 3 (by decide +kernel) (by decide +kernel))))))) (@span_join (check book) 57 567 57 (@span_join (check book) 27 567 30 (@span_join (check book) 12 567 15 (@span_join (check book) 6 567 6 (@span_join (check book) 3 567 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 573 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 579 9 (@span_join (check book) 3 579 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 585 6 (by decide +kernel) (@span_join (check book) 3 588 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 594 15 (@span_join (check book) 6 594 9 (@span_join (check book) 3 594 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 600 6 (by decide +kernel) (@span_join (check book) 3 603 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 609 9 (@span_join (check book) 3 609 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 615 6 (by decide +kernel) (@span_join (check book) 3 618 3 (by decide +kernel) (by decide +kernel)))))) (@span_join (check book) 27 624 30 (@span_join (check book) 12 624 15 (@span_join (check book) 6 624 6 (@span_join (check book) 3 624 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 630 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 636 9 (@span_join (check book) 3 636 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 642 6 (by decide +kernel) (@span_join (check book) 3 645 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 651 15 (@span_join (check book) 6 651 9 (@span_join (check book) 3 651 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 657 6 (by decide +kernel) (@span_join (check book) 3 660 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 666 9 (@span_join (check book) 3 666 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 672 6 (by decide +kernel) (@span_join (check book) 3 675 3 (by decide +kernel) (by decide +kernel)))))))) (@span_join (check book) 114 681 114 (@span_join (check book) 57 681 57 (@span_join (check book) 27 681 30 (@span_join (check book) 12 681 15 (@span_join (check book) 6 681 6 (@span_join (check book) 3 681 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 687 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 693 9 (@span_join (check book) 3 693 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 699 6 (by decide +kernel) (@span_join (check book) 3 702 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 708 15 (@span_join (check book) 6 708 9 (@span_join (check book) 3 708 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 714 6 (by decide +kernel) (@span_join (check book) 3 717 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 723 9 (@span_join (check book) 3 723 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 729 6 (by decide +kernel) (@span_join (check book) 3 732 3 (by decide +kernel) (by decide +kernel)))))) (@span_join (check book) 27 738 30 (@span_join (check book) 12 738 15 (@span_join (check book) 6 738 6 (@span_join (check book) 3 738 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 744 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 750 9 (@span_join (check book) 3 750 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 756 6 (by decide +kernel) (@span_join (check book) 3 759 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 765 15 (@span_join (check book) 6 765 9 (@span_join (check book) 3 765 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 771 6 (by decide +kernel) (@span_join (check book) 3 774 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 780 9 (@span_join (check book) 3 780 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 786 6 (by decide +kernel) (@span_join (check book) 3 789 3 (by decide +kernel) (by decide +kernel))))))) (@span_join (check book) 57 795 57 (@span_join (check book) 27 795 30 (@span_join (check book) 12 795 15 (@span_join (check book) 6 795 6 (@span_join (check book) 3 795 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 801 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 807 9 (@span_join (check book) 3 807 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 813 6 (by decide +kernel) (@span_join (check book) 3 816 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 822 15 (@span_join (check book) 6 822 9 (@span_join (check book) 3 822 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 828 6 (by decide +kernel) (@span_join (check book) 3 831 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 837 9 (@span_join (check book) 3 837 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 843 6 (by decide +kernel) (@span_join (check book) 3 846 3 (by decide +kernel) (by decide +kernel)))))) (@span_join (check book) 27 852 30 (@span_join (check book) 12 852 15 (@span_join (check book) 6 852 6 (@span_join (check book) 3 852 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 858 3 (by decide +kernel) (by decide +kernel))) (@span_join (check book) 6 864 9 (@span_join (check book) 3 864 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 870 6 (by decide +kernel) (@span_join (check book) 3 873 3 (by decide +kernel) (by decide +kernel))))) (@span_join (check book) 15 879 15 (@span_join (check book) 6 879 9 (@span_join (check book) 3 879 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 885 6 (by decide +kernel) (@span_join (check book) 3 888 3 (by decide +kernel) (by decide +kernel)))) (@span_join (check book) 6 894 9 (@span_join (check book) 3 894 3 (by decide +kernel) (by decide +kernel)) (@span_join (check book) 3 900 6 (by decide +kernel) (@span_join (check book) 3 903 3 (by decide +kernel) (by decide +kernel))))))))))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma endSlow : check book 909=true := by
  apply regroup (by decide +kernel)
  intro x y xy len
  have n : (state book 909).length=9 := by decide +kernel
  rw [n] at len
  have x9 : x<9 := by omega
  interval_cases x <;> interval_cases y <;> first | omega | decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma allStates : span (check book) 910 0=true := @span_join (check book) 909 0 1 hRunAll (show span (check book) 1 909=true by simpa [span] using endSlow)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma final : excluded 11 canonicalInputs := by
  have h := proof (b := book) (by decide +kernel) (fun i hi => by exact of_decide_eq_true (span_ok (p := fun i => decide (book.shifts.at' i<4)) (n := 910) (i := 0) (by decide +kernel) i (by omega) hi)) (fun j hj => realize j hj (span_ok hSigAll j (by omega) hj)) (fun i hi => span_ok allStates i (by omega) hi) (i := 909) (by decide +kernel)
  have l : book.levels.at' 909=11 := by decide +kernel
  have eq : state book 909=canonicalInputs := by decide +kernel
  rwa [l,eq] at h
end Research.FOrbit3091
end PEqualNP.Outside.L_meta_3091_aux
theorem PEqualNP.Outside.L_meta_3091 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → (2 : ℕ) ≤ List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := PEqualNP.Outside.L_meta_3091_aux.Research.Full3091.combined PEqualNP.Outside.L_meta_3091_aux.Research.FOrbit3091.final PEqualNP.Outside.L_meta_3091_aux.Research.SmallMono3091.done
