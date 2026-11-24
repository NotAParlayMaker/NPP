import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
abbrev Sig := Nat × Nat
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def top : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def bnot (x : Nat) : Nat := x ^^^ top
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def zero : Sig := (0, 0)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def one : Sig := (top, top)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def target : Sig := (top, 0)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def unionSep (d : Bool) : List Sig → Nat
  | [] => 0
  | a :: l => sep d a ||| unionSep d l
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def Valid1 (x : Nat) : Prop := ∀ j, 414 ≤ j → x.testBit j = false
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma top_eq_pow : top = 2 ^ 207 * 2 ^ 207 - 1 := by decide
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 414) := by
  rw [top_eq_pow]; exact pow_add_testBit 207 207 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 414 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma testBit_bnot_lt (x : Nat) {j : Nat} (hj : j < 414) :
    (bnot x).testBit j = !(x.testBit j) := by
  simp [bnot, Nat.testBit_xor, testBit_top, hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 414 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 414 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_xor {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ^^^ y) := fun j hj => by
  rw [Nat.testBit_xor, hx j hj, hy j hj]; rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 207 * 2 ^ 207 := by
    have hp : 0 < 2 ^ 207 * 2 ^ 207 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_sep {d : Bool} {a : Sig} (ha : Valid a) : Valid1 (sep d a) := by
  cases d
  · exact valid1_and ha.1
  · exact valid1_xor ha.1 ha.2
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_unionSep {d : Bool} {v : List Sig} (hv : ∀ a ∈ v, Valid a) : Valid1 (unionSep d v) := by
  induction v with
  | nil => exact valid1_zero
  | cons a l ih =>
    exact valid1_or (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sep_binary (t d : Bool) {a b : Sig} (_ha : Valid a) (_hb : Valid b) (i : Nat) (hi : i < 414)
    (h : (sep t (bin d a b)).testBit i = true) :
    (sep t a).testBit i = true ∨ (sep t b).testBit i = true := by
  cases t <;> cases d <;>
    simp only [sep, bin, Bool.false_eq_true, ite_true, ite_false, Nat.testBit_xor,
      Nat.testBit_and, Nat.testBit_or, testBit_bnot_lt _ hi] at h ⊢ <;>
    revert h <;>
    cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> simp
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sep_weaken (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) a).testBit i = true) : (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simpa [ht] using h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).testBit i = true ↔ ∃ a ∈ v, (sep d a).testBit i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih =>
    simp only [unionSep, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l ++ r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep, ih, Nat.or_assoc]
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def bit (side : Bool) (i : Fin 414) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
end PEqualNP.Outside.L_meta_3400_aux.Basis1868


namespace PEqualNP.Outside.L_meta_3400_aux.Conflict1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
abbrev I := Fin 414
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
abbrev P (a : Sig) (p : I) := bit true p a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
abbrev N (a : Sig) (n : I) := bit false n a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def D (p n : I) (a : Sig) : Prop := P a p ≠ N a n
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def op (d x y : Bool) : Bool := if d then x || y else x && y

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bop (s i d a b) : bit s i (bin d a b) = op d (bit s i a) (bit s i b) := bit_bin s i d a b
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma d_bin {d p n a b} (hd : D p n (bin d a b)) : D p n a ∨ D p n b := by
  by_contra! hn
  apply hd
  unfold P N
  rw [bop,bop]
  exact congrArg₂ (op d) (not_ne_iff.mp hn.1) (not_ne_iff.mp hn.2)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma d_neg {p n a} (hv : Valid a) : D p n (neg a) ↔ D p n a := by
  unfold D P N
  rw [bit_neg _ _ hv,bit_neg _ _ hv]
  cases bit true p a <;> cases bit false n a <;> decide

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def Unique (p n : I) (S : Finset Sig) (a : Sig) := ∀ c ∈ S, D p n c → c = a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def Mark (p n : I) (S : Finset Sig) (a : Sig) :=
  D p n a ∧ (∃ m, Unique p m S a) ∧ ∃ q, Unique q n S a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def Edge (S : Finset Sig) (a b : Sig) :=
  ∃ p n, Mark p n S a ∧ Mark p n S b

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma unique_diff {k t z U p n} (h : Live k t (insert z U)) (hu : ∀ c ∈ U, ¬ D p n c) :
    D p n z := by
  obtain ⟨c,hc,hd⟩ := pair_sep h p n
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hd
  · exact (hu c hc hd).elim

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma transUnique {p n a z S U} (h : Unique p n S a) (hu : U ⊆ S) (ha : a ∉ U) :
    Unique p n (insert z U) z := by
  intro c hc hd
  rcases Finset.mem_insert.mp hc with h | hc
  · exact h
  · exact (ha (h c (hu hc) hd ▸ hc)).elim

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_unique_keep {d p n a b c U} (h : Unique p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Unique p n (insert (bin d a b) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · rcases d_bin hd with h' | h'
    · exact (hna (h _ (Finset.mem_insert_self _ _) h').symm).elim
    · exact (hnb (h _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) h').symm).elim
  · exact h _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)) hd

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_unique_keep {p n a c U} (h : Unique p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Unique p n (insert (neg a) U) c := by
  intro z hz hd
  rcases Finset.mem_insert.mp hz with rfl | hu
  · exact (hna (h _ (Finset.mem_insert_self _ _) ((d_neg hv).mp hd)).symm).elim
  · exact h _ (Finset.mem_insert_of_mem hu) hd

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_mark_keep {d p n a b c U} (h : Mark p n (insert a (insert b U)) c)
    (hna : c ≠ a) (hnb : c ≠ b) : Mark p n (insert (bin d a b) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,bin_unique_keep hm hna hnb⟩,q,bin_unique_keep hq hna hnb⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_mark_keep {p n a c U} (h : Mark p n (insert a U) c)
    (hna : c ≠ a) (hv : Valid a) : Mark p n (insert (neg a) U) c := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  exact ⟨hd,⟨m,neg_unique_keep hm hna hv⟩,q,neg_unique_keep hq hna hv⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_mark_move {p n a U} (h : Mark p n (insert a U) a)
    (ha : a ∉ U) (hv : Valid a) : Mark p n (insert (neg a) U) (neg a) := by
  obtain ⟨hd,⟨m,hm⟩,q,hq⟩ := h
  have sub : U ⊆ insert a U := Finset.subset_insert _ _
  exact ⟨(d_neg hv).mpr hd,⟨m,transUnique hm sub ha⟩,q,transUnique hq sub ha⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma mix : ∀ (d ap an bp bn al ar : Bool), ap ≠ an →
    op d ap bp ≠ op d al bp → op d ar bn ≠ op d an bn →
    bp = bn ∧ op d ap bp ≠ op d an bn := by decide +kernel

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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


set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def Colored (S : Finset Sig) (k : Nat) :=
  ∃ f : Sig → Nat, (∀ x ∈ S, f x < k) ∧
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Edge S x y → f x ≠ f y

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma bin_swap (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,Nat.and_comm,Nat.or_comm]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

end PEqualNP.Outside.L_meta_3400_aux.Conflict1868

namespace PEqualNP.Outside.L_meta_3400_aux.Grid1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
abbrev Ix := Fin 256
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def coord (side : Bool) (i : Nat) := if side then i / 16 * 16 else i % 16
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def ix (s : Bool) (i : Ix) : Fin 414 := ⟨coord s i.val,by unfold coord; cases s <;> have := i.isLt <;> simp <;> omega⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def hop (n mask x : Nat) : Nat := (x ||| ((x <<< n) &&& (mask <<< n))) ||| ((x >>> n) &&& mask)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def safe (s : Bool) (n mask : Nat) : Prop :=
  ∀ i : Ix, (((mask <<< n).testBit i.val = true → n ≤ i.val ∧ coord s (i.val-n) = coord s i.val) ∧
    (mask.testBit i.val = true → i.val+n < 256 ∧ coord s (i.val+n) = coord s i.val))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
instance (s n m) : Decidable (safe s n m) := by unfold safe; infer_instance

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def m0 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma s0 : safe true 1 m0 := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def m1 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma s1 : safe true 2 m1 := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def m2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma s2 : safe true 4 m2 := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def m3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma s3 : safe true 8 m3 := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def m4 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma s4 : safe false 16 m4 := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def m5 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma s5 : safe false 32 m5 := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def m6 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma s6 : safe false 64 m6 := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def m7 : Nat := 0xffffffffffffffffffffffffffffffff
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma s7 : safe false 128 m7 := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def row (x : Nat) := (hop 8 m3 (hop 4 m2 (hop 2 m1 (hop 1 m0 x))))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma row_sound (x : Nat) (gain : Nat → Prop) (base : ∀ i : Ix, x.testBit i.val = true → gain (coord true i.val)) (i : Ix) (h : (row x).testBit i.val = true) : gain (coord true i.val) := by
  exact (hop_sound s3 gain (hop_sound s2 gain (hop_sound s1 gain (hop_sound s0 gain base)))) i h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def col (x : Nat) := (hop 128 m7 (hop 64 m6 (hop 32 m5 (hop 16 m4 x))))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma col_sound (x : Nat) (gain : Nat → Prop) (base : ∀ i : Ix, x.testBit i.val = true → gain (coord false i.val)) (i : Ix) (h : (col x).testBit i.val = true) : gain (coord false i.val) := by
  exact (hop_sound s7 gain (hop_sound s6 gain (hop_sound s5 gain (hop_sound s4 gain base)))) i h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def unit (side : Bool) : Nat := if side then 0x1000100010001000100010001000100010001000100010001000100010001 else 0xffff
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma unit_coord : ∀ (s : Bool) (i : Ix), (unit s).testBit i.val = true → coord s i.val = i.val := by decide +kernel

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def pick (s yes : Bool) (a : Sig) := let bits := if s then a.1 else a.2
  (if yes then bits else bits ^^^ top) &&& unit s

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def spread (s yes : Bool) (a : Sig) :=
  if s then row (pick s yes a) else col (pick s yes a)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

end PEqualNP.Outside.L_meta_3400_aux.Grid1868

namespace PEqualNP.Outside.L_meta_3400_aux.Check1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Grid1868 PEqualNP.Outside.L_meta_3400_aux.Conflict1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def xmask (a : Sig) : Nat :=
  ((spread true true a) &&& (spread false false a)) |||
  ((spread true false a) &&& (spread false true a))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def same (a : Sig) : Nat :=
  ((spread true true a) &&& (spread false true a)) |||
  ((spread true false a) &&& (spread false false a))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma xmask_sound {a} (i : Ix) (h : (xmask a).testBit i.val = true) : D (ix true i) (ix false i) a := by
  simp only [xmask,Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨hp,hn⟩ | ⟨hp,hn⟩
  · exact fun eq => Bool.noConfusion ((spread_sound _ _ _ _ hp).symm.trans (eq.trans (spread_sound _ _ _ _ hn)))
  · exact fun eq => Bool.noConfusion ((spread_sound _ _ _ _ hp).symm.trans (eq.trans (spread_sound _ _ _ _ hn)))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma same_sound {a} (i : Ix) (h : (same a).testBit i.val = true) : ¬ D (ix true i) (ix false i) a := by
  simp only [same,Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨hp,hn⟩ | ⟨hp,hn⟩ <;>
    exact fun eq => eq ((spread_sound _ _ _ _ hp).trans (spread_sound _ _ _ _ hn).symm)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
abbrev Signs := List (Sig × Nat)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def allSame (a : Sig) : Signs → Nat
  | [] => 2^256-1
  | (c,m)::cs => if c = a then allSame a cs else m &&& allSame a cs

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def marks (v : Signs) (a : Sig) :=
  let uniq := allSame a v
  (xmask a &&& row uniq) &&& col uniq

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def entries (v : List Sig) : Signs :=
  let signs := v.map fun a => (a,same a)
  v.map fun a => (a,(2^256-1) &&& marks signs a)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma entries_fst (v : List Sig) : (entries v).map Prod.fst = v := by simp [entries,Function.comp_def]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma eBound {v : List Sig} {a} (ha : a ∈ entries v) {i : Nat} (h : a.2.testBit i = true) : i < 256 := by
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
  simp only [Nat.testBit_and,Bool.and_eq_true] at h
  have q := h.1
  rw [Nat.testBit_two_pow_sub_one] at q
  exact of_decide_eq_true q

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma eEdge {v : List Sig} {x y} (hx : x ∈ entries v) (hy : y ∈ entries v)
    (h : x.2 &&& y.2 ≠ 0) : Edge v.toFinset x.1 y.1 := by
  obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero h
  rw [Nat.testBit_and,Bool.and_eq_true] at hi
  let j : Ix := ⟨i,eBound hx hi.1⟩
  exact ⟨ix true j,ix false j,eMark hx j hi.1,eMark hy j hi.2⟩

end PEqualNP.Outside.L_meta_3400_aux.Check1868


namespace PEqualNP.Outside.L_meta_3400_aux.ColorSearch1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Conflict1868 PEqualNP.Outside.L_meta_3400_aux.Check1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def paint (n : Nat) : Signs → (Nat → Nat) → Bool
  | [], _ => true
  | x::xs, bins =>
    (List.range n).any fun i => ((bins i &&& x.2) == 0) &&
      paint n xs (fun j => if i=j then bins j ||| x.2 else bins j)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

end PEqualNP.Outside.L_meta_3400_aux.ColorSearch1868

namespace PEqualNP.Outside.L_meta_3400_aux.Free1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Conflict1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def flip (s : Bool) (a : Sig) := if s then neg a else a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def sign (a : Sig) := bit true 0 a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def can (a : Sig) := flip (sign a) a

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg2 (a : Sig) : neg (neg a) = a := by
  obtain ⟨u,v⟩ := a
  simp [neg,bnot,Nat.xor_assoc]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flip2 (s a) : flip s (flip s a) = a := by cases s <;> simp [flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipFalse (a) : flip false a = a := rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipTrue (a) : flip true a = neg a := rfl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma vf {a} (s) (h : Valid a) : Valid (flip s a) := by cases s <;> first | exact h | exact valid_neg h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma vc {a} (h : Valid a) : Valid (can a) := vf _ h

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sign_neg {a} (h : Valid a) : sign (neg a) = !sign a := bit_neg true 0 h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_neg {a} (v : Valid a) : can (neg a) = can a := by
  unfold can
  rw [sign_neg v]
  cases sign a <;> simp [flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_flip {a} (s) (v : Valid a) : can (flip s a) = can a := by
  cases s with
  | false => rfl
  | true => exact can_neg v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can2 {a} (v : Valid a) : can (can a) = can a := can_flip _ v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma recover (a) : flip (sign a) (can a) = a := flip2 _ _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma ncan (a) : flip (!sign a) (can a) = neg a := by
  unfold can
  cases sign a <;> simp [flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_zero : can zero = zero := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_one : can one = zero := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipProper (s) {a} (ha : proper a) : proper (flip s a) := by
  cases s
  · exact ha
  · refine ⟨valid_neg ha.1,?_,?_⟩
    · intro h
      exact ha.2.2 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.1))
    · intro h
      exact ha.2.1 ((neg2 a).symm.trans ((congrArg neg h).trans neg_laws.2))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma canProper {a} (h : proper a) : proper (can a) := flipProper _ h

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma sameClass {a b} (h : can a = can b) : a = b ∨ a = neg b := by
  have ha := recover a
  rw [h] at ha
  unfold can at ha
  cases ea : sign a <;> cases eb : sign b <;> simp [ea,eb,flip,neg2] at ha <;> aesop

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def blend (d s t : Bool) (a b : Sig) := can (bin d (flip s a) (flip t b))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
inductive BL : Nat → Finset Sig → Prop where
  | stop : BL 0 {can target}
  | step {k U a b d s t} (ha : proper a) (hb : proper b)
      (ac : can a = a) (bc : can b = b) (hab : a ≠ b)
      (fresh : blend d s t a b ∉ insert a (insert b U))
      (tail : BL k (insert (blend d s t a b) U)) : BL (k+1) (insert a (insert b U))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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


set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma BL.forms {k S} (l : BL k S) : ∀ a ∈ S, proper a ∧ can a = a := by
  induction l with
  | stop => simpa using And.intro (canProper target_proper) (can2 valid_target)
  | step ha hb ca cb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨⟨ha,ca⟩,⟨hb,cb⟩,fun a h => ih _ (Finset.mem_insert_of_mem h)⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma neg_ne {a} (hv : Valid a) : neg a ≠ a := by
  intro h
  have eq := sign_neg hv
  rw [h] at eq
  cases e : sign a <;> simp [e] at eq

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def Present (n : Nat) (S : Finset Sig) := ∃ t, Live (n+t) t S

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma insertFlip {n a U} (s : Bool) (ha : proper a)
    (hf : s = true → neg a ∉ insert a U) (h : Present n (insert (flip s a) U)) :
    Present n (insert a U) := by
  cases s
  · exact h
  · obtain ⟨t,hl⟩ := h
    exact ⟨t+1,by simpa [Nat.add_assoc] using Live.unary ha (hf rfl) hl⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma freeColors {k S} (h : BL k S) : ∃ n, Colored S n ∧ n+S.card ≤ k+2 := by
  obtain ⟨t,hl⟩ := h.expand
  obtain ⟨n,c,b⟩ := live_colored hl
  exact ⟨n,c,by omega⟩

end PEqualNP.Outside.L_meta_3400_aux.Free1868

namespace PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Conflict1868 PEqualNP.Outside.L_meta_3400_aux.Check1868 PEqualNP.Outside.L_meta_3400_aux.Free1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma negFlip (u : Bool) (a : Sig) : neg (flip u a) = flip (!u) a := by
  cases u <;> simp [PEqualNP.Outside.L_meta_3400_aux.Free1868.flip,neg2]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma deM {a b} (ha : Valid a) (hb : Valid b) :
    neg (bin true a b) = bin false (neg a) (neg b) := by
  apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i
  · change (bnot (a.1 ||| b.1)).testBit i = ((bnot a.1) &&& (bnot b.1)).testBit i
    simp only [testBit_bnot (valid1_or ha.1 hb.1),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.1,testBit_bnot hb.1]
    by_cases e : i < 414 <;> simp [e]
  · change (bnot (a.2 ||| b.2)).testBit i = ((bnot a.2) &&& (bnot b.2)).testBit i
    simp only [testBit_bnot (valid1_or ha.2 hb.2),Nat.testBit_or,Nat.testBit_and,testBit_bnot ha.2,testBit_bnot hb.2]
    by_cases e : i < 414 <;> simp [e]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flipBlend {a b} (ha : Valid a) (hb : Valid b) (d s t : Bool) :
    ∃ u v, blend false u v a b = blend d s t a b := by
  cases d
  · exact ⟨s,t,rfl⟩
  · refine ⟨!s,!t,?_⟩
    unfold blend
    rw [← negFlip,← negFlip,← deM (vf s ha) (vf t hb),can_neg (valid_bin (vf s ha) (vf t hb))]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma blend_symm (d s t a b) : blend d s t a b = blend d t s b a := by unfold blend; rw [bin_comm]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def keep (a b : Sig) (u v : Bool) (c : Sig) := (c != a || u) && (c != b || v)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def next (v : List Sig) (a b z : Sig) (l r : Bool) := z :: v.filter (keep a b l r)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def oneB (v : List Sig) (go : List Sig → Bool) (a b : Sig) (s t : Bool) :=
  let z := blend false s t a b
  z != zero && !(v.contains z) &&
  ([false,true].any fun l => [false,true].any fun r => go (next v a b z l r))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def pairB (v : List Sig) (go : List Sig → Bool) (a b : Sig) :=
  [false,true].any fun s => [false,true].any fun t => oneB v go a b s t

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def colorB (k : Nat) (v : List Sig) := PEqualNP.Outside.L_meta_3400_aux.ColorSearch1868.paint (k+2-v.length) (entries v) (fun _ => 0)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma colorB_sound {k m v} (hm : m ≤ k) (h : BL m v.toFinset) (nd : v.Nodup) :
    colorB k v = true := by
  obtain ⟨n,⟨f,b,c⟩,lim⟩ := freeColors h
  have mem {x} (hx : x ∈ entries v) : x.1 ∈ v.toFinset := by
    rw [←entries_fst v]; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,hx,rfl⟩)
  apply PEqualNP.Outside.L_meta_3400_aux.ColorSearch1868.paint_ok _ f
  · rwa [entries_fst]
  · intro x hx
    have := b _ (mem hx)
    rw [List.toFinset_card_of_nodup nd] at lim
    omega
  · simp
  · intro x hx y hy hne eq
    by_contra bb
    exact c _ (mem hx) _ (mem hy) hne (eEdge hx hy bb) eq

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def baseTest (v : List Sig) := v == [can target]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def fs : Nat → List Sig → Bool
  | 0, v => baseTest v
  | k+1, v =>
    baseTest v || (v.length ≤ k+2 && unionSep true v == top && colorB (k+1) v &&
      scanPairs (pairB v (fs k)) v)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma anyBool {f : Bool → Bool} (a) (h : f a = true) : [false,true].any f = true :=
  List.any_eq_true.mpr ⟨a,by cases a <;> simp,h⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma fs_sound {k S} (l : BL k S) (m : Nat) (hm : k ≤ m) (v : List Sig) (nd : v.Nodup)
    (rep : v.toFinset = S) : fs m v = true := by
  induction l generalizing m v with
  | stop =>
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v
    cases m <;> simp [fs,baseTest]
  | @step j U a b d s t ha hb ca cb hab fresh tail ih =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    let z := blend d s t a b
    have form : BL (j+1) v.toFinset := rep ▸ BL.step ha hb ca cb hab fresh tail
    have card := freeColors form
    obtain ⟨n,hn,lim⟩ := card
    obtain ⟨_,hl⟩ := form.expand
    have hc := live_size hl
    rw [List.toFinset_card_of_nodup nd] at hc
    have len : v.length ≤ m+2 := by omega
    rw [fs]
    apply Bool.or_eq_true_iff.mpr; right
    simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    refine ⟨⟨⟨len,coverageB form⟩,colorB_sound hm form nd⟩,?_⟩
    have va : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (u w : Bool) (id : blend false u w x y = z)
        (eqS : v.toFinset = insert x (insert y U)) : pairB v (fs m) x y = true := by
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
      exact ih m (by omega) _ nw pw
    obtain ⟨u,w,id⟩ := flipBlend ha.1 hb.1 d s t
    apply scanPairs_complete _ va vb hab
    · exact yes a b u w id rep
    · exact yes b a w u ((blend_symm false w u b a).trans id) (by rwa [Finset.insert_comm b a])

end PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868

namespace PEqualNP.Outside.L_meta_3400_aux.Part1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Conflict1868 PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def walk : List Sig → Nat → Nat → Sig
  | [],p,n => if p=0 || n=0 then zero else (p,n)
  | a::v,p,n =>
    if p=0 || n=0 then zero else
    let hi := walk v (p &&& a.1) (n &&& a.2)
    let lo := walk v (p &&& bnot a.1) (n &&& bnot a.2)
    (hi.1 ||| lo.1,hi.2 ||| lo.2)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def Indist (p n : I) (v : List Sig) := ∀ a ∈ v, ¬ D p n a

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def Admits (v : List Sig) (u w : Nat) (ans : Sig) :=
  (∀ p : I, ans.1.testBit p.val = true → u.testBit p.val = true ∧
    ∃ n : I, w.testBit n.val = true ∧ Indist p n v) ∧
  (∀ n : I, ans.2.testBit n.val = true → w.testBit n.val = true ∧
    ∃ p : I, u.testBit p.val = true ∧ Indist p n v)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma admZero (v p n) : Admits v p n zero := by simp [Admits,zero]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma findBit {p} (vp : Valid1 p) (hp : p ≠ 0) : ∃ i : I, p.testBit i.val = true := by
  obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero hp
  have bound : i < 414 := by by_contra hh; rw [vp i (by omega)] at hi; contradiction
  exact ⟨⟨i,bound⟩,hi⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma combine {u w p n a v} (ha : Valid a)
    (hi : Admits v (p &&& a.1) (n &&& a.2) u)
    (lo : Admits v (p &&& bnot a.1) (n &&& bnot a.2) w) :
    Admits (a::v) p n (u.1 ||| w.1,u.2 ||| w.2) := by
  have add (i j : I) (ep : a.1.testBit i.val = a.2.testBit j.val) (old : Indist i j v) :
      Indist i j (a::v) := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hv
    · exact fun dh => dh ep
    · exact old _ hv
  constructor
  · intro i hh
    rw [Nat.testBit_or,Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · obtain ⟨h1,j,h2,old⟩ := hi.1 i hh
      rw [Nat.testBit_and,Bool.and_eq_true] at h1 h2
      exact ⟨h1.1,j,h2.1,add i j (h1.2.trans h2.2.symm) old⟩
    · obtain ⟨h1,j,h2,old⟩ := lo.1 i hh
      rw [Nat.testBit_and,Bool.and_eq_true] at h1 h2
      have ep : a.1.testBit i.val = false := by simpa [testBit_bnot ha.1,i.isLt] using h1.2
      have en : a.2.testBit j.val = false := by simpa [testBit_bnot ha.2,j.isLt] using h2.2
      exact ⟨h1.1,j,h2.1,add i j (ep.trans en.symm) old⟩
  · intro j hh
    rw [Nat.testBit_or,Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · obtain ⟨h2,i,h1,old⟩ := hi.2 j hh
      rw [Nat.testBit_and,Bool.and_eq_true] at h1 h2
      exact ⟨h2.1,i,h1.1,add i j (h1.2.trans h2.2.symm) old⟩
    · obtain ⟨h2,i,h1,old⟩ := lo.2 j hh
      rw [Nat.testBit_and,Bool.and_eq_true] at h1 h2
      have ep : a.1.testBit i.val = false := by simpa [testBit_bnot ha.1,i.isLt] using h1.2
      have en : a.2.testBit j.val = false := by simpa [testBit_bnot ha.2,j.isLt] using h2.2
      exact ⟨h2.1,i,h1.1,add i j (ep.trans en.symm) old⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma walk_ok (v : List Sig) (hv : ∀ a ∈ v, Valid a) (p n : Nat) (hp : Valid1 p) (hn : Valid1 n) :
    Admits v p n (walk v p n) := by
  induction v generalizing p n with
  | nil =>
    by_cases h : p=0 ∨ n=0
    · simpa [walk,h] using admZero [] p n
    · obtain ⟨i,hi⟩ := findBit hp (not_or.mp h).1
      obtain ⟨j,hj⟩ := findBit hn (not_or.mp h).2
      simp only [walk,Bool.or_eq_true,decide_eq_true_eq,h,↓reduceIte]
      exact ⟨fun i' hx => ⟨hx,j,hj,by simp [Indist]⟩, fun j' hx => ⟨hx,i,hi,by simp [Indist]⟩⟩
  | cons a v ih =>
    by_cases h : p=0 ∨ n=0
    · simpa [walk,h] using admZero (a::v) p n
    · simp only [walk,Bool.or_eq_true,decide_eq_true_eq,h,↓reduceIte]
      have va := hv a (List.mem_cons_self ..)
      apply combine va
      · exact ih (fun c hc => hv c (List.mem_cons_of_mem _ hc)) _ _ (valid1_and hp) (valid1_and hn)
      · exact ih (fun c hc => hv c (List.mem_cons_of_mem _ hc)) _ _ (valid1_and hp) (valid1_and hn)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma noCollision {k v} (h : BL k v.toFinset) : (walk v top top).1 &&& top = 0 := by
  have all : ∀ a ∈ v, Valid a := fun a ha => (h.forms _ (List.mem_toFinset.mpr ha)).1.1
  have wo := walk_ok v all top top valid1_top valid1_top
  by_contra hn
  obtain ⟨j,hj⟩ := Nat.exists_testBit_of_ne_zero hn
  rw [Nat.testBit_and,Bool.and_eq_true,testBit_top,decide_eq_true_eq] at hj
  let p : I := ⟨j,hj.2⟩
  obtain ⟨_,n,_,ind⟩ := wo.1 p hj.1
  obtain ⟨t,l⟩ := h.expand
  obtain ⟨a,ha,hd⟩ := pair_sep l p n
  exact ind a (List.mem_toFinset.mp ha) hd

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
structure Profile where
  sig : Sig
  p0 : Nat
  p1 : Nat
  n0 : Nat
  n1 : Nat

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def profile (v : List Sig) (a : Sig) : Profile :=
  let masks := walk (v.erase a) top top
  ⟨a,masks.1 &&& bnot a.1,masks.1 &&& a.1,masks.2 &&& bnot a.2,masks.2 &&& a.2⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def prow (r : Profile) (truth : Bool) := if truth then r.p1 else r.p0
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def nrow (r : Profile) (truth : Bool) := if truth then r.n1 else r.n0
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def overlap (x y : Nat) := (x &&& y &&& top) != 0
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def clash (x y : Profile) : Bool :=
  (overlap x.p1 y.p1 && overlap x.n0 y.n0) ||
  (overlap x.p1 y.p0 && overlap x.n0 y.n1) ||
  (overlap x.p0 y.p1 && overlap x.n1 y.n0) ||
  (overlap x.p0 y.p0 && overlap x.n1 y.n1)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma overlap_yes {x y} (o : overlap x y = true) : ∃ i : I, x.testBit i.val = true ∧ y.testBit i.val = true := by
  simp only [overlap,bne_iff_ne] at o
  obtain ⟨i,h⟩ := Nat.exists_testBit_of_ne_zero o
  simp only [Nat.testBit_and,Bool.and_eq_true,testBit_top,decide_eq_true_eq] at h
  exact ⟨⟨i,h.2⟩,h.1⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma profile_mark {v} (val : ∀ a ∈ v, Valid a) {a} (ha : a ∈ v) (p n : I) (pol : Bool)
    (hp : (prow (profile v a) pol).testBit p.val = true)
    (hn : (nrow (profile v a) (!pol)).testBit n.val = true) : Mark p n v.toFinset a := by
  have ok := walk_ok (v.erase a) (fun c hc => val c (List.mem_of_mem_erase hc)) top top valid1_top valid1_top
  have unique {p n} (d : Indist p n (v.erase a)) : Unique p n v.toFinset a := by
    intro c hc hd
    by_contra ne
    exact d c ((List.mem_erase_of_ne ne).mpr (List.mem_toFinset.mp hc)) hd
  have mk (hp' : (walk (v.erase a) top top).1.testBit p.val = true)
      (hn' : (walk (v.erase a) top top).2.testBit n.val = true) (d : D p n a) : Mark p n v.toFinset a := by
    obtain ⟨_,j,_,u⟩ := ok.1 p hp'
    obtain ⟨_,i,_,v⟩ := ok.2 n hn'
    exact ⟨d,⟨j,unique u⟩,i,unique v⟩
  have va := val a ha
  cases pol <;>
    simp [prow,nrow,profile,Nat.testBit_and,testBit_bnot va.1,testBit_bnot va.2,p.isLt,n.isLt] at hp hn <;>
    apply mk hp.1 hn.1 <;> unfold D P N bit <;> simp [hp.2,hn.2]

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma clash_edge {v} (val : ∀ a ∈ v, Valid a) {a b} (ha : a ∈ v) (hb : b ∈ v)
    (c : clash (profile v a) (profile v b) = true) : Edge v.toFinset a b := by
  have obtainEdge (pa pb : Bool) (x : overlap (prow (profile v a) pa) (prow (profile v b) pb) = true)
      (y : overlap (nrow (profile v a) (!pa)) (nrow (profile v b) (!pb)) = true) : Edge v.toFinset a b := by
    obtain ⟨p,x1,x2⟩ := overlap_yes x
    obtain ⟨n,y1,y2⟩ := overlap_yes y
    exact ⟨p,n,profile_mark val ha p n pa x1 y1,profile_mark val hb p n pb x2 y2⟩
  simp only [clash,Bool.or_eq_true,Bool.and_eq_true] at c
  rcases c with ((⟨x,y⟩|⟨x,y⟩)|⟨x,y⟩)|⟨x,y⟩
  · exact obtainEdge true true x y
  · exact obtainEdge true false x y
  · exact obtainEdge false true x y
  · exact obtainEdge false false x y

end PEqualNP.Outside.L_meta_3400_aux.Part1868

namespace PEqualNP.Outside.L_meta_3400_aux.Full1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Conflict1868 PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868 PEqualNP.Outside.L_meta_3400_aux.Part1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def cm (n : Nat) : List Profile → (Nat → List Profile) → Bool
  | [],_ => true
  | x::xs, groups => (List.range n).any fun i =>
      ((groups i).all fun y => !clash x y) &&
      cm n xs (fun j => if i=j then x::groups j else groups j)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma cm_ok {n xs} (groups : Nat → List Profile) (f : Sig → Nat) (nd : (xs.map Profile.sig).Nodup)
    (bd : ∀ x ∈ xs, f x.sig < n)
    (ok : ∀ x ∈ xs, ∀ y ∈ groups (f x.sig), clash x y = false)
    (d : ∀ x ∈ xs, ∀ y ∈ xs, x.sig ≠ y.sig → f x.sig = f y.sig → clash x y = false) :
    cm n xs groups = true := by
  induction xs generalizing groups with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hn,nd⟩ := List.nodup_cons.mp nd
    apply List.any_eq_true.mpr
    refine ⟨f x.sig,List.mem_range.mpr (bd x (by simp)),Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
    · exact List.all_eq_true.mpr (fun y hy => by simp [ok x (by simp) y hy])
    · apply ih _ nd (fun a ha => bd a (List.mem_cons_of_mem _ ha)) _ (fun a ha b hb =>
        d a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      intro y hy a ha
      have hy' := List.mem_cons_of_mem x hy
      by_cases e : f x.sig = f y.sig
      · simp only [ite_eq_left e,List.mem_cons] at ha
        rcases ha with hh | ha
        · subst a
          have nxy : y.sig ≠ x.sig := fun eq => hn (List.mem_map.mpr ⟨y,hy,eq⟩)
          exact d y hy' x (by simp) nxy e.symm
        · exact ok y hy' a ha
      · simp only [ite_eq_right e] at ha
        exact ok y hy' a ha

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def fullColor (k : Nat) (v : List Sig) := cm (k+2-v.length) (v.map (profile v)) (fun _ => [])
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma fullColor_ok {k m v} (hm : m≤k) (h : BL m v.toFinset) (nd : v.Nodup) : fullColor k v = true := by
  obtain ⟨n,⟨f,bd,d⟩,lim⟩ := freeColors h
  have val : ∀ a ∈ v, Valid a := fun a ha => (h.forms a (List.mem_toFinset.mpr ha)).1.1
  have card := List.toFinset_card_of_nodup nd
  apply cm_ok _ f
  · simpa [profile,Function.comp_def] using nd
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    have := bd a (List.mem_toFinset.mpr ha)
    change f a < _
    omega
  · simp
  · intro x hx y hy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
    intro ne eq
    apply Bool.eq_false_iff.mpr
    intro c
    exact d _ (List.mem_toFinset.mpr ha) _ (List.mem_toFinset.mpr hb) ne (clash_edge val ha hb c) eq

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def fs2 : Nat → List Sig → Bool
  | 0, v => baseTest v
  | k+1, v =>
    baseTest v || (v.length ≤ k+2 && unionSep true v == top &&
      (((walk v top top).1 &&& top) == 0) && fullColor (k+1) v &&
      scanPairs (pairB v (fs2 k)) v)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma complete {k S} (l : BL k S) (m : Nat) (hm : k ≤ m) (v : List Sig) (nd : v.Nodup)
    (rep : v.toFinset = S) : fs2 m v = true := by
  induction l generalizing m v with
  | stop =>
    have hv : v = [can target] := List.perm_singleton.mp
      (List.perm_of_nodup_nodup_toFinset_eq nd (by simp) (by simpa using rep))
    subst v
    cases m <;> simp [fs2,baseTest]
  | @step j U a b d s t ha hb ca cb hab fresh tail ih =>
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    let z := blend d s t a b
    have form : BL (j+1) v.toFinset := rep ▸ BL.step ha hb ca cb hab fresh tail
    have card := freeColors form
    obtain ⟨n,hn,lim⟩ := card
    obtain ⟨_,hl⟩ := form.expand
    have hc := live_size hl
    rw [List.toFinset_card_of_nodup nd] at hc
    have len : v.length ≤ m+2 := by omega
    rw [fs2]
    apply Bool.or_eq_true_iff.mpr; right
    simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
    refine ⟨⟨⟨⟨len,coverageB form⟩,noCollision form⟩,fullColor_ok hm form nd⟩,?_⟩
    have va : a ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self ..)
    have vb : b ∈ v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have yes (x y : Sig) (u w : Bool) (id : blend false u w x y = z)
        (eqS : v.toFinset = insert x (insert y U)) : pairB v (fs2 m) x y = true := by
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
      exact ih m (by omega) _ nw pw
    obtain ⟨u,w,id⟩ := flipBlend ha.1 hb.1 d s t
    apply scanPairs_complete _ va vb hab
    · exact yes a b u w id rep
    · exact yes b a w u ((blend_symm false w u b a).trans id) (by rwa [Finset.insert_comm b a])


end PEqualNP.Outside.L_meta_3400_aux.Full1868

namespace PEqualNP.Outside.L_meta_3400_aux.Cuts1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Conflict1868 PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868 PEqualNP.Outside.L_meta_3400_aux.Part1868 PEqualNP.Outside.L_meta_3400_aux.Full1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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



set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def excluded (k : Nat) (v : List Sig) := ∀ n ≤ k, ¬ BL n v.toFinset
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def pre (k : Nat) (v : List Sig) : Bool :=
  v.length ≤ k+1 && unionSep true v == top &&
  (((walk v top top).1 &&& top) == 0) && fullColor k v

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pre_ok {n k v} (nd : v.Nodup) (h : BL n v.toFinset) (nk : n ≤ k) : pre k v = true := by
  obtain ⟨u,l⟩ := h.expand
  have b := live_size l
  rw [List.toFinset_card_of_nodup nd] at b
  simp only [pre,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  exact ⟨⟨⟨by omega,coverageB h⟩,noCollision h⟩,fullColor_ok nk h nd⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def skip (k : Nat) (blocked : List (List Sig)) (v : List Sig) : Bool :=
  pre k v && !blocked.any (fun w => decide (w.toFinset = v.toFinset))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma cut {k : Nat} {v : List Sig} {blocked : List (List Sig)}
    (nd : v.Nodup) (prior : ∀ w ∈ blocked, excluded k w)
    (hc : (baseTest v || scanPairs (pairB v (skip k blocked)) v) = false) : excluded (k+1) v := by
  intro n hn l
  have yes := oneStep l k hn v nd rfl (skip k blocked) (by
    intro w dw j jk h
    simp only [skip,Bool.and_eq_true]
    refine ⟨pre_ok dw h jk,?_⟩
    simp only [Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨b,hb,he⟩ := List.any_eq_true.mp hh
    exact prior b hb j jk ((of_decide_eq_true he) ▸ h))
  rw [hc] at yes
  contradiction

end PEqualNP.Outside.L_meta_3400_aux.Cuts1868

namespace PEqualNP.Outside.L_meta_3400_aux.FastCuts1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Conflict1868 PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868 PEqualNP.Outside.L_meta_3400_aux.Part1868 PEqualNP.Outside.L_meta_3400_aux.Full1868 PEqualNP.Outside.L_meta_3400_aux.Cuts1868

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def apart : List Sig → Nat → Nat → Bool
  | [],p,n => p == 0 || n == 0
  | a::v,p,n => p == 0 || n == 0 ||
    (apart v (p &&& a.1) (n &&& a.2) && apart v (p &&& bnot a.1) (n &&& bnot a.2))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma apart_sound {v : List Sig} (val : ∀ a∈v,Valid a) {p n} (vp : Valid1 p) (vn : Valid1 n)
    (sep : ∀ (i j : I), p.testBit i.val = true → n.testBit j.val = true → ∃ a∈v,D i j a) :
    apart v p n = true := by
  induction v generalizing p n with
  | nil =>
    by_contra hh
    have nz : p ≠ 0 ∧ n ≠ 0 := by simpa [apart] using hh
    obtain ⟨i,hi⟩ := findBit vp nz.1
    obtain ⟨j,hj⟩ := findBit vn nz.2
    obtain ⟨a,ha,_⟩ := sep i j hi hj
    cases ha
  | cons a v ih =>
    apply Bool.or_eq_true_iff.mpr; right
    have va := val a (by simp)
    have stay (i j : I) (hi : p.testBit i.val = true) (hj : n.testBit j.val = true)
        (ne : ¬ D i j a) : ∃ c ∈ v,D i j c := by
      obtain ⟨c,hc,dc⟩ := sep i j hi hj
      rcases List.mem_cons.mp hc with rfl | hm
      · exact (ne dc).elim
      · exact ⟨c,hm,dc⟩
    apply Bool.and_eq_true_iff.mpr
    constructor <;> apply ih (fun c hc => val c (List.mem_cons_of_mem _ hc)) (valid1_and vp) (valid1_and vn) <;>
      intro i j hp hn <;> rw [Nat.testBit_and,Bool.and_eq_true] at hp hn <;> apply stay _ _ hp.1 hn.1
    · exact fun d => d (hp.2.trans hn.2.symm)
    · have ei : a.1.testBit i.val = false := by simpa [testBit_bnot va.1,i.isLt] using hp.2
      have ej : a.2.testBit j.val = false := by simpa [testBit_bnot va.2,j.isLt] using hn.2
      exact fun d => d (ei.trans ej.symm)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def preF (k : Nat) (v : List Sig) : Bool :=
  v.length ≤ k+1 && unionSep true v == top && apart v top top && colorB k v && fullColor k v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma preF_ok {n k v} (nd : v.Nodup) (h : BL n v.toFinset) (nk : n ≤ k) : preF k v = true := by
  obtain ⟨u,l⟩ := h.expand
  have b := live_size l
  rw [List.toFinset_card_of_nodup nd] at b
  have ap : apart v top top = true := by
    apply apart_sound (fun a ha => (h.forms _ (List.mem_toFinset.mpr ha)).1.1) valid1_top valid1_top
    intro p n _ _
    obtain ⟨a,ha,d⟩ := pair_sep l p n
    exact ⟨a,List.mem_toFinset.mp ha,d⟩
  simp only [preF,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  exact ⟨⟨⟨⟨by omega,coverageB h⟩,ap⟩,colorB_sound nk h nd⟩,fullColor_ok nk h nd⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
def cutGo (k : Nat) (blocked : List (List Sig)) (v : List Sig) : Bool :=
  preF k v && !blocked.any (fun w => decide (w.toFinset = v.toFinset))

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma cutoff {k : Nat} {v : List Sig} {blocked : List (List Sig)}
    (nd : v.Nodup) (prior : ∀ w ∈ blocked, excluded k w)
    (hc : (baseTest v || scanPairs (pairB v (cutGo k blocked)) v) = false) : excluded (k+1) v := by
  intro n hn l
  have yes := oneStep l k hn v nd rfl (cutGo k blocked) (by
    intro w dw j jk h
    simp only [cutGo,Bool.and_eq_true]
    refine ⟨preF_ok dw h jk,?_⟩
    simp only [Bool.not_eq_true']
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨b,hb,he⟩ := List.any_eq_true.mp hh
    exact prior b hb j jk ((of_decide_eq_true he) ▸ h))
  rw [hc] at yes
  contradiction
end PEqualNP.Outside.L_meta_3400_aux.FastCuts1868

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.Free1868
namespace PEqualNP.Outside.L_meta_3400_aux.Board1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
def mult : List (Sig × Nat) → Sig
  | [] => zero
  | o::l => let (atLeastOne,atLeastTwo) := mult l
            (atLeastOne ||| o.2,atLeastTwo ||| (atLeastOne &&& o.2))
end PEqualNP.Outside.L_meta_3400_aux.Board1868
namespace PEqualNP.Outside.L_meta_3400_aux.LinearWide1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.Board1868
def maskLo (n : Nat) := (1 <<< n)-1
def tileUnit (n count : Nat) := maskLo (n*count) / maskLo n
def lanes := tileUnit 64 414
def topGrid := maskLo (64*414)
def shiftPart (width x : Nat) := (x ||| (x <<< (63*width))) &&& (maskLo width * tileUnit (64*width) (512/width))
def spreadP (x : Nat) : Nat :=
  shiftPart 1 ( shiftPart 2 ( shiftPart 4 ( shiftPart 8 ( shiftPart 16 ( shiftPart 32 ( shiftPart 64 ( shiftPart 128 ( shiftPart 256 (x)))))))))
def orL (s x : Nat) := x ||| (x <<< s)
def orR (s x : Nat) := x ||| (x >>> s)
def growP (x : Nat) := orL 1 ( orL 2 ( orL 4 ( orL 8 ( orL 16 ( orL 32 (x))))))
def growN (x : Nat) := (orL 64 ( orL 128 ( orL 256 ( orL 512 ( orL 1024 ( orL 2048 ( orL 4096 ( orL 8192 ( orL 16384 (x)))))))))) &&& topGrid
def rowStep (s x : Nat) := PEqualNP.Outside.L_meta_3400_aux.Grid1868.hop s (maskLo s * tileUnit (2*s) (26496/(2*s))) x
def fillR (x : Nat) := rowStep 1 ( rowStep 2 ( rowStep 4 ( rowStep 8 ( rowStep 16 ( rowStep 32 (x))))))
def fillC (x : Nat) := growN ((orR 64 ( orR 128 ( orR 256 ( orR 512 ( orR 1024 ( orR 2048 ( orR 4096 ( orR 8192 ( orR 16384 (x)))))))))) &&& maskLo 64)
def diff (signed : Bool) (a : Sig) :=
  let p := growP (spreadP a.1)
  let n := growN (a.2 &&& maskLo 64)
  (a,if signed then p ^^^ n else p &&& (topGrid ^^^ n))
end PEqualNP.Outside.L_meta_3400_aux.LinearWide1868
namespace PEqualNP.Outside.L_meta_3400_aux.Linear1868
def Linear (f : Nat → Nat) := f 0 = 0 ∧ ∀ x y, f (x ||| y) = f x ||| f y
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linId : Linear id := ⟨rfl,fun _ _ => rfl⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linAnd (mask : Nat) : Linear (fun x => x &&& mask) :=
  ⟨by simp,fun _ _ => Nat.and_or_distrib_right ..⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linLeft (n : Nat) : Linear (fun x => x <<< n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp only [Nat.testBit_shiftLeft,Nat.testBit_or]
    by_cases e : n ≤ j <;> simp [e]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linRight (n : Nat) : Linear (fun x => x >>> n) := by
  constructor
  · simp
  · intro x y; apply Nat.eq_of_testBit_eq; intro j
    simp [Nat.testBit_shiftRight,Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linOr {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f x ||| g x) :=
  ⟨by simp [hf.1,hg.1],fun x y => by dsimp only; rw [hf.2,hg.2]; ac_rfl⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linComp {f g} (hf : Linear f) (hg : Linear g) : Linear (fun x => f (g x)) :=
  ⟨by dsimp only; rw [hg.1,hf.1],fun _ _ => by dsimp only; rw [hg.2,hf.2]⟩

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma trunc_succ (x n : Nat) : x % 2^(n+1) = (x % 2^n) ||| (if x.testBit n then 2^n else 0) := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_mod_two_pow,Nat.testBit_or]
  cases e : x.testBit n <;> by_cases h : j=n <;> by_cases lt : j<n <;>
    simp_all [Nat.testBit_two_pow, show (j < n+1) ↔ j<n ∨ j=n by omega] <;> omega
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma images {f : Nat→Nat} (hl : Linear f) {x n} (lim : x < 2^n) (j) :
    (f x).testBit j = true ↔ ∃ i < n, x.testBit i = true ∧ (f (2^i)).testBit j = true := by
  simpa [Nat.mod_eq_of_lt lim] using imagesTrunc hl x j n
end PEqualNP.Outside.L_meta_3400_aux.Linear1868

namespace PEqualNP.Outside.L_meta_3400_aux.WProof1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868 PEqualNP.Outside.L_meta_3400_aux.Linear1868
def pRead (x : Nat) := growP (spreadP x)
def nRead (x : Nat) := growN (x &&& maskLo 64)
def rMask (r : Nat) := maskLo 64 <<< (64*r)
def cMask (c : Nat) := lanes <<< c
def wTop := maskLo 26496
end PEqualNP.Outside.L_meta_3400_aux.WProof1868

namespace PEqualNP.Outside.L_meta_3400_aux.WProof1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868 PEqualNP.Outside.L_meta_3400_aux.Linear1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linOL (d) : Linear (orL d) := linOr linId (linLeft d)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linOR (d) : Linear (orR d) := linOr linId (linRight d)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linShift (d) : Linear (shiftPart d) := by
  unfold shiftPart
  exact linComp (f := fun x => x &&& _) (g := fun x => x ||| (x <<< (63*d))) (linAnd _) (linOL _)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linRowStep (s) : Linear (rowStep s) :=
  linOr (linOr linId (linComp (linAnd _) (linLeft s))) (linComp (linAnd _) (linRight s))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linGrowP : Linear growP := by
  unfold growP
  iterate 5 apply linComp (linOL _)
  exact linOL _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linGrowN : Linear growN := by
  unfold growN
  apply linComp (linAnd _)
  iterate 8 apply linComp (linOL _)
  exact linOL _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pLin : Linear pRead := by
  apply linComp linGrowP
  unfold spreadP
  iterate 8 apply linComp (linShift _)
  exact linShift _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma nLin : Linear nRead := linComp (f := growN) (g := fun x => x &&& maskLo 64) linGrowN (linAnd _)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma rLin : Linear fillR := by
  unfold fillR
  iterate 5 apply linComp (linRowStep _)
  exact linRowStep _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma cLin : Linear fillC := by
  unfold fillC
  apply linComp linGrowN
  apply linComp (linAnd _)
  iterate 8 apply linComp (linOR _)
  exact linOR _

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma rowMaskBit (r i : Nat) : (rMask r).testBit i = true ↔ i/64 = r := by
  simp only [rMask,maskLo,Nat.one_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one]
  by_cases le : 64*r ≤ i <;> simp [le] <;> omega
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma topBitW (i) : wTop.testBit i = decide (i<26496) := by
  unfold wTop maskLo
  rw [Nat.one_shiftLeft,Nat.testBit_two_pow_sub_one]

def Sub (x y : Nat) := ∀ i, x.testBit i = true → y.testBit i = true
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma linMono {f} (h : Linear f) {x y} (s : Sub x y) : Sub (f x) (f y) := by
  have e : x ||| y = y := by
    apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_or]
    cases hx : x.testBit i <;> simp [hx,s i]
  intro i hi
  have e' := congrArg (fun w : Nat => w.testBit i) (h.2 x y)
  simp [e,Nat.testBit_or,hi] at e'
  exact e'
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
end PEqualNP.Outside.L_meta_3400_aux.WProof1868

namespace PEqualNP.Outside.L_meta_3400_aux.WProof1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868 PEqualNP.Outside.L_meta_3400_aux.Linear1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pulsePos : ∀ i : Fin 414, pRead (2^i.val) = rMask i.val := by decide +kernel
end PEqualNP.Outside.L_meta_3400_aux.WProof1868

namespace PEqualNP.Outside.L_meta_3400_aux.WProof1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868 PEqualNP.Outside.L_meta_3400_aux.Linear1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pulseNeg : ∀ i : Fin 414, nRead (2^i.val) = (if i.val<64 then cMask i.val else 0) := by decide +kernel
end PEqualNP.Outside.L_meta_3400_aux.WProof1868

namespace PEqualNP.Outside.L_meta_3400_aux.WProof1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868 PEqualNP.Outside.L_meta_3400_aux.Linear1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pulseLanes : ∀ r : Fin 414, (lanes >>> (64*r.val)) &&& maskLo 64 = 1 := by decide +kernel
end PEqualNP.Outside.L_meta_3400_aux.WProof1868

namespace PEqualNP.Outside.L_meta_3400_aux.WProof1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868 PEqualNP.Outside.L_meta_3400_aux.Linear1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pulseR : ∀ i : Fin 414, fillR (wTop ^^^ rMask i.val) &&& rMask i.val = 0 := by decide +kernel
end PEqualNP.Outside.L_meta_3400_aux.WProof1868

namespace PEqualNP.Outside.L_meta_3400_aux.WProof1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868 PEqualNP.Outside.L_meta_3400_aux.Linear1868
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pulseC : ∀ i : Fin 64, fillC (wTop ^^^ cMask i.val) &&& cMask i.val = 0 := by decide +kernel
end PEqualNP.Outside.L_meta_3400_aux.WProof1868

namespace PEqualNP.Outside.L_meta_3400_aux.WProof1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868 PEqualNP.Outside.L_meta_3400_aux.Linear1868
abbrev Ix := Fin 26496
abbrev I := Fin 414
def posAt (i : Ix) : I := ⟨i.val/64,by have := i.isLt;omega⟩
def negAt (i : Ix) : I := ⟨i.val % 64,by omega⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma laneAt (i : Ix) : lanes.testBit i.val = decide (i.val % 64 = 0) := by
  have e := congrArg (fun x : Nat => x.testBit (i.val % 64)) (pulseLanes (posAt i))
  have es : 64*(i.val/64) + i.val % 64 = i.val := by omega
  have le : i.val % 64 < 64 := by omega
  change (((lanes >>> (64*(i.val/64))) &&& maskLo 64).testBit (i.val % 64)) = _ at e
  simp only [maskLo,Nat.one_shiftLeft,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one,
    es,le,decide_true,Bool.and_true] at e
  rw [e]
  apply Bool.eq_iff_iff.mpr
  exact Nat.testBit_one_eq_true_iff_self_eq_zero.trans decide_eq_true_iff.symm
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma colMaskBit {c : Nat} (hc : c<64) (i : Ix) : (cMask c).testBit i.val = true ↔ i.val % 64 = c := by
  unfold cMask
  rw [Nat.testBit_shiftLeft]
  by_cases le : c ≤ i.val
  · simp only [le,decide_true,Bool.true_and]
    have q : i.val-c < 26496 := by have := i.isLt; omega
    rw [laneAt ⟨_,q⟩,decide_eq_true_eq]
    change (i.val-c) % 64=0 ↔ i.val % 64=c
    omega
  · simp [le]
    omega
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pReadBit {a} (val : Valid1 a) (i : Ix) : (pRead a).testBit i.val = a.testBit (posAt i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images pLin (validBound val)]
  constructor
  · rintro ⟨j,le,h,yes⟩
    rw [pulsePos ⟨j,le⟩] at yes
    change a.testBit (i.val/64) = true
    rwa [(rowMaskBit j i.val).mp yes]
  · intro h
    exact ⟨_,(posAt i).isLt,h,by rw [pulsePos (posAt i)];exact (rowMaskBit ..).mpr rfl⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma nReadBit {a} (val : Valid1 a) (i : Ix) : (nRead a).testBit i.val = a.testBit (negAt i).val := by
  apply Bool.eq_iff_iff.mpr
  rw [images nLin (validBound val)]
  constructor
  · rintro ⟨j,le,h,yes⟩
    rw [pulseNeg ⟨j,le⟩] at yes
    by_cases lt : j<64
    · simp only [lt,↓reduceIte] at yes
      change a.testBit (i.val % 64) = true
      rwa [(colMaskBit lt i).mp yes]
    · simp [lt] at yes
  · intro h
    refine ⟨_,(negAt i).isLt,h,?_⟩
    rw [pulseNeg (negAt i)]
    have lt : (negAt i).val < 64 := Nat.mod_lt _ (by decide)
    simp only [lt,↓reduceIte]
    exact (colMaskBit lt i).mpr rfl

def DS (signed : Bool) (p n : I) (a : Sig) :=
  if signed then PEqualNP.Outside.L_meta_3400_aux.Conflict1868.D p n a else (a.1.testBit p.val=true ∧ a.2.testBit n.val=false)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma diffBit (s : Bool) {a} (va : Valid a) (i : Ix) :
    (diff s a).2.testBit i.val = true ↔ DS s (posAt i) (negAt i) a := by
  have top : topGrid.testBit i.val = true := by change wTop.testBit i.val = true;rw [topBitW];exact decide_eq_true i.isLt
  cases s
  · change (pRead a.1 &&& (topGrid ^^^ nRead a.2)).testBit i.val = true ↔ a.1.testBit (posAt i).val = true ∧ a.2.testBit (negAt i).val = false
    simp [Nat.testBit_and,Nat.testBit_xor,pReadBit va.1,nReadBit va.2,top]
  · change (pRead a.1 ^^^ nRead a.2).testBit i.val = true ↔ a.1.testBit (posAt i).val ≠ a.2.testBit (negAt i).val
    simp [Nat.testBit_xor,pReadBit va.1,nReadBit va.2]
end PEqualNP.Outside.L_meta_3400_aux.WProof1868

namespace PEqualNP.Outside.L_meta_3400_aux.WProof1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868 PEqualNP.Outside.L_meta_3400_aux.Linear1868
open PEqualNP.Outside.L_meta_3400_aux.Board1868 (mult)
abbrev Sign := Sig × Nat
def signs (d : Bool) (v : List Sig) := v.map (diff d)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma focusValid {v a} : Sub (focus v a) wTop := by
  intro i hi; simp only [focus,Nat.testBit_and,Bool.and_eq_true] at hi;exact hi.2
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma fromMark {d v} (valid : ∀ a∈v,Valid a) {a} (ha : a∈v) (i : Ix)
    (hit : (entryW (signs d v) (diff d a)).2.testBit i.val = true) : M d (posAt i) (negAt i) v a := by
  let u := focus (signs d v) (diff d a)
  simp only [entryW,Nat.testBit_and,Bool.and_eq_true] at hit
  have hr := fromRow rLin ((rowMaskBit (posAt i).val i.val).mpr rfl) (pulseR (posAt i)) (focusValid (v := signs d v) (a := diff d a)) hit.1.1.2
  have nc : (negAt i).val < 64 := Nat.mod_lt _ (by decide)
  have hn := fromRow cLin ((colMaskBit nc i).mpr rfl) (pulseC ⟨(negAt i).val,nc⟩) (focusValid (v := signs d v) (a := diff d a)) hit.1.2
  refine ⟨(diffBit d (valid a ha) i).mp hit.1.1.1,?_,?_⟩
  · obtain ⟨j,hj,jr⟩ := hr
    have b : j<26496 := of_decide_eq_true (topBitW j ▸ focusValid j hj)
    have e : posAt ⟨j,b⟩ = posAt i := Fin.ext ((rowMaskBit ..).mp jr)
    exact ⟨negAt ⟨j,b⟩,e ▸ singleD valid ha ⟨j,b⟩ hj⟩
  · obtain ⟨j,hj,jn⟩ := hn
    have b : j<26496 := of_decide_eq_true (topBitW j ▸ focusValid j hj)
    have e : negAt ⟨j,b⟩ = negAt i := Fin.ext ((colMaskBit nc ⟨j,b⟩).mp jn)
    exact ⟨posAt ⟨j,b⟩,e ▸ singleD valid ha ⟨j,b⟩ hj⟩

def entries (d : Bool) (v : List Sig) := let g := signs d v; g.map (entryW g)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma entries_fst (d) (v) : (entries d v).map Prod.fst = v := by
  simp [entries,signs,entryW,diff,Function.comp_def]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma memSig {d v a} (ha : a ∈ entries d v) : a.1 ∈ v := by
  rw [← entries_fst d v];exact List.mem_map_of_mem ha
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
end PEqualNP.Outside.L_meta_3400_aux.WProof1868
namespace PEqualNP.Outside.L_meta_3400_aux.Guard3400
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868 PEqualNP.Outside.L_meta_3400_aux.Cuts1868 PEqualNP.Outside.L_meta_3400_aux.Conflict1868
open PEqualNP.Outside.L_meta_3400_aux.WProof1868 PEqualNP.Outside.L_meta_3400_aux.LinearWide1868
open PEqualNP.Outside.L_meta_3400_aux.Board1868 (mult)
open PEqualNP.Outside.L_meta_3400_aux.ColorSearch1868 (paint paint_ok)

def grid (k : Nat) (v : List Sig) : Bool :=
  (((mult (signs true v)).1 &&& wTop) == wTop) &&
    paint (k+2-v.length) (PEqualNP.Outside.L_meta_3400_aux.WProof1868.entries true v) (fun _ => 0)

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
    by_cases hi : i<26496
    · let z : Ix := ⟨i,hi⟩
      obtain ⟨a,ha,hd⟩ := psep (posAt z) (negAt z)
      have hit := multiOne (List.mem_map_of_mem (f := diff true) ha) i ((diffBit true (val a ha) z).mpr hd)
      simpa [hi,signs] using hit
    · simp [hi]
  · apply paint_ok _ f
    · rwa [PEqualNP.Outside.L_meta_3400_aux.WProof1868.entries_fst]
    · intro x hx
      have := bd _ (List.mem_toFinset.mpr (memSig hx))
      omega
    · simp
    · intro x hx y hy ne eq
      by_contra hh
      obtain ⟨p,q,h1,h2⟩ := edgeWitness val hx hy hh
      apply ok _ (List.mem_toFinset.mpr (memSig hx)) _ (List.mem_toFinset.mpr (memSig hy)) ne _ eq
      exact ⟨p,q,by simpa [DS,M,U,PEqualNP.Outside.L_meta_3400_aux.Conflict1868.Mark,PEqualNP.Outside.L_meta_3400_aux.Conflict1868.Unique] using h1,by simpa [DS,M,U,PEqualNP.Outside.L_meta_3400_aux.Conflict1868.Mark,PEqualNP.Outside.L_meta_3400_aux.Conflict1868.Unique] using h2⟩

def fast (k : Nat) (v : List Sig) : Bool :=
  decide (v.length≤k+1) && (unionSep true v == top) && grid k v
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma fast_ok {n k v} (nd : v.Nodup) (h : BL n v.toFinset) (nk : n ≤ k) : fast k v = true := by
  obtain ⟨t,l⟩ := h.expand
  have sz := live_size l
  rw [List.toFinset_card_of_nodup nd] at sz
  simp only [fast,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
  exact ⟨⟨by omega,coverageB h⟩,grid_ok nk nd h⟩

def go (k : Nat) (blocked : List (List Sig)) (v : List Sig) : Bool :=
  fast k v && !blocked.any (fun w => decide (w.toFinset=v.toFinset))
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

end PEqualNP.Outside.L_meta_3400_aux.Guard3400
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.Free1868
namespace PEqualNP.Outside.L_meta_3400_aux.Check2516
def costly (g : Gate) : Bool := match g.op with | .not => false | _ => true
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma gateTag {w : List Sig} (hw : ∀ a∈w, Valid a) (g : Gate)
    (legal : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ (∃ a∈w, proper a ∧ gv w g=neg a) ∨
      ((if costly g then 1 else 0)=1 ∧ ∃ d a b,a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ gv w g=bin d a b) := by
  by_cases h : costly g=true
  · rcases gate_rep hw g legal with a|a|a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨by simp [h],a⟩)
  · obtain ⟨o,l⟩ := g
    cases o <;> try simp [costly] at h
    have nt (a : Sig) (v : Valid a) (r : represented w a) :
        represented w (neg a) ∨ ∃ a'∈w, proper a' ∧ neg a=neg a' := by
      rcases operand_cases v r with rfl|rfl|⟨mem,hp⟩
      · exact Or.inl (Or.inr (fun hp => hp.2.2 neg_laws.1))
      · exact Or.inl (Or.inr (fun hp => hp.2.1 neg_laws.2))
      · exact Or.inr ⟨a,mem,hp,rfl⟩
    cases l with
    | nil => exact (nt zero valid_zero (Or.inr (fun h => h.2.1 rfl))).imp_right Or.inl
    | cons i l => exact (nt (w.getD i zero) (valid_getD hw i) (get_rep w i)).imp_right Or.inl
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma pullTag (c : Nat) {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ (∃ a ∈ w, proper a ∧ z=neg a) ∨ (c=1 ∧ ∃ d a b, a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ z=bin d a b)) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' + t ≤ k+t'+c ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨hc,d, a, b, ha, hb, pa, pb, hab, eq⟩)
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
        exact ⟨k+1, t, _, by omega, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma tagExtract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.countP costly + t ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pullTag (if costly g then 1 else 0) ht (gateTag hw g (legal g (by simp))) hs
    exact ⟨l,u,T,by cases he : costly g <;> simp [he] at hl ⊢ <;> omega,hu,hT⟩
end PEqualNP.Outside.L_meta_3400_aux.Check2516
namespace PEqualNP.Outside.L_meta_3400_aux.Check2516
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868 PEqualNP.Outside.L_meta_3400_aux.Cuts1868 PEqualNP.Outside.L_meta_3400_aux.Conflict1868
def x0 : Sig := (0x1d9f0a2e19e4d7cfb4e45eeb2bd76d22790cf158040647963418f1109100a662800f44322d95322d125a8a51b4b1058900bf6635,0x11170a221160158ab0441e4b02806420400c3018040607922408f110000026600003043221953029101a0841b410018800a32614)
def x1 : Sig := (0x32d8f998ec21ebfc6c71a97d8fdb3c903f791274d88b0048805b9cd38c67990db0b043089c0970239c340307406b0860de084863,0x20c05188e800ca640c2121248c5118103160000458090048005304438c23810db0b043081c00400284240306406900209c084060)
def x2 : Sig := (0x2c7f04f346c33df3ba385ed4d7eb9e251793a2aaaaa8a9e88a0c2b8052802a434d233a06d1620718d0853059d58a6e2840a4009d,0xc2b001106802591b01046d0518a000006938022a2a0a9a08a082a8012002a024c033806810207005081001915822e0040840094)
def x3 : Sig := (0x1b70f24e336a5ecf5f12b33ef6add45d8626749918769c0c01e5574862e501b4295ad11024daac60800a4b0aac44001a2c60974d,0x1110824211601a4a4a00312a2220945d000474081852140c0065514860c501a00158c01004d8a020800a0a02a804000a2c608648)
def x4 : Sig := (0x1eeb679e3bffa00515bfc1c41c450170c30475c7e7312940b58126a715284016f8351611c2a48b54432dc1a449331653335c0463,0xee8659c2a9fa00505bbc0841c450100830001c7e3212840918006a715284016f8241201c2200b544325c1a441231651131c0022)
def x5 : Sig := (0x2ba8e57587943f73cdc325bf7976e8cae8c3c92c72e1d41f596200264085da080e4c00ae8510c30265e14dbe428691a2030582e1,0xa28601506940a514c832194615688428843c80430a0d00c59600006408498080c4c00808400c30240c141be42828022030480e0)
def x6 : Sig := (0x373db9e7fc3f901862dfc618619803930c780e4281b247b4556cd02b4f5e359852803c4302888b91488aa0f88e060744da22aa9b,0x1339a8671437101842d2c018618001830c100e4281b24594552cd028435c149042003c0200888b11488aa0f88e06054442228a9a)
def x7 : Sig := (0x2fd6de79c7dfc0228b6ff823822202ec30838b807c5d24900ea7d12ca46b4155524062e04af5007e6c94b4c433457044a4bb2501,0x21d49e68c14bc022036c9823822002ac300003804c5d04100487d128a46b4155120042604af5007c2c14b44020455044a43b2500)
def x8 : Sig := (0x35e71f81f8186fbcf38c3fc3fc3cf30fc0fc0c36470c3261621242c8a01a66e6b4818b6d222155c00323142330488a94151ab195,0x24c61580e80865a4b10c0e419c08620040a80030460c22612212028080026246b081036d222114c00320140110480a9010183104)
def xs : List Sig := [x0,x1,x2,x3,x4,x5,x6,x7,x8]

def input (s : Bool) (i : Fin 414) (j : Fin 9) := bit s i (xs.getD j.val zero)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma xv : ∀ a∈xs,Valid a := by
  intro a ha
  simp only [xs,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;>
    intro j hj <;> apply Nat.testBit_eq_false_of_lt <;> exact (by decide : _ < 2^414) |>.trans_le (Nat.pow_le_pow_right (by decide) hj)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma inputs_list (s : Bool) (i : Fin 414) : List.ofFn (input s i)=xs.map (bit s i) := by
  apply List.ext_getElem
  · simp [xs]
  · intro j h h';simp only [List.getElem_ofFn,List.getElem_map,input,List.getD_eq_getElem _ _ (by simpa using h')]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma inputs_ok : ∀ s i, edgeF (input s i)=s := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma get_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates xs := by
  let w := execute C.gates xs
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates xs xv
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates xs).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ xv (fun g hg => (h g hg).1)]
    have eq := he (input s i)
    rw [inputs_list, inputs_ok] at eq
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
def canonicalInputs := xs.map can
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma canonValid {a} (ha : a ∈ canonicalInputs) : Valid a := by
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ha
  exact vc (xv u hu)
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma canonRequired : canonicalInputs.all (fun a => unionSep true (canonicalInputs.erase a) != top) = true := by decide +kernel
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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


end PEqualNP.Outside.L_meta_3400_aux.Check2516
namespace PEqualNP.Outside.L_meta_3400_aux.Basis1868
def reindexLoop (f : Fin 414 → Fin 414) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 414 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 414 → Fin 414) (x : Nat) : Nat := reindexLoop f x 414
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_testBit (f : Fin 414 → Fin 414) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 414 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 414 j
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_valid1 (f : Fin 414 → Fin 414) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 414 by omega]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_and (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_and]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_or (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_or]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_bnot (f : Fin 414 → Fin 414) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_zero (f : Fin 414 → Fin 414) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_top (f : Fin 414 → Fin 414) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 414
  · simp [hj, testBit_top, (f ⟨j, hj⟩).isLt]
  · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma reindex_comp (f g : Fin 414 → Fin 414) (x : Nat) :
    reindex f (reindex g x) = reindex (fun j => g (f j)) x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, reindex_testBit, (f ⟨j, hj⟩).isLt]
  · simp [hj]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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

end PEqualNP.Outside.L_meta_3400_aux.Basis1868
namespace PEqualNP.Outside.L_meta_3400_aux.Sym1868
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
def Good (H J : SigHom) (a : Sig) := Valid a ∧ J.fn (H.fn a) = a
variable {H J : SigHom}
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodNeg {a} (h : Good H J a) : Good H J (neg a) :=
  ⟨valid_neg h.1,by rw [H.hneg h.1,J.hneg (H.valid a),h.2]⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodBin {a b} (ha : Good H J a) (hb : Good H J b) {d} : Good H J (bin d a b) :=
  ⟨valid_bin ha.1 hb.1,by rw [H.hbin,J.hbin,ha.2,hb.2]⟩
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma inj {a b} (ha : Good H J a) (hb : Good H J b) (e : H.fn a = H.fn b) : a=b := by
  rw [← ha.2,← hb.2,e]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma properH {a} (ga : Good H J a) (ha : proper a) : proper (H.fn a) :=
  ⟨H.valid a,fun e => ha.2.1 (ga.2.symm.trans ((congrArg J.fn e).trans J.hzero)),
    fun e => ha.2.2 (ga.2.symm.trans ((congrArg J.fn e).trans J.hone))⟩
end PEqualNP.Outside.L_meta_3400_aux.Sym1868
namespace PEqualNP.Outside.L_meta_3400_aux.Moves3400
open PEqualNP.Outside.L_meta_3400_aux.Basis1868
open PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.Sym1868 PEqualNP.Outside.L_meta_3400_aux.Cuts1868
def SignFixed (H : SigHom) := ∀ a, sign (H.fn a)=sign a
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma flip_map (H : SigHom) (s : Bool) {a : Sig} (ha : Valid a) :
    H.fn (flip s a)=flip s (H.fn a) := by cases s <;> first | rfl | exact H.hneg ha
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma can_map {H : SigHom} (fix : SignFixed H) {a : Sig} (ha : Valid a) :
    H.fn (can a)=can (H.fn a) := by unfold can; rw [fix a,flip_map H _ ha]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma blend_map {H : SigHom} (fix : SignFixed H) {a b : Sig} (ha : Valid a) (hb : Valid b) (d s t) :
    H.fn (blend d s t a b)=blend d s t (H.fn a) (H.fn b) := by
  unfold blend
  rw [can_map fix (valid_bin (vf s ha) (vf t hb)),H.hbin,flip_map H _ ha,flip_map H _ hb]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodFlip {H J : SigHom} {a} (h : Good H J a) (s : Bool) : Good H J (flip s a) := by
  cases s <;> first | exact h | exact goodNeg h
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma goodBlend {H J : SigHom} {a b} (ha : Good H J a) (hb : Good H J b) (d s t) :
    Good H J (blend d s t a b) := goodFlip (goodBin (goodFlip ha s) (goodFlip hb t)) _
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma fixed (p n : Fin 414 → Fin 414) (z : p 0=0) : SignFixed (pairHom p n) := by
  intro a
  change (reindex p a.1).testBit 0=a.1.testBit 0
  rw [reindex_testBit]
  simp [z]
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
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
end PEqualNP.Outside.L_meta_3400_aux.Moves3400
namespace PEqualNP.Outside.L_meta_3400_aux.Orbit3400
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868 PEqualNP.Outside.L_meta_3400_aux.Cuts1868 PEqualNP.Outside.L_meta_3400_aux.Guard3400 PEqualNP.Outside.L_meta_3400_aux.Moves3400
def v0 : Sig := (0x2260f5d1e61b28304b1ba114d42892dd86f30ea7fbf9b869cbe70eef6eff599d7ff0bbcdd26acdd2eda575ae4b4efa76ff4099ca,0x2ee8f5ddee9fea754fbbe1b4fd7f9bdfbff3cfe7fbf9f86ddbf70eefffffd99ffffcfbcdde6acfd6efe5f7be4beffe77ff5cd9eb)
def v1 : Sig := (0xd27066713de1403938e56827024c36fc086ed8b2774ffb77fa4632c739866f24f4fbcf763f68fdc63cbfcf8bf94f79f21f7b79c,0x1f3fae7717ff359bf3dededb73aee7efce9ffffba7f6ffb7ffacfbbc73dc7ef24f4fbcf7e3ffbffd7bdbfcf9bf96ffdf63f7bf9f)
def v2 : Sig := (0x1380fb0cb93cc20c45c7a12b281461dae86c5d555557561775f3d47fad7fd5bcb2dcc5f92e9df8e72f7acfa62a7591d7bf5bff62,0x33d4ffeef97fda6e4fefb92fae75fffff96c7fdd5d5f565f75f7d57fedffd5fdb3fcc7f97efdf8ffaf7effe6ea7dd1ffbf7bff6b)
def v3 : Sig := (0x248f0db1cc95a130a0ed4cc109522ba279d98b66e78963f3fe1aa8b79d1afe4bd6a52eefdb25539f7ff5b4f553bbffe5d39f68b2,0x2eef7dbdee9fe5b5b5ffced5dddf6ba2fffb8bf7e7adebf3ff9aaeb79f3afe5ffea73feffb275fdf7ff5f5fd57fbfff5d39f79b7)
def v4 : Sig := (0x21149861c4005ffaea403e3be3bafe8f3cfb8a3818ced6bf4a7ed958ead7bfe907cae9ee3d5b74abbcd23e5bb6cce9accca3fb9c,0x31179a63d5605ffafa443f7be3bafeff7cfffe381cded7bf6e7ff958ead7bfe907dbedfe3ddff4abbcda3e5bbedce9aeece3ffdd)
def v5 : Sig := (0x14571a8a786bc08c323cda4086891735173c36d38d1e2be0a69dffd9bf7a25f7f1b3ff517aef3cfd9a1eb241bd796e5dfcfa7d1e,0x35d79feaf96bf5aeb37cde6b9ea977bd77bc37fbcf5f2ff3a69ffff9bf7b67f7f3b3ff7f7bff3cfdbf3ebe41bd7d7fddfcfb7f1f)
def v6 : Sig := (0x8c2461803c06fe79d2039e79e67fc6cf387f1bd7e4db84baa932fd4b0a1ca67ad7fc3bcfd77746eb7755f0771f9f8bb25dd5564,0x2cc65798ebc8efe7bd2d3fe79e7ffe7cf3eff1bd7e4dba6baad32fd7bca3eb6fbdffc3fdff7774eeb7755f0771f9fabbbddd7565)
def v7 : Sig := (0x1029218638203fdd749007dc7dddfd13cf7c747f83a2db6ff1582ed35b94beaaadbf9d1fb50aff81936b4b3bccba8fbb5b44dafe,0x1e2b61973eb43fddfc9367dc7ddffd53cffffc7fb3a2fbeffb782ed75b94beaaedffbd9fb50aff83d3eb4bbfdfbaafbb5bc4daff)
def v8 : Sig := (0xa18e07e07e790430c73c03c03c30cf03f03f3c9b8f3cd9e9dedbd375fe599194b7e7492dddeaa3ffcdcebdccfb7756beae54e6a,0x1b39ea7f17f79a5b4ef3f1be63f79dffbf57ffcfb9f3dd9eddedfd7f7ffd9db94f7efc92dddeeb3ffcdfebfeefb7f56fefe7cefb)
def v9 : Sig := (0x200441021a0000030a00005020824d80820c832370b8214ba4022c629840904f40b8c542628dd0618174a80b04f21621409188,0xe28a455069f2011439ac090712e83cf8e93cfe3a3f0f825dba40aac73dc58924f4cb8c5c26a8fd46bc1f4b80b86fe576354998b)
def v10 : Sig := (0xd07022611c4140390845682200441224004e108040447963400610011002662000f04322194020c024a8850b490058900b72614,0x11170a221160158ab0441e4b02806420400c3018040607922408f110000026600003043221953029101a0841b410018800a32614)
def v11 : Sig := (0x2240f190e40128304811a1148408109006710224d889004880430cc30c67190d30b00308900840028c240106404a0860de000842,0x20c05188e800ca640c2121248c5118103160000458090048005304438c23810db0b043081c00400284240306406900209c084060)
def v12 : Sig := (0x2f67f7f7f7df3c33db9ff796f42cd3ffc6f7efaffffdffffffe76fef7fff7fff7fffbffff3fecfdeefeffdfeffdefffffff7bfde,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v13 : Sig := (0x200f100a01800004103a100000000d880600c055151100141e3046f2c7f519c32d081c90208c8c22d2045a60a449056bf409942,0x22c0f5cce81fca644faba124ac759bdfb9604fc55959504d51f7046fedffd19db3fcc3c95e68c8d6af64f7a64a6dd077bf58d96b)
def v14 : Sig := (0x1000204111c0000018600022004414ac0044d010554561775a0402c211844b0024c84f1229488c4234acca02a1491972153b700,0x1314ae66117f100a43ce980b2224e7efc80c7fd90556561775a4d13c61dc54f0034c84f162fdb8fd2b5afce0aa14d1df2373bf0b)
def v15 : Sig := (0xc27046302c2140392085680502082250082a08a2220a9a00a042300528022424d03380641620718408130589580660800a4009c,0xc2b001106802591b01046d0518a000006938022a2a0a9a08a082a8012002a024c033806810207005081001915822e0040840094)
def v16 : Sig := (0x104006100001402820016026020c20f008288080044d6b74a244108629026e0074aa8e62152048820c23c58b684e18c00a3b39c,0x11178a631560159af2441e5b63aae6ef4c9ffe3804d6d7b76e2cf91862d43ee0074bacf621dfb4a938da3c59be94e98e60e3bf9d)
def v17 : Sig := (0x20109800c4004bf868402839839a3c803c790230188a0008005a985088479909008041081c0970239c10020300480820cc004800,0x20001000c0004a60080021208010181030600000180800080053004088038109009041081c00400284000202004800208c004040)
def v18 : Sig := (0x4070202104a0000120c5200000003250004248305142ba026846308331824f24103bc5162e60cdc020ab040bd10661d20f2351c,0x15178e62116b358ab35cde4b12a867ad469c37fb87562fb3a68cfbb8335866f24303bc7763ff3cfd3b1abc41bd147fdd60f33f1f)
def v19 : Sig := (0x105018886821c08c203088408689141017381250880a004080199cd18c620105b0b04300180930219814020100690840dc084802,0x20c01188e800c024002000208c0110103120000048090040001304418c230105b0b043081800000084240200006900009c084000)
def v23 : Sig := (0x1009800800042084040202b2010608a28680810104656174072d058a85795a802c8c1e82c1970a32c520e02224481848c03fb00,0x31149a62d1605a6a4a44392ba230feff786c7e181c5e561f6477d158e8d795e903d8c5f83cddf0abac5a3e42aa5cc1aeac63ff49)
def v24 : Sig := (0x2014006144001df2aa001e10c3aa9e0514938228088880a80a0c090042802a410502280611420408908030599488682840a0009c,0x3000104000590b0000650418a000004938020008081a00a08280002002a000403280601020400108000191480280040800094)
def v25 : Sig := (0x10001a083828c00c0004800000000110002c1451051602002491d459ad7a05b4b090c5512a8d38e50a1a820028710055bc5a7d02,0x31d49feaf96bd02e036c982b8e2177bd712c37d94d5f06532497d579ad7b45f5b3b0c7797afd38fdaf3ebe40a87d51ddbc7b7f0b)
def v26 : Sig := (0x45700824043008032385a408689162517102282880829e0820c2b801200204341233a00506204189004304195086e0840a0001c,0x403000000002580b01046401088000006900022820029a082082a801200220240033806010204001000000115002e0040800014)
def v30 : Sig := (0x11800a0c1924c20c04c4002b28146102680c5150040646163410d01081008420800c44302c953025025a8a0020310181001b6620,0x11140a221160100a0044180b02006420400c3018040606122400d110000004600000043020953029001a0840a010018800232600)
def v38 : Sig := (0x206004d1460328300a180014d4289205069302a2aaa8a8688a040a80428008014d203a04d0620510c0853008410a6a2040000088,0xc2800110680201100104090510a000006938022a2a0a8208a000a80120008024c003804800207004081001801822e0040040080)
def v39 : Sig := (0x33e0ffddff3fea3c4fdfa13ffc3cf3dfeeff5ff7fffffe7ffff7deffefffddbdfffcfffdfefffdf7efffffae6b7ffbf7ff5bffea,0x3ffcfffffffffa7f4ffff9bfff7ffffffffffffffffffe7ffff7dfffffffddfffffcfffdfeffffffeffffffeebffffffff7fffeb)
def v40 : Sig := (0x20000591c4112030000900000000028000d10a26e3892061ca0208a70c1a580956a02acdd22041926da534a4430afa64d3000882,0x2ee8759dee9fe03505bbc094dd5f0b82bff38be7e3a9e861db920ea79f3ad81ffea43bcdda224fd66fe5f5bc43ebfe75d31c59a3)
def v41 : Sig := (0x48f082008848100a0e44cc10952292279088140040043923418a0109100a642800504220905120d1250805110b10581009f6030,0x7082000000580b0440e410080602040080010040403922408a010000026400003042221051009101000411410018000832014)
def v42 : Sig := (0x260f040220a08004b12a114d428905d862204811870980801e5064862e5019429509100004a8c408000410a084400122c409148,0x804000000a404a0021202020905d000044001850100c0065004860c501800158c0000448800080000202080400022c408048)
def v43 : Sig := (0x26effdf1ee9fa930ebffedd5dd7abbfffffb8fe7fff9fbfbffffaeffffffffdffff5bfefdb6fdfdffff5f5ff5bfffff7ffdff9fa,0x2eeffdfdee9feff5ffffeff5fdfffbfffffbcff7fffdfbffffffaeffffffffdfffffffefff6fdfdffff5f7ff5ffffff7ffdff9ff)
def v44 : Sig := (0x20009041c40008304a002010c028928d04f30a2018c890294a6608486ad7198907c0a9cc104a4482ac80340a024ce824cc009988,0x20009041c4004a704a002130e13a9adf3cf3ce2018d8d02d4a770848ead7998907d8e9cc1c4ac482acc0361a0acce826ec40d9c9)
def v45 : Sig := (0x1140820000057caa0401e2b23926c0238088018000646960018d1108000a660000a40222d11302910520a51b480018800a36214,0x11170a221160158ab0441e4b02806420400c3018040607922408f110000026600003043221953029101a0841b410018800a32614)
def v46 : Sig := (0x2606590221b2000011b81041400005082000487e3312840818106a70428401478301201c2208950412541a44902125233400042,0xee8659c2a9fa00505bbc0841c450100830001c7e3212840918006a715284016f8241201c2200b544325c1a441231651131c0022)
def v47 : Sig := (0x2374fdf1e61b7ffaeb5bbf3ff7bafedfbefb8ebffbfffeffcbffdfffeefffffd7ffafbefff7bfdfbfdf77fffffcefbfeffe3fbde,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v48 : Sig := (0x401080600b00000218800084081215063006838918286082850ec92e7a019571b0bb41526a0cd08804300009486a54fc40190a,0x24c095c8e80be0240338c0209c29139d37b007e3cb59286182970ee9bf7b4197f3b0fb4d5a6a0cd4af24b600096d7e55fc58590b)
def v49 : Sig := (0x14170a0a1860c08c30245a4002810520110c3050040603802418f11091002462800344102885302d121a8241b431040900ba6414,0x11170a221160158ab0441e4b02806420400c3018040607922408f110000026600003043221953029101a0841b410018800a32614)
def v50 : Sig := (0x2220e5518610283049032114502080c880c3082472e1900949620026408558080e40008c8000c10265a145ae42069022030080c0,0xa28601506940a514c832194615688428843c80430a0d00c59600006408498080c4c00808400c30240c141be42828022030480e0)
def v51 : Sig := (0x3677ffdbfe7be8bc7b3ffb54d6a997fd97ff3ef7ffffbbe9efffffffffff7dfffff3ffddfaeffdffffbff7efff7ffe7ffffafdde,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v52 : Sig := (0x40441002002820090021049420904c828300a57a49b8498a830ec420a148052d70838cd0624442a52555064148f83225401140,0x2cc05598ea88ea650d2921a49c7f9a5cb3e3c1a57a49b8698ad30ec7bca3c90fbdfcc3cdde6244c6a765570641e9fa33bd5c5161)
def v53 : Sig := (0x882020801c047c7942018e30a476c207104f118040400022010211090008262800f40302d15302c12500a0130b10089009d4424,0x6020001400582b0041e4302006420400c30180404020220002110000022600003003021153028101008013010008800812404)
def v54 : Sig := (0x2220b1c1e41b0010421b80104008029104700e0281b000204164002b4e5e11985280384102088990488020a80a060244da00888a,0x228a045041700104292c010610001830c100e4281b0400451240028435c10904200380000088b104880a0b80a0604444200888a)
def v55 : Sig := (0x2ae2f7d9e7db6ff7df3bb9f7de6ffefdf7f7ffbffffdb86bebf72ffffeffdbfffffffbfdff7ffdfefff57faf7bfffaffffddddee,0x2eeef7ddefdfeff7ffbffff7ff7ffffffffffffffffdfa6ffbf72ffffffffbfffffffbfdff7ffffefff5ffbf7bfffeffffddfdef)
def v56 : Sig := (0x2021802000281040100114540890118670042783a09869c1400ec34a9418882db0990d900acd808121412a480a8a325b4098ca,0xe2861952e942a554c9361947d5f99538ff3cc67b3a0f86ddb700ec75b94988aedfcb98d940acf82c3e143be4baaae335b44d8eb)
def v57 : Sig := (0x10090006182017cd348006c829d56d02490c705800024306301820101100a622800f041225003201124a0a1184b0058900044234,0x1003000210201588b000064800806400400c30180002038220082010000026200003041221003001100a08019410018800800214)
def v58 : Sig := (0x2240d451c61b00200b0ba000802002cc00830a80785920000aa7002c246b4115524022c0426000526c84348403447044a4000100,0x20c09448c00bc020032880208020028c300003804859000000870028a46b4115120042404a6000542c04b40000455044a4180100)
def v59 : Sig := (0x3269f5d7fe3b3ffd7f9ba7dcfdfdffdfcfff7efffbfbfb6ffbff2eff7fffffbfffffbfdff76affd3ffef7fbfcffeffffff44dbfe,0x3eebf5dffebffffdffbbe7fcfdffffdffffffffffbfbfbeffbff2effffffffbfffffffdfff6affd7ffefffbfdfffffffffdcdbff)
def v60 : Sig := (0x200e0500603000008138014000000d006030281b8f1880889e50c274ee519194b703080d04a8812ec84618c4b067062ea40084a,0xa28e05d06978a514eb3e1b4617799dfbf53cfc7b9f1d80cd9e50c6f7ffd99994f7cf880dc4acb16ecc5e3be4ba7f467ef44c8eb)
def v61 : Sig := (0x818002e01e490430460402803c30c203900f148000245961408b11011008000000e44120d94222d10588a5084b1050900a54620,0x11110a221160100a0040100a0280042000043008000205920408f110000004200002041201942029101a0840a410010800a30610)
def v62 : Sig := (0x20601581e018283043082100d428920d80f00c2643083061420202c8201a408434808b4d022045c00121142200488a1415009180,0x24c01580e8086024010800009c08020000a00020420820610212028080024006b080034d022004c00320140000480a1010181100)
def v63 : Sig := (0x2a78f5ffe7ffb8734f7be13cd7eb9efdbff3ffeffbfbfdffdfefbfff7fffd99d7ffeffdfdffeeffffdfdfffecfffff7fffe5dfea,0x3ff9fffffffffa7f4ffbf1beffff9fffbff7ffeffbfbfdffdfffffffffffddbffffeffdfdffeeffffffffffeefffff7fffffdffb)
def v64 : Sig := (0x1280f908a820c20c4441a129081020902868105450030000005394538c67910cb09041080c0970230c300306006100409e084862,0x20c05188e800ca640c2121248c5118103160000458090048005304438c23810db0b043081c00400284240306406900209c084060)
def v65 : Sig := (0x1fa7ff6fbbfed60fd7cff7ab7834e3ffe8eefddf7777ffb77ff7f77ffffff7feffdffdff6fffffff6ffbfffebff5f7dfbffffffe,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v66 : Sig := (0x407042100940000808c44800000032240808902270063b37e0020241118664246052ce74324039c63c1b4f01390f78501972090,0xe2f2c35069f2591b1deced1518e63a2ce9b8bf3a7a4ebb3ff88aab413187e524e073ce7e3271fdd7bd1f4f91792ffd543973997)
def v67 : Sig := (0x20880990cc01a130206108410952288039590264c0890040801a88938c02980990a00208980150031c340005402b0860d2084822,0x20c05188e800c024042100048c5108003160000440090040001204038c22800db0a0030818004002042401044069002090084020)
def v68 : Sig := (0x9200246134a1403130212027024c04d8006648900749c0401a44308628000b0094a901020d28c40000a4808ac04001a2060970c,0x111082421160100a4200100a2220844d00047408005214040024510860c400a00148801000d8a020000a0800a804000a20608608)
def v69 : Sig := (0x2daf0ff7dfdfb533b3ef5ec37976ebeff9dfefefe7fdfff7ffbeebbfff9afefbdfefbefffbf7dfdf7ffffcfdffbffffff3ffffbe,0x3ffffffffffff5bff7ffdedfffffefefffffffffe7fffff7ffbeffbffffefeffffefbffffbffffff7ffffdfdfffffffff3ffffbf)
def v70 : Sig := (0xc23060613de0001118e408010040160c00465832730290035802224110840124805141142a48b544309c0a00910161321540400,0xe282414029f2001019ac08010040100820001c3a3202800918002a41108401248041001c2200b544301c0a00102165103140002)
def v71 : Sig := (0x2d379e67d7de5ffbfbce7ebbf3beffeffcffefbb3ffeffbf7ffefb7cfbdffffb4fcffdff7fffffffffdbfefbbfdcffbfedf7ff9c,0x3f3fbe77d7ff7ffbfbdefffbf3befffffefffffbbffeffbffffffbfcfbdffffb4fdffdffffffffffffdbfefbbfdeffffeff7ffdf)
def v75 : Sig := (0x380e1048114020045c3212b281460cae840490450415417516200260005d008024c00a80410c00225604da60204918203018260,0x200600400140a404c83210420548842884048041000500c5160000640849008004c00800400c002004041a64200802203008060)
def v78 : Sig := (0x420208004040841020184086011424130430910c0c2840a2912fd0b0200067a133c3107867346c921412013179681924d85504,0x24c61788e948e5a6b12c1e639e29763c73ac31b94e4d2a63a2932fd1bc236367b1b3c37d7b7734ecb7341e0131797a99bcd97505)
def v79 : Sig := (0x880441003802f638d0021a71866e848e083c12c7241900b080200040081ca000c4c00ac8510400225614d06408090a201050060,0x800401002800a410c012184005688408043c0043000900808400006008088080c4c008084004002004141064080802201040060)
def v86 : Sig := (0x920046503941403818204827024c04ac082c9082260d41759200024408042000e4c00a60110830061c14cb80284918201058280,0xa2820150694001140820090610680428803c80020a0d00459200004408418000c4c00808000830040c140b80282800203048080)
def v87 : Sig := (0x1d771eef7bffd48fb3bedec2f6add77fd7beffdbaf7efff7ffbdfffdfffa67f7fffffff77bffbffdfbdffef9bffdffdffdffff9e,0x3fffbffffffff5bff3fedefbffaff7ffffbffffbeffffff7ffbffffdffff7ff7fffffffffbffbffdfffffef9bfffffdfffffff9f)
def v88 : Sig := (0x802060003c00403910010821024c06cc086e1892644b8032a802304308042620d4f80b46176044c23415c003190f09b21d51504,0xc06061003c82583b10c1ec3122ee66cc28ff1b92644ba23aa802b9430806a620d4f80f5e37734ec33515c013190fa9b21d53505)
def v89 : Sig := (0xc0401800006be40c2029658e433c00330110345809004880130cd080218805a03043089c017022943403074069082004084060,0x20c05188e800ca640c2121248c5118103160000458090048005304438c23810db0b043081c00400284240306406900209c084060)
def v90 : Sig := (0x5250067101e1000028e46006000030300000c02013047b4552440284318249042003c4302808b90408aa0f88e0407040022a298,0x1339a8671437101842d2c018618001830c100e4281b24594552cd028435c149042003c0200888b11488aa0f88e06054442228a9a)
def v91 : Sig := (0xde7467f13de7fe79fae7fe7fe67ff6ff387fdbf7f7dffffffb76ffcf3b9eef7ef7ffffffff7fffef7fffffffffdffbf25fff7fc,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v92 : Sig := (0x21000610001401108006807004c103c004640b0320db2771002200539026a20d0f9c1721028f80034b48388c90879b0144929c,0x1e2b201716b43599f09246d8718ee543ce9ffc7ba3a2fba7fb282a9453943ea24d4fbc97a10abf8153cb48b99f92af9b43c49a9f)
def v93 : Sig := (0x1008218028202bdc6410015c0dd93c100f7810748082004880580cd308049808a0b001089408700190200303402a08205a004862,0x418028000a440c0121040c51181001600004100000480050044308008008a0b0010814004002802003064028002018004060)
def v94 : Sig := (0xd06066103de0002830e50020020026c00828980245424900ea4412c20084050424020e042f4005c6080b4c03304700420b32500,0x1148e60014b0002034c9803022002ac00000380045404100484d128204840500200006042f5007c2810b4402004504420332500)
def v95 : Sig := (0x1d2f27e73bfe3fdff79e57de7dfdff7fcffefdffa7f6fffffffc6fff7b9cfefaefffbdfff7feffddf3ebfffbffbeffbf7bf7fffe,0x1f3feff73fff3fdfffdfffdf7fffffffcfffffffb7f6fffffffcffff7bdcfefaefffbdfff7fffffffbfbffffffbeffff7bf7ffff)
def v96 : Sig := (0x800006603c6100300024000000000600002e1892070cd961da42124538000104b4e349241d68a1c60c8e8d88f94750b20e50608,0x1b39aa7717f7101b42d2d09a63a685ef8e17ffcba1f2dd96ddacf93c73dc1cb04f4ebc92c1deab3d78dbe8f8af96f54f63e78e9b)
def v97 : Sig := (0x218e018042180400c71803c03c30c903f0112409883000880499c130c659909003040009c0820239c14030440230060ca004862,0x400800008a400c212124005118103140000418010008004104430c218109003040001c00400284040306402100208c004060)
def v98 : Sig := (0x527060110180400938c16827024c30fc0840c020704322162004208201866e204018865222005c003031420300082940112b194,0x406040000082580b10c0e41100862004088003006042221220002800000624200010065222114c00300140110000a9000103104)
def v99 : Sig := (0xf3fe67f17ff94439fffd6be73e7cfffff87ffcbbff7ffbfffedff3f7ffdfffb4f7ffcf7fffeafffffdffffcffb7f7ffebf7fffe,0x1f3fee7f17ffbfdbffffffff73ffffffffdfffffbff7ffbfffedffff7ffdfffb4f7ffcf7ffffffffffdfffffffb7ffffeff7ffff)
def v100 : Sig := (0x8009008814800000c50001081021826848094445014213741280378d1ad408928404e90a0550872f7084a4023191c5931b6822,0x22c47dace81fc02405ef88058c556ba2f9680bd5450d4253759284378d3ad45db2a407e97a2558df2f74f5e44279d1f5931b7923)
def v101 : Sig := (0x240f04b144812130a0284cc001420a2011918222a28821e08a08288010002a4344212a06d120031850853051518a6e2040840090,0xc2b001106802591b01046d0518a000006938022a2a0a9a08a082a8012002a024c033806810207005081001915822e0040840094)
def v102 : Sig := (0x1300f20c3128420c4502a12a20044058802454111056140401e15448206501b42058c1102498a860000a4b02284400122c409740,0x1110824211601a4a4a00312a2220945d000474081852140c0065514860c501a00158c01004d8a020800a0a02a804000a2c608648)
def v103 : Sig := (0x378fffbdfdbde33ce5efedeb29566bfaf9fddf77f7df77f7fffbfcffbd7ffffff6fdefffffbdfbff7ffffff77bfffff7ffdffff2,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v104 : Sig := (0x1280630c393c80040587810008040150c0045545451100003581042705284014b0140411028488440328c1a40831105333580462,0x2c0658c281f800405ab80040c450100810001c5410100401180042705284014b0240201422008540324c1a44021105113180022)
def v105 : Sig := (0x3394fb6dfd3cdffeefc7bf3bebbeffdffcffdf7d5ddfd6bf7fffdd7feffffffdb7deedff3fdffcefbffaffffbefdf9fffffbfffe,0x33d7ffeffd7fdffeffefbf7feffffffffdfffffd5ddfd7ff7ffffd7feffffffdb7ffefff7ffffcffbffefffffefdf9fffffbffff)
def v106 : Sig := (0x17d7fb8ef97fc28c77fffb6bae9d77ffff7c7fd7dd5f7ff7f7ffffffbf7ff5fff3fffff97efffcffbf7effe7bf7dffdffffbff7e,0x37d7ffeef97fffeeffffff6fbefdfffffffc7fffdf5f7ffff7fffffffffff7fff3ffffff7ffffcffbf7effe7ff7dfffffffbff7f)
def v107 : Sig := (0x804208010042040500212308046048e00451155445100320930454a021c024a05cc1b82c15706627704f062071909325595560,0x20c45788e948ca660d2d39278e75fe7cf16c719d5c4d124b20d30557aca3c16db1fcc3f97e7570eea7745f066079d0bbbd597561)
def v108 : Sig := (0x842041002c02de3982018c496639c241383a0a82a08a8488a002b8010800a430d230204d1620408900510015188682800840004,0xc02001002802581b00006c0100a0000028380202200a8208a002a8010002a020c030004810204001001000111802a0000840004)
def v109 : Sig := (0x1300b904b83c800840c780082010019208680c40011246145560d02b0d5e15981280044102888881080a80a00a0401449a02aa02,0x1310a8661037100842c280082000018308000e40011244145524d028415c14900200040000888811080aa0e08a04014402228a0a)
def v110 : Sig := (0x1bc2ff1cbbfcefefdde7b9efbe77fdfefbeffdfd7f5ffe5ffff3ffffbdffdfffbfffc7fdfffffcefbf7fdfa77bfdf9ffbfdfff66,0x3fd6fffefbffffefffefbfefbe7ffffffbeffffd7f5ffe7ffff7fffffdffffffbfffc7fdfffffcffbf7fffe7fbfdfbffbfffff6f)
def v111 : Sig := (0x100021043820020c4480010828146112c86c54550102520771500453091494a8a09c85192408f881036a4b22083081931b40da62,0x1200618638341a4c4c83210c2c55fd53c96c7c5d1102524f71700457499494a8a1fc85993408f883836a4ba6ca3881bb1b40da6b)
def v112 : Sig := (0x29008200003dd1301006d455c99c010710202a82a0896880082a8052802a020d2318069102070090010019c48a0e284004009c,0xc2b001106802591b01046d0518a000006938022a2a0a9a08a082a8012002a024c033806810207005081001915822e0040840094)
def v113 : Sig := (0x380da08811cc0000147a023000000c8200009005455041004a3d02ca46b4114124040e00a9500662c10848422451044a41b2500,0x21d49e68c14bc022036c9823822002ac300003804c5d04100487d128a46b4155120042604af5007c2c14b44020455044a43b2500)
def v114 : Sig := (0x13a9fb8eb93cffdd75d7a7ff7dddfddbef7c7d7fd7f7df7ff5fbfeffffffffbebfffddffbf9fffe7bf7bcfbfeeff9fffff5ffffe,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v115 : Sig := (0x200e00c0124800004438028000000d0280051411053441615e194370d659118025c44900c9ca8272c58cb840a351143aa414e62,0x1310ea6e11779a4a4ee3b12e22759dffb9447fcd1953541e55e5d57f6dfd95b9037cc4905cdce83fac5eebe6ea35d16faf63ce6b)
def v116 : Sig := (0x818007206c310430830401403c30c201703a288a8a08988880c29005280080149223002d1420218d0842058c582642840a40008,0x829001106800011001040904182000006138002a0a0898088082800120008004c02380281020300508100180582240040840090)
def v117 : Sig := (0x11801b00b818420c418421032814610ac06c0c144504120160124048a01a44a4b0808169220150c00322042220408094151ab100,0x20c41580e8084024010c08018c00620040280010440c02412012000080024044b0800369222110c0032014000048009010183100)
def v118 : Sig := (0x1b98fb7ebfffd24f4df7e13f2bd76dfaff6fffddfdf7df9ffdfffd7fffffddbdfbfef5fbffdffafffffeeffeeff7f5ffffffff6a,0x3bfdffffffffda7f4ffff9bfeff7ffffff7fffdffdffdfdffdfffd7fffffddfdfffefffbfffffbfffffffffeeffff5fffffffffb)
def v120 : Sig := (0x20040821c4000130a0400c0101122a8238d98a20008842b34a1a88108812be49068028ee1901508b3cd034511288e9a4c0836890,0x20071821c40045b0b0440e51c19a6aa27cfb8a30048cc3b36e1aa8108a12be4906832dee3907548b3cd0345916d8e9a4c0837995)
def v121 : Sig := (0x110904000005eca4a00323ae2a8d40d042200181846940c0064514862c501a0014ac100245a242080020a0aa44400080c20930c,0x1110824211601a4a4a00312a2220945d000474081852140c0065514860c501a00158c01004d8a020800a0a02a804000a2c608648)
def v122 : Sig := (0x48b05900895a00000ad40c00840012041000146e7012140b40020a715084002d0250601c2240314432580a441331641131c0022,0xee8659c2a9fa00505bbc0841c450100830001c7e3212840918006a715284016f8241201c2200b544325c1a441231651131c0022)
def v123 : Sig := (0x259f9df1cc95fffaeaed7efbebfaffaf7dfb8b7effcff7fffe7ef9ffffdfffebd7efefefff7f77bffff7befff7ffffeddfbffbbe,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v124 : Sig := (0x407088048018000202c48400000032011180242850823e0a618a8919d1a2443d0a12e415a25109d1a14b04111396e45d09a6812,0x24c71da8e80be5a4b17cce419c8963a077b803f3c70d2bf3a69aaeb19f3a6657f2a33f6f7b271cdd3f34b44115797fd5d09b7917)
def v125 : Sig := (0x1050120a306a408c1210920086891415062434910816080000855748226001b42112d11020ca2c60800a0200ac4000182c60150c,0x111082421160100a0200102a0220141d000434080852040000055148204101a00110c01000d82020800a0a00a80400082c600608)
def v126 : Sig := (0x208805318494213080c104810952288268c1892462814013580200260000da08060400ae8100430265e104b4428291a0030500a0,0xa2860150694001104830094415608028843880420a0c00059000006000098080c0400808000430240c141bc42828020030400a0)
def v127 : Sig := (0x34df1fbbfcffe1bcb2fddec18fdb3fb77ffdbff7ef9f6bf3fe9fffffbf7afffff7b7fffffbef7fffffffb6f5fffbfffdffff7dbe,0x3ffffffffffff5bfb7ffdeffdfff7fbfffffbfffefffeff3ff9fffffbf7bffffffb7fffffbff7ffffffffffdfffffffdffff7fbf)
def v128 : Sig := (0x82041000802120802008c1084228207181812466092043aa1228949000ca43842502acd925500e3775140551b9f8a1019d4020,0x2cc65598ea88e5a5b52d0ec59c5f6a20f3eb81b5660daa63aa922e979c22ea4fbca703edfb2754ce3775550551f9fab1919d7125)
def v129 : Sig := (0x840420803404ec71d0031269625d44c82067099184498080081074020a10024295ac1102452246080004b022040001a24401544,0x20001400a42080031220220945c000470081840100800410140208101200158c0100450202080000a022000000a2c400440)
def v130 : Sig := (0x240d09a1cc15801020cd44000110038208580a42818043b0540880230d1a340852802c43020003914880a0f002020744d2022892,0x22928250417001000d2c010418001820c100a4281a04190550880200318141042003c0200000b114880a0f80602054442020892)
def v131 : Sig := (0x2ccf4fb9cfd5eff7bded7de79f77ffeefbdffbffffcdfbfbfe9baff7bdbbfe6fffffefffff7777fffff5fff773fbfffff7df7df6,0x2eef7fbdefdfeff7bdfffff7dffffffefffffbffffedfbfbffdbaff7bfbbff7fffffffffff777ffffff5ffff77fbffffffdf7df7)
def v132 : Sig := (0x9018008002110208004c0095029024958006683804363f01828931910be0a84a50c0f910053811361003140ba8fa1530448b2,0xe2b61952e942595b49346d45ddf6902cffb8877a3a0ebe3fb182e971b10be0aeca73d8fb1025f8353e141bd57baafb1538458b7)
def v133 : Sig := (0x1020200630201ecd5410031c748dd411862474190022980c01400640428400a0291a9110240aac00800a4b0a8c00001a0840924c,0x1000000210201a484800210820009451000474081002100c00600040408400a0015880100408a000800a0a028800000a08408248)
def v134 : Sig := (0x24860c31c4958020806d4801000202a030818b00640920900e028024840a4041520022e04a25001e6c94b4c413017044809b2000,0x20c41c28c00bc020016c8801800002a030000380440d001004828020842a4055120002604a25005c2c14b44000415044801b2100)
def v135 : Sig := (0x34af2db7fcb5bffdf4fd4fdd7ddfffb3fffdff7fe7abfbffff5aaef7df9efeebffbfbfffff2fff9fffffffffdfbbffffdbdffafe,0x3eef7dbffebffffdfdffefddfddffff3fffffffff7affbfffffaaef7dfbefeffffffbfffff2fffdfffffffffdffbffffdbdffbff)
def v136 : Sig := (0x800300485800000614000014208a039018340a08141929c08a8371d00980942242482d904021f7cd4a0d443b37561c2854822,0xa29683d0697801104f3c09441d709a2bf538bc7a1a1c992dd88ac371f389c194e263c82d9064b1f7cd5e1fc47b3f565c38748b3)
def v137 : Sig := (0xa10e04e036210430c12803c028104500602708918728c0c01e5150042e50110095a501004daa82080084b088c04000a28600648,0x1110824211601a4a4a00312a2220945d000474081852140c0065514860c501a00158c01004d8a020800a0a02a804000a2c608648)
def v138 : Sig := (0x24870d81c8102130a08c0cc10810230240d808264708226162120080801a664294810a6d022151800321142110088a84111a2090,0x24c61580e80865a4b10c0e419c08620040a80030460c22612212028080026246b081036d222114c00320140110480a9010183104)
def v139 : Sig := (0x2e9fedffcff7b173acffccfd0bd32ff27fdbfbeffffbefffffffbdb7dfffff5bdfff7effdffffbbffffdfffddfbfffeffbff6efa,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v142 : Sig := (0x1418004000408822001a008288160514380210080e02a0021cd958aa5225e10182e940384b34a998123241b448680ccca2791c,0x31179a62d16055aab2441e6b82a876bd74bc36380c5e07b3261ff958aa5327e10393ed7e39df34a9bc1a3e41bc5c698cece37f1d)
def v143 : Sig := (0x1443028a386b8004103cc04004010130030434c385102940a481268115280016f031161142a40854020c80000931065130580402,0x4c00588280ba0040138c0001c010100030001c3c3012840808006a115284016f020120142200854032480000121165110180002)
def v144 : Sig := (0x2100806184001f72c840243b6132e88a28c3882810c0d41f4862000040859a08064800ae0510400224c00c1a028481a000018280,0x104000a5048002110611288420843c8001080d00c4860000040849808044800800400c00200c0001a02808022000080c0)
def v145 : Sig := (0x35579aebfc6bdffefa7cfe7be7bbffbf3fffbefb9ddeffffeeffffd9ffffbffff7fbffff7fff7cffbedebe5bbffdeffdfcfbff9e,0x35d79febfd6bfffefb7cff7bffbbffff7ffffffbdfdfffffeefffff9fffffffff7fbffff7ffffcffbffebe5bbffdfffffcfbffdf)
def v146 : Sig := (0x4fe2880038238222fc0c30838038184c900b0a120950a0818a61054ac1ac3d53742ab4501e0330c8e8a804815104,0x20061200c1404fe2b8043f63823afe7c70eff0381c4c922b2a532950a883ab6905dbc1fc3d5774aab4501e0330d8e8aaacc17545)
def v147 : Sig := (0x8c2461803c02005152001c41c450060c304718566012840a081268410204006a8350210c02400440325410441311013215c0460,0xcc045982a88a005052900841c45000083000185620128408080068714204006b8240201c22000440325410441211211111c0020)
def v148 : Sig := (0x21149861c400101862400618619802830c780a00008246b4406cd0084a56358802802842000800810882205886040104c822aa98,0x111188631420101842400018618000830c100e0000924594442cd0084254148002002c0200888001088a20588e04010440228a98)
def v149 : Sig := (0x29d6de79c7c07fffff603ffffffffeeffffffbbd7ecffeffeaffffdcfaf7ffefafffebfefd7f74efbff77f5ff7fdf9bfedfffffc,0x3dd7dffbffe8ffffff6d3ffffffffeffffffffbd7edfffffeeffffdffef7ffefbfffeffffffff4efbfff7f5ffffdfbbffdfffffd)
def v150 : Sig := (0x1fd8600006186198fc030c7800380082d22f405808504a94bea8058a890e350a748190420a1b848889a84800da9c,0x1003000314201fd8f8002758619afc534cfffc381082d3af6a7828504a94bea805dbad9e350af48390ca0a1b9e98a9aa48c0dadd)
def v151 : Sig := (0x1029218638202005149001c41c450110c304744783200940b100268311000002a835141180008b00032941204832061313440062,0xe2861942a942005049340841c45010083000047a32028409100068711000002e824100180000b00432141a44122061113040022)
def v152 : Sig := (0x21149861c40040228a4038238222028c30838a00184c04900a26d108a0430141024060e00851002a2c9034403244600484a32100,0x21149a60c140402202441823822002ac300002000c5c04100407d108a04301410200406008d500282c10344020444004a4232500)
def v153 : Sig := (0x313db9e7fc207ffffed03fffffffff9ffffffe7f9beedffffb7effdbfbd7bfebaffffdffbd5bffabbffb7f7bfefeefbfdfe7fbfe,0x3f3ffbf7fff47ffffed77ffffffffffffffffe7fbffeffffff7fffdffbd7bfebeffffdffbddfffabfffb7ffffffeefbfffe7ffff)
def v154 : Sig := (0x108060040010420840003803820c803c03820818c2c49e086c99104ac59909034a60821d5a202bbcd02a5886846128c8a14a08,0x11118a6315601a5a4a40313a63b29cff3c57fe0818d2d59e4c6df9586ad59da9075aec921ddee02bbcda2a5aae94e12eece3ced9)
def v155 : Sig := (0xa08601e03e780010433c00400410070030071c1a0310900958124271520001048341410c0848a14400cc1844933144322440462,0xa28601c0297800104b3c08400450100830001c7a1210800918004271528001048241000c0000b144005c1a44123144103040022)
def v156 : Sig := (0x21041801c0004fb8e2003e03e038f20f00f80830000c122142124048a01226e00480896c2001548000021403304888840402b194,0x20061000c00045a0b0040e418008620040a80030040c022122120000800222400081016c20011480000014011048088000003104)
def v157 : Sig := (0x2b1cf87fc7e7dffbee73fe3fe3fbfeff3ffbfbf9b8ffdfbfdffffd7ffff7bff94ffefdfefddffebffcdeffdffffffdefeee7fffe,0x3b3ffa7fd7f7dffbfef7ffffe3ffffffffffffffbdffdfbffffffd7fffffbff94ffffdfefddfffbffcdffffffffffdefefe7ffff)
def v162 : Sig := (0x14151882782b8008221cc2000088031104380642811203a0040cd0090f5a259050803c4102880891080aa0408c000644d822281a,0x11118862102310080250c008008001810410064281120590040cd0280358049042003c0200880811080aa0408c04054440220a1a)
def v163 : Sig := (0x1cd75e9a7bebefefbf3cfbe79eefff7df7bff7ffff5fbbebae9fffddbffbeff7fdfffffdffff7cffbf7fff47fdf9fefffdff7d7e,0x3dd7dffafbebffefbf7dffef9efffffdf7fff7ffff5fbffbaedfffffbffbefffffffffffffff7cffbf7fff47fdfdfffffdff7f7f)
def v164 : Sig := (0x100100823820008c3010024004891511073c345381020b60a0182ed11b1024a2a1b39d11300a3c81920a02018c380e195840581e,0x140301823820358cb01046481c89751147bc347b83022be3a2182ed11b1026a2e1b3bd1f310a3c81932a0a019d382f9958c05a1f)
def v165 : Sig := (0x28210400003f514480059c7954e802c840402c02a0d00f5140000240849a080c0c000e8500c3000161493a408281a2030482e0,0xa28601506940a514c832194615688428843c80430a0d00c59600006408498080c4c00808400c30240c141be42828022030480e0)
def v166 : Sig := (0x4561a08404bc000022cd80082000224100002800c1c20800685d108a46a0155500062404ae5007c0814b04031416044a4ba2500,0x21d49e68c14bc022036c9823822002ac300003804c5d04100487d128a46b4155120042604af5007c2c14b44020455044a43b2500)
def v167 : Sig := (0x147f3b8e786bffdd76bcdfdcffddff37df7c76ff8fbefbeff7ddffdbfffebffffdbfff5fffeffffd9b7ffb7bfdfbeffffffefffe,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v168 : Sig := (0x10000a006380000030c00002810430170032c188120980848dbd111f6001114132741058ce283d981ca2408d316449e8e04c0a,0x11118a6a1163900a0270d02a02a115bd371437cb89530d92848dfd793f7905b14332fc1259de283dbc1eaa40ad35754dece34e1b)
def v169 : Sig := (0xa08e074078410430c43003c014208c02803c10830e1c41e19600026408598080a4c00828510820264c0499c4286112202050260,0xa28601506940a514c832194615688428843c80430a0d00c59600006408498080c4c00808400c30240c141be42828022030480e0)
def v170 : Sig := (0x14471a807808408c320c1a4084081305003c0412050c2260221042c8a01a24e6b0818b41222114c00202100130480a14141a3114,0x24c61580e80865a4b10c0e419c08620040a80030460c22612212028080026246b081036d222114c00320140110480a9010183104)
def v171 : Sig := (0x1e5ffafe7fefd0cf3e7fda7c87cb1ff53f3ff7dbbdffeffebffdffffffffbdfffbffffd3ffffbefffedefbddffff7f7ffeff7f7e,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v173 : Sig := (0x2fc5140001c41c45fc00c304703d0200984ba0102ed010808a22ad3f811cb502740093614b0340b888bb01445064,0xc0241902a802fc5bc0127c41c5ffc50c3eff03d3200ba6baa502ed71880aa2aadff819db502748293614b0751b8aabb19c45065)
def v174 : Sig := (0x102921863820101860900618619801130c78044281a24324514800034b14348800801c0300088b81000a00388c0207005a008a9a,0x122920071434101840924018618001030c100c4281a24184512800004314148040003c0200088b01408a00b88e02050042008a9a)
def v175 : Sig := (0x8c2461803c04022892038238222006c308381807c4d20000a830104a0214045004042a04875006e241414043141700024990500,0x20c41608c148c022012c18238220022c300001804c4d000000830100a4234145100042604a75006c2414140020415000a4192500)
def v176 : Sig := (0x18eb679e3be07ffffdb03ffffffffd7ffffff5ffffeffb6ffbdb2fd7fbb5feefadffdfbffd7fffefb77f5f3ffdfbffbb7fdddffe,0x3eef779ffffcfffffdbf7fffffffff7ffffffdffffeffbeffbfb2fd7ffb7ffeffdffffffff7fffeff7ff5fbffffbffbbffddffff)
def v177 : Sig := (0x800401803c000430c20002402430c603303f1893841880a88812d1410a18801097e4090dd56202eb4544b0441b1702b20c54460,0x800421803c08a430c2131a602779c7cb347f18d3841980a88c12d573ca189290d7ec090dd56602eb4554b0661b1f02badc54461)
def v178 : Sig := (0x218a066042790000053c018018000900c00024080b24594156c90234f4411184200340200888a114888a0d88e060540ca200a0a,0x1339a8671437101842d2c018618001830c100e4281b24594552cd028435c149042003c0200888b11488aa0f88e06054442228a9a)
def v179 : Sig := (0xc2060000006fa4910039c39c24f00cc0840034460c3041221202c0a0004266a401832c20215440032114033048889005181104,0x24c61580e80865a4b10c0e419c08620040a80030460c22612212028080026246b081036d222114c00320140110480a9010183104)
def v180 : Sig := (0xadae67e07e7ffe79d73f9ff9fe7fcfcff87f3fdfefffddfbfffbff7ffe5db7fef7ff7befdfffe7ffffdffdffffffdfbeffd5f6e,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v185 : Sig := (0x82006002010410410001c01c10c100f00704980a2c90e91482c135b849808093e1412950aaa0190484b18ccb2052b4a444a6a,0x1a29601716b41a594c93619c61d79d538f57fc4fb1a2d98ed9682c575b949ca84d7ebc92950aeb03d0cb4bbecfb2a52b4bc4cafb)
def v186 : Sig := (0xa10c07807c780020863c020020200e030038380385104900ca59124046101114240608048d4003e6c94a0c403057040a0a10400,0x1108a680143800202609022022000ac30000380085104100485d128246901110200400048d4003c2c14a04020055044a4230400)
def v187 : Sig := (0x1021018038002f9c708007c07c1cf103c07c043603001261601002c0001026a2a481890d200055800323002300088a9011009094,0x402018028002584b00006401c08600040a80030020022612210028000002202a081010d200014800320000110080a9010001004)
def v188 : Sig := (0x1a39e1fe3fe7bfdf7cf3c7fc7fdffdf3ff7ff7ffbbf3dffffdfdbff75ff5bfbbeffffd9ffddeffbfffffebffcfbffffbfbe5defe,0x1f3bebff3ff7bfdffef3f7fe7ffffdffffffffffbbf3fffffffdffff7ffdbfbbeffffd9ffddeffbfffffebffffbfffffffe7deff)
def v249 : Sig := (0x300f304b11c00004187a102200441dac0644d055555561775e3446f2d7f55bc32dc85f9229cc8c62f6acda62a5491d7bf53bf42,0x33d4ffeef97fda6e4fefb92fae75fffff96c7fdd5d5f565f75f7d57fedffd5fdb3fcc7f97efdf8ffaf7effe6ea7dd1ffbf7bff6b)
def v275 : Sig := (0x2c6704f346c33c339a185694d42892250693a2aaaaa8a9e88a042b8052802a434d233a06d1620718c0853058d58a6e2840a4009c,0xc2b001106802591b01046d0518a000006938022a2a0a9a08a082a8012002a024c033806810207005081001915822e0040840094)
def v304 : Sig := (0x240705b1c4952030808d4480000003a240d18b26e78963f3fe0228a71d1a7e4b56a52eefd324439e6fe5b4f4539affe5d3972892,0x2eef7dbdee9fe5b5b5ffced5dddf6ba2fffb8bf7e7adebf3ff9aaeb79f3afe5ffea73feffb275fdf7ff5f5fd57fbfff5d39f79b7)
def v329 : Sig := (0xb60f246334a1c035b12b316f42cd05d8626648918749c0c01e5474862e501b4295a911020da8c40800a490aac44001a2c60974c,0x1110824211601a4a4a00312a2220945d000474081852140c0065514860c501a00158c01004d8a020800a0a02a804000a2c608648)
def v356 : Sig := (0x21049061c4001c32ca003612e028d28f04f38a2818ccd6bf4a6649486ad73fe907caa9ee315a448aacc23c5ab6cce9accca3bb9c,0x31179a63d5605ffafa443f7be3bafeff7cfffe381cded7bf6e7ff958ead7bfe907dbedfe3ddff4abbcda3e5bbedce9aeece3ffdd)
def v379 : Sig := (0xe63679633df2001119fc18414040170c2046587e7312940b58126a71528401678351611c2a48b54432dc1a44912165333540442,0xee8659c2a9fa00505bbc0841c450100830001c7e3212840918006a715284016f8241201c2200b544325c1a441231651131c0022)
def v404 : Sig := (0x4471282704b0000121cd20084081335063426838d1c2be0a6856fc93f7a25f771b3bf5172ee0cdc8a0eb040bd586e5dfcf23d1e,0x35d79feaf96bf5aeb37cde6b9ea977bd77bc37fbcf5f2ff3a69ffff9bf7b67f7f3b3ff7f7bff3cfdbf3ebe41bd7d7fddfcfb7f1f)
def v424 : Sig := (0x2b20e57587943c33c98325967024c0cac0c3c92c72e1d41f5962002640855a080e4c00ae8110c30265e14dbe428691a2030582c0,0xa28601506940a514c832194615688428843c80430a0d00c59600006408498080c4c00808400c30240c141be42828022030480e0)
def v447 : Sig := (0x842461003c02c23990031869424d06cc287e1ad7e4db84baa832fc430a14a672d7f83bcf176444ea7655d0671d8f8bb25d51544,0x2cc65798ebc8efe7bd2d3fe79e7ffe7cf3eff1bd7e4dba6baad32fd7bca3eb6fbdffc3fdff7774eeb7755f0771f9fabbbddd7565)
def v466 : Sig := (0x2725b1e7f41f1010429fc6106008039304700e0281b047b45564402b4f5e359852803c4302888b90488aa0f88e060744da22aa9a,0x1339a8671437101842d2c018618001830c100e4281b24594552cd028435c149042003c0200888b11488aa0f88e06054442228a9a)
def v487 : Sig := (0x21218630003c1150900794740cd113c674642f83a0db6ff1402ec35b943eaa2dbf9d1fb10acf80836b493acc9a8fbb5b449ade,0x1e2b61973eb43fddfc9367dc7ddffd53cffffc7fb3a2fbeffb782ed75b94beaaedffbd9fb50aff83d3eb4bbfdfbaafbb5bc4daff)
def v504 : Sig := (0x2f46d671c7df00228b0ff002802002ec00838b807c5d24900ea7412c246b4155524022e042f4005e6c84b4c433447044a4b32500,0x21d49e68c14bc022036c9823822002ac300003804c5d04100487d128a46b4155120042604af5007c2c14b44020455044a43b2500)
def v523 : Sig := (0xa00e07607c710030813c014000000f00603e389b8f1cd9e9de52d275fe519194b7e3492d1de8a1eeccce9dccf96756beae50e4a,0x1b39ea7f17f79a5b4ef3f1be63f79dffbf57ffcfb9f3dd9eddedfd7f7ffd9db94f7efc92dddeeb3ffcdfebfeefb7f56fefe7cefb)
def v538 : Sig := (0x25671781f0182c30d38c3782f42cd30fc0f40c26470c3261620242c8201a66e634818b6d222045c00323142230488a941512b194,0x24c61580e80865a4b10c0e419c08620040a80030460c22612212028080026246b081036d222114c00320140110480a9010183104)
def v594 : Sig := (0x300f900a01842084143a12b201060daa8680c155157561741f3d47fac7fd5bc32d8c1e92e19f8e32d724fa62a4491d6bf43fb42,0x33d4ffeef97fda6e4fefb92fae75fffff96c7fdd5d5f565f75f7d57fedffd5fdb3fcc7f97efdf8ffaf7effe6ea7dd1ffbf7bff6b)
def v609 : Sig := (0x200e0000000000000038000000000d0000000011051000001e104270c65111802500080000888022c0041840a041042aa400842,0x200e04c00178a404ea3a124207599dfb9404fc51951500c51e5046f6dfd9199037cc0805c48c816ac44e3a64a25d067af40c86b)
def v658 : Sig := (0x29218220003dd1701007d455c99c118770242f83a09969c1482ec35a943a8a2db3990f910acf809121413bcc8a8e3a5b4498de,0xe2b61952e942fd5fc9367d47ddf99538ff3cc67b3a0f9eddb782ec75b94ba8aedffb98f950acf82d3e143bf5faaae335bc4d8ff)
def v684 : Sig := (0x11a92b8e3924ffdd74d407ff7dddfd13ef7c757f87a6df7ff558fed3db94beaaadbfdd3fbd9fffa5937bcb3becbb8fbb5b5ffefe,0x1f3f6bb73ff43fdffcd77fdf7fdffd73cffffc7fb7a6ffffff78ffd75b94beeaedffbdbfb59fffabd3fb4bffffbaafbb5be7feff)
def v755 : Sig := (0x207404f146033df2aa181e14d7aa9e05169382aaaaa8a8e88a0c0b8042802a414d223a06d1620518d0853059d58a6a2840a0009c,0xc2b001106802591b01046d0518a000006938022a2a0a9a08a082a8012002a024c033806810207005081001915822e0040840094)
def v819 : Sig := (0x114986000005fcaea403e3be3bafc0f3c2a80181846d69e007cd158e2c5a7e0014ac1222d5b342990520a5bb4c401880ca3f31c,0x11178a6211601fcafa443f6b22a0f47d400c74181c56179e246df15860c527e0015bc43225ddb029901a0a43bc14018a2ce3a65c)
def v848 : Sig := (0x21149df1c4117ffaea493e3be3bafe8f3cfb8a3efbcff6ffca7ed9ffeedfffe957eaebefff7b75bbfdf73efff7cefbecdfa3fb9e,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
def v859 : Sig := (0x20040db1c4112130a0490c0101122a8238d98a26e38962f3ca1a88b78c1afe4956a02aefdb21519b7df534f5538afbe4d3836892,0x2eef7dbdee9fe5b5b5ffced5dddf6ba2fffb8bf7e7adebf3ff9aaeb79f3afe5ffea73feffb275fdf7ff5f5fd57fbfff5d39f79b7)
def v946 : Sig := (0xc2441002802920892029c59c62b86cf38381a57e49b84baa932ed4b0a1ca47ad7583acd967544eb775550751f9f8b325dd5160,0x2cc65598ea88efe5bd2d2fe59c7ffa7cf3ebc1b57e4dba6baad32ed7bca3eb4fbdffc3edff6754ceb775570751f9fab3bddd7165)
def v973 : Sig := (0x262db9e1ec1f801062dfc410411803930c780e4281b043b0556c802b4f5e359852803c4302088b914880a0f80a060744da02a89a,0x229a8650417001042d2c010618001830c100e4281b04194552c8028435c149042003c0200088b114880a0f80e0605444202889a)
def v1002 : Sig := (0x29218028002910609005d45d58b913cf78046783a0db6bf1582ed35b94be8aadb59d0f910adf819361413b48ba8fb35b44d8fa,0xe2b61952e942fd5fc9367d47ddff953cffbcc77b3a0fbeffb782ed75b94be8aedffbd8fb50adf83d3e143bf5fbaafb35bc4d8ff)
def v1027 : Sig := (0x26c6dc71c69f80208b6fe801802202ec30838b807c5920900ea7802ca46b4155524022e04a65005e6c94b4c413457044a49b2100,0x20c49c68c00bc020036c8821802002ac300003804c5d001004878028a46b4155120042604a65005c2c14b44000455044a41b2100)
def v1081 : Sig := (0x1280f30cb93c80044587a100080401d8c0645d455551100175e3046f2d7f519cb2d485d9028cc8c62f28c5a60a759057bf589d62,0x22c0f5cce81fca644faba124ac759bdfb9604fc55959504d51f7046fedffd19db3fcc3c95e68c8d6af64f7a64a6dd077bf58d96b)
def v1127 : Sig := (0xa08e05e07e780010c33c014004100f0070373c1b8f189089de52c275fe519194b743490d0ce8a16ec8ce18c4b377463ea440c6a,0xa28e05d06978a514eb3e1b4617799dfbf53cfc7b9f1d80cd9e50c6f7ffd99994f7cf880dc4acb16ecc5e3be4ba7f467ef44c8eb)
def v1184 : Sig := (0x1240461021a1402830a16027020c24f80828c8b2374feb74ba4432c629866f04f4ab8e763728dd861c37cf8bf84f39e21e3b39c,0x1f3fae7717ff359bf3dededb73aee7efce9ffffba7f6ffb7ffacfbbc73dc7ef24f4fbcf7e3ffbffd7bdbfcf9bf96ffdf63f7bf9f)
def v1209 : Sig := (0x2250f990e4016bf86851a93d879a3c903e790234d88b0048805b9cd38c67990d30b043089c0970239c340307404a0860de004842,0x20c05188e800ca640c2121248c5118103160000458090048005304438c23810db0b043081c00400284240306406900209c084060)
def v1300 : Sig := (0x370f040220a5eca4b12b33ef6a8d45d8622049918769c0c01e5574862e501b4295ad100245aac6080024b0aac44001a2c60934c,0x1110824211601a4a4a00312a2220945d000474081852140c0065514860c501a00158c01004d8a020800a0a02a804000a2c608648)
def v1321 : Sig := (0x541880600b408822189a008688161516380693891e2ae0829ddfd9ae7a25f571b2fb417a6b3cf998163241bd486a5cfce2791e,0x35d79feaf96bf5aeb37cde6b9ea977bd77bc37fbcf5f2ff3a69ffff9bf7b67f7f3b3ff7f7bff3cfdbf3ebe41bd7d7fddfcfb7f1f)
def v1342 : Sig := (0x2320e57186103f72c943253f7132e8caa8c3882c72e1d41f496200264085da080e4800ae8510c10265e14dbe428691a2030182c0,0xa28601506940a514c832194615688428843c80430a0d00c59600006408498080c4c00808400c30240c141be42828022030480e0)
def v1365 : Sig := (0x40441002006fe2890039279622fc4cb28380bd7a4db84b8a930fd4a0a1ca652d7ac3acfd73746ab5755f0771c8f8ba25c15144,0x2cc65798ebc8efe7bd2d3fe79e7ffe7cf3eff1bd7e4dba6baad32fd7bca3eb6fbdffc3fdff7774eeb7755f0771f9fabbbddd7565)
def v1384 : Sig := (0x2334b9e1e41b1018625b8618619802930c780e0281b246b4416cd02b4e5e35985280384302088991488220f88e060344da22aa9a,0x1339a8671437101842d2c018618001830c100e4281b24594552cd028435c149042003c0200888b11488aa0f88e06054442228a9a)
def v1405 : Sig := (0x20218020003fd86010071c7598fc138e78043f83a2da6fc1580ed34a94bea82dba990fb50afd8191634b3bcc8a8bba5b40dade,0x1e2b61973eb43fddfc9367dc7ddffd53cffffc7fb3a2fbeffb782ed75b94beaaedffbd9fb50aff83d3eb4bbfdfbaafbb5bc4daff)
def v1422 : Sig := (0x2354dc71c61b40228b4bb823822202cc30838a80785d24900aa7d12ca46b4155524062e04a71007a6c9434c433447044a4a32100,0x21d49e68c14bc022036c9823822002ac300003804c5d04100487d128a46b4155120042604af5007c2c14b44020455044a43b2500)
def v1441 : Sig := (0x210e070060310420853803c03820cd03e038289b8f3cc9e89ed9d374ee599194b7a7082dd5aa83bfcd46bdccf86716aeae14a4a,0x1b39ea7f17f79a5b4ef3f1be63f79dffbf57ffcfb9f3dd9eddedfd7f7ffd9db94f7efc92dddeeb3ffcdfebfeefb7f56fefe7cefb)
def v1455 : Sig := (0x21641d81e0186fb8e3083f03f438f20f80f80c36430c3261421242c8a01a66e434808b6d222155c00123142330488a941502b194,0x24c61580e80865a4b10c0e419c08620040a80030460c22612212028080026246b081036d222114c00320140110480a9010183104)
def s0 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8]
def s1 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9]
def s2 : List Sig := [v1,v2,v3,v4,v5,v6,v7,v8,v9,v13]
def s3 : List Sig := [v0,v2,v3,v4,v5,v6,v7,v8,v9,v18]
def s4 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v10]
def s5 : List Sig := [v1,v2,v3,v4,v5,v6,v7,v8,v10,v13]
def s6 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v11]
def s8 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v12]
def s9 : List Sig := [v0,v1,v3,v4,v5,v6,v7,v8,v249]
def s10 : List Sig := [v0,v1,v3,v4,v5,v6,v7,v8,v275]
def s11 : List Sig := [v0,v1,v2,v4,v5,v6,v7,v8,v304]
def s12 : List Sig := [v0,v1,v2,v4,v5,v6,v7,v8,v329]
def s13 : List Sig := [v0,v1,v2,v3,v5,v6,v7,v8,v356]
def s14 : List Sig := [v0,v1,v2,v3,v5,v6,v7,v8,v379]
def s15 : List Sig := [v0,v1,v2,v3,v4,v6,v7,v8,v404]
def s16 : List Sig := [v0,v1,v2,v3,v4,v6,v7,v8,v424]
def s17 : List Sig := [v0,v1,v2,v3,v4,v5,v7,v8,v447]
def s18 : List Sig := [v0,v1,v2,v3,v4,v5,v7,v8,v466]
def s19 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v8,v487]
def s20 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v8,v504]
def s21 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v523]
def s22 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v538]
def s23 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v13]
def s24 : List Sig := [v1,v2,v3,v4,v5,v6,v7,v8,v13,v56]
def s25 : List Sig := [v1,v2,v3,v4,v5,v6,v7,v8,v13,v57]
def s26 : List Sig := [v0,v1,v3,v4,v5,v6,v7,v8,v13,v14]
def s27 : List Sig := [v0,v1,v3,v4,v5,v6,v7,v8,v13,v15]
def s28 : List Sig := [v0,v1,v3,v4,v5,v6,v7,v8,v13,v23]
def s29 : List Sig := [v0,v1,v3,v4,v5,v6,v7,v8,v13,v24]
def s30 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v609]
def s31 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v30]
def s32 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v13]
def s33 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v8,v658]
def s34 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v8,v684]
def s35 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v38]
def s38 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v39]
def s39 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v40]
def s40 : List Sig := [v0,v1,v2,v3,v5,v6,v7,v8,v819]
def s41 : List Sig := [v0,v1,v2,v3,v5,v6,v7,v8,v848]
def s42 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v41]
def s43 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v42]
def s44 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v43]
def s45 : List Sig := [v0,v1,v2,v3,v4,v5,v7,v8,v946]
def s46 : List Sig := [v0,v1,v2,v3,v4,v5,v7,v8,v973]
def s47 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v8,v1002]
def s48 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v8,v1027]
def s49 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v44]
def s50 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v45]
def s51 : List Sig := [v0,v1,v2,v3,v5,v6,v7,v8,v23,v45]
def s52 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v1081]
def s53 : List Sig := [v0,v1,v2,v3,v5,v6,v7,v8,v45,v121]
def s54 : List Sig := [v0,v1,v2,v3,v5,v6,v7,v8,v45,v154]
def s55 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v1127]
def s56 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v46]
def s57 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v47]
def s58 : List Sig := [v0,v2,v3,v4,v5,v6,v7,v8,v1184]
def s59 : List Sig := [v0,v2,v3,v4,v5,v6,v7,v8,v1209]
def s60 : List Sig := [v0,v1,v3,v4,v5,v6,v7,v8,v594]
def s61 : List Sig := [v0,v1,v3,v4,v5,v6,v7,v8,v755]
def s62 : List Sig := [v0,v1,v2,v4,v5,v6,v7,v8,v859]
def s63 : List Sig := [v0,v1,v2,v4,v5,v6,v7,v8,v1300]
def s64 : List Sig := [v0,v1,v2,v3,v4,v6,v7,v8,v1321]
def s65 : List Sig := [v0,v1,v2,v3,v4,v6,v7,v8,v1342]
def s66 : List Sig := [v0,v1,v2,v3,v4,v5,v7,v8,v1365]
def s67 : List Sig := [v0,v1,v2,v3,v4,v5,v7,v8,v1384]
def s68 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v8,v1405]
def s69 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v8,v1422]
def s70 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v1441]
def s71 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v1455]
def s72 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v48]
def s75 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v49]
def s77 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v50]
def s79 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v51]
def s94 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v52]
def s95 : List Sig := [v1,v2,v3,v4,v5,v6,v7,v8,v52,v60]
def s96 : List Sig := [v0,v1,v2,v3,v4,v5,v7,v8,v52,v128]
def s97 : List Sig := [v0,v1,v2,v3,v4,v5,v7,v8,v52,v78]
def s98 : List Sig := [v0,v1,v2,v3,v4,v5,v7,v8,v52,v179]
def s99 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v53]
def s100 : List Sig := [v1,v2,v3,v4,v5,v6,v7,v8,v53,v60]
def s101 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v54]
def s102 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v55]
def s103 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v56]
def s107 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v57]
def s108 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v58]
def s109 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v59]
def s110 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v60]
def s115 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v61]
def s119 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v62]
def s122 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v63]
def s123 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v14]
def s125 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v64]
def s127 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v15]
def s128 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v65]
def s143 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v66]
def s151 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v67]
def s155 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v68]
def s158 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v69]
def s159 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v16]
def s163 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v17]
def s164 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v70]
def s165 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v71]
def s166 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v18]
def s171 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v19]
def s175 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v86]
def s178 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v87]
def s179 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v88]
def s180 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v89]
def s186 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v90]
def s187 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v91]
def s202 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v92]
def s205 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v93]
def s206 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v94]
def s207 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v95]
def s208 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v96]
def s211 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v97]
def s212 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v98]
def s213 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v99]
def s218 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v100]
def s220 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v101]
def s222 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v102]
def s223 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v103]
def s238 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v23]
def s240 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v24]
def s241 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v104]
def s242 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v105]
def s243 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v25]
def s246 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v26]
def s247 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v75]
def s248 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v106]
def s253 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v107]
def s258 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v108]
def s260 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v109]
def s261 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v110]
def s262 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v111]
def s263 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v112]
def s268 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v113]
def s269 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v114]
def s284 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v115]
def s289 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v116]
def s293 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v117]
def s296 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v118]
def s297 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v120]
def s298 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v121]
def s302 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v122]
def s303 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v123]
def s318 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v124]
def s327 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v125]
def s331 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v126]
def s334 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v127]
def s335 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v128]
def s336 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v129]
def s337 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v130]
def s338 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v131]
def s339 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v132]
def s342 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v133]
def s343 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v134]
def s344 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v135]
def s345 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v136]
def s346 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v137]
def s347 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v138]
def s348 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v139]
def s363 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v142]
def s365 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v143]
def s366 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v144]
def s367 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v145]
def s368 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v146]
def s369 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v147]
def s370 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v148]
def s371 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v149]
def s372 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v150]
def s373 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v151]
def s374 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v152]
def s375 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v153]
def s376 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v154]
def s377 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v155]
def s378 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v156]
def s379 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v157]
def s380 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v78]
def s381 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v79]
def s382 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v162]
def s383 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v163]
def s384 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v164]
def s385 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v165]
def s388 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v166]
def s389 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v167]
def s404 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v168]
def s405 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v169]
def s406 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v170]
def s407 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v171]
def s422 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v173]
def s423 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v174]
def s424 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v175]
def s425 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v176]
def s426 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v177]
def s427 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v178]
def s428 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v179]
def s431 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v180]
def s446 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v185]
def s447 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v186]
def s448 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v187]
def s449 : List Sig := [v0,v1,v2,v3,v4,v5,v6,v7,v8,v188]
def p0 : List (List Sig) := [s1,s4,s6,s8,s23,s31,s35,s38,s39,s42,s43,s44,s49,s50,s56,s57,s72,s75,s77,s79,s94,s99,s101,s102,s103,s107,s108,s109,s110,s115,s119,s122,s123,s125,s127,s128,s143,s151,s155,s158,s159,s163,s164,s165,s166,s171,s175,s178,s179,s180,s186,s187,s202,s205,s206,s207,s208,s211,s212,s213,s218,s220,s222,s223,s238,s240,s241,s242,s243,s246,s247,s248,s253,s258,s260,s261,s262,s263,s268,s269,s284,s289,s293,s296,s297,s298,s302,s303,s318,s327,s331,s334,s335,s336,s337,s338,s339,s342,s343,s344,s345,s346,s347,s348,s363,s365,s366,s367,s368,s369,s370,s371,s372,s373,s374,s375,s376,s377,s378,s379,s380,s381,s382,s383,s384,s385,s388,s389,s404,s405,s406,s407,s422,s423,s424,s425,s426,s427,s428,s431,s446,s447,s448,s449]
def p1 : List (List Sig) := [s2,s3]
def p2 : List (List Sig) := []
def p4 : List (List Sig) := [s5]
def p5 : List (List Sig) := []
def p8 : List (List Sig) := [s9,s10,s11,s12,s13,s14,s15,s16,s17,s18,s19,s20,s21,s22]
def p9 : List (List Sig) := []
def p10 : List (List Sig) := []
def p11 : List (List Sig) := []
def p12 : List (List Sig) := []
def p13 : List (List Sig) := []
def p14 : List (List Sig) := []
def p19 : List (List Sig) := []
def p20 : List (List Sig) := []
def p23 : List (List Sig) := [s2,s5,s24,s25,s26,s27,s28,s29,s30]
def p24 : List (List Sig) := []
def p25 : List (List Sig) := []
def p30 : List (List Sig) := []
def p31 : List (List Sig) := [s32,s33,s34]
def p32 : List (List Sig) := []
def p33 : List (List Sig) := []
def p34 : List (List Sig) := []
def p38 : List (List Sig) := []
def p39 : List (List Sig) := [s40,s41]
def p40 : List (List Sig) := []
def p41 : List (List Sig) := []
def p42 : List (List Sig) := []
def p44 : List (List Sig) := [s45,s46,s47,s48]
def p45 : List (List Sig) := []
def p46 : List (List Sig) := []
def p49 : List (List Sig) := []
def p50 : List (List Sig) := [s51,s52,s53,s54,s55]
def p51 : List (List Sig) := []
def p52 : List (List Sig) := []
def p53 : List (List Sig) := []
def p56 : List (List Sig) := []
def p57 : List (List Sig) := [s58,s59,s60,s61,s62,s63,s64,s65,s66,s67,s68,s69,s70,s71]
def p58 : List (List Sig) := []
def p59 : List (List Sig) := []
def p60 : List (List Sig) := []
def p61 : List (List Sig) := []
def p62 : List (List Sig) := []
def p63 : List (List Sig) := []
def p66 : List (List Sig) := []
def p67 : List (List Sig) := []
def p94 : List (List Sig) := [s95,s96,s97,s98]
def p96 : List (List Sig) := []
def p97 : List (List Sig) := []
def p99 : List (List Sig) := [s100]
def p101 : List (List Sig) := []
def p102 : List (List Sig) := []
def p368 : List (List Sig) := []
def p369 : List (List Sig) := []
def p371 : List (List Sig) := []
def selectRow (word : Nat) (i : Fin 414) : Fin 414 := Fin.ofNat 414 ((word >>> (9*i.val)) &&& 511)
def h1 := pairHom (selectRow 0x33b9bce66b3394c9e572d98cbe4b2191c7e371d86c2e1f0384c56331788c160f137ebd602f376bbdfefb75bddf2f170b8dbee774b95b2db6eb5d9ecd68b55a6c965b0d82c762aed6ebf5caf56ab354aad5aaf58a9d3a9f50a8d4a8949a552e9942a351e874da2d226f389f4fe733a9b4f27b40a0cee67319acc26932964aa572f96cba532593c9251268d48239228cc6237218ec8e3f1e8a442231787c362b1689c32250e84c1e1706854220b03820f8ea16570c438b2078a98e386886d44a4038e8e81944150525f123302e140694098cf209941c7c0c28178304b93d16b51dac1503742b0dee6f72054b2ea178859251282dc4c5669004842c2206806592e91c1062440c8de2d322c0aeb257bfc785a3705c80323b01046a42d3d520de091e5365e4e8ac3e0c6d86c3021248d4fa9038824446626188d0b705935a684128ace0382aa00462f141e8c86c3ba9c52f14b22818445a89496370e9a8268916a3012795522946107627016271ca8d7895588387c280511590c727a50448b24878960613034a4700d065c6a91e95474040e8f43e803610d2420412a1fcdc3e19cce0141050ea542e11cdceb3e93528201c92876fd4b10c8495550599c2a34a7c8c607d9588c712e94cca03798180a3c040085800) (selectRow 0xe0a0e0a46015188c4261509810040d190146007088a81212090c8221c0c8c014360381c240a090d838090e0241430150c04c260c81c520a030080c02010180e3605048121c01068040203014642a180443214150106005130500c090200804060e0081e36050141204038d83429090481236068140625158d466180d85c2e211288c3c2c1106c50210180c3e1d1a85c72390f8204818158946e080b88c66331986c46230f8744401008b056171181428200a0c4380607810522c1b00c26320381014191987c521b120542e0d06848561103068682d1207c2e30198445630008183437068c80e0f088544e15060605209148844c34190d40a1803868062417864102c0d8c8322e130680e0f128a8041f19840040f0e8104626128c452390905024310e0cc44161b86c30210d8d44e020b03c10140404062370707808231b8ac1a380e0042e2f1c81854270a80c54090e8a018040d0944617160ac2613168a81226140044a101084c1627110e470381b038242805064141c130d4441e1187842051804460361b0140c020501412020e8343e241981c30341b8c826190702c18011585052100b8984a381188836201c82006121083c6035138582a2a1887022280d0bc082d17024141e1b0180a0d0e8085800)
lemma f1 : SignFixed h1 := fixed _ _ (by decide +kernel)
def h2 := pairHom (selectRow 0x3379ccee673596ca6632b97c9e3b1f8dc8e4b2189c1e1b1981c162b0985c5e1f1179bb5e2f97dbaddf017ebd5fef771b9dc2e972b7dbad96db55aecf66b4da2c360b158ecb64add72b55eafd76b159aa556ad57a8d3ea74ea9542994da2d0a9149a250e9747a352a7f39a0cf2753e9bcf681369dce26b30994ce633497cb2552e95cb64d2492ca64f289148e331f9046a391d8c47a431b88c36250e864562f0f884522d1383c2a110985c1a0704828e8de676e054ae3c42aa0863b09130d0793a0693e4641254646a6f225281921024425254b1cf871143ac36ff6d8992c2911240ea4902ab9900d1828946132b2a81ed1049f4c80e33134548a3294010a31013c3001410501a1652240143c2e3480cbc1ba51c614122c110795e33964107891ca27703adc702f4213050aa15878dcb2061c0584510805d47d16875f69711adc7c3b220e510562a10148254e12864f32c87c5e651488cd849403b062f50b30ce0472d07c2e35139785aaf3105c36037e9f074540e3913a431322c5896159d8d80432109183e28118047a2a91034b0401547039128f4c00b259d4d2cf38974ba4d25864de952f93c6ea737075160b3124844532c8f454032d19dfca8663dd6aa0648396a0c102c58e084d811a6060c1051400) (selectRow 0x141c0383c54130a8546213188680c050a010540a180c86c09048506007088a8381205028121c048480e36038d8382a190a84c26088281e1c0101804060300814120e0246c07030a40c06010102832150c022191906854041306404360d0180c02038181a120e0106c1a05048520f048246c12028101017108786e281586c36270b8cc3a01160ac3e270402070240f06c20101c06072281085c46180d8cc6e371b8ac66331c090582211004421b19810320b0c8540e02068681e010902062140506838111b8e01e2b1c84c3605028244230010a41c161c8e0362a1b8c0422a11008522302850140d1804c4a13178a01e360789c4c0e0a0780828050a410391a0443001158502220130a4140d0b8c80c381b8d40c0d1206866260b8541e10048641215038dc580c118ac5027158784a060603430190c0d42a23168743433118840a030388836340800864250982064361207c5e1a1485c661b0088462310b0c86c260f8882e35138c45c25160400603090b4121f0e044380713078581d198744e04150c054120901004060e0106c061201470391b828500e118506211168b85e22108641e350d8982e03198b0560b08060100913834541e1283026320a81c601f148d03416100d8381d090080805120180200)
lemma f2 : SignFixed h2 := fixed _ _ (by decide +kernel)
def h3 := pairHom (selectRow 0x3379dce6673597c9e573196ca63b1b8fc8e43258ac260b1185c36270781c3e2f1978bbde7017fbd5daf97bbadf6fd72ba5bee771b85b6d96eb55a6d166b5d9ec161b2d92c563ad57eb75eae576b157ab556a959a8d42a54ea9d3e8f48a15169b4aa1d128d4ca5d2677369e506813d9c4fa75399fcde65319acd26133974b6572f954b24d2792ca249298f47e3b2390c6e31198e48a411a8743e2f118845a250d8644e2b148442e0f06854260705821106467691a4a690648641239641659c794d955e62a3e950de275384cb4a85a90d2c30011c01c560184146cf42098420d400f028257d9982429293f8368938a2c1e9d21a089e7c572288c4d1f0f4301b16990101f3e9d4525d238f1fa902e371601711968f47525018dc790b9a164eb7ba900e5e2892cc40c6d964068b3618110b217b1c3ac34b07dea82100b00a971b92cca391d0ecdc714a9008e494e090de9f26004183e068dc5625113b198ea2e9158ea44a00578a0351dc405f1c2f1462805038889558a31a209132a83a2136248560427ad5c8651e8a952e30d0e8aa0611068c43b249403c0b5b8502aff2b0582c8a5baa064545799046de440b1540b1c1d90057261408c284a19d441918bc48435429f0842f16870e0183a011a6b0041049a00) (selectRow 0x24360483c2213188c42a130a8140c1a0a0102212180643807038506009150446c0a090480e3603828121c048706c110c8444c26150481e3601018040603008240a1b01c3809030340c06010102819088c054320c8142204130c8041c028180c0204818520a1b0103805090281a0f0381c380a0d0104817108a0461e138944a2b0b8cc30221609c6a2b12090200814094703808074061e1085c6e1d128cc46231189c663308020580100888422519810640b190c41202148141e22050902a14090146c2a118401e270184c4a1a0d01c4230010341c2f018404a11118c04211008081a370d05024291804c36130b0781e1c078ac4c0e0a0a0081e090344803168a83a2213850542e1303424290b8640c101187c0c290401466260b8c41e38038c80e310488c580c1b89c3c2b138a03606060a43a320e87c62371a0600a331b8843439048044a2d1c008321b09890321c040d42c050685c6625110842a151786438261a8042e1f15854401b160e07239050d00e351b0a86c09130a05818198605604088c0220a0501004061b0103806040682003118483c0e1b8502a2a1a0802c01108c81e1f128982e39198b04e0b1c0744807158a422280d8302619188246035068b40a2f170706c1805008081a040184400)
lemma f3 : SignFixed h3 := fixed _ _ (by decide +kernel)
def h4 := pairHom (selectRow 0x3399dcde6b3395cb65f3193ca6432392c6e3b1f88c3e27158cc5e0b0383c261b0b7cbedeeff80bf5d6f179bb5def573ba5c6e56fb85b6dd6cb4daad767b459ac563b2596c161ae57abb5fad56eaf58acd52ab56a954ea34fa853a9147a3526954da652e8543a2516793a9dcf67d419fd026d379c4e665339a4d66131974be592d954ae51299249a4b278fc7a412191c8a33188d46e3b1c894562d138a45e1d0c86c461f108542e0d07844260905818681a5d67a881406029d47a2278885d4474f941eeb52580c28ec083d51646151c1548c3d10ce20c2a29c98d242190b232162c8de2b69b713a427f9a02e31071690a12381b9487c22875501f63824301705898504d2586484673cac838062f998081b24a2c04196f24104470dbf878357993da29c3a1f476564b884a85a5b9d86e3c178f914e455134266e0b20192db441f4742232989040e4ab8cf2232f248289b518e0acc7192204a2b1c89c2ace33ab87c4f5e0e1281e579dc2c5c00a509808299c434952b8c00e3d3225914595b8904ab0520a9863a04ad4824022194a0901c910766211955402d361bd985206080401d361181a0335098924a1ba012c2d0098058b15195550085e174d27544b2052eb079f0522f05bf4861828ac1f604142a43e00) (selectRow 0x38070503464310984c2a310a8a404040c868641c1505024361b064540a180c80e090e0706c071b0241412050480e320a0c84c26180701a07030080c02010183809038d8240a0103c0402030683214190a860110a0a4641a130440c12148080406050080a090386824290e0241e0d1b0d8240902068301b13874461f108ac56250d8dc48220088470250c06006390e8ac6a35018a0201f1386c6628158dc4623118846e37018e4022c160884e2b1b868222e0884c1406028a41a22048602a190e0a40e301180c1a21080c45604020d84e2a0303c5a0c0800c5632118a84e32160181e33020643805150c42e311a07c1a12068944c2d0c874341f0e03c3010070c0502210864600b1303c38050d85004031187804051c8a46e260d84c1a351b0446c130508c022f198843e25108742e021781450111407826330b09052371989c0808050b0560e1a81828171886028121c8e068290786c6e2b1109c2a150605024261c0b0361e128544017008d41008048586c38038c00e0a1307402241b8904a1a190a86409048680c020386824021c8100610118703e2d198642a300b080682c138441a1e1589836081b804422e1a8a0303612814641d0b8bc621409828543807838520c058480e240481834041c8084400)
lemma f4 : SignFixed h4 := fixed _ _ (by decide +kernel)
def h5 := pairHom (selectRow 0x3399bcee6b3393ca6632f95cb6432591c6e3f1d82c0e2f0b83c4e230f8cc3613157bbadf2f177bb5f6ff7abf602f36fb95c2e973b8db2dd6db4da2cd67b55aec762b0586c965aed6ab95faf56eaf56aad52b358a953aa14fa8d4e874aa4d1a8f45a5d328948a153671379ecee6d409cd067d3a9e4fe6930994c6673596cae552e964be51259249e53268dc86311e8ec7235208cc7e472289c321d1286c3e2d158a4422f1183422150985c1e090382994285d3333162b207918e0624ea8dfc472891136a8372541aaf250c57875148f4b2ff208f8f80e040d42e524b99154421c818322364915e232461a498f5062590a071e92c4c716e07d6a1d1d154504c0b2903038371bc642027818a6b22fb3d2094442f0806f490106e474a3a878a7641e4e877689b0022f4228c109612a81043c2b10d00ae2c8e19c4b05a29a6db249b18e620d0886e0c01b8c9e2b2f3781af7109345e3a211256e231609d12131039086794593436eb76270166a1d86c2e540e1f0ca037eb0c24703216900aa129816eb0130a460c72aaa0f40228068880416140022215824ec2d3e86544d20719cce1f3e9d428952e291101041228b42d1d890720a108256a5445974d0460abcc541e029c454560b15c7c284fac1f6900c2a43a00) (selectRow 0x12121b03460310a85426310981004290c8686009150440e0a050645436190c0241c048241412050706c071b01c2430088c04c26190241a12030080c0201018121c090280e36010140402030683211180a8641408810601a130500c070200804061b0081e1c090680e04048700a0d050280e1c14868721b1387c661d1285c2e210d8dc502c008943c211c8e46a180f85c06031a890101d1386c46240b8dc6633198946e371a8600222110b04e171b868282e0a0546c06078101a2c0e0e42619048102432198d41a25040c42e29148284e2a030145a34040d42e30198a84e30110180a2314864120f150c45631060741a07068844c2d0c87c341d0481472080b0c8482c12864642013014120f0d8440435198e0040f0c0106e260d8541a030505014151b0cc022f118943a211287c56021783c4814120e02a23070a008371189c52101b0882e1601818222b188e422070c07818040286c6e171609c26131a0440e260f08836381084c162b0080c20100e038141e090c824361307c02281b8a0421a180a8601c0e0680c02090680e020c0a46a08198243a2d1186426320702c1822138501a380b89836101b8044a2e01890720a1083c601f158bc62110a8d8541e0285808341001c24280e01834290c0085800)
lemma f5 : SignFixed h5 := fixed _ _ (by decide +kernel)
def h6 := pairHom (selectRow 0x33b9bce6673598cae4f2f94cb63f1b8ec96432385c3623058ac262f1987c0e27077fc05eaef78bcdfaf77cbedd6ed74b95cedf70b8db2db6eb45a6d56bb359ec965b0d82c762af57eb75aaed72ad57ac566a955a8546a553a753e9543a25368b47a450a934ba651a7b3e9c502833b9e4da6f3f9ccea693598cca673096cba5f2b964aa4f2694ca2492590c6e471d8f47e411a9147231198b45e1f1088c3a27148ac4a190d85c22130a8341e0b03821408420291a03804699bcaa2c79aa8264f7b82590293602032271ab392cb5540f8b4c3200f4182f4a92842664ba914614450f01ab77db3c0e2a693a928153e2f00af11f0dcf27172200ea38219c0509416990a81d36118545d238f0ae0435115604c15a588246082c8964f261a40c1e4d898245e4f9b8440e6daa92abc3e89092062b0e83e302d0746237338e41e84411b8342c63804967c018088e883b98032510b8ec1c430a20846b7312bd44fe2eb7074260d8ed16762e270ce5f26a2c421858830a003053fce855521643ea33eb7846903caa15c1a380a552e332b1c12b231194440144111d61612835128c1782c168012ad48408761905692248e4b21626a8114fd0b910ea180d881986f7aa7464a7429c464561694c7a2868a4192b02a1e87000) (selectRow 0xe0a0e0142815188c426150983c0c1a088a4280719064121209044641c1505014360381c240a090d838090e02414140c8504c261501c0a0a010180406030080e3605048121c030340c06010a422190a0c854300c83c2829130c00409078180c020e0180836050a4120f038d81a050904812360d0a4502b1289066381388442171588c722c1109c0617140a01010120843c1e0407c6a38128ac6e1f1088c66331989c4623040404401008b04a21118a46020180c438020203c0a2c1b0a026110383c142a198200a271a854421a0d0484a32010342c2f1a8204214198c84a14008081a370d0440e04190543615070e00a090285c4c16088905238038345035168a83e2c13844542e130340e04158640c08198740c040803c4626158c40a1e090c024310e0cc44341b89c70171389036061a0103e300f8746237060e41e231b89434180e004422d0f008321b0a8a032090800c1c0f068ac462116094261317864122601804561d0b84c161b1107830181b0302403050a8141c130904439118e42e290a0c828361b0a40406050a412060806810351981c70161b844262a0602c1c01128c00a1d108985618118884e200f07c50120b81028240d8d02a19188706403068b41e2f1702414391b008521a080185800)
lemma f6 : SignFixed h6 := fixed _ _ (by decide +kernel)
def h7 := pairHom (selectRow 0x33b9ccde673594cb65f2798cae3f1d8dc9647218bc66130787c46170d8ac4e07057abf5fef775bee02ef76bcde2f970b7dc6e574b9dbadb6cb459acf6bb4daacb64b1d8ac360add76bd5aafd72ad55aa566b157a853e9d53a95469745a6d128746a1522994aa4d1e733fa04e26f369d4ee833e9ecf263339a4c26b3295caa592d97cba4f2494c964d288e476351b8c4664523904863d1f8845227168ac321f1788c361d1284c1a17078442a0b0481b1c322022a25fa3c42ad47c010385cd24f68994a2751b80c845c49054366f1915546d2548e8e27c0c079288c6da90b42a310108c8807b91e61461b3042ce179640a742a9b0c80c678e052800d110a821339e4503b1b834280b13011623c35149648b4106dc60d302c0924f4584c0c4a4e91d3e9c090949a564b85c305911bac9606070f472dc518edfc6c1687df684158948601280b0922f040084cb73b84084c855074ac1a150acfa88452bdea31058c07a474b07498a7139785aec1113128952b9c58e0829ab9e23e522f0725a11a80fa90320c9fe43221d4804104940cab0450249a2c5b9c0481637118d0663e174ba38371bc32032f9e504352587d781611378c41c551c052954b081d4b55126d507669831500e3382874547ba4192b2141e90000) (selectRow 0x6c090901454150984c6215188680c0f088a45436190c0141c0e04464120a0a812071b0d838090e01c240a09028122a180a84c260a0d80a09010180406030086c07048701412030100c06010a42230150c8281918068542913064040a0d0180c02090181a07048a4141a1b01c08050e0701407078a4202b128e06e240b86c36271588c3e011105c3a27080403c281c06c10080f0e43024128ac66390d88c6e371b85c46230f0a0442c160044a1b118a432200c84c2402068680a010384062111b06812141b8780a170c054360f078704a32010102c0e0c078362a1b8c84a2a160080833078446c0d190544215178900a0a0289c4c16088e052241b01020180605072010b844280b130106c0d158c00c1e1b80c0c0d1406846261584c0a080e0643813090dc44341985c48270b8e042061a03472191c80c26331687c3423198941e35090b0360c0400860210a840600a140745e1a020ac461b008946231070c014260e8b05603138c45c21110206a35038b4381d048501212130e0441f1187c4e29150c85407038a40406048a414061403c3c181b8d84816198446214168b85e2c128640a030d8985635118882e20040e4201c138345438108d02a3009848641d02030340e05828121f03808520f140180200)
lemma f7 : SignFixed h7 := fixed _ _ (by decide +kernel)
def h8 := pairHom (selectRow 0x3399bcee673595cc6532d93cbe371f8ec864b2381c16330d89c1e1f118bc2e2b097dbe5d6ed79bc5eefd80bfdeaef73b8dd2e16fb95b2dd6db3daed569b35a2c762b0586c965af572b55baed7ea959ac55ead55a7d46a752a75429344a1d22854ca6d169546a3d2e7d3d9bcea793fa0ce6713b9b5026732984d66931964be5d2a96cae4926944a64f259046a3f199148e431b8f462391d8ac4a1b0c8744629138b45e210f8541e0d0b84c220903828f56a2d183396204698c8341d4fa2d12647890c240d15861506a501a042420c9952845201405e0c2a0912cae4b91c367526a40524b02bfca2466e3d4b4690705df6f73288cf25646088286204b1c065a1013d2a2c158a88c1652240a60413b0c0c5936084822a75ac96e642c85560603a099907779a21007c4222ca817411284ab03891002524a0b19823338ec1edb3ea20aa1d3807d6e0e142a5486e2f07950075e0e4f8093a9f46e4b1c17dfca20b3488826518e554922e270ceaf452a92c080e0bc7a287eb3d361a23930021b4129c6e3c3c864cc5563834047a1f1c086b21c0f9001f370e8205d248a426e40602c1622249096a187613cd876128ec985d450d49a0a5e0e82808518b4623275344dede64958de711015ca0034e8f10a064ab8cc400) (selectRow 0x12121b06828310a85426310983c0c051503428090c8c80e0a050a8323608850241c048241412050706c071b01c2414190504c2608824341201018040603008121c090280e36030a40c060103454320a06422301903c280d130c00407078180c021b018081c090340e0f04870521a050280e1c028343c270d8206610158844217138dc062c008ac72170f0784838040845028120d43e100d89c4635108dc6633198ac6e37120e00222110b036211b834602e180546c020203c342c0e078262a0483c241119890342b0f8c44205028283619010a45e160f8904214198643614110085223028a812040c8c44a310704034070d05c4c2f150201a10048a43c1f1a0446a2c158a82220130a41204138c80c24198600c041c03c6e26138543428050c014151b0cc022d118ac2017158204a06168106a301a8602a230600c1e371186c0a1d1b08842341400864251887864071c0e41c0f1489c6e211606c26130b0c80e261c8884e180b84c1625008a03a1d0e03014390904424361302002031b80c2e0d0a064281c0e0340406090340e061c014481f19824202f118a826110602c1c220d8c03418108984e1d1b804562e140d43c0a0b8102808128b462320a8d83239148d01e161001c24030e0081a051c0185800)
lemma f8 : SignFixed h8 := fixed _ _ (by decide +kernel)
def h9 := pairHom (selectRow 0x3399dcde673593cbe5b2995cc6371d8fc86472587c460f098bc66070589c56170d75bddf6fd7abfdf2ed77bc5e7016fb85cae373ba5b6dd6cb3d9ad169b5daac563b2596c161ad576bd5bae57ea955ab55eb159a7d429d52a9d468d42a450e894ba2d368f49a55326d3b9d4de7139a04fe793d9f506613499cc66535954ae5b2c974be4927944964d298c466371a8e4763d1f90c8245238644e29158b4421b128743e231783426150883c2e0905819c1502d6184c149064908ca1f28af02a644e8f80e14118a16a5c3b1a546323786836dc01110ac0e04180b4e44211d28461c010546e07a313e75228c52c6806131f69b0d0ac9e2f7f9881a222a8e92a96339e40639118a4ea0b130103890138c164aa3ea8cf4290f0184a6455225602468a91e69c6412514714baf0104c1b8416eb03e14076d20d8e5442b100040adb36124121f1e8744a0c0c2a44c4b2f3ad6a12458b0e255231b1046e2697dd4cc05948a0a4108b0b2de351dc40ec40164b45429958e0182b999ee652385c76941b8d5043c279bd9e091d0508041218f47c062690d141d25b1c945d440a99cae070582c62440c95028579e4faa05b8042e5d4029c70b145b1c1a54108b5ea427f1d03292698bc327c33bf48895788f10ab201b8c4400) (selectRow 0x38070506822310984c2a310a8140c0f15034221c0c8c024361b0a8320a0a0440e090e0706c071b0241412050480e11180444c260a0703407010180406030083809038d8240a030100c0601034543008864283218014220d130c80412028180c020501852090383424050e024081a1b0d824090783470270d84046080b8944a2b138dc6a220085c302b1c0e0501e0809448241400c3a080d89c6603128dc46231185c6e3714078022c1608836251b834642e1904c1402148143422048e02a2a0e0140e14118a034170e8c44a0f078d83619010105e0e0e8a04a11118643611160080833078a838290c8c442310b02034120d0ac4c2f150401a080e010701d0605006220b8a8280b130103829138c00c28118e40c290f0146e261384c34241b0c86c130508c022d1985c102b0b8404206168a40632018e426331a0d40a371986c1e1f050b04a0c120086021188e060120f0602c050209c6e251106c2a15070c024260c0b04e39158544021008903e1f048d06c18038500e0a1304002351b8d4560d0886422090483404060383424060f03c501d11870102f198a82a141a0802c2c0d8c83439128984e1f1b8042e2e1200c7036158a42210108b46230098283218020300a0e058480e35048081a0f0f0184400)
lemma f9 : SignFixed h9 := fixed _ _ (by decide +kernel)
def h10 := pairHom (selectRow 0x3379ccee6b3397cc6532796cae472590c763f1b83c4e171782c0e131586c66230f77bc5daeb7bbe5e6f57fc05fafb72b7dd2e171b9dbad96db35a2d36ab3daec360b158ecb64afd6ab95dadd7aab56abd62b354a754aa151a7d4e8b4ba651e8d43a55269b42a451281419ccda77389ecde7f3c9d4fa6332984d26b3395cb65d2a97cb24b289349e53248ec723d188dc8647228fc66352087c3a190d8944e21118bc5a29158441a0f0b84c2a070482824540b463a8aeb07d834888a4d9686226641c13a32128608caf0f3f8b2293a8e978ae719545e5601a4954456d9e42e190f818847d64948e8a83304d16a23886da6f31d1248e0c180e4de3b1e8f8a88b0b2912a8012ad550202781814b07639120215b96552b51a8f0d82610b30087628991e2777b8dc587c42168061b3737856040706870ff5e2002a492e9890a97258dca08a21934d871041049e824e2808cd14a088f83d0c92d107d00970d0691033c3464260892c242f978ba6a0ea5954287e8bc12080e3493e443ca8c70173704110b2239d5b8501f0c8f4026390ce03c00b1c584d411954e6711909eac32b0b45a39118a4541813a916e601598946670ebac3e534a194de282602d120d6701c284a02830280e0b2c4aa54092c81e904a9007600) (selectRow 0x141c0381032130a85462131883404291803c320a0a0446c09048c0280719064381205028121c048480e36038d83819088644c2619028081c030080c020101814120e0246c070101404020303c60110c850642a08834320f130a80c360680804060380834120e03c6c0d050480a04048246c121483c3e210b8e46e031289c4e1b108cc200116094101b0f87c30351c89c3a1d0c0e03c030b8844638138cc6e371b89466330c0d45822110042e271983c540b150540e060d03408010907c62300503438321b86008250f04c4e29148242e140301418340f0604e191b8502e19110180a23148c0141a0a04c56131680c08360206c4c0c180e41e03050143e1e0b0c87001128c0642013014141a1084404181b890041a1a834662610854081d048a81215038dc580e11894061b128e4560207068702a1c0902a23178401a331185c5228038884e160e818222b0987c22361a8205a0d0288466270085c62311a0446c260408842240d8c45c2b160745028090bc12080e0c83807130e4581019840360f0c85032120903c0c020e03c6c021a8a4301e1b828060c118c06232178b85a220b8a80824138984228198b04a0b0e8e03e090d86832391583826110a81c2808028581a34100d83810090181e291a8080200)
lemma f10 : SignFixed h10 := fixed _ _ (by decide +kernel)
def h11 := pairHom (selectRow 0x3379dce66b3396cae4f2997cc6472192c76371f84c56070f86c2e0f1382c46331776bcddef57ec05e2eb7dbe5eeff71b85cedf72ba5b6d96eb359ed76ab45a6c161b2d92c563ae56ebf5dad57aab54acd62af56a754e9f51a854a8546a3d329744a4d2a9145a6d0e753c9b4e67f379f4e27741a04f6613598cce6534954b25f2b974b64b299349251278cc62451c8d4823f1e91c76372186c46210f8bc52190e89456271683c26110a8342e07058210c8c0b723d4a606028a4744d3a25198260931da26f24820545f30288980d0a1102e663d0681871141d916c3421e578a800ac16a82428c136195722554fe2b28da69f22095482f290ec6439281952aaa2e91ca82224908322d322c1fa067623078962593004425024056264b0c408920393dee5e7888c3a0e6da5050a34429cd8043e154c4cf0b888d2250b0e192975b88c7a4d04a2856560c104c87d4e0d4549d2d2001c50542dcdc820f9719c1516bfcaa4f2ca00424a579dc2c2716085160305030861858b71e63a3c86cc4bc443acdcb252051a43d329bdc6a9380258e900f9c03a8a3e8f9bc671bad5d44538880403b1b8348c083511c961e360e036671604002572d0f864032c82c262934144ea247d8bcea7c2e8703495642c81e3c2a1007200) (selectRow 0x2436048106413188c42a130a8a4040d1803c64120a0a83807038c028090c8c86c0a090480e3603828121c048706c32150c84c260c8480836030080c0201018240a1b01c38090106804020303c602a190503211150a4640f130440c1c148080406048080a0a1b03c38290902834040381c380a0683c6a210b80c46390d8ac5625108cc70221606c48251a8d43a1f018ac30180e84050390b8846e10158cc46231186c66330e87c5801008882e2b1983c220b088c41206028a40822050d42a30090a46c1911874081b1404c560d0681c2e1403068182d140745632118502e32008183437068c024050a04c4e131a0e4081c020944c0c1800c1e39090686a281786420220d8c0322e130682405108a8041d1182004050f8a46626108c40818038440e310488c580e1b86c72250d80c4e020701420110802062370b0e052331b85c1a1e04804562f0c0185427098d4541c0f89068290d084662b1105c2a15168a83826120044208128544027160603c1e050580e241b0646c091300c5838198e04a0f19050640a0503c0c021b03c38020f8343a2811848720c1b8c02a190b08068010b844080815898421e198b0360b0c0406a0712814640313838262a1882428240d0bc522d170706c38050181e0d0f8084400)
lemma f11 : SignFixed h11 := fixed _ _ (by decide +kernel)
end PEqualNP.Outside.L_meta_3400_aux.Orbit3400
namespace PEqualNP.Outside.L_meta_3400_aux.Orbit3400
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.FreeSearch1868 PEqualNP.Outside.L_meta_3400_aux.Cuts1868 PEqualNP.Outside.L_meta_3400_aux.Guard3400 PEqualNP.Outside.L_meta_3400_aux.Moves3400
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
theorem compact : excluded 12 s0 := by
  have x1v0 : h1.fn v0 = v0 := by decide +kernel
  have x1v1 : h1.fn v1 = v5 := by decide +kernel
  have x1v2 : h1.fn v2 = v8 := by decide +kernel
  have x1v3 : h1.fn v3 = v3 := by decide +kernel
  have x1v4 : h1.fn v4 = v4 := by decide +kernel
  have x1v5 : h1.fn v5 = v1 := by decide +kernel
  have x1v6 : h1.fn v6 = v7 := by decide +kernel
  have x1v7 : h1.fn v7 = v6 := by decide +kernel
  have x1v8 : h1.fn v8 = v2 := by decide +kernel
  have x1v9 : h1.fn v9 = v48 := by decide +kernel
  have x1v10 : h1.fn v10 = v49 := by decide +kernel
  have x1v12 : h1.fn v12 = v51 := by decide +kernel
  have x1v13 : h1.fn v13 = v60 := by decide +kernel
  have x1v23 : h1.fn v23 = v154 := by decide +kernel
  have x1v30 : h1.fn v30 = v61 := by decide +kernel
  have x1v39 : h1.fn v39 = v63 := by decide +kernel
  have x1v45 : h1.fn v45 = v45 := by decide +kernel
  have x1v48 : h1.fn v48 = v9 := by decide +kernel
  have x1v49 : h1.fn v49 = v10 := by decide +kernel
  have x1v51 : h1.fn v51 = v12 := by decide +kernel
  have x1v52 : h1.fn v52 = v56 := by decide +kernel
  have x1v53 : h1.fn v53 = v57 := by decide +kernel
  have x1v54 : h1.fn v54 = v58 := by decide +kernel
  have x1v55 : h1.fn v55 = v59 := by decide +kernel
  have x1v56 : h1.fn v56 = v52 := by decide +kernel
  have x1v57 : h1.fn v57 = v53 := by decide +kernel
  have x1v58 : h1.fn v58 = v54 := by decide +kernel
  have x1v59 : h1.fn v59 = v55 := by decide +kernel
  have x1v60 : h1.fn v60 = v13 := by decide +kernel
  have x1v61 : h1.fn v61 = v30 := by decide +kernel
  have x1v63 : h1.fn v63 = v39 := by decide +kernel
  have x1v146 : h1.fn v146 = v150 := by decide +kernel
  have x1v147 : h1.fn v147 = v151 := by decide +kernel
  have x1v149 : h1.fn v149 = v153 := by decide +kernel
  have x1v150 : h1.fn v150 = v146 := by decide +kernel
  have x1v151 : h1.fn v151 = v147 := by decide +kernel
  have x1v153 : h1.fn v153 = v149 := by decide +kernel
  have x1v154 : h1.fn v154 = v23 := by decide +kernel
  have x1v594 : h1.fn v594 = v1441 := by decide +kernel
  have x1v755 : h1.fn v755 = v1455 := by decide +kernel
  have x1v946 : h1.fn v946 = v1002 := by decide +kernel
  have x1v973 : h1.fn v973 = v1027 := by decide +kernel
  have x1v1002 : h1.fn v1002 = v946 := by decide +kernel
  have x1v1027 : h1.fn v1027 = v973 := by decide +kernel
  have x1v1081 : h1.fn v1081 = v1127 := by decide +kernel
  have x1v1127 : h1.fn v1127 = v1081 := by decide +kernel
  have x1v1184 : h1.fn v1184 = v1321 := by decide +kernel
  have x1v1209 : h1.fn v1209 = v1342 := by decide +kernel
  have x1v1321 : h1.fn v1321 = v1184 := by decide +kernel
  have x1v1342 : h1.fn v1342 = v1209 := by decide +kernel
  have x1v1365 : h1.fn v1365 = v1405 := by decide +kernel
  have x1v1384 : h1.fn v1384 = v1422 := by decide +kernel
  have x1v1405 : h1.fn v1405 = v1365 := by decide +kernel
  have x1v1422 : h1.fn v1422 = v1384 := by decide +kernel
  have x1v1441 : h1.fn v1441 = v594 := by decide +kernel
  have x1v1455 : h1.fn v1455 = v755 := by decide +kernel
  have x2v0 : h2.fn v0 = v1 := by decide +kernel
  have x2v1 : h2.fn v1 = v0 := by decide +kernel
  have x2v2 : h2.fn v2 = v5 := by decide +kernel
  have x2v3 : h2.fn v3 = v8 := by decide +kernel
  have x2v4 : h2.fn v4 = v6 := by decide +kernel
  have x2v5 : h2.fn v5 = v2 := by decide +kernel
  have x2v6 : h2.fn v6 = v4 := by decide +kernel
  have x2v7 : h2.fn v7 = v7 := by decide +kernel
  have x2v8 : h2.fn v8 = v3 := by decide +kernel
  have x2v9 : h2.fn v9 = v9 := by decide +kernel
  have x2v10 : h2.fn v10 = v11 := by decide +kernel
  have x2v11 : h2.fn v11 = v10 := by decide +kernel
  have x2v13 : h2.fn v13 = v18 := by decide +kernel
  have x2v16 : h2.fn v16 = v52 := by decide +kernel
  have x2v17 : h2.fn v17 = v53 := by decide +kernel
  have x2v18 : h2.fn v18 = v13 := by decide +kernel
  have x2v19 : h2.fn v19 = v30 := by decide +kernel
  have x2v30 : h2.fn v30 = v19 := by decide +kernel
  have x2v39 : h2.fn v39 = v87 := by decide +kernel
  have x2v40 : h2.fn v40 = v96 := by decide +kernel
  have x2v41 : h2.fn v41 = v97 := by decide +kernel
  have x2v43 : h2.fn v43 = v99 := by decide +kernel
  have x2v44 : h2.fn v44 = v88 := by decide +kernel
  have x2v45 : h2.fn v45 = v89 := by decide +kernel
  have x2v46 : h2.fn v46 = v90 := by decide +kernel
  have x2v47 : h2.fn v47 = v91 := by decide +kernel
  have x2v52 : h2.fn v52 = v16 := by decide +kernel
  have x2v53 : h2.fn v53 = v17 := by decide +kernel
  have x2v54 : h2.fn v54 = v70 := by decide +kernel
  have x2v55 : h2.fn v55 = v71 := by decide +kernel
  have x2v70 : h2.fn v70 = v54 := by decide +kernel
  have x2v71 : h2.fn v71 = v55 := by decide +kernel
  have x2v87 : h2.fn v87 = v39 := by decide +kernel
  have x2v88 : h2.fn v88 = v44 := by decide +kernel
  have x2v89 : h2.fn v89 = v45 := by decide +kernel
  have x2v90 : h2.fn v90 = v46 := by decide +kernel
  have x2v91 : h2.fn v91 = v47 := by decide +kernel
  have x2v96 : h2.fn v96 = v40 := by decide +kernel
  have x2v97 : h2.fn v97 = v41 := by decide +kernel
  have x2v99 : h2.fn v99 = v43 := by decide +kernel
  have x2v147 : h2.fn v147 = v148 := by decide +kernel
  have x2v148 : h2.fn v148 = v147 := by decide +kernel
  have x2v249 : h2.fn v249 = v404 := by decide +kernel
  have x2v275 : h2.fn v275 = v424 := by decide +kernel
  have x2v304 : h2.fn v304 = v523 := by decide +kernel
  have x2v329 : h2.fn v329 = v538 := by decide +kernel
  have x2v356 : h2.fn v356 = v447 := by decide +kernel
  have x2v379 : h2.fn v379 = v466 := by decide +kernel
  have x2v404 : h2.fn v404 = v249 := by decide +kernel
  have x2v424 : h2.fn v424 = v275 := by decide +kernel
  have x2v447 : h2.fn v447 = v356 := by decide +kernel
  have x2v466 : h2.fn v466 = v379 := by decide +kernel
  have x2v523 : h2.fn v523 = v304 := by decide +kernel
  have x2v538 : h2.fn v538 = v329 := by decide +kernel
  have x3v0 : h3.fn v0 = v5 := by decide +kernel
  have x3v1 : h3.fn v1 = v0 := by decide +kernel
  have x3v2 : h3.fn v2 = v1 := by decide +kernel
  have x3v3 : h3.fn v3 = v2 := by decide +kernel
  have x3v4 : h3.fn v4 = v7 := by decide +kernel
  have x3v5 : h3.fn v5 = v8 := by decide +kernel
  have x3v6 : h3.fn v6 = v4 := by decide +kernel
  have x3v7 : h3.fn v7 = v6 := by decide +kernel
  have x3v8 : h3.fn v8 = v3 := by decide +kernel
  have x3v10 : h3.fn v10 = v50 := by decide +kernel
  have x3v14 : h3.fn v14 = v9 := by decide +kernel
  have x3v30 : h3.fn v30 = v86 := by decide +kernel
  have x3v41 : h3.fn v41 = v75 := by decide +kernel
  have x3v44 : h3.fn v44 = v164 := by decide +kernel
  have x3v45 : h3.fn v45 = v165 := by decide +kernel
  have x3v46 : h3.fn v46 = v166 := by decide +kernel
  have x3v47 : h3.fn v47 = v167 := by decide +kernel
  have x3v52 : h3.fn v52 = v142 := by decide +kernel
  have x3v53 : h3.fn v53 = v144 := by decide +kernel
  have x3v54 : h3.fn v54 = v143 := by decide +kernel
  have x3v55 : h3.fn v55 = v145 := by decide +kernel
  have x3v64 : h3.fn v64 = v10 := by decide +kernel
  have x3v65 : h3.fn v65 = v12 := by decide +kernel
  have x3v66 : h3.fn v66 = v13 := by decide +kernel
  have x3v67 : h3.fn v67 = v30 := by decide +kernel
  have x3v69 : h3.fn v69 = v39 := by decide +kernel
  have x3v92 : h3.fn v92 = v52 := by decide +kernel
  have x3v93 : h3.fn v93 = v53 := by decide +kernel
  have x3v94 : h3.fn v94 = v54 := by decide +kernel
  have x3v95 : h3.fn v95 = v55 := by decide +kernel
  have x3v173 : h3.fn v173 = v146 := by decide +kernel
  have x3v174 : h3.fn v174 = v147 := by decide +kernel
  have x3v176 : h3.fn v176 = v149 := by decide +kernel
  have x4v0 : h4.fn v0 = v2 := by decide +kernel
  have x4v1 : h4.fn v1 = v1 := by decide +kernel
  have x4v2 : h4.fn v2 = v0 := by decide +kernel
  have x4v3 : h4.fn v3 = v5 := by decide +kernel
  have x4v4 : h4.fn v4 = v7 := by decide +kernel
  have x4v5 : h4.fn v5 = v3 := by decide +kernel
  have x4v6 : h4.fn v6 = v6 := by decide +kernel
  have x4v7 : h4.fn v7 = v4 := by decide +kernel
  have x4v8 : h4.fn v8 = v8 := by decide +kernel
  have x4v9 : h4.fn v9 = v14 := by decide +kernel
  have x4v10 : h4.fn v10 = v15 := by decide +kernel
  have x4v13 : h4.fn v13 = v13 := by decide +kernel
  have x4v14 : h4.fn v14 = v9 := by decide +kernel
  have x4v15 : h4.fn v15 = v10 := by decide +kernel
  have x4v23 : h4.fn v23 = v56 := by decide +kernel
  have x4v24 : h4.fn v24 = v57 := by decide +kernel
  have x4v25 : h4.fn v25 = v40 := by decide +kernel
  have x4v26 : h4.fn v26 = v41 := by decide +kernel
  have x4v30 : h4.fn v30 = v38 := by decide +kernel
  have x4v38 : h4.fn v38 = v30 := by decide +kernel
  have x4v40 : h4.fn v40 = v25 := by decide +kernel
  have x4v41 : h4.fn v41 = v26 := by decide +kernel
  have x4v43 : h4.fn v43 = v106 := by decide +kernel
  have x4v44 : h4.fn v44 = v111 := by decide +kernel
  have x4v45 : h4.fn v45 = v112 := by decide +kernel
  have x4v46 : h4.fn v46 = v113 := by decide +kernel
  have x4v47 : h4.fn v47 = v114 := by decide +kernel
  have x4v52 : h4.fn v52 = v107 := by decide +kernel
  have x4v53 : h4.fn v53 = v108 := by decide +kernel
  have x4v54 : h4.fn v54 = v109 := by decide +kernel
  have x4v55 : h4.fn v55 = v110 := by decide +kernel
  have x4v56 : h4.fn v56 = v23 := by decide +kernel
  have x4v57 : h4.fn v57 = v24 := by decide +kernel
  have x4v106 : h4.fn v106 = v43 := by decide +kernel
  have x4v107 : h4.fn v107 = v52 := by decide +kernel
  have x4v108 : h4.fn v108 = v53 := by decide +kernel
  have x4v109 : h4.fn v109 = v54 := by decide +kernel
  have x4v110 : h4.fn v110 = v55 := by decide +kernel
  have x4v111 : h4.fn v111 = v44 := by decide +kernel
  have x4v112 : h4.fn v112 = v45 := by decide +kernel
  have x4v113 : h4.fn v113 = v46 := by decide +kernel
  have x4v114 : h4.fn v114 = v47 := by decide +kernel
  have x4v147 : h4.fn v147 = v175 := by decide +kernel
  have x4v175 : h4.fn v175 = v147 := by decide +kernel
  have x5v0 : h5.fn v0 = v8 := by decide +kernel
  have x5v1 : h5.fn v1 = v5 := by decide +kernel
  have x5v2 : h5.fn v2 = v0 := by decide +kernel
  have x5v3 : h5.fn v3 = v1 := by decide +kernel
  have x5v4 : h5.fn v4 = v6 := by decide +kernel
  have x5v5 : h5.fn v5 = v3 := by decide +kernel
  have x5v6 : h5.fn v6 = v7 := by decide +kernel
  have x5v7 : h5.fn v7 = v4 := by decide +kernel
  have x5v8 : h5.fn v8 = v2 := by decide +kernel
  have x5v10 : h5.fn v10 = v170 := by decide +kernel
  have x5v23 : h5.fn v23 = v52 := by decide +kernel
  have x5v24 : h5.fn v24 = v53 := by decide +kernel
  have x5v30 : h5.fn v30 = v62 := by decide +kernel
  have x5v45 : h5.fn v45 = v179 := by decide +kernel
  have x5v52 : h5.fn v52 = v185 := by decide +kernel
  have x5v53 : h5.fn v53 = v187 := by decide +kernel
  have x5v54 : h5.fn v54 = v186 := by decide +kernel
  have x5v55 : h5.fn v55 = v188 := by decide +kernel
  have x5v100 : h5.fn v100 = v9 := by decide +kernel
  have x5v101 : h5.fn v101 = v10 := by decide +kernel
  have x5v103 : h5.fn v103 = v12 := by decide +kernel
  have x5v104 : h5.fn v104 = v54 := by decide +kernel
  have x5v105 : h5.fn v105 = v55 := by decide +kernel
  have x5v115 : h5.fn v115 = v13 := by decide +kernel
  have x5v116 : h5.fn v116 = v30 := by decide +kernel
  have x5v118 : h5.fn v118 = v39 := by decide +kernel
  have x5v152 : h5.fn v152 = v147 := by decide +kernel
  have x6v0 : h6.fn v0 = v3 := by decide +kernel
  have x6v1 : h6.fn v1 = v2 := by decide +kernel
  have x6v2 : h6.fn v2 = v1 := by decide +kernel
  have x6v3 : h6.fn v3 = v0 := by decide +kernel
  have x6v4 : h6.fn v4 = v4 := by decide +kernel
  have x6v5 : h6.fn v5 = v8 := by decide +kernel
  have x6v6 : h6.fn v6 = v7 := by decide +kernel
  have x6v7 : h6.fn v7 = v6 := by decide +kernel
  have x6v8 : h6.fn v8 = v5 := by decide +kernel
  have x6v10 : h6.fn v10 = v102 := by decide +kernel
  have x6v30 : h6.fn v30 = v68 := by decide +kernel
  have x6v41 : h6.fn v41 = v42 := by decide +kernel
  have x6v42 : h6.fn v42 = v41 := by decide +kernel
  have x6v44 : h6.fn v44 = v120 := by decide +kernel
  have x6v45 : h6.fn v45 = v121 := by decide +kernel
  have x6v46 : h6.fn v46 = v122 := by decide +kernel
  have x6v47 : h6.fn v47 = v123 := by decide +kernel
  have x6v52 : h6.fn v52 = v132 := by decide +kernel
  have x6v53 : h6.fn v53 = v133 := by decide +kernel
  have x6v54 : h6.fn v54 = v134 := by decide +kernel
  have x6v55 : h6.fn v55 = v135 := by decide +kernel
  have x6v68 : h6.fn v68 = v30 := by decide +kernel
  have x6v102 : h6.fn v102 = v10 := by decide +kernel
  have x6v120 : h6.fn v120 = v44 := by decide +kernel
  have x6v121 : h6.fn v121 = v45 := by decide +kernel
  have x6v122 : h6.fn v122 = v46 := by decide +kernel
  have x6v123 : h6.fn v123 = v47 := by decide +kernel
  have x6v132 : h6.fn v132 = v52 := by decide +kernel
  have x6v133 : h6.fn v133 = v53 := by decide +kernel
  have x6v134 : h6.fn v134 = v54 := by decide +kernel
  have x6v135 : h6.fn v135 = v55 := by decide +kernel
  have x7v0 : h7.fn v0 = v3 := by decide +kernel
  have x7v1 : h7.fn v1 = v8 := by decide +kernel
  have x7v2 : h7.fn v2 = v5 := by decide +kernel
  have x7v3 : h7.fn v3 = v0 := by decide +kernel
  have x7v4 : h7.fn v4 = v4 := by decide +kernel
  have x7v5 : h7.fn v5 = v2 := by decide +kernel
  have x7v6 : h7.fn v6 = v6 := by decide +kernel
  have x7v7 : h7.fn v7 = v7 := by decide +kernel
  have x7v8 : h7.fn v8 = v1 := by decide +kernel
  have x7v9 : h7.fn v9 = v136 := by decide +kernel
  have x7v10 : h7.fn v10 = v137 := by decide +kernel
  have x7v12 : h7.fn v12 = v139 := by decide +kernel
  have x7v13 : h7.fn v13 = v124 := by decide +kernel
  have x7v30 : h7.fn v30 = v125 := by decide +kernel
  have x7v39 : h7.fn v39 = v127 := by decide +kernel
  have x7v52 : h7.fn v52 = v128 := by decide +kernel
  have x7v53 : h7.fn v53 = v129 := by decide +kernel
  have x7v54 : h7.fn v54 = v130 := by decide +kernel
  have x7v55 : h7.fn v55 = v131 := by decide +kernel
  have x7v124 : h7.fn v124 = v13 := by decide +kernel
  have x7v125 : h7.fn v125 = v30 := by decide +kernel
  have x7v127 : h7.fn v127 = v39 := by decide +kernel
  have x7v128 : h7.fn v128 = v52 := by decide +kernel
  have x7v129 : h7.fn v129 = v53 := by decide +kernel
  have x7v130 : h7.fn v130 = v54 := by decide +kernel
  have x7v131 : h7.fn v131 = v55 := by decide +kernel
  have x7v136 : h7.fn v136 = v9 := by decide +kernel
  have x7v137 : h7.fn v137 = v10 := by decide +kernel
  have x7v139 : h7.fn v139 = v12 := by decide +kernel
  have x8v0 : h8.fn v0 = v1 := by decide +kernel
  have x8v1 : h8.fn v1 = v2 := by decide +kernel
  have x8v2 : h8.fn v2 = v3 := by decide +kernel
  have x8v3 : h8.fn v3 = v8 := by decide +kernel
  have x8v4 : h8.fn v4 = v6 := by decide +kernel
  have x8v5 : h8.fn v5 = v0 := by decide +kernel
  have x8v6 : h8.fn v6 = v7 := by decide +kernel
  have x8v7 : h8.fn v7 = v4 := by decide +kernel
  have x8v8 : h8.fn v8 = v5 := by decide +kernel
  have x8v9 : h8.fn v9 = v14 := by decide +kernel
  have x8v10 : h8.fn v10 = v64 := by decide +kernel
  have x8v12 : h8.fn v12 = v65 := by decide +kernel
  have x8v13 : h8.fn v13 = v66 := by decide +kernel
  have x8v30 : h8.fn v30 = v67 := by decide +kernel
  have x8v39 : h8.fn v39 = v69 := by decide +kernel
  have x8v50 : h8.fn v50 = v10 := by decide +kernel
  have x8v52 : h8.fn v52 = v92 := by decide +kernel
  have x8v53 : h8.fn v53 = v93 := by decide +kernel
  have x8v54 : h8.fn v54 = v94 := by decide +kernel
  have x8v55 : h8.fn v55 = v95 := by decide +kernel
  have x8v75 : h8.fn v75 = v41 := by decide +kernel
  have x8v86 : h8.fn v86 = v30 := by decide +kernel
  have x8v142 : h8.fn v142 = v52 := by decide +kernel
  have x8v143 : h8.fn v143 = v54 := by decide +kernel
  have x8v144 : h8.fn v144 = v53 := by decide +kernel
  have x8v145 : h8.fn v145 = v55 := by decide +kernel
  have x8v146 : h8.fn v146 = v173 := by decide +kernel
  have x8v147 : h8.fn v147 = v174 := by decide +kernel
  have x8v149 : h8.fn v149 = v176 := by decide +kernel
  have x8v164 : h8.fn v164 = v44 := by decide +kernel
  have x8v165 : h8.fn v165 = v45 := by decide +kernel
  have x8v166 : h8.fn v166 = v46 := by decide +kernel
  have x8v167 : h8.fn v167 = v47 := by decide +kernel
  have x9v0 : h9.fn v0 = v5 := by decide +kernel
  have x9v1 : h9.fn v1 = v8 := by decide +kernel
  have x9v2 : h9.fn v2 = v3 := by decide +kernel
  have x9v3 : h9.fn v3 = v2 := by decide +kernel
  have x9v4 : h9.fn v4 = v7 := by decide +kernel
  have x9v5 : h9.fn v5 = v0 := by decide +kernel
  have x9v6 : h9.fn v6 = v6 := by decide +kernel
  have x9v7 : h9.fn v7 = v4 := by decide +kernel
  have x9v8 : h9.fn v8 = v1 := by decide +kernel
  have x9v9 : h9.fn v9 = v168 := by decide +kernel
  have x9v10 : h9.fn v10 = v169 := by decide +kernel
  have x9v12 : h9.fn v12 = v171 := by decide +kernel
  have x9v30 : h9.fn v30 = v126 := by decide +kernel
  have x9v52 : h9.fn v52 = v78 := by decide +kernel
  have x9v53 : h9.fn v53 = v79 := by decide +kernel
  have x9v54 : h9.fn v54 = v162 := by decide +kernel
  have x9v55 : h9.fn v55 = v163 := by decide +kernel
  have x9v78 : h9.fn v78 = v52 := by decide +kernel
  have x9v79 : h9.fn v79 = v53 := by decide +kernel
  have x9v126 : h9.fn v126 = v30 := by decide +kernel
  have x9v162 : h9.fn v162 = v54 := by decide +kernel
  have x9v163 : h9.fn v163 = v55 := by decide +kernel
  have x9v168 : h9.fn v168 = v9 := by decide +kernel
  have x9v169 : h9.fn v169 = v10 := by decide +kernel
  have x9v171 : h9.fn v171 = v12 := by decide +kernel
  have x10v0 : h10.fn v0 = v8 := by decide +kernel
  have x10v1 : h10.fn v1 = v3 := by decide +kernel
  have x10v2 : h10.fn v2 = v2 := by decide +kernel
  have x10v3 : h10.fn v3 = v1 := by decide +kernel
  have x10v4 : h10.fn v4 = v6 := by decide +kernel
  have x10v5 : h10.fn v5 = v5 := by decide +kernel
  have x10v6 : h10.fn v6 = v4 := by decide +kernel
  have x10v7 : h10.fn v7 = v7 := by decide +kernel
  have x10v8 : h10.fn v8 = v0 := by decide +kernel
  have x10v10 : h10.fn v10 = v138 := by decide +kernel
  have x10v30 : h10.fn v30 = v117 := by decide +kernel
  have x10v41 : h10.fn v41 = v98 := by decide +kernel
  have x10v44 : h10.fn v44 = v177 := by decide +kernel
  have x10v45 : h10.fn v45 = v179 := by decide +kernel
  have x10v46 : h10.fn v46 = v178 := by decide +kernel
  have x10v47 : h10.fn v47 = v180 := by decide +kernel
  have x10v52 : h10.fn v52 = v154 := by decide +kernel
  have x10v53 : h10.fn v53 = v156 := by decide +kernel
  have x10v54 : h10.fn v54 = v155 := by decide +kernel
  have x10v55 : h10.fn v55 = v157 := by decide +kernel
  have x10v98 : h10.fn v98 = v41 := by decide +kernel
  have x10v117 : h10.fn v117 = v30 := by decide +kernel
  have x10v138 : h10.fn v138 = v10 := by decide +kernel
  have x10v154 : h10.fn v154 = v52 := by decide +kernel
  have x10v155 : h10.fn v155 = v54 := by decide +kernel
  have x10v156 : h10.fn v156 = v53 := by decide +kernel
  have x10v157 : h10.fn v157 = v55 := by decide +kernel
  have x10v177 : h10.fn v177 = v44 := by decide +kernel
  have x10v178 : h10.fn v178 = v46 := by decide +kernel
  have x10v179 : h10.fn v179 = v45 := by decide +kernel
  have x10v180 : h10.fn v180 = v47 := by decide +kernel
  have x11v0 : h11.fn v0 = v2 := by decide +kernel
  have x11v1 : h11.fn v1 = v3 := by decide +kernel
  have x11v2 : h11.fn v2 = v8 := by decide +kernel
  have x11v3 : h11.fn v3 = v5 := by decide +kernel
  have x11v4 : h11.fn v4 = v7 := by decide +kernel
  have x11v5 : h11.fn v5 = v1 := by decide +kernel
  have x11v6 : h11.fn v6 = v4 := by decide +kernel
  have x11v7 : h11.fn v7 = v6 := by decide +kernel
  have x11v8 : h11.fn v8 = v0 := by decide +kernel
  have x11v9 : h11.fn v9 = v100 := by decide +kernel
  have x11v10 : h11.fn v10 = v101 := by decide +kernel
  have x11v12 : h11.fn v12 = v103 := by decide +kernel
  have x11v13 : h11.fn v13 = v115 := by decide +kernel
  have x11v30 : h11.fn v30 = v116 := by decide +kernel
  have x11v39 : h11.fn v39 = v118 := by decide +kernel
  have x11v52 : h11.fn v52 = v23 := by decide +kernel
  have x11v53 : h11.fn v53 = v24 := by decide +kernel
  have x11v54 : h11.fn v54 = v104 := by decide +kernel
  have x11v55 : h11.fn v55 = v105 := by decide +kernel
  have x11v62 : h11.fn v62 = v30 := by decide +kernel
  have x11v147 : h11.fn v147 = v152 := by decide +kernel
  have x11v170 : h11.fn v170 = v10 := by decide +kernel
  have x11v179 : h11.fn v179 = v45 := by decide +kernel
  have x11v185 : h11.fn v185 = v52 := by decide +kernel
  have x11v186 : h11.fn v186 = v54 := by decide +kernel
  have x11v187 : h11.fn v187 = v53 := by decide +kernel
  have x11v188 : h11.fn v188 = v55 := by decide +kernel
  have e2 : excluded 10 s2 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p2) (by decide +kernel) _ (by decide +kernel)
    simp [p2]
  have e5 : excluded 10 s5 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p5) (by decide +kernel) _ (by decide +kernel)
    simp [p5]
  have e9 : excluded 10 s9 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p9) (by decide +kernel) _ (by decide +kernel)
    simp [p9]
  have e10 : excluded 10 s10 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p10) (by decide +kernel) _ (by decide +kernel)
    simp [p10]
  have e11 : excluded 10 s11 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p11) (by decide +kernel) _ (by decide +kernel)
    simp [p11]
  have e12 : excluded 10 s12 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p12) (by decide +kernel) _ (by decide +kernel)
    simp [p12]
  have e13 : excluded 10 s13 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p13) (by decide +kernel) _ (by decide +kernel)
    simp [p13]
  have e14 : excluded 10 s14 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p14) (by decide +kernel) _ (by decide +kernel)
    simp [p14]
  have e19 : excluded 10 s19 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p19) (by decide +kernel) _ (by decide +kernel)
    simp [p19]
  have e20 : excluded 10 s20 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p20) (by decide +kernel) _ (by decide +kernel)
    simp [p20]
  have e24 : excluded 10 s24 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p24) (by decide +kernel) _ (by decide +kernel)
    simp [p24]
  have e25 : excluded 10 s25 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p25) (by decide +kernel) _ (by decide +kernel)
    simp [p25]
  have e30 : excluded 10 s30 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p30) (by decide +kernel) _ (by decide +kernel)
    simp [p30]
  have e32 : excluded 10 s32 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p32) (by decide +kernel) _ (by decide +kernel)
    simp [p32]
  have e33 : excluded 10 s33 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p33) (by decide +kernel) _ (by decide +kernel)
    simp [p33]
  have e34 : excluded 10 s34 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p34) (by decide +kernel) _ (by decide +kernel)
    simp [p34]
  have e40 : excluded 10 s40 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p40) (by decide +kernel) _ (by decide +kernel)
    simp [p40]
  have e41 : excluded 10 s41 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p41) (by decide +kernel) _ (by decide +kernel)
    simp [p41]
  have e45 : excluded 10 s45 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p45) (by decide +kernel) _ (by decide +kernel)
    simp [p45]
  have e46 : excluded 10 s46 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p46) (by decide +kernel) _ (by decide +kernel)
    simp [p46]
  have e51 : excluded 10 s51 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p51) (by decide +kernel) _ (by decide +kernel)
    simp [p51]
  have e52 : excluded 10 s52 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p52) (by decide +kernel) _ (by decide +kernel)
    simp [p52]
  have e53 : excluded 10 s53 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p53) (by decide +kernel) _ (by decide +kernel)
    simp [p53]
  have e58 : excluded 10 s58 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p58) (by decide +kernel) _ (by decide +kernel)
    simp [p58]
  have e59 : excluded 10 s59 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p59) (by decide +kernel) _ (by decide +kernel)
    simp [p59]
  have e60 : excluded 10 s60 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p60) (by decide +kernel) _ (by decide +kernel)
    simp [p60]
  have e61 : excluded 10 s61 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p61) (by decide +kernel) _ (by decide +kernel)
    simp [p61]
  have e62 : excluded 10 s62 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p62) (by decide +kernel) _ (by decide +kernel)
    simp [p62]
  have e63 : excluded 10 s63 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p63) (by decide +kernel) _ (by decide +kernel)
    simp [p63]
  have e66 : excluded 10 s66 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p66) (by decide +kernel) _ (by decide +kernel)
    simp [p66]
  have e67 : excluded 10 s67 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p67) (by decide +kernel) _ (by decide +kernel)
    simp [p67]
  have e96 : excluded 10 s96 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p96) (by decide +kernel) _ (by decide +kernel)
    simp [p96]
  have e97 : excluded 10 s97 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=9) (blocked:=p97) (by decide +kernel) _ (by decide +kernel)
    simp [p97]
  have e3 : excluded 10 s3 := by
    apply move h2 h2 f2 _ _ e2
    · simp only [s3,List.map_cons,List.map_nil,x2v0,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v9,x2v18]
      decide +kernel
    · simp only [s3,List.all_cons,List.all_nil,x2v0,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v9,x2v18,x2v1,x2v13]
      decide +kernel
  have e15 : excluded 10 s15 := by
    apply move h2 h2 f2 _ _ e9
    · simp only [s15,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v6,x2v7,x2v8,x2v404]
      decide +kernel
    · simp only [s15,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v6,x2v7,x2v8,x2v404,x2v5,x2v249]
      decide +kernel
  have e16 : excluded 10 s16 := by
    apply move h2 h2 f2 _ _ e10
    · simp only [s16,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v6,x2v7,x2v8,x2v424]
      decide +kernel
    · simp only [s16,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v6,x2v7,x2v8,x2v424,x2v5,x2v275]
      decide +kernel
  have e17 : excluded 10 s17 := by
    apply move h2 h2 f2 _ _ e13
    · simp only [s17,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v7,x2v8,x2v447]
      decide +kernel
    · simp only [s17,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v7,x2v8,x2v447,x2v6,x2v356]
      decide +kernel
  have e18 : excluded 10 s18 := by
    apply move h2 h2 f2 _ _ e14
    · simp only [s18,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v7,x2v8,x2v466]
      decide +kernel
    · simp only [s18,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v7,x2v8,x2v466,x2v6,x2v379]
      decide +kernel
  have e21 : excluded 10 s21 := by
    apply move h2 h2 f2 _ _ e11
    · simp only [s21,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v523]
      decide +kernel
    · simp only [s21,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v523,x2v8,x2v304]
      decide +kernel
  have e22 : excluded 10 s22 := by
    apply move h2 h2 f2 _ _ e12
    · simp only [s22,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v538]
      decide +kernel
    · simp only [s22,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v538,x2v8,x2v329]
      decide +kernel
  have e26 : excluded 10 s26 := by
    apply move h4 h4 f4 _ _ e2
    · simp only [s26,List.map_cons,List.map_nil,x4v0,x4v1,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v13,x4v14]
      decide +kernel
    · simp only [s26,List.all_cons,List.all_nil,x4v0,x4v1,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v13,x4v14,x4v2,x4v9]
      decide +kernel
  have e27 : excluded 10 s27 := by
    apply move h4 h4 f4 _ _ e5
    · simp only [s27,List.map_cons,List.map_nil,x4v0,x4v1,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v13,x4v15]
      decide +kernel
    · simp only [s27,List.all_cons,List.all_nil,x4v0,x4v1,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v13,x4v15,x4v2,x4v10]
      decide +kernel
  have e28 : excluded 10 s28 := by
    apply move h4 h4 f4 _ _ e24
    · simp only [s28,List.map_cons,List.map_nil,x4v0,x4v1,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v13,x4v23]
      decide +kernel
    · simp only [s28,List.all_cons,List.all_nil,x4v0,x4v1,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v13,x4v23,x4v2,x4v56]
      decide +kernel
  have e29 : excluded 10 s29 := by
    apply move h4 h4 f4 _ _ e25
    · simp only [s29,List.map_cons,List.map_nil,x4v0,x4v1,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v13,x4v24]
      decide +kernel
    · simp only [s29,List.all_cons,List.all_nil,x4v0,x4v1,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v13,x4v24,x4v2,x4v57]
      decide +kernel
  have e47 : excluded 10 s47 := by
    apply move h1 h1 f1 _ _ e45
    · simp only [s47,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v8,x1v1002]
      decide +kernel
    · simp only [s47,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v8,x1v1002,x1v7,x1v946]
      decide +kernel
  have e48 : excluded 10 s48 := by
    apply move h1 h1 f1 _ _ e46
    · simp only [s48,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v8,x1v1027]
      decide +kernel
    · simp only [s48,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v8,x1v1027,x1v7,x1v973]
      decide +kernel
  have e54 : excluded 10 s54 := by
    apply move h1 h1 f1 _ _ e51
    · simp only [s54,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v5,x1v6,x1v7,x1v8,x1v45,x1v154]
      decide +kernel
    · simp only [s54,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v5,x1v6,x1v7,x1v8,x1v45,x1v154,x1v23]
      decide +kernel
  have e55 : excluded 10 s55 := by
    apply move h1 h1 f1 _ _ e52
    · simp only [s55,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v1127]
      decide +kernel
    · simp only [s55,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v1127,x1v1081]
      decide +kernel
  have e64 : excluded 10 s64 := by
    apply move h1 h1 f1 _ _ e58
    · simp only [s64,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v6,x1v7,x1v8,x1v1321]
      decide +kernel
    · simp only [s64,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v6,x1v7,x1v8,x1v1321,x1v5,x1v1184]
      decide +kernel
  have e65 : excluded 10 s65 := by
    apply move h1 h1 f1 _ _ e59
    · simp only [s65,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v6,x1v7,x1v8,x1v1342]
      decide +kernel
    · simp only [s65,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v6,x1v7,x1v8,x1v1342,x1v5,x1v1209]
      decide +kernel
  have e68 : excluded 10 s68 := by
    apply move h1 h1 f1 _ _ e66
    · simp only [s68,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v8,x1v1405]
      decide +kernel
    · simp only [s68,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v8,x1v1405,x1v7,x1v1365]
      decide +kernel
  have e69 : excluded 10 s69 := by
    apply move h1 h1 f1 _ _ e67
    · simp only [s69,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v8,x1v1422]
      decide +kernel
    · simp only [s69,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v8,x1v1422,x1v7,x1v1384]
      decide +kernel
  have e70 : excluded 10 s70 := by
    apply move h1 h1 f1 _ _ e60
    · simp only [s70,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v1441]
      decide +kernel
    · simp only [s70,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v1441,x1v8,x1v594]
      decide +kernel
  have e71 : excluded 10 s71 := by
    apply move h1 h1 f1 _ _ e61
    · simp only [s71,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v1455]
      decide +kernel
    · simp only [s71,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v1455,x1v8,x1v755]
      decide +kernel
  have e95 : excluded 10 s95 := by
    apply move h1 h1 f1 _ _ e24
    · simp only [s95,List.map_cons,List.map_nil,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v52,x1v60]
      decide +kernel
    · simp only [s95,List.all_cons,List.all_nil,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v52,x1v60,x1v56,x1v13]
      decide +kernel
  have e98 : excluded 10 s98 := by
    apply move h11 h5 f11 _ _ e51
    · simp only [s98,List.map_cons,List.map_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v7,x11v8,x11v52,x11v179]
      decide +kernel
    · simp only [s98,List.all_cons,List.all_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v7,x11v8,x11v52,x11v179,x5v2,x5v3,x5v8,x5v5,x5v7,x5v1,x5v6,x5v0,x5v23,x5v45]
      decide +kernel
  have e100 : excluded 10 s100 := by
    apply move h1 h1 f1 _ _ e25
    · simp only [s100,List.map_cons,List.map_nil,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v53,x1v60]
      decide +kernel
    · simp only [s100,List.all_cons,List.all_nil,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v53,x1v60,x1v57,x1v13]
      decide +kernel
  have e1 : excluded 11 s1 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p1) (by decide +kernel) _ (by decide +kernel)
    simp only [p1,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e2,e3⟩
  have e4 : excluded 11 s4 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p4) (by decide +kernel) _ (by decide +kernel)
    simp only [p4,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact e5
  have e8 : excluded 11 s8 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p8) (by decide +kernel) _ (by decide +kernel)
    simp only [p8,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,e20,e21,e22⟩
  have e23 : excluded 11 s23 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p23) (by decide +kernel) _ (by decide +kernel)
    simp only [p23,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e2,e5,e24,e25,e26,e27,e28,e29,e30⟩
  have e31 : excluded 11 s31 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p31) (by decide +kernel) _ (by decide +kernel)
    simp only [p31,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e32,e33,e34⟩
  have e38 : excluded 11 s38 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p38) (by decide +kernel) _ (by decide +kernel)
    simp [p38]
  have e39 : excluded 11 s39 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p39) (by decide +kernel) _ (by decide +kernel)
    simp only [p39,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e40,e41⟩
  have e42 : excluded 11 s42 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p42) (by decide +kernel) _ (by decide +kernel)
    simp [p42]
  have e44 : excluded 11 s44 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p44) (by decide +kernel) _ (by decide +kernel)
    simp only [p44,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e45,e46,e47,e48⟩
  have e49 : excluded 11 s49 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p49) (by decide +kernel) _ (by decide +kernel)
    simp [p49]
  have e50 : excluded 11 s50 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p50) (by decide +kernel) _ (by decide +kernel)
    simp only [p50,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e51,e52,e53,e54,e55⟩
  have e56 : excluded 11 s56 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p56) (by decide +kernel) _ (by decide +kernel)
    simp [p56]
  have e57 : excluded 11 s57 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p57) (by decide +kernel) _ (by decide +kernel)
    simp only [p57,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e58,e59,e60,e61,e62,e63,e64,e65,e66,e67,e68,e69,e70,e71⟩
  have e94 : excluded 11 s94 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p94) (by decide +kernel) _ (by decide +kernel)
    simp only [p94,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e95,e96,e97,e98⟩
  have e99 : excluded 11 s99 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p99) (by decide +kernel) _ (by decide +kernel)
    simp only [p99,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact e100
  have e101 : excluded 11 s101 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p101) (by decide +kernel) _ (by decide +kernel)
    simp [p101]
  have e102 : excluded 11 s102 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p102) (by decide +kernel) _ (by decide +kernel)
    simp [p102]
  have e368 : excluded 11 s368 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p368) (by decide +kernel) _ (by decide +kernel)
    simp [p368]
  have e369 : excluded 11 s369 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p369) (by decide +kernel) _ (by decide +kernel)
    simp [p369]
  have e371 : excluded 11 s371 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=10) (blocked:=p371) (by decide +kernel) _ (by decide +kernel)
    simp [p371]
  have e6 : excluded 11 s6 := by
    apply move h2 h2 f2 _ _ e4
    · simp only [s6,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v11]
      decide +kernel
    · simp only [s6,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v11,x2v10]
      decide +kernel
  have e35 : excluded 11 s35 := by
    apply move h4 h4 f4 _ _ e31
    · simp only [s35,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v38]
      decide +kernel
    · simp only [s35,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v38,x4v30]
      decide +kernel
  have e43 : excluded 11 s43 := by
    apply move h6 h6 f6 _ _ e42
    · simp only [s43,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v42]
      decide +kernel
    · simp only [s43,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v42,x6v41]
      decide +kernel
  have e72 : excluded 11 s72 := by
    apply move h1 h1 f1 _ _ e1
    · simp only [s72,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v48]
      decide +kernel
    · simp only [s72,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v48,x1v9]
      decide +kernel
  have e75 : excluded 11 s75 := by
    apply move h1 h1 f1 _ _ e4
    · simp only [s75,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v49]
      decide +kernel
    · simp only [s75,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v49,x1v10]
      decide +kernel
  have e77 : excluded 11 s77 := by
    apply move h8 h3 f8 _ _ e4
    · simp only [s77,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v50]
      decide +kernel
    · simp only [s77,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v50,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v10]
      decide +kernel
  have e79 : excluded 11 s79 := by
    apply move h1 h1 f1 _ _ e8
    · simp only [s79,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v51]
      decide +kernel
    · simp only [s79,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v51,x1v12]
      decide +kernel
  have e103 : excluded 11 s103 := by
    apply move h1 h1 f1 _ _ e94
    · simp only [s103,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v56]
      decide +kernel
    · simp only [s103,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v56,x1v52]
      decide +kernel
  have e107 : excluded 11 s107 := by
    apply move h1 h1 f1 _ _ e99
    · simp only [s107,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v57]
      decide +kernel
    · simp only [s107,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v57,x1v53]
      decide +kernel
  have e108 : excluded 11 s108 := by
    apply move h1 h1 f1 _ _ e101
    · simp only [s108,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v58]
      decide +kernel
    · simp only [s108,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v58,x1v54]
      decide +kernel
  have e109 : excluded 11 s109 := by
    apply move h1 h1 f1 _ _ e102
    · simp only [s109,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v59]
      decide +kernel
    · simp only [s109,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v59,x1v55]
      decide +kernel
  have e110 : excluded 11 s110 := by
    apply move h1 h1 f1 _ _ e23
    · simp only [s110,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v60]
      decide +kernel
    · simp only [s110,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v60,x1v13]
      decide +kernel
  have e115 : excluded 11 s115 := by
    apply move h1 h1 f1 _ _ e31
    · simp only [s115,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v61]
      decide +kernel
    · simp only [s115,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v61,x1v30]
      decide +kernel
  have e119 : excluded 11 s119 := by
    apply move h11 h5 f11 _ _ e31
    · simp only [s119,List.map_cons,List.map_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v62]
      decide +kernel
    · simp only [s119,List.all_cons,List.all_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v62,x5v2,x5v3,x5v8,x5v5,x5v7,x5v1,x5v4,x5v6,x5v0,x5v30]
      decide +kernel
  have e122 : excluded 11 s122 := by
    apply move h1 h1 f1 _ _ e38
    · simp only [s122,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v63]
      decide +kernel
    · simp only [s122,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v63,x1v39]
      decide +kernel
  have e123 : excluded 11 s123 := by
    apply move h3 h8 f3 _ _ e1
    · simp only [s123,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v14]
      decide +kernel
    · simp only [s123,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v14,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v9]
      decide +kernel
  have e125 : excluded 11 s125 := by
    apply move h3 h8 f3 _ _ e4
    · simp only [s125,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v64]
      decide +kernel
    · simp only [s125,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v64,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v10]
      decide +kernel
  have e127 : excluded 11 s127 := by
    apply move h4 h4 f4 _ _ e4
    · simp only [s127,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v15]
      decide +kernel
    · simp only [s127,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v15,x4v10]
      decide +kernel
  have e128 : excluded 11 s128 := by
    apply move h3 h8 f3 _ _ e8
    · simp only [s128,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v65]
      decide +kernel
    · simp only [s128,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v65,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v12]
      decide +kernel
  have e143 : excluded 11 s143 := by
    apply move h3 h8 f3 _ _ e23
    · simp only [s143,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v66]
      decide +kernel
    · simp only [s143,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v66,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v13]
      decide +kernel
  have e151 : excluded 11 s151 := by
    apply move h3 h8 f3 _ _ e31
    · simp only [s151,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v67]
      decide +kernel
    · simp only [s151,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v67,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v30]
      decide +kernel
  have e155 : excluded 11 s155 := by
    apply move h6 h6 f6 _ _ e31
    · simp only [s155,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v68]
      decide +kernel
    · simp only [s155,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v68,x6v30]
      decide +kernel
  have e158 : excluded 11 s158 := by
    apply move h3 h8 f3 _ _ e38
    · simp only [s158,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v69]
      decide +kernel
    · simp only [s158,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v69,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v39]
      decide +kernel
  have e159 : excluded 11 s159 := by
    apply move h2 h2 f2 _ _ e94
    · simp only [s159,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v16]
      decide +kernel
    · simp only [s159,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v16,x2v52]
      decide +kernel
  have e163 : excluded 11 s163 := by
    apply move h2 h2 f2 _ _ e99
    · simp only [s163,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v17]
      decide +kernel
    · simp only [s163,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v17,x2v53]
      decide +kernel
  have e164 : excluded 11 s164 := by
    apply move h2 h2 f2 _ _ e101
    · simp only [s164,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v70]
      decide +kernel
    · simp only [s164,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v70,x2v54]
      decide +kernel
  have e165 : excluded 11 s165 := by
    apply move h2 h2 f2 _ _ e102
    · simp only [s165,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v71]
      decide +kernel
    · simp only [s165,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v71,x2v55]
      decide +kernel
  have e166 : excluded 11 s166 := by
    apply move h2 h2 f2 _ _ e23
    · simp only [s166,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v18]
      decide +kernel
    · simp only [s166,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v18,x2v13]
      decide +kernel
  have e171 : excluded 11 s171 := by
    apply move h2 h2 f2 _ _ e31
    · simp only [s171,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v19]
      decide +kernel
    · simp only [s171,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v19,x2v30]
      decide +kernel
  have e175 : excluded 11 s175 := by
    apply move h8 h3 f8 _ _ e31
    · simp only [s175,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v86]
      decide +kernel
    · simp only [s175,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v86,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v30]
      decide +kernel
  have e178 : excluded 11 s178 := by
    apply move h2 h2 f2 _ _ e38
    · simp only [s178,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v87]
      decide +kernel
    · simp only [s178,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v87,x2v39]
      decide +kernel
  have e179 : excluded 11 s179 := by
    apply move h2 h2 f2 _ _ e49
    · simp only [s179,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v88]
      decide +kernel
    · simp only [s179,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v88,x2v44]
      decide +kernel
  have e180 : excluded 11 s180 := by
    apply move h2 h2 f2 _ _ e50
    · simp only [s180,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v89]
      decide +kernel
    · simp only [s180,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v89,x2v45]
      decide +kernel
  have e186 : excluded 11 s186 := by
    apply move h2 h2 f2 _ _ e56
    · simp only [s186,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v90]
      decide +kernel
    · simp only [s186,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v90,x2v46]
      decide +kernel
  have e187 : excluded 11 s187 := by
    apply move h2 h2 f2 _ _ e57
    · simp only [s187,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v91]
      decide +kernel
    · simp only [s187,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v91,x2v47]
      decide +kernel
  have e202 : excluded 11 s202 := by
    apply move h3 h8 f3 _ _ e94
    · simp only [s202,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v92]
      decide +kernel
    · simp only [s202,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v92,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v52]
      decide +kernel
  have e205 : excluded 11 s205 := by
    apply move h3 h8 f3 _ _ e99
    · simp only [s205,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v93]
      decide +kernel
    · simp only [s205,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v93,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v53]
      decide +kernel
  have e206 : excluded 11 s206 := by
    apply move h3 h8 f3 _ _ e101
    · simp only [s206,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v94]
      decide +kernel
    · simp only [s206,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v94,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v54]
      decide +kernel
  have e207 : excluded 11 s207 := by
    apply move h3 h8 f3 _ _ e102
    · simp only [s207,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v95]
      decide +kernel
    · simp only [s207,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v95,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v55]
      decide +kernel
  have e208 : excluded 11 s208 := by
    apply move h2 h2 f2 _ _ e39
    · simp only [s208,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v96]
      decide +kernel
    · simp only [s208,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v96,x2v40]
      decide +kernel
  have e211 : excluded 11 s211 := by
    apply move h2 h2 f2 _ _ e42
    · simp only [s211,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v97]
      decide +kernel
    · simp only [s211,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v97,x2v41]
      decide +kernel
  have e212 : excluded 11 s212 := by
    apply move h10 h10 f10 _ _ e42
    · simp only [s212,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v98]
      decide +kernel
    · simp only [s212,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v98,x10v41]
      decide +kernel
  have e213 : excluded 11 s213 := by
    apply move h2 h2 f2 _ _ e44
    · simp only [s213,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v99]
      decide +kernel
    · simp only [s213,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v99,x2v43]
      decide +kernel
  have e218 : excluded 11 s218 := by
    apply move h5 h11 f5 _ _ e1
    · simp only [s218,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v100]
      decide +kernel
    · simp only [s218,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v100,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v9]
      decide +kernel
  have e220 : excluded 11 s220 := by
    apply move h5 h11 f5 _ _ e4
    · simp only [s220,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v101]
      decide +kernel
    · simp only [s220,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v101,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v10]
      decide +kernel
  have e222 : excluded 11 s222 := by
    apply move h6 h6 f6 _ _ e4
    · simp only [s222,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v102]
      decide +kernel
    · simp only [s222,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v102,x6v10]
      decide +kernel
  have e223 : excluded 11 s223 := by
    apply move h5 h11 f5 _ _ e8
    · simp only [s223,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v103]
      decide +kernel
    · simp only [s223,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v103,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v12]
      decide +kernel
  have e238 : excluded 11 s238 := by
    apply move h5 h11 f5 _ _ e94
    · simp only [s238,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v23]
      decide +kernel
    · simp only [s238,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v23,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v52]
      decide +kernel
  have e240 : excluded 11 s240 := by
    apply move h5 h11 f5 _ _ e99
    · simp only [s240,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v24]
      decide +kernel
    · simp only [s240,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v24,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v53]
      decide +kernel
  have e241 : excluded 11 s241 := by
    apply move h5 h11 f5 _ _ e101
    · simp only [s241,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v104]
      decide +kernel
    · simp only [s241,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v104,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v54]
      decide +kernel
  have e242 : excluded 11 s242 := by
    apply move h5 h11 f5 _ _ e102
    · simp only [s242,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v105]
      decide +kernel
    · simp only [s242,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v105,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v55]
      decide +kernel
  have e243 : excluded 11 s243 := by
    apply move h4 h4 f4 _ _ e39
    · simp only [s243,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v25]
      decide +kernel
    · simp only [s243,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v25,x4v40]
      decide +kernel
  have e246 : excluded 11 s246 := by
    apply move h4 h4 f4 _ _ e42
    · simp only [s246,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v26]
      decide +kernel
    · simp only [s246,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v26,x4v41]
      decide +kernel
  have e247 : excluded 11 s247 := by
    apply move h8 h3 f8 _ _ e42
    · simp only [s247,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v75]
      decide +kernel
    · simp only [s247,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v75,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v41]
      decide +kernel
  have e248 : excluded 11 s248 := by
    apply move h4 h4 f4 _ _ e44
    · simp only [s248,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v106]
      decide +kernel
    · simp only [s248,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v106,x4v43]
      decide +kernel
  have e253 : excluded 11 s253 := by
    apply move h4 h4 f4 _ _ e94
    · simp only [s253,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v107]
      decide +kernel
    · simp only [s253,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v107,x4v52]
      decide +kernel
  have e258 : excluded 11 s258 := by
    apply move h4 h4 f4 _ _ e99
    · simp only [s258,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v108]
      decide +kernel
    · simp only [s258,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v108,x4v53]
      decide +kernel
  have e260 : excluded 11 s260 := by
    apply move h4 h4 f4 _ _ e101
    · simp only [s260,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v109]
      decide +kernel
    · simp only [s260,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v109,x4v54]
      decide +kernel
  have e261 : excluded 11 s261 := by
    apply move h4 h4 f4 _ _ e102
    · simp only [s261,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v110]
      decide +kernel
    · simp only [s261,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v110,x4v55]
      decide +kernel
  have e262 : excluded 11 s262 := by
    apply move h4 h4 f4 _ _ e49
    · simp only [s262,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v111]
      decide +kernel
    · simp only [s262,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v111,x4v44]
      decide +kernel
  have e263 : excluded 11 s263 := by
    apply move h4 h4 f4 _ _ e50
    · simp only [s263,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v112]
      decide +kernel
    · simp only [s263,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v112,x4v45]
      decide +kernel
  have e268 : excluded 11 s268 := by
    apply move h4 h4 f4 _ _ e56
    · simp only [s268,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v113]
      decide +kernel
    · simp only [s268,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v113,x4v46]
      decide +kernel
  have e269 : excluded 11 s269 := by
    apply move h4 h4 f4 _ _ e57
    · simp only [s269,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v114]
      decide +kernel
    · simp only [s269,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v114,x4v47]
      decide +kernel
  have e284 : excluded 11 s284 := by
    apply move h5 h11 f5 _ _ e23
    · simp only [s284,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v115]
      decide +kernel
    · simp only [s284,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v115,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v13]
      decide +kernel
  have e289 : excluded 11 s289 := by
    apply move h5 h11 f5 _ _ e31
    · simp only [s289,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v116]
      decide +kernel
    · simp only [s289,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v116,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v30]
      decide +kernel
  have e293 : excluded 11 s293 := by
    apply move h10 h10 f10 _ _ e31
    · simp only [s293,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v117]
      decide +kernel
    · simp only [s293,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v117,x10v30]
      decide +kernel
  have e296 : excluded 11 s296 := by
    apply move h5 h11 f5 _ _ e38
    · simp only [s296,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v118]
      decide +kernel
    · simp only [s296,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v118,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v39]
      decide +kernel
  have e297 : excluded 11 s297 := by
    apply move h6 h6 f6 _ _ e49
    · simp only [s297,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v120]
      decide +kernel
    · simp only [s297,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v120,x6v44]
      decide +kernel
  have e298 : excluded 11 s298 := by
    apply move h6 h6 f6 _ _ e50
    · simp only [s298,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v121]
      decide +kernel
    · simp only [s298,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v121,x6v45]
      decide +kernel
  have e302 : excluded 11 s302 := by
    apply move h6 h6 f6 _ _ e56
    · simp only [s302,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v122]
      decide +kernel
    · simp only [s302,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v122,x6v46]
      decide +kernel
  have e303 : excluded 11 s303 := by
    apply move h6 h6 f6 _ _ e57
    · simp only [s303,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v123]
      decide +kernel
    · simp only [s303,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v123,x6v47]
      decide +kernel
  have e318 : excluded 11 s318 := by
    apply move h7 h7 f7 _ _ e23
    · simp only [s318,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v124]
      decide +kernel
    · simp only [s318,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v124,x7v13]
      decide +kernel
  have e327 : excluded 11 s327 := by
    apply move h7 h7 f7 _ _ e31
    · simp only [s327,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v125]
      decide +kernel
    · simp only [s327,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v125,x7v30]
      decide +kernel
  have e331 : excluded 11 s331 := by
    apply move h9 h9 f9 _ _ e31
    · simp only [s331,List.map_cons,List.map_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v126]
      decide +kernel
    · simp only [s331,List.all_cons,List.all_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v126,x9v30]
      decide +kernel
  have e334 : excluded 11 s334 := by
    apply move h7 h7 f7 _ _ e38
    · simp only [s334,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v127]
      decide +kernel
    · simp only [s334,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v127,x7v39]
      decide +kernel
  have e335 : excluded 11 s335 := by
    apply move h7 h7 f7 _ _ e94
    · simp only [s335,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v128]
      decide +kernel
    · simp only [s335,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v128,x7v52]
      decide +kernel
  have e336 : excluded 11 s336 := by
    apply move h7 h7 f7 _ _ e99
    · simp only [s336,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v129]
      decide +kernel
    · simp only [s336,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v129,x7v53]
      decide +kernel
  have e337 : excluded 11 s337 := by
    apply move h7 h7 f7 _ _ e101
    · simp only [s337,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v130]
      decide +kernel
    · simp only [s337,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v130,x7v54]
      decide +kernel
  have e338 : excluded 11 s338 := by
    apply move h7 h7 f7 _ _ e102
    · simp only [s338,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v131]
      decide +kernel
    · simp only [s338,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v131,x7v55]
      decide +kernel
  have e339 : excluded 11 s339 := by
    apply move h6 h6 f6 _ _ e94
    · simp only [s339,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v132]
      decide +kernel
    · simp only [s339,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v132,x6v52]
      decide +kernel
  have e342 : excluded 11 s342 := by
    apply move h6 h6 f6 _ _ e99
    · simp only [s342,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v133]
      decide +kernel
    · simp only [s342,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v133,x6v53]
      decide +kernel
  have e343 : excluded 11 s343 := by
    apply move h6 h6 f6 _ _ e101
    · simp only [s343,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v134]
      decide +kernel
    · simp only [s343,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v134,x6v54]
      decide +kernel
  have e344 : excluded 11 s344 := by
    apply move h6 h6 f6 _ _ e102
    · simp only [s344,List.map_cons,List.map_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v135]
      decide +kernel
    · simp only [s344,List.all_cons,List.all_nil,x6v0,x6v1,x6v2,x6v3,x6v4,x6v5,x6v6,x6v7,x6v8,x6v135,x6v55]
      decide +kernel
  have e345 : excluded 11 s345 := by
    apply move h7 h7 f7 _ _ e1
    · simp only [s345,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v136]
      decide +kernel
    · simp only [s345,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v136,x7v9]
      decide +kernel
  have e346 : excluded 11 s346 := by
    apply move h7 h7 f7 _ _ e4
    · simp only [s346,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v137]
      decide +kernel
    · simp only [s346,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v137,x7v10]
      decide +kernel
  have e347 : excluded 11 s347 := by
    apply move h10 h10 f10 _ _ e4
    · simp only [s347,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v138]
      decide +kernel
    · simp only [s347,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v138,x10v10]
      decide +kernel
  have e348 : excluded 11 s348 := by
    apply move h7 h7 f7 _ _ e8
    · simp only [s348,List.map_cons,List.map_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v139]
      decide +kernel
    · simp only [s348,List.all_cons,List.all_nil,x7v0,x7v1,x7v2,x7v3,x7v4,x7v5,x7v6,x7v7,x7v8,x7v139,x7v12]
      decide +kernel
  have e363 : excluded 11 s363 := by
    apply move h8 h3 f8 _ _ e94
    · simp only [s363,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v142]
      decide +kernel
    · simp only [s363,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v142,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v52]
      decide +kernel
  have e365 : excluded 11 s365 := by
    apply move h8 h3 f8 _ _ e101
    · simp only [s365,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v143]
      decide +kernel
    · simp only [s365,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v143,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v54]
      decide +kernel
  have e366 : excluded 11 s366 := by
    apply move h8 h3 f8 _ _ e99
    · simp only [s366,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v144]
      decide +kernel
    · simp only [s366,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v144,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v53]
      decide +kernel
  have e367 : excluded 11 s367 := by
    apply move h8 h3 f8 _ _ e102
    · simp only [s367,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v145]
      decide +kernel
    · simp only [s367,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v145,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v55]
      decide +kernel
  have e370 : excluded 11 s370 := by
    apply move h2 h2 f2 _ _ e369
    · simp only [s370,List.map_cons,List.map_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v148]
      decide +kernel
    · simp only [s370,List.all_cons,List.all_nil,x2v0,x2v1,x2v2,x2v3,x2v4,x2v5,x2v6,x2v7,x2v8,x2v148,x2v147]
      decide +kernel
  have e372 : excluded 11 s372 := by
    apply move h1 h1 f1 _ _ e368
    · simp only [s372,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v150]
      decide +kernel
    · simp only [s372,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v150,x1v146]
      decide +kernel
  have e373 : excluded 11 s373 := by
    apply move h1 h1 f1 _ _ e369
    · simp only [s373,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v151]
      decide +kernel
    · simp only [s373,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v151,x1v147]
      decide +kernel
  have e374 : excluded 11 s374 := by
    apply move h5 h11 f5 _ _ e369
    · simp only [s374,List.map_cons,List.map_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v152]
      decide +kernel
    · simp only [s374,List.all_cons,List.all_nil,x5v0,x5v1,x5v2,x5v3,x5v4,x5v5,x5v6,x5v7,x5v8,x5v152,x11v8,x11v5,x11v0,x11v1,x11v6,x11v3,x11v7,x11v4,x11v2,x11v147]
      decide +kernel
  have e375 : excluded 11 s375 := by
    apply move h1 h1 f1 _ _ e371
    · simp only [s375,List.map_cons,List.map_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v153]
      decide +kernel
    · simp only [s375,List.all_cons,List.all_nil,x1v0,x1v1,x1v2,x1v3,x1v4,x1v5,x1v6,x1v7,x1v8,x1v153,x1v149]
      decide +kernel
  have e376 : excluded 11 s376 := by
    apply move h10 h10 f10 _ _ e94
    · simp only [s376,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v154]
      decide +kernel
    · simp only [s376,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v154,x10v52]
      decide +kernel
  have e377 : excluded 11 s377 := by
    apply move h10 h10 f10 _ _ e101
    · simp only [s377,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v155]
      decide +kernel
    · simp only [s377,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v155,x10v54]
      decide +kernel
  have e378 : excluded 11 s378 := by
    apply move h10 h10 f10 _ _ e99
    · simp only [s378,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v156]
      decide +kernel
    · simp only [s378,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v156,x10v53]
      decide +kernel
  have e379 : excluded 11 s379 := by
    apply move h10 h10 f10 _ _ e102
    · simp only [s379,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v157]
      decide +kernel
    · simp only [s379,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v157,x10v55]
      decide +kernel
  have e380 : excluded 11 s380 := by
    apply move h9 h9 f9 _ _ e94
    · simp only [s380,List.map_cons,List.map_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v78]
      decide +kernel
    · simp only [s380,List.all_cons,List.all_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v78,x9v52]
      decide +kernel
  have e381 : excluded 11 s381 := by
    apply move h9 h9 f9 _ _ e99
    · simp only [s381,List.map_cons,List.map_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v79]
      decide +kernel
    · simp only [s381,List.all_cons,List.all_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v79,x9v53]
      decide +kernel
  have e382 : excluded 11 s382 := by
    apply move h9 h9 f9 _ _ e101
    · simp only [s382,List.map_cons,List.map_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v162]
      decide +kernel
    · simp only [s382,List.all_cons,List.all_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v162,x9v54]
      decide +kernel
  have e383 : excluded 11 s383 := by
    apply move h9 h9 f9 _ _ e102
    · simp only [s383,List.map_cons,List.map_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v163]
      decide +kernel
    · simp only [s383,List.all_cons,List.all_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v163,x9v55]
      decide +kernel
  have e384 : excluded 11 s384 := by
    apply move h8 h3 f8 _ _ e49
    · simp only [s384,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v164]
      decide +kernel
    · simp only [s384,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v164,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v44]
      decide +kernel
  have e385 : excluded 11 s385 := by
    apply move h8 h3 f8 _ _ e50
    · simp only [s385,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v165]
      decide +kernel
    · simp only [s385,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v165,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v45]
      decide +kernel
  have e388 : excluded 11 s388 := by
    apply move h8 h3 f8 _ _ e56
    · simp only [s388,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v166]
      decide +kernel
    · simp only [s388,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v166,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v46]
      decide +kernel
  have e389 : excluded 11 s389 := by
    apply move h8 h3 f8 _ _ e57
    · simp only [s389,List.map_cons,List.map_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v167]
      decide +kernel
    · simp only [s389,List.all_cons,List.all_nil,x8v0,x8v1,x8v2,x8v3,x8v4,x8v5,x8v6,x8v7,x8v8,x8v167,x3v1,x3v2,x3v3,x3v8,x3v6,x3v0,x3v7,x3v4,x3v5,x3v47]
      decide +kernel
  have e404 : excluded 11 s404 := by
    apply move h9 h9 f9 _ _ e1
    · simp only [s404,List.map_cons,List.map_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v168]
      decide +kernel
    · simp only [s404,List.all_cons,List.all_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v168,x9v9]
      decide +kernel
  have e405 : excluded 11 s405 := by
    apply move h9 h9 f9 _ _ e4
    · simp only [s405,List.map_cons,List.map_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v169]
      decide +kernel
    · simp only [s405,List.all_cons,List.all_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v169,x9v10]
      decide +kernel
  have e406 : excluded 11 s406 := by
    apply move h11 h5 f11 _ _ e4
    · simp only [s406,List.map_cons,List.map_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v170]
      decide +kernel
    · simp only [s406,List.all_cons,List.all_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v170,x5v2,x5v3,x5v8,x5v5,x5v7,x5v1,x5v4,x5v6,x5v0,x5v10]
      decide +kernel
  have e407 : excluded 11 s407 := by
    apply move h9 h9 f9 _ _ e8
    · simp only [s407,List.map_cons,List.map_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v171]
      decide +kernel
    · simp only [s407,List.all_cons,List.all_nil,x9v0,x9v1,x9v2,x9v3,x9v4,x9v5,x9v6,x9v7,x9v8,x9v171,x9v12]
      decide +kernel
  have e422 : excluded 11 s422 := by
    apply move h3 h8 f3 _ _ e368
    · simp only [s422,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v173]
      decide +kernel
    · simp only [s422,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v173,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v146]
      decide +kernel
  have e423 : excluded 11 s423 := by
    apply move h3 h8 f3 _ _ e369
    · simp only [s423,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v174]
      decide +kernel
    · simp only [s423,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v174,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v147]
      decide +kernel
  have e424 : excluded 11 s424 := by
    apply move h4 h4 f4 _ _ e369
    · simp only [s424,List.map_cons,List.map_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v175]
      decide +kernel
    · simp only [s424,List.all_cons,List.all_nil,x4v0,x4v1,x4v2,x4v3,x4v4,x4v5,x4v6,x4v7,x4v8,x4v175,x4v147]
      decide +kernel
  have e425 : excluded 11 s425 := by
    apply move h3 h8 f3 _ _ e371
    · simp only [s425,List.map_cons,List.map_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v176]
      decide +kernel
    · simp only [s425,List.all_cons,List.all_nil,x3v0,x3v1,x3v2,x3v3,x3v4,x3v5,x3v6,x3v7,x3v8,x3v176,x8v5,x8v0,x8v1,x8v2,x8v7,x8v8,x8v4,x8v6,x8v3,x8v149]
      decide +kernel
  have e426 : excluded 11 s426 := by
    apply move h10 h10 f10 _ _ e49
    · simp only [s426,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v177]
      decide +kernel
    · simp only [s426,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v177,x10v44]
      decide +kernel
  have e427 : excluded 11 s427 := by
    apply move h10 h10 f10 _ _ e56
    · simp only [s427,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v178]
      decide +kernel
    · simp only [s427,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v178,x10v46]
      decide +kernel
  have e428 : excluded 11 s428 := by
    apply move h10 h10 f10 _ _ e50
    · simp only [s428,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v179]
      decide +kernel
    · simp only [s428,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v179,x10v45]
      decide +kernel
  have e431 : excluded 11 s431 := by
    apply move h10 h10 f10 _ _ e57
    · simp only [s431,List.map_cons,List.map_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v180]
      decide +kernel
    · simp only [s431,List.all_cons,List.all_nil,x10v0,x10v1,x10v2,x10v3,x10v4,x10v5,x10v6,x10v7,x10v8,x10v180,x10v47]
      decide +kernel
  have e446 : excluded 11 s446 := by
    apply move h11 h5 f11 _ _ e94
    · simp only [s446,List.map_cons,List.map_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v185]
      decide +kernel
    · simp only [s446,List.all_cons,List.all_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v185,x5v2,x5v3,x5v8,x5v5,x5v7,x5v1,x5v4,x5v6,x5v0,x5v52]
      decide +kernel
  have e447 : excluded 11 s447 := by
    apply move h11 h5 f11 _ _ e101
    · simp only [s447,List.map_cons,List.map_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v186]
      decide +kernel
    · simp only [s447,List.all_cons,List.all_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v186,x5v2,x5v3,x5v8,x5v5,x5v7,x5v1,x5v4,x5v6,x5v0,x5v54]
      decide +kernel
  have e448 : excluded 11 s448 := by
    apply move h11 h5 f11 _ _ e99
    · simp only [s448,List.map_cons,List.map_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v187]
      decide +kernel
    · simp only [s448,List.all_cons,List.all_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v187,x5v2,x5v3,x5v8,x5v5,x5v7,x5v1,x5v4,x5v6,x5v0,x5v53]
      decide +kernel
  have e449 : excluded 11 s449 := by
    apply move h11 h5 f11 _ _ e102
    · simp only [s449,List.map_cons,List.map_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v188]
      decide +kernel
    · simp only [s449,List.all_cons,List.all_nil,x11v0,x11v1,x11v2,x11v3,x11v4,x11v5,x11v6,x11v7,x11v8,x11v188,x5v2,x5v3,x5v8,x5v5,x5v7,x5v1,x5v4,x5v6,x5v0,x5v55]
      decide +kernel
  have e0 : excluded 12 s0 := by
    apply PEqualNP.Outside.L_meta_3400_aux.Guard3400.resolve (k:=11) (blocked:=p0) (by decide +kernel) _ (by decide +kernel)
    simp only [p0,List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    exact ⟨e1,e4,e6,e8,e23,e31,e35,e38,e39,e42,e43,e44,e49,e50,e56,e57,e72,e75,e77,e79,e94,e99,e101,e102,e103,e107,e108,e109,e110,e115,e119,e122,e123,e125,e127,e128,e143,e151,e155,e158,e159,e163,e164,e165,e166,e171,e175,e178,e179,e180,e186,e187,e202,e205,e206,e207,e208,e211,e212,e213,e218,e220,e222,e223,e238,e240,e241,e242,e243,e246,e247,e248,e253,e258,e260,e261,e262,e263,e268,e269,e284,e289,e293,e296,e297,e298,e302,e303,e318,e327,e331,e334,e335,e336,e337,e338,e339,e342,e343,e344,e345,e346,e347,e348,e363,e365,e366,e367,e368,e369,e370,e371,e372,e373,e374,e375,e376,e377,e378,e379,e380,e381,e382,e383,e384,e385,e388,e389,e404,e405,e406,e407,e422,e423,e424,e425,e426,e427,e428,e431,e446,e447,e448,e449⟩
  exact e0
end PEqualNP.Outside.L_meta_3400_aux.Orbit3400

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3400_aux.Basis1868 PEqualNP.Outside.L_meta_3400_aux.Check2516 PEqualNP.Outside.L_meta_3400_aux.Free1868 PEqualNP.Outside.L_meta_3400_aux.Orbit3400
namespace PEqualNP.Outside.L_meta_3400_aux.Bound3400
set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
lemma total (C : Circuit) : C.gates.countP costly + PEqualNP.NotBracket.notCount C = C.size := by
  unfold PEqualNP.NotBracket.notCount Circuit.size
  rw [← List.countP_eq_length_filter]
  apply Eq.trans _ (List.length_eq_countP_add_countP costly (l:=C.gates)).symm
  apply congrArg (fun n => C.gates.countP costly + n)
  apply congrArg (fun f => C.gates.countP f)
  funext g
  obtain ⟨op,ins⟩ := g
  cases op <;> simp [costly]
end PEqualNP.Outside.L_meta_3400_aux.Bound3400

set_option maxRecDepth 120000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_3400 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x4 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x3 x4.1 && x3 x4.2) → (13 : ℕ) ≤ x1.size - PEqualNP.NotBracket.notCount x1 := by
  intro C fan he
  have agree (x : Fin 9 → Bool) : C.eval (List.ofFn x)=edgeF x := by
    have h := he x
    simp only [List.any_cons,List.any_nil,Bool.or_false,edgeF,Bool.or_assoc] at h ⊢
    exact h
  have out := get_target C fan agree
  obtain ⟨k,t,S,b,hl,sub⟩ := tagExtract C.gates xs xv fan out
  obtain ⟨m,T,mc,hB,hsub⟩ := compress hl
  have incl : T⊆canonicalInputs.toFinset := by
    intro u hu
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (hsub hu)
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,sub a ha,rfl⟩)
  rw [canonical_needed hB incl] at hB
  have count := PEqualNP.Outside.L_meta_3400_aux.Bound3400.total C
  change C.gates.countP costly + PEqualNP.NotBracket.notCount C = C.size at count
  by_contra! small
  have eq : canonicalInputs=PEqualNP.Outside.L_meta_3400_aux.Orbit3400.s0 := by decide +kernel
  rw [eq] at hB
  exact PEqualNP.Outside.L_meta_3400_aux.Orbit3400.compact m (by omega) hB
