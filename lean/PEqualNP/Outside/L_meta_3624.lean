import Mathlib
import PEqualNP.Defs

-- A search over sets of live words, run by the kernel, with lower bounds on vertex-deleted
-- subgraphs used as pruning. The live-set relation follows the one of L-meta-1670.

namespace PEqualNP.Outside.L_meta_3624
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section Vs1


-- words and moves

lemma tb_land (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i
lemma tb_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i
lemma tb_xor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i ^^ y.testBit i) :=
  Nat.testBit_xor x y i
lemma tb_shr (x k i : Nat) : (Nat.shiftRight x k).testBit i = x.testBit (k + i) := by
  have := Nat.testBit_shiftRight (i := k) (j := i) x
  exact this

abbrev Mv := Option Bool × Nat × Nat

def neg (top a : Nat) : Nat := Nat.xor a top
def bin (d : Bool) (a b : Nat) : Nat := cond d (Nat.lor a b) (Nat.land a b)
def res (top : Nat) (m : Mv) : Nat :=
  match m.1 with
  | none => neg top m.2.1
  | some d => bin d m.2.1 m.2.2
def ops (m : Mv) : Finset Nat := {m.2.1, m.2.2}
def good (m : Mv) : Prop :=
  match m.1 with
  | none => m.2.1 = m.2.2
  | some _ => m.2.1 ≠ m.2.2

def Dv (top tgt : Nat) : List Mv → Finset Nat → Finset Nat → Prop
  | [], H, S => S = {tgt} ∧ S ⊆ H
  | m :: ms, H, S => good m ∧ res top m ∉ H ∧ S ⊆ H ∧
      ∃ U, S = ops m ∪ U ∧ Dv top tgt ms (insert (res top m) H) (insert (res top m) U)

def nb (ms : List Mv) : Nat := ms.countP (fun m => m.1.isSome)
def nu (ms : List Mv) : Nat := ms.countP (fun m => m.1.isNone)

lemma nb_nu (ms : List Mv) : nb ms + nu ms = ms.length := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [nb, nu, List.countP_cons, List.length_cons] at ih ⊢
    rcases m with ⟨_ | d, a, b⟩ <;> simp <;> omega

lemma nb_perm {l r : List Mv} (h : l.Perm r) : nb l = nb r := h.countP_eq _
lemma nu_perm {l r : List Mv} (h : l.Perm r) : nu l = nu r := h.countP_eq _

variable {top tgt : Nat}

lemma Dv.sub {ms H S} (h : Dv top tgt ms H S) : S ⊆ H := by
  cases ms with
  | nil => exact h.2
  | cons m ms => exact h.2.2.1

lemma Dv.mono {ms : List Mv} : ∀ {H H' S : Finset Nat}, Dv top tgt ms H' S → H ⊆ H' → S ⊆ H →
    Dv top tgt ms H S := by
  induction ms with
  | nil => intro H H' S h _ hs; exact ⟨h.1, hs⟩
  | cons m ms ih =>
    rintro H H' S ⟨hg, hf, _, U, hU, hd⟩ hH hs
    refine ⟨hg, fun h => hf (hH h), hs, U, hU, ih hd (Finset.insert_subset_insert _ hH) ?_⟩
    apply Finset.insert_subset_insert
    intro x hx; exact hs (by rw [hU]; exact Finset.mem_union_right _ hx)

lemma ops_ne (m : Mv) : m.2.1 ∈ ops m := by simp [ops]

lemma Dv.swap {m1 m2 ms H S} (h : Dv top tgt (m1 :: m2 :: ms) H S) (hn : res top m1 ∉ ops m2) :
    Dv top tgt (m2 :: m1 :: ms) H S := by
  obtain ⟨g1, f1, hs, U1, e1, g2, f2, hs2, U2, e2, hd⟩ := h
  have hU1 : U1 ⊆ H := fun x hx => hs (by rw [e1]; exact Finset.mem_union_right _ hx)
  have z1U : res top m1 ∉ U1 := fun h => f1 (hU1 h)
  have z1U2 : res top m1 ∈ U2 := by
    have : res top m1 ∈ ops m2 ∪ U2 := by rw [← e2]; exact Finset.mem_insert_self _ _
    exact (Finset.mem_union.mp this).resolve_left hn
  have eU1 : U1 = ops m2 ∪ U2.erase (res top m1) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ ops m2 ∪ U2 := by rw [← e2]; exact Finset.mem_insert_of_mem hx
      rcases Finset.mem_union.mp hx' with h | h
      · exact Finset.mem_union_left _ h
      · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, h⟩)
        rintro rfl; exact z1U hx
    · intro hx
      have key : x ≠ res top m1 ∧ x ∈ ops m2 ∪ U2 := by
        rcases Finset.mem_union.mp hx with h | h
        · exact ⟨fun e => hn (e ▸ h), Finset.mem_union_left _ h⟩
        · exact ⟨(Finset.mem_erase.mp h).1, Finset.mem_union_right _ (Finset.mem_erase.mp h).2⟩
      rw [← e2] at key
      exact (Finset.mem_insert.mp key.2).resolve_left key.1
  have f2' : res top m2 ∉ H := fun h => f2 (Finset.mem_insert_of_mem h)
  have z12 : res top m2 ≠ res top m1 := fun h => f2 (by rw [h]; exact Finset.mem_insert_self _ _)
  refine ⟨g2, f2', hs, ops m1 ∪ U2.erase (res top m1), ?_, g1, ?_, ?_,
    insert (res top m2) (U2.erase (res top m1)), ?_, ?_⟩
  · rw [e1, eU1]; ext x; simp only [Finset.mem_union]; tauto
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact z12 h.symm
    · exact f1 h
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rcases Finset.mem_union.mp hx with h | h
      · exact hs (by rw [e1]; exact Finset.mem_union_left _ h)
      · exact hU1 (by rw [eU1]; exact Finset.mem_union_right _ h)
  · ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
  · rw [Finset.insert_comm (res top m1) (res top m2) H]
    have : insert (res top m1) (insert (res top m2) (U2.erase (res top m1))) = insert (res top m2) U2 := by
      rw [Finset.insert_comm, Finset.insert_erase z1U2]
    rw [this]; exact hd

lemma Dv.front {ms : List Mv} : ∀ {H S : Finset Nat} {m : Mv}, Dv top tgt ms H S → m ∈ ms → ops m ⊆ H →
    ∃ ms', Dv top tgt (m :: ms') H S ∧ (m :: ms').Perm ms := by
  induction ms with
  | nil => intro H S m _ hm; simp at hm
  | cons m1 ms ih =>
    intro H S m h hm hop
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact ⟨ms, h, List.Perm.refl _⟩
    obtain ⟨g1, f1, hs, U1, e1, hd⟩ := h
    obtain ⟨ms', hd', hp⟩ := ih hd hm' (hop.trans (Finset.subset_insert _ _))
    refine ⟨m1 :: ms', ?_, ?_⟩
    · apply Dv.swap (m1 := m1)
      · exact ⟨g1, f1, hs, U1, e1, hd'⟩
      · exact fun h => f1 (hop h)
    · exact (List.Perm.swap m1 m ms').trans (hp.cons m1)

lemma ops_card (m : Mv) : (ops m).card ≤ 2 := Finset.card_le_two

lemma Dv.card {ms : List Mv} : ∀ {H S : Finset Nat}, Dv top tgt ms H S → S.card ≤ nb ms + 1 := by
  induction ms with
  | nil => intro H S h; rw [h.1]; simp
  | cons m ms ih =>
    rintro H S ⟨hg, hf, hs, U, e, hd⟩
    have hU : res top m ∉ U := fun h => hf (hs (by rw [e]; exact Finset.mem_union_right _ h))
    have h1 := ih hd
    rw [Finset.card_insert_of_notMem hU] at h1
    have h2 : S.card ≤ (ops m).card + U.card := by rw [e]; exact Finset.card_union_le _ _
    rcases m with ⟨_ | d, a, b⟩
    · have : (ops (none, a, b)).card = 1 := by
        simp only [good] at hg; subst hg; simp [ops]
      simp only [nb, List.countP_cons] at h1 ⊢
      simp at h1 ⊢; omega
    · have := ops_card (some d, a, b)
      simp only [nb, List.countP_cons] at h1 ⊢
      simp at h1 ⊢; omega

-- separation

def sep (full : Nat) (d : Bool) (a : Nat) : Nat :=
  @Bool.rec (fun _ => Nat) (Nat.land (Nat.xor a (Nat.land a (Nat.shiftRight a 402))) full)
    (Nat.land (Nat.xor a (Nat.shiftRight a 402)) full) d

lemma sep_bit (full : Nat) (d : Bool) (a i : Nat) (hi : full.testBit i = true) :
    (sep full d a).testBit i =
      (if d then (a.testBit i ^^ a.testBit (402 + i)) else (a.testBit i && !(a.testBit (402 + i)))) := by
  cases d <;> simp only [sep, tb_land, tb_xor, tb_shr, hi, Bool.and_true] <;>
    cases a.testBit i <;> cases a.testBit (402 + i) <;> rfl

lemma sep_bit_off (full : Nat) (d : Bool) (a i : Nat) (hi : full.testBit i = false) :
    (sep full d a).testBit i = false := by
  cases d <;> simp [sep, tb_land, hi]

-- constants of one problem
structure Gd (top full tgt : Nat) : Prop where
  t1 : ∀ i, full.testBit i = true → top.testBit i = true
  t2 : ∀ i, full.testBit i = true → top.testBit (402 + i) = true
  p1 : ∀ i, full.testBit i = true → tgt.testBit i = true
  p2 : ∀ i, full.testBit i = true → tgt.testBit (402 + i) = false

lemma Dv.sep {full : Nat} (g : Gd top full tgt) {ms : List Mv} : ∀ {H S : Finset Nat},
    Dv top tgt ms H S → ∀ i, full.testBit i = true →
    ∃ a ∈ S, (sep full (decide (1 ≤ nu ms)) a).testBit i = true := by
  induction ms with
  | nil =>
    intro H S h i hi
    refine ⟨tgt, by rw [h.1]; simp, ?_⟩
    rw [sep_bit _ _ _ _ hi, g.p1 i hi, g.p2 i hi]; simp [nu]
  | cons m ms ih =>
    rintro H S ⟨hg, hf, hs, U, e, hd⟩ i hi
    obtain ⟨x, hx, hb⟩ := ih hd i hi
    rw [sep_bit _ _ _ _ hi] at hb
    have up : ∀ y ∈ S, (if decide (1 ≤ nu ms) = true then (y.testBit i ^^ y.testBit (402 + i))
        else (y.testBit i && !(y.testBit (402 + i)))) = true →
        ∃ a ∈ S, (PEqualNP.Outside.L_meta_3624.sep full (decide (1 ≤ nu (m :: ms))) a).testBit i = true := by
      intro y hy hb
      refine ⟨y, hy, ?_⟩
      rw [sep_bit _ _ _ _ hi]
      by_cases h : 1 ≤ nu ms
      · have h' : 1 ≤ nu (m :: ms) := by simp only [nu, List.countP_cons] at h ⊢; omega
        simpa [h, h'] using hb
      · by_cases h' : 1 ≤ nu (m :: ms)
        · simp only [h, h', decide_true, decide_false] at hb ⊢
          revert hb; cases y.testBit i <;> cases y.testBit (402 + i) <;> simp
        · simpa [h, h'] using hb
    rcases Finset.mem_insert.mp hx with rfl | hU
    · have hop1 : m.2.1 ∈ S := by rw [e]; exact Finset.mem_union_left _ (by simp [ops])
      have hop2 : m.2.2 ∈ S := by rw [e]; exact Finset.mem_union_left _ (by simp [ops])
      rcases m with ⟨_ | d, a, b⟩
      · refine ⟨a, hop1, ?_⟩
        rw [sep_bit _ _ _ _ hi]
        have h' : 1 ≤ nu ((none, a, b) :: ms) := by simp [nu]
        simp only [h', decide_true, if_true]
        simp only [res, neg, tb_xor, g.t1 i hi, g.t2 i hi] at hb
        revert hb
        cases a.testBit i <;> cases a.testBit (402 + i) <;> simp
      · have : (if decide (1 ≤ nu ms) = true then (a.testBit i ^^ a.testBit (402 + i))
            else (a.testBit i && !(a.testBit (402 + i)))) = true ∨
            (if decide (1 ≤ nu ms) = true then (b.testBit i ^^ b.testBit (402 + i))
            else (b.testBit i && !(b.testBit (402 + i)))) = true := by
          revert hb
          cases d <;> simp only [res, bin, cond_true, cond_false, tb_land, tb_lor] <;>
            by_cases h : 1 ≤ nu ms <;> simp only [h, decide_true, decide_false] <;>
            cases a.testBit i <;> cases a.testBit (402 + i) <;> cases b.testBit i <;>
            cases b.testBit (402 + i) <;> simp
        rcases this with h | h
        · exact up a hop1 h
        · exact up b hop2 h
    · exact up x (by rw [e]; exact Finset.mem_union_right _ hU) hb

-- circuits run on words

def gv (top : Nat) (w : List Nat) (g : Gate) : Nat :=
  let xs := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => xs.foldr Nat.land top
  | .or => xs.foldr Nat.lor 0
  | .not => neg top (xs.headD 0)
  | _ => 0
def exec (top : Nat) (gs : List Gate) (w : List Nat) : List Nat :=
  gs.foldl (fun l g => l ++ [gv top l g]) w
def legal (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
def Val (top a : Nat) : Prop := ∀ j, a.testBit j = true → top.testBit j = true

lemma exec_cons (g : Gate) (gs : List Gate) (w : List Nat) :
    exec top (g :: gs) w = exec top gs (w ++ [gv top w g]) := rfl
lemma exec_append (gs gs' : List Gate) (w : List Nat) :
    exec top (gs ++ gs') w = exec top gs' (exec top gs w) := by simp [exec]
lemma exec_sub (gs : List Gate) : ∀ (w : List Nat), ∀ a ∈ w, a ∈ exec top gs w := by
  induction gs with
  | nil => intro w a h; exact h
  | cons g gs ih => intro w a h; rw [exec_cons]; exact ih _ a (by simp [h])

lemma val_zero : Val top 0 := fun j h => by simp at h
lemma val_top : Val top top := fun _ h => h
lemma val_land {a b : Nat} (ha : Val top a) : Val top (Nat.land a b) := fun j h => by
  rw [tb_land, Bool.and_eq_true] at h; exact ha j h.1
lemma val_lor {a b : Nat} (ha : Val top a) (hb : Val top b) : Val top (Nat.lor a b) := fun j h => by
  rw [tb_lor, Bool.or_eq_true] at h; exact h.elim (ha j) (hb j)
lemma val_neg {a : Nat} (ha : Val top a) : Val top (neg top a) := fun j h => by
  rw [neg, tb_xor] at h
  by_contra hn
  have h1 : a.testBit j = false := by
    by_contra h2; exact hn (ha j (by simpa using h2))
  simp [h1, hn] at h
lemma val_getD {w : List Nat} (hw : ∀ a ∈ w, Val top a) (i : Nat) : Val top (w.getD i 0) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact val_zero
  | some a => exact hw a (List.mem_of_getElem? h)

lemma land_top {a : Nat} (ha : Val top a) : Nat.land a top = a := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [tb_land]
  cases h : a.testBit j
  · rfl
  · simp [ha j h]
lemma top_land {a : Nat} (ha : Val top a) : Nat.land top a = a := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [tb_land]
  cases h : a.testBit j
  · simp
  · simp [ha j h]
lemma lor_zero (a : Nat) : Nat.lor a 0 = a := by
  apply Nat.eq_of_testBit_eq; intro j; simp [tb_lor]
lemma zero_lor (a : Nat) : Nat.lor 0 a = a := by
  apply Nat.eq_of_testBit_eq; intro j; simp [tb_lor]
lemma land_zero (a : Nat) : Nat.land a 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; simp [tb_land]
lemma zero_land (a : Nat) : Nat.land 0 a = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; simp [tb_land]
lemma lor_top {a : Nat} (ha : Val top a) : Nat.lor a top = top := by
  apply Nat.eq_of_testBit_eq; intro j; rw [tb_lor]
  cases h : a.testBit j
  · simp
  · simp [ha j h]
lemma top_lor {a : Nat} (ha : Val top a) : Nat.lor top a = top := by
  apply Nat.eq_of_testBit_eq; intro j; rw [tb_lor]
  cases h : a.testBit j
  · simp
  · simp [ha j h]
lemma land_self (a : Nat) : Nat.land a a = a := by
  apply Nat.eq_of_testBit_eq; intro j; simp [tb_land]
lemma lor_self (a : Nat) : Nat.lor a a = a := by
  apply Nat.eq_of_testBit_eq; intro j; simp [tb_lor]
lemma neg_zero : neg top 0 = top := by
  apply Nat.eq_of_testBit_eq; intro j; simp [neg, tb_xor]
lemma neg_top : neg top top = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; simp [neg, tb_xor]

lemma gv_val {w : List Nat} (hw : ∀ a ∈ w, Val top a) (g : Gate) : Val top (gv top w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Val top ((l.map (fun i => w.getD i 0)).foldr Nat.land top)
    induction l with
    | nil => exact val_top
    | cons i l ih => exact val_land (val_getD hw i)
  | or =>
    change Val top ((l.map (fun i => w.getD i 0)).foldr Nat.lor 0)
    induction l with
    | nil => exact val_zero
    | cons i l ih => exact val_lor (val_getD hw i) ih
  | not =>
    cases l with
    | nil => exact val_neg val_zero
    | cons i _ => exact val_neg (val_getD hw i)
  | mod _ => exact val_zero
  | maj => exact val_zero

def Hof (top : Nat) (w : List Nat) : Finset Nat := insert 0 (insert top w.toFinset)
def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

lemma mem_Hof {w : List Nat} {a : Nat} : a ∈ Hof top w ↔ a = 0 ∨ a = top ∨ a ∈ w := by
  simp [Hof]

lemma getD_cases (w : List Nat) (i : Nat) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_of_getElem? h)

lemma opd {w : List Nat} (i : Nat) (h0 : w.getD i 0 ≠ 0) : w.getD i 0 ∈ w :=
  (getD_cases w i).resolve_left h0

lemma witness {w : List Nat} (hw : ∀ a ∈ w, Val top a) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hz : gv top w g ∉ Hof top w) :
    ∃ m : Mv, good m ∧ res top m = gv top w g ∧ m.1.isNone = isNot g ∧
      ∀ a ∈ ops m, a ∈ w ∧ a ≠ 0 ∧ a ≠ top := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  obtain ⟨ho, hl⟩ := hg
  rw [mem_Hof] at hz
  push Not at hz
  obtain ⟨z0, zt, zw⟩ := hz
  have notc : ∀ i : Nat, o = .not → gv top w ⟨o, l⟩ = neg top (w.getD i 0) →
      ∃ m : Mv, good m ∧ res top m = gv top w ⟨o, l⟩ ∧ m.1.isNone = isNot ⟨o, l⟩ ∧
      ∀ a ∈ ops m, a ∈ w ∧ a ≠ 0 ∧ a ≠ top := by
    intro i ho h
    have h0 : w.getD i 0 ≠ 0 := fun e => by rw [h, e, neg_zero] at zt; exact zt rfl
    have h1 : w.getD i 0 ≠ top := fun e => by rw [h, e, neg_top] at z0; exact z0 rfl
    refine ⟨(none, w.getD i 0, w.getD i 0), rfl, h.symm, by subst ho; rfl, ?_⟩
    intro a ha; simp only [ops, Finset.mem_insert, Finset.mem_singleton, or_self] at ha
    subst ha; exact ⟨opd i h0, h0, h1⟩
  have binc : ∀ (d : Bool) (i j : Nat), o = cond d .or .and →
      gv top w ⟨o, l⟩ = bin d (w.getD i 0) (w.getD j 0) →
      ∃ m : Mv, good m ∧ res top m = gv top w ⟨o, l⟩ ∧ m.1.isNone = isNot ⟨o, l⟩ ∧
      ∀ a ∈ ops m, a ∈ w ∧ a ≠ 0 ∧ a ≠ top := by
    intro d i j ho h
    have vi := val_getD hw i
    have vj := val_getD hw j
    have hne : w.getD i 0 ≠ w.getD j 0 := by
      intro e
      have hh : gv top w ⟨o, l⟩ = w.getD i 0 := by
        rw [h, ← e]; cases d
        · exact land_self _
        · exact lor_self _
      rcases getD_cases w i with h' | h'
      · exact z0 (hh.trans h')
      · exact zw (hh ▸ h')
    have hi0 : w.getD i 0 ≠ 0 := by
      intro e; rw [e] at h
      cases d
      · exact z0 (h.trans (zero_land _))
      · have hh := h.trans (zero_lor _)
        rcases getD_cases w j with h' | h'
        · exact z0 (hh.trans h')
        · exact zw (hh ▸ h')
    have hj0 : w.getD j 0 ≠ 0 := by
      intro e; rw [e] at h
      cases d
      · exact z0 (h.trans (land_zero _))
      · have hh := h.trans (lor_zero _)
        rcases getD_cases w i with h' | h'
        · exact z0 (hh.trans h')
        · exact zw (hh ▸ h')
    have hi1 : w.getD i 0 ≠ top := by
      intro e; rw [e] at h
      cases d
      · have hh := h.trans (top_land vj); exact zw (hh ▸ opd j hj0)
      · exact zt (h.trans (top_lor vj))
    have hj1 : w.getD j 0 ≠ top := by
      intro e; rw [e] at h
      cases d
      · have hh := h.trans (land_top vi); exact zw (hh ▸ opd i hi0)
      · exact zt (h.trans (lor_top vi))
    refine ⟨(some d, w.getD i 0, w.getD j 0), hne, h.symm, by subst ho; cases d <;> rfl, ?_⟩
    intro a ha; simp only [ops, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨opd i hi0, hi0, hi1⟩
    · exact ⟨opd j hj0, hj0, hj1⟩
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
  · rcases ho with rfl | rfl | rfl
    · exact absurd rfl zt
    · exact absurd rfl z0
    · exact absurd (neg_zero (top := top)) zt
  · rcases ho with rfl | rfl | rfl
    · have hh : gv top w ⟨.and, [i]⟩ = w.getD i 0 := land_top (val_getD hw i)
      rcases getD_cases w i with h' | h'
      · exact absurd (hh.trans h') z0
      · exact absurd (hh ▸ h') zw
    · have hh : gv top w ⟨.or, [i]⟩ = w.getD i 0 := lor_zero _
      rcases getD_cases w i with h' | h'
      · exact absurd (hh.trans h') z0
      · exact absurd (hh ▸ h') zw
    · exact notc i rfl rfl
  · rcases ho with rfl | rfl | rfl
    · refine binc false i j rfl ?_
      change Nat.land _ (Nat.land _ top) = Nat.land _ _
      rw [land_top (val_getD hw j)]
    · refine binc true i j rfl ?_
      change Nat.lor _ (Nat.lor _ 0) = Nat.lor _ _
      rw [lor_zero]
    · exact notc i rfl rfl
  · simp at hl

lemma extract (h0 : tgt ≠ 0) (h1 : tgt ≠ top) (gs : List Gate) : ∀ (w : List Nat),
    (∀ a ∈ w, Val top a) → legal gs → tgt ∈ exec top gs w →
    ∃ ms S, Dv top tgt ms (Hof top w) S ∧ (∀ a ∈ S, a ∈ w ∧ a ≠ 0 ∧ a ≠ top) ∧
      nb ms ≤ gs.countP (fun g => !isNot g) ∧ nu ms ≤ gs.countP isNot := by
  induction gs with
  | nil =>
    intro w _ _ ht
    have ht' : tgt ∈ w := ht
    refine ⟨[], {tgt}, ⟨rfl, ?_⟩, ?_, by simp [nb], by simp [nu]⟩
    · intro a ha; rw [Finset.mem_singleton] at ha; subst ha; rw [mem_Hof]; exact Or.inr (Or.inr ht')
    · intro a ha; rw [Finset.mem_singleton] at ha; subst ha; exact ⟨ht', h0, h1⟩
  | cons g gs ih =>
    intro w hw hl ht
    have hw' : ∀ a ∈ w ++ [gv top w g], Val top a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · rw [List.mem_singleton] at ha; exact ha ▸ gv_val hw g
    obtain ⟨ms, S, hd, hS, hb, hn⟩ := ih _ hw' (fun a ha => hl a (by simp [ha])) ht
    have cb : gs.countP (fun g => !isNot g) ≤ (g :: gs).countP (fun g => !isNot g) := by
      rw [List.countP_cons]; omega
    have cn : gs.countP isNot ≤ (g :: gs).countP isNot := by rw [List.countP_cons]; omega
    have hsub : Hof top w ⊆ Hof top (w ++ [gv top w g]) := by
      intro a ha; rw [mem_Hof] at ha ⊢; simp; tauto
    by_cases hz : gv top w g ∈ Hof top w
    · have hS' : ∀ a ∈ S, a ∈ w ∧ a ≠ 0 ∧ a ≠ top := by
        intro a ha
        obtain ⟨h1, h2, h3⟩ := hS a ha
        refine ⟨?_, h2, h3⟩
        rcases List.mem_append.mp h1 with h | h
        · exact h
        · rw [List.mem_singleton] at h; subst h
          rw [mem_Hof] at hz; tauto
      refine ⟨ms, S, hd.mono hsub ?_, hS', hb.trans cb, hn.trans cn⟩
      intro a ha; rw [mem_Hof]; exact Or.inr (Or.inr (hS' a ha).1)
    · obtain ⟨m, hg, hr, hk, hop⟩ := witness hw g (hl g (by simp)) hz
      have hH : Hof top (w ++ [gv top w g]) = insert (res top m) (Hof top w) := by
        ext a; rw [Finset.mem_insert, mem_Hof, mem_Hof, hr]; simp; tauto
      by_cases hzS : gv top w g ∈ S
      · refine ⟨m :: ms, ops m ∪ S.erase (gv top w g), ⟨hg, hr ▸ hz, ?_, _, rfl, ?_⟩, ?_, ?_, ?_⟩
        · intro a ha
          rw [mem_Hof]
          rcases Finset.mem_union.mp ha with h | h
          · exact Or.inr (Or.inr (hop a h).1)
          · obtain ⟨h1, h2⟩ := Finset.mem_erase.mp h
            have := (hS a h2).1
            simp [h1] at this
            exact Or.inr (Or.inr this)
        · rw [← hH, hr, Finset.insert_erase hzS]; exact hd
        · intro a ha
          rcases Finset.mem_union.mp ha with h | h
          · exact hop a h
          · obtain ⟨h1, h2⟩ := Finset.mem_erase.mp h
            obtain ⟨h3, h4, h5⟩ := hS a h2
            simp [h1] at h3
            exact ⟨h3, h4, h5⟩
        · simp only [nb, List.countP_cons] at hb ⊢
          have : m.1.isSome = !isNot g := by rw [← hk]; cases m.1 <;> rfl
          rw [this]; omega
        · simp only [nu, List.countP_cons] at hn ⊢
          rw [hk]; omega
      · have hS' : ∀ a ∈ S, a ∈ w ∧ a ≠ 0 ∧ a ≠ top := by
          intro a ha
          obtain ⟨h1, h2, h3⟩ := hS a ha
          refine ⟨?_, h2, h3⟩
          rcases List.mem_append.mp h1 with h | h
          · exact h
          · rw [List.mem_singleton] at h; subst h; exact absurd ha hzS
        refine ⟨ms, S, hd.mono hsub ?_, hS', hb.trans cb, hn.trans cn⟩
        intro a ha; rw [mem_Hof]; exact Or.inr (Or.inr (hS' a ha).1)


end Vs1

section Vs2
variable {top tgt : Nat}

-- feasibility under a restriction mask

def eqM (μ a b : Nat) : Prop := ∀ j, μ.testBit j = true → a.testBit j = b.testBit j
def zM (μ a : Nat) : Prop := ∀ j, μ.testBit j = true → a.testBit j = false
def oM (μ a : Nat) : Prop := ∀ j, μ.testBit j = true → a.testBit j = true
def conM (μ a : Nat) : Prop := zM μ a ∨ oM μ a

def Feas (top tgt μ q : Nat) (S : Finset Nat) : Prop :=
  ∀ w : List Nat, (∀ a ∈ S, conM μ a ∨ ∃ b ∈ w, eqM μ b a) →
    ∃ gs, legal gs ∧ gs.length ≤ q ∧ ∃ b ∈ exec top gs w, eqM μ b tgt

structure Msk (top tgt μ : Nat) : Prop where
  sub : ∀ j, μ.testBit j = true → top.testBit j = true
  tg : ¬ conM μ tgt

lemma Feas.mono {μ q q' S S'} (h : Feas top tgt μ q S) (hq : q ≤ q') (hS : S ⊆ S') :
    Feas top tgt μ q' S' := by
  intro w hw
  obtain ⟨gs, hl, hn, hb⟩ := h w (fun a ha => hw a (hS ha))
  exact ⟨gs, hl, hn.trans hq, hb⟩

lemma exec_get_not (w : List Nat) (i : Nat) :
    exec top [⟨GateOp.not, [i]⟩] w = w ++ [neg top (w.getD i 0)] := rfl

lemma mem_getD {w : List Nat} {b : Nat} (h : b ∈ w) : ∃ i, w.getD i 0 = b := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
  exact ⟨i, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact e⟩

lemma oneGate {μ : Nat} (hm : ∀ j, μ.testBit j = true → top.testBit j = true) (m : Mv) (w : List Nat)
    (h1 : conM μ m.2.1 ∨ ∃ b ∈ w, eqM μ b m.2.1) (h2 : conM μ m.2.2 ∨ ∃ b ∈ w, eqM μ b m.2.2) :
    ∃ gs, legal gs ∧ gs.length ≤ 1 ∧ (∀ a ∈ w, a ∈ exec top gs w) ∧
      (conM μ (res top m) ∨ ∃ b ∈ exec top gs w, eqM μ b (res top m)) := by
  have nil : (conM μ (res top m) ∨ ∃ b ∈ w, eqM μ b (res top m)) →
      ∃ gs, legal gs ∧ gs.length ≤ 1 ∧ (∀ a ∈ w, a ∈ exec top gs w) ∧
      (conM μ (res top m) ∨ ∃ b ∈ exec top gs w, eqM μ b (res top m)) :=
    fun h => ⟨[], by simp [legal], by simp, fun a ha => ha, h⟩
  rcases m with ⟨_ | d, a, b⟩
  · rcases h1 with h | ⟨x, hx, hxa⟩
    · apply nil; left
      rcases h with h | h
      · right; intro j hj; simp [res, neg, tb_xor, h j hj, hm j hj]
      · left; intro j hj; simp only [res, neg, tb_xor]; rw [h j hj, hm j hj]; rfl
    · obtain ⟨i, hi⟩ := mem_getD hx
      refine ⟨[⟨.not, [i]⟩], ?_, by simp, ?_, Or.inr ⟨neg top x, ?_, ?_⟩⟩
      · intro g hg; simp at hg; subst hg; simp
      · intro y hy; exact exec_sub _ _ y hy
      · rw [exec_get_not, hi]; simp
      · intro j hj; simp only [res, neg, tb_xor, hxa j hj]
  · have side : ∀ (u v : Nat), conM μ u → (conM μ v ∨ ∃ b ∈ w, eqM μ b v) →
        (∀ j, (bin d a b).testBit j = (bin d u v).testBit j) →
        (conM μ (res top (some d, a, b)) ∨ ∃ y ∈ w, eqM μ y (res top (some d, a, b))) := by
      intro u v hu hv e
      have e' : ∀ j, (res top (some d, a, b)).testBit j = (bin d u v).testBit j := e
      cases d <;> simp only [bin, Bool.cond_true, Bool.cond_false, tb_land, tb_lor] at e' <;>
        rcases hu with hu | hu
      · left; left; intro j hj; rw [e', hu j hj]; rfl
      · rcases hv with hv | ⟨y, hy, hv⟩
        · left
          rcases hv with hv | hv
          · left; intro j hj; rw [e', hv j hj]; simp
          · right; intro j hj; rw [e', hv j hj, hu j hj]; rfl
        · right; exact ⟨y, hy, fun j hj => by rw [e', hu j hj, hv j hj]; simp⟩
      · rcases hv with hv | ⟨y, hy, hv⟩
        · left
          rcases hv with hv | hv
          · left; intro j hj; rw [e', hv j hj, hu j hj]; rfl
          · right; intro j hj; rw [e', hv j hj]; simp
        · right; exact ⟨y, hy, fun j hj => by rw [e', hu j hj, hv j hj]; simp⟩
      · left; right; intro j hj; rw [e', hu j hj]; rfl
    rcases h1 with h1 | ⟨x, hx, hxa⟩
    · exact nil (side a b h1 h2 (fun _ => rfl))
    rcases h2 with h2 | ⟨y, hy, hyb⟩
    · exact nil (side b a h2 (Or.inr ⟨x, hx, hxa⟩) (fun j => by
        cases d <;> simp only [bin, Bool.cond_true, Bool.cond_false, tb_land, tb_lor]
        · exact Bool.and_comm _ _
        · exact Bool.or_comm _ _))
    obtain ⟨i, hi⟩ := mem_getD hx
    obtain ⟨k, hk⟩ := mem_getD hy
    cases d
    · refine ⟨[⟨.and, [i, k]⟩], ?_, by simp, ?_, Or.inr ⟨Nat.land x (Nat.land y top), ?_, ?_⟩⟩
      · intro g hg; simp at hg; subst hg; simp
      · intro y hy; exact exec_sub _ _ y hy
      · have : exec top [⟨GateOp.and, [i, k]⟩] w =
            w ++ [Nat.land (w.getD i 0) (Nat.land (w.getD k 0) top)] := rfl
        rw [this, hi, hk]; simp
      · intro j hj
        simp only [res, bin, Bool.cond_false, tb_land, hxa j hj, hyb j hj, hm j hj, Bool.and_true]
    · refine ⟨[⟨.or, [i, k]⟩], ?_, by simp, ?_, Or.inr ⟨Nat.lor x (Nat.lor y 0), ?_, ?_⟩⟩
      · intro g hg; simp at hg; subst hg; simp
      · intro y hy; exact exec_sub _ _ y hy
      · have : exec top [⟨GateOp.or, [i, k]⟩] w =
            w ++ [Nat.lor (w.getD i 0) (Nat.lor (w.getD k 0) 0)] := rfl
        rw [this, hi, hk]; simp
      · intro j hj
        simp only [res, bin, Bool.cond_true, tb_lor, hxa j hj, hyb j hj]; simp

lemma Feas.pull {μ q : Nat} (hm : ∀ j, μ.testBit j = true → top.testBit j = true) {m : Mv} {U : Finset Nat}
    (h : Feas top tgt μ q (insert (res top m) U)) : Feas top tgt μ (q + 1) (ops m ∪ U) := by
  intro w hw
  obtain ⟨g1, l1, n1, s1, r1⟩ := oneGate hm m w (hw _ (Finset.mem_union_left _ (by simp [ops])))
    (hw _ (Finset.mem_union_left _ (by simp [ops])))
  obtain ⟨gs, l2, n2, r2⟩ := h (exec top g1 w) (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact r1
    · rcases hw a (Finset.mem_union_right _ ha) with h | ⟨b, hb, e⟩
      · exact Or.inl h
      · exact Or.inr ⟨b, s1 b hb, e⟩)
  refine ⟨g1 ++ gs, ?_, by simp; omega, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact l1 g h
    · exact l2 g h
  · rw [exec_append]; exact r2

lemma Feas.free {μ q z : Nat} {S U : Finset Nat} (h : Feas top tgt μ q (insert z U)) (hU : U ⊆ S)
    (hz : conM μ z ∨ ∃ s ∈ S, eqM μ s z) : Feas top tgt μ q S := by
  intro w hw
  apply h w
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · rcases hz with hz | ⟨s, hs, e⟩
    · exact Or.inl hz
    · rcases hw s hs with h | ⟨b, hb, e'⟩
      · left
        rcases h with h | h
        · left; intro j hj; rw [← e j hj]; exact h j hj
        · right; intro j hj; rw [← e j hj]; exact h j hj
      · exact Or.inr ⟨b, hb, fun j hj => (e' j hj).trans (e j hj)⟩
  · exact hw a (hU ha)

-- an operand that is constant under the mask makes the gate free
lemma freeOp {μ : Nat} (hm : ∀ j, μ.testBit j = true → top.testBit j = true) (m : Mv) (a : Nat)
    (ha : a ∈ ops m) (hc : conM μ a) (hg : good m) :
    conM μ (res top m) ∨ ∃ s ∈ ops m, eqM μ s (res top m) := by
  rcases m with ⟨_ | d, x, y⟩
  · simp only [good] at hg; subst hg
    simp only [ops, Finset.mem_insert, Finset.mem_singleton, or_self] at ha; subst ha
    left
    rcases hc with h | h
    · right; intro j hj; simp [res, neg, tb_xor, h j hj, hm j hj]
    · left; intro j hj; simp only [res, neg, tb_xor]; rw [h j hj, hm j hj]; rfl
  · simp only [ops, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> cases d <;> rcases hc with h | h
    · left; left; intro j hj; simp [res, bin, tb_land, h j hj]
    · right; exact ⟨y, by simp [ops], fun j hj => by simp [res, bin, tb_land, h j hj]⟩
    · right; exact ⟨y, by simp [ops], fun j hj => by simp [res, bin, tb_lor, h j hj]⟩
    · left; right; intro j hj; simp [res, bin, tb_lor, h j hj]
    · left; left; intro j hj; simp [res, bin, tb_land, h j hj]
    · right; exact ⟨x, by simp [ops], fun j hj => by simp [res, bin, tb_land, h j hj]⟩
    · right; exact ⟨x, by simp [ops], fun j hj => by simp [res, bin, tb_lor, h j hj]⟩
    · left; right; intro j hj; simp [res, bin, tb_lor, h j hj]

open Classical in
noncomputable def cN (μ : Nat) (S : Finset Nat) : Nat := (S.filter (fun a => conM μ a)).card

lemma cN_union (μ : Nat) (A B : Finset Nat) : cN μ (A ∪ B) ≤ cN μ A + cN μ B := by
  classical
  unfold cN; rw [Finset.filter_union]; exact Finset.card_union_le _ _
lemma cN_insert (μ z : Nat) (U : Finset Nat) (hz : z ∉ U) (hc : conM μ z) :
    cN μ (insert z U) = cN μ U + 1 := by
  classical
  unfold cN; rw [Finset.filter_insert, if_pos hc, Finset.card_insert_of_notMem]
  simp [hz]
lemma cN_insert' (μ z : Nat) (U : Finset Nat) (hc : ¬ conM μ z) :
    cN μ (insert z U) = cN μ U := by
  classical
  unfold cN; rw [Finset.filter_insert, if_neg hc]
lemma cN_ops_le (μ : Nat) (m : Mv) : cN μ (ops m) ≤ 2 := by
  classical
  exact (Finset.card_filter_le _ _).trans (ops_card m)
lemma cN_ops_zero (μ : Nat) (m : Mv) (h : ∀ a ∈ ops m, ¬ conM μ a) : cN μ (ops m) = 0 := by
  classical
  unfold cN; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun a ha => h a ha

lemma cN_free_le (μ : Nat) (hm : ∀ j, μ.testBit j = true → top.testBit j = true) (m : Mv)
    (hz : ¬ conM μ (res top m)) : cN μ (ops m) ≤ 1 := by
  classical
  by_contra hn
  have h2 : cN μ (ops m) = 2 := by have := cN_ops_le μ m; omega
  have hall : ∀ a ∈ ops m, conM μ a := by
    intro a ha
    by_contra hc
    have : cN μ (ops m) < (ops m).card := by
      unfold cN; apply Finset.card_lt_card
      refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
      exact hc (Finset.mem_filter.mp (h ha)).2
    have := ops_card m; omega
  apply hz
  rcases m with ⟨_ | d, x, y⟩
  · rcases hall x (by simp [ops]) with h | h
    · right; intro j hj; simp [res, neg, tb_xor, h j hj, hm j hj]
    · left; intro j hj; simp only [res, neg, tb_xor]; rw [h j hj, hm j hj]; rfl
  · have hx := hall x (by simp [ops])
    have hy := hall y (by simp [ops])
    cases d <;> rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      first
      | (left; intro j hj; simp [res, bin, tb_land, tb_lor, hx j hj, hy j hj]; done)
      | (right; intro j hj; simp [res, bin, tb_land, tb_lor, hx j hj, hy j hj]; done)

lemma Dv.feas {μ : Nat} (hμ : Msk top tgt μ) {ms : List Mv} : ∀ {H S : Finset Nat},
    Dv top tgt ms H S → cN μ S ≤ ms.length ∧ ∀ q, ms.length ≤ q + cN μ S → Feas top tgt μ q S := by
  induction ms with
  | nil =>
    intro H S h
    have hc : cN μ S = 0 := by
      classical
      rw [h.1]; unfold cN; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a ha; rw [Finset.mem_singleton] at ha; subst ha; exact hμ.tg
    refine ⟨by rw [hc]; simp, fun q _ w hw => ?_⟩
    rcases hw tgt (by rw [h.1]; simp) with h | ⟨b, hb, e⟩
    · exact absurd h hμ.tg
    · exact ⟨[], by simp [legal], by simp, b, hb, e⟩
  | cons m ms ih =>
    rintro H S ⟨hg, hf, hs, U, e, hd⟩
    obtain ⟨ih1, ih2⟩ := ih hd
    have hU : res top m ∉ U := fun h => hf (hs (by rw [e]; exact Finset.mem_union_right _ h))
    have hcS : cN μ S ≤ cN μ (ops m) + cN μ U := by rw [e]; exact cN_union _ _ _
    have hUS : U ⊆ S := by rw [e]; exact Finset.subset_union_right
    have hoS : ops m ⊆ S := by rw [e]; exact Finset.subset_union_left
    rw [List.length_cons]
    by_cases hz : conM μ (res top m)
    · rw [cN_insert μ _ U hU hz] at ih1 ih2
      have h2 := cN_ops_le μ m
      exact ⟨by omega, fun q hq => (ih2 q (by omega)).free hUS (Or.inl hz)⟩
    · rw [cN_insert' μ _ U hz] at ih1 ih2
      by_cases hc : ∃ a ∈ ops m, conM μ a
      · obtain ⟨a, ha, hc⟩ := hc
        have h1 := cN_free_le μ hμ.sub m hz
        refine ⟨by omega, fun q hq => (ih2 q (by omega)).free hUS ?_⟩
        rcases freeOp hμ.sub m a ha hc hg with h | ⟨s, hs, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, hoS hs, h⟩
      · push Not at hc
        have h0 := cN_ops_zero μ m hc
        refine ⟨by omega, fun q hq => ?_⟩
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        rw [e]; exact (ih2 q' (by omega)).pull hμ.sub

def LB (top tgt μ L : Nat) (S : Finset Nat) : Prop := ∀ q, Feas top tgt μ q S → L ≤ q

lemma LB.mono {μ L S S'} (h : LB top tgt μ L S) (hS : S' ⊆ S) : LB top tgt μ L S' :=
  fun q hq => h q (hq.mono le_rfl hS)
lemma LB.step {μ L : Nat} {m : Mv} {U : Finset Nat} (hm : ∀ j, μ.testBit j = true → top.testBit j = true)
    (h : LB top tgt μ L (ops m ∪ U)) : LB top tgt μ (L - 1) (insert (res top m) U) := by
  intro q hq; have := h _ (hq.pull hm); omega
lemma LB.stepFree {μ L : Nat} {m : Mv} {U : Finset Nat} (hm : ∀ j, μ.testBit j = true → top.testBit j = true)
    (h : LB top tgt μ L (ops m ∪ U)) (hg : good m) (hc : ∃ a ∈ ops m, conM μ a) :
    LB top tgt μ L (insert (res top m) U) := by
  intro q hq
  obtain ⟨a, ha, hc⟩ := hc
  apply h
  apply hq.free Finset.subset_union_right
  rcases freeOp hm m a ha hc hg with h | ⟨s, hs, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, Finset.mem_union_left _ hs, h⟩
lemma LB.len {μ L : Nat} {ms H S} (hμ : Msk top tgt μ) (h : LB top tgt μ L S) (hd : Dv top tgt ms H S) :
    L + cN μ S ≤ ms.length := by
  obtain ⟨h1, h2⟩ := hd.feas hμ
  have := h _ (h2 (ms.length - cN μ S) (by omega))
  omega


end Vs2

-- the search, written with recursors so that the kernel runs it quickly

structure Par where
  top : Nat
  full : Nat
  tgt : Nat
  bias : Nat
structure El where
  a : Nat
  s : Nat
  zf : Nat
  of : Nat
  f : Nat
  u : Nat
section Sec3
noncomputable def force (n : Nat) (f : Nat → Bool) : Bool :=
  @Nat.rec (fun _ => Bool) (f 0) (fun m _ => f (Nat.succ m)) n
noncomputable def has (z : Nat) (l : List El) : Bool :=
  @List.rec El (fun _ => Bool) false (fun e _ ih => (@Bool.rec (fun _ => Bool) (ih) true (Nat.beq e.a z))) l
noncomputable def sufOf (l : List El) : Nat :=
  @List.rec El (fun _ => Nat) 0 (fun e _ _ => Nat.lor e.s e.f) l
noncomputable def buildK (l : List El) : (List El → Bool) → Bool :=
  @List.rec El (fun _ => (List El → Bool) → Bool) (fun k => k [])
    (fun a _ ih k => ih fun r => force (sufOf r) fun u => k (⟨a.a, a.s, a.zf, a.of, u, 0⟩ :: r)) l
noncomputable def uniqK (l : List El) : Nat → (List El → Bool) → Bool :=
  @List.rec El (fun _ => Nat → (List El → Bool) → Bool) (fun _ k => k [])
    (fun e _ ih acc k => force (Nat.xor e.s (Nat.land e.s (Nat.lor acc e.f))) fun u =>
      force (Nat.lor acc e.s) fun acc' => ih acc' fun r => k (⟨e.a, e.s, e.zf, e.of, e.f, u⟩ :: r)) l
noncomputable def appK (a : List El) : List El → (List El → Bool) → Bool :=
  @List.rec El (fun _ => List El → (List El → Bool) → Bool) (fun l k => k l)
    (fun x _ ih l k => ih l fun r => k (x :: r)) a
noncomputable def seps (dn : List El) (acc : Nat) : Nat :=
  @List.rec El (fun _ => Nat) acc (fun e _ ih => Nat.lor e.s ih) dn
abbrev Ch := Nat → List El → List El → Bool
structure Ctx where
  P : Par
  ch : Ch
  d : Bool
  t : Nat
  k : Nat
  R : Nat
  all : List El
structure Pr where
  newer : List El
  acc : Nat
  x : El
  e : El
  dn : List El
  ys : List El
noncomputable def chk (b R : Nat) (k : Nat → Bool) : Bool :=
  force R fun R => (@Bool.rec (fun _ => Bool) false (k R) (Nat.beq (Nat.land R b) b))
noncomputable def mk (a s zf of : Nat) (k : El → Bool) : Bool :=
  force zf fun zf => force of fun of => k ⟨a, s, zf, of, 0, 0⟩
noncomputable def cf (e : El) : Nat := Nat.lor e.zf e.of
noncomputable def kid (c : Ctx) (R : Nat) (z : El) (act dn old : List El) : Bool :=
  chk c.P.bias (Nat.sub R (cf z)) fun R => appK dn old fun o => c.ch R (z :: act) o
noncomputable def base (c : Ctx) (p : Pr) : Nat := Nat.sub c.R (Nat.lor (cf p.x) (cf p.e))
noncomputable def fin2 (c : Ctx) (p : Pr) (z : El) : Bool :=
  (@Bool.rec (fun _ => Bool) false (kid c (base c p) z (p.x :: p.newer) p.dn (p.e :: p.ys)) (Nat.ble 2 c.k))
noncomputable def finY (c : Ctx) (p : Pr) (z : El) (R1 : Nat) : Bool :=
  (@Bool.rec (fun _ => Bool) (fin2 c p z) true ((@Bool.rec (fun _ => Bool) false (kid c (Nat.add (base c p) (cf p.x)) z p.newer p.dn (p.e :: p.ys)) (Nat.beq (Nat.lor R1 p.e.s) c.P.full))))
noncomputable def finX (c : Ctx) (p : Pr) (z : El) (R1 : Nat) : Bool :=
  (@Bool.rec (fun _ => Bool) (finY c p z R1) true ((@Bool.rec (fun _ => Bool) false (kid c (Nat.add (base c p) (cf p.e)) z (p.x :: p.newer) p.dn p.ys) (Nat.beq (Nat.lor R1 p.x.s) c.P.full))))
noncomputable def fin1 (c : Ctx) (p : Pr) (z : El) (R1 : Nat) : Bool := (@Bool.rec (fun _ => Bool) false (finX c p z R1) (Nat.ble 1 c.k))
noncomputable def fin (c : Ctx) (p : Pr) (z : El) (R1 : Nat) : Bool :=
  (@Bool.rec (fun _ => Bool) (fin1 c p z R1) true ((@Bool.rec (fun _ => Bool) false (kid c (Nat.add (base c p) (Nat.add (cf p.x) (cf p.e))) z p.newer p.dn p.ys) (Nat.beq R1 c.P.full))))
noncomputable def hand2 (c : Ctx) (p : Pr) (z sz zf of R1 : Nat) : Bool :=
  @Bool.rec (fun _ => Bool) (mk z sz zf of fun z => fin c p z R1) false (has z c.all)
noncomputable def hand3 (c : Ctx) (p : Pr) (z sz zf of R1 : Nat) : Bool :=
  (@Bool.rec (fun _ => Bool) ((@Bool.rec (fun _ => Bool) false ((@Bool.rec (fun _ => Bool) false (hand2 c p z sz zf of R1) (Nat.beq (Nat.lor R1 (Nat.lor p.x.s p.e.s)) c.P.full))) (Nat.ble 1 c.k))) true ((@Bool.rec (fun _ => Bool) false (hand2 c p z sz zf of R1) (Nat.beq R1 c.P.full))))
noncomputable def hand (c : Ctx) (p : Pr) (R0 z zf of : Nat) : Bool :=
  force z fun z => force (sep c.P.full c.d z) fun sz => force (Nat.lor R0 sz) fun R1 => hand3 c p z sz zf of R1
noncomputable def hA (c : Ctx) (p : Pr) (R0 : Nat) : Bool :=
  hand c p R0 (Nat.land p.x.a p.e.a) (Nat.lor p.x.zf p.e.zf) (Nat.land p.x.of p.e.of)
noncomputable def hO (c : Ctx) (p : Pr) (R0 : Nat) : Bool :=
  hand c p R0 (Nat.lor p.x.a p.e.a) (Nat.land p.x.zf p.e.zf) (Nat.lor p.x.of p.e.of)
noncomputable def f0 (c : Ctx) (p : Pr) (t : Nat) : Bool :=
  (@Bool.rec (fun _ => Bool) ((@Bool.rec (fun _ => Bool) false ((@Bool.rec (fun _ => Bool) false (hO c p (Nat.lor (seps p.dn p.acc) p.e.f)) (Nat.beq (Nat.land p.e.u p.x.a) 0))) (Nat.beq t 0))) true ((@Bool.rec (fun _ => Bool) false ((@Bool.rec (fun _ => Bool) false (hA c p (Nat.lor (seps p.dn p.acc) p.e.f)) (Nat.beq (Nat.land p.e.u p.x.a) p.e.u))) (Nat.beq t p.x.u))))
noncomputable def f1 (c : Ctx) (p : Pr) (R0 t t' : Nat) : Bool :=
  (@Bool.rec (fun _ => Bool) ((@Bool.rec (fun _ => Bool) false (hO c p R0) ((@Bool.rec (fun _ => Bool) (Nat.beq t' 0) true (Nat.beq t 0))))) true ((@Bool.rec (fun _ => Bool) false (hA c p R0) ((@Bool.rec (fun _ => Bool) (Nat.beq t' p.e.u) true (Nat.beq t p.x.u))))))
noncomputable def l0 (c : Ctx) (newer : List El) (acc : Nat) (x : El) (ux : Nat) (l : List El) : List El → Bool :=
  @List.rec El (fun _ => List El → Bool) (fun _ => false)
    (fun e ys ih dn => (@Bool.rec (fun _ => Bool) (ih (e :: dn)) true ((@Bool.rec (fun _ => Bool) false (f0 c ⟨newer, acc, x, e, dn, ys⟩ (Nat.land ux e.a)) (Nat.beq (Nat.mul (Nat.land ux e.a) (Nat.sub ux (Nat.land ux e.a))) 0))))) l
noncomputable def l1 (c : Ctx) (newer : List El) (x : El) (l : List El) : Nat → List El → Bool :=
  @List.rec El (fun _ => Nat → List El → Bool) (fun _ _ => false)
    (fun e ys ih acc dn => (@Bool.rec (fun _ => Bool) (force (Nat.lor acc e.s) fun acc => ih acc (e :: dn)) true (f1 c ⟨newer, acc, x, e, dn, ys⟩ (Nat.lor acc e.f) (Nat.land x.u e.a) (Nat.land e.u x.a)))) l
noncomputable def l2 (c : Ctx) (newer : List El) (x : El) (l : List El) : Nat → List El → Bool :=
  @List.rec El (fun _ => Nat → List El → Bool) (fun _ _ => false)
    (fun e ys ih acc dn => (@Bool.rec (fun _ => Bool) ((@Bool.rec (fun _ => Bool) (force (Nat.lor acc e.s) fun acc => ih acc (e :: dn)) true (hO c ⟨newer, acc, x, e, dn, ys⟩ (Nat.lor acc e.f)))) true (hA c ⟨newer, acc, x, e, dn, ys⟩ (Nat.lor acc e.f)))) l
noncomputable def pairs (c : Ctx) (newer : List El) (acc : Nat) (x : El) (es : List El) : Bool :=
  @Nat.rec (fun _ => Bool) (force x.u fun ux => l0 c newer acc x ux es [])
    (fun k _ => @Nat.rec (fun _ => Bool) (l1 c newer x es acc []) (fun _ _ => l2 c newer x es acc []) k) c.k
noncomputable def unK (c : Ctx) (chU : Ch) (newer : List El) (w : El) (es : List El) (z : El) : Bool :=
  @Bool.rec (fun _ => Bool)
    (@Bool.rec (fun _ => Bool) (chk c.P.bias (Nat.sub (Nat.sub c.R (cf w)) (cf z)) fun R => chU R (z :: w :: newer) es) true (chk c.P.bias (Nat.sub c.R (cf z)) fun R => chU R (z :: newer) es)) false (has z.a c.all)
noncomputable def un2 (c : Ctx) (chU : Ch) (newer : List El) (w : El) (es : List El) (z : Nat) : Bool :=
  mk z 0 w.of w.zf fun z => unK c chU newer w es z
noncomputable def unary (c : Ctx) (chU : Ch) (newer : List El) (w : El) (es : List El) (U0 : Nat) : Bool :=
  force (neg c.P.top w.a) fun z =>
  (@Bool.rec (fun _ => Bool) false (un2 c chU newer w es z) (Nat.beq (Nat.lor U0 (sep c.P.full (Nat.ble 2 c.t) z)) c.P.full))
noncomputable def scan (c : Ctx) (hB hU : Bool) (U0 : Nat) (chU : Ch) (es : List El) : Nat → List El → Nat → Bool :=
  @List.rec El (fun _ => Nat → List El → Nat → Bool) (fun _ _ _ => false)
    (fun e es ih n newer acc => @Nat.rec (fun _ => Bool) false (fun n _ =>
      (@Bool.rec (fun _ => Bool) ((@Bool.rec (fun _ => Bool) (force (Nat.lor acc e.s) fun acc' => ih n (e :: newer) acc') true ((@Bool.rec (fun _ => Bool) false (unary c chU newer e es U0) (hU))))) true ((@Bool.rec (fun _ => Bool) false (pairs c newer acc e es) (hB))))) n) es
noncomputable def isTgt (t : Nat) (l : List El) : Bool :=
  @List.rec El (fun _ => Bool) false (fun e l _ => @List.rec El (fun _ => Bool) (Nat.beq e.a t) (fun _ _ _ => false) l) l
noncomputable def len (l : List El) : Nat := @List.rec El (fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l
noncomputable def resep (full : Nat) (d : Bool) (l : List El) : (List El → Bool) → Bool :=
  @List.rec El (fun _ => (List El → Bool) → Bool) (fun k => k [])
    (fun e _ ih k => ih fun r => force (sep full d e.a) fun s => k (⟨e.a, s, e.zf, e.of, 0, 0⟩ :: r)) l
noncomputable def seps0 (full : Nat) (d : Bool) (l : List El) : Nat :=
  @List.rec El (fun _ => Nat) 0 (fun e _ ih => Nat.lor (sep full d e.a) ih) l
noncomputable def body2 (P : Par) (B T n : Nat) (chB chU : Ch) (R : Nat) (act l es : List El) : Bool :=
  (@Bool.rec (fun _ => Bool) (force (Nat.sub (Nat.succ B) n) fun k => force (@Bool.rec (fun _ => Nat) 0 (seps0 P.full (Nat.ble 2 T) l) (Nat.ble 1 T)) fun U0 => scan ⟨P, chB, Nat.ble 1 T, T, k, R, l⟩ (Nat.ble 1 B) (Nat.ble 1 T) U0 chU es (len act) [] 0) true ((@Bool.rec (fun _ => Bool) false (isTgt P.tgt l) (Nat.beq T 0))))
noncomputable def body (P : Par) (B T : Nat) (chB chU : Ch) : Ch := fun R act old =>
  appK act old fun l => force (len l) fun n =>
  (@Bool.rec (fun _ => Bool) false (buildK l fun es => (@Bool.rec (fun _ => Bool) false (uniqK es 0 fun es => body2 P B T n chB chU R act l es) (Nat.beq (sufOf es) P.full))) (Nat.ble n (Nat.succ B)))
noncomputable def node (P : Par) (f : Nat) : Nat → Nat → Ch :=
  @Nat.rec (fun _ => Nat → Nat → Ch) (fun _ _ _ _ _ => true)
    (fun _ ih B T => body P B T (ih (Nat.pred B) T)
      (fun R act old => resep P.full (Nat.ble 2 T) act fun act => resep P.full (Nat.ble 2 T) old fun old =>
        ih B (Nat.pred T) R act old)) f
end Sec3

section Vs4
variable {top tgt : Nat}

lemma bAnd (c x : Bool) : @Bool.rec (fun _ => Bool) false x c = (c && x) := by cases c <;> rfl
lemma bOr (c x : Bool) : @Bool.rec (fun _ => Bool) x true c = (c || x) := by cases c <;> rfl
lemma bNot (c x : Bool) : @Bool.rec (fun _ => Bool) x false c = (!c && x) := by cases c <;> rfl
lemma force_eq (n : Nat) (f : Nat → Bool) : force n f = f n := by cases n <;> rfl

lemma has_eq (z : Nat) (l : List El) : has z l = true ↔ z ∈ l.map El.a := by
  induction l with
  | nil => simp [has]
  | cons e l ih =>
    have : has z (e :: l) = (Nat.beq e.a z || has z l) := bOr _ _
    rw [this, Bool.or_eq_true, ih, Nat.beq_eq]
    simp [eq_comm]

lemma appK_eq (a : List El) : ∀ (l : List El) (k : List El → Bool), appK a l k = k (a ++ l) := by
  induction a with
  | nil => intro l k; rfl
  | cons x a ih => intro l k; exact ih l _

noncomputable def reF : List El → List El
  | [] => []
  | e :: l => ⟨e.a, e.s, e.zf, e.of, sufOf (reF l), 0⟩ :: reF l
def reU : List El → Nat → List El
  | [], _ => []
  | e :: l, acc => ⟨e.a, e.s, e.zf, e.of, e.f, Nat.xor e.s (Nat.land e.s (Nat.lor acc e.f))⟩ ::
      reU l (Nat.lor acc e.s)
def reS (full : Nat) (d : Bool) : List El → List El
  | [] => []
  | e :: l => ⟨e.a, sep full d e.a, e.zf, e.of, 0, 0⟩ :: reS full d l

lemma buildK_eq (l : List El) : ∀ k, buildK l k = k (reF l) := by
  induction l with
  | nil => intro k; rfl
  | cons e l ih =>
    intro k
    have : buildK (e :: l) k = buildK l fun r => force (sufOf r) fun u =>
      k (⟨e.a, e.s, e.zf, e.of, u, 0⟩ :: r) := rfl
    rw [this, ih, force_eq]; rfl
lemma uniqK_eq (l : List El) : ∀ acc k, uniqK l acc k = k (reU l acc) := by
  induction l with
  | nil => intro acc k; rfl
  | cons e l ih =>
    intro acc k
    have : uniqK (e :: l) acc k = force (Nat.xor e.s (Nat.land e.s (Nat.lor acc e.f))) fun u =>
      force (Nat.lor acc e.s) fun acc' => uniqK l acc' fun r =>
        k (⟨e.a, e.s, e.zf, e.of, e.f, u⟩ :: r) := rfl
    rw [this, force_eq, force_eq, ih]; rfl
lemma resep_eq (full : Nat) (d : Bool) (l : List El) : ∀ k, resep full d l k = k (reS full d l) := by
  induction l with
  | nil => intro k; rfl
  | cons e l ih =>
    intro k
    have : resep full d (e :: l) k = resep full d l fun r => force (sep full d e.a) fun s =>
      k (⟨e.a, s, e.zf, e.of, 0, 0⟩ :: r) := rfl
    rw [this, ih, force_eq]; rfl

-- union of the s fields
def sU : List El → Nat
  | [] => 0
  | e :: l => Nat.lor e.s (sU l)
lemma sU_bit (l : List El) (i : Nat) : (sU l).testBit i = true ↔ ∃ e ∈ l, e.s.testBit i = true := by
  induction l with
  | nil => simp [sU]
  | cons e l ih => simp only [sU, tb_lor, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
lemma seps_bit (l : List El) (acc i : Nat) : (seps l acc).testBit i = true ↔
    acc.testBit i = true ∨ ∃ e ∈ l, e.s.testBit i = true := by
  induction l with
  | nil => simp [seps]
  | cons e l ih =>
    have : seps (e :: l) acc = Nat.lor e.s (seps l acc) := rfl
    rw [this, tb_lor, Bool.or_eq_true, ih]
    simp only [List.mem_cons, exists_eq_or_imp]; tauto
lemma seps0_bit (full : Nat) (d : Bool) (l : List El) (i : Nat) : (seps0 full d l).testBit i = true ↔
    ∃ e ∈ l, (sep full d e.a).testBit i = true := by
  induction l with
  | nil => simp [seps0]
  | cons e l ih =>
    have : seps0 full d (e :: l) = Nat.lor (sep full d e.a) (seps0 full d l) := rfl
    rw [this, tb_lor, Bool.or_eq_true, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
lemma len_eq (l : List El) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons e l ih => have : len (e :: l) = Nat.succ (len l) := rfl; rw [this, ih]; rfl

-- same data up to the two scratch fields
def same (e e' : El) : Prop := e.a = e'.a ∧ e.s = e'.s ∧ e.zf = e'.zf ∧ e.of = e'.of
lemma reF_same (l : List El) : List.Forall₂ same l (reF l) := by
  induction l with
  | nil => exact .nil
  | cons e l ih => exact .cons ⟨rfl, rfl, rfl, rfl⟩ ih
lemma reU_same (l : List El) : ∀ acc, List.Forall₂ same l (reU l acc) := by
  induction l with
  | nil => intro _; exact .nil
  | cons e l ih => intro acc; exact .cons ⟨rfl, rfl, rfl, rfl⟩ (ih _)

-- what the scratch fields hold after the two passes
def Ents : Nat → List El → Prop
  | _, [] => True
  | acc, e :: l => e.f = sU l ∧ e.u = Nat.xor e.s (Nat.land e.s (Nat.lor acc e.f)) ∧
      Ents (Nat.lor acc e.s) l
lemma sufOf_reF (l : List El) : sufOf (reF l) = sU l := by
  induction l with
  | nil => rfl
  | cons e l ih => change Nat.lor e.s (sufOf (reF l)) = _; rw [ih]; rfl
lemma sU_same {l l' : List El} (h : List.Forall₂ same l l') : sU l = sU l' := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp only [sU, h.2.1, ih]
lemma ents (l : List El) : ∀ acc, Ents acc (reU (reF l) acc) := by
  induction l with
  | nil => intro _; trivial
  | cons e l ih =>
    intro acc
    refine ⟨?_, rfl, ih _⟩
    change sufOf (reF l) = sU (reU (reF l) _)
    rw [sufOf_reF, ← sU_same (reU_same _ _), ← sU_same (reF_same _)]

-- packed numbers, one byte per lane
def b2n (b : Bool) : Nat := cond b 1 0
def encV : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, v => v 0 + 256 * encV n (fun i => v (i + 1))
def encB (n : Nat) (f : Nat → Bool) : Nat := encV n (fun i => b2n (f i))

lemma b2n_le (b : Bool) : b2n b ≤ 1 := by cases b <;> decide
lemma tb_split (x y j : Nat) (hx : x < 256) : (x + 256 * y).testBit j =
    (if j < 8 then x.testBit j else y.testBit (j - 8)) := by
  have h : x + 256 * y = 2 ^ 8 * y + x := by omega
  rw [h, Nat.testBit_two_pow_mul_add y (by simpa using hx)]
lemma encV_bit (n : Nat) : ∀ (v : Nat → Nat), (∀ i < n, v i < 256) → ∀ j,
    (encV n v).testBit j = (decide (j / 8 < n) && (v (j / 8)).testBit (j % 8)) := by
  induction n with
  | zero => intro v _ j; simp [encV]
  | succ n ih =>
    intro v hv j
    rw [encV, tb_split _ _ _ (hv 0 (by omega)), ih _ (fun i hi => hv (i + 1) (by omega))]
    by_cases hj : j < 8
    · have h0 : j / 8 = 0 := by omega
      have h1 : j % 8 = j := by omega
      simp [hj, h0, h1]
    · have h0 : j / 8 = (j - 8) / 8 + 1 := by omega
      have h1 : j % 8 = (j - 8) % 8 := by omega
      simp only [hj, if_false, h0, h1]
      congr 1
lemma encV_congr (n : Nat) : ∀ {v w : Nat → Nat}, (∀ i < n, v i = w i) → encV n v = encV n w := by
  induction n with
  | zero => intro v w _; rfl
  | succ n ih => intro v w h; rw [encV, encV, h 0 (by omega), ih (fun i hi => h (i + 1) (by omega))]
lemma encV_add (n : Nat) : ∀ (v w : Nat → Nat), Nat.add (encV n v) (encV n w) = encV n (fun i => v i + w i) := by
  induction n with
  | zero => intro v w; rfl
  | succ n ih =>
    intro v w
    have := ih (fun i => v (i + 1)) (fun i => w (i + 1))
    simp only [encV, Nat.add_eq] at this ⊢; omega
lemma encV_sub (n : Nat) : ∀ (v w : Nat → Nat), (∀ i < n, w i ≤ v i) →
    Nat.sub (encV n v) (encV n w) = encV n (fun i => v i - w i) := by
  intro v w h
  have : encV n v = Nat.add (encV n (fun i => v i - w i)) (encV n w) := by
    rw [encV_add]; apply encV_congr; intro i hi; have := h i hi; omega
  rw [this]; simp

def flg (i X : Nat) : Bool := X.testBit (8 * i)
def WF (n X : Nat) : Prop := X = encB n (fun i => flg i X)
lemma encB_bit (n : Nat) (f : Nat → Bool) (j : Nat) :
    (encB n f).testBit j = (decide (j / 8 < n) && decide (j % 8 = 0) && f (j / 8)) := by
  rw [encB, encV_bit n _ (fun i _ => by have := b2n_le (f i); omega)]
  cases f (j / 8)
  · simp [b2n]
  · simp only [b2n, Bool.cond_true, Bool.and_true]
    congr 1
    have : j % 8 < 8 := by omega
    interval_cases j % 8 <;> rfl
lemma WF_encB (n : Nat) (f : Nat → Bool) : WF n (encB n f) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [encB_bit, encB_bit]
  by_cases h1 : j / 8 < n <;> by_cases h2 : j % 8 = 0
  · have : 8 * (j / 8) = j := by omega
    simp [flg, encB_bit, h1]
  all_goals simp [h1, h2]
lemma flg_encB (n : Nat) (f : Nat → Bool) (i : Nat) (hi : i < n) : flg i (encB n f) = f i := by
  simp [flg, encB_bit, hi]
lemma WF_bit {n X : Nat} (hx : WF n X) (j : Nat) (h : ¬ (j / 8 < n ∧ j % 8 = 0)) : X.testBit j = false := by
  rw [hx, encB_bit]
  by_cases h1 : j / 8 < n <;> by_cases h2 : j % 8 = 0
  · exact absurd ⟨h1, h2⟩ h
  all_goals simp [h1, h2]
lemma WF_of {n X : Nat} (h : ∀ j, ¬ (j / 8 < n ∧ j % 8 = 0) → X.testBit j = false) : WF n X := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [encB_bit]
  by_cases h1 : j / 8 < n <;> by_cases h2 : j % 8 = 0
  · have : 8 * (j / 8) = j := by omega
    simp [flg, h1, h2, this]
  all_goals (rw [h j (by tauto)]; simp [h1, h2])
lemma WF_lor {n X Y : Nat} (hx : WF n X) (hy : WF n Y) : WF n (Nat.lor X Y) :=
  WF_of fun j h => by rw [tb_lor, WF_bit hx j h, WF_bit hy j h]; rfl
lemma WF_land {n X Y : Nat} (hx : WF n X) (hy : WF n Y) : WF n (Nat.land X Y) :=
  WF_of fun j h => by rw [tb_land, WF_bit hx j h, WF_bit hy j h]; rfl
lemma chk_eq (n : Nat) (v : Nat → Nat) (hv : ∀ i < n, v i ≤ 127) (k : Nat → Bool)
    (h : ∀ i < n, 64 ≤ v i) (hk : k (encV n v) = true) :
    chk (encV n (fun _ => 64)) (encV n v) k = true := by
  rw [chk, force_eq, bAnd, hk, Bool.and_true, Nat.beq_eq]
  apply Nat.eq_of_testBit_eq; intro j
  rw [tb_land, encV_bit _ _ (fun i hi => by have := hv i hi; omega), encV_bit _ _ (fun i _ => by omega)]
  by_cases hj : j / 8 < n
  · have h1 := h _ hj; have h2 := hv _ hj
    simp only [hj, decide_true, Bool.true_and]
    generalize v (j / 8) = x at h1 h2
    have : j % 8 < 8 := by omega
    revert this; generalize j % 8 = r; intro hr
    revert x r; decide +kernel
  · simp [hj]

end Vs4


structure Env (P : Par) (n : Nat) (Λ : Nat → Nat) : Prop where
  gd : Gd P.top P.full P.tgt
  msk : ∀ i < n, Msk P.top P.tgt (Λ i)
  bias : P.bias = encV n (fun _ => 64)

def EOK (n : Nat) (Λ : Nat → Nat) (e : El) : Prop :=
  WF n e.zf ∧ WF n e.of ∧ ∀ i < n, (flg i e.zf = true → zM (Λ i) e.a) ∧ (flg i e.of = true → oM (Λ i) e.a)
def con (i : Nat) (e : El) : Bool := flg i e.zf || flg i e.of
def cfl (i : Nat) (l : List El) : Nat := l.countP (con i)
def wd (l : List El) : List Nat := l.map El.a

lemma con_sound {n : Nat} {Λ : Nat → Nat} {e : El} (h : EOK n Λ e) {i : Nat} (hi : i < n) (hc : con i e = true) :
    conM (Λ i) e.a := by
  rcases Bool.or_eq_true_iff.mp hc with h' | h'
  · exact Or.inl ((h.2.2 i hi).1 h')
  · exact Or.inr ((h.2.2 i hi).2 h')

lemma cfl_le {n : Nat} {Λ : Nat → Nat} {l : List El} (h : ∀ e ∈ l, EOK n Λ e) (hn : (wd l).Nodup) {i : Nat} (hi : i < n) :
    cfl i l ≤ cN (Λ i) (wd l).toFinset := by
  classical
  unfold cfl cN
  rw [List.countP_eq_length_filter]
  have hnd : ((l.filter (con i)).map El.a).Nodup := hn.sublist (List.filter_sublist.map _)
  rw [← List.length_map (f := El.a), ← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
  obtain ⟨e, ⟨he, hc⟩, rfl⟩ := hx
  rw [Finset.mem_filter]
  exact ⟨by simp [wd]; exact ⟨e, he, rfl⟩, con_sound (h e he) hi hc⟩

lemma cfl_perm {l r : List El} (h : l.Perm r) (i : Nat) : cfl i l = cfl i r := h.countP_eq _
lemma cfl_append (l r : List El) (i : Nat) : cfl i (l ++ r) = cfl i l + cfl i r := List.countP_append
lemma cfl_cons (e : El) (l : List El) (i : Nat) : cfl i (e :: l) = b2n (con i e) + cfl i l := by
  unfold cfl; rw [List.countP_cons]; cases con i e <;> simp [b2n] <;> omega

def JOK (P : Par) (n : Nat) (Λ : Nat → Nat) (K : Nat) (v : Nat → Nat) (l : List El) : Prop :=
  ∀ i < n, 64 ≤ v i ∧ v i ≤ 126 ∧ ∃ L, LB P.top P.tgt (Λ i) L (wd l).toFinset ∧ K + 64 ≤ L + cfl i l + v i

def Inv (P : Par) (n : Nat) (Λ : Nat → Nat) (sk : El → Prop) (B T R : Nat) (act old : List El) : Prop :=
  ∃ ms H v, Dv P.top P.tgt ms H (wd (act ++ old)).toFinset ∧ nb ms ≤ B ∧ nu ms = T ∧
    (wd (act ++ old)).Nodup ∧ (∀ e ∈ act ++ old, sk e ∧ EOK n Λ e) ∧
    (∀ m ∈ ms, ops m ⊆ (wd (act ++ old)).toFinset → ∃ a ∈ ops m, a ∈ wd act) ∧
    R = encV n v ∧ JOK P n Λ (B + T) v (act ++ old)

lemma wd_perm {l r : List El} (h : l.Perm r) : (wd l).Perm (wd r) := h.map _

lemma childInv {P : Par} {n : Nat} {Λ : Nat → Nat} (env : Env P n Λ) {sk : El → Prop} {K B' T' : Nat} {m : Mv} {ms' : List Mv}
    {H U : Finset Nat} {v : Nat → Nat} {l dl lu act' old' : List El} {z : El} {fr : Nat → Bool}
    (hg : good m) (hf : res P.top m ∉ H) (hsub : (wd l).toFinset ⊆ H) (hS : (wd l).toFinset = ops m ∪ U)
    (hd : Dv P.top P.tgt ms' (insert (res P.top m) H) (insert (res P.top m) U))
    (hB : nb ms' ≤ B') (hT : nu ms' = T') (hK : K = B' + T' + 1)
    (hn : (wd l).Nodup) (he : ∀ e ∈ l, EOK n Λ e) (hj : JOK P n Λ K v l)
    (hz : z.a = res P.top m) (hze : EOK n Λ z) (hsk : ∀ e ∈ z :: lu, sk e)
    (hp : (dl ++ lu).Perm l) (hlu : (wd lu).toFinset = U) (hp' : (act' ++ old').Perm (z :: lu))
    (hav : ∀ m' ∈ ms', ops m' ⊆ insert (res P.top m) U → ∃ a ∈ ops m', a ∈ wd act')
    (hfr : ∀ i < n, fr i = true → ∃ a ∈ ops m, conM (Λ i) a)
    (hzc : ∀ i < n, con i z = true → fr i = true)
    (hmo : ∀ i < n, cfl i dl ≤ b2n (fr i) + b2n (con i z)) :
    (∀ i < n, 64 + b2n (fr i) + b2n (con i z) ≤ v i + cfl i dl) ∧
    Inv P n Λ sk B' T' (encV n (fun i => v i - b2n (fr i) + cfl i dl - b2n (con i z))) act' old' := by
  have hzU : res P.top m ∉ U := fun h => hf (hsub (by rw [hS]; exact Finset.mem_union_right _ h))
  have hnl : (wd (dl ++ lu)).Nodup := (wd_perm hp).nodup_iff.mpr hn
  have hnlu : (wd lu).Nodup := by
    rw [wd, List.map_append] at hnl; exact (List.nodup_append.mp hnl).2.1
  have hzlu : z.a ∉ wd lu := fun h => hzU (by rw [← hlu, ← hz]; exact List.mem_toFinset.mpr h)
  have hn' : (wd (z :: lu)).Nodup := by
    change (z.a :: wd lu).Nodup; exact List.nodup_cons.mpr ⟨hzlu, hnlu⟩
  have hset : (wd (act' ++ old')).toFinset = insert (res P.top m) U := by
    rw [List.toFinset_eq_of_perm _ _ (wd_perm hp')]
    change (z.a :: wd lu).toFinset = _
    rw [List.toFinset_cons, hlu, hz]
  have helu : ∀ e ∈ z :: lu, EOK n Λ e := by
    intro e h
    rcases List.mem_cons.mp h with rfl | h
    · exact hze
    · exact he e (hp.mem_iff.mp (List.mem_append_right _ h))
  have hset2 : (wd (z :: lu)).toFinset = insert (res P.top m) U := by
    rw [← hset, List.toFinset_eq_of_perm _ _ (wd_perm hp')]
  have hlen : ms'.length ≤ B' + T' := by have := nb_nu ms'; omega
  have key : ∀ i < n, (64 + b2n (fr i) + b2n (con i z) ≤ v i + cfl i dl) ∧
      ∃ L, LB P.top P.tgt (Λ i) L (insert (res P.top m) U) ∧
        B' + T' + 64 ≤ L + cfl i (z :: lu) + (v i - b2n (fr i) + cfl i dl - b2n (con i z)) := by
    intro i hi
    obtain ⟨h64, _, L, hL, hKL⟩ := hj i hi
    rw [hS] at hL
    have hmo := hmo i hi
    rw [← cfl_perm hp, cfl_append] at hKL
    rw [cfl_cons]
    cases hfi : fr i
    · have hzi : con i z = false := by
        by_contra h; have := hzc i hi (by simpa using h); rw [hfi] at this; exact absurd this (by decide)
      rw [hfi, hzi] at hmo
      simp only [hzi, b2n, Bool.cond_false] at hmo ⊢
      refine ⟨by omega, L - 1, hL.step (env.msk i hi).sub, by omega⟩
    · have hL' := hL.stepFree (env.msk i hi).sub hg (hfr i hi hfi)
      have h1 := hL'.len (env.msk i hi) hd
      have h2 := cfl_le helu hn' hi
      rw [hset2, cfl_cons] at h2
      simp only [b2n, Bool.cond_true] at h2 ⊢
      refine ⟨by omega, L, hL', by omega⟩
  refine ⟨fun i hi => (key i hi).1, ms', insert (res P.top m) H, _, hset ▸ hd, hB, hT,
    (wd_perm hp').nodup_iff.mpr hn', ?_, ?_, rfl, ?_⟩
  · intro e h
    have h' := hp'.mem_iff.mp h
    exact ⟨hsk e h', helu e h'⟩
  · intro m' hm' hs; rw [hset] at hs; exact hav m' hm' hs
  · intro i hi
    obtain ⟨k1, L, k2, k3⟩ := key i hi
    obtain ⟨h64, h126, _⟩ := hj i hi
    have := hmo i hi
    have := b2n_le (fr i)
    have := b2n_le (con i z)
    refine ⟨by beta_reduce; omega, by beta_reduce; omega, L, by rw [hset]; exact k2, ?_⟩
    rw [cfl_perm hp']; exact k3

lemma cf_enc {n : Nat} {Λ : Nat → Nat} {e : El} (h : EOK n Λ e) : cf e = encV n (fun i => b2n (con i e)) := by
  have hw : WF n (cf e) := WF_lor h.1 h.2.1
  have : cf e = encB n (fun i => flg i (cf e)) := hw
  rw [this]; apply encV_congr; intro i _
  change b2n (flg i (Nat.lor e.zf e.of)) = _
  rw [flg, tb_lor]; rfl

lemma base_enc {n : Nat} {Λ : Nat → Nat} {x e : El} (hx : EOK n Λ x) (he : EOK n Λ e) :
    Nat.lor (cf x) (cf e) = encV n (fun i => b2n (con i x || con i e)) := by
  have hw : WF n (Nat.lor (cf x) (cf e)) := WF_lor (WF_lor hx.1 hx.2.1) (WF_lor he.1 he.2.1)
  have : Nat.lor (cf x) (cf e) = encB n (fun i => flg i (Nat.lor (cf x) (cf e))) := hw
  rw [this]; apply encV_congr; intro i _
  change b2n (flg i (Nat.lor (Nat.lor x.zf x.of) (Nat.lor e.zf e.of))) = _
  simp only [flg, tb_lor]; rfl

lemma kid_true {P : Par} {n : Nat} {Λ : Nat → Nat} (env : Env P n Λ) (c : Ctx) (hc : c.P = P) {R0 : Nat} {z : El}
    {act dn old : List El} {v w : Nat → Nat} (hR : R0 = encV n v) (hz : EOK n Λ z)
    (hv : ∀ i < n, 64 + b2n (con i z) ≤ v i) (hv' : ∀ i < n, v i ≤ 127 + b2n (con i z)) (hw : ∀ i < n, w i = v i - b2n (con i z))
    (hk : c.ch (encV n w) (z :: act) (dn ++ old) = true) : kid c R0 z act dn old = true := by
  unfold kid
  have e : Nat.sub R0 (cf z) = encV n w := by
    rw [hR, cf_enc hz, encV_sub _ _ _ (fun i hi => by have := hv i hi; omega)]
    exact encV_congr _ (fun i hi => (hw i hi).symm)
  rw [e, hc, env.bias]
  apply chk_eq
  · intro i hi; have := hv' i hi; have := hw i hi; omega
  · intro i hi; have := hv i hi; have := hw i hi; omega
  · rw [appK_eq]; exact hk


-- everything known about one node, over a list in any order
structure Rdy (P : Par) (n : Nat) (Λ : Nat → Nat) (B T : Nat) (v : Nat → Nat) (ms : List Mv) (H : Finset Nat)
    (l : List El) : Prop where
  dv : Dv P.top P.tgt ms H (wd l).toFinset
  hB : nb ms ≤ B
  hT : nu ms = T
  nd : (wd l).Nodup
  sp : ∀ e ∈ l, e.s = sep P.full (decide (1 ≤ T)) e.a
  ok : ∀ e ∈ l, EOK n Λ e
  jo : JOK P n Λ (B + T) v l

lemma Rdy.perm {P n Λ B T v ms H l r} (h : Rdy P n Λ B T v ms H l) (p : l.Perm r) : Rdy P n Λ B T v ms H r := by
  have hs : (wd r).toFinset = (wd l).toFinset := (List.toFinset_eq_of_perm _ _ (wd_perm p)).symm
  refine ⟨hs ▸ h.dv, h.hB, h.hT, (wd_perm p).nodup_iff.mp h.nd, fun e he => h.sp e (p.mem_iff.mpr he),
    fun e he => h.ok e (p.mem_iff.mpr he), fun i hi => ?_⟩
  obtain ⟨a, b, L, c, d⟩ := h.jo i hi
  exact ⟨a, b, L, hs ▸ c, by rw [← cfl_perm p]; exact d⟩

lemma ball_and {c x : Bool} (h1 : c = true) (h2 : x = true) : (c && x) = true := by rw [h1, h2]; rfl
lemma bor_l {c x : Bool} (h : c = true) : (c || x) = true := by rw [h]; rfl
lemma bor_r {c x : Bool} (h : x = true) : (c || x) = true := by rw [h]; cases c <;> rfl

def zfl (dd : Bool) (x e : El) : Nat := cond dd (Nat.land x.zf e.zf) (Nat.lor x.zf e.zf)
def ofl (dd : Bool) (x e : El) : Nat := cond dd (Nat.lor x.of e.of) (Nat.land x.of e.of)

lemma zOK {n : Nat} {Λ : Nat → Nat} {x e : El} (hx : EOK n Λ x) (he : EOK n Λ e) (dd : Bool) (s : Nat) :
    EOK n Λ ⟨bin dd x.a e.a, s, zfl dd x e, ofl dd x e, 0, 0⟩ := by
  cases dd
  · refine ⟨WF_lor hx.1 he.1, WF_land hx.2.1 he.2.1, fun i hi => ⟨fun h j hj => ?_, fun h j hj => ?_⟩⟩
    · simp only [flg, zfl, Bool.cond_false, tb_lor, Bool.or_eq_true] at h
      simp only [bin, Bool.cond_false, tb_land]
      rcases h with h | h
      · rw [(hx.2.2 i hi).1 h j hj]; rfl
      · rw [(he.2.2 i hi).1 h j hj]; simp
    · simp only [flg, ofl, Bool.cond_false, tb_land, Bool.and_eq_true] at h
      simp only [bin, Bool.cond_false, tb_land]
      rw [(hx.2.2 i hi).2 h.1 j hj, (he.2.2 i hi).2 h.2 j hj]; rfl
  · refine ⟨WF_land hx.1 he.1, WF_lor hx.2.1 he.2.1, fun i hi => ⟨fun h j hj => ?_, fun h j hj => ?_⟩⟩
    · simp only [flg, zfl, Bool.cond_true, tb_land, Bool.and_eq_true] at h
      simp only [bin, Bool.cond_true, tb_lor]
      rw [(hx.2.2 i hi).1 h.1 j hj, (he.2.2 i hi).1 h.2 j hj]; rfl
    · simp only [flg, ofl, Bool.cond_true, tb_lor, Bool.or_eq_true] at h
      simp only [bin, Bool.cond_true, tb_lor]
      rcases h with h | h
      · rw [(hx.2.2 i hi).2 h j hj]; rfl
      · rw [(he.2.2 i hi).2 h j hj]; simp

lemma con_z (dd : Bool) (x e : El) (s a i : Nat) :
    con i ⟨a, s, zfl dd x e, ofl dd x e, 0, 0⟩ =
      (cond dd ((flg i x.zf && flg i e.zf) || (flg i x.of || flg i e.of))
        ((flg i x.zf || flg i e.zf) || (flg i x.of && flg i e.of))) := by
  cases dd <;> simp [con, zfl, ofl, flg, tb_land, tb_lor]

abbrev zEl (P : Par) (T : Nat) (dd : Bool) (x e : El) : El :=
  ⟨bin dd x.a e.a, sep P.full (decide (1 ≤ T)) (bin dd x.a e.a), zfl dd x e, ofl dd x e, 0, 0⟩
lemma cfl_nil (i : Nat) : cfl i [] = 0 := rfl
lemma cfl_one (i : Nat) (e : El) : cfl i [e] = b2n (con i e) := by rw [cfl_cons, cfl_nil]; rfl
lemma cfl_two (i : Nat) (x e : El) : cfl i [x, e] = b2n (con i x) + b2n (con i e) := by rw [cfl_cons, cfl_one]

-- the choice of a binary gate with newest operand x and partner e
structure Pick (P : Par) (n : Nat) (Λ : Nat → Nat) (B T : Nat) (v : Nat → Nat) (H : Finset Nat)
    (newer : List El) (x e : El) (dn ys : List El) (dd : Bool) (m : Mv) (ms' : List Mv) (U : Finset Nat) : Prop where
  rdy : Rdy P n Λ B T v (m :: ms') H (x :: e :: (newer ++ dn ++ ys))
  som : m.1 = some dd
  hop : ops m = {x.a, e.a}
  hrs : res P.top m = bin dd x.a e.a
  hS : (wd (x :: e :: (newer ++ dn ++ ys))).toFinset = ops m ∪ U
  hf : res P.top m ∉ H
  hg : good m
  hd : Dv P.top P.tgt ms' (insert (res P.top m) H) (insert (res P.top m) U)
  av : ∀ m' ∈ ms', ops m' ⊆ (wd (x :: e :: (newer ++ dn ++ ys))).toFinset → ∃ a ∈ ops m', a ∈ wd (x :: newer)

section Sec5
variable {P : Par} {n : Nat} {Λ : Nat → Nat} {B T : Nat} {v : Nat → Nat} {H : Finset Nat}
  {newer : List El} {x e : El} {dn ys : List El} {dd : Bool} {m : Mv} {ms' : List Mv} {U : Finset Nat}

lemma Pick.nbT (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) : nb ms' + 1 ≤ B ∧ nu ms' = T := by
  have h1 := h.rdy.hB; have h2 := h.rdy.hT
  simp only [nb, nu, List.countP_cons, h.som] at h1 h2 ⊢
  simp at h1 h2; exact ⟨h1, h2⟩

lemma Pick.restU (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (a : Nat) (ha : a ∈ wd (newer ++ dn ++ ys)) : a ∈ U := by
  have hS : a ∈ ops m ∪ U := by
    rw [← h.hS, List.mem_toFinset]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)
  rcases Finset.mem_union.mp hS with h1 | h1
  · exfalso
    rw [h.hop] at h1
    have nd := h.rdy.nd
    simp only [wd, List.map_cons, List.nodup_cons] at nd
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with rfl | rfl
    · exact nd.1 (List.mem_cons_of_mem _ ha)
    · exact nd.2.1 ha
  · exact h1

lemma Pick.memU (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (a : Nat) (ha : a ∈ U) :
    a = x.a ∨ a = e.a ∨ a ∈ wd (newer ++ dn ++ ys) := by
  have : a ∈ (wd (x :: e :: (newer ++ dn ++ ys))).toFinset := by rw [h.hS]; exact Finset.mem_union_right _ ha
  simpa [wd] using this

lemma Pick.cover (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ) (i : Nat)
    (hi : P.full.testBit i = true) :
    (sep P.full (decide (1 ≤ T)) (bin dd x.a e.a)).testBit i = true ∨
    (x.a ∈ U ∧ x.s.testBit i = true) ∨ (e.a ∈ U ∧ e.s.testBit i = true) ∨
    ∃ y ∈ newer ++ dn ++ ys, y.s.testBit i = true := by
  obtain ⟨a, ha, hb⟩ := h.hd.sep env.gd i hi
  rw [h.nbT.2] at hb
  rcases Finset.mem_insert.mp ha with rfl | hU
  · left; rw [← h.hrs]; exact hb
  · rcases h.memU a hU with rfl | rfl | hr
    · right; left; exact ⟨hU, by rw [h.rdy.sp x (by simp)]; exact hb⟩
    · right; right; left; exact ⟨hU, by rw [h.rdy.sp e (by simp)]; exact hb⟩
    · right; right; right
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
      exact ⟨y, hy, by rw [h.rdy.sp y (by simp at hy ⊢; tauto)]; exact hb⟩

lemma Pick.card (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) : (insert (res P.top m) U).card ≤ B := by
  have := h.hd.card; have := h.nbT.1; omega

lemma Pick.zU (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) : res P.top m ∉ U := fun hm =>
  h.hf (h.rdy.dv.sub (by rw [h.hS]; exact Finset.mem_union_right _ hm))

lemma sbit_full {P : Par} {d : Bool} {y : El} (h : y.s = sep P.full d y.a) {i : Nat} (hb : y.s.testBit i = true) :
    P.full.testBit i = true := by
  by_contra hn
  rw [h, sep_bit_off _ _ _ _ (by simpa using hn)] at hb; exact absurd hb (by decide)

lemma eq_full {X full : Nat} (h1 : ∀ i, full.testBit i = true → X.testBit i = true)
    (h2 : ∀ i, X.testBit i = true → full.testBit i = true) : X = full := by
  apply Nat.eq_of_testBit_eq; intro i
  cases h : full.testBit i
  · by_contra hn; have := h2 i (by simpa using hn); rw [h] at this; exact absurd this (by decide)
  · exact h1 i h

lemma Pick.child (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ)
    {dl lu act' old' : List El}
    (hp : (dl ++ lu).Perm (x :: e :: (newer ++ dn ++ ys))) (hlu : (wd lu).toFinset = U)
    (hp' : (act' ++ old').Perm
      (zEl P T dd x e :: lu))
    (hav : ∀ m' ∈ ms', ops m' ⊆ insert (res P.top m) U → ∃ a ∈ ops m', a ∈ wd act')
    (hdl : ∀ i, cfl i dl ≤ b2n (con i x) + b2n (con i e)) :
    (∀ i < n, 64 + b2n (con i x || con i e) +
        b2n (con i (zEl P T dd x e))
        ≤ v i + cfl i dl) ∧
    (∀ i < n, v i ≤ 126) ∧
    Inv P n Λ (fun y => y.s = sep P.full (decide (1 ≤ T)) y.a) (B - 1) T
      (encV n (fun i => v i - b2n (con i x || con i e) + cfl i dl -
        b2n (con i (zEl P T dd x e))))
      act' old' := by
  have hx := h.rdy.ok x (by simp)
  have he := h.rdy.ok e (by simp)
  have nt := h.nbT
  have := childInv (K := B + T) (B' := B - 1) (T' := T) (fr := fun i => con i x || con i e) (act' := act') (old' := old')
    (sk := fun y => y.s = sep P.full (decide (1 ≤ T)) y.a)
    (z := zEl P T dd x e)
    (dl := dl) (lu := lu)
    env h.hg h.hf h.rdy.dv.sub h.hS h.hd (by omega) nt.2 (by omega) h.rdy.nd h.rdy.ok h.rdy.jo
    h.hrs.symm (zOK hx he dd _) ?_ hp hlu hp' hav ?_ ?_ ?_
  · exact ⟨this.1, fun i hi => (h.rdy.jo i hi).2.1, this.2⟩
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rfl
    · exact h.rdy.sp y (hp.mem_iff.mp (List.mem_append_right _ hy))
  · intro i hi hc
    rw [h.hop]
    rcases Bool.or_eq_true_iff.mp hc with hc | hc
    · exact ⟨x.a, by simp, con_sound hx hi hc⟩
    · exact ⟨e.a, by simp, con_sound he hi hc⟩
  · intro i hi hc
    rw [con_z] at hc
    revert hc
    simp only [con]
    cases dd <;> cases flg i x.zf <;> cases flg i x.of <;> cases flg i e.zf <;> cases flg i e.of <;> simp
  · intro i hi
    refine (hdl i).trans ?_
    rw [con_z]
    simp only [con]
    cases dd <;> cases flg i x.zf <;> cases flg i x.of <;> cases flg i e.zf <;> cases flg i e.of <;> decide

end Sec5


section Sec6
variable {P : Par} {n : Nat} {Λ : Nat → Nat} {B T : Nat} {v : Nat → Nat} {H : Finset Nat}
  {newer : List El} {x e : El} {dn ys : List El} {dd : Bool} {m : Mv} {ms' : List Mv} {U : Finset Nat}

structure CtxOK (P : Par) (n : Nat) (Λ : Nat → Nat) (B T : Nat) (v : Nat → Nat) (N : Nat) (c : Ctx) : Prop where
  eP : c.P = P
  d : c.d = decide (1 ≤ T)
  t : c.t = T
  k : c.k = B + 1 - N
  R : c.R = encV n v
  ch : ∀ R a o, Inv P n Λ (fun y => y.s = sep P.full (decide (1 ≤ T)) y.a) (B - 1) T R a o → c.ch R a o = true

lemma wd_fin (l : List El) (a : Nat) : a ∈ (wd l).toFinset ↔ a ∈ wd l := List.mem_toFinset

lemma Pick.fin_true (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ) (c : Ctx)
    (hc : CtxOK P n Λ B T v (x :: e :: (newer ++ dn ++ ys)).length c) (acc R0 R1 : Nat)
    (hR0 : ∀ i, R0.testBit i = true ↔ ∃ y ∈ newer ++ dn ++ ys, y.s.testBit i = true)
    (hR1 : R1 = Nat.lor R0 (sep P.full (decide (1 ≤ T)) (bin dd x.a e.a))) :
    fin c ⟨newer, acc, x, e, dn, ys⟩ (zEl P T dd x e) R1 = true := by
  have hx := h.rdy.ok x (by simp)
  have he := h.rdy.ok e (by simp)
  have nd := h.rdy.nd
  have hxe : x.a ≠ e.a := by
    intro h'; simp only [wd, List.map_cons, List.nodup_cons] at nd
    exact nd.1 (by rw [h']; simp)
  have hxr : x.a ∉ wd (newer ++ dn ++ ys) := by
    intro h'; simp only [wd, List.map_cons, List.nodup_cons] at nd
    exact nd.1 (List.mem_cons_of_mem _ h')
  have her : e.a ∉ wd (newer ++ dn ++ ys) := by
    intro h'; simp only [wd, List.map_cons, List.nodup_cons] at nd
    exact nd.2.1 h'
  have hz : EOK n Λ (zEl P T dd x e) := zOK hx he dd _
  have hbase : base c ⟨newer, acc, x, e, dn, ys⟩ = Nat.sub (encV n v) (encV n (fun i => b2n (con i x || con i e))) := by
    unfold base; rw [hc.R]; exact congrArg _ (base_enc hx he)
  have hfr : ∀ i < n, b2n (con i x || con i e) ≤ v i := fun i hi => by
    have := (h.rdy.jo i hi).1; have := b2n_le (con i x || con i e); omega
  rw [encV_sub _ _ _ hfr] at hbase
  have hR1bit : ∀ i, R1.testBit i = true ↔ (∃ y ∈ newer ++ dn ++ ys, y.s.testBit i = true) ∨
      (sep P.full (decide (1 ≤ T)) (bin dd x.a e.a)).testBit i = true := by
    intro i; rw [hR1, tb_lor, Bool.or_eq_true, hR0]
  have hR1full : ∀ i, R1.testBit i = true → P.full.testBit i = true := by
    intro i hb
    rcases (hR1bit i).mp hb with ⟨y, hy, hb⟩ | hb
    · exact sbit_full (h.rdy.sp y (by simp at hy ⊢; tauto)) hb
    · by_contra hn; rw [sep_bit_off _ _ _ _ (by simpa using hn)] at hb; exact absurd hb (by decide)
  have hsx : ∀ i, x.s.testBit i = true → P.full.testBit i = true := fun i hb => sbit_full (h.rdy.sp x (by simp)) hb
  have hse : ∀ i, e.s.testBit i = true → P.full.testBit i = true := fun i hb => sbit_full (h.rdy.sp e (by simp)) hb
  have hnew : ∀ m' ∈ ms', ops m' ⊆ insert (res P.top m) U → ∃ a ∈ ops m', a = bin dd x.a e.a ∨ (a ∈ U ∧ a ∈ wd (x :: newer)) := by
    intro m' hm' hs
    by_cases hzm : res P.top m ∈ ops m'
    · exact ⟨_, hzm, Or.inl h.hrs⟩
    · have hsU : ops m' ⊆ U := fun a ha => (Finset.mem_insert.mp (hs ha)).resolve_left (fun e => hzm (e ▸ ha))
      obtain ⟨a, ha, hw⟩ := h.av m' hm' (by rw [h.hS]; exact hsU.trans Finset.subset_union_right)
      exact ⟨a, ha, Or.inr ⟨hsU ha, hw⟩⟩
  have hUset : ∀ a, a ∈ U ↔ (a = x.a ∧ x.a ∈ U) ∨ (a = e.a ∧ e.a ∈ U) ∨ a ∈ wd (newer ++ dn ++ ys) := by
    intro a
    constructor
    · intro ha
      rcases h.memU a ha with rfl | rfl | hr
      · exact Or.inl ⟨rfl, ha⟩
      · exact Or.inr (Or.inl ⟨rfl, ha⟩)
      · exact Or.inr (Or.inr hr)
    · rintro (⟨rfl, ha⟩ | ⟨rfl, ha⟩ | ha)
      · exact ha
      · exact ha
      · exact h.restU a ha
  have hcard := h.card
  rw [Finset.card_insert_of_notMem h.zU] at hcard
  have hlen : (x :: e :: (newer ++ dn ++ ys)).length = (newer ++ dn ++ ys).length + 2 := rfl
  have hrn : (wd (newer ++ dn ++ ys)).Nodup := by
    simp only [wd, List.map_cons, List.nodup_cons] at nd; exact nd.2.2
  have hcu : ∀ (extra : List El), (wd (extra ++ (newer ++ dn ++ ys))).Nodup →
      (wd (extra ++ (newer ++ dn ++ ys))).toFinset = U → U.card = extra.length + (newer ++ dn ++ ys).length := by
    intro extra hn hU
    rw [← hU, List.toFinset_card_of_nodup hn]; simp only [wd, List.length_map, List.length_append]
  by_cases hxU : x.a ∈ U
  · by_cases heU : e.a ∈ U
    · -- keep both
      have hU : (wd ([x, e] ++ (newer ++ dn ++ ys))).toFinset = U := by
        ext a; rw [hUset, wd_fin]; simp [wd, hxU, heU]
      have hk : 2 ≤ c.k := by
        have := hcu [x, e] nd hU
        rw [hc.k, hlen]; simp only [List.length_cons, List.length_nil] at this; omega
      have hp' : ((zEl P T dd x e :: x :: newer) ++ (dn ++ e :: ys)).Perm
          (zEl P T dd x e :: ([x, e] ++ (newer ++ dn ++ ys))) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
        refine ((List.Perm.trans ?_ (List.perm_middle (a := e) (l₁ := newer ++ dn) (l₂ := ys) |>.trans (by simp))).cons _).cons _
        simp
      obtain ⟨c1, c2, c3⟩ := h.child env (dl := []) (lu := [x, e] ++ (newer ++ dn ++ ys))
        (act' := zEl P T dd x e :: x :: newer) (old' := dn ++ e :: ys) (by simp) hU hp' (by
          intro m' hm' hs
          obtain ⟨a, ha, h1 | ⟨_, h2⟩⟩ := hnew m' hm' hs
          · exact ⟨a, ha, by rw [h1]; simp [wd]⟩
          · exact ⟨a, ha, List.mem_cons_of_mem _ h2⟩) (by intro i; simp only [cfl_nil]; omega)
      have : fin2 c ⟨newer, acc, x, e, dn, ys⟩ (zEl P T dd x e) = true := by
        unfold fin2; rw [bAnd]
        refine ball_and (Nat.ble_eq.mpr hk) (kid_true env c hc.eP hbase hz (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (hc.ch _ _ _ c3))
        · have h1 := c1 i hi; have h2 := hfr i hi; simp only [cfl_nil] at h1; beta_reduce; omega
        · have := c2 i hi; beta_reduce; omega
        · simp only [cfl_nil, Nat.add_zero]
      unfold fin fin1 finX finY
      simp only [bOr, bAnd]
      exact bor_r (ball_and (Nat.ble_eq.mpr (by omega)) (bor_r (bor_r this)))
    · -- keep x
      have hU : (wd ([x] ++ (newer ++ dn ++ ys))).toFinset = U := by
        ext a; rw [hUset, wd_fin]; simp [wd, hxU, heU]
      have hk : 1 ≤ c.k := by
        have := hcu [x] (by simp only [wd, List.cons_append, List.nil_append, List.map_cons, List.nodup_cons]; exact ⟨hxr, hrn⟩) hU
        rw [hc.k, hlen]; simp only [List.length_cons, List.length_nil] at this; omega
      have hcov : Nat.lor R1 x.s = P.full := by
        apply eq_full
        · intro i hi
          rw [tb_lor, Bool.or_eq_true, hR1bit]
          rcases h.cover env i hi with h1 | ⟨_, h1⟩ | ⟨h1, _⟩ | h1
          · exact Or.inl (Or.inr h1)
          · exact Or.inr h1
          · exact absurd h1 heU
          · exact Or.inl (Or.inl h1)
        · intro i hb; rw [tb_lor, Bool.or_eq_true] at hb
          exact hb.elim (hR1full i) (hsx i)
      obtain ⟨c1, c2, c3⟩ := h.child env (dl := [e]) (lu := [x] ++ (newer ++ dn ++ ys))
        (act' := zEl P T dd x e :: x :: newer) (old' := dn ++ ys) (List.Perm.swap _ _ _) hU (by simp) (by
          intro m' hm' hs
          obtain ⟨a, ha, h1 | ⟨_, h2⟩⟩ := hnew m' hm' hs
          · exact ⟨a, ha, by rw [h1]; simp [wd]⟩
          · exact ⟨a, ha, List.mem_cons_of_mem _ h2⟩) (by intro i; simp only [cfl_one, cfl_two]; omega)
      have hkid : kid c (Nat.add (base c ⟨newer, acc, x, e, dn, ys⟩) (cf e)) (zEl P T dd x e) (x :: newer) dn ys = true := by
        refine kid_true env c hc.eP (v := fun i => v i - b2n (con i x || con i e) + b2n (con i e)) ?_ hz
          (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (hc.ch _ _ _ c3)
        · rw [hbase, cf_enc he, encV_add]
        · have h1 := c1 i hi; have h2 := hfr i hi; simp only [cfl_one, cfl_two] at h1; beta_reduce; omega
        · have := c2 i hi; have := b2n_le (con i e)
          have : b2n (con i e) ≤ b2n (con i x || con i e) := by cases con i x <;> cases con i e <;> decide
          have := (h.rdy.jo i hi).1; have := hfr i hi
          beta_reduce; omega
        · simp only [cfl_one, cfl_two]
      unfold fin fin1 finX
      simp only [bOr, bAnd]
      exact bor_r (ball_and (Nat.ble_eq.mpr hk) (bor_l (ball_and (Nat.beq_eq.mpr (by rw [hc.eP]; exact hcov)) hkid)))
  · by_cases heU : e.a ∈ U
    · -- keep e
      have hU : (wd ([e] ++ (newer ++ dn ++ ys))).toFinset = U := by
        ext a; rw [hUset, wd_fin]; simp [wd, hxU, heU]
      have hk : 1 ≤ c.k := by
        have := hcu [e] (by simp only [wd, List.cons_append, List.nil_append, List.map_cons, List.nodup_cons]; exact ⟨her, hrn⟩) hU
        rw [hc.k, hlen]; simp only [List.length_cons, List.length_nil] at this; omega
      have hcov : Nat.lor R1 e.s = P.full := by
        apply eq_full
        · intro i hi
          rw [tb_lor, Bool.or_eq_true, hR1bit]
          rcases h.cover env i hi with h1 | ⟨h1, _⟩ | ⟨_, h1⟩ | h1
          · exact Or.inl (Or.inr h1)
          · exact absurd h1 hxU
          · exact Or.inr h1
          · exact Or.inl (Or.inl h1)
        · intro i hb; rw [tb_lor, Bool.or_eq_true] at hb
          exact hb.elim (hR1full i) (hse i)
      have hp' : ((zEl P T dd x e :: newer) ++ (dn ++ e :: ys)).Perm
          (zEl P T dd x e :: ([e] ++ (newer ++ dn ++ ys))) := by
        simp only [List.cons_append, List.nil_append, List.append_assoc]
        refine (List.Perm.trans ?_ (List.perm_middle (a := e) (l₁ := newer ++ dn) (l₂ := ys) |>.trans (by simp))).cons _
        simp
      obtain ⟨c1, c2, c3⟩ := h.child env (dl := [x]) (lu := [e] ++ (newer ++ dn ++ ys))
        (act' := zEl P T dd x e :: newer) (old' := dn ++ e :: ys) (by simp) hU hp' (by
          intro m' hm' hs
          obtain ⟨a, ha, h1 | ⟨h3, h2⟩⟩ := hnew m' hm' hs
          · exact ⟨a, ha, by rw [h1]; simp [wd]⟩
          · refine ⟨a, ha, List.mem_cons_of_mem _ ?_⟩
            rcases List.mem_cons.mp h2 with rfl | h2
            · exact absurd h3 hxU
            · exact h2) (by intro i; simp only [cfl_one, cfl_two]; omega)
      have hkid : kid c (Nat.add (base c ⟨newer, acc, x, e, dn, ys⟩) (cf x)) (zEl P T dd x e) newer dn (e :: ys) = true := by
        refine kid_true env c hc.eP (v := fun i => v i - b2n (con i x || con i e) + b2n (con i x)) ?_ hz
          (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (hc.ch _ _ _ c3)
        · rw [hbase, cf_enc hx, encV_add]
        · have h1 := c1 i hi; have h2 := hfr i hi; simp only [cfl_one, cfl_two] at h1; beta_reduce; omega
        · have := c2 i hi; have := b2n_le (con i x)
          have : b2n (con i x) ≤ b2n (con i x || con i e) := by cases con i x <;> cases con i e <;> decide
          have := (h.rdy.jo i hi).1; have := hfr i hi
          beta_reduce; omega
        · simp only [cfl_one, cfl_two]
      unfold fin fin1 finX finY
      simp only [bOr, bAnd]
      exact bor_r (ball_and (Nat.ble_eq.mpr hk) (bor_r (bor_l (ball_and (Nat.beq_eq.mpr (by rw [hc.eP]; exact hcov)) hkid))))
    · -- drop both
      have hU : (wd (newer ++ dn ++ ys)).toFinset = U := by
        ext a; rw [hUset, wd_fin]; simp [hxU, heU]
      have hcov : R1 = P.full := by
        apply eq_full _ hR1full
        intro i hi
        rw [hR1bit]
        rcases h.cover env i hi with h1 | ⟨h1, _⟩ | ⟨h1, _⟩ | h1
        · exact Or.inr h1
        · exact absurd h1 hxU
        · exact absurd h1 heU
        · exact Or.inl h1
      obtain ⟨c1, c2, c3⟩ := h.child env (dl := [x, e]) (lu := newer ++ dn ++ ys)
        (act' := zEl P T dd x e :: newer) (old' := dn ++ ys) (by simp) hU (by simp) (by
          intro m' hm' hs
          obtain ⟨a, ha, h1 | ⟨h3, h2⟩⟩ := hnew m' hm' hs
          · exact ⟨a, ha, by rw [h1]; simp [wd]⟩
          · refine ⟨a, ha, List.mem_cons_of_mem _ ?_⟩
            rcases List.mem_cons.mp h2 with rfl | h2
            · exact absurd h3 hxU
            · exact h2) (by intro i; simp only [cfl_one, cfl_two]; omega)
      have hkid : kid c (Nat.add (base c ⟨newer, acc, x, e, dn, ys⟩) (Nat.add (cf x) (cf e))) (zEl P T dd x e) newer dn ys = true := by
        refine kid_true env c hc.eP (v := fun i => v i - b2n (con i x || con i e) + (b2n (con i x) + b2n (con i e))) ?_ hz
          (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (hc.ch _ _ _ c3)
        · rw [hbase, cf_enc hx, cf_enc he, encV_add, encV_add]
        · have h1 := c1 i hi; have h2 := hfr i hi; simp only [cfl_one, cfl_two] at h1; beta_reduce; omega
        · have := c2 i hi; have := b2n_le (con i x); have := b2n_le (con i e)
          have h9 : b2n (con i x) + b2n (con i e) ≤ 1 + b2n (con i x || con i e) := by cases con i x <;> cases con i e <;> decide
          have := (h.rdy.jo i hi).1; have := hfr i hi
          beta_reduce; omega
        · simp only [cfl_one, cfl_two]
      unfold fin
      simp only [bOr, bAnd]
      exact bor_l (ball_and (Nat.beq_eq.mpr (by rw [hc.eP]; exact hcov)) hkid)

end Sec6


lemma mk_eq (a s zf of : Nat) (k : El → Bool) : PEqualNP.Outside.L_meta_3624.mk a s zf of k = k ⟨a, s, zf, of, 0, 0⟩ := by
  change force zf (fun zf => force of fun of => k ⟨a, s, zf, of, 0, 0⟩) = _
  rw [force_eq, force_eq]

section Sec7
variable {P : Par} {n : Nat} {Λ : Nat → Nat} {B T : Nat} {v : Nat → Nat} {H : Finset Nat}
  {newer : List El} {x e : El} {dn ys : List El} {dd : Bool} {m : Mv} {ms' : List Mv} {U : Finset Nat}

lemma Pick.kx (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (hx : x.a ∈ U) :
    1 ≤ B + 1 - (x :: e :: (newer ++ dn ++ ys)).length := by
  have hcard := h.card
  rw [Finset.card_insert_of_notMem h.zU] at hcard
  have nd := h.rdy.nd
  simp only [wd, List.map_cons, List.nodup_cons] at nd
  have hn : (x.a :: wd (newer ++ dn ++ ys)).Nodup :=
    List.nodup_cons.mpr ⟨fun h' => nd.1 (List.mem_cons_of_mem _ h'), nd.2.2⟩
  have hs : (x.a :: wd (newer ++ dn ++ ys)).toFinset ⊆ U := by
    intro a ha; rw [List.mem_toFinset] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hx
    · exact h.restU a ha
  have := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hn] at this
  simp only [List.length_cons, wd, List.length_map] at this ⊢; omega
lemma Pick.ke (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (he : e.a ∈ U) :
    1 ≤ B + 1 - (x :: e :: (newer ++ dn ++ ys)).length := by
  have hcard := h.card
  rw [Finset.card_insert_of_notMem h.zU] at hcard
  have nd := h.rdy.nd
  simp only [wd, List.map_cons, List.nodup_cons] at nd
  have hn : (e.a :: wd (newer ++ dn ++ ys)).Nodup := List.nodup_cons.mpr ⟨nd.2.1, nd.2.2⟩
  have hs : (e.a :: wd (newer ++ dn ++ ys)).toFinset ⊆ U := by
    intro a ha; rw [List.mem_toFinset] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he
    · exact h.restU a ha
  have := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hn] at this
  simp only [List.length_cons, wd, List.length_map] at this ⊢; omega
lemma Pick.kxe (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (hx : x.a ∈ U) (he : e.a ∈ U) :
    2 ≤ B + 1 - (x :: e :: (newer ++ dn ++ ys)).length := by
  have hcard := h.card
  rw [Finset.card_insert_of_notMem h.zU] at hcard
  have hs : (wd (x :: e :: (newer ++ dn ++ ys))).toFinset ⊆ U := by
    intro a ha; rw [List.mem_toFinset] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hx
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he
    · exact h.restU a ha
  have := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup h.rdy.nd] at this
  simp only [List.length_cons, wd, List.length_map] at this ⊢; omega

lemma Pick.ux (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ) (hx : x.a ∉ U) (i : Nat)
    (h1 : x.s.testBit i = true) (h2 : e.s.testBit i = false) (h3 : ∀ y ∈ newer ++ dn ++ ys, y.s.testBit i = false) :
    e.a.testBit i = !dd := by
  have hi := sbit_full (h.rdy.sp x (by simp)) h1
  rcases h.cover env i hi with hz | ⟨h', _⟩ | ⟨_, h'⟩ | ⟨y, hy, h'⟩
  · rw [h.rdy.sp x (by simp), sep_bit _ _ _ _ hi] at h1
    rw [h.rdy.sp e (by simp), sep_bit _ _ _ _ hi] at h2
    rw [sep_bit _ _ _ _ hi] at hz
    revert h1 h2 hz
    cases dd <;> simp only [bin, Bool.cond_true, Bool.cond_false, tb_land, tb_lor] <;>
      by_cases hT : 1 ≤ T <;> simp only [hT, decide_true, decide_false] <;>
      cases x.a.testBit i <;> cases x.a.testBit (402 + i) <;> cases e.a.testBit i <;>
      cases e.a.testBit (402 + i) <;> simp
  · exact absurd h' hx
  · rw [h2] at h'; exact absurd h' (by decide)
  · rw [h3 y hy] at h'; exact absurd h' (by decide)

lemma Pick.ue (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ) (he : e.a ∉ U) (i : Nat)
    (h1 : e.s.testBit i = true) (h2 : x.s.testBit i = false) (h3 : ∀ y ∈ newer ++ dn ++ ys, y.s.testBit i = false) :
    x.a.testBit i = !dd := by
  have hi := sbit_full (h.rdy.sp e (by simp)) h1
  rcases h.cover env i hi with hz | ⟨_, h'⟩ | ⟨h', _⟩ | ⟨y, hy, h'⟩
  · rw [h.rdy.sp e (by simp), sep_bit _ _ _ _ hi] at h1
    rw [h.rdy.sp x (by simp), sep_bit _ _ _ _ hi] at h2
    rw [sep_bit _ _ _ _ hi] at hz
    revert h1 h2 hz
    cases dd <;> simp only [bin, Bool.cond_true, Bool.cond_false, tb_land, tb_lor] <;>
      by_cases hT : 1 ≤ T <;> simp only [hT, decide_true, decide_false] <;>
      cases x.a.testBit i <;> cases x.a.testBit (402 + i) <;> cases e.a.testBit i <;>
      cases e.a.testBit (402 + i) <;> simp
  · rw [h2] at h'; exact absurd h' (by decide)
  · exact absurd h' he
  · rw [h3 y hy] at h'; exact absurd h' (by decide)

lemma Pick.hand_true (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ) (c : Ctx)
    (hc : CtxOK P n Λ B T v (x :: e :: (newer ++ dn ++ ys)).length c) (hall : ∀ a ∈ wd c.all, a ∈ H) (acc R0 : Nat)
    (hR0 : ∀ i, R0.testBit i = true ↔ ∃ y ∈ newer ++ dn ++ ys, y.s.testBit i = true) :
    (cond dd (hO c ⟨newer, acc, x, e, dn, ys⟩ R0) (hA c ⟨newer, acc, x, e, dn, ys⟩ R0)) = true := by
  have e1 : (cond dd (hO c ⟨newer, acc, x, e, dn, ys⟩ R0) (hA c ⟨newer, acc, x, e, dn, ys⟩ R0)) =
      hand c ⟨newer, acc, x, e, dn, ys⟩ R0 (bin dd x.a e.a) (zfl dd x e) (ofl dd x e) := by
    cases dd <;> rfl
  rw [e1]
  unfold hand
  rw [force_eq, force_eq, force_eq]
  have hfin := h.fin_true env c hc acc R0 _ hR0 rfl
  rw [hc.eP, hc.d]
  set R1 := Nat.lor R0 (sep P.full (decide (1 ≤ T)) (bin dd x.a e.a)) with hR1
  have hhas : has (bin dd x.a e.a) c.all = false := by
    by_contra hn
    have := (has_eq _ _).mp (by simpa using hn)
    exact h.hf (by rw [h.hrs]; exact hall _ this)
  have h2 : hand2 c ⟨newer, acc, x, e, dn, ys⟩ (bin dd x.a e.a) (sep P.full (decide (1 ≤ T)) (bin dd x.a e.a))
      (zfl dd x e) (ofl dd x e) R1 = true := by
    unfold hand2; rw [bNot, hhas, mk_eq]; exact hfin
  unfold hand3
  simp only [bOr, bAnd, hc.eP]
  by_cases hk : 1 ≤ c.k
  · apply bor_r
    refine ball_and (Nat.ble_eq.mpr hk) (ball_and (Nat.beq_eq.mpr ?_) h2)
    apply eq_full
    · intro i hi
      simp only [tb_lor, Bool.or_eq_true, hR1, hR0]
      rcases h.cover env i hi with h1 | ⟨_, h1⟩ | ⟨_, h1⟩ | h1
      · exact Or.inl (Or.inr h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
      · exact Or.inl (Or.inl h1)
    · intro i hb
      simp only [tb_lor, Bool.or_eq_true, hR1, hR0] at hb
      rcases hb with (⟨y, hy, hb⟩ | hb) | hb | hb
      · exact sbit_full (h.rdy.sp y (by simp at hy ⊢; tauto)) hb
      · by_contra hn; rw [sep_bit_off _ _ _ _ (by simpa using hn)] at hb; exact absurd hb (by decide)
      · exact sbit_full (h.rdy.sp x (by simp)) hb
      · exact sbit_full (h.rdy.sp e (by simp)) hb
  · apply bor_l
    refine ball_and ?_ h2
    have h3 := hfin
    unfold fin fin1 at h3
    simp only [bOr, bAnd, hc.eP] at h3
    have h0 : Nat.ble 1 c.k = false := by
      by_contra hn; exact hk (Nat.ble_eq.mp (by simpa using hn))
    rw [h0, Bool.false_and, Bool.or_false, Bool.and_eq_true] at h3
    exact h3.1

-- bits unique to one entry
def Uq (u s : Nat) (others : List El) : Prop :=
  ∀ i, u.testBit i = true → s.testBit i = true ∧ ∀ y ∈ others, y.s.testBit i = false

lemma land_eq_left {u a : Nat} (h : ∀ i, u.testBit i = true → a.testBit i = true) : Nat.land u a = u := by
  apply Nat.eq_of_testBit_eq; intro i; rw [tb_land]
  cases hu : u.testBit i
  · rfl
  · rw [h i hu]; rfl
lemma land_eq_zero {u a : Nat} (h : ∀ i, u.testBit i = true → a.testBit i = false) : Nat.land u a = 0 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [tb_land]
  cases hu : u.testBit i
  · simp
  · rw [h i hu]; simp

lemma Pick.cx (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ) (hx : x.a ∉ U)
    (hu : Uq x.u x.s (e :: (newer ++ dn ++ ys))) :
    Nat.land x.u e.a = cond dd 0 x.u := by
  have := fun i hi => h.ux env hx i (hu i hi).1 ((hu i hi).2 e (by simp)) (fun y hy => (hu i hi).2 y (List.mem_cons_of_mem _ hy))
  cases dd
  · exact land_eq_left this
  · exact land_eq_zero this
lemma Pick.ce (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ) (he : e.a ∉ U)
    (hu : Uq e.u e.s (x :: (newer ++ dn ++ ys))) :
    Nat.land e.u x.a = cond dd 0 e.u := by
  have := fun i hi => h.ue env he i (hu i hi).1 ((hu i hi).2 x (by simp)) (fun y hy => (hu i hi).2 y (List.mem_cons_of_mem _ hy))
  cases dd
  · exact land_eq_left this
  · exact land_eq_zero this

lemma Pick.f0_true (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ) (c : Ctx)
    (hc : CtxOK P n Λ B T v (x :: e :: (newer ++ dn ++ ys)).length c) (hall : ∀ a ∈ wd c.all, a ∈ H) (acc : Nat)
    (hk : c.k = 0) (hux : Uq x.u x.s (e :: (newer ++ dn ++ ys))) (hue : Uq e.u e.s (x :: (newer ++ dn ++ ys)))
    (hacc : ∀ i, acc.testBit i = true ↔ ∃ y ∈ newer, y.s.testBit i = true)
    (hef : ∀ i, e.f.testBit i = true ↔ ∃ y ∈ ys, y.s.testBit i = true) :
    Nat.mul (Nat.land x.u e.a) (Nat.sub x.u (Nat.land x.u e.a)) = 0 ∧
    f0 c ⟨newer, acc, x, e, dn, ys⟩ (Nat.land x.u e.a) = true := by
  have hxU : x.a ∉ U := fun h' => by have := h.kx h'; rw [← hc.k, hk] at this; omega
  have heU : e.a ∉ U := fun h' => by have := h.ke h'; rw [← hc.k, hk] at this; omega
  have hcx := h.cx env hxU hux
  have hce := h.ce env heU hue
  have hR0 : ∀ i, (Nat.lor (seps dn acc) e.f).testBit i = true ↔ ∃ y ∈ newer ++ dn ++ ys, y.s.testBit i = true := by
    intro i; rw [tb_lor, Bool.or_eq_true, seps_bit, hacc, hef]
    constructor
    · rintro ((⟨y, hy, hb⟩ | ⟨y, hy, hb⟩) | ⟨y, hy, hb⟩) <;> exact ⟨y, by simp [hy], hb⟩
    · rintro ⟨y, hy, hb⟩
      simp only [List.mem_append] at hy
      rcases hy with (hy | hy) | hy
      · exact Or.inl (Or.inl ⟨y, hy, hb⟩)
      · exact Or.inl (Or.inr ⟨y, hy, hb⟩)
      · exact Or.inr ⟨y, hy, hb⟩
  have hh := h.hand_true env c hc hall acc _ hR0
  unfold f0
  simp only [bOr, bAnd]
  rw [hcx, hce]
  cases dd
  · exact ⟨by simp, bor_l (ball_and (Nat.beq_eq.mpr rfl) (ball_and (Nat.beq_eq.mpr rfl) hh))⟩
  · exact ⟨by simp, bor_r (ball_and (Nat.beq_eq.mpr rfl) (ball_and (Nat.beq_eq.mpr rfl) hh))⟩

lemma Pick.f1_true (h : Pick P n Λ B T v H newer x e dn ys dd m ms' U) (env : Env P n Λ) (c : Ctx)
    (hc : CtxOK P n Λ B T v (x :: e :: (newer ++ dn ++ ys)).length c) (hall : ∀ a ∈ wd c.all, a ∈ H) (acc R0 : Nat)
    (hk : c.k = 1) (hux : Uq x.u x.s (e :: (newer ++ dn ++ ys))) (hue : Uq e.u e.s (x :: (newer ++ dn ++ ys)))
    (hR0 : ∀ i, R0.testBit i = true ↔ ∃ y ∈ newer ++ dn ++ ys, y.s.testBit i = true) :
    f1 c ⟨newer, acc, x, e, dn, ys⟩ R0 (Nat.land x.u e.a) (Nat.land e.u x.a) = true := by
  have hor : x.a ∉ U ∨ e.a ∉ U := by
    by_contra hn; push Not at hn
    have := h.kxe hn.1 hn.2; rw [← hc.k, hk] at this; omega
  have hh := h.hand_true env c hc hall acc _ hR0
  unfold f1
  simp only [bOr, bAnd]
  rcases hor with hxU | heU
  · rw [h.cx env hxU hux]
    cases dd
    · exact bor_l (ball_and (bor_l (Nat.beq_eq.mpr rfl)) hh)
    · exact bor_r (ball_and (bor_l (Nat.beq_eq.mpr rfl)) hh)
  · rw [h.ce env heU hue]
    cases dd
    · exact bor_l (ball_and (bor_r (Nat.beq_eq.mpr rfl)) hh)
    · exact bor_r (ball_and (bor_r (Nat.beq_eq.mpr rfl)) hh)
end Sec7

lemma l0_cons (c : Ctx) (newer : List El) (acc : Nat) (x : El) (ux : Nat) (e : El) (ys dn : List El) :
    l0 c newer acc x ux (e :: ys) dn =
      ((Nat.beq (Nat.mul (Nat.land ux e.a) (Nat.sub ux (Nat.land ux e.a))) 0 &&
        f0 c ⟨newer, acc, x, e, dn, ys⟩ (Nat.land ux e.a)) || l0 c newer acc x ux ys (e :: dn)) := by
  rw [← bAnd, ← bOr]; rfl
lemma l1_cons (c : Ctx) (newer : List El) (x e : El) (ys : List El) (acc : Nat) (dn : List El) :
    l1 c newer x (e :: ys) acc dn =
      (f1 c ⟨newer, acc, x, e, dn, ys⟩ (Nat.lor acc e.f) (Nat.land x.u e.a) (Nat.land e.u x.a) ||
        l1 c newer x ys (Nat.lor acc e.s) (e :: dn)) := by
  rw [← bOr, ← force_eq (Nat.lor acc e.s) (fun acc => l1 c newer x ys acc (e :: dn))]; rfl
lemma l2_cons (c : Ctx) (newer : List El) (x e : El) (ys : List El) (acc : Nat) (dn : List El) :
    l2 c newer x (e :: ys) acc dn =
      (hA c ⟨newer, acc, x, e, dn, ys⟩ (Nat.lor acc e.f) ||
        (hO c ⟨newer, acc, x, e, dn, ys⟩ (Nat.lor acc e.f) || l2 c newer x ys (Nat.lor acc e.s) (e :: dn))) := by
  rw [← bOr, ← bOr, ← force_eq (Nat.lor acc e.s) (fun acc => l2 c newer x ys acc (e :: dn))]; rfl

lemma l0_split (c : Ctx) (newer : List El) (acc : Nat) (x : El) (ux : Nat) (e : El) (ys : List El) (pre : List El) : ∀ dn,
    (Nat.mul (Nat.land ux e.a) (Nat.sub ux (Nat.land ux e.a)) = 0 ∧
      f0 c ⟨newer, acc, x, e, pre.reverse ++ dn, ys⟩ (Nat.land ux e.a) = true) →
    l0 c newer acc x ux (pre ++ e :: ys) dn = true := by
  induction pre with
  | nil => intro dn h; rw [List.nil_append, l0_cons]; exact bor_l (ball_and (Nat.beq_eq.mpr h.1) h.2)
  | cons y pre ih =>
    intro dn h
    rw [List.cons_append, l0_cons]
    apply bor_r; apply ih
    simpa using h
lemma acc_step {acc : Nat} {y : El} {pre : List El} {acc' : Nat}
    (h : ∀ i, acc'.testBit i = true ↔ (Nat.lor acc y.s).testBit i = true ∨ ∃ z ∈ pre, z.s.testBit i = true) :
    ∀ i, acc'.testBit i = true ↔ acc.testBit i = true ∨ ∃ z ∈ y :: pre, z.s.testBit i = true := by
  intro i; rw [h, tb_lor, Bool.or_eq_true]; simp only [List.mem_cons, exists_eq_or_imp]; tauto
lemma l1_split (c : Ctx) (newer : List El) (x e : El) (ys : List El) (pre : List El) : ∀ acc dn,
    (∀ acc', (∀ i, acc'.testBit i = true ↔ acc.testBit i = true ∨ ∃ z ∈ pre, z.s.testBit i = true) →
      f1 c ⟨newer, acc', x, e, pre.reverse ++ dn, ys⟩ (Nat.lor acc' e.f) (Nat.land x.u e.a) (Nat.land e.u x.a) = true) →
    l1 c newer x (pre ++ e :: ys) acc dn = true := by
  induction pre with
  | nil => intro acc dn h; rw [List.nil_append, l1_cons]; exact bor_l (h acc (by simp))
  | cons y pre ih =>
    intro acc dn h
    rw [List.cons_append, l1_cons]
    apply bor_r; apply ih
    intro acc' h'
    have := h acc' (acc_step h')
    simpa using this
lemma l2_split (c : Ctx) (newer : List El) (x e : El) (ys : List El) (pre : List El) : ∀ acc dn,
    (∀ acc', (∀ i, acc'.testBit i = true ↔ acc.testBit i = true ∨ ∃ z ∈ pre, z.s.testBit i = true) →
      (hA c ⟨newer, acc', x, e, pre.reverse ++ dn, ys⟩ (Nat.lor acc' e.f) = true ∨
       hO c ⟨newer, acc', x, e, pre.reverse ++ dn, ys⟩ (Nat.lor acc' e.f) = true)) →
    l2 c newer x (pre ++ e :: ys) acc dn = true := by
  induction pre with
  | nil =>
    intro acc dn h; rw [List.nil_append, l2_cons]
    rcases h acc (by simp) with h | h
    · exact bor_l h
    · exact bor_r (bor_l h)
  | cons y pre ih =>
    intro acc dn h
    rw [List.cons_append, l2_cons]
    apply bor_r; apply bor_r; apply ih
    intro acc' h'
    have := h acc' (acc_step h')
    simpa using this

lemma Ents_split (pre r : List El) : ∀ acc, Ents acc (pre ++ r) →
    ∃ acc', (∀ i, acc'.testBit i = true ↔ acc.testBit i = true ∨ ∃ z ∈ pre, z.s.testBit i = true) ∧ Ents acc' r := by
  induction pre with
  | nil => intro acc h; exact ⟨acc, by simp, h⟩
  | cons y pre ih =>
    intro acc h
    obtain ⟨acc', h1, h2⟩ := ih _ h.2.2
    exact ⟨acc', acc_step h1, h2⟩

lemma uq_of {acc : Nat} {e : El} {l others : List El} (h : Ents acc (e :: l))
    (ho : ∀ y ∈ others, (∀ i, y.s.testBit i = true → acc.testBit i = true) ∨ y ∈ l) : Uq e.u e.s others := by
  intro i hi
  rw [h.2.1, tb_xor, tb_land, tb_lor, h.1] at hi
  have h1 : e.s.testBit i = true := by
    by_contra hn; simp [hn] at hi
  refine ⟨h1, fun y hy => ?_⟩
  by_contra hn
  have hn' : y.s.testBit i = true := by simpa using hn
  have : (acc.testBit i || (sU l).testBit i) = true := by
    rw [Bool.or_eq_true]
    rcases ho y hy with h' | h'
    · exact Or.inl (h' i hn')
    · exact Or.inr ((sU_bit l i).mpr ⟨y, h', hn'⟩)
  rw [h1, this] at hi; exact absurd hi (by decide)

lemma pairs_true {P : Par} {n : Nat} {Λ : Nat → Nat} {B T : Nat} {v : Nat → Nat} {H : Finset Nat}
    {newer : List El} {x e : El} {pre ys : List El} {dd : Bool} {m : Mv} {ms' : List Mv} {U : Finset Nat}
    (h : Pick P n Λ B T v H newer x e (pre.reverse ++ []) ys dd m ms' U) (env : Env P n Λ) (c : Ctx)
    (hc : CtxOK P n Λ B T v (x :: e :: (newer ++ (pre.reverse ++ []) ++ ys)).length c) (hall : ∀ a ∈ wd c.all, a ∈ H) (acc : Nat)
    (hent : Ents acc (x :: (pre ++ e :: ys)))
    (hacc : ∀ i, acc.testBit i = true ↔ ∃ y ∈ newer, y.s.testBit i = true) :
    pairs c newer acc x (pre ++ e :: ys) = true := by
  have hux : Uq x.u x.s (e :: (newer ++ (pre.reverse ++ []) ++ ys)) := by
    apply uq_of hent
    intro y hy
    simp only [List.mem_cons, List.mem_append, List.mem_reverse, List.not_mem_nil, or_false] at hy ⊢
    rcases hy with rfl | (hy | hy) | hy
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl fun i hb => (hacc i).mpr ⟨y, hy, hb⟩
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr (Or.inr hy))
  obtain ⟨acc2, ha2, hent2⟩ := Ents_split (x :: pre) (e :: ys) acc hent
  have hue : Uq e.u e.s (x :: (newer ++ (pre.reverse ++ []) ++ ys)) := by
    apply uq_of hent2
    intro y hy
    simp only [List.mem_cons, List.mem_append, List.mem_reverse, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | (hy | hy) | hy
    · exact Or.inl fun i hb => (ha2 i).mpr (Or.inr ⟨y, by simp, hb⟩)
    · exact Or.inl fun i hb => (ha2 i).mpr (Or.inl ((hacc i).mpr ⟨y, hy, hb⟩))
    · exact Or.inl fun i hb => (ha2 i).mpr (Or.inr ⟨y, by simp [hy], hb⟩)
    · exact Or.inr hy
  have hef : ∀ i, e.f.testBit i = true ↔ ∃ y ∈ ys, y.s.testBit i = true := by
    intro i; rw [hent2.1, sU_bit]
  have hR : ∀ acc', (∀ i, acc'.testBit i = true ↔ acc.testBit i = true ∨ ∃ z ∈ pre, z.s.testBit i = true) →
      ∀ i, (Nat.lor acc' e.f).testBit i = true ↔ ∃ y ∈ newer ++ (pre.reverse ++ []) ++ ys, y.s.testBit i = true := by
    intro acc' h' i
    rw [tb_lor, Bool.or_eq_true, h', hacc, hef]
    simp only [List.mem_append, List.mem_reverse, List.not_mem_nil, or_false]
    constructor
    · rintro ((⟨y, hy, hb⟩ | ⟨y, hy, hb⟩) | ⟨y, hy, hb⟩)
      · exact ⟨y, Or.inl (Or.inl hy), hb⟩
      · exact ⟨y, Or.inl (Or.inr hy), hb⟩
      · exact ⟨y, Or.inr hy, hb⟩
    · rintro ⟨y, (hy | hy) | hy, hb⟩
      · exact Or.inl (Or.inl ⟨y, hy, hb⟩)
      · exact Or.inl (Or.inr ⟨y, hy, hb⟩)
      · exact Or.inr ⟨y, hy, hb⟩
  unfold pairs
  rcases hk : c.k with _ | _ | k
  · change force x.u (fun ux => l0 c newer acc x ux (pre ++ e :: ys) []) = true
    rw [force_eq]
    exact l0_split c newer acc x x.u e ys pre [] (h.f0_true env c hc hall acc hk hux hue hacc hef)
  · change l1 c newer x (pre ++ e :: ys) acc [] = true
    exact l1_split c newer x e ys pre acc [] (fun acc' h' => h.f1_true env c hc hall acc' _ hk hux hue (hR acc' h'))
  · change l2 c newer x (pre ++ e :: ys) acc [] = true
    refine l2_split c newer x e ys pre acc [] (fun acc' h' => ?_)
    have := h.hand_true env c hc hall acc' _ (hR acc' h')
    cases dd
    · exact Or.inl this
    · exact Or.inr this



lemma EOK_neg {top n : Nat} {Λ : Nat → Nat} (hm : ∀ i < n, ∀ j, (Λ i).testBit j = true → top.testBit j = true)
    {x : El} (hx : EOK n Λ x) (s : Nat) : EOK n Λ ⟨neg top x.a, s, x.of, x.zf, 0, 0⟩ := by
  refine ⟨hx.2.1, hx.1, fun i hi => ⟨fun h j hj => ?_, fun h j hj => ?_⟩⟩
  · simp only [neg, tb_xor]; rw [(hx.2.2 i hi).2 h j hj, hm i hi j hj]; rfl
  · simp only [neg, tb_xor]; rw [(hx.2.2 i hi).1 h j hj, hm i hi j hj]; rfl

lemma wd_reS (full : Nat) (d : Bool) (l : List El) : wd (reS full d l) = wd l := by
  induction l with
  | nil => rfl
  | cons e l ih => change e.a :: wd (reS full d l) = e.a :: wd l; rw [ih]
lemma cfl_reS (full : Nat) (d : Bool) (l : List El) (i : Nat) : cfl i (reS full d l) = cfl i l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    change cfl i (⟨e.a, sep full d e.a, e.zf, e.of, 0, 0⟩ :: reS full d l) = _
    rw [cfl_cons, cfl_cons, ih]; rfl
lemma reS_append (full : Nat) (d : Bool) (l r : List El) : reS full d (l ++ r) = reS full d l ++ reS full d r := by
  induction l with
  | nil => rfl
  | cons e l ih => change _ :: reS full d (l ++ r) = _ :: (reS full d l ++ reS full d r); rw [ih]
lemma mem_reS {full : Nat} {d : Bool} {l : List El} {y : El} (h : y ∈ reS full d l) :
    ∃ e ∈ l, y = ⟨e.a, sep full d e.a, e.zf, e.of, 0, 0⟩ := by
  induction l with
  | nil => simp [reS] at h
  | cons e l ih =>
    rcases List.mem_cons.mp h with h | h
    · exact ⟨e, by simp, h⟩
    · obtain ⟨e', h1, h2⟩ := ih h; exact ⟨e', by simp [h1], h2⟩

lemma Inv_reS {P : Par} {n : Nat} {Λ : Nat → Nat} {sk : El → Prop} {B T R : Nat} {act old : List El} (d : Bool)
    (h : Inv P n Λ sk B T R act old) :
    Inv P n Λ (fun y => y.s = sep P.full d y.a) B T R (reS P.full d act) (reS P.full d old) := by
  obtain ⟨ms, H, v, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨ms, H, v, ?_, h2, h3, ?_, ?_, ?_, h7, ?_⟩
  · rw [← reS_append, wd_reS]; exact h1
  · rw [← reS_append, wd_reS]; exact h4
  · rw [← reS_append]
    intro y hy
    obtain ⟨e, he, rfl⟩ := mem_reS hy
    exact ⟨rfl, (h5 e he).2⟩
  · rw [← reS_append, wd_reS, wd_reS]; exact h6
  · intro i hi
    rw [← reS_append, wd_reS, cfl_reS]; exact h8 i hi

structure UOK (P : Par) (n : Nat) (Λ : Nat → Nat) (B T : Nat) (chU : Ch) : Prop where
  ch : ∀ R a o, Inv P n Λ (fun y => y.s = sep P.full (Nat.ble 2 T) y.a) B (T - 1) R
      (reS P.full (Nat.ble 2 T) a) (reS P.full (Nat.ble 2 T) o) → chU R a o = true

lemma ble2 (T : Nat) : Nat.ble 2 T = decide (1 ≤ T - 1) := by
  by_cases h : 2 ≤ T
  · have : 1 ≤ T - 1 := by omega
    rw [Nat.ble_eq.mpr h]; simp [this]
  · have : ¬ 1 ≤ T - 1 := by omega
    have h' : Nat.ble 2 T = false := by
      by_contra hn; exact h (Nat.ble_eq.mp (by simpa using hn))
    rw [h']; simp [this]
lemma ble1 (T : Nat) : Nat.ble 1 T = decide (1 ≤ T) := by
  by_cases h : 1 ≤ T
  · rw [Nat.ble_eq.mpr h]; simp [h]
  · have h' : Nat.ble 1 T = false := by
      by_contra hn; exact h (Nat.ble_eq.mp (by simpa using hn))
    rw [h']; simp [h]

lemma unary_true {P : Par} {n : Nat} {Λ : Nat → Nat} (env : Env P n Λ) {B T N : Nat} {v : Nat → Nat} {H : Finset Nat}
    {newer es : List El} {x : El} {m : Mv} {ms' : List Mv} {U : Finset Nat} (c : Ctx) (hc : CtxOK P n Λ B T v N c)
    (chU : Ch) (hU : UOK P n Λ B T chU)
    (hall : ∀ a ∈ wd c.all, a ∈ H) (U0 : Nat)
    (hU0 : ∀ i, U0.testBit i = true ↔ ∃ y ∈ newer ++ x :: es, (sep P.full (Nat.ble 2 T) y.a).testBit i = true)
    (rdy : Rdy P n Λ B T v (m :: ms') H (newer ++ x :: es)) (hm : m.1 = none) (ho : m.2.1 = x.a)
    (hS : (wd (newer ++ x :: es)).toFinset = ops m ∪ U) (hf : res P.top m ∉ H) (hg : good m)
    (hd : Dv P.top P.tgt ms' (insert (res P.top m) H) (insert (res P.top m) U))
    (av : ∀ m' ∈ ms', ops m' ⊆ (wd (newer ++ x :: es)).toFinset → ∃ a ∈ ops m', a ∈ wd (x :: newer)) :
    unary c chU newer x es U0 = true := by
  have hx := rdy.ok x (by simp)
  have hops : ops m = {x.a} := by
    obtain ⟨o, a, b⟩ := m
    simp only at hm ho; subst hm; subst ho
    simp only [good] at hg; subst hg; simp [ops]
  have hres : res P.top m = neg P.top x.a := by
    obtain ⟨o, a, b⟩ := m; simp only at hm ho; subst hm; subst ho; rfl
  have nt : nb ms' ≤ B ∧ nu ms' + 1 = T := by
    have h1 := rdy.hB; have h2 := rdy.hT
    simp only [nb, nu, List.countP_cons, hm] at h1 h2 ⊢
    simp at h1 h2; exact ⟨h1, h2⟩
  have nd := rdy.nd
  have hperm : (x :: (newer ++ es)).Perm (newer ++ x :: es) := List.perm_middle.symm
  have ndx : (wd (x :: (newer ++ es))).Nodup := (wd_perm hperm).nodup_iff.mpr nd
  have hxr : x.a ∉ wd (newer ++ es) := (List.nodup_cons.mp ndx).1
  have hz : EOK n Λ ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩ := EOK_neg (fun i hi => (env.msk i hi).sub) hx 0
  have hcz : ∀ i, con i ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩ = con i x := fun i => Bool.or_comm _ _
  have hrestU : ∀ a ∈ wd (newer ++ es), a ∈ U := by
    intro a ha
    have : a ∈ ops m ∪ U := by
      rw [← hS, List.mem_toFinset]
      exact (wd_perm hperm).mem_iff.mp (List.mem_cons_of_mem _ ha)
    rcases Finset.mem_union.mp this with h | h
    · rw [hops, Finset.mem_singleton] at h; subst h; exact absurd ha hxr
    · exact h
  have hmemU : ∀ a ∈ U, a = x.a ∨ a ∈ wd (newer ++ es) := by
    intro a ha
    have : a ∈ wd (newer ++ x :: es) := by
      rw [← List.mem_toFinset, hS]; exact Finset.mem_union_right _ ha
    exact List.mem_cons.mp ((wd_perm hperm).mem_iff.mpr this)
  have hcov : Nat.lor U0 (sep P.full (Nat.ble 2 T) (neg P.top x.a)) = P.full := by
    apply eq_full
    · intro i hi
      obtain ⟨a, ha, hb⟩ := hd.sep env.gd i hi
      have hT' : decide (1 ≤ nu ms') = Nat.ble 2 T := by rw [ble2]; have := nt.2; congr 2; omega
      rw [hT'] at hb
      rw [tb_lor, Bool.or_eq_true, hU0]
      rcases Finset.mem_insert.mp ha with rfl | ha
      · right; rw [← hres]; exact hb
      · left
        have : a ∈ wd (newer ++ x :: es) := by
          rw [← List.mem_toFinset, hS]; exact Finset.mem_union_right _ ha
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp this
        exact ⟨y, hy, hb⟩
    · intro i hb
      rw [tb_lor, Bool.or_eq_true, hU0] at hb
      by_contra hn
      have hn' : P.full.testBit i = false := by simpa using hn
      rcases hb with ⟨y, _, hb⟩ | hb
      · rw [sep_bit_off _ _ _ _ hn'] at hb; exact absurd hb (by decide)
      · rw [sep_bit_off _ _ _ _ hn'] at hb; exact absurd hb (by decide)
  have hhas : has (neg P.top x.a) c.all = false := by
    by_contra hn
    have := (has_eq _ _).mp (by simpa using hn)
    exact hf (by rw [hres]; exact hall _ this)
  have hnew : ∀ m' ∈ ms', ops m' ⊆ insert (res P.top m) U → ∃ a ∈ ops m', a = neg P.top x.a ∨ (a ∈ U ∧ a ∈ wd (x :: newer)) := by
    intro m' hm' hs
    by_cases hzm : res P.top m ∈ ops m'
    · exact ⟨_, hzm, Or.inl hres⟩
    · have hsU : ops m' ⊆ U := fun a ha => (Finset.mem_insert.mp (hs ha)).resolve_left (fun e => hzm (e ▸ ha))
      obtain ⟨a, ha, hw⟩ := av m' hm' (by rw [hS]; exact hsU.trans Finset.subset_union_right)
      exact ⟨a, ha, Or.inr ⟨hsU ha, hw⟩⟩
  have hjo := rdy.jo
  have hbias : c.P.bias = encV n (fun _ => 64) := by rw [hc.eP]; exact env.bias
  have hsub : Nat.sub c.R (cf ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩) = encV n (fun i => v i - b2n (con i x)) := by
    rw [hc.R, cf_enc hz, encV_sub]
    · exact encV_congr _ (fun i _ => by rw [hcz])
    · intro i hi; rw [hcz]; have := (hjo i hi).1; have := b2n_le (con i x); omega
  unfold unary
  rw [force_eq, bAnd, hc.eP, hc.t]
  refine ball_and (Nat.beq_eq.mpr hcov) ?_
  unfold un2; rw [mk_eq]
  unfold unK; rw [bNot, hhas, bOr]
  refine ball_and rfl ?_
  by_cases hxU : x.a ∈ U
  · -- keep x
    have hlu : (wd ([x] ++ (newer ++ es))).toFinset = U := by
      ext a; rw [List.mem_toFinset]
      constructor
      · intro ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hxU
        · exact hrestU a ha
      · intro ha
        rcases hmemU a ha with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h
    obtain ⟨c1, c3⟩ := childInv (K := B + T) (B' := B) (T' := T - 1) (fr := fun i => con i x)
      (act' := ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩ :: x :: newer) (old' := es) (sk := fun _ => True)
      (z := ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩) (dl := []) (lu := [x] ++ (newer ++ es))
      env hg hf rdy.dv.sub hS hd nt.1 (by omega) (by omega) nd rdy.ok hjo hres.symm hz (fun _ _ => trivial)
      (by simpa using hperm) hlu (by simp) (by
        intro m' hm' hs
        obtain ⟨a, ha, h1 | ⟨_, h2⟩⟩ := hnew m' hm' hs
        · exact ⟨a, ha, by rw [h1]; simp [wd]⟩
        · exact ⟨a, ha, List.mem_cons_of_mem _ h2⟩)
      (fun i hi h => ⟨x.a, by rw [hops]; simp, con_sound hx hi h⟩)
      (fun i _ h => by rw [hcz] at h; exact h) (fun i _ => by rw [cfl_nil]; omega)
    apply bor_r
    have e1 : Nat.sub (Nat.sub c.R (cf x)) (cf ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩) =
        encV n (fun i => v i - b2n (con i x) + cfl i [] - b2n (con i ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩)) := by
      rw [hc.R, cf_enc hx, cf_enc hz, encV_sub, encV_sub]
      · simp only [cfl_nil, Nat.add_zero]
      · intro i hi; have := (hjo i hi).1; have := b2n_le (con i x)
        rw [hcz]; omega
      · intro i hi; have := (hjo i hi).1; have := b2n_le (con i x); omega
    rw [e1, hbias]
    apply chk_eq
    · intro i hi; have := (hjo i hi).2.1; beta_reduce; rw [cfl_nil]; omega
    · intro i hi; have h1 := c1 i hi; beta_reduce at h1 ⊢; rw [cfl_nil] at h1 ⊢; omega
    · exact hU.ch _ _ _ (Inv_reS _ c3)
  · -- drop x
    have hlu : (wd (newer ++ es)).toFinset = U := by
      ext a; rw [List.mem_toFinset]
      constructor
      · exact hrestU a
      · intro ha
        rcases hmemU a ha with rfl | h
        · exact absurd ha hxU
        · exact h
    obtain ⟨c1, c3⟩ := childInv (K := B + T) (B' := B) (T' := T - 1) (fr := fun i => con i x)
      (act' := ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩ :: newer) (old' := es) (sk := fun _ => True)
      (z := ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩) (dl := [x]) (lu := newer ++ es)
      env hg hf rdy.dv.sub hS hd nt.1 (by omega) (by omega) nd rdy.ok hjo hres.symm hz (fun _ _ => trivial)
      hperm hlu (by simp) (by
        intro m' hm' hs
        obtain ⟨a, ha, h1 | ⟨h3, h2⟩⟩ := hnew m' hm' hs
        · exact ⟨a, ha, by rw [h1]; simp [wd]⟩
        · refine ⟨a, ha, List.mem_cons_of_mem _ ?_⟩
          rcases List.mem_cons.mp h2 with rfl | h2
          · exact absurd h3 hxU
          · exact h2)
      (fun i hi h => ⟨x.a, by rw [hops]; simp, con_sound hx hi h⟩)
      (fun i _ h => by rw [hcz] at h; exact h) (fun i _ => by rw [cfl_one]; omega)
    apply bor_l
    have e1 : encV n (fun i => v i - b2n (con i x)) =
        encV n (fun i => v i - b2n (con i x) + cfl i [x] - b2n (con i ⟨neg P.top x.a, 0, x.of, x.zf, 0, 0⟩)) := by
      apply encV_congr; intro i hi
      have := (hjo i hi).1; have := b2n_le (con i x)
      rw [cfl_one, hcz]; omega
    rw [hsub, e1, hbias]
    apply chk_eq
    · intro i hi; have := (hjo i hi).2.1; have := (hjo i hi).1; have := b2n_le (con i x)
      beta_reduce; rw [cfl_one, hcz]; omega
    · intro i hi; have h1 := c1 i hi; beta_reduce at h1 ⊢; rw [cfl_one, hcz] at h1 ⊢; omega
    · exact hU.ch _ _ _ (Inv_reS _ c3)



lemma scan_cons (c : Ctx) (hB hU : Bool) (U0 : Nat) (chU : Ch) (e : El) (es : List El) (k : Nat) (newer : List El) (acc : Nat) :
    scan c hB hU U0 chU (e :: es) (k + 1) newer acc =
      ((hB && pairs c newer acc e es) || ((hU && unary c chU newer e es U0) ||
        scan c hB hU U0 chU es k (e :: newer) (Nat.lor acc e.s))) := by
  rw [← bAnd, ← bAnd, ← bOr, ← bOr, ← force_eq (Nat.lor acc e.s) (fun acc' => scan c hB hU U0 chU es k (e :: newer) acc')]; rfl

lemma scan_true {P : Par} {n : Nat} {Λ : Nat → Nat} (env : Env P n Λ) {B T N : Nat} {v : Nat → Nat} {H : Finset Nat}
    {ms : List Mv} (c : Ctx) (hc : CtxOK P n Λ B T v N c) (chU : Ch) (hU : 1 ≤ T → UOK P n Λ B T chU)
    (hall : ∀ a ∈ wd c.all, a ∈ H) (U0 : Nat) (es : List El) : ∀ (k : Nat) (newer : List El) (acc : Nat),
    Rdy P n Λ B T v ms H (newer ++ es) → (newer ++ es).length = N → Ents acc es →
    (∀ i, acc.testBit i = true ↔ ∃ y ∈ newer, y.s.testBit i = true) →
    (1 ≤ T → ∀ i, U0.testBit i = true ↔ ∃ y ∈ newer ++ es, (sep P.full (Nat.ble 2 T) y.a).testBit i = true) →
    (∀ m ∈ ms, ops m ⊆ (wd (newer ++ es)).toFinset → ∃ a ∈ ops m, a ∈ wd newer ∨ a ∈ wd (es.take k)) →
    scan c (Nat.ble 1 B) (Nat.ble 1 T) U0 chU es k newer acc = true ∨
      ∀ m ∈ ms, ops m ⊆ (wd (newer ++ es)).toFinset → ∃ a ∈ ops m, a ∈ wd newer := by
  induction es with
  | nil =>
    intro k newer acc _ _ _ _ _ hav
    right; intro m hm hs
    obtain ⟨a, ha, h | h⟩ := hav m hm hs
    · exact ⟨a, ha, h⟩
    · simp [wd] at h
  | cons x es ih =>
    intro k newer acc rdy hN hent hacc hU0 hav
    cases k with
    | zero =>
      right; intro m hm hs
      obtain ⟨a, ha, h | h⟩ := hav m hm hs
      · exact ⟨a, ha, h⟩
      · simp [wd] at h
    | succ k =>
      have hperm : (newer ++ x :: es).Perm ((x :: newer) ++ es) := List.perm_middle
      have hset : (wd ((x :: newer) ++ es)).toFinset = (wd (newer ++ x :: es)).toFinset :=
        (List.toFinset_eq_of_perm _ _ (wd_perm hperm)).symm
      have ih' := ih k (x :: newer) (Nat.lor acc x.s) (rdy.perm hperm)
        (by rw [← hN]; exact hperm.length_eq.symm) hent.2.2
        (by intro i; rw [tb_lor, Bool.or_eq_true, hacc]; simp only [List.mem_cons, exists_eq_or_imp]; exact or_comm)
        (by
          intro hT i; rw [hU0 hT]
          exact exists_congr fun y => and_congr_left fun _ => hperm.mem_iff)
        (by
          intro m hm hs; rw [hset] at hs
          obtain ⟨a, ha, h | h⟩ := hav m hm hs
          · exact ⟨a, ha, Or.inl (List.mem_cons_of_mem _ h)⟩
          · rw [List.take_succ_cons] at h
            rcases List.mem_cons.mp h with h | h
            · exact ⟨a, ha, Or.inl (by rw [h]; exact List.mem_cons_self)⟩
            · exact ⟨a, ha, Or.inr h⟩)
      rw [scan_cons]
      rcases ih' with h | h
      · left; exact bor_r (bor_r h)
      · rw [hset] at h
        by_cases hno : ∀ m ∈ ms, ops m ⊆ (wd (newer ++ x :: es)).toFinset → ∃ a ∈ ops m, a ∈ wd newer
        · exact Or.inr hno
        · left
          push Not at hno
          obtain ⟨m, hm, hs, hna⟩ := hno
          have hxm : x.a ∈ ops m := by
            obtain ⟨a, ha, h'⟩ := h m hm hs
            rcases List.mem_cons.mp h' with rfl | h'
            · exact ha
            · exact absurd h' (hna a ha)
          obtain ⟨ms', hd, hp⟩ := rdy.dv.front hm (hs.trans rdy.dv.sub)
          have rdy' : Rdy P n Λ B T v (m :: ms') H (newer ++ x :: es) :=
            ⟨hd, by rw [nb_perm hp]; exact rdy.hB, by rw [nu_perm hp]; exact rdy.hT, rdy.nd, rdy.sp, rdy.ok, rdy.jo⟩
          obtain ⟨hg, hf, _, U, hS, hd'⟩ := hd
          have av : ∀ m' ∈ ms', ops m' ⊆ (wd (newer ++ x :: es)).toFinset → ∃ a ∈ ops m', a ∈ wd (x :: newer) :=
            fun m' hm' hs' => h m' (hp.mem_iff.mp (List.mem_cons_of_mem _ hm')) hs'
          rcases ho : m.1 with _ | dd
          · have hT : 1 ≤ T := by
              have := rdy'.hT; simp only [nu, List.countP_cons, ho] at this; simp at this; omega
            have h1 : m.2.1 = x.a := by
              obtain ⟨o, a, b⟩ := m
              simp only at ho; subst ho
              simp only [good] at hg; subst hg
              simp only [ops, Finset.mem_insert, Finset.mem_singleton, or_self] at hxm
              exact hxm.symm
            exact bor_r (bor_l (ball_and (Nat.ble_eq.mpr hT)
              (unary_true env c hc chU (hU hT) hall U0 (hU0 hT) rdy' ho h1 hS hf hg hd' av)))
          · have hB1 : 1 ≤ B := by
              have := rdy'.hB; simp only [nb, List.countP_cons, ho] at this; simp at this; omega
            obtain ⟨b, hb, hops, hres⟩ : ∃ b, b ≠ x.a ∧ ops m = {x.a, b} ∧ res P.top m = bin dd x.a b := by
              obtain ⟨o, a, b⟩ := m
              simp only at ho; subst ho
              simp only [good] at hg
              simp only [ops, Finset.mem_insert, Finset.mem_singleton] at hxm
              rcases hxm with rfl | rfl
              · exact ⟨b, Ne.symm hg, rfl, rfl⟩
              · refine ⟨a, hg, by simp [ops, Finset.pair_comm], ?_⟩
                change bin dd a x.a = bin dd x.a a
                apply Nat.eq_of_testBit_eq; intro j
                cases dd <;> simp only [bin, Bool.cond_true, Bool.cond_false, tb_land, tb_lor]
                · exact Bool.and_comm _ _
                · exact Bool.or_comm _ _
            have hbm : b ∈ ops m := by rw [hops]; simp
            have hbes : b ∈ wd es := by
              have h1 := hs hbm
              rw [List.mem_toFinset] at h1
              have h2 := (wd_perm hperm).mem_iff.mp h1
              rcases List.mem_cons.mp h2 with h3 | h3
              · exact absurd h3 hb
              · change b ∈ (newer ++ es).map El.a at h3
                rw [List.map_append] at h3
                rcases List.mem_append.mp h3 with h4 | h4
                · exact absurd h4 (hna b hbm)
                · exact h4
            obtain ⟨e, he, rfl⟩ := List.mem_map.mp hbes
            obtain ⟨pre, ys, rfl⟩ := List.append_of_mem he
            have hp2 : (newer ++ x :: (pre ++ e :: ys)).Perm (x :: e :: (newer ++ (pre.reverse ++ []) ++ ys)) := by
              refine hperm.trans ?_
              simp only [List.cons_append, List.append_nil]
              refine List.Perm.cons _ ?_
              refine (List.Perm.trans (by rw [← List.append_assoc]) (List.perm_middle (a := e) (l₁ := newer ++ pre) (l₂ := ys))).trans ?_
              refine List.Perm.cons _ ?_
              exact (((List.reverse_perm pre).symm).append_left newer).append_right ys
            have hs2 : (wd (x :: e :: (newer ++ (pre.reverse ++ []) ++ ys))).toFinset = (wd (newer ++ x :: (pre ++ e :: ys))).toFinset :=
              (List.toFinset_eq_of_perm _ _ (wd_perm hp2)).symm
            have pk : Pick P n Λ B T v H newer x e (pre.reverse ++ []) ys dd m ms' U :=
              ⟨rdy'.perm hp2, ho, hops, hres, by rw [hs2]; exact hS, hf, hg, hd', by rw [hs2]; exact av⟩
            refine bor_l (ball_and (Nat.ble_eq.mpr hB1) (pairs_true pk env c ?_ hall acc hent hacc))
            rw [← hp2.length_eq, hN]; exact hc

lemma Forall2_wd {l r : List El} (h : List.Forall₂ same l r) : wd l = wd r := by
  induction h with
  | nil => rfl
  | cons h _ ih => change _ :: _ = _ :: _; rw [h.1]; exact congrArg _ ih
lemma Forall2_cfl {l r : List El} (h : List.Forall₂ same l r) (i : Nat) : cfl i l = cfl i r := by
  induction h with
  | nil => rfl
  | cons h _ ih => rw [cfl_cons, cfl_cons, ih]; unfold con; rw [h.2.2.1, h.2.2.2]
lemma Forall2_mem {l r : List El} (h : List.Forall₂ same l r) {y : El} (hy : y ∈ r) : ∃ x ∈ l, same x y := by
  induction h with
  | nil => simp at hy
  | cons h _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, by simp, h⟩
    · obtain ⟨x, hx, hs⟩ := ih hy; exact ⟨x, by simp [hx], hs⟩
lemma Forall2_trans {l r t : List El} (h : List.Forall₂ same l r) : List.Forall₂ same r t → List.Forall₂ same l t := by
  induction h generalizing t with
  | nil => intro h'; exact h'
  | cons h _ ih =>
    intro h'
    cases h' with
    | cons h1 h2 => exact .cons ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.1.trans h1.2.2.1, h.2.2.2.trans h1.2.2.2⟩ (ih h2)

lemma isTgt_true {t : Nat} {l : List El} (hn : (wd l).Nodup) (hs : (wd l).toFinset = {t}) : isTgt t l = true := by
  have hc : (wd l).length = 1 := by
    rw [← List.toFinset_card_of_nodup hn, hs]; simp
  rcases l with _ | ⟨e, _ | ⟨e', l⟩⟩
  · simp [wd] at hc
  · have : e.a = t := by
      have : e.a ∈ (wd [e]).toFinset := by simp [wd]
      rw [hs, Finset.mem_singleton] at this; exact this
    change Nat.beq e.a t = true
    rw [this]; exact Nat.beq_refl t
  · simp [wd] at hc

lemma node_true {P : Par} {n : Nat} {Λ : Nat → Nat} (env : Env P n Λ) (f : Nat) : ∀ (B T R : Nat) (act old : List El),
    Inv P n Λ (fun y => y.s = sep P.full (decide (1 ≤ T)) y.a) B T R act old → node P f B T R act old = true := by
  induction f with
  | zero => intro B T R act old _; rfl
  | succ f ih =>
    intro B T R act old hinv
    obtain ⟨ms, H, v, hd, hB, hT, hnd, hok, hav, hR, hjo⟩ := hinv
    change body P B T (node P f (Nat.pred B) T)
      (fun R act old => resep P.full (Nat.ble 2 T) act fun act => resep P.full (Nat.ble 2 T) old fun old =>
        node P f B (Nat.pred T) R act old) R act old = true
    unfold body
    rw [appK_eq, force_eq, len_eq, bAnd, buildK_eq, bAnd, uniqK_eq]
    set l := act ++ old with hl
    set es := reU (reF l) 0 with hes
    have hsame : List.Forall₂ same l es := Forall2_trans (reF_same l) (reU_same (reF l) 0)
    have hwd : wd es = wd l := (Forall2_wd hsame).symm
    have hlen : l.length ≤ B + 1 := by
      have := hd.card
      rw [List.toFinset_card_of_nodup hnd, wd, List.length_map] at this; omega
    have hsp : ∀ e ∈ l, e.s = sep P.full (decide (1 ≤ T)) e.a := fun e he => (hok e he).1
    have hfull : sufOf (reF l) = P.full := by
      rw [sufOf_reF]
      apply eq_full
      · intro i hi
        obtain ⟨a, ha, hb⟩ := hd.sep env.gd i hi
        rw [hT] at hb
        rw [List.mem_toFinset] at ha
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
        exact (sU_bit l i).mpr ⟨e, he, by rw [hsp e he]; exact hb⟩
      · intro i hb
        obtain ⟨e, he, hb⟩ := (sU_bit l i).mp hb
        exact sbit_full (hsp e he) hb
    refine ball_and (Nat.ble_eq.mpr hlen) (ball_and (Nat.beq_eq.mpr hfull) ?_)
    unfold body2
    rw [bOr, bAnd, force_eq, force_eq, len_eq]
    rcases ms with _ | ⟨m0, ms0⟩
    · apply bor_l
      refine ball_and (Nat.beq_eq.mpr hT.symm) (isTgt_true hnd hd.1)
    · apply bor_r
      have rdy : Rdy P n Λ B T v (m0 :: ms0) H ([] ++ es) := by
        refine ⟨by rw [List.nil_append, hwd]; exact hd, hB, hT, by rw [List.nil_append, hwd]; exact hnd, ?_, ?_, ?_⟩
        · intro e he
          obtain ⟨x, hx, hs⟩ := Forall2_mem hsame he
          rw [← hs.2.1, ← hs.1]; exact hsp x hx
        · intro e he
          obtain ⟨x, hx, hs⟩ := Forall2_mem hsame he
          have := (hok x hx).2
          unfold EOK at this ⊢
          rw [← hs.1, ← hs.2.2.1, ← hs.2.2.2]; exact this
        · intro i hi
          rw [List.nil_append, hwd, ← Forall2_cfl hsame]; exact hjo i hi
      have hc : CtxOK P n Λ B T v es.length ⟨P, node P f (Nat.pred B) T, Nat.ble 1 T, T, Nat.sub (Nat.succ B) l.length, R, l⟩ := by
        refine ⟨rfl, ble1 T, rfl, ?_, hR, fun R a o h => ih _ _ _ _ _ h⟩
        rw [← hsame.length_eq]; rfl
      have := scan_true env (ms := m0 :: ms0) (H := H)
        ⟨P, node P f (Nat.pred B) T, Nat.ble 1 T, T, Nat.sub (Nat.succ B) l.length, R, l⟩ hc
        (fun R act old => resep P.full (Nat.ble 2 T) act fun act => resep P.full (Nat.ble 2 T) old fun old =>
          node P f B (Nat.pred T) R act old)
        (fun hT1 => ⟨fun R a o h => by
          rw [resep_eq, resep_eq]
          refine ih _ _ _ _ _ ?_
          have e : (fun y : El => y.s = sep P.full (decide (1 ≤ Nat.pred T)) y.a) = (fun y : El => y.s = sep P.full (Nat.ble 2 T) y.a) := by
            funext y; rw [ble2]; rfl
          rw [e]; exact h⟩)
        (fun a ha => hd.sub (List.mem_toFinset.mpr ha))
        (@Bool.rec (fun _ => Nat) 0 (seps0 P.full (Nat.ble 2 T) l) (Nat.ble 1 T)) es act.length [] 0 rdy rfl
        (ents l 0) (by simp) ?_ ?_
      · rcases this with h | h
        · exact h
        · exfalso
          have hs0 : ops m0 ⊆ (wd ([] ++ es)).toFinset := by
            obtain ⟨_, _, _, U, hS, _⟩ := rdy.dv
            rw [hS]; exact Finset.subset_union_left
          obtain ⟨a, _, ha⟩ := h m0 (by simp) hs0
          simp [wd] at ha
      · intro hT1 i
        rw [Nat.ble_eq.mpr hT1]
        change (seps0 P.full (Nat.ble 2 T) l).testBit i = true ↔ _
        rw [seps0_bit, List.nil_append]
        constructor
        · rintro ⟨e, he, hb⟩
          have : e.a ∈ wd es := by rw [hwd]; exact List.mem_map.mpr ⟨e, he, rfl⟩
          obtain ⟨y, hy, hya⟩ := List.mem_map.mp this
          exact ⟨y, hy, by rw [hya]; exact hb⟩
        · rintro ⟨e, he, hb⟩
          have : e.a ∈ wd l := by rw [← hwd]; exact List.mem_map.mpr ⟨e, he, rfl⟩
          obtain ⟨y, hy, hya⟩ := List.mem_map.mp this
          exact ⟨y, hy, by rw [hya]; exact hb⟩
      · intro m hm hs
        rw [List.nil_append, hwd] at hs
        obtain ⟨a, ha, h⟩ := hav m hm hs
        refine ⟨a, ha, Or.inr ?_⟩
        have : wd (es.take act.length) = wd act := by
          rw [wd, List.map_take]
          change (wd es).take act.length = wd act
          rw [hwd, hl, wd, List.map_append, List.take_append_of_le_length (by simp)]
          simp [wd]
        rw [this]; exact h



-- packed flags of the starting elements
def isZ (m a : Nat) : Bool := Nat.beq (Nat.land a m) 0
def isO (m a : Nat) : Bool := Nat.beq (Nat.land a m) m
def encL : List Nat → Nat
  | [] => 0
  | v :: l => v + 256 * encL l
lemma encL_eq (l : List Nat) : encL l = encV l.length (fun i => l.getD i 0) := by
  induction l with
  | nil => rfl
  | cons v l ih => rw [encL, ih]; rfl
def zfL (mus : List Nat) (a : Nat) : Nat := encL (mus.map fun m => b2n (isZ m a))
def ofL (mus : List Nat) (a : Nat) : Nat := encL (mus.map fun m => b2n (isO m a))
lemma encF (mus : List Nat) (f : Nat → Bool) : encL (mus.map fun m => b2n (f m)) =
    encB mus.length (fun i => f (mus.getD i 0)) := by
  rw [encL_eq, List.length_map, encB]
  apply encV_congr; intro i hi
  simp [List.getD_eq_getElem?_getD, hi]

lemma isZ_iff (m a : Nat) : isZ m a = true ↔ zM m a := by
  unfold isZ zM; rw [Nat.beq_eq]
  constructor
  · intro h j hj
    have := congrArg (fun x => x.testBit j) h
    simp only [tb_land, hj, Bool.and_true, Nat.zero_testBit] at this; exact this
  · intro h; apply Nat.eq_of_testBit_eq; intro j
    rw [tb_land, Nat.zero_testBit]
    cases hm : m.testBit j
    · simp
    · rw [h j hm]; rfl
lemma isO_iff (m a : Nat) : isO m a = true ↔ oM m a := by
  unfold isO oM; rw [Nat.beq_eq]
  constructor
  · intro h j hj
    have := congrArg (fun x => x.testBit j) h
    simp only [tb_land, hj, Bool.and_true] at this; exact this
  · intro h; apply Nat.eq_of_testBit_eq; intro j
    rw [tb_land]
    cases hm : m.testBit j
    · simp
    · rw [h j hm]; rfl
def conB (m a : Nat) : Bool := isZ m a || isO m a
lemma conB_iff (m a : Nat) : conB m a = true ↔ conM m a := by
  unfold conB conM; rw [Bool.or_eq_true, isZ_iff, isO_iff]

def mkEl (full : Nat) (d : Bool) (mus : List Nat) (a : Nat) : El := ⟨a, sep full d a, zfL mus a, ofL mus a, 0, 0⟩
noncomputable def mkAll (full : Nat) (d : Bool) (mus : List Nat) (S : List Nat) : (List El → Bool) → Bool :=
  @List.rec Nat (fun _ => (List El → Bool) → Bool) (fun k => k [])
    (fun a _ ih k => ih fun r => force a fun a => force (sep full d a) fun s => force (zfL mus a) fun zf =>
      force (ofL mus a) fun of => k (⟨a, s, zf, of, 0, 0⟩ :: r)) S
lemma mkAll_eq (full : Nat) (d : Bool) (mus S : List Nat) : ∀ k, mkAll full d mus S k = k (S.map (mkEl full d mus)) := by
  induction S with
  | nil => intro k; rfl
  | cons a S ih =>
    intro k
    have : mkAll full d mus (a :: S) k = mkAll full d mus S fun r => force a fun a => force (sep full d a) fun s =>
      force (zfL mus a) fun zf => force (ofL mus a) fun of => k (⟨a, s, zf, of, 0, 0⟩ :: r) := rfl
    rw [this, ih, force_eq, force_eq, force_eq, force_eq]; rfl

def cnt (S : List Nat) (m : Nat) : Nat := S.countP (conB m)
def vals (K : Nat) (mus Ls S : List Nat) : List Nat := List.zipWith (fun m L => 64 + K - L - cnt S m) mus Ls
def dead (K : Nat) (mus Ls S : List Nat) : Bool := (List.zipWith (fun m L => decide (K < L + cnt S m)) mus Ls).any id
noncomputable def rootChk (P : Par) (f B T : Nat) (mus Ls S : List Nat) : Bool :=
  dead (B + T) mus Ls S ||
    ((vals (B + T) mus Ls S).all (fun v => Nat.ble v 126) &&
      !(mkAll P.full (Nat.ble 1 T) mus S fun els => force (encL (vals (B + T) mus Ls S)) fun R => node P f B T R els []))

lemma wd_mk (full : Nat) (d : Bool) (mus S : List Nat) : wd (S.map (mkEl full d mus)) = S := by
  induction S with
  | nil => rfl
  | cons a S ih => change a :: wd _ = _; rw [ih]
lemma con_mk (full : Nat) (d : Bool) (mus : List Nat) (a i : Nat) (hi : i < mus.length) :
    con i (mkEl full d mus a) = conB (mus.getD i 0) a := by
  change (flg i (zfL mus a) || flg i (ofL mus a)) = _
  rw [zfL, ofL, encF mus (fun m => isZ m a), encF mus (fun m => isO m a), flg_encB _ _ _ hi, flg_encB _ _ _ hi]; rfl
lemma cfl_mk (full : Nat) (d : Bool) (mus S : List Nat) (i : Nat) (hi : i < mus.length) :
    cfl i (S.map (mkEl full d mus)) = cnt S (mus.getD i 0) := by
  unfold cfl cnt; rw [List.countP_map]
  apply List.countP_congr; intro a _
  simp only [Function.comp, con_mk _ _ _ _ _ hi]
lemma EOK_mk (full : Nat) (d : Bool) (mus : List Nat) (a : Nat) :
    EOK mus.length (fun i => mus.getD i 0) (mkEl full d mus a) := by
  refine ⟨?_, ?_, fun i hi => ⟨fun h => ?_, fun h => ?_⟩⟩
  · change WF _ (zfL mus a); rw [zfL, encF mus (fun m => isZ m a)]; exact WF_encB _ _
  · change WF _ (ofL mus a); rw [ofL, encF mus (fun m => isO m a)]; exact WF_encB _ _
  · change flg i (zfL mus a) = true at h
    rw [zfL, encF mus (fun m => isZ m a), flg_encB _ _ _ hi] at h; exact (isZ_iff _ _).mp h
  · change flg i (ofL mus a) = true at h
    rw [ofL, encF mus (fun m => isO m a), flg_encB _ _ _ hi] at h; exact (isO_iff _ _).mp h

lemma rootNo {P : Par} {f B T : Nat} {mus Ls S : List Nat} (hg : Gd P.top P.full P.tgt)
    (hm : ∀ i < mus.length, Msk P.top P.tgt (mus.getD i 0)) (hb : P.bias = encL (mus.map fun _ => 64))
    (hl : Ls.length = mus.length) (hn : S.Nodup)
    (hLB : ∀ i < mus.length, LB P.top P.tgt (mus.getD i 0) (Ls.getD i 0) S.toFinset)
    (h : rootChk P f B T mus Ls S = true) {ms : List Mv} {H : Finset Nat} (hd : Dv P.top P.tgt ms H S.toFinset)
    (hB : nb ms ≤ B) (hT : nu ms = T) : False := by
  have env : Env P mus.length (fun i => mus.getD i 0) := by
    refine ⟨hg, hm, ?_⟩
    rw [hb, encL_eq, List.length_map]; apply encV_congr; intro i hi
    simp [List.getD_eq_getElem?_getD, hi]
  have hlen : ms.length ≤ B + T := by have := nb_nu ms; omega
  have hcn : ∀ i < mus.length, cnt S (mus.getD i 0) ≤ cN (mus.getD i 0) S.toFinset := by
    intro i hi
    have := cfl_le (n := mus.length) (Λ := fun i => mus.getD i 0) (l := S.map (mkEl P.full true mus))
      (by intro e he; obtain ⟨a, _, rfl⟩ := List.mem_map.mp he; exact EOK_mk _ _ _ _) (by rw [wd_mk]; exact hn) hi
    rw [cfl_mk _ _ _ _ _ hi, wd_mk] at this; exact this
  have hKL : ∀ i < mus.length, Ls.getD i 0 + cnt S (mus.getD i 0) ≤ B + T := by
    intro i hi
    have := (hLB i hi).len (hm i hi) hd
    have := hcn i hi; omega
  unfold rootChk at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · unfold dead at h
    rw [List.any_eq_true] at h
    obtain ⟨b, hb1, hb2⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb1
    rw [List.length_zipWith] at hi
    simp only [List.getElem_zipWith, id, decide_eq_true_eq] at hb2
    have := hKL i (by omega)
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at this
    omega
  · rw [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hv, hno⟩ := h
    rw [mkAll_eq, force_eq] at hno
    have hvl : (vals (B + T) mus Ls S).length = mus.length := by
      unfold vals; rw [List.length_zipWith]; omega
    have hvi : ∀ i < mus.length, (vals (B + T) mus Ls S).getD i 0 =
        64 + (B + T) - Ls.getD i 0 - cnt S (mus.getD i 0) := by
      intro i hi
      rw [List.getD_eq_getElem _ _ (by omega)]
      unfold vals
      rw [List.getElem_zipWith, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)]
    have hnode := node_true env f B T (encL (vals (B + T) mus Ls S)) (S.map (mkEl P.full (Nat.ble 1 T) mus)) []
      ⟨ms, H, fun i => (vals (B + T) mus Ls S).getD i 0, by rw [List.append_nil, wd_mk]; exact hd, hB, hT,
        by rw [List.append_nil, wd_mk]; exact hn, ?_, ?_, by rw [encL_eq, hvl], ?_⟩
    · rw [hnode] at hno; exact absurd hno (by decide)
    · intro e he
      rw [List.append_nil] at he
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
      exact ⟨by rw [← ble1]; rfl, EOK_mk _ _ _ _⟩
    · intro m _ hs
      rw [List.append_nil, wd_mk] at hs
      refine ⟨m.2.1, by simp [ops], ?_⟩
      rw [wd_mk]; exact List.mem_toFinset.mp (hs (by simp [ops]))
    · intro i hi
      have h1 := hKL i hi
      have h2 := hvi i hi
      have h3 := hv _ (List.getElem_mem (show i < (vals (B + T) mus Ls S).length by omega))
      rw [Nat.ble_eq, ← List.getD_eq_getElem _ 0] at h3
      refine ⟨by beta_reduce; omega, by beta_reduce; omega, Ls.getD i 0, by rw [List.append_nil, wd_mk]; exact hLB i hi, ?_⟩
      rw [List.append_nil, cfl_mk _ _ _ _ _ hi]; beta_reduce; omega

-- circuits and words
lemma bits_gv (j : Nat) (hj : top.testBit j = true) (w : List Nat) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (gv top w g).testBit j = g.op.eval (g.inputs.map fun i => (w.map (fun a => a.testBit j)).getD i false) := by
  have rd : ∀ i, (w.map (fun a => a.testBit j)).getD i false = (w.getD i 0).testBit j := by
    intro i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases w[i]? <;> simp
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [rd]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact hj
    | cons a l ih =>
      change (Nat.land (w.getD a 0) ((l.map (fun i => w.getD i 0)).foldr Nat.land top)).testBit j = (_ && _)
      rw [tb_land]; exact congrArg _ ih
  · induction l with
    | nil => exact Nat.zero_testBit j
    | cons a l ih =>
      change (Nat.lor (w.getD a 0) ((l.map (fun i => w.getD i 0)).foldr Nat.lor 0)).testBit j = (_ || _)
      rw [tb_lor]; exact congrArg _ ih
  · cases l with
    | nil => change (neg top 0).testBit j = _; rw [neg, tb_xor, hj]; simp [GateOp.eval]
    | cons a l => change (neg top (w.getD a 0)).testBit j = _; rw [neg, tb_xor, hj]; simp [GateOp.eval]
lemma bits_exec (j : Nat) (hj : top.testBit j = true) (gs : List Gate) (hg : legal gs) : ∀ w : List Nat,
    (exec top gs w).map (fun a => a.testBit j) =
      gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)])
        (w.map (fun a => a.testBit j)) := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [exec_cons, ih (fun a ha => hg a (by simp [ha])), List.foldl_cons, List.map_append, List.map_singleton,
      bits_gv j hj w g (hg g (by simp)).1]
lemma exec_val (gs : List Gate) : ∀ w : List Nat, (∀ a ∈ w, Val top a) → ∀ a ∈ exec top gs w, Val top a := by
  induction gs with
  | nil => intro w h; exact h
  | cons g gs ih =>
    intro w h
    rw [exec_cons]; apply ih
    intro a ha; rcases List.mem_append.mp ha with ha | ha
    · exact h a ha
    · rw [List.mem_singleton] at ha; exact ha ▸ gv_val h g
lemma eval_bit (j : Nat) (hj : top.testBit j = true) (gs : List Gate) (hg : legal gs) (o : Nat) (w : List Nat) :
    ((exec top gs w).getD o 0).testBit j = (Circuit.mk gs o).eval (w.map (fun a => a.testBit j)) := by
  change _ = (gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)])
    (w.map (fun a => a.testBit j))).getD o false
  rw [← bits_exec j hj gs hg w]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (exec top gs w)[o]? <;> simp
lemma tgt_mem {tgt : Nat} (ht : tgt ≠ 0) (hv : Val top tgt) (gs : List Gate) (hg : legal gs) (o : Nat) (w : List Nat)
    (hw : ∀ a ∈ w, Val top a)
    (h : ∀ j, top.testBit j = true → (Circuit.mk gs o).eval (w.map (fun a => a.testBit j)) = tgt.testBit j) :
    tgt ∈ exec top gs w := by
  have e : (exec top gs w).getD o 0 = tgt := by
    apply Nat.eq_of_testBit_eq; intro j
    cases hj : top.testBit j
    · have h1 : ∀ x : Nat, Val top x → x.testBit j = false := by
        intro x hx; by_contra hn; rw [hx j (by simpa using hn)] at hj; exact absurd hj (by decide)
      rw [h1 _ (val_getD (exec_val gs w hw) o), h1 _ hv]
    · rw [eval_bit j hj gs hg, h j hj]
  rcases getD_cases (exec top gs w) o with h' | h'
  · exact absurd (e.symm.trans h') ht
  · exact e ▸ h'

-- the function and its restricted lower bounds
def bf (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 ||
    x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
def LBc (Z : List Nat) (L : Nat) : Prop := ∀ (gs : List Gate) (o : Nat), legal gs →
  (∀ x : Fin 9 → Bool, (∀ i : Fin 9, i.val ∈ Z → x i = false) → (Circuit.mk gs o).eval (List.ofFn x) = bf x) → L ≤ gs.length

def wbf (w : List Nat) : Nat :=
  let l := fun a b => Nat.land (w.getD a 0) (w.getD b 0)
  Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (l 0 1) (l 1 2)) (l 2 3)) (l 3 4))
    (l 4 0)) (l 0 5)) (l 1 6)) (l 2 7)) (l 3 8)) (l 5 7)) (l 6 8)) (l 8 5)
lemma wbf_bit (w : List Nat) (j : Nat) : (wbf w).testBit j = bf (fun i => (w.getD i.val 0).testBit j) := by
  simp only [wbf, tb_lor, tb_land, bf]; rfl
lemma list9 (w : List Nat) (hl : w.length = 9) (j : Nat) :
    w.map (fun a => a.testBit j) = List.ofFn (fun i : Fin 9 => (w.getD i.val 0).testBit j) := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp only [List.length_map, hl] at h1
    simp only [List.getElem_map, List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ (by omega)]



-- moving a restricted lower bound along a symmetry
def ren (σ : Fin 9 → Fin 9) (i : Nat) : Nat := if h : i < 9 then (σ ⟨i, h⟩).val else i
def renG (σ : Fin 9 → Fin 9) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren σ)⟩
def stp (l : List Bool) (g : Gate) : List Bool := l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]
def Rel (σ : Fin 9 → Fin 9) (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ 9 ≤ W.length ∧ ∀ i, W'.getD (ren σ i) false = W.getD i false
lemma rel_stp (σ : Fin 9 → Fin 9) {W W' : List Bool} (g : Gate) (h : Rel σ W W') : Rel σ (stp W g) (stp W' (renG σ g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (renG σ g).op.eval ((renG σ g).inputs.map fun i => W'.getD i false) =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [renG, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _; exact h3 i
  refine ⟨by simp [stp, h1], by simp [stp]; omega, fun i => ?_⟩
  unfold stp
  rw [hv]
  have gl : ∀ (X : List Bool) (b : Bool) (k : Nat), (X ++ [b]).getD k false =
      if k < X.length then X.getD k false else if k = X.length then b else false := by
    intro X b k
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
    split
    · rfl
    · split
      · rename_i h; subst h; simp
      · rw [List.getElem?_eq_none (by simp; omega)]; rfl
  rw [gl, gl, h3, ← h1]
  by_cases hi : i < 9
  · have h4 : ren σ i < 9 := by unfold ren; rw [dif_pos hi]; exact (σ ⟨i, hi⟩).isLt
    rw [if_pos (by omega), if_pos (by omega)]
  · have h4 : ren σ i = i := by unfold ren; rw [dif_neg hi]
    rw [h4]
lemma rel_fold (σ : Fin 9 → Fin 9) (gs : List Gate) : ∀ {W W' : List Bool}, Rel σ W W' →
    Rel σ (gs.foldl stp W) ((gs.map (renG σ)).foldl stp W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih => intro W W' h; exact ih (rel_stp σ g h)
lemma rel_init (σ : Fin 9 → Fin 9) (x : Fin 9 → Bool) : Rel σ (List.ofFn (fun i => x (σ i))) (List.ofFn x) := by
  refine ⟨by simp, by simp, fun i => ?_⟩
  by_cases hi : i < 9
  · have h4 : ren σ i = (σ ⟨i, hi⟩).val := by unfold ren; rw [dif_pos hi]
    rw [h4, List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hi)]
    rw [List.getElem_ofFn, List.getElem_ofFn]
  · have h4 : ren σ i = i := by unfold ren; rw [dif_neg hi]
    rw [h4, List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by simpa using hi)]
lemma ren_eval (σ : Fin 9 → Fin 9) (gs : List Gate) (o : Nat) (x : Fin 9 → Bool) :
    (Circuit.mk (gs.map (renG σ)) (ren σ o)).eval (List.ofFn x) = (Circuit.mk gs o).eval (List.ofFn (fun i => x (σ i))) :=
  (rel_fold σ gs (rel_init σ x)).2.2 o
lemma LBc.move {Z Z' : List Nat} {L : Nat} (h : LBc Z L) (σ : Fin 9 → Fin 9)
    (hσ : ∀ x : Fin 9 → Bool, bf (fun i => x (σ i)) = bf x) (hz : ∀ i : Fin 9, i.val ∈ Z' → (σ i).val ∈ Z) : LBc Z' L := by
  intro gs o hl hc
  have := h (gs.map (renG σ)) (ren σ o) (by
      intro g hg
      obtain ⟨g0, h0, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hl g0 h0).1, by simp only [renG, List.length_map]; exact (hl g0 h0).2⟩)
    (by
      intro x hx
      rw [ren_eval, hc _ (fun i hi => hx _ (hz i hi)), hσ])
  simpa using this

-- one problem: nine words, of which those in Z are zero
structure Prob where
  P : Par
  W : List Nat
  Z : List Nat
  req : List Nat
def low : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def muOf (p : Prob) (ds : List Nat) : Nat :=
  ds.foldl (fun m i => Nat.land m (neg p.P.top (p.W.getD i 0))) (Nat.land p.P.top low)
def ptX (k : Nat) : Fin 9 → Bool := fun i => k.testBit i.val

structure POK (p : Prob) : Prop where
  l9 : p.W.length = 9
  g1 : Nat.land p.P.full p.P.top = p.P.full
  g2 : Nat.land p.P.full (Nat.shiftRight p.P.top 402) = p.P.full
  g3 : Nat.land p.P.full p.P.tgt = p.P.full
  g4 : Nat.land p.P.full (Nat.shiftRight p.P.tgt 402) = 0
  wt : wbf p.W = p.P.tgt
  va : ∀ a ∈ p.W, Nat.land a p.P.top = a
  zz : ∀ i ∈ p.Z, p.W.getD i 0 = 0
  t0 : p.P.tgt ≠ 0
  t1 : p.P.tgt ≠ p.P.top
  pt : ∀ k : Fin 512, (∀ i : Fin 9, i.val ∈ p.Z → ptX k.val i = false) →
    p.P.top.testBit (804 + k.val) = true ∧ ∀ i : Fin 9, (p.W.getD i.val 0).testBit (804 + k.val) = ptX k.val i

lemma land_bit {a b : Nat} (h : Nat.land a b = a) {j : Nat} (hj : a.testBit j = true) : b.testBit j = true := by
  have := congrArg (fun x => x.testBit j) h
  simp only [tb_land, hj, Bool.true_and] at this; exact this

lemma POK.gd {p : Prob} (h : POK p) : Gd p.P.top p.P.full p.P.tgt := by
  refine ⟨fun i hi => land_bit h.g1 hi, fun i hi => ?_, fun i hi => land_bit h.g3 hi, fun i hi => ?_⟩
  · have := land_bit h.g2 hi; rwa [tb_shr] at this
  · have := congrArg (fun x => x.testBit i) h.g4
    simpa [tb_land, hi, tb_shr] using this
lemma POK.val {p : Prob} (h : POK p) : ∀ a ∈ p.W, Val p.P.top a := fun a ha _ hj => land_bit (h.va a ha) hj
lemma POK.valT {p : Prob} (h : POK p) : Val p.P.top p.P.tgt := by
  rw [← h.wt]
  have hv : ∀ i, Val p.P.top (p.W.getD i 0) := fun i => val_getD h.val i
  unfold wbf
  repeat' apply val_lor
  all_goals exact val_land (hv _)

lemma muOf_bit (p : Prob) (ds : List Nat) (j : Nat) : (muOf p ds).testBit j = true ↔
    p.P.top.testBit j = true ∧ low.testBit j = true ∧ ∀ i ∈ ds, (p.W.getD i 0).testBit j = false := by
  have gen : ∀ (ds : List Nat) (m : Nat), (∀ j, m.testBit j = true → p.P.top.testBit j = true) →
      ((ds.foldl (fun m i => Nat.land m (neg p.P.top (p.W.getD i 0))) m).testBit j = true ↔
        m.testBit j = true ∧ ∀ i ∈ ds, (p.W.getD i 0).testBit j = false) := by
    intro ds
    induction ds with
    | nil => intro m _; simp
    | cons d ds ih =>
      intro m hm
      rw [List.foldl_cons, ih _ (fun j hj => by rw [tb_land, Bool.and_eq_true] at hj; exact hm j hj.1)]
      rw [tb_land, neg, tb_xor, Bool.and_eq_true]
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rw [hm j h1] at h2
        exact ⟨h1, by simpa using h2, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, by rw [hm j h1, h2]; rfl⟩, h3⟩
  unfold muOf
  rw [gen _ _ (fun j hj => by rw [tb_land, Bool.and_eq_true] at hj; exact hj.1), tb_land, Bool.and_eq_true]
  tauto

lemma low_bit0 : ∀ k : Fin 512, low.testBit (804 + k.val) = true := by decide +kernel
lemma low_bit (k : Fin 512) : low.testBit (804 + k.val) = true := low_bit0 k

lemma ofPt0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    b2n b0 + 2 * b2n b1 + 4 * b2n b2 + 8 * b2n b3 + 16 * b2n b4 + 32 * b2n b5 + 64 * b2n b6 + 128 * b2n b7 + 256 * b2n b8 < 512 ∧
    ∀ i : Fin 9, ptX (b2n b0 + 2 * b2n b1 + 4 * b2n b2 + 8 * b2n b3 + 16 * b2n b4 + 32 * b2n b5 + 64 * b2n b6 + 128 * b2n b7 + 256 * b2n b8) i =
      (![b0, b1, b2, b3, b4, b5, b6, b7, b8] : Fin 9 → Bool) i := by decide +kernel
lemma ofPt (x : Fin 9 → Bool) : ∃ k : Fin 512, ptX k.val = x := by
  obtain ⟨h1, h2⟩ := ofPt0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  refine ⟨⟨_, h1⟩, funext fun i => (h2 i).trans ?_⟩
  fin_cases i <;> rfl

lemma wordLB {p : Prob} (hp : POK p) {ds : List Nat} {L : Nat} (hz : ∀ i ∈ p.Z, i ∈ ds) (h : LBc ds L) :
    LB p.P.top p.P.tgt (muOf p ds) L p.W.toFinset := by
  intro q hq
  obtain ⟨gs, hl, hn, b, hb, he⟩ := hq p.W (fun a ha => Or.inr ⟨a, List.mem_toFinset.mp ha, fun _ _ => rfl⟩)
  obtain ⟨o, rfl⟩ := mem_getD hb
  refine (h gs o hl ?_).trans hn
  intro x hx
  obtain ⟨k, rfl⟩ := ofPt x
  obtain ⟨h1, h2⟩ := hp.pt k (fun i hi => hx i (hz _ hi))
  have hm : (muOf p ds).testBit (804 + k.val) = true := by
    rw [muOf_bit]
    refine ⟨h1, low_bit k, fun i hi => ?_⟩
    by_cases h9 : i < 9
    · rw [h2 ⟨i, h9⟩]; exact hx ⟨i, h9⟩ hi
    · rw [List.getD_eq_default _ _ (by rw [hp.l9]; omega)]; exact Nat.zero_testBit _
  have e := he _ hm
  rw [eval_bit _ h1 gs hl, list9 _ hp.l9] at e
  have e2 : (fun i : Fin 9 => (p.W.getD i.val 0).testBit (804 + k.val)) = ptX k.val := funext h2
  rw [e2] at e
  rw [e, ← hp.wt, wbf_bit, e2]

def mskB (p : Prob) (μ : Nat) : Bool := !(conB μ p.P.tgt)
lemma mskOK {p : Prob} {ds : List Nat} (h : mskB p (muOf p ds) = true) : Msk p.P.top p.P.tgt (muOf p ds) := by
  refine ⟨fun j hj => ((muOf_bit p ds j).mp hj).1, fun hc => ?_⟩
  rw [mskB, (conB_iff _ _).mpr hc] at h; exact absurd h (by decide)

-- the cover condition for a list of words
def uni (full : Nat) (S : List Nat) : Nat := S.foldr (fun a acc => Nat.lor (sep full true a) acc) 0
lemma uni_bit (full : Nat) (S : List Nat) (i : Nat) : (uni full S).testBit i = true ↔ ∃ a ∈ S, (sep full true a).testBit i = true := by
  induction S with
  | nil => simp [uni]
  | cons a S ih =>
    change (Nat.lor (sep full true a) (uni full S)).testBit i = true ↔ _
    rw [tb_lor, Bool.or_eq_true, ih]; simp only [List.mem_cons, exists_eq_or_imp]
lemma need {p : Prob} (hp : POK p) {ms H S} (hd : Dv p.P.top p.P.tgt ms H S) {cand : List Nat} {r : Nat}
    (hS : ∀ a ∈ S, a ∈ cand) (h : Nat.beq (uni p.P.full (cand.filter (fun a => !Nat.beq a r))) p.P.full = false) : r ∈ S := by
  by_contra hr
  have : uni p.P.full (cand.filter (fun a => !Nat.beq a r)) = p.P.full := by
    apply eq_full
    · intro i hi
      obtain ⟨a, ha, hb⟩ := hd.sep hp.gd i hi
      rw [uni_bit]
      refine ⟨a, ?_, ?_⟩
      · rw [List.mem_filter]
        refine ⟨hS a ha, ?_⟩
        have : a ≠ r := fun e => hr (e ▸ ha)
        have h2 : Nat.beq a r = false := by
          by_contra hn; exact this (Nat.beq_eq.mp (by simpa using hn))
        rw [h2]; rfl
      · rw [sep_bit _ _ _ _ hi] at hb ⊢
        revert hb
        by_cases hT : 1 ≤ nu ms <;> simp only [hT, decide_true, decide_false] <;>
          cases a.testBit i <;> cases a.testBit (402 + i) <;> simp
    · intro i hb
      obtain ⟨a, _, hb⟩ := (uni_bit _ _ _).mp hb
      by_contra hn
      rw [sep_bit_off _ _ _ _ (by simpa using hn)] at hb; exact absurd hb (by decide)
  rw [this, Nat.beq_refl] at h; exact absurd h (by decide)

lemma cntNot (gs : List Gate) : gs.countP (fun g => !isNot g) + gs.countP isNot = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [List.countP_cons, List.length_cons]; cases isNot g <;> simp <;> omega

-- restricted lower bound from the search
abbrev Lane := List Nat × Nat
def musOf (p : Prob) (ls : List Lane) : List Nat := ls.map (fun l => muOf p l.1)
def subOK (p : Prob) : Bool :=
  p.W.all (fun a => Nat.beq a 0 || p.req.contains a) && p.req.all (fun r => p.W.contains r) &&
    p.req.all (fun r => !Nat.beq (uni p.P.full (p.req.filter (fun a => !Nat.beq a r))) p.P.full)

lemma probLB {p : Prob} (hp : POK p) (hs : subOK p = true) (hnd : p.req.Nodup) {ls : List Lane} {K : Nat}
    (hls : ∀ l ∈ ls, LBc l.1 l.2 ∧ (∀ i ∈ p.Z, i ∈ l.1) ∧ mskB p (muOf p l.1) = true)
    (hb : p.P.bias = encL ((musOf p ls).map fun _ => 64))
    (hr : ∀ T ≤ K, rootChk p.P (K + 1) (K - T) T (musOf p ls) (ls.map Prod.snd) p.req = true) : LBc p.Z (K + 1) := by
  intro gs o hl hc
  by_contra hlt
  have hmem : p.P.tgt ∈ exec p.P.top gs p.W := by
    apply tgt_mem hp.t0 hp.valT gs hl o p.W hp.val
    intro j hj
    rw [list9 _ hp.l9, hc _ (fun i hi => by rw [hp.zz _ hi]; exact Nat.zero_testBit _), ← hp.wt, wbf_bit]
  obtain ⟨ms, S, hd, hS, hB, hN⟩ := extract hp.t0 hp.t1 gs p.W hp.val hl hmem
  simp only [subOK, Bool.and_eq_true, List.all_eq_true] at hs
  obtain ⟨⟨s1, s2⟩, s3⟩ := hs
  have hSr : ∀ a ∈ S, a ∈ p.req := by
    intro a ha
    obtain ⟨h1, h2, _⟩ := hS a ha
    have := s1 a h1
    rw [Bool.or_eq_true, Nat.beq_eq] at this
    exact this.elim (fun h => absurd h h2) (fun h => by simpa using h)
  have hSeq : S = p.req.toFinset := by
    ext a; rw [List.mem_toFinset]
    refine ⟨hSr a, fun ha => need hp hd hSr ?_⟩
    have := s3 a ha; simpa using this
  subst hSeq
  have hcount : nb ms + nu ms ≤ gs.length := by
    have := cntNot gs
    omega
  have hmu : ∀ i (hi : i < ls.length), (musOf p ls).getD i 0 = muOf p (ls[i]).1 := by
    intro i hi; unfold musOf; rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
  have hT : nu ms ≤ K := by omega
  refine rootNo (f := K + 1) (B := K - nu ms) (T := nu ms) hp.gd ?_ hb (by simp [musOf]) hnd ?_ (hr _ hT) hd (by omega) rfl
  · intro i hi
    have hi' : i < ls.length := by simpa [musOf] using hi
    rw [hmu i hi']; exact mskOK (hls _ (List.getElem_mem hi')).2.2
  · intro i hi
    have hi' : i < ls.length := by simpa [musOf] using hi
    rw [hmu i hi', List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map]
    refine (wordLB hp (hls _ (List.getElem_mem hi')).2.1 (hls _ (List.getElem_mem hi')).1).mono ?_
    intro a ha; rw [List.mem_toFinset] at ha ⊢
    have := s2 a ha; simpa using this



def sg0 : Fin 9 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb0 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg0 i)) = bf x := by decide +kernel
def sg1 : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb1 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg1 i)) = bf x := by decide +kernel
def sg2 : Fin 9 → Fin 9 := ![1, 0, 5, 8, 6, 2, 4, 7, 3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb2 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg2 i)) = bf x := by decide +kernel
def sg3 : Fin 9 → Fin 9 := ![1, 2, 3, 8, 6, 0, 7, 4, 5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb3 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg3 i)) = bf x := by decide +kernel
def sg4 : Fin 9 → Fin 9 := ![2, 1, 0, 5, 7, 3, 6, 4, 8]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb4 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg4 i)) = bf x := by decide +kernel
def sg5 : Fin 9 → Fin 9 := ![2, 3, 8, 5, 7, 1, 4, 6, 0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb5 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg5 i)) = bf x := by decide +kernel
def sg6 : Fin 9 → Fin 9 := ![3, 2, 1, 0, 4, 8, 7, 6, 5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb6 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg6 i)) = bf x := by decide +kernel
def sg7 : Fin 9 → Fin 9 := ![3, 8, 5, 0, 4, 2, 6, 7, 1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb7 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg7 i)) = bf x := by decide +kernel
def sg8 : Fin 9 → Fin 9 := ![5, 0, 1, 2, 7, 8, 4, 6, 3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb8 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg8 i)) = bf x := by decide +kernel
def sg9 : Fin 9 → Fin 9 := ![5, 8, 3, 2, 7, 0, 6, 4, 1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb9 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg9 i)) = bf x := by decide +kernel
def sg10 : Fin 9 → Fin 9 := ![8, 3, 2, 1, 6, 5, 4, 7, 0]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb10 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg10 i)) = bf x := by decide +kernel
def sg11 : Fin 9 → Fin 9 := ![8, 5, 0, 1, 6, 3, 7, 4, 2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sgb11 : ∀ x : Fin 9 → Bool, bf (fun i => x (sg11 i)) = bf x := by decide +kernel
def q0r3 : Nat := 0x100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010000000000000000000000000000000000000000000000000000000000000000000000000000000000005294a52091088c8caa8000000000000000000000000000000000000000000000000000000000000000000000000000000000001f07c8744273333ff
def q0r4 : Nat := 0x10100000101000001010000010100000101000001010000010100000101000001010000010100000101000001010000010100000101000001010000010100000000000000000000000000000000000000000000000000000000000000000000000000000000000001ad6b5ac526313070554000000000000000000000000000000000000000000000000000000000000000000000000000000000000007f1498c4c3c3ff
def q0r5 : Nat := 0x10101010000000001010101000000000101010100000000010101010000000001010101000000000101010100000000010101010000000001010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000318c6300382c2a2a33000000000000000000000000000000000000000000000000000000000000000000000000000000000003e0f8018e0f8fcfccc
def q0r6 : Nat := 0x10101010101010100000000000000000101010101010101000000000000000001010101010101010000000000000000010101010101010100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f7bdefb03d803fc03c00000000000000000000000000000000000000000000000000000000000000000000000000000000007c00003e0ff00ff00f0
def q0r7 : Nat := 0x10101010101010101010101010101010000000000000000000000000000000001010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ce739cffc00015d5c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f83ff0000ffff00
def q0r8 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010842104f425340000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fff003ffffff000000
def q0 : Prob := ⟨⟨0x10101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000007ffffffffffffffffff, 0x7ffffffffffffffffff, 0x1010101010101010101010101000100010101010101010101010101010001000101010101000000010101010100000001000000010000000100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007ffffffffffffffffff, 0x0⟩, [0, 0, 0, q0r3, q0r4, q0r5, q0r6, q0r7, q0r8], [0, 1, 2], [q0r3, q0r4, q0r5, q0r6, q0r7, q0r8]⟩
def q0L : List Lane := []
def q0M : List Nat := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0ok : POK q0 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0mu : musOf q0 q0L = q0M := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0bi : q0.P.bias = encL (q0M.map fun _ => 64) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0nd : q0.req.Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0s : subOK q0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0c0 : rootChk q0.P 7 6 0 q0M (q0L.map Prod.snd) q0.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0c1 : rootChk q0.P 7 5 1 q0M (q0L.map Prod.snd) q0.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0c2 : rootChk q0.P 7 4 2 q0M (q0L.map Prod.snd) q0.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0c3 : rootChk q0.P 7 3 3 q0M (q0L.map Prod.snd) q0.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0c4 : rootChk q0.P 7 2 4 q0M (q0L.map Prod.snd) q0.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0c5 : rootChk q0.P 7 1 5 q0M (q0L.map Prod.snd) q0.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0c6 : rootChk q0.P 7 0 6 q0M (q0L.map Prod.snd) q0.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0cs : ∀ T ≤ 6, rootChk q0.P (6 + 1) (6 - T) T (musOf q0 q0L) (q0L.map Prod.snd) q0.req = true := by
  intro T hT
  rw [q0mu]
  interval_cases T
  · exact q0c0
  · exact q0c1
  · exact q0c2
  · exact q0c3
  · exact q0c4
  · exact q0c5
  · exact q0c6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q0LB : LBc [0, 1, 2] 7 := probLB (p := q0) q0ok q0s q0nd (ls := q0L) (K := 6) (by simp [q0L]) q0bi q0cs
def q1r2 : Nat := 0x10100000101000001010000010100000101000001010000010100000101000001010000010100000101000001010000010100000101000001010000010100000000000000000000000000000000000000000000000000000000000000000000000000000000004a5294a4093190888aa800000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff034c642727ff
def q1r3 : Nat := 0x1100000011000000110000001100000011000000110000001100000011000000110000001100000011000000110000001100000011000000110000001100000000000000000000000000000000000000000000000000000000000000000000000000000000000318c631a22420b13115400000000000000000000000000000000000000000000000000000000000000000000000000000000000f801f8c9087c4c4ff
def q1r5 : Nat := 0x111100000000000011110000000000001111000000000000111100000000000011110000000000001111000000000000111100000000000011110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018c6318c038342c2c3300000000000000000000000000000000000000000000000000000000000000000000000000000000001f07c0010e0f8f8f8cc
def q1r6 : Nat := 0x111100001111000000000000000000001111000011110000000000000000000011110000111100000000000000000000111100001111000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000039ce739f03e803fc03c0000000000000000000000000000000000000000000000000000000000000000000000000000000003e000000e0ff00ff00f0
def q1r7 : Nat := 0x1111000011110000111100001111000000000000000000000000000000000000111100001111000011110000111100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a5294a53f400013534000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fe0ff0000ffff00
def q1r8 : Nat := 0x1111000011110000111100001111000011110000111100001111000011110000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c6318c60dc14b4000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fff8000ffffff000000
def q1 : Prob := ⟨⟨0x1111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffff, 0x3fffffffffffffffffff, 0x111100001111000011110000111000001111000011110000111100001100000011110000101000001111000010100000100000001000000010000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffff, 0x0⟩, [0, 0, q1r2, q1r3, 0, q1r5, q1r6, q1r7, q1r8], [0, 1, 4], [q1r2, q1r3, q1r5, q1r6, q1r7, q1r8]⟩
def q1L : List Lane := []
def q1M : List Nat := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1ok : POK q1 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1mu : musOf q1 q1L = q1M := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1bi : q1.P.bias = encL (q1M.map fun _ => 64) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1nd : q1.req.Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1s : subOK q1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1c0 : rootChk q1.P 8 7 0 q1M (q1L.map Prod.snd) q1.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1c1 : rootChk q1.P 8 6 1 q1M (q1L.map Prod.snd) q1.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1c2 : rootChk q1.P 8 5 2 q1M (q1L.map Prod.snd) q1.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1c3 : rootChk q1.P 8 4 3 q1M (q1L.map Prod.snd) q1.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1c4 : rootChk q1.P 8 3 4 q1M (q1L.map Prod.snd) q1.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1c5 : rootChk q1.P 8 2 5 q1M (q1L.map Prod.snd) q1.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1c6 : rootChk q1.P 8 1 6 q1M (q1L.map Prod.snd) q1.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1c7 : rootChk q1.P 8 0 7 q1M (q1L.map Prod.snd) q1.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1cs : ∀ T ≤ 7, rootChk q1.P (7 + 1) (7 - T) T (musOf q1 q1L) (q1L.map Prod.snd) q1.req = true := by
  intro T hT
  rw [q1mu]
  interval_cases T
  · exact q1c0
  · exact q1c1
  · exact q1c2
  · exact q1c3
  · exact q1c4
  · exact q1c5
  · exact q1c6
  · exact q1c7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q1LB : LBc [0, 1, 4] 8 := probLB (p := q1) q1ok q1s q1nd (ls := q1L) (K := 7) (by simp [q1L]) q1bi q1cs
def q2r1 : Nat := 0x40400000404000004040000040400000404000004040000040400000404000004040000040400000404000004040000040400000404000004040000040400000000000000000000000000000000000000000000000000000000000000000000000000000000015ad6b54b04b302b32a8000000000000000000000000000000000000000000000000000000000000000000000000000000000000007d2c12cc0fccff
def q2r3 : Nat := 0x5000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000000000000000000000000000000000000000000000000000000000000000000000000000000000f7bdef82a8c2b33c330000000000000000000000000000000000000000000000000000000000000000000000000000000000001f0020fa30fccf0cc
def q2r5 : Nat := 0x5050000000000000505000000000000050500000000000005050000000000000505000000000000050500000000000005050000000000000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000318c630030e8282abc000000000000000000000000000000000000000000000000000000000000000000000000000000000003e0f8030c3f0f0fff0
def q2r6 : Nat := 0x5050000050500000000000000000000050500000505000000000000000000000505000005050000000000000000000005050000050500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a5294aa03a003d401540000000000000000000000000000000000000000000000000000000000000000000000000000000007c0007fc0fc00ff00ff
def q2r7 : Nat := 0x5050000050500000505000005050000000000000000000000000000000000000505000005050000050500000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ce739cffc00017d54000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f83ff0000ffff00
def q2r8 : Nat := 0x50500000505000005050000050500000505000005050000050500000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010842105d451540000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fff003ffffff000000
def q2 : Prob := ⟨⟨0x5050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505000005050000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000007ffffffffffffffffff, 0x7ffffffffffffffffff, 0x505000005050000050500000500000005050000050500000505000005000000050500000404000005050000000000000404000004040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007ffffffffffffffffff, 0x0⟩, [0, q2r1, 0, q2r3, 0, q2r5, q2r6, q2r7, q2r8], [0, 2, 4], [q2r1, q2r3, q2r5, q2r6, q2r7, q2r8]⟩
def q2L : List Lane := []
def q2M : List Nat := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2ok : POK q2 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2mu : musOf q2 q2L = q2M := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2bi : q2.P.bias = encL (q2M.map fun _ => 64) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2nd : q2.req.Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2s : subOK q2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2c0 : rootChk q2.P 7 6 0 q2M (q2L.map Prod.snd) q2.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2c1 : rootChk q2.P 7 5 1 q2M (q2L.map Prod.snd) q2.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2c2 : rootChk q2.P 7 4 2 q2M (q2L.map Prod.snd) q2.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2c3 : rootChk q2.P 7 3 3 q2M (q2L.map Prod.snd) q2.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2c4 : rootChk q2.P 7 2 4 q2M (q2L.map Prod.snd) q2.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2c5 : rootChk q2.P 7 1 5 q2M (q2L.map Prod.snd) q2.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2c6 : rootChk q2.P 7 0 6 q2M (q2L.map Prod.snd) q2.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2cs : ∀ T ≤ 6, rootChk q2.P (6 + 1) (6 - T) T (musOf q2 q2L) (q2L.map Prod.snd) q2.req = true := by
  intro T hT
  rw [q2mu]
  interval_cases T
  · exact q2c0
  · exact q2c1
  · exact q2c2
  · exact q2c3
  · exact q2c4
  · exact q2c5
  · exact q2c6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2LB : LBc [0, 2, 4] 7 := probLB (p := q2) q2ok q2s q2nd (ls := q2L) (K := 6) (by simp [q2L]) q2bi q2cs
def q3r1 : Nat := 0x440000004400000044000000440000004400000044000000440000004400000044000000440000004400000044000000440000004400000044000000440000000000000000000000000000000000000000000000000000000000000000000000000000000008c6318c65021902644a800000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff9408660d93ff
def q3r2 : Nat := 0x500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000005000000050000000500000000000000000000000000000000000000000000000000000000000000000000000000000000005294a5280ac60c8829140000000000000000000000000000000000000000000000000000000000000000000000000000000000007c1f07b187321e4f
def q3r5 : Nat := 0x5500000000000000550000000000000055000000000000005500000000000000550000000000000055000000000000005500000000000000550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018c6318c0305460d0e300000000000000000000000000000000000000000000000000000000000000000000000000000000001ff800018c1f9c3e38c
def q3r6 : Nat := 0x55000000550000000000000000000000550000005500000000000000000000005500000055000000000000000000000055000000550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000318c6319039007d00b40000000000000000000000000000000000000000000000000000000000000000000000000000000003e0003e0e0fe01fc03f0
def q3r7 : Nat := 0x55000000550000005500000055000000000000000000000000000000000000005500000055000000550000005500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a5294a53f4000172d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffc00ff0001fffc00
def q3r8 : Nat := 0x55000000550000005500000055000000550000005500000055000000550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c6318c62fc6ab8000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff00000fffffe000000
def q3 : Prob := ⟨⟨0x55000000550000005500000055000000550000005500000055000000550000005500000055000000550000005500000055000000550000005500000055000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffff, 0x3fffffffffffffffffff, 0x5500000055000000550000005000000055000000550000005500000040000000550000005400000055000000500000004400000044000000400000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffff, 0x0⟩, [0, q3r1, q3r2, 0, 0, q3r5, q3r6, q3r7, q3r8], [0, 3, 4], [q3r1, q3r2, q3r5, q3r6, q3r7, q3r8]⟩
def q3L : List Lane := []
def q3M : List Nat := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3ok : POK q3 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3mu : musOf q3 q3L = q3M := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3bi : q3.P.bias = encL (q3M.map fun _ => 64) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3nd : q3.req.Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3s : subOK q3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3c0 : rootChk q3.P 8 7 0 q3M (q3L.map Prod.snd) q3.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3c1 : rootChk q3.P 8 6 1 q3M (q3L.map Prod.snd) q3.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3c2 : rootChk q3.P 8 5 2 q3M (q3L.map Prod.snd) q3.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3c3 : rootChk q3.P 8 4 3 q3M (q3L.map Prod.snd) q3.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3c4 : rootChk q3.P 8 3 4 q3M (q3L.map Prod.snd) q3.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3c5 : rootChk q3.P 8 2 5 q3M (q3L.map Prod.snd) q3.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3c6 : rootChk q3.P 8 1 6 q3M (q3L.map Prod.snd) q3.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3c7 : rootChk q3.P 8 0 7 q3M (q3L.map Prod.snd) q3.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3cs : ∀ T ≤ 7, rootChk q3.P (7 + 1) (7 - T) T (musOf q3 q3L) (q3L.map Prod.snd) q3.req = true := by
  intro T hT
  rw [q3mu]
  interval_cases T
  · exact q3c0
  · exact q3c1
  · exact q3c2
  · exact q3c3
  · exact q3c4
  · exact q3c5
  · exact q3c6
  · exact q3c7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q3LB : LBc [0, 3, 4] 8 := probLB (p := q3) q3ok q3s q3nd (ls := q3L) (K := 7) (by simp [q3L]) q3bi q3cs
def q4r1 : Nat := 0x444400004444000000000000000000004444000044440000000000000000000044440000444400000000000000000000444400004444000000000000000000000000000000000000000000000000000000000000000000000000000000000b5ad6b5ac918cb194948000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fb24633c65273
def q4r2 : Nat := 0x5050000050500000000000000000000050500000505000000000000000000000505000005050000000000000000000005050000050500000000000000000000000000000000000000000000000000000000000000000000000000000000004a5294a40461042024a40000000000000000000000000000000000000000000000000000000000000000000000000000000000007fff039843087fff
def q4r3 : Nat := 0x550000005500000000000000000000005500000055000000000000000000000055000000550000000000000000000000550000005500000000000000000000000000000000000000000000000000000000000000000000000000000000000318c6318a180a3c18a500000000000000000000000000000000000000000000000000000000000000000000000000000000001f003e03c607cf0639c
def q4r5 : Nat := 0x55550000000000000000000000000000555500000000000000000000000000005555000000000000000000000000000055550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018c6318c01d402b40f80000000000000000000000000000000000000000000000000000000000000000000000000000000003e0f8000c07f80ff83e0
def q4r7 : Nat := 0x555500005555000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a5294a53fa00014bd00000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffc00ff8000fffc00
def q4r8 : Nat := 0x555500005555000000000000000000005555000055550000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c6318c635e2b5c000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff00000ffffff000000
def q4 : Prob := ⟨⟨0x555500005555000000000000000000005555000055550000000000000000000055550000555500000000000000000000555500005555000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffff, 0x3fffffffffffffffffff, 0x55550000555000000000000000000000555500005540000000000000000000005555000050500000000000000000000050400000504000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffff, 0x0⟩, [0, q4r1, q4r2, q4r3, 0, q4r5, 0, q4r7, q4r8], [0, 4, 6], [q4r1, q4r2, q4r3, q4r5, q4r7, q4r8]⟩
def q4L : List Lane := []
def q4M : List Nat := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4ok : POK q4 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4mu : musOf q4 q4L = q4M := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4bi : q4.P.bias = encL (q4M.map fun _ => 64) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4nd : q4.req.Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4s : subOK q4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4c0 : rootChk q4.P 8 7 0 q4M (q4L.map Prod.snd) q4.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4c1 : rootChk q4.P 8 6 1 q4M (q4L.map Prod.snd) q4.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4c2 : rootChk q4.P 8 5 2 q4M (q4L.map Prod.snd) q4.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4c3 : rootChk q4.P 8 4 3 q4M (q4L.map Prod.snd) q4.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4c4 : rootChk q4.P 8 3 4 q4M (q4L.map Prod.snd) q4.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4c5 : rootChk q4.P 8 2 5 q4M (q4L.map Prod.snd) q4.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4c6 : rootChk q4.P 8 1 6 q4M (q4L.map Prod.snd) q4.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4c7 : rootChk q4.P 8 0 7 q4M (q4L.map Prod.snd) q4.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4cs : ∀ T ≤ 7, rootChk q4.P (7 + 1) (7 - T) T (musOf q4 q4L) (q4L.map Prod.snd) q4.req = true := by
  intro T hT
  rw [q4mu]
  interval_cases T
  · exact q4c0
  · exact q4c1
  · exact q4c2
  · exact q4c3
  · exact q4c4
  · exact q4c5
  · exact q4c6
  · exact q4c7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q4LB : LBc [0, 4, 6] 8 := probLB (p := q4) q4ok q4s q4nd (ls := q4L) (K := 7) (by simp [q4L]) q4bi q4cs
def q5r1 : Nat := 0x444444444444444400000000000000000000000000000000000000000000000044444444444444440000000000000000000000000000000000000000000000000000000000000000000000000000000000b5ad6b32314c9949948000000000000000000000000000000000000000000000000000000000000000000000000000000000000007cc8c5b3673673
def q5r2 : Nat := 0x5050505050505050000000000000000000000000000000000000000000000000505050505050505000000000000000000000000000000000000000000000000000000000000000000000000000000000014a5294c0c23060a60a40000000000000000000000000000000000000000000000000000000000000000000000000000000000000fff0309c387f87f
def q5r3 : Nat := 0x55005500550055000000000000000000000000000000000000000000000000005500550055005500000000000000000000000000000000000000000000000000000000000000000000000000000000000010842103000a145145000000000000000000000000000000000000000000000000000000000000000000000000000000000003fff800c0e7cf9cf9c
def q5r4 : Nat := 0x555500005555000000000000000000000000000000000000000000000000000055550000555500000000000000000000000000000000000000000000000000000000000000000000000000000000000001ef7bdefc03e02b82b80000000000000000000000000000000000000000000000000000000000000000000000000000000000001f003f00f80fe0fe0
def q5r5 : Nat := 0x555555550000000000000000000000000000000000000000000000000000000055555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000739ce7aba8003ffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000007c00003fff000fff000
def q5r8 : Nat := 0x5555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018c63185457f5c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fe0003ffffff000000
def q5 : Prob := ⟨⟨0x555555555555555500000000000000000000000000000000000000000000000055555555555555550000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000007ffffffffffffffffff, 0x7ffffffffffffffffff, 0x55555555554055400000000000000000000000000000000000000000000000005540504055405040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007ffffffffffffffffff, 0x0⟩, [0, q5r1, q5r2, q5r3, q5r4, q5r5, 0, 0, q5r8], [0, 6, 7], [q5r1, q5r2, q5r3, q5r4, q5r5, q5r8]⟩
def q5L : List Lane := []
def q5M : List Nat := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5ok : POK q5 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5mu : musOf q5 q5L = q5M := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5bi : q5.P.bias = encL (q5M.map fun _ => 64) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5nd : q5.req.Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5s : subOK q5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5c0 : rootChk q5.P 7 6 0 q5M (q5L.map Prod.snd) q5.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5c1 : rootChk q5.P 7 5 1 q5M (q5L.map Prod.snd) q5.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5c2 : rootChk q5.P 7 4 2 q5M (q5L.map Prod.snd) q5.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5c3 : rootChk q5.P 7 3 3 q5M (q5L.map Prod.snd) q5.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5c4 : rootChk q5.P 7 2 4 q5M (q5L.map Prod.snd) q5.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5c5 : rootChk q5.P 7 1 5 q5M (q5L.map Prod.snd) q5.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5c6 : rootChk q5.P 7 0 6 q5M (q5L.map Prod.snd) q5.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5cs : ∀ T ≤ 6, rootChk q5.P (6 + 1) (6 - T) T (musOf q5 q5L) (q5L.map Prod.snd) q5.req = true := by
  intro T hT
  rw [q5mu]
  interval_cases T
  · exact q5c0
  · exact q5c1
  · exact q5c2
  · exact q5c3
  · exact q5c4
  · exact q5c5
  · exact q5c6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q5LB : LBc [0, 6, 7] 7 := probLB (p := q5) q5ok q5s q5nd (ls := q5L) (K := 6) (by simp [q5L]) q5bi q5cs
def q6r0 : Nat := 0xaaaa0000aaaa0000000000000000000000000000000000000000000000000000aaaa0000aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000008c6318c4848c9044994800000000000000000000000000000000000000000000000000000000000000000000000000000000000f801f21232639f673
def q6r1 : Nat := 0xcccc0000cccc0000000000000000000000000000000000000000000000000000cccc0000cccc0000000000000000000000000000000000000000000000000000000000000000000000000000000006318c63218304c9120a400000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff860c3f26487f
def q6r2 : Nat := 0xf0f00000f0f00000000000000000000000000000000000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000094a52948e0c0a20e14500000000000000000000000000000000000000000000000000000000000000000000000000000000000007fe0383039c78f9c
def q6r3 : Nat := 0xff000000ff000000000000000000000000000000000000000000000000000000ff000000ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000294a5297002a05e02b800000000000000000000000000000000000000000000000000000000000000000000000000000000001f07c00c03fc1f80fe0
def q6r5 : Nat := 0xffff000000000000000000000000000000000000000000000000000000000000ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000318c631b520007bb4000000000000000000000000000000000000000000000000000000000000000000000000000000000003e0f8000ffc001fff000
def q6r8 : Nat := 0xffff0000ffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c6318c60add5f8000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ff00000fffffe000000
def q6 : Prob := ⟨⟨0xffff0000ffff0000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffff, 0x3fffffffffffffffffff, 0xffff0000ffc80000000000000000000000000000000000000000000000000000faea0000f8c800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffff, 0x0⟩, [q6r0, q6r1, q6r2, q6r3, 0, q6r5, 0, 0, q6r8], [4, 6, 7], [q6r0, q6r1, q6r2, q6r3, q6r5, q6r8]⟩
def q6L : List Lane := []
def q6M : List Nat := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6ok : POK q6 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6mu : musOf q6 q6L = q6M := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6bi : q6.P.bias = encL (q6M.map fun _ => 64) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6nd : q6.req.Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6s : subOK q6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6c0 : rootChk q6.P 8 7 0 q6M (q6L.map Prod.snd) q6.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6c1 : rootChk q6.P 8 6 1 q6M (q6L.map Prod.snd) q6.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6c2 : rootChk q6.P 8 5 2 q6M (q6L.map Prod.snd) q6.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6c3 : rootChk q6.P 8 4 3 q6M (q6L.map Prod.snd) q6.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6c4 : rootChk q6.P 8 3 4 q6M (q6L.map Prod.snd) q6.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6c5 : rootChk q6.P 8 2 5 q6M (q6L.map Prod.snd) q6.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6c6 : rootChk q6.P 8 1 6 q6M (q6L.map Prod.snd) q6.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6c7 : rootChk q6.P 8 0 7 q6M (q6L.map Prod.snd) q6.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6cs : ∀ T ≤ 7, rootChk q6.P (7 + 1) (7 - T) T (musOf q6 q6L) (q6L.map Prod.snd) q6.req = true := by
  intro T hT
  rw [q6mu]
  interval_cases T
  · exact q6c0
  · exact q6c1
  · exact q6c2
  · exact q6c3
  · exact q6c4
  · exact q6c5
  · exact q6c6
  · exact q6c7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q6LB : LBc [4, 6, 7] 8 := probLB (p := q6) q6ok q6s q6nd (ls := q6L) (K := 7) (by simp [q6L]) q6bi q6cs
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr012 : LBc [0, 1, 2] 7 := q0LB.move sg0 sgb0 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr014 : LBc [0, 1, 4] 8 := q1LB.move sg0 sgb0 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr015 : LBc [0, 1, 5] 7 := q0LB.move sg2 sgb2 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr016 : LBc [0, 1, 6] 8 := q1LB.move sg2 sgb2 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr024 : LBc [0, 2, 4] 7 := q2LB.move sg0 sgb0 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr027 : LBc [0, 2, 7] 7 := q2LB.move sg4 sgb4 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr034 : LBc [0, 3, 4] 8 := q3LB.move sg0 sgb0 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr045 : LBc [0, 4, 5] 8 := q1LB.move sg1 sgb1 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr046 : LBc [0, 4, 6] 8 := q4LB.move sg0 sgb0 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr047 : LBc [0, 4, 7] 8 := q4LB.move sg1 sgb1 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr048 : LBc [0, 4, 8] 7 := q2LB.move sg1 sgb1 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr057 : LBc [0, 5, 7] 8 := q1LB.move sg3 sgb3 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr058 : LBc [0, 5, 8] 7 := q0LB.move sg1 sgb1 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr067 : LBc [0, 6, 7] 7 := q5LB.move sg0 sgb0 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr068 : LBc [0, 6, 8] 7 := q2LB.move sg5 sgb5 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr123 : LBc [1, 2, 3] 7 := q0LB.move sg6 sgb6 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr126 : LBc [1, 2, 6] 8 := q1LB.move sg8 sgb8 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr127 : LBc [1, 2, 7] 8 := q1LB.move sg4 sgb4 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr134 : LBc [1, 3, 4] 7 := q2LB.move sg6 sgb6 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr136 : LBc [1, 3, 6] 7 := q2LB.move sg8 sgb8 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr146 : LBc [1, 4, 6] 8 := q4LB.move sg2 sgb2 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr147 : LBc [1, 4, 7] 7 := q5LB.move sg2 sgb2 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr156 : LBc [1, 5, 6] 7 := q2LB.move sg2 sgb2 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr157 : LBc [1, 5, 7] 7 := q2LB.move sg3 sgb3 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr167 : LBc [1, 6, 7] 8 := q4LB.move sg8 sgb8 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr168 : LBc [1, 6, 8] 8 := q3LB.move sg2 sgb2 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr234 : LBc [2, 3, 4] 8 := q1LB.move sg6 sgb6 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr237 : LBc [2, 3, 7] 8 := q1LB.move sg11 sgb11 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr238 : LBc [2, 3, 8] 7 := q0LB.move sg10 sgb10 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr246 : LBc [2, 4, 6] 7 := q5LB.move sg4 sgb4 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr247 : LBc [2, 4, 7] 8 := q4LB.move sg11 sgb11 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr257 : LBc [2, 5, 7] 8 := q3LB.move sg3 sgb3 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr267 : LBc [2, 6, 7] 8 := q4LB.move sg4 sgb4 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr268 : LBc [2, 6, 8] 7 := q2LB.move sg10 sgb10 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr278 : LBc [2, 7, 8] 7 := q2LB.move sg11 sgb11 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr345 : LBc [3, 4, 5] 7 := q2LB.move sg7 sgb7 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr346 : LBc [3, 4, 6] 8 := q4LB.move sg7 sgb7 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr347 : LBc [3, 4, 7] 8 := q4LB.move sg6 sgb6 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr348 : LBc [3, 4, 8] 8 := q1LB.move sg7 sgb7 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr357 : LBc [3, 5, 7] 7 := q2LB.move sg9 sgb9 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr358 : LBc [3, 5, 8] 7 := q0LB.move sg7 sgb7 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr367 : LBc [3, 6, 7] 7 := q5LB.move sg6 sgb6 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr368 : LBc [3, 6, 8] 8 := q1LB.move sg10 sgb10 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr456 : LBc [4, 5, 6] 7 := q5LB.move sg3 sgb3 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr457 : LBc [4, 5, 7] 8 := q4LB.move sg3 sgb3 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr467 : LBc [4, 6, 7] 8 := q6LB.move sg0 sgb0 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr468 : LBc [4, 6, 8] 8 := q4LB.move sg10 sgb10 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr478 : LBc [4, 7, 8] 7 := q5LB.move sg5 sgb5 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr567 : LBc [5, 6, 7] 8 := q4LB.move sg9 sgb9 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr568 : LBc [5, 6, 8] 8 := q1LB.move sg5 sgb5 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr578 : LBc [5, 7, 8] 8 := q1LB.move sg9 sgb9 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tr678 : LBc [6, 7, 8] 8 := q4LB.move sg5 sgb5 (by decide +kernel)


def prr1 : Nat := 0x444400004444000044440000444400004444000044440000444400004444000044440000444400004444000044440000444400004444000044440000444400000000000000000000000000000000000000000000000000000000000000001264c993264c992964024632022c6509129480000000000000000000000000000000000000000000000000000000000000000000000000fe03fa5900918cc0cf1943e7e73
def prr2 : Nat := 0x505000005050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505000000000000000000000000000000000000000000000000000000000000000000891224489122440024c1841208080a2444a4000000000000000000000000000000000000000000000000000000000000000000000007f01fff801d30610c93021fc993ff
def prr3 : Nat := 0x55000000550000005500000055000000550000005500000055000000550000005500000055000000550000005500000055000000550000005500000055000000000000000000000000000000000000000000000000000000000000000000074e9d3a74e9d3b050906028c70f061c38a5000000000000000000000000000000000000000000000000000000000000000000001fc00001fc041e24181f31c3c18f1e39c
def prr5 : Nat := 0x5555000000000000555500000000000055550000000000005555000000000000555500000000000055550000000000005555000000000000555500000000000000000000000000000000000000000000000000000000000000000000000001c3870e1c3870e000e07500b00ad03f80f80000000000000000000000000000000000000000000000000000000000000000000fe03f8000000060381fe03e03fe0fe03e0
def prr6 : Nat := 0x55550000555500000000000000000000555500005555000000000000000000005555000055550000000000000000000055550000555500000000000000000000000000000000000000000000000000000000000000000000000000000000058b162c58b162d400f90000fdd00036ed00000000000000000000000000000000000000000000000000000000000000000007f0000000fe0007803fe0003ffc000fffc00
def prr7 : Nat := 0x55550000555500005555000055550000000000000000000000000000000000005555000055550000555500005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000162c58b162c58b1ffd0000004f752f40000000000000000000000000000000000000000000000000000000000000000000000000003fff000007ffc000003ffffff000000
def prr8 : Nat := 0x55550000555500005555000055550000555500005555000055550000555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000183060c183060c0baf068ad7000000000000000000000000000000000000000000000000000000000000000000000000000007ffffc000000007ffffffffc000000000000
def pr : Prob := ⟨⟨0x555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500000000000000000000000000000000000000000000000000000000000000001fffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffff, 0x7fffffffffffffffffffffffffffffffffff, 0x55550000555500005555000055500000555500005555000055550000554000005555000054540000555500005050000054440000544400005040000050400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffff, 0x40404040404040⟩, [0, prr1, prr2, prr3, 0, prr5, prr6, prr7, prr8], [0, 4], [prr1, prr2, prr3, prr5, prr6, prr7, prr8]⟩
def prL : List Lane := [([0, 1, 4], 8), ([0, 2, 4], 7), ([0, 3, 4], 8), ([0, 4, 5], 8), ([0, 4, 6], 8), ([0, 4, 7], 8), ([0, 4, 8], 7)]
def prM : List Nat := [0x1111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x505000005050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x55000000550000005500000055000000550000005500000055000000550000005500000055000000550000005500000055000000550000005500000055000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x55550000000000005555000000000000555500000000000055550000000000005555000000000000555500000000000055550000000000005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x555500005555000000000000000000005555000055550000000000000000000055550000555500000000000000000000555500005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x55550000555500005555000055550000000000000000000000000000000000005555000055550000555500005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x555500005555000055550000555500005555000055550000555500005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prok : POK pr :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prmu : musOf pr prL = prM := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prbi : pr.P.bias = encL (prM.map fun _ => 64) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prnd : pr.req.Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prs : subOK pr = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc0 : rootChk pr.P 11 10 0 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc1 : rootChk pr.P 11 9 1 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc2 : rootChk pr.P 11 8 2 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc3 : rootChk pr.P 11 7 3 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc4 : rootChk pr.P 11 6 4 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc5 : rootChk pr.P 11 5 5 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc6 : rootChk pr.P 11 4 6 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc7 : rootChk pr.P 11 3 7 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc8 : rootChk pr.P 11 2 8 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc9 : rootChk pr.P 11 1 9 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prc10 : rootChk pr.P 11 0 10 prM (prL.map Prod.snd) pr.req = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prcs : ∀ T ≤ 10, rootChk pr.P (10 + 1) (10 - T) T (musOf pr prL) (prL.map Prod.snd) pr.req = true := by
  intro T hT
  rw [prmu]
  interval_cases T
  · exact prc0
  · exact prc1
  · exact prc2
  · exact prc3
  · exact prc4
  · exact prc5
  · exact prc6
  · exact prc7
  · exact prc8
  · exact prc9
  · exact prc10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prH : ∀ l ∈ prL, LBc l.1 l.2 ∧ (∀ i ∈ pr.Z, i ∈ l.1) ∧ mskB pr (muOf pr l.1) = true := by
  have h2 : ∀ l ∈ prL, (∀ i ∈ pr.Z, i ∈ l.1) ∧ mskB pr (muOf pr l.1) = true := by decide +kernel
  intro l hl
  refine ⟨?_, h2 l hl⟩
  simp only [prL, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tr014
  · exact tr024
  · exact tr034
  · exact tr045
  · exact tr046
  · exact tr047
  · exact tr048
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma prLB : LBc [0, 4] 11 := probLB (p := pr) prok prs prnd (ls := prL) (K := 10) prH (by rw [prmu]; exact prbi) prcs
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pa04 : LBc [0, 4] 11 := prLB.move sg0 sgb0 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pa16 : LBc [1, 6] 11 := prLB.move sg2 sgb2 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pa27 : LBc [2, 7] 11 := prLB.move sg4 sgb4 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pa34 : LBc [3, 4] 11 := prLB.move sg6 sgb6 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pa57 : LBc [5, 7] 11 := prLB.move sg3 sgb3 (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pa68 : LBc [6, 8] 11 := prLB.move sg5 sgb5 (by decide +kernel)


lemma LB.ins {top tgt μ L : Nat} {m : Mv} {X : Finset Nat} (hm : ∀ j, μ.testBit j = true → top.testBit j = true)
    (h : LB top tgt μ L X) (hg : good m) (ho : ops m ⊆ X) :
    LB top tgt μ (L - b2n (!(conB μ m.2.1 || conB μ m.2.2))) (insert (res top m) X) := by
  have hX : ops m ∪ X = X := Finset.union_eq_right.mpr ho
  cases hc : (conB μ m.2.1 || conB μ m.2.2)
  · simp only [Bool.not_false, b2n, Bool.cond_true]
    exact LB.step hm (by rw [hX]; exact h)
  · simp only [Bool.not_true, b2n, Bool.cond_false]
    refine LB.stepFree hm (by rw [hX]; exact h) hg ?_
    rcases Bool.or_eq_true_iff.mp hc with hc | hc
    · exact ⟨_, by simp [ops], (conB_iff _ _).mp hc⟩
    · exact ⟨_, by simp [ops], (conB_iff _ _).mp hc⟩

def stt (R8 : List Nat) (r0 n g : Bool) (rw nw gw : Nat) : List Nat :=
  cond r0 [rw] [] ++ R8 ++ cond n [nw] [] ++ cond g [gw] []
lemma stt_sub (R8 : List Nat) (x n G : Bool) (r nw gw : Nat) : (stt R8 x n G r nw gw).Sublist (r :: R8 ++ [nw, gw]) := by
  have e : r :: R8 ++ [nw, gw] = [r] ++ R8 ++ [nw] ++ [gw] := by simp
  have c : ∀ (b : Bool) (y : Nat), (cond b [y] []).Sublist [y] := by intro b y; cases b <;> simp
  rw [e]
  exact (((c x r).append (List.Sublist.refl R8)).append (c n nw)).append (c G gw)
def lsN (useN : Bool) (r0 : Nat) (mus Ls : List Nat) : List Nat :=
  List.zipWith (fun m L => L - b2n (useN && !(conB m r0 || conB m r0))) mus Ls
def lsG (useG : Bool) (a b : Nat) (mus Ls : List Nat) : List Nat :=
  List.zipWith (fun m L => L - b2n (useG && !(conB m a || conB m b))) mus Ls

-- what has to be checked for a second gate reading the words a and b
structure Good (p : Prob) (ls : List Lane) (r0 : Nat) (R8 : List Nat) (a b : Nat) (gn : Bool) : Prop where
  sub : ∀ r ∈ R8, Nat.beq (uni p.P.full ((r0 :: R8 ++ [neg p.P.top r0, Nat.land a b]).filter (fun x => !Nat.beq x r))) p.P.full = false
  one : Nat.beq (uni p.P.full (R8 ++ [Nat.land a b])) p.P.full = false
  nd : (r0 :: R8 ++ [neg p.P.top r0, Nat.land a b]).Nodup
  ne : a ≠ b
  mem : (a ∈ p.W ∧ b ∈ p.W) ∨ (gn = true ∧ a ∈ p.W ++ [neg p.P.top r0] ∧ b ∈ p.W ++ [neg p.P.top r0])
  chk : ∀ T ≤ 1, ∀ x n : Bool, (x || n) = true →
    rootChk p.P 14 12 T (musOf p ls)
      (lsG true a b (musOf p ls) (lsN (n || gn) r0 (musOf p ls) (ls.map Prod.snd))) (stt R8 x n true r0 (neg p.P.top r0) (Nat.land a b)) = true

lemma getD_zip {f : Nat → Nat → Nat} {l r : List Nat} {i : Nat} (hl : i < l.length) (hr : i < r.length) :
    (List.zipWith f l r).getD i 0 = f (l.getD i 0) (r.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_zipWith]; omega), List.getElem_zipWith,
    List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hr]

lemma mainNo {p : Prob} (hp : POK p) {ls : List Lane}
    (hls : ∀ l ∈ ls, LBc l.1 l.2 ∧ (∀ i ∈ p.Z, i ∈ l.1) ∧ mskB p (muOf p l.1) = true)
    (hbi : p.P.bias = encL ((musOf p ls).map fun _ => 64)) {r0 : Nat} {R8 : List Nat}
    (hr0 : r0 ∈ p.W) (hW : ∀ a ∈ p.W, a ∈ r0 :: R8) (hR8 : ∀ a ∈ R8, a ∈ p.W)
    (hbase : ∀ T ≤ 1, ∀ x n : Bool, (x || n) = true →
      rootChk p.P 14 12 T (musOf p ls) (lsG false 0 0 (musOf p ls) (lsN n r0 (musOf p ls) (ls.map Prod.snd)))
        (stt R8 x n false r0 (neg p.P.top r0) 0) = true)
    {a b : Nat} {gn : Bool} (hgd : Good p ls r0 R8 a b gn)
    (w : List Nat) (hw : ∀ x ∈ w, x ∈ r0 :: R8 ++ [neg p.P.top r0, Nat.land a b]) (hwv : ∀ x ∈ w, Val p.P.top x)
    (gs : List Gate) (o : Nat) (hl : legal gs) (hlen : gs.length = 13) (hnot : gs.countP isNot = 1)
    (hc : ∀ j, p.P.top.testBit j = true → (Circuit.mk gs o).eval (w.map (fun a => a.testBit j)) = p.P.tgt.testBit j) : False := by
  have hmem : p.P.tgt ∈ exec p.P.top gs w := tgt_mem hp.t0 hp.valT gs hl o w hwv hc
  obtain ⟨ms, S, hd, hS, hB, hN⟩ := extract hp.t0 hp.t1 gs w hwv hl hmem
  have hcn := cntNot gs
  have hB' : nb ms ≤ 12 := by omega
  have hN' : nu ms ≤ 1 := by omega
  have hSc : ∀ x ∈ S, x ∈ r0 :: R8 ++ [neg p.P.top r0, Nat.land a b] := fun x hx => hw x (hS x hx).1
  have h8 : ∀ r ∈ R8, r ∈ S := fun r hr => need hp hd hSc (hgd.sub r hr)
  have h1 : r0 ∈ S ∨ neg p.P.top r0 ∈ S := by
    by_contra hn; push Not at hn
    have : uni p.P.full (R8 ++ [Nat.land a b]) = p.P.full := by
      apply eq_full
      · intro i hi
        obtain ⟨x, hx, hb⟩ := hd.sep hp.gd i hi
        rw [uni_bit]
        refine ⟨x, ?_, ?_⟩
        · have := hSc x hx
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this ⊢
          rcases this with rfl | h | rfl | rfl
          · exact absurd hx hn.1
          · exact Or.inl h
          · exact absurd hx hn.2
          · exact Or.inr rfl
        · rw [sep_bit _ _ _ _ hi] at hb ⊢
          revert hb
          by_cases hT : 1 ≤ nu ms <;> simp only [hT, decide_true, decide_false] <;>
            cases x.testBit i <;> cases x.testBit (402 + i) <;> simp
      · intro i hb
        obtain ⟨x, _, hb⟩ := (uni_bit _ _ _).mp hb
        by_contra hn
        rw [sep_bit_off _ _ _ _ (by simpa using hn)] at hb; exact absurd hb (by decide)
    have h2 := hgd.one
    rw [this, Nat.beq_refl] at h2; exact absurd h2 (by decide)
  classical
  have hSeq : ∀ G : Bool, (Nat.land a b ∈ S ↔ G = true) → ∀ gw, (G = true → gw = Nat.land a b) →
      S = (stt R8 (decide (r0 ∈ S)) (decide (neg p.P.top r0 ∈ S)) G r0 (neg p.P.top r0) gw).toFinset := by
    intro G hG gw hgw
    ext x
    rw [List.mem_toFinset]
    constructor
    · intro hx
      have := hSc x hx
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this
      unfold stt
      rcases this with rfl | h | rfl | rfl
      · simp [hx]
      · simp [h]
      · simp [hx]
      · have hG1 := hG.mp hx
        rw [hG1, hgw hG1]; simp
    · intro hx
      unfold stt at hx
      simp only [List.mem_append] at hx
      rcases hx with ((hx | hx) | hx) | hx
      · by_cases h : r0 ∈ S
        · simp [h] at hx; subst hx; exact h
        · simp [h] at hx
      · exact h8 x hx
      · by_cases h : neg p.P.top r0 ∈ S
        · simp [h] at hx; subst hx; exact h
        · simp [h] at hx
      · cases G
        · simp at hx
        · simp at hx; subst hx; rw [hgw rfl]; exact hG.mpr rfl
  have hmul : (musOf p ls).length = ls.length := by simp [musOf]
  have hmu : ∀ i (hi : i < ls.length), (musOf p ls).getD i 0 = muOf p (ls[i]).1 := by
    intro i hi; unfold musOf; rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp
  have hmsk : ∀ i < (musOf p ls).length, Msk p.P.top p.P.tgt ((musOf p ls).getD i 0) := by
    intro i hi; rw [hmul] at hi
    rw [hmu i hi]; exact mskOK (hls _ (List.getElem_mem hi)).2.2
  have hLB0 : ∀ i < ls.length, LB p.P.top p.P.tgt ((musOf p ls).getD i 0) ((ls.map Prod.snd).getD i 0) p.W.toFinset := by
    intro i hi
    rw [hmu i hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]
    exact wordLB hp (hls _ (List.getElem_mem hi)).2.1 (hls _ (List.getElem_mem hi)).1
  have hLBn : ∀ u : Bool, ∀ i < ls.length, LB p.P.top p.P.tgt ((musOf p ls).getD i 0)
      ((lsN u r0 (musOf p ls) (ls.map Prod.snd)).getD i 0) (cond u (insert (neg p.P.top r0) p.W.toFinset) p.W.toFinset) := by
    intro u i hi
    unfold lsN
    rw [getD_zip (by omega) (by simpa using hi)]
    cases u
    · simp only [Bool.false_and, b2n, Bool.cond_false, Nat.sub_zero]; exact hLB0 i hi
    · simp only [Bool.true_and, Bool.cond_true]
      exact (hLB0 i hi).ins (m := (none, r0, r0)) (hmsk i (by omega)).sub rfl
        (by intro x hx; simp [ops] at hx; subst hx; exact List.mem_toFinset.mpr hr0)
  have hlnN : ∀ u, (lsN u r0 (musOf p ls) (ls.map Prod.snd)).length = ls.length := by
    intro u; unfold lsN; rw [List.length_zipWith, hmul, List.length_map]; omega
  by_cases hgS : Nat.land a b ∈ S
  · have e := hSeq true ⟨fun _ => rfl, fun _ => hgS⟩ (Nat.land a b) (fun _ => rfl)
    have hnd := hgd.nd.sublist (stt_sub R8 (decide (r0 ∈ S)) (decide (neg p.P.top r0 ∈ S)) true r0 (neg p.P.top r0) (Nat.land a b))
    refine rootNo (f := 14) (B := 12) (T := nu ms) hp.gd hmsk hbi ?_ hnd ?_
      (hgd.chk _ hN' (decide (r0 ∈ S)) (decide (neg p.P.top r0 ∈ S)) (by simpa using h1)) (by rw [← e]; exact hd) hB' rfl
    · unfold lsG; rw [List.length_zipWith, hlnN, hmul]; omega
    · intro i hi
      rw [hmul] at hi
      rw [← e]
      unfold lsG
      rw [getD_zip (by omega) (by rw [hlnN]; exact hi)]
      simp only [Bool.true_and]
      have hab : ops (some false, a, b) ⊆ cond (decide (neg p.P.top r0 ∈ S) || gn) (insert (neg p.P.top r0) p.W.toFinset) p.W.toFinset := by
        intro x hx
        simp only [ops, Finset.mem_insert, Finset.mem_singleton] at hx
        have : (x ∈ p.W) ∨ (gn = true ∧ x ∈ p.W ++ [neg p.P.top r0]) := by
          rcases hgd.mem with ⟨ha, hb⟩ | ⟨h, ha, hb⟩
          · rcases hx with rfl | rfl
            · exact Or.inl ha
            · exact Or.inl hb
          · rcases hx with rfl | rfl
            · exact Or.inr ⟨h, ha⟩
            · exact Or.inr ⟨h, hb⟩
        rcases this with h | ⟨h, h'⟩
        · cases (decide (neg p.P.top r0 ∈ S) || gn)
          · exact List.mem_toFinset.mpr h
          · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h)
        · rw [h, Bool.or_true]
          change x ∈ insert (neg p.P.top r0) p.W.toFinset
          rw [Finset.mem_insert, List.mem_toFinset]
          rw [List.mem_append, List.mem_singleton] at h'; tauto
      refine ((hLBn (decide (neg p.P.top r0 ∈ S) || gn) i hi).ins (m := (some false, a, b)) (hmsk i (by omega)).sub hgd.ne hab).mono ?_
      intro x hx
      have := hSc x hx
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this
      have inW : ∀ y ∈ p.W, y ∈ cond (decide (neg p.P.top r0 ∈ S) || gn) (insert (neg p.P.top r0) p.W.toFinset) p.W.toFinset := by
        intro y hy
        cases (decide (neg p.P.top r0 ∈ S) || gn)
        · exact List.mem_toFinset.mpr hy
        · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hy)
      rcases this with rfl | h | rfl | rfl
      · exact Finset.mem_insert_of_mem (inW _ hr0)
      · exact Finset.mem_insert_of_mem (inW _ (hR8 _ h))
      · apply Finset.mem_insert_of_mem
        simp only [hx, decide_true, Bool.true_or, Bool.cond_true]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_self _ _
  · have e := hSeq false ⟨fun h => absurd h hgS, fun h => absurd h (by decide)⟩ 0 (fun h => absurd h (by decide))
    have hnd : (stt R8 (decide (r0 ∈ S)) (decide (neg p.P.top r0 ∈ S)) false r0 (neg p.P.top r0) 0).Nodup :=
      hgd.nd.sublist (stt_sub R8 (decide (r0 ∈ S)) (decide (neg p.P.top r0 ∈ S)) false r0 (neg p.P.top r0) (Nat.land a b))
    refine rootNo (f := 14) (B := 12) (T := nu ms) hp.gd hmsk hbi ?_ hnd ?_
      (hbase _ hN' (decide (r0 ∈ S)) (decide (neg p.P.top r0 ∈ S)) (by simpa using h1)) (by rw [← e]; exact hd) hB' rfl
    · unfold lsG; rw [List.length_zipWith, hlnN, hmul]; omega
    · intro i hi
      rw [hmul] at hi
      rw [← e]
      unfold lsG
      rw [getD_zip (by omega) (by rw [hlnN]; exact hi)]
      simp only [Bool.false_and]
      refine (hLBn (decide (neg p.P.top r0 ∈ S)) i hi).mono ?_
      intro x hx
      have := hSc x hx
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at this
      have inW : ∀ y ∈ p.W, y ∈ cond (decide (neg p.P.top r0 ∈ S)) (insert (neg p.P.top r0) p.W.toFinset) p.W.toFinset := by
        intro y hy
        cases decide (neg p.P.top r0 ∈ S)
        · exact List.mem_toFinset.mpr hy
        · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hy)
      rcases this with rfl | h | rfl | rfl
      · exact inW _ hr0
      · exact inW _ (hR8 _ h)
      · simp only [hx, decide_true, Bool.cond_true]
        exact Finset.mem_insert_self _ _
      · exact absurd hx hgS



def mpr0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa544544544544544544544544544544544544130404632002c60042025192112054c802084094c80024488b250000890849948000000000000000003ffc003ffc000003ffc4c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673
def mpr1 : Nat := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc82382382382382382382382382382382382384294984101008190c28860900010204cc31892304108100201099292231120a4000000000000003ffc000000000003fffffe10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f
def mpr2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0314314314314314314314314314314314314000020028960f06070471814820400a100400400a2620e11c28620c41c40e1450000000000003ffc000000000003fffffc0000001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c
def mpr3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff000690690690690690690690690690690690691800015002030001800005401c301f000f81603e0101f00c0178140bc02c02b80000003ffc000000000003ffc003ffc000000600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0
def mpr4 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000a92a92a92a92a92a92a92a92a92a92a92a92e031fa000c7c007e007da000e00fa001f0009f4002fc001374002bf00053b4000000000000000000000003fffffc00000000380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000
def mpr5 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff0000000001b01b01b01b01b01b01b01b01b01b01b01b000000000f800055a9000000ca800001a964000003ffdba000003fff768000000003ffc003ffc000003ffc00000000000000000f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000
def mpr6 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff00000000000000000dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc5a8000000fcba50000000000fffefdfa0000000003ef7effdfef4000000000003ffc000000000003ffc000000000000000003ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000
def mpr7 : Nat := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffdffd7000000000000000357bff5e569bfbff5c00000000000000000000000000000003fffffc000000000000000000003ffffffffc000000000000003fffffffffffffffff00000000000000000000000
def mpr8 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000f00f00f00f00f00f00f00f00f00f00f00f00a57ffeaff0345aaa56fffabf00000000000000000000000000000000000000003ffffffffc000000000000000000000000003fffffffffffffffffffffffc0000000000000000000000000000000000000000
def mp : Prob := ⟨⟨0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 0x40404040404040404040404040404040404040404040404040404040404040404040404040404040404040404040404040404040404040404040⟩, [mpr0, mpr1, mpr2, mpr3, mpr4, mpr5, mpr6, mpr7, mpr8], [], [mpr0, mpr1, mpr2, mpr3, mpr4, mpr5, mpr6, mpr7, mpr8]⟩
def mpL : List Lane := [([0, 4], 11), ([1, 6], 11), ([2, 7], 11), ([3, 4], 11), ([5, 7], 11), ([6, 8], 11), ([0, 1, 2], 7), ([0, 1, 4], 8), ([0, 1, 5], 7), ([0, 1, 6], 8), ([0, 2, 4], 7), ([0, 2, 7], 7), ([0, 3, 4], 8), ([0, 4, 5], 8), ([0, 4, 6], 8), ([0, 4, 7], 8), ([0, 4, 8], 7), ([0, 5, 7], 8), ([0, 5, 8], 7), ([0, 6, 7], 7), ([0, 6, 8], 7), ([1, 2, 3], 7), ([1, 2, 6], 8), ([1, 2, 7], 8), ([1, 3, 4], 7), ([1, 3, 6], 7), ([1, 4, 6], 8), ([1, 4, 7], 7), ([1, 5, 6], 7), ([1, 5, 7], 7), ([1, 6, 7], 8), ([1, 6, 8], 8), ([2, 3, 4], 8), ([2, 3, 7], 8), ([2, 3, 8], 7), ([2, 4, 6], 7), ([2, 4, 7], 8), ([2, 5, 7], 8), ([2, 6, 7], 8), ([2, 6, 8], 7), ([2, 7, 8], 7), ([3, 4, 5], 7), ([3, 4, 6], 8), ([3, 4, 7], 8), ([3, 4, 8], 8), ([3, 5, 7], 7), ([3, 5, 8], 7), ([3, 6, 7], 7), ([3, 6, 8], 8), ([4, 5, 6], 7), ([4, 5, 7], 8), ([4, 6, 7], 8), ([4, 6, 8], 8), ([4, 7, 8], 7), ([5, 6, 7], 8), ([5, 6, 8], 8), ([5, 7, 8], 8), ([6, 7, 8], 8)]
def mpM : List Nat := [0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3333333333333333000000000000000033333333333333330000000000000000333333333333333300000000000000003333333333333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffff00000000ffffffff0000000000000000000000000000000000000000ffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffff0000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010101000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000011110000111100001111000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x111111110000000011111111000000001111111100000000111111110000000011111111000000001111111100000000111111110000000011111111000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1111111111111111000000000000000011111111111111110000000000000000111111111111111100000000000000001111111111111111000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x505000005050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505000005050000050500000505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x50505050505050505050505050505050000000000000000000000000000000005050505050505050505050505050505000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x55000000550000005500000055000000550000005500000055000000550000005500000055000000550000005500000055000000550000005500000055000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x55550000000000005555000000000000555500000000000055550000000000005555000000000000555500000000000055550000000000005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x555500005555000000000000000000005555000055550000000000000000000055550000555500000000000000000000555500005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x55550000555500005555000055550000000000000000000000000000000000005555000055550000555500005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x555500005555000055550000555500005555000055550000555500005555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x5555555500000000555555550000000000000000000000000000000000000000555555550000000055555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x55555555000000005555555500000000555555550000000055555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x55555555555555550000000000000000000000000000000000000000000000005555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x555555555555555500000000000000005555555555555555000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x30003000300030003000300030003000300030003000300030003000300030003000300030003000300030003000300030003000300030003000300030003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x303030303030303000000000000000003030303030303030000000000000000030303030303030300000000000000000303030303030303000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x30303030303030303030303030303030000000000000000000000000000000003030303030303030303030303030303000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x33000000330000003300000033000000330000003300000033000000330000003300000033000000330000003300000033000000330000003300000033000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x33003300330033000000000000000000330033003300330000000000000000003300330033003300000000000000000033003300330033000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x333300003333000000000000000000003333000033330000000000000000000033330000333300000000000000000000333300003333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x33330000333300003333000033330000000000000000000000000000000000003333000033330000333300003333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x33333333000000000000000000000000333333330000000000000000000000003333333300000000000000000000000033333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x3333333300000000333333330000000000000000000000000000000000000000333333330000000033333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x33333333333333330000000000000000000000000000000000000000000000003333333333333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x333333333333333300000000000000003333333333333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f0000000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf000f000f000f000f000f000f000f00000000000000000000000000000000000f000f000f000f000f000f000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf0f00000f0f000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f000000000000000000000f0f00000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf0f00000f0f00000f0f00000f0f0000000000000000000000000000000000000f0f00000f0f00000f0f00000f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000000000000f0f0f0f000000000f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf0f0f0f0f0f0f0f0000000000000000000000000000000000000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff00000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff0000000000000000000000ff000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xff000000ff000000ff000000ff00000000000000000000000000000000000000ff000000ff000000ff000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xff00ff0000000000ff00ff000000000000000000000000000000000000000000ff00ff0000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xff00ff00ff00ff00000000000000000000000000000000000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffff0000000000000000000000000000ffff0000000000000000000000000000ffff0000000000000000000000000000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffff000000000000ffff00000000000000000000000000000000000000000000ffff000000000000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffff0000ffff0000000000000000000000000000000000000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffff0000ffff00000000000000000000ffff0000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffff0000ffff0000ffff0000ffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffff00000000000000000000000000000000000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffff000000000000000000000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffff00000000ffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mpok : POK mp :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mpmu : musOf mp mpL = mpM := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mpbi : mp.P.bias = encL (mpM.map fun _ => 64) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mpnd : mp.req.Nodup := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma mpH : ∀ l ∈ mpL, LBc l.1 l.2 ∧ (∀ i ∈ mp.Z, i ∈ l.1) ∧ mskB mp (muOf mp l.1) = true := by
  have h2 : ∀ l ∈ mpL, (∀ i ∈ mp.Z, i ∈ l.1) ∧ mskB mp (muOf mp l.1) = true := by decide +kernel
  intro l hl
  refine ⟨?_, h2 l hl⟩
  simp only [mpL, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pa04
  · exact pa16
  · exact pa27
  · exact pa34
  · exact pa57
  · exact pa68
  · exact tr012
  · exact tr014
  · exact tr015
  · exact tr016
  · exact tr024
  · exact tr027
  · exact tr034
  · exact tr045
  · exact tr046
  · exact tr047
  · exact tr048
  · exact tr057
  · exact tr058
  · exact tr067
  · exact tr068
  · exact tr123
  · exact tr126
  · exact tr127
  · exact tr134
  · exact tr136
  · exact tr146
  · exact tr147
  · exact tr156
  · exact tr157
  · exact tr167
  · exact tr168
  · exact tr234
  · exact tr237
  · exact tr238
  · exact tr246
  · exact tr247
  · exact tr257
  · exact tr267
  · exact tr268
  · exact tr278
  · exact tr345
  · exact tr346
  · exact tr347
  · exact tr348
  · exact tr357
  · exact tr358
  · exact tr367
  · exact tr368
  · exact tr456
  · exact tr457
  · exact tr467
  · exact tr468
  · exact tr478
  · exact tr567
  · exact tr568
  · exact tr578
  · exact tr678
def R8 : List Nat := [mpr1, mpr2, mpr3, mpr4, mpr5, mpr6, mpr7, mpr8]
def mpV : List Nat := mpL.map Prod.snd

def nw : Nat := neg mp.P.top mpr0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma nwE : neg mp.P.top mpr0 = nw := rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma b_011 : rootChk mp.P 14 12 0 mpM (lsG false 0 0 mpM (lsN true mpr0 mpM mpV)) (stt R8 true true false mpr0 nw 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma b_010 : rootChk mp.P 14 12 0 mpM (lsG false 0 0 mpM (lsN false mpr0 mpM mpV)) (stt R8 true false false mpr0 nw 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma b_001 : rootChk mp.P 14 12 0 mpM (lsG false 0 0 mpM (lsN true mpr0 mpM mpV)) (stt R8 false true false mpr0 nw 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma b_111 : rootChk mp.P 14 12 1 mpM (lsG false 0 0 mpM (lsN true mpr0 mpM mpV)) (stt R8 true true false mpr0 nw 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma b_110 : rootChk mp.P 14 12 1 mpM (lsG false 0 0 mpM (lsN false mpr0 mpM mpV)) (stt R8 true false false mpr0 nw 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma b_101 : rootChk mp.P 14 12 1 mpM (lsG false 0 0 mpM (lsN true mpr0 mpM mpV)) (stt R8 false true false mpr0 nw 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma baseAll : ∀ T ≤ 1, ∀ x n : Bool, (x || n) = true →
    rootChk mp.P 14 12 T (musOf mp mpL) (lsG false 0 0 (musOf mp mpL) (lsN n mpr0 (musOf mp mpL) (mpL.map Prod.snd)))
      (stt R8 x n false mpr0 (neg mp.P.top mpr0) 0) = true := by
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact b_001
  · exact b_010
  · exact b_011
  · exact absurd hxn (by decide)
  · exact b_101
  · exact b_110
  · exact b_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g01_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr1 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr1)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g01_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr1 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr1)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g01_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr1 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr1)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g01_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr1 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr1)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g01_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr1 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr1)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g01_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr1 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr1)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good01 : Good mp mpL mpr0 R8 mpr0 mpr1 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g01_001
  · exact g01_010
  · exact g01_011
  · exact absurd hxn (by decide)
  · exact g01_101
  · exact g01_110
  · exact g01_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g02_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr2 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g02_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr2 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g02_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr2 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g02_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr2 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g02_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr2 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g02_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr2 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good02 : Good mp mpL mpr0 R8 mpr0 mpr2 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g02_001
  · exact g02_010
  · exact g02_011
  · exact absurd hxn (by decide)
  · exact g02_101
  · exact g02_110
  · exact g02_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g03_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g03_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr3 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g03_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g03_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g03_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr3 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g03_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good03 : Good mp mpL mpr0 R8 mpr0 mpr3 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g03_001
  · exact g03_010
  · exact g03_011
  · exact absurd hxn (by decide)
  · exact g03_101
  · exact g03_110
  · exact g03_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g04_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g04_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr4 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g04_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g04_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g04_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr4 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g04_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good04 : Good mp mpL mpr0 R8 mpr0 mpr4 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g04_001
  · exact g04_010
  · exact g04_011
  · exact absurd hxn (by decide)
  · exact g04_101
  · exact g04_110
  · exact g04_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g06_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g06_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g06_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr0 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g06_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr0 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g06_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr0 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g06_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr0 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr0 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good06 : Good mp mpL mpr0 R8 mpr0 mpr6 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g06_001
  · exact g06_010
  · exact g06_011
  · exact absurd hxn (by decide)
  · exact g06_101
  · exact g06_110
  · exact g06_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr2 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr2 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr2 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr2 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr2 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g12_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr2 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good12 : Good mp mpL mpr0 R8 mpr1 mpr2 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g12_001
  · exact g12_010
  · exact g12_011
  · exact absurd hxn (by decide)
  · exact g12_101
  · exact g12_110
  · exact g12_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr3 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr3 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g13_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good13 : Good mp mpL mpr0 R8 mpr1 mpr3 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g13_001
  · exact g13_010
  · exact g13_011
  · exact absurd hxn (by decide)
  · exact g13_101
  · exact g13_110
  · exact g13_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g14_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g14_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr4 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g14_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g14_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g14_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr4 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g14_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good14 : Good mp mpL mpr0 R8 mpr1 mpr4 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g14_001
  · exact g14_010
  · exact g14_011
  · exact absurd hxn (by decide)
  · exact g14_101
  · exact g14_110
  · exact g14_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr5 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr5)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr5 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr5)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr5 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr5)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr5 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr5)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr5 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr5)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g15_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr5 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr5)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good15 : Good mp mpL mpr0 R8 mpr1 mpr5 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g15_001
  · exact g15_010
  · exact g15_011
  · exact absurd hxn (by decide)
  · exact g15_101
  · exact g15_110
  · exact g15_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g16_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good16 : Good mp mpL mpr0 R8 mpr1 mpr6 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g16_001
  · exact g16_010
  · exact g16_011
  · exact absurd hxn (by decide)
  · exact g16_101
  · exact g16_110
  · exact g16_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr7 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr7 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g17_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good17 : Good mp mpL mpr0 R8 mpr1 mpr7 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g17_001
  · exact g17_010
  · exact g17_011
  · exact absurd hxn (by decide)
  · exact g17_101
  · exact g17_110
  · exact g17_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g18_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr8 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g18_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr8 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g18_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 mpr8 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g18_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr8 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g18_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr8 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g18_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 mpr8 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good18 : Good mp mpL mpr0 R8 mpr1 mpr8 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g18_001
  · exact g18_010
  · exact g18_011
  · exact absurd hxn (by decide)
  · exact g18_101
  · exact g18_110
  · exact g18_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr1 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr1 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr1 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g19_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr1 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr1 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good19 : Good mp mpL mpr0 R8 mpr1 nw true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inr ⟨rfl, by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g19_001
  · exact g19_010
  · exact g19_011
  · exact absurd hxn (by decide)
  · exact g19_101
  · exact g19_110
  · exact g19_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g23_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g23_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr3 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g23_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g23_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g23_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr3 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g23_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr3 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good23 : Good mp mpL mpr0 R8 mpr2 mpr3 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g23_001
  · exact g23_010
  · exact g23_011
  · exact absurd hxn (by decide)
  · exact g23_101
  · exact g23_110
  · exact g23_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g24_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g24_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr4 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g24_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g24_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g24_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr4 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g24_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good24 : Good mp mpL mpr0 R8 mpr2 mpr4 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g24_001
  · exact g24_010
  · exact g24_011
  · exact absurd hxn (by decide)
  · exact g24_101
  · exact g24_110
  · exact g24_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g26_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g26_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g26_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g26_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g26_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g26_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good26 : Good mp mpL mpr0 R8 mpr2 mpr6 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g26_001
  · exact g26_010
  · exact g26_011
  · exact absurd hxn (by decide)
  · exact g26_101
  · exact g26_110
  · exact g26_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g27_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g27_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr7 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g27_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g27_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g27_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr7 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g27_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good27 : Good mp mpL mpr0 R8 mpr2 mpr7 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g27_001
  · exact g27_010
  · exact g27_011
  · exact absurd hxn (by decide)
  · exact g27_101
  · exact g27_110
  · exact g27_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g28_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr8 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g28_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr8 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g28_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 mpr8 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g28_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr8 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g28_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr8 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g28_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 mpr8 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 mpr8)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good28 : Good mp mpL mpr0 R8 mpr2 mpr8 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g28_001
  · exact g28_010
  · exact g28_011
  · exact absurd hxn (by decide)
  · exact g28_101
  · exact g28_110
  · exact g28_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g29_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g29_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g29_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr2 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g29_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr2 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g29_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr2 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g29_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr2 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr2 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good29 : Good mp mpL mpr0 R8 mpr2 nw true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inr ⟨rfl, by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g29_001
  · exact g29_010
  · exact g29_011
  · exact absurd hxn (by decide)
  · exact g29_101
  · exact g29_110
  · exact g29_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g34_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr3 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr3 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g34_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr3 mpr4 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr3 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g34_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr3 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr3 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g34_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr3 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr3 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g34_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr3 mpr4 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr3 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g34_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr3 mpr4 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr3 mpr4)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good34 : Good mp mpL mpr0 R8 mpr3 mpr4 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g34_001
  · exact g34_010
  · exact g34_011
  · exact absurd hxn (by decide)
  · exact g34_101
  · exact g34_110
  · exact g34_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g36_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr3 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr3 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g36_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr3 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr3 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g36_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr3 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr3 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g36_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr3 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr3 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g36_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr3 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr3 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g36_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr3 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr3 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good36 : Good mp mpL mpr0 R8 mpr3 mpr6 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g36_001
  · exact g36_010
  · exact g36_011
  · exact absurd hxn (by decide)
  · exact g36_101
  · exact g36_110
  · exact g36_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g39_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr3 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr3 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g39_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr3 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr3 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g39_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr3 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr3 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g39_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr3 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr3 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g39_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr3 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr3 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g39_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr3 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr3 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good39 : Good mp mpL mpr0 R8 mpr3 nw true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inr ⟨rfl, by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g39_001
  · exact g39_010
  · exact g39_011
  · exact absurd hxn (by decide)
  · exact g39_101
  · exact g39_110
  · exact g39_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g46_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr4 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr4 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g46_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr4 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr4 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g46_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr4 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr4 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g46_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr4 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr4 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g46_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr4 mpr6 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr4 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g46_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr4 mpr6 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr4 mpr6)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good46 : Good mp mpL mpr0 R8 mpr4 mpr6 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g46_001
  · exact g46_010
  · exact g46_011
  · exact absurd hxn (by decide)
  · exact g46_101
  · exact g46_110
  · exact g46_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g49_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr4 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr4 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g49_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr4 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr4 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g49_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr4 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr4 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g49_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr4 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr4 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g49_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr4 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr4 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g49_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr4 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr4 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good49 : Good mp mpL mpr0 R8 mpr4 nw true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inr ⟨rfl, by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g49_001
  · exact g49_010
  · exact g49_011
  · exact absurd hxn (by decide)
  · exact g49_101
  · exact g49_110
  · exact g49_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g67_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr6 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr6 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g67_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr6 mpr7 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr6 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g67_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr6 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr6 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g67_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr6 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr6 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g67_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr6 mpr7 mpM (lsN (false || false) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr6 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g67_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr6 mpr7 mpM (lsN (true || false) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr6 mpr7)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good67 : Good mp mpL mpr0 R8 mpr6 mpr7 false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inl ⟨by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g67_001
  · exact g67_010
  · exact g67_011
  · exact absurd hxn (by decide)
  · exact g67_101
  · exact g67_110
  · exact g67_111
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g69_011 : rootChk mp.P 14 12 0 mpM (lsG true mpr6 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr6 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g69_010 : rootChk mp.P 14 12 0 mpM (lsG true mpr6 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr6 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g69_001 : rootChk mp.P 14 12 0 mpM (lsG true mpr6 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr6 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g69_111 : rootChk mp.P 14 12 1 mpM (lsG true mpr6 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 true true true mpr0 nw (Nat.land mpr6 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g69_110 : rootChk mp.P 14 12 1 mpM (lsG true mpr6 nw mpM (lsN (false || true) mpr0 mpM mpV)) (stt R8 true false true mpr0 nw (Nat.land mpr6 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma g69_101 : rootChk mp.P 14 12 1 mpM (lsG true mpr6 nw mpM (lsN (true || true) mpr0 mpM mpV)) (stt R8 false true true mpr0 nw (Nat.land mpr6 nw)) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma good69 : Good mp mpL mpr0 R8 mpr6 nw true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, Or.inr ⟨rfl, by decide +kernel, by decide +kernel⟩, ?_⟩
  intro T hT x n hxn
  rw [mpmu]
  interval_cases T <;> cases x <;> cases n
  · exact absurd hxn (by decide)
  · exact g69_001
  · exact g69_010
  · exact g69_011
  · exact absurd hxn (by decide)
  · exact g69_101
  · exact g69_110
  · exact g69_111
def wI : List Nat := mp.W
def wS : List Nat := [mpr0, mpr5, mpr8, mpr3, mpr4, mpr1, mpr7, mpr6, mpr2]
def Fit (w : List Nat) (i j : Nat) : Prop :=
  ∃ a b gn, Good mp mpL mpr0 R8 a b gn ∧ Nat.land ((w ++ [nw]).getD i 0) ((w ++ [nw]).getD j 0) = Nat.land a b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fits (i j : Fin 10) (h : i ≠ j) (h1 : ¬ (i.val = 0 ∧ j.val = 9)) (h2 : ¬ (i.val = 9 ∧ j.val = 0)) :
    Fit wI i.val j.val ∨ Fit wS i.val j.val := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl h
  · exact Or.inl ⟨_, _, _, good01, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good02, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good03, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good04, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good01, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good06, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good06, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good02, by decide +kernel⟩
  · exact absurd ⟨rfl, rfl⟩ h1
  · exact Or.inl ⟨_, _, _, good01, by decide +kernel⟩
  · exact absurd rfl h
  · exact Or.inl ⟨_, _, _, good12, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good13, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good14, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good15, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good16, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good17, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good18, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good19, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good02, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good12, by decide +kernel⟩
  · exact absurd rfl h
  · exact Or.inl ⟨_, _, _, good23, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good24, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good18, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good26, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good27, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good28, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good29, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good03, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good13, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good23, by decide +kernel⟩
  · exact absurd rfl h
  · exact Or.inl ⟨_, _, _, good34, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good13, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good36, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good36, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good23, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good39, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good04, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good14, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good24, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good34, by decide +kernel⟩
  · exact absurd rfl h
  · exact Or.inr ⟨_, _, _, good14, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good46, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good46, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good24, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good49, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good01, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good15, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good18, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good13, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good14, by decide +kernel⟩
  · exact absurd rfl h
  · exact Or.inr ⟨_, _, _, good17, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good16, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good12, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good19, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good06, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good16, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good26, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good36, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good46, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good17, by decide +kernel⟩
  · exact absurd rfl h
  · exact Or.inl ⟨_, _, _, good67, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good27, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good69, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good06, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good17, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good27, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good36, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good46, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good16, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good67, by decide +kernel⟩
  · exact absurd rfl h
  · exact Or.inr ⟨_, _, _, good26, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good69, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good02, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good18, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good28, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good23, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good24, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good12, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good27, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good26, by decide +kernel⟩
  · exact absurd rfl h
  · exact Or.inr ⟨_, _, _, good29, by decide +kernel⟩
  · exact absurd ⟨rfl, rfl⟩ h2
  · exact Or.inl ⟨_, _, _, good19, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good29, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good39, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good49, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good19, by decide +kernel⟩
  · exact Or.inl ⟨_, _, _, good69, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good69, by decide +kernel⟩
  · exact Or.inr ⟨_, _, _, good29, by decide +kernel⟩
  · exact absurd rfl h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wIb : wbf wI = mp.P.tgt := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wSb : wbf wS = mp.P.tgt := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wIm : ∀ x ∈ wI, x ∈ mp.W := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wSm : ∀ x ∈ wS, x ∈ mp.W := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wWR : ∀ x ∈ mp.W, x ∈ mpr0 :: R8 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wRW : ∀ x ∈ R8, x ∈ mp.W := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma r0W : mpr0 ∈ mp.W := by decide +kernel
lemma map_getD (w : List Nat) (j i : Nat) : (w.map (fun a => a.testBit j)).getD i false = (w.getD i 0).testBit j := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp

lemma step (w : List Nat) (hl : w.length = 9) (hb : wbf w = mp.P.tgt) (hm : ∀ x ∈ w, x ∈ mp.W) (h0 : w.getD 0 0 = mpr0)
    (i j : Nat) (hf : Fit w i j) (C : Circuit) (hfan : FanInTwo C) (hsz : C.gates.length = 13) (hnot : C.gates.countP isNot = 1)
    (hc : ∀ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++
      [(List.ofFn x ++ [!x 0]).getD i false && (List.ofFn x ++ [!x 0]).getD j false]) = bf x) : False := by
  obtain ⟨a, b, gn, hg, hab⟩ := hf
  have hnv : Val mp.P.top nw := val_neg (mpok.val _ r0W)
  have hv : ∀ x ∈ w ++ [nw], Val mp.P.top x := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact mpok.val _ (hm x h)
    · rw [List.mem_singleton] at h; exact h ▸ hnv
  refine mainNo mpok mpH (by rw [mpmu]; exact mpbi) r0W wWR wRW baseAll hg
    (w ++ [nw] ++ [Nat.land a b]) ?_ ?_ C.gates C.output (fun g hg => hfan g hg) hsz hnot ?_
  · intro x hx
    rw [List.mem_append, List.mem_append, List.mem_singleton, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | rfl
    · exact List.mem_append_left _ (wWR x (hm x hx))
    · exact List.mem_append_right _ (by rw [nwE]; exact List.mem_cons_self)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hv x h
    · rw [List.mem_singleton] at h; subst h
      rw [← hab]; exact val_land (val_getD hv i)
  · intro k hk
    have e1 : w.map (fun a => a.testBit k) = List.ofFn (fun q : Fin 9 => (w.getD q.val 0).testBit k) := list9 w hl k
    have e2 : nw.testBit k = !((w.getD (0 : Fin 9).val 0).testBit k) := by
      change (neg mp.P.top mpr0).testBit k = !((w.getD 0 0).testBit k)
      rw [h0, neg, tb_xor, hk, Bool.xor_true]
    have e3 : (w ++ [nw]).map (fun a => a.testBit k) =
        List.ofFn (fun q : Fin 9 => (w.getD q.val 0).testBit k) ++ [!((w.getD (0 : Fin 9).val 0).testBit k)] := by
      rw [List.map_append, e1, List.map_singleton, e2]
    have e4 : (Nat.land a b).testBit k =
        ((List.ofFn (fun q : Fin 9 => (w.getD q.val 0).testBit k) ++ [!((w.getD (0 : Fin 9).val 0).testBit k)]).getD i false &&
         (List.ofFn (fun q : Fin 9 => (w.getD q.val 0).testBit k) ++ [!((w.getD (0 : Fin 9).val 0).testBit k)]).getD j false) := by
      rw [← e3, map_getD, map_getD, ← hab, tb_land]
    rw [List.map_append, e3, List.map_singleton, e4, ← hb, wbf_bit]
    exact hc (fun q : Fin 9 => (w.getD q.val 0).testBit k)

lemma notCount (C : Circuit) (hfan : FanInTwo C) :
    C.gates.countP (fun g => !g.op.eval [true]) = C.gates.countP isNot := by
  apply List.countP_congr
  intro g hg
  have h := (hfan g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  unfold isNot
  rcases h with h | h | h <;> rw [h] <;> decide
lemma main : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size = (13 : ℕ) →           List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => !x6.op.eval [Bool.true]) x3.gates = (1 : ℕ) →             (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x7 ≠ x8 ∧ x1 = [↑x7, ↑x8] ∧ ¬(↑x7 = (0 : ℕ) ∧ ↑x8 = (9 : ℕ)) ∧ ¬(↑x7 = (9 : ℕ) ∧ ↑x8 = (0 : ℕ))) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x3.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro x1 _ C hfan hsz hcnt hp
  obtain ⟨i, j, hij, rfl, h1, h2⟩ := hp
  by_contra hne
  push Not at hne
  have hn : C.gates.countP isNot = 1 := by rw [← notCount C hfan]; exact hcnt
  have hc : ∀ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++
      [(List.ofFn x ++ [!x 0]).getD i.val false && (List.ofFn x ++ [!x 0]).getD j.val false]) = bf x := by
    intro x
    have h := hne x
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id, Bool.and_true] at h
    exact Classical.not_not.mp h
  rcases fits i j hij h1 h2 with h | h
  · exact step wI rfl wIb wIm rfl i.val j.val h C hfan hsz hn hc
  · exact step wS rfl wSb wSm rfl i.val j.val h C hfan hsz hn hc

end PEqualNP.Outside.L_meta_3624

theorem PEqualNP.Outside.L_meta_3624 : ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size = (13 : ℕ) →           List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => !x6.op.eval [Bool.true]) x3.gates = (1 : ℕ) →             (∃ (x7 : Fin (10 : ℕ)) (x8 : Fin (10 : ℕ)), x7 ≠ x8 ∧ x1 = [↑x7, ↑x8] ∧ ¬(↑x7 = (0 : ℕ) ∧ ↑x8 = (9 : ℕ)) ∧ ¬(↑x7 = (9 : ℕ) ∧ ↑x8 = (0 : ℕ))) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x3.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  exact PEqualNP.Outside.L_meta_3624.main
