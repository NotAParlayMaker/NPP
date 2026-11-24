import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3420

-- Words are naturals below 2^24.  Bits 0..11 are edge rows, bits 12..23 independent rows.

/-- dominance test: `d` has every edge bit of `w` and no independent bit outside `w`. -/
def domN (w d : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.land w 4095) (Nat.sub 16777215 d)) 0 &&
  Nat.beq (Nat.land (Nat.land d (Nat.sub 16777215 w)) 16773120) 0

/-- the blocking relation: dominance (`m = true`) or plain equality (`m = false`). -/
def blk (m : Bool) (w d : ℕ) : Bool := cond m (domN w d) (Nat.beq w d)

def base10 : List ℕ :=
  [113184, 430348, 902208, 3227782, 5521457, 5689661, 8532035, 11083800, 13501056, 15731968]

def base12 : List ℕ := 0 :: 16777215 :: base10

theorem land_compl (w : ℕ) : w &&& (16777215 - w) = 0 := by
  rcases lt_or_ge w (2 ^ 24) with h | h
  · apply Nat.eq_of_testBit_eq
    intro i
    have e : 16777215 - w = 2 ^ 24 - (w + 1) := by omega
    rw [e, Nat.testBit_and, Nat.testBit_two_pow_sub_succ h]
    cases w.testBit i <;> simp
  · have e : 16777215 - w = 0 := by omega
    simp [e]

theorem domN_refl (w : ℕ) : domN w w = true := by
  have h := land_compl w
  have h1 : Nat.land (Nat.land w 4095) (Nat.sub 16777215 w) = 0 := by
    show (w &&& 4095) &&& (16777215 - w) = 0
    rw [Nat.and_right_comm, h]; simp
  have h2 : Nat.land (Nat.land w (Nat.sub 16777215 w)) 16773120 = 0 := by
    show (w &&& (16777215 - w)) &&& 16773120 = 0
    rw [h]; simp
  unfold domN
  rw [h1, h2]
  rfl

theorem blk_refl (m : Bool) (w : ℕ) : blk m w w = true := by
  cases m
  · simp [blk]
  · simp [blk, domN_refl]

/-- abstract reachability of the final live set `{4095}` from live set `D` within `k` steps. -/
inductive Reach (m : Bool) : Finset ℕ → ℕ → Prop
  | done (k : ℕ) : Reach m {4095} k
  | step (D : Finset ℕ) (k u v w : ℕ) (ka kb : Bool) :
      u ∈ D → v ∈ D → (w = u &&& v ∨ w = u ||| v) →
      (∀ d ∈ D, blk m w d = false) → (∀ d ∈ base12, blk m w d = false) →
      Reach m (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k →
      Reach m D (k + 1)

theorem Reach.mono {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) : Reach m D (k + 1) := by
  induction h with
  | done k => exact Reach.done _
  | step D k u v w ka kb hu hv hw hd hb _ ih => exact Reach.step D (k + 1) u v w ka kb hu hv hw hd hb ih

theorem Reach.mono_le {m : Bool} {D : Finset ℕ} {k k' : ℕ} (hk : k ≤ k') (h : Reach m D k) :
    Reach m D k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.mono

theorem Reach.zero {m : Bool} {D : Finset ℕ} (h : Reach m D 0) : D = {4095} := by
  cases h
  rfl

theorem Reach.inv' {m : Bool} {D : Finset ℕ} {k' : ℕ} (h : Reach m D k') : ∀ k : ℕ, k' = k + 1 →
    D = {4095} ∨ ∃ (u v w : ℕ) (ka kb : Bool), u ∈ D ∧ v ∈ D ∧ (w = u &&& v ∨ w = u ||| v) ∧
      (∀ d ∈ D, blk m w d = false) ∧ (∀ d ∈ base12, blk m w d = false) ∧
      Reach m (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k := by
  induction h with
  | done k0 => intro _ _; exact Or.inl rfl
  | step D k0 u v w ka kb hu hv hw hd hb hr _ =>
    intro k hk
    obtain rfl : k0 = k := by omega
    exact Or.inr ⟨u, v, w, ka, kb, hu, hv, hw, hd, hb, hr⟩

theorem Reach.inv {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D (k + 1)) :
    D = {4095} ∨ ∃ (u v w : ℕ) (ka kb : Bool), u ∈ D ∧ v ∈ D ∧ (w = u &&& v ∨ w = u ||| v) ∧
      (∀ d ∈ D, blk m w d = false) ∧ (∀ d ∈ base12, blk m w d = false) ∧
      Reach m (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k :=
  h.inv' k rfl

theorem Reach.card {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) : D.card ≤ k + 1 := by
  induction h with
  | done k => simp
  | step D k u v w ka kb hu hv hw hd hb _ ih =>
    have hwD : w ∉ D := fun hm => by
      have := hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwF : w ∉ D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwD (Finset.mem_of_mem_filter _ hm)
    rw [Finset.card_insert_of_notMem hwF] at ih
    have hsub : D ⊆ insert u (insert v
        (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) := by
      intro x hx
      by_cases h1 : x = u
      · simp [h1]
      by_cases h2 : x = v
      · simp [h2]
      simp [hx, h1, h2]
    have h2 := Finset.card_le_card hsub
    have h3 := Finset.card_insert_le u (insert v
        (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))))
    have h4 := Finset.card_insert_le v
        (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))
    omega

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

theorem Reach.sep {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) (e i : ℕ) (he : e < 12)
    (hi : 12 ≤ i) : ∃ w ∈ D, w.testBit e = true ∧ w.testBit i = false := by
  induction h with
  | done k =>
    refine ⟨4095, by simp, ?_, ?_⟩
    · rw [tb4095]; simpa using he
    · rw [tb4095]; simpa using hi
  | step D k u v w ka kb hu hv hw hd hb _ ih =>
    obtain ⟨x, hx, h1, h2⟩ := ih
    rcases Finset.mem_insert.mp hx with hxw | hx
    · subst hxw
      rcases hw with hw | hw
      · subst hw
        rw [Nat.testBit_and] at h1 h2
        cases hum : u.testBit i
        · exact ⟨u, hu, by simp_all, hum⟩
        · exact ⟨v, hv, by simp_all, by simp_all⟩
      · subst hw
        rw [Nat.testBit_or] at h1 h2
        cases hue : u.testBit e
        · exact ⟨v, hv, by simp_all, by simp_all⟩
        · exact ⟨u, hu, hue, by simp_all⟩
    · exact ⟨x, Finset.mem_of_mem_filter _ hx, h1, h2⟩

-- the computable checker

def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb_eq (w e : ℕ) : tb w e = w.testBit e := by
  have h : Nat.land (Nat.shiftRight w e) 1 = 1 &&& (w >>> e) := Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1 &&& w >>> e) = X
  cases X <;> rfl

/-- the rectangle of `x`: bit `12 * e + i` is set when `x` has edge bit `e` and lacks
independent bit `12 + i`. -/
def rect (x J : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)

def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ, e < n → x.testBit e = true →
    (rect x J n).testBit (12 * e + i) = true := by
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J <<< (12 * n)) 0) ||| rect x J n).testBit (12 * e + i) = true
    rw [Nat.testBit_or]
    by_cases hen : e = n
    · subst hen
      rw [tb_eq, hx]
      simp [Nat.testBit_shiftLeft, hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, h2, tb4095]
  simp [hi]

theorem sep_bit {m : Bool} {D : Finset ℕ} {k : ℕ} (hR : Reach m D k) (p : ℕ) (hp : p < 144) :
    ∃ x ∈ D, (rectW x).testBit p = true := by
  obtain ⟨x, hx, h1, h2⟩ := hR.sep (p / 12) (12 + p % 12) (by omega) (by omega)
  refine ⟨x, hx, ?_⟩
  have := rectW_tb x (p / 12) (p % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h1 h2
  rwa [Nat.div_add_mod] at this

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

/-- cover test on the union `c` of rectangles. -/
def covR (c : ℕ) : Bool := Nat.beq (Nat.land c full) full

theorem covR_of (c : ℕ) (h : ∀ p, p < 144 → c.testBit p = true) : covR c = true := by
  have e : Nat.land c full = full := by
    show c &&& full = full
    rw [full_eq]
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hp : p < 144
    · simp [hp, h p hp]
    · simp [hp]
  unfold covR
  rw [e]
  exact Nat.beq_refl _

def orR : List ℕ → ℕ
  | [] => 0
  | x :: l => Nat.lor (rectW x) (orR l)

theorem orR_tb (p : ℕ) : ∀ l : List ℕ, ∀ x ∈ l, (rectW x).testBit p = true →
    (orR l).testBit p = true := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx h
    show (rectW a ||| orR l).testBit p = true
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp hx with hxa | hx
    · rw [← hxa, h]; rfl
    · rw [ih x hx h]; simp

theorem cover_sound {m : Bool} {l : List ℕ} {k : ℕ} (h : covR (orR l) = false) :
    ¬ Reach m l.toFinset k := by
  intro hR
  have : covR (orR l) = true := by
    apply covR_of
    intro p hp
    obtain ⟨x, hx, hb⟩ := sep_bit hR p hp
    exact orR_tb p l x (List.mem_toFinset.mp hx) hb
  rw [h] at this
  exact Bool.noConfusion this

def allFinal : List ℕ → Bool
  | [] => true
  | a :: l => Nat.beq a 4095 && allFinal l

theorem allFinal_of : ∀ l : List ℕ, (∀ a ∈ l, a = 4095) → allFinal l = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    have ha := h a (List.mem_cons_self)
    simp only [allFinal, ha, Bool.and_eq_true]
    exact ⟨rfl, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))⟩

theorem notFinal {l : List ℕ} (h : allFinal l = false) : l.toFinset ≠ {4095} := by
  intro he
  have : allFinal l = true := by
    apply allFinal_of
    intro a ha
    have : a ∈ l.toFinset := List.mem_toFinset.mpr ha
    rw [he] at this
    exact Finset.mem_singleton.mp this
  rw [h] at this
  exact Bool.noConfusion this

/-- sorted insertion (only `Perm` to `w :: l` matters for soundness). -/
def ins (w : ℕ) : List ℕ → List ℕ
  | [] => [w]
  | a :: l => cond (Nat.blt w a) (w :: a :: l) (a :: ins w l)

theorem ins_perm (w : ℕ) : ∀ l : List ℕ, (ins w l).Perm (w :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    unfold ins
    cases Nat.blt w a
    · exact (List.Perm.cons a ih).trans (List.Perm.swap w a l)
    · exact List.Perm.refl _

def sortedFrom (a : ℕ) : List ℕ → Bool
  | [] => true
  | b :: l => Nat.blt a b && sortedFrom b l

def sortedB : List ℕ → Bool
  | [] => true
  | a :: l => sortedFrom a l

theorem sortedFrom_lt : ∀ (l : List ℕ) (a : ℕ), sortedFrom a l = true → ∀ x ∈ l, a < x := by
  intro l
  induction l with
  | nil => intro a _ x hx; simp at hx
  | cons b l ih =>
    intro a h x hx
    simp only [sortedFrom, Bool.and_eq_true] at h
    have hab : a < b := by simpa [Nat.blt_eq] using h.1
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hab
    · exact lt_trans hab (ih b h.2 x hx)

theorem sortedFrom_nodup : ∀ (l : List ℕ) (a : ℕ), sortedFrom a l = true → (a :: l).Nodup := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons b l ih =>
    intro a h
    have hlt := sortedFrom_lt (b :: l) a h
    simp only [sortedFrom, Bool.and_eq_true] at h
    refine List.nodup_cons.mpr ⟨fun hm => lt_irrefl a (hlt a hm), ih b h.2⟩

theorem sortedB_nodup {l : List ℕ} (h : sortedB l = true) : l.Nodup := by
  cases l with
  | nil => simp
  | cons a l => exact sortedFrom_nodup l a h

/-- certificate tables: binary search trees of states (soundness does not need the order). -/
abbrev Tree : Type := BinaryTree (List ℕ)

def lcmp : List ℕ → List ℕ → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | a :: x, b :: y => cond (Nat.blt a b) Ordering.lt (cond (Nat.blt b a) Ordering.gt (lcmp x y))

theorem lcmp_eq : ∀ (x y : List ℕ), lcmp x y = Ordering.eq → x = y := by
  intro x
  induction x with
  | nil => intro y h; cases y with
    | nil => rfl
    | cons b y => simp [lcmp] at h
  | cons a x ih =>
    intro y h
    cases y with
    | nil => simp [lcmp] at h
    | cons b y =>
      unfold lcmp at h
      cases h1 : Nat.blt a b
      · cases h2 : Nat.blt b a
        · rw [h1, h2] at h
          have e1 : ¬ a < b := by rw [← Nat.blt_eq, h1]; simp
          have e2 : ¬ b < a := by rw [← Nat.blt_eq, h2]; simp
          have : a = b := by omega
          rw [this, ih y h]
        · rw [h1, h2] at h; simp at h
      · rw [h1] at h; simp at h

def thas : Tree → List ℕ → Bool
  | BinaryTree.nil, _ => false
  | BinaryTree.node key l r, x =>
    match lcmp x key with
    | Ordering.lt => thas l x
    | Ordering.eq => true
    | Ordering.gt => thas r x

def tall (p : List ℕ → Bool) : Tree → Bool
  | BinaryTree.nil => true
  | BinaryTree.node key l r => p key && tall p l && tall p r

theorem thas_all (p : List ℕ → Bool) : ∀ (t : Tree) (x : List ℕ), tall p t = true →
    thas t x = true → p x = true := by
  intro t
  induction t with
  | nil => intro x _ h; simp [thas] at h
  | node key l r ihl ihr =>
    intro x ha hh
    simp only [tall, Bool.and_eq_true] at ha
    unfold thas at hh
    cases hc : lcmp x key
    · rw [hc] at hh; exact ihl x ha.1.2 hh
    · rw [lcmp_eq x key hc]; exact ha.1.1
    · rw [hc] at hh; exact ihr x ha.2 hh

/-- `closed`: the state `l` with `k` steps left certainly cannot reach the target. -/
def closed (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  Nat.blt (Nat.succ k) l.length || !(covR (orR l)) || (Nat.beq k 0 && !(allFinal l)) || thas prev l

def Inv (m : Bool) (prev : Tree) (k : ℕ) : Prop :=
  ∀ x : List ℕ, thas prev x = true → ¬ Reach m x.toFinset k

theorem closed_sound {m : Bool} {prev : Tree} {k : ℕ} {l : List ℕ} (hnd : l.Nodup)
    (hinv : Inv m prev k) (h : closed prev k l = true) : ¬ Reach m l.toFinset k := by
  intro hR
  simp only [closed, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ((h | h) | h) | h
  · have h1 : k + 1 < l.length := by simpa [Nat.blt_eq] using h
    have h2 := hR.card
    rw [List.toFinset_card_of_nodup hnd] at h2
    omega
  · exact cover_sound h hR
  · have hk : k = 0 := Nat.eq_of_beq_eq_true h.1
    subst hk
    exact notFinal h.2 hR.zero
  · exact hinv l h hR

theorem beq_false_iff (x u : ℕ) : Nat.beq x u = false ↔ x ≠ u := by
  constructor
  · intro h he
    rw [he, Nat.beq_refl] at h
    exact Bool.noConfusion h
  · intro h
    cases hb : Nat.beq x u
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h

def remF (ka kb : Bool) (u v x : ℕ) : Bool := (ka || !(Nat.beq x u)) && (kb || !(Nat.beq x v))

/-- soundness of a pruning rule: a state that can reach the target passes the test. -/
def PruneOK (m : Bool) (P : List ℕ → ℕ → Bool) : Prop :=
  ∀ (l : List ℕ) (k : ℕ), l.Nodup → Reach m l.toFinset k → P l k = true

theorem PruneOK.triv (m : Bool) : PruneOK m (fun _ _ => true) := fun _ _ _ _ => rfl

theorem PruneOK.and {m : Bool} {P Q : List ℕ → ℕ → Bool} (hP : PruneOK m P) (hQ : PruneOK m Q) :
    PruneOK m (fun l k => P l k && Q l k) := by
  intro l k hnd hR
  simp only [hP l k hnd hR, hQ l k hnd hR, Bool.and_self]

def lastOK (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  (Nat.beq k 0 && !(allFinal l)) || thas prev l || !(P l k)

theorem lastOK_sound {m : Bool} {P : List ℕ → ℕ → Bool} {prev : Tree} {k : ℕ} {l : List ℕ}
    (hP : PruneOK m P) (hnd : l.Nodup)
    (hinv : Inv m prev k) (h : lastOK P prev k l = true) : ¬ Reach m l.toFinset k := by
  intro hR
  simp only [lastOK, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with (h | h) | h
  · have hk : k = 0 := Nat.eq_of_beq_eq_true h.1
    subst hk
    exact notFinal h.2 hR.zero
  · exact hinv l h hR
  · rw [hP l k hnd hR] at h; exact Bool.noConfusion h

/-- one successor: size test `sz`, cover test on the rectangle union `c`, then table lookup. -/
def sOK (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ) (ka kb : Bool) : Bool :=
  sz || !(covR c) || lastOK P prev k (ins w (l.filter (remF ka kb u v)))

def blkAny (m : Bool) (w : ℕ) : List ℕ → Bool
  | [] => false
  | d :: l => blk m w d || blkAny m w l

theorem blkAny_false (m : Bool) (w : ℕ) : ∀ l : List ℕ, (∀ d ∈ l, blk m w d = false) →
    blkAny m w l = false := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [blkAny, h a List.mem_cons_self, Bool.false_or]
    exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd))

def opOK2 (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) : Bool :=
  sOK P prev k l u v w (Nat.blt (Nat.add k 2) l.length) c false false &&
  sOK P prev k l u v w (Nat.blt (Nat.succ k) l.length) (Nat.lor c rv) false true &&
  sOK P prev k l u v w (Nat.blt (Nat.succ k) l.length) (Nat.lor c ru) true false &&
  sOK P prev k l u v w (Nat.blt k l.length) (Nat.lor c (Nat.lor ru rv)) true true

def opOK (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) : Bool :=
  blkAny m w base12 || blkAny m w l || opOK2 P prev k l u ru v rv w (Nat.lor (rectW w) ro)

/-- union of the rectangles of the words other than `u`, `v`. -/
def orEx (u v : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: l => cond (Nat.beq x u || Nat.beq x v) (orEx u v l) (Nat.lor (rectW x) (orEx u v l))

theorem orEx_tb (u v p : ℕ) : ∀ l : List ℕ, ∀ x : ℕ, x ∈ l → x ≠ u → x ≠ v →
    (rectW x).testBit p = true → (orEx u v l).testBit p = true := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons y l ih =>
    intro x hx hxu hxv h
    unfold orEx
    rcases List.mem_cons.mp hx with hxa | hx
    · subst hxa
      rw [(beq_false_iff x u).mpr hxu, (beq_false_iff x v).mpr hxv]
      show (rectW x ||| orEx u v l).testBit p = true
      rw [Nat.testBit_or, h]; rfl
    · have := ih x hx hxu hxv h
      cases (Nat.beq y u || Nat.beq y v)
      · show (rectW y ||| orEx u v l).testBit p = true
        rw [Nat.testBit_or, this]; simp
      · exact this

def pairOK (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v : ℕ) : Bool :=
  opOK m P prev k l u (rectW u) v (rectW v) (orEx u v l) (Nat.land u v) &&
  opOK m P prev k l u (rectW u) v (rectW v) (orEx u v l) (Nat.lor u v)

def allB {α : Type} (f : α → Bool) : List α → Bool
  | [] => true
  | a :: l => f a && allB f l

theorem allB_mem {α : Type} (f : α → Bool) : ∀ l : List α, allB f l = true →
    ∀ x ∈ l, f x = true := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a l ih =>
    intro h x hx
    simp only [allB, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

def pairsAll {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => allB (f a) l && pairsAll f l

theorem pairsAll_mem {α : Type} (f : α → α → Bool) : ∀ l : List α, pairsAll f l = true →
    ∀ u ∈ l, ∀ v ∈ l, u ≠ v → f u v = true ∨ f v u = true := by
  intro l
  induction l with
  | nil => intro _ u hu; simp at hu
  | cons a l ih =>
    intro h u hu v hv huv
    simp only [pairsAll, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hu with hua | hu
    · rcases List.mem_cons.mp hv with hva | hv
      · exact absurd (hua.trans hva.symm) huv
      · rw [hua]; exact Or.inl (allB_mem _ l h.1 v hv)
    · rcases List.mem_cons.mp hv with hva | hv
      · rw [hva]; exact Or.inr (allB_mem _ l h.1 u hu)
      · exact ih h.2 u hu v hv huv

theorem size_lb (D : Finset ℕ) (u v : ℕ) (ka kb : Bool) :
    D.card ≤ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))).card +
      (cond ka 0 1 + cond kb 0 1) := by
  have hsub : D ⊆ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ∪
      ((cond ka ∅ {u}) ∪ (cond kb ∅ {v})) := by
    intro x hx
    by_cases h1 : x = u <;> by_cases h2 : x = v <;> cases ka <;> cases kb <;> simp_all
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))
    ((cond ka ∅ {u}) ∪ (cond kb ∅ {v}))
  have h3 := Finset.card_union_le (cond ka (∅ : Finset ℕ) {u}) (cond kb ∅ {v})
  have h4 : (cond ka (∅ : Finset ℕ) {u}).card = cond ka 0 1 := by cases ka <;> simp
  have h5 : (cond kb (∅ : Finset ℕ) {v}).card = cond kb 0 1 := by cases kb <;> simp
  omega

theorem pair_sound {m : Bool} {P : List ℕ → ℕ → Bool} {prev : Tree} {k : ℕ} {l : List ℕ} {u v : ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k) (hnd : l.Nodup) (hp : pairOK m P prev k l u v = true)
    (hu : u ∈ l) (hv : v ∈ l)
    (ka kb : Bool) (w : ℕ) (hw : w = u &&& v ∨ w = u ||| v)
    (hd : ∀ d ∈ l, blk m w d = false) (hb : ∀ d ∈ base12, blk m w d = false) :
    ¬ Reach m (insert w (l.toFinset.filter
      (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k := by
  intro hR
  simp only [pairOK, Bool.and_eq_true] at hp
  have hop : opOK m P prev k l u (rectW u) v (rectW v) (orEx u v l) w = true := by
    rcases hw with rfl | rfl
    · exact hp.1
    · exact hp.2
  simp only [opOK, blkAny_false m w base12 hb, blkAny_false m w l hd, Bool.false_or, opOK2,
    Bool.and_eq_true] at hop
  have hwl : w ∉ l := fun hm => by
    have := hd w hm
    rw [blk_refl] at this
    exact Bool.noConfusion this
  -- size
  have hsz : l.length ≤ k + (cond ka 0 1 + cond kb 0 1) := by
    have h1 := hR.card
    have hwF : w ∉ l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwl (List.mem_toFinset.mp (Finset.mem_of_mem_filter _ hm))
    rw [Finset.card_insert_of_notMem hwF] at h1
    have h2 := size_lb l.toFinset u v ka kb
    rw [List.toFinset_card_of_nodup hnd] at h2
    omega
  -- cover
  have hbit : ∀ p, p < 144 → ((rectW w).testBit p = true ∨ (orEx u v l).testBit p = true) ∨
      (ka = true ∧ (rectW u).testBit p = true) ∨ (kb = true ∧ (rectW v).testBit p = true) := by
    intro p hp
    obtain ⟨x, hx, hxb⟩ := sep_bit hR p hp
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl (Or.inl hxb)
    · obtain ⟨hxl, h1, h2⟩ := Finset.mem_filter.mp hx
      by_cases hxu : x = u
      · exact Or.inr (Or.inl ⟨h1.resolve_right (fun h => h hxu), hxu ▸ hxb⟩)
      · by_cases hxv : x = v
        · exact Or.inr (Or.inr ⟨h2.resolve_right (fun h => h hxv), hxv ▸ hxb⟩)
        · exact Or.inl (Or.inr (orEx_tb u v p _ x (List.mem_toFinset.mp hxl) hxu hxv hxb))
  have hfs : (ins w (l.filter (remF ka kb u v))).toFinset =
      insert w (l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) := by
    ext x
    rw [List.mem_toFinset, (ins_perm w _).mem_iff]
    simp [remF, List.mem_filter, beq_false_iff]
  have key : ∀ (sz : Bool) (c : ℕ), sOK P prev k l u v w sz c ka kb = true →
      (sz = true → False) → (∀ p, p < 144 → c.testBit p = true) → False := by
    intro sz c h h1 h2
    simp only [sOK, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | h) | h
    · exact h1 h
    · rw [covR_of c h2] at h; exact Bool.noConfusion h
    · rw [← hfs] at hR
      refine lastOK_sound hP ?_ hinv h hR
      rw [(ins_perm w _).nodup_iff]
      exact List.nodup_cons.mpr ⟨fun hm => hwl (List.mem_filter.mp hm).1, hnd.filter _⟩
  cases ka <;> cases kb
  · refine key _ _ hop.1.1.1 (fun h => ?_) (fun p hp => ?_)
    · have : k + 2 < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show (rectW w ||| orEx u v l).testBit p = true
      rw [Nat.testBit_or]; simp at this; simpa using this
  · refine key _ _ hop.1.1.2 (fun h => ?_) (fun p hp => ?_)
    · have : k + 1 < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show ((rectW w ||| orEx u v l) ||| rectW v).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_or]; simp at this; simpa using this
  · refine key _ _ hop.1.2 (fun h => ?_) (fun p hp => ?_)
    · have : k + 1 < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show ((rectW w ||| orEx u v l) ||| rectW u).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_or]; simp at this; simpa using this
  · refine key _ _ hop.2 (fun h => ?_) (fun p hp => ?_)
    · have : k < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show ((rectW w ||| orEx u v l) ||| (rectW u ||| rectW v)).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]; simp at this; simpa using this

def expOK (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  sortedB l && !(allFinal l) && pairsAll (pairOK m P prev k l) l

theorem expOK_sound {m : Bool} {P : List ℕ → ℕ → Bool} {prev : Tree} {k : ℕ} {l : List ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k)
    (h : expOK m P prev k l = true) : ¬ Reach m l.toFinset (k + 1) := by
  intro hR
  simp only [expOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hs, hf⟩, hp⟩ := h
  have hnd := sortedB_nodup hs
  rcases hR.inv with he | ⟨u, v, w, ka, kb, hu, hv, hw, hd, hb, hR'⟩
  · exact notFinal hf he
  · have hd' : ∀ d ∈ l, blk m w d = false := fun d hdm => hd d (List.mem_toFinset.mpr hdm)
    have hu' := List.mem_toFinset.mp hu
    have hv' := List.mem_toFinset.mp hv
    have huv : u ≠ v := by
      rintro rfl
      have hwu : w = u := by
        rcases hw with hw | hw
        · rw [hw, Nat.and_self]
        · rw [hw, Nat.or_self]
      have := hd u hu
      rw [hwu, blk_refl] at this
      exact Bool.noConfusion this
    rcases pairsAll_mem _ _ hp u hu' v hv' huv with h1 | h1
    · exact pair_sound hP hinv hnd h1 hu' hv' ka kb w hw hd' hb hR'
    · have hw2 : w = v &&& u ∨ w = v ||| u := by
        rw [Nat.and_comm v u, Nat.or_comm v u]; exact hw
      have hfe : (l.toFinset.filter (fun x => (kb = true ∨ x ≠ v) ∧ (ka = true ∨ x ≠ u))) =
          (l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) := by
        ext x
        simp only [Finset.mem_filter]
        tauto
      have := pair_sound hP hinv hnd h1 hv' hu' kb ka w hw2 hd' hb
      rw [hfe] at this
      exact this hR'

/-- all sublists of a list satisfy `p`. -/
def subsAll : List ℕ → (List ℕ → Bool) → Bool
  | [], p => p []
  | a :: l, p => subsAll l p && subsAll l (fun s => p (a :: s))

theorem subsAll_sub : ∀ (l : List ℕ) (p : List ℕ → Bool), subsAll l p = true →
    ∀ s : List ℕ, s.Sublist l → p s = true := by
  intro l
  induction l with
  | nil =>
    intro p h s hs
    rw [List.sublist_nil.mp hs]; exact h
  | cons a l ih =>
    intro p h s hs
    simp only [subsAll, Bool.and_eq_true] at h
    cases hs with
    | cons _ hs' => exact ih p h.1 s hs'
    | cons_cons _ hs' => exact ih _ h.2 _ hs'

-- kernel-friendly versions: raw recursors, fully unfolded into one term

def bor (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) b true a
def band (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) false b a
def bnot (a : Bool) : Bool := @Bool.rec (fun _ => Bool) true false a

theorem bor_eq (a b : Bool) : bor a b = (a || b) := by cases a <;> rfl
theorem band_eq (a b : Bool) : band a b = (a && b) := by cases a <;> rfl
theorem bnot_eq (a : Bool) : bnot a = !a := by cases a <;> rfl

def domN' (w d : ℕ) : Bool :=
  band (Nat.beq (Nat.land (Nat.land w 4095) (Nat.sub 16777215 d)) 0)
    (Nat.beq (Nat.land (Nat.land d (Nat.sub 16777215 w)) 16773120) 0)

theorem domN'_eq (w d : ℕ) : domN' w d = domN w d := by
  unfold domN' domN; rw [band_eq]

def blk' (m : Bool) (w d : ℕ) : Bool := @Bool.rec (fun _ => Bool) (Nat.beq w d) (domN' w d) m

theorem blk'_eq (m : Bool) (w d : ℕ) : blk' m w d = blk m w d := by
  cases m
  · rfl
  · show domN' w d = domN w d
    exact domN'_eq w d

def blkAny' (m : Bool) (w : ℕ) (l : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false (fun d _ ih => bor (blk' m w d) ih) l

theorem blkAny'_eq (m : Bool) (w : ℕ) (l : List ℕ) : blkAny' m w l = blkAny m w l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    show bor (blk' m w d) (blkAny' m w l) = (blk m w d || blkAny m w l)
    rw [ih, bor_eq, blk'_eq]

def tb' (w e : ℕ) : Bool := bnot (Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb'_eq (w e : ℕ) : tb' w e = tb w e := by
  unfold tb' tb; rw [bnot_eq]

def rect' (x J n : ℕ) : ℕ :=
  @Nat.rec (fun _ => ℕ) 0
    (fun e ih => Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) ih) n

theorem rect'_eq (x J n : ℕ) : rect' x J n = rect x J n := by
  induction n with
  | zero => rfl
  | succ e ih =>
    show Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) (rect' x J e) =
      Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)
    rw [ih, tb'_eq]
    cases tb x e <;> rfl

def rectW' (x : ℕ) : ℕ := rect' x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rectW'_eq (x : ℕ) : rectW' x = rectW x := rect'_eq _ _ _

def orEx' (u v : ℕ) (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0
    (fun x _ ih => @Bool.rec (fun _ => ℕ) (Nat.lor (rectW' x) ih) ih
      (bor (Nat.beq x u) (Nat.beq x v))) l

theorem orEx'_eq (u v : ℕ) (l : List ℕ) : orEx' u v l = orEx u v l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show @Bool.rec (fun _ => ℕ) (Nat.lor (rectW' x) (orEx' u v l)) (orEx' u v l)
      (bor (Nat.beq x u) (Nat.beq x v)) =
      cond (Nat.beq x u || Nat.beq x v) (orEx u v l) (Nat.lor (rectW x) (orEx u v l))
    rw [ih, bor_eq, rectW'_eq]
    cases (Nat.beq x u || Nat.beq x v) <;> rfl

def allFinal' (l : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) true (fun a _ ih => band (Nat.beq a 4095) ih) l

theorem allFinal'_eq (l : List ℕ) : allFinal' l = allFinal l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show band (Nat.beq a 4095) (allFinal' l) = (Nat.beq a 4095 && allFinal l)
    rw [ih, band_eq]

def ins' (w : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [w]
    (fun a t ih => @Bool.rec (fun _ => List ℕ) (a :: ih) (w :: a :: t) (Nat.blt w a)) l

theorem ins'_eq (w : ℕ) (l : List ℕ) : ins' w l = ins w l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show @Bool.rec (fun _ => List ℕ) (a :: ins' w l) (w :: a :: l) (Nat.blt w a) =
      cond (Nat.blt w a) (w :: a :: l) (a :: ins w l)
    rw [ih]
    cases Nat.blt w a <;> rfl

def filt' (ka kb : Bool) (u v : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) []
    (fun x _ ih => @Bool.rec (fun _ => List ℕ) ih (x :: ih)
      (band (bor ka (bnot (Nat.beq x u))) (bor kb (bnot (Nat.beq x v))))) l

theorem filt'_eq (ka kb : Bool) (u v : ℕ) (l : List ℕ) :
    filt' ka kb u v l = l.filter (remF ka kb u v) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show @Bool.rec (fun _ => List ℕ) (filt' ka kb u v l) (x :: filt' ka kb u v l)
      (band (bor ka (bnot (Nat.beq x u))) (bor kb (bnot (Nat.beq x v)))) = _
    rw [ih, band_eq, bor_eq, bor_eq, bnot_eq, bnot_eq, List.filter_cons]
    show _ = if remF ka kb u v x = true then _ else _
    unfold remF
    cases ((ka || !Nat.beq x u) && (kb || !Nat.beq x v)) <;> rfl

def lcmp' (x y : List ℕ) : Ordering :=
  @List.rec ℕ (fun _ => List ℕ → Ordering)
    (fun y => @List.rec ℕ (fun _ => Ordering) Ordering.eq (fun _ _ _ => Ordering.lt) y)
    (fun a _ ih y => @List.rec ℕ (fun _ => Ordering) Ordering.gt
      (fun b y' _ => @Bool.rec (fun _ => Ordering)
        (@Bool.rec (fun _ => Ordering) (ih y') Ordering.gt (Nat.blt b a)) Ordering.lt (Nat.blt a b)) y)
    x y

theorem lcmp'_eq (x : List ℕ) : ∀ y : List ℕ, lcmp' x y = lcmp x y := by
  induction x with
  | nil => intro y; cases y <;> rfl
  | cons a x ih =>
    intro y
    cases y with
    | nil => rfl
    | cons b y =>
      show @Bool.rec (fun _ => Ordering)
        (@Bool.rec (fun _ => Ordering) (lcmp' x y) Ordering.gt (Nat.blt b a)) Ordering.lt (Nat.blt a b) =
        cond (Nat.blt a b) Ordering.lt (cond (Nat.blt b a) Ordering.gt (lcmp x y))
      rw [ih y]
      cases Nat.blt a b <;> cases Nat.blt b a <;> rfl

noncomputable def has' (t : Tree) (x : List ℕ) : Bool :=
  @BinaryTree.rec (List ℕ) (fun _ => Bool) false
    (fun key _ _ ihl ihr => @Ordering.rec (fun _ => Bool) ihl true ihr (lcmp' x key)) t

theorem has'_eq (t : Tree) (x : List ℕ) : has' t x = thas t x := by
  induction t with
  | nil => rfl
  | node key l r ihl ihr =>
    show @Ordering.rec (fun _ => Bool) (has' l x) true (has' r x) (lcmp' x key) =
      thas (BinaryTree.node key l r) x
    rw [ihl, ihr, lcmp'_eq]
    cases h : lcmp x key <;> rw [thas, h]

noncomputable def lastOK' (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  bor (bor (band (Nat.beq k 0) (bnot (allFinal' l))) (has' prev l)) (bnot (P l k))

theorem lastOK'_eq (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : lastOK' P prev k l = lastOK P prev k l := by
  unfold lastOK' lastOK
  rw [bor_eq, bor_eq, band_eq, bnot_eq, bnot_eq, allFinal'_eq, has'_eq]

def covR' (c : ℕ) : Bool := Nat.beq (Nat.land c full) full

/-- hand `f` the value of `x` as an evaluated numeral (the kernel substitutes arguments
unevaluated; a recursor on the argument forces it). -/
def forceN (x : ℕ) (f : ℕ → Bool) : Bool :=
  @Nat.rec (fun _ => Bool) (f 0) (fun p _ => f (Nat.succ p)) x

theorem forceN_eq (x : ℕ) (f : ℕ → Bool) : forceN x f = f x := by
  cases x <;> rfl

/-- hand `c` the list `l` with evaluated spine and elements. -/
def forceL (l : List ℕ) (c : List ℕ → Bool) : Bool :=
  @List.rec ℕ (fun _ => (List ℕ → Bool) → Bool) (fun c => c [])
    (fun x _ ih c => forceN x (fun x' => ih (fun t => c (x' :: t)))) l c

theorem forceL_eq (l : List ℕ) : ∀ c : List ℕ → Bool, forceL l c = c l := by
  induction l with
  | nil => intro c; rfl
  | cons x l ih =>
    intro c
    show forceN x (fun x' => forceL l (fun t => c (x' :: t))) = c (x :: l)
    rw [forceN_eq, ih]

noncomputable def sOK' (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ) (ka kb : Bool) : Bool :=
  bor (bor sz (bnot (covR' c))) (forceL (ins' w (filt' ka kb u v l)) (lastOK' P prev k))

theorem sOK'_eq (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ) (ka kb : Bool) :
    sOK' P prev k l u v w sz c ka kb = sOK P prev k l u v w sz c ka kb := by
  unfold sOK' sOK
  rw [bor_eq, bor_eq, bnot_eq, forceL_eq, lastOK'_eq, ins'_eq, filt'_eq]
  rfl

def len' (l : List ℕ) : ℕ := @List.rec ℕ (fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) l

theorem len'_eq (l : List ℕ) : len' l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => show Nat.succ (len' l) = _; rw [ih]; rfl

noncomputable def opOK2' (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) : Bool :=
  band (band (band
    (sOK' P prev k l u v w (Nat.blt (Nat.add k 2) (len' l)) c false false)
    (sOK' P prev k l u v w (Nat.blt (Nat.succ k) (len' l)) (Nat.lor c rv) false true))
    (sOK' P prev k l u v w (Nat.blt (Nat.succ k) (len' l)) (Nat.lor c ru) true false))
    (sOK' P prev k l u v w (Nat.blt k (len' l)) (Nat.lor c (Nat.lor ru rv)) true true)

theorem opOK2'_eq (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) :
    opOK2' P prev k l u ru v rv w c = opOK2 P prev k l u ru v rv w c := by
  unfold opOK2' opOK2
  simp only [band_eq, sOK'_eq, len'_eq]

noncomputable def opOK' (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) : Bool :=
  bor (bor (blkAny' m w base12) (blkAny' m w l))
    (opOK2' P prev k l u ru v rv w (Nat.lor (rectW' w) ro))

theorem opOK'_eq (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) :
    opOK' m P prev k l u ru v rv ro w = opOK m P prev k l u ru v rv ro w := by
  unfold opOK' opOK
  simp only [bor_eq, blkAny'_eq, opOK2'_eq, rectW'_eq]

noncomputable def pairOK' (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v : ℕ) : Bool :=
  band (opOK' m P prev k l u (rectW' u) v (rectW' v) (orEx' u v l) (Nat.land u v))
    (opOK' m P prev k l u (rectW' u) v (rectW' v) (orEx' u v l) (Nat.lor u v))

theorem pairOK'_eq (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) (u v : ℕ) :
    pairOK' m P prev k l u v = pairOK m P prev k l u v := by
  unfold pairOK' pairOK
  simp only [band_eq, opOK'_eq, rectW'_eq, orEx'_eq]

def allB' (f : ℕ → Bool) (l : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) true (fun a _ ih => band (f a) ih) l

theorem allB'_eq (f : ℕ → Bool) (l : List ℕ) : allB' f l = allB f l := by
  induction l with
  | nil => rfl
  | cons a l ih => show band (f a) (allB' f l) = (f a && allB f l); rw [ih, band_eq]

def pairsAll' (f : ℕ → ℕ → Bool) (l : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) true (fun a t ih => band (allB' (f a) t) ih) l

theorem pairsAll'_eq (f : ℕ → ℕ → Bool) (l : List ℕ) : pairsAll' f l = pairsAll f l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show band (allB' (f a) l) (pairsAll' f l) = (allB (f a) l && pairsAll f l)
    rw [ih, band_eq, allB'_eq]

noncomputable def expOK' (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) : Bool :=
  band (band (sortedB l) (bnot (allFinal' l))) (pairsAll' (pairOK' m P prev k l) l)

theorem expOK'_eq (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) (l : List ℕ) :
    expOK' m P prev k l = expOK m P prev k l := by
  unfold expOK' expOK
  have : pairOK' m P prev k l = pairOK m P prev k l := by
    funext u v; exact pairOK'_eq m P prev k l u v
  rw [band_eq, band_eq, bnot_eq, allFinal'_eq, pairsAll'_eq, this]

/-- `expOK'` with every auxiliary definition unfolded (one closed term for the kernel). -/
noncomputable def expFastSub :
    {f : Bool → (List ℕ → ℕ → Bool) → Tree → ℕ → List ℕ → Bool // f = expOK'} := by
  refine ⟨?f, ?h⟩
  case h =>
    delta expOK' pairsAll' allB' pairOK' opOK' opOK2' sOK' len' covR' lastOK' has' lcmp' filt' ins'
      allFinal' orEx' rectW' rect' tb' blkAny' blk' domN' band bor bnot full base12 base10 forceL forceN
    beta_reduce
    exact rfl

noncomputable def expFast : Bool → (List ℕ → ℕ → Bool) → Tree → ℕ → List ℕ → Bool :=
  expFastSub.1

theorem expFast_eq (m : Bool) (P : List ℕ → ℕ → Bool) (prev : Tree) (k : ℕ) :
    expFast m P prev k = expOK m P prev k := by
  funext l
  have : expFast = expOK' := expFastSub.2
  rw [this]
  exact expOK'_eq m P prev k l

theorem level_fast {m : Bool} {P : List ℕ → ℕ → Bool} {prev T : Tree} {k : ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k)
    (h : tall (expFast m P prev k) T = true) : Inv m T (k + 1) := by
  rw [expFast_eq] at h
  intro x hx
  exact expOK_sound hP hinv (thas_all _ T x h hx)

theorem level_sound {m : Bool} {P : List ℕ → ℕ → Bool} {prev T : Tree} {k : ℕ}
    (hP : PruneOK m P) (hinv : Inv m prev k)
    (h : tall (expOK m P prev k) T = true) : Inv m T (k + 1) := by
  intro x hx
  exact expOK_sound hP hinv (thas_all _ T x h hx)

theorem tall_node (p : List ℕ → Bool) (l r : Tree) (key : List ℕ) (h1 : tall p l = true)
    (h2 : p key = true) (h3 : tall p r = true) : tall p (BinaryTree.node key l r) = true := by
  simp only [tall, h1, h2, h3]; rfl

theorem inv_leaf (m : Bool) : Inv m BinaryTree.nil 0 := by
  intro x hx
  simp [thas] at hx

/-- the conclusion of a certificate: no subset of the base words reaches the target. -/
def NoStart (m : Bool) (n : ℕ) : Prop :=
  ∀ L : Finset ℕ, (∀ x ∈ L, x ∈ base10) → ¬ Reach m L n

theorem start_sound {m : Bool} {prev : Tree} {n : ℕ} (hinv : Inv m prev n)
    (h : subsAll base10 (closed prev n) = true) : NoStart m n := by
  intro L hL
  have hs : (base10.filter (fun x => decide (x ∈ L))).Sublist base10 := List.filter_sublist
  have he : (base10.filter (fun x => decide (x ∈ L))).toFinset = L := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hL x h, h⟩⟩
  have hnd : (base10.filter (fun x => decide (x ∈ L))).Nodup := List.Nodup.sublist hs (by decide)
  have := closed_sound hnd hinv (subsAll_sub base10 _ h _ hs)
  rw [he] at this
  exact this

/-- reachability with history: `H` = all words produced so far (live or not); a new word must
not be blocked by `base12`, by `H`, or by the live set `D`. -/
inductive ReachH (m : Bool) : Finset ℕ → Finset ℕ → ℕ → Prop
  | done (H : Finset ℕ) (k : ℕ) : ReachH m H {4095} k
  | step (H D : Finset ℕ) (k u v w : ℕ) (ka kb : Bool) :
      u ∈ D → v ∈ D → (w = u &&& v ∨ w = u ||| v) →
      (∀ d ∈ H, blk m w d = false) →
      (∀ d ∈ D, blk m w d = false) → (∀ d ∈ base12, blk m w d = false) →
      ReachH m (insert w H)
        (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k →
      ReachH m H D (k + 1)

theorem ReachH.toReach {m : Bool} {H D : Finset ℕ} {k : ℕ} (h : ReachH m H D k) : Reach m D k := by
  induction h with
  | done H k => exact Reach.done k
  | step H D k u v w ka kb hu hv hw _ hd hb _ ih => exact Reach.step D k u v w ka kb hu hv hw hd hb ih

theorem ReachH.anti {m : Bool} {H D : Finset ℕ} {k : ℕ} (h : ReachH m H D k) :
    ∀ H' : Finset ℕ, H' ⊆ H → ReachH m H' D k := by
  induction h with
  | done H k => intro H' _; exact ReachH.done H' k
  | step H D k u v w ka kb hu hv hw hH hd hb _ ih =>
    intro H' hsub
    exact ReachH.step H' D k u v w ka kb hu hv hw (fun d hd' => hH d (hsub hd')) hd hb
      (ih _ (Finset.insert_subset_insert w hsub))

theorem ReachH.mono {m : Bool} {H D : Finset ℕ} {k : ℕ} (h : ReachH m H D k) :
    ReachH m H D (k + 1) := by
  induction h with
  | done H k => exact ReachH.done _ _
  | step H D k u v w ka kb hu hv hw hH hd hb _ ih =>
    exact ReachH.step H D (k + 1) u v w ka kb hu hv hw hH hd hb ih

theorem ReachH.mono_le {m : Bool} {H D : Finset ℕ} {k k' : ℕ} (hk : k ≤ k') (h : ReachH m H D k) :
    ReachH m H D k' := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih.mono

theorem ReachH.inv' {m : Bool} {H D : Finset ℕ} {k' : ℕ} (h : ReachH m H D k') : ∀ k : ℕ,
    k' = k + 1 →
    D = {4095} ∨ ∃ (u v w : ℕ) (ka kb : Bool), u ∈ D ∧ v ∈ D ∧ (w = u &&& v ∨ w = u ||| v) ∧
      (∀ d ∈ H, blk m w d = false) ∧
      (∀ d ∈ D, blk m w d = false) ∧ (∀ d ∈ base12, blk m w d = false) ∧
      ReachH m (insert w H)
        (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k := by
  induction h with
  | done H k0 => intro _ _; exact Or.inl rfl
  | step H D k0 u v w ka kb hu hv hw hH hd hb hr _ =>
    intro k hk
    obtain rfl : k0 = k := by omega
    exact Or.inr ⟨u, v, w, ka, kb, hu, hv, hw, hH, hd, hb, hr⟩

-- from a trace to `Reach`

inductive Tr (m : Bool) : List ℕ → Prop
  | nil : Tr m []
  | snoc (s : List ℕ) (w : ℕ) : Tr m s → w < 16777216 →
      (∀ d ∈ base12 ++ s, blk m w d = false) →
      (∃ u ∈ base12 ++ s, ∃ v ∈ base12 ++ s, w = u &&& v ∨ w = u ||| v) → Tr m (s ++ [w])

theorem Tr.bound {m : Bool} {s : List ℕ} (h : Tr m s) : ∀ x ∈ s, x < 16777216 := by
  induction h with
  | nil => intro x hx; simp at hx
  | snoc s w _ hw _ _ ih =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ih x hx
    · rw [List.mem_singleton.mp hx]; exact hw

theorem ones_and (v : ℕ) (hv : v < 16777216) : 16777215 &&& v = v := by
  have e : (16777215 : ℕ) = 2 ^ 24 - 1 := by norm_num
  rw [Nat.and_comm, e, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt hv

theorem ones_or (v : ℕ) (hv : v < 16777216) : 16777215 ||| v = 16777215 := by
  have e : (16777215 : ℕ) = 2 ^ 24 - 1 := by norm_num
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, e, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 24
  · simp [hi]
  · have : v.testBit i = false := by
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le hv (by
        have : (2 : ℕ) ^ 24 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
    simp [hi, this]

theorem absorb (S : List ℕ) (h0 : 0 ∈ S) (h1 : 16777215 ∈ S) (hb : ∀ x ∈ S, x < 16777216)
    (u v : ℕ) (hu : u ∈ S) (hv : v ∈ S) (hz : u = 0 ∨ u = 16777215 ∨ u = v) :
    u &&& v ∈ S ∧ u ||| v ∈ S := by
  rcases hz with rfl | rfl | rfl
  · simpa using ⟨h0, hv⟩
  · rw [ones_and v (hb v hv), ones_or v (hb v hv)]; exact ⟨hv, h1⟩
  · simpa using hu

theorem base12_lt : ∀ x ∈ base12, x < 16777216 := by decide

theorem mem12 {x : ℕ} (h : x ∈ base12) : x = 0 ∨ x = 16777215 ∨ x ∈ base10 := by
  simpa [base12] using h

theorem Tr.reach {m : Bool} {s : List ℕ} (h : Tr m s) : ∀ (L : Finset ℕ) (k : ℕ),
    (∀ x ∈ L, x ∈ base10 ∨ x ∈ s) → ReachH m s.toFinset L k →
    ∃ L0 : Finset ℕ, (∀ x ∈ L0, x ∈ base10) ∧ ReachH m ∅ L0 (k + s.length) := by
  induction h with
  | nil =>
    intro L k hL hR
    exact ⟨L, fun x hx => (hL x hx).resolve_right (by simp), by simpa using hR⟩
  | snoc s w hs hwlt hdom hop ih =>
    intro L k hL hR
    have hlen : k + (s ++ [w]).length = k + s.length + 1 := by simp; omega
    rw [hlen]
    by_cases hwL : w ∈ L
    · obtain ⟨u, hu, v, hv, hw⟩ := hop
      have hne : ∀ x ∈ base12 ++ s, w ≠ x := fun x hx he => by
        have := hdom x hx
        rw [← he, blk_refl] at this
        exact Bool.noConfusion this
      have hbd : ∀ x ∈ base12 ++ s, x < 16777216 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact base12_lt x hx
        · exact hs.bound x hx
      have h0 : (0 : ℕ) ∈ base12 ++ s := List.mem_append_left _ (by simp [base12])
      have h1 : (16777215 : ℕ) ∈ base12 ++ s := List.mem_append_left _ (by simp [base12])
      have hwS : ¬ (w ∈ base12 ++ s) := fun hm => hne w hm rfl
      have hu0 : ¬ (u = 0 ∨ u = 16777215 ∨ u = v) := fun hz => by
        have := absorb _ h0 h1 hbd u v hu hv hz
        rcases hw with hw | hw
        · exact hwS (hw ▸ this.1)
        · exact hwS (hw ▸ this.2)
      have hv0 : ¬ (v = 0 ∨ v = 16777215) := fun hz => by
        have := absorb _ h0 h1 hbd v u hv hu (by tauto)
        rw [Nat.and_comm, Nat.or_comm] at this
        rcases hw with hw | hw
        · exact hwS (hw ▸ this.1)
        · exact hwS (hw ▸ this.2)
      have hu' : u ∈ base10 ∨ u ∈ s := by
        rcases List.mem_append.mp hu with hx | hx
        · rcases mem12 hx with h | h | h
          · exact absurd (Or.inl h) hu0
          · exact absurd (Or.inr (Or.inl h)) hu0
          · exact Or.inl h
        · exact Or.inr hx
      have hv' : v ∈ base10 ∨ v ∈ s := by
        rcases List.mem_append.mp hv with hx | hx
        · rcases mem12 hx with h | h | h
          · exact absurd (Or.inl h) hv0
          · exact absurd (Or.inr h) hv0
          · exact Or.inl h
        · exact Or.inr hx
      have hwu : w ≠ u := hne u hu
      have hwv : w ≠ v := hne v hv
      have hL' : ∀ x ∈ insert u (insert v (L.erase w)), x ∈ base10 ∨ x ∈ s := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hu'
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hv'
        have hx2 := Finset.mem_erase.mp hx
        rcases hL x hx2.2 with h | h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inr h
          · exact absurd (List.mem_singleton.mp h) hx2.1
      have hsub : ∀ x, (x ∈ base10 ∨ x ∈ s) → x ∈ base12 ++ s := by
        intro x hx
        rcases hx with h | h
        · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        · exact List.mem_append_right _ h
      have hEq : insert w ((insert u (insert v (L.erase w))).filter
          (fun x => (decide (u ∈ L) = true ∨ x ≠ u) ∧ (decide (v ∈ L) = true ∨ x ≠ v))) = L := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_erase, decide_eq_true_eq]
        constructor
        · rintro (rfl | ⟨hx, h1, h2⟩)
          · exact hwL
          · rcases hx with rfl | rfl | hx
            · exact h1.resolve_right (fun h => h rfl)
            · exact h2.resolve_right (fun h => h rfl)
            · exact hx.2
        · intro hx
          by_cases hxw : x = w
          · exact Or.inl hxw
          · refine Or.inr ⟨Or.inr (Or.inr ⟨hxw, hx⟩), ?_, ?_⟩
            · by_cases hxu : x = u
              · exact Or.inl (hxu ▸ hx)
              · exact Or.inr hxu
            · by_cases hxv : x = v
              · exact Or.inl (hxv ▸ hx)
              · exact Or.inr hxv
      have hT : (s ++ [w]).toFinset = insert w s.toFinset := by
        ext x; simp [or_comm]
      have hR' : ReachH m s.toFinset (insert u (insert v (L.erase w))) (k + 1) := by
        refine ReachH.step _ _ k u v w (decide (u ∈ L)) (decide (v ∈ L)) (by simp) (by simp) hw
          (fun d hd => hdom d (List.mem_append_right _ (List.mem_toFinset.mp hd)))
          (fun d hd => hdom d (hsub d (hL' d hd)))
          (fun d hd => hdom d (List.mem_append_left _ hd)) ?_
        rw [hEq, ← hT]; exact hR
      obtain ⟨L0, hL0, hR0⟩ := ih _ (k + 1) hL' hR'
      refine ⟨L0, hL0, ?_⟩
      have e : k + 1 + s.length = k + s.length + 1 := by omega
      rw [← e]; exact hR0
    · have hL' : ∀ x ∈ L, x ∈ base10 ∨ x ∈ s := by
        intro x hx
        rcases hL x hx with h | h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inr h
          · exact absurd (List.mem_singleton.mp h ▸ hx) hwL
      obtain ⟨L0, hL0, hR0⟩ := ih L k hL' (hR.anti _ (by
        intro x hx
        rw [List.mem_toFinset] at hx ⊢
        exact List.mem_append_left _ hx))
      exact ⟨L0, hL0, hR0.mono⟩

/-- conclusion of a certificate with history. -/
def NoStartH (m : Bool) (n : ℕ) : Prop :=
  ∀ L : Finset ℕ, (∀ x ∈ L, x ∈ base10) → ¬ ReachH m ∅ L n

theorem NoStart.toH {m : Bool} {n : ℕ} (h : NoStart m n) : NoStartH m n :=
  fun L hL hR => h L hL hR.toReach

/-- Nat-level conclusion: no trace of length at most `n` contains 4095. -/
theorem no_trace {m : Bool} {n : ℕ} (h : NoStartH m n) {s : List ℕ}
    (hs : Tr m s) (hlen : s.length ≤ n) : 4095 ∉ s := by
  intro hmem
  obtain ⟨L0, hL0, hR0⟩ := hs.reach {4095} 0
    (fun x hx => Or.inr (Finset.mem_singleton.mp hx ▸ hmem)) (ReachH.done _ 0)
  exact h L0 hL0 (hR0.mono_le (by omega))

-- bridge to `BitVec 24`

theorem dom_bridge (a d : BitVec 24) :
    ((a &&& 4095) &&& ~~~d = 0 ∧ (d &&& ~~~a) &&& 16773120 = 0) ↔ domN a.toNat d.toNat = true := by
  have e1 : Nat.land (Nat.land a.toNat 4095) (Nat.sub 16777215 d.toNat) =
      ((a &&& 4095) &&& ~~~d).toNat := by
    simp only [BitVec.toNat_and, BitVec.toNat_not]; rfl
  have e2 : Nat.land (Nat.land d.toNat (Nat.sub 16777215 a.toNat)) 16773120 =
      ((d &&& ~~~a) &&& 16773120).toNat := by
    simp only [BitVec.toNat_and, BitVec.toNat_not]; rfl
  unfold domN
  rw [e1, e2, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true h1),
      BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true h2)⟩

def baseBV : List (BitVec 24) :=
  0 :: 16777215 :: [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056,
    15731968, 5689661]

theorem baseBV_mem {x : BitVec 24} (h : x ∈ baseBV) : x.toNat ∈ base12 := by
  simp only [baseBV, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem base12_mem {y : ℕ} (h : y ∈ base12) :
    BitVec.ofNat 24 y ∈ baseBV ∧ (BitVec.ofNat 24 y).toNat = y := by
  simp only [base12, base10, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp [baseBV], rfl⟩

theorem search_soundH (n : ℕ) (hc : NoStartH true n) :
    ¬ ∃ t : List (BitVec 24), let B : List (BitVec 24) := 0 :: 16777215 :: [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661];
      t.length ≤ n ∧ (4095 : BitVec 24) ∈ t ∧ ∀ (j : ℕ) (hj : j < t.length),
        (∀ d ∈ B ++ t.take j, ¬ ((t[j] &&& 4095) &&& ~~~d = 0 ∧ (d &&& ~~~t[j]) &&& 16773120 = 0)) ∧
        ∃ u ∈ B ++ t.take j, ∃ v ∈ B ++ t.take j, t[j] = u &&& v ∨ t[j] = u ||| v := by
  rintro ⟨t, hlen, hmem, H⟩
  have hmap : ∀ (j : ℕ) (x : BitVec 24), x ∈ baseBV ++ t.take j →
      x.toNat ∈ base12 ++ (t.take j).map BitVec.toNat := by
    intro j x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (baseBV_mem hx)
    · exact List.mem_append_right _ (List.mem_map_of_mem hx)
  have hmap' : ∀ (j : ℕ) (y : ℕ), y ∈ base12 ++ (t.take j).map BitVec.toNat →
      ∃ x ∈ baseBV ++ t.take j, x.toNat = y := by
    intro j y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact ⟨_, List.mem_append_left _ (base12_mem hy).1, (base12_mem hy).2⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      exact ⟨x, List.mem_append_right _ hx, rfl⟩
  have htr : ∀ j : ℕ, j ≤ t.length → Tr true ((t.take j).map BitVec.toNat) := by
    intro j
    induction j with
    | zero => intro _; exact Tr.nil
    | succ j ih =>
      intro hj
      have hj' : j < t.length := hj
      rw [List.take_succ_eq_append_getElem hj', List.map_append]
      obtain ⟨hd, u, hu, v, hv, huv⟩ := H j hj'
      refine Tr.snoc _ _ (ih (Nat.le_of_lt hj')) (t[j]).isLt ?_ ?_
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hmap' j y hy
        have := hd x hx
        rw [dom_bridge] at this
        simpa [blk] using this
      · refine ⟨u.toNat, hmap j u hu, v.toNat, hmap j v hv, ?_⟩
        rcases huv with h | h
        · left; rw [h, BitVec.toNat_and]
        · right; rw [h, BitVec.toNat_or]
  have hT := htr t.length le_rfl
  rw [List.take_length] at hT
  refine no_trace hc hT (by simpa using hlen) ?_
  exact List.mem_map.mpr ⟨4095, hmem, rfl⟩

-- fuel DFS: the kernel runs the search itself, no state tables

/-- `rec k l = true` certifies that `l` cannot reach the target in `k` steps. -/
def Good (m : Bool) (rec : ℕ → List ℕ → Bool) : Prop :=
  ∀ (k : ℕ) (l : List ℕ), l.Nodup → rec k l = true → ¬ Reach m l.toFinset k

def sD (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ)
    (ka kb : Bool) : Bool :=
  sz || !(covR c) || rec k (w :: l.filter (remF ka kb u v))

def opD2 (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) : Bool :=
  sD rec k l u v w (Nat.blt (Nat.add k 2) l.length) c false false &&
  sD rec k l u v w (Nat.blt (Nat.succ k) l.length) (Nat.lor c rv) false true &&
  sD rec k l u v w (Nat.blt (Nat.succ k) l.length) (Nat.lor c ru) true false &&
  sD rec k l u v w (Nat.blt k l.length) (Nat.lor c (Nat.lor ru rv)) true true

def opD (m : Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) : Bool :=
  blkAny m w base12 || blkAny m w l || opD2 rec k l u ru v rv w (Nat.lor (rectW w) ro)

def pairD (m : Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u v : ℕ) : Bool :=
  opD m rec k l u (rectW u) v (rectW v) (orEx u v l) (Nat.land u v) &&
  opD m rec k l u (rectW u) v (rectW v) (orEx u v l) (Nat.lor u v)

/-- one node: pruned, or (not final and every move is blocked or leads to a closed child). -/
def node (m : Bool) (P : List ℕ → ℕ → Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) : Bool :=
  !(P l k) || (!(allFinal l) && (Nat.beq k 0 || pairsAll (pairD m rec (Nat.pred k) l) l))

/-- the DFS with `fuel` levels; below them `leaf` decides. -/
def dfsG (m : Bool) (P : List ℕ → ℕ → Bool) (leaf : ℕ → List ℕ → Bool) : ℕ → ℕ → List ℕ → Bool
  | 0 => leaf
  | f + 1 => node m P (dfsG m P leaf f)

theorem child_toFinset (l : List ℕ) (w : ℕ) (ka kb : Bool) (u v : ℕ) :
    (w :: l.filter (remF ka kb u v)).toFinset =
      insert w (l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) := by
  ext x
  simp [remF, List.mem_filter, beq_false_iff]

theorem child_nodup {l : List ℕ} {w : ℕ} (hnd : l.Nodup) (hwl : w ∉ l) (ka kb : Bool) (u v : ℕ) :
    (w :: l.filter (remF ka kb u v)).Nodup :=
  List.nodup_cons.mpr ⟨fun hm => hwl (List.mem_filter.mp hm).1, hnd.filter _⟩

/-- if the child can reach the target, neither the size test nor the cover test fired, so the
recursive call was made and returned `true`. -/
theorem op_core {m : Bool} {rec : ℕ → List ℕ → Bool} {k : ℕ} {l : List ℕ} {u v w : ℕ}
    (hnd : l.Nodup) (hwl : w ∉ l) (ka kb : Bool)
    (hop : opD2 rec k l u (rectW u) v (rectW v) w (Nat.lor (rectW w) (orEx u v l)) = true)
    (hR : Reach m (insert w (l.toFinset.filter
      (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k) :
    rec k (w :: l.filter (remF ka kb u v)) = true := by
  simp only [opD2, Bool.and_eq_true] at hop
  have hsz : l.length ≤ k + (cond ka 0 1 + cond kb 0 1) := by
    have h1 := hR.card
    have hwF : w ∉ l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwl (List.mem_toFinset.mp (Finset.mem_of_mem_filter _ hm))
    rw [Finset.card_insert_of_notMem hwF] at h1
    have h2 := size_lb l.toFinset u v ka kb
    rw [List.toFinset_card_of_nodup hnd] at h2
    omega
  have hbit : ∀ p, p < 144 → ((rectW w).testBit p = true ∨ (orEx u v l).testBit p = true) ∨
      (ka = true ∧ (rectW u).testBit p = true) ∨ (kb = true ∧ (rectW v).testBit p = true) := by
    intro p hp
    obtain ⟨x, hx, hxb⟩ := sep_bit hR p hp
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl (Or.inl hxb)
    · obtain ⟨hxl, h1, h2⟩ := Finset.mem_filter.mp hx
      by_cases hxu : x = u
      · exact Or.inr (Or.inl ⟨h1.resolve_right (fun h => h hxu), hxu ▸ hxb⟩)
      · by_cases hxv : x = v
        · exact Or.inr (Or.inr ⟨h2.resolve_right (fun h => h hxv), hxv ▸ hxb⟩)
        · exact Or.inl (Or.inr (orEx_tb u v p _ x (List.mem_toFinset.mp hxl) hxu hxv hxb))
  have key : ∀ (sz : Bool) (c : ℕ), sD rec k l u v w sz c ka kb = true →
      (sz = true → False) → (∀ p, p < 144 → c.testBit p = true) →
      rec k (w :: l.filter (remF ka kb u v)) = true := by
    intro sz c h h1 h2
    simp only [sD, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | h) | h
    · exact absurd h (fun h' => h1 h')
    · rw [covR_of c h2] at h; exact Bool.noConfusion h
    · exact h
  cases ka <;> cases kb
  · refine key _ _ hop.1.1.1 (fun h => ?_) (fun p hp => ?_)
    · have : k + 2 < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show (rectW w ||| orEx u v l).testBit p = true
      rw [Nat.testBit_or]; simp at this; simpa using this
  · refine key _ _ hop.1.1.2 (fun h => ?_) (fun p hp => ?_)
    · have : k + 1 < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show ((rectW w ||| orEx u v l) ||| rectW v).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_or]; simp at this; simpa using this
  · refine key _ _ hop.1.2 (fun h => ?_) (fun p hp => ?_)
    · have : k + 1 < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show ((rectW w ||| orEx u v l) ||| rectW u).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_or]; simp at this; simpa using this
  · refine key _ _ hop.2 (fun h => ?_) (fun p hp => ?_)
    · have : k < l.length := by simpa [Nat.blt_eq] using h
      simp at hsz; omega
    · have := hbit p hp
      show ((rectW w ||| orEx u v l) ||| (rectW u ||| rectW v)).testBit p = true
      rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_or]; simp at this; simpa using this

theorem pairD_sound {m : Bool} {rec : ℕ → List ℕ → Bool} {k : ℕ} {l : List ℕ} {u v : ℕ}
    (hrec : Good m rec) (hnd : l.Nodup) (hp : pairD m rec k l u v = true)
    (ka kb : Bool) (w : ℕ) (hw : w = u &&& v ∨ w = u ||| v)
    (hd : ∀ d ∈ l, blk m w d = false) (hb : ∀ d ∈ base12, blk m w d = false) :
    ¬ Reach m (insert w (l.toFinset.filter
      (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k := by
  intro hR
  simp only [pairD, Bool.and_eq_true] at hp
  have hop : opD m rec k l u (rectW u) v (rectW v) (orEx u v l) w = true := by
    rcases hw with rfl | rfl
    · exact hp.1
    · exact hp.2
  simp only [opD, blkAny_false m w base12 hb, blkAny_false m w l hd, Bool.false_or] at hop
  have hwl : w ∉ l := fun hm => by
    have := hd w hm
    rw [blk_refl] at this
    exact Bool.noConfusion this
  have h1 := op_core hnd hwl ka kb hop hR
  have h2 := hrec k _ (child_nodup hnd hwl ka kb u v) h1
  rw [child_toFinset] at h2
  exact h2 hR

theorem node_sound {m : Bool} {P : List ℕ → ℕ → Bool} {rec : ℕ → List ℕ → Bool}
    (hP : PruneOK m P) (hrec : Good m rec) : Good m (node m P rec) := by
  intro k l hnd h hR
  simp only [node, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with h | ⟨hf, h⟩
  · rw [hP l k hnd hR] at h; exact Bool.noConfusion h
  · rcases h with h | hp
    · have hk : k = 0 := Nat.eq_of_beq_eq_true h
      subst hk
      exact notFinal hf hR.zero
    · cases k with
      | zero => exact notFinal hf hR.zero
      | succ k =>
        rcases hR.inv with he | ⟨u, v, w, ka, kb, hu, hv, hw, hd, hb, hR'⟩
        · exact notFinal hf he
        · have hd' : ∀ d ∈ l, blk m w d = false := fun d hdm => hd d (List.mem_toFinset.mpr hdm)
          have hu' := List.mem_toFinset.mp hu
          have hv' := List.mem_toFinset.mp hv
          have huv : u ≠ v := by
            rintro rfl
            have hwu : w = u := by
              rcases hw with hw | hw
              · rw [hw, Nat.and_self]
              · rw [hw, Nat.or_self]
            have := hd u hu
            rw [hwu, blk_refl] at this
            exact Bool.noConfusion this
          rcases pairsAll_mem _ _ hp u hu' v hv' huv with h1 | h1
          · exact pairD_sound hrec hnd h1 ka kb w hw hd' hb hR'
          · have hw2 : w = v &&& u ∨ w = v ||| u := by
              rw [Nat.and_comm v u, Nat.or_comm v u]; exact hw
            have hfe : (l.toFinset.filter (fun x => (kb = true ∨ x ≠ v) ∧ (ka = true ∨ x ≠ u))) =
                (l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) := by
              ext x
              simp only [Finset.mem_filter]
              tauto
            have := pairD_sound hrec hnd h1 kb ka w hw2 hd' hb
            rw [hfe] at this
            exact this hR'

/-- the ONE generic soundness theorem of the DFS. -/
theorem dfsG_sound {m : Bool} {P : List ℕ → ℕ → Bool} {leaf : ℕ → List ℕ → Bool}
    (hP : PruneOK m P) (hleaf : Good m leaf) : ∀ f : ℕ, Good m (dfsG m P leaf f) := by
  intro f
  induction f with
  | zero => exact hleaf
  | succ f ih => exact node_sound hP ih

theorem good_false (m : Bool) : Good m (fun _ _ => false) := by
  intro k l _ h
  exact Bool.noConfusion h

/-- cut states (cubes): `(steps left, live list)`, each proved by its own chunk theorem. -/
def hasCube : List (ℕ × List ℕ) → ℕ → List ℕ → Bool
  | [], _, _ => false
  | c :: cs, k, l => (Nat.beq k c.1 && (lcmp l c.2 == Ordering.eq)) || hasCube cs k l

def CubeGood (m : Bool) (c : ℕ × List ℕ) : Prop := c.2.Nodup → ¬ Reach m c.2.toFinset c.1

theorem hasCube_good {m : Bool} : ∀ cs : List (ℕ × List ℕ), (∀ c ∈ cs, CubeGood m c) →
    Good m (hasCube cs) := by
  intro cs
  induction cs with
  | nil => intro _ k l _ h; exact Bool.noConfusion h
  | cons c cs ih =>
    intro hc k l hnd h
    simp only [hasCube, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · have hk : k = c.1 := Nat.eq_of_beq_eq_true h1
      have hl : l = c.2 := lcmp_eq _ _ h2
      rw [hk, hl]
      exact hc c List.mem_cons_self (hl ▸ hnd)
    · exact ih (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')) k l hnd h

def startD (rec : ℕ → List ℕ → Bool) (n : ℕ) (s : List ℕ) : Bool :=
  Nat.blt (Nat.succ n) s.length || !(covR (orR s)) || rec n s

theorem startD_sound {m : Bool} {rec : ℕ → List ℕ → Bool} {n : ℕ} (hrec : Good m rec)
    (h : subsAll base10 (startD rec n) = true) : NoStart m n := by
  intro L hL
  have hs : (base10.filter (fun x => decide (x ∈ L))).Sublist base10 := List.filter_sublist
  have he : (base10.filter (fun x => decide (x ∈ L))).toFinset = L := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hL x h, h⟩⟩
  have hnd : (base10.filter (fun x => decide (x ∈ L))).Nodup := List.Nodup.sublist hs (by decide)
  have h1 := subsAll_sub base10 _ h _ hs
  rw [← he]
  intro hR
  simp only [startD, Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with (h1 | h1) | h1
  · have h2 : n + 1 < (base10.filter (fun x => decide (x ∈ L))).length := by
      simpa [Nat.blt_eq] using h1
    have h3 := hR.card
    rw [List.toFinset_card_of_nodup hnd] at h3
    omega
  · exact cover_sound h1 hR
  · exact hrec n _ hnd h1 hR

-- raw-recursor twins of the DFS

def sD' (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ)
    (ka kb : Bool) : Bool :=
  bor (bor sz (bnot (covR' c))) (forceL (w :: filt' ka kb u v l) (rec k))

theorem sD'_eq (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u v w : ℕ) (sz : Bool) (c : ℕ)
    (ka kb : Bool) : sD' rec k l u v w sz c ka kb = sD rec k l u v w sz c ka kb := by
  unfold sD' sD
  rw [bor_eq, bor_eq, bnot_eq, filt'_eq, forceL_eq]
  rfl

def opD2' (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) : Bool :=
  band (band (band
    (sD' rec k l u v w (Nat.blt (Nat.add k 2) (len' l)) c false false)
    (sD' rec k l u v w (Nat.blt (Nat.succ k) (len' l)) (Nat.lor c rv) false true))
    (sD' rec k l u v w (Nat.blt (Nat.succ k) (len' l)) (Nat.lor c ru) true false))
    (sD' rec k l u v w (Nat.blt k (len' l)) (Nat.lor c (Nat.lor ru rv)) true true)

theorem opD2'_eq (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u ru v rv w c : ℕ) :
    opD2' rec k l u ru v rv w c = opD2 rec k l u ru v rv w c := by
  unfold opD2' opD2
  simp only [band_eq, sD'_eq, len'_eq]

def opD' (m : Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) : Bool :=
  bor (bor (blkAny' m w base12) (blkAny' m w l))
    (opD2' rec k l u ru v rv w (Nat.lor (rectW' w) ro))

theorem opD'_eq (m : Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u ru v rv ro w : ℕ) :
    opD' m rec k l u ru v rv ro w = opD m rec k l u ru v rv ro w := by
  unfold opD' opD
  simp only [bor_eq, blkAny'_eq, opD2'_eq, rectW'_eq]

def pairD' (m : Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u v : ℕ) : Bool :=
  band (opD' m rec k l u (rectW' u) v (rectW' v) (orEx' u v l) (Nat.land u v))
    (opD' m rec k l u (rectW' u) v (rectW' v) (orEx' u v l) (Nat.lor u v))

theorem pairD'_eq (m : Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) (u v : ℕ) :
    pairD' m rec k l u v = pairD m rec k l u v := by
  unfold pairD' pairD
  simp only [band_eq, opD'_eq, rectW'_eq, orEx'_eq]

def node' (m : Bool) (P : List ℕ → ℕ → Bool) (rec : ℕ → List ℕ → Bool) (k : ℕ) (l : List ℕ) : Bool :=
  bor (bnot (P l k)) (band (bnot (allFinal' l))
    (@Nat.rec (fun _ => Bool) true (fun k' _ => pairsAll' (pairD' m rec k' l) l) k))

theorem node'_eq (m : Bool) (P : List ℕ → ℕ → Bool) (rec : ℕ → List ℕ → Bool) :
    node' m P rec = node m P rec := by
  funext k l
  unfold node' node
  have h1 : ∀ k', pairD' m rec k' l = pairD m rec k' l := by
    intro k'; funext u v; exact pairD'_eq m rec _ l u v
  rw [bor_eq, bnot_eq, band_eq, bnot_eq, allFinal'_eq]
  cases k with
  | zero => rfl
  | succ k =>
    show (!P l (k + 1) || (!allFinal l && pairsAll' (pairD' m rec k l) l)) = _
    rw [pairsAll'_eq, h1]
    rfl

def dfs' (m : Bool) (P : List ℕ → ℕ → Bool) (leaf : ℕ → List ℕ → Bool) (f : ℕ) :
    ℕ → List ℕ → Bool :=
  @Nat.rec (fun _ => ℕ → List ℕ → Bool) leaf (fun _ ih => node' m P ih) f

theorem dfs'_eq (m : Bool) (P : List ℕ → ℕ → Bool) (leaf : ℕ → List ℕ → Bool) (f : ℕ) :
    dfs' m P leaf f = dfsG m P leaf f := by
  induction f with
  | zero => rfl
  | succ f ih =>
    show node' m P (dfs' m P leaf f) = node m P (dfsG m P leaf f)
    rw [ih, node'_eq]

theorem dfs'_good {m : Bool} {P : List ℕ → ℕ → Bool} {leaf : ℕ → List ℕ → Bool}
    (hP : PruneOK m P) (hleaf : Good m leaf) (f : ℕ) : Good m (dfs' m P leaf f) := by
  rw [dfs'_eq]
  exact dfsG_sound hP hleaf f

/-- a chunk theorem `dfs' m P (fun _ _ => false) f k l = true` closes the cube `(k, l)`. -/
theorem cube_good {m : Bool} {P : List ℕ → ℕ → Bool} (hP : PruneOK m P) (f k : ℕ) (l : List ℕ)
    (h : dfs' m P (fun _ _ => false) f k l = true) : CubeGood m (k, l) :=
  fun hnd => dfs'_good hP (good_false m) f k l hnd h

/-- cut states are stored in a `Tree` with key `k :: l`; a chunk theorem is
`tall (cubeRun m P) T = true` for a subtree `T`. -/
noncomputable def cubeRun (m : Bool) (P : List ℕ → ℕ → Bool) (key : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false
    (fun k l _ => dfs' m P (fun _ _ => false) (Nat.succ k) k l) key

noncomputable def cubeLeaf (T : Tree) (k : ℕ) (l : List ℕ) : Bool := has' T (k :: l)

theorem cubeLeaf_good {m : Bool} {P : List ℕ → ℕ → Bool} (hP : PruneOK m P) {T : Tree}
    (h : tall (cubeRun m P) T = true) : Good m (cubeLeaf T) := by
  intro k l hnd hh
  have h1 : thas T (k :: l) = true := by rw [← has'_eq]; exact hh
  have h2 : cubeRun m P (k :: l) = true := thas_all _ T _ h h1
  exact cube_good hP (Nat.succ k) k l h2 hnd

/-- final assembly: cubes in `T` (all closed by chunk theorems), top of the search by `d` levels. -/
theorem dfs_top {m : Bool} {P : List ℕ → ℕ → Bool} (hP : PruneOK m P) {T : Tree}
    (hT : tall (cubeRun m P) T = true) (d n : ℕ)
    (h : subsAll base10 (startD (dfs' m P (cubeLeaf T) d) n) = true) : NoStart m n :=
  startD_sound (dfs'_good hP (cubeLeaf_good hP hT) d) h

theorem search_sound (n : ℕ) (hc : NoStart true n) :
    ¬ ∃ t : List (BitVec 24), let B : List (BitVec 24) := 0 :: 16777215 :: [5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968, 5689661];
      t.length ≤ n ∧ (4095 : BitVec 24) ∈ t ∧ ∀ (j : ℕ) (hj : j < t.length),
        (∀ d ∈ B ++ t.take j, ¬ ((t[j] &&& 4095) &&& ~~~d = 0 ∧ (d &&& ~~~t[j]) &&& 16773120 = 0)) ∧
        ∃ u ∈ B ++ t.take j, ∃ v ∈ B ++ t.take j, t[j] = u &&& v ∨ t[j] = u ||| v :=
  search_soundH n hc.toH

-- fuel DFS with history dominance (the history `h` lists every word produced on the path)

def GoodH (m : Bool) (rec : ℕ → List ℕ → List ℕ → Bool) : Prop :=
  ∀ (k : ℕ) (h l : List ℕ), l.Nodup → (∀ x ∈ l, x ∈ base12 ∨ x ∈ h) → rec k h l = true →
    ¬ ReachH m h.toFinset l.toFinset k

def opH (m : Bool) (rec : ℕ → List ℕ → List ℕ → Bool) (k : ℕ) (h l : List ℕ)
    (u ru v rv ro w : ℕ) : Bool :=
  blkAny m w base12 || blkAny m w h ||
    opD2 (fun k' l' => rec k' (w :: h) l') k l u ru v rv w (Nat.lor (rectW w) ro)

def pairH (m : Bool) (rec : ℕ → List ℕ → List ℕ → Bool) (k : ℕ) (h l : List ℕ) (u v : ℕ) : Bool :=
  opH m rec k h l u (rectW u) v (rectW v) (orEx u v l) (Nat.land u v) &&
  opH m rec k h l u (rectW u) v (rectW v) (orEx u v l) (Nat.lor u v)

def nodeH (m : Bool) (P : List ℕ → ℕ → Bool) (rec : ℕ → List ℕ → List ℕ → Bool) (k : ℕ)
    (h l : List ℕ) : Bool :=
  !(P l k) || (!(allFinal l) && (Nat.beq k 0 || pairsAll (pairH m rec (Nat.pred k) h l) l))

def dfsH (m : Bool) (P : List ℕ → ℕ → Bool) (leaf : ℕ → List ℕ → List ℕ → Bool) :
    ℕ → ℕ → List ℕ → List ℕ → Bool
  | 0 => leaf
  | f + 1 => nodeH m P (dfsH m P leaf f)

theorem pairH_sound {m : Bool} {rec : ℕ → List ℕ → List ℕ → Bool} {k : ℕ} {h l : List ℕ} {u v : ℕ}
    (hrec : GoodH m rec) (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ base12 ∨ x ∈ h)
    (hp : pairH m rec k h l u v = true)
    (ka kb : Bool) (w : ℕ) (hw : w = u &&& v ∨ w = u ||| v)
    (hH : ∀ d ∈ h, blk m w d = false) (hb : ∀ d ∈ base12, blk m w d = false) :
    ¬ ReachH m (insert w h.toFinset) (insert w (l.toFinset.filter
      (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k := by
  intro hR
  simp only [pairH, Bool.and_eq_true] at hp
  have hop : opH m rec k h l u (rectW u) v (rectW v) (orEx u v l) w = true := by
    rcases hw with rfl | rfl
    · exact hp.1
    · exact hp.2
  simp only [opH, blkAny_false m w base12 hb, blkAny_false m w h hH, Bool.false_or] at hop
  have hwl : w ∉ l := fun hm => by
    have : blk m w w = false := by
      rcases hsub w hm with h1 | h1
      · exact hb w h1
      · exact hH w h1
    rw [blk_refl] at this
    exact Bool.noConfusion this
  have h1 := op_core (m := m) hnd hwl ka kb hop hR.toReach
  have hsub' : ∀ x ∈ w :: l.filter (remF ka kb u v), x ∈ base12 ∨ x ∈ w :: h := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inr List.mem_cons_self
    · rcases hsub x (List.mem_filter.mp hx).1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (List.mem_cons_of_mem _ h2)
  have h2 := hrec k (w :: h) _ (child_nodup hnd hwl ka kb u v) hsub' h1
  rw [child_toFinset, List.toFinset_cons] at h2
  exact h2 hR

theorem nodeH_sound {m : Bool} {P : List ℕ → ℕ → Bool} {rec : ℕ → List ℕ → List ℕ → Bool}
    (hP : PruneOK m P) (hrec : GoodH m rec) : GoodH m (nodeH m P rec) := by
  intro k h l hnd hsub hh hR
  simp only [nodeH, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hh
  rcases hh with hh | ⟨hf, hh⟩
  · rw [hP l k hnd hR.toReach] at hh; exact Bool.noConfusion hh
  · rcases hh with hh | hp
    · have hk : k = 0 := Nat.eq_of_beq_eq_true hh
      subst hk
      exact notFinal hf hR.toReach.zero
    · cases k with
      | zero => exact notFinal hf hR.toReach.zero
      | succ k =>
        rcases hR.inv' k rfl with he | ⟨u, v, w, ka, kb, hu, hv, hw, hH, hd, hb, hR'⟩
        · exact notFinal hf he
        · have hH' : ∀ d ∈ h, blk m w d = false := fun d hdm => hH d (List.mem_toFinset.mpr hdm)
          have hu' := List.mem_toFinset.mp hu
          have hv' := List.mem_toFinset.mp hv
          have huv : u ≠ v := by
            rintro rfl
            have hwu : w = u := by
              rcases hw with hw | hw
              · rw [hw, Nat.and_self]
              · rw [hw, Nat.or_self]
            have := hd u hu
            rw [hwu, blk_refl] at this
            exact Bool.noConfusion this
          rcases pairsAll_mem _ _ hp u hu' v hv' huv with h1 | h1
          · exact pairH_sound hrec hnd hsub h1 ka kb w hw hH' hb hR'
          · have hw2 : w = v &&& u ∨ w = v ||| u := by
              rw [Nat.and_comm v u, Nat.or_comm v u]; exact hw
            have hfe : (l.toFinset.filter (fun x => (kb = true ∨ x ≠ v) ∧ (ka = true ∨ x ≠ u))) =
                (l.toFinset.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) := by
              ext x
              simp only [Finset.mem_filter]
              tauto
            have := pairH_sound hrec hnd hsub h1 kb ka w hw2 hH' hb
            rw [hfe] at this
            exact this hR'

/-- generic soundness of the DFS with history. -/
theorem dfsH_sound {m : Bool} {P : List ℕ → ℕ → Bool} {leaf : ℕ → List ℕ → List ℕ → Bool}
    (hP : PruneOK m P) (hleaf : GoodH m leaf) : ∀ f : ℕ, GoodH m (dfsH m P leaf f) := by
  intro f
  induction f with
  | zero => exact hleaf
  | succ f ih => exact nodeH_sound hP ih

def opH' (m : Bool) (rec : ℕ → List ℕ → List ℕ → Bool) (k : ℕ) (h l : List ℕ)
    (u ru v rv ro w : ℕ) : Bool :=
  bor (bor (blkAny' m w base12) (blkAny' m w h))
    (opD2' (fun k' l' => rec k' (w :: h) l') k l u ru v rv w (Nat.lor (rectW' w) ro))

theorem opH'_eq (m : Bool) (rec : ℕ → List ℕ → List ℕ → Bool) (k : ℕ) (h l : List ℕ)
    (u ru v rv ro w : ℕ) : opH' m rec k h l u ru v rv ro w = opH m rec k h l u ru v rv ro w := by
  unfold opH' opH
  simp only [bor_eq, blkAny'_eq, opD2'_eq, rectW'_eq]

def pairH' (m : Bool) (rec : ℕ → List ℕ → List ℕ → Bool) (k : ℕ) (h l : List ℕ) (u v : ℕ) : Bool :=
  band (opH' m rec k h l u (rectW' u) v (rectW' v) (orEx' u v l) (Nat.land u v))
    (opH' m rec k h l u (rectW' u) v (rectW' v) (orEx' u v l) (Nat.lor u v))

theorem pairH'_eq (m : Bool) (rec : ℕ → List ℕ → List ℕ → Bool) (k : ℕ) (h l : List ℕ) (u v : ℕ) :
    pairH' m rec k h l u v = pairH m rec k h l u v := by
  unfold pairH' pairH
  simp only [band_eq, opH'_eq, rectW'_eq, orEx'_eq]

def nodeH' (m : Bool) (P : List ℕ → ℕ → Bool) (rec : ℕ → List ℕ → List ℕ → Bool) (k : ℕ)
    (h l : List ℕ) : Bool :=
  bor (bnot (P l k)) (band (bnot (allFinal' l))
    (@Nat.rec (fun _ => Bool) true (fun k' _ => pairsAll' (pairH' m rec k' h l) l) k))

theorem nodeH'_eq (m : Bool) (P : List ℕ → ℕ → Bool) (rec : ℕ → List ℕ → List ℕ → Bool) :
    nodeH' m P rec = nodeH m P rec := by
  funext k h l
  unfold nodeH' nodeH
  have h1 : ∀ k', pairH' m rec k' h l = pairH m rec k' h l := by
    intro k'; funext u v; exact pairH'_eq m rec _ h l u v
  rw [bor_eq, bnot_eq, band_eq, bnot_eq, allFinal'_eq]
  cases k with
  | zero => rfl
  | succ k =>
    show (!P l (k + 1) || (!allFinal l && pairsAll' (pairH' m rec k h l) l)) = _
    rw [pairsAll'_eq, h1]
    rfl

def dfsH' (m : Bool) (P : List ℕ → ℕ → Bool) (leaf : ℕ → List ℕ → List ℕ → Bool) (f : ℕ) :
    ℕ → List ℕ → List ℕ → Bool :=
  @Nat.rec (fun _ => ℕ → List ℕ → List ℕ → Bool) leaf (fun _ ih => nodeH' m P ih) f

theorem dfsH'_good {m : Bool} {P : List ℕ → ℕ → Bool} {leaf : ℕ → List ℕ → List ℕ → Bool}
    (hP : PruneOK m P) (hleaf : GoodH m leaf) (f : ℕ) : GoodH m (dfsH' m P leaf f) := by
  have : dfsH' m P leaf f = dfsH m P leaf f := by
    induction f with
    | zero => rfl
    | succ f ih =>
      show nodeH' m P (dfsH' m P leaf f) = nodeH m P (dfsH m P leaf f)
      rw [ih, nodeH'_eq]
  rw [this]
  exact dfsH_sound hP hleaf f

/-- cubes with history: key `k :: |h| :: h ++ l`. -/
noncomputable def cubeRunH (m : Bool) (P : List ℕ → ℕ → Bool) (key : List ℕ) : Bool :=
  @List.rec ℕ (fun _ => Bool) false (fun k t _ =>
    @List.rec ℕ (fun _ => Bool) false (fun nh rest _ =>
      forceL (rest.take nh) (fun h => forceL (rest.drop nh) (fun l =>
        dfsH' m P (fun _ _ _ => false) (Nat.succ k) k h l))) t) key

noncomputable def cubeLeafH (T : Tree) (k : ℕ) (h l : List ℕ) : Bool :=
  has' T (k :: len' h :: h ++ l)

theorem cubeLeafH_good {m : Bool} {P : List ℕ → ℕ → Bool} (hP : PruneOK m P) {T : Tree}
    (hT : tall (cubeRunH m P) T = true) : GoodH m (cubeLeafH T) := by
  intro k h l hnd hsub hh
  have h1 : thas T (k :: len' h :: h ++ l) = true := by rw [← has'_eq]; exact hh
  have h2 : cubeRunH m P (k :: len' h :: h ++ l) = true := thas_all _ T _ hT h1
  have h3 : dfsH' m P (fun _ _ _ => false) (Nat.succ k) k h l = true := by
    have e : cubeRunH m P (k :: len' h :: h ++ l) =
        forceL ((h ++ l).take (len' h)) (fun h' => forceL ((h ++ l).drop (len' h)) (fun l' =>
          dfsH' m P (fun _ _ _ => false) (Nat.succ k) k h' l')) := rfl
    rw [e, forceL_eq, forceL_eq, len'_eq, List.take_left, List.drop_left] at h2
    exact h2
  exact dfsH'_good hP (fun _ _ _ _ _ hf => Bool.noConfusion hf) (Nat.succ k) k h l hnd hsub h3

def startH (rec : ℕ → List ℕ → List ℕ → Bool) (n : ℕ) (s : List ℕ) : Bool :=
  Nat.blt (Nat.succ n) s.length || !(covR (orR s)) || rec n [] s

/-- final assembly of the DFS with history. -/
theorem dfsH_top {m : Bool} {P : List ℕ → ℕ → Bool} (hP : PruneOK m P) {T : Tree}
    (hT : tall (cubeRunH m P) T = true) (d n : ℕ)
    (h : subsAll base10 (startH (dfsH' m P (cubeLeafH T) d) n) = true) : NoStartH m n := by
  intro L hL
  have hs : (base10.filter (fun x => decide (x ∈ L))).Sublist base10 := List.filter_sublist
  have he : (base10.filter (fun x => decide (x ∈ L))).toFinset = L := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hL x h, h⟩⟩
  have hnd : (base10.filter (fun x => decide (x ∈ L))).Nodup := List.Nodup.sublist hs (by decide)
  have h1 := subsAll_sub base10 _ h _ hs
  rw [← he]
  intro hR
  simp only [startH, Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with (h1 | h1) | h1
  · have h2 : n + 1 < (base10.filter (fun x => decide (x ∈ L))).length := by
      simpa [Nat.blt_eq] using h1
    have h3 := hR.toReach.card
    rw [List.toFinset_card_of_nodup hnd] at h3
    omega
  · exact cover_sound h1 hR.toReach
  · refine dfsH'_good hP (cubeLeafH_good hP hT) d n [] _ hnd ?_ h1 (by simpa using hR)
    intro x hx
    exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hs.subset hx)))

-- ===== rectangle test for tight states (Karchmer-Wigderson partition of a read-once formula) =====

theorem ite_p {c : Prop} [Decidable c] (a b : ℕ) (h : c) : (if c then a else b) = a := by
  split
  · rfl
  · contradiction

theorem ite_n {c : Prop} [Decidable c] (a b : ℕ) (h : ¬ c) : (if c then a else b) = b := by
  split
  · contradiction
  · rfl

theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

/-- one backward step of the Karchmer-Wigderson partition: the cells owned by the gate `w` are
handed to its two inputs `u`, `v` according to `c`. -/
theorem kw_step (D D' : Finset ℕ) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, e < 12 → 12 ≤ i →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', e < 12 → e' < 12 → 12 ≤ i → 12 ≤ i' → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, e < 12 → 12 ≤ i →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', e < 12 → e' < 12 → 12 ≤ i → 12 ≤ i' → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, e < 12 → 12 ≤ i → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_p _ _ (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_n _ _ (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_p _ _ (h3), ite_p _ _ (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_n _ _ (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_n _ _ (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_n _ _ h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_n _ _ h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_n _ _ (h3n)]
        exact h3

theorem size_lb2 (D : Finset ℕ) (u v : ℕ) (ka kb : Bool) :
    D.card ≤ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))).card +
      (cond ka 0 1 + cond kb 0 1) := by
  have hsub : D ⊆ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ∪
      ((cond ka ∅ {u}) ∪ (cond kb ∅ {v})) := by
    intro x hx
    by_cases h1 : x = u <;> by_cases h2 : x = v <;> cases ka <;> cases kb <;> simp_all
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))
    ((cond ka ∅ {u}) ∪ (cond kb ∅ {v}))
  have h3 := Finset.card_union_le (cond ka (∅ : Finset ℕ) {u}) (cond kb ∅ {v})
  have h4 : (cond ka (∅ : Finset ℕ) {u}).card = cond ka 0 1 := by cases ka <;> simp
  have h5 : (cond kb (∅ : Finset ℕ) {v}).card = cond kb 0 1 := by cases kb <;> simp
  omega

theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

/-- **Karchmer-Wigderson partition.**  In a tight state (`|D| = k + 1`: every live word is read
exactly once, the rest of the computation is a read-once formula over `D`) every grid cell
(edge row `e < 12`, independent row `i ≥ 12`) has an owner `f e i ∈ D` with `e ∈ E(owner)`,
`i ∉ I(owner)`, and the cells of one owner form a combinatorial rectangle. -/
theorem Reach.kw {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) (ht : D.card = k + 1) :
    ∃ f : ℕ → ℕ → ℕ,
      (∀ e i, e < 12 → 12 ≤ i →
        f e i ∈ D ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
      (∀ e i e' i', e < 12 → e' < 12 → 12 ≤ i → 12 ≤ i' → f e i = f e' i' → f e i' = f e i) := by
  induction h with
  | done k =>
    refine ⟨fun _ _ => 4095, ?_, ?_⟩
    · intro e i he hi
      refine ⟨by simp, ?_, ?_⟩
      · rw [tb4095]; simpa using he
      · rw [tb4095]; simpa using hi
    · intros; rfl
  | step D k u v w ka kb hu hv hw hd hb hR ih =>
    have hwD : w ∉ D := fun hm => by
      have := hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwu : w ≠ u := fun h => hwD (h ▸ hu)
    have hwv : w ≠ v := fun h => hwD (h ▸ hv)
    have huv : u ≠ v := by
      rintro rfl
      rcases hw with hw | hw
      · rw [Nat.and_self] at hw; exact hwu hw
      · rw [Nat.or_self] at hw; exact hwu hw
    have hwF : w ∉ D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwD (Finset.mem_of_mem_filter _ hm)
    have hkk : ka = false ∧ kb = false := by
      have h1 := hR.card
      rw [Finset.card_insert_of_notMem hwF] at h1
      have h2 := size_lb2 D u v ka kb
      generalize (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))).card = c at h1 h2
      cases ka <;> cases kb
      · exact ⟨rfl, rfl⟩
      · exfalso
        have h2' : D.card ≤ c + (1 + 0) := h2
        omega
      · exfalso
        have h2' : D.card ≤ c + (0 + 1) := h2
        omega
      · exfalso
        have h2' : D.card ≤ c + (0 + 0) := h2
        omega
    obtain ⟨rfl, rfl⟩ := hkk
    have h1 := hR.card
    rw [Finset.card_insert_of_notMem hwF] at h1
    have h2 : D.card ≤ (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))).card + (1 + 1) :=
      size_lb2 D u v false false
    have hc : (insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v)))).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hwF]; omega
    obtain ⟨f, hf, hr⟩ := ih hc
    have huD : u ∉ insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hwu h.symm
      · have := (Finset.mem_filter.mp h).2.1
        simp at this
    have hvD : v ∉ insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hwv h.symm
      · have := (Finset.mem_filter.mp h).2.2
        simp at this
    have hsub : ∀ x ∈ insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))), x ≠ w → x ∈ D := by
      intro x hx hxw
      rcases Finset.mem_insert.mp hx with h | h
      · exact absurd h hxw
      · exact Finset.mem_of_mem_filter _ h
    rcases hw with rfl | rfl
    · exact kw_step D _ u v (u &&& v) (fun _ i => !(u.testBit i)) f hu hv huv huD hvD hsub hf hr
        (fun e i h1 h2 h3 => and_cu u v e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv u v e i h1 h2 h3)
        (fun e i e' i' h => h.symm)
    · exact kw_step D _ u v (u ||| v) (fun e _ => u.testBit e) f hu hv huv huD hvD hsub hf hr
        (fun e i h1 h2 h3 => or_cu u v e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv u v e i h1 h2 h3)
        (fun e i e' i' _ => rfl)

-- bit lemmas for the raw operations

theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q = Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q

theorem full_tb (q : ℕ) : full.testBit q = decide (q < 144) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q, h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q, a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land, Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

-- the rectangular hull of a 144-bit cell set, by shifts and masks only

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j, j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j, hj, hp⟩ := hx q h
    exact ⟨j, by omega, hp⟩
  · obtain ⟨j, hj, hp⟩ := hx _ h
    refine ⟨j + s, by omega, ?_⟩
    rw [Nat.mul_add, Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j, j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hs, h⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx q h
    exact ⟨j, by omega, hq, hp⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s, by omega, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [e]; exact hp

/-- bit `12 * e` for every row `e < 12`. -/
def rowM : ℕ := 5445847423328601499764522166702896582657

theorem rowM_tb (q : ℕ) (h : rowM.testBit q = true) : q < 144 ∧ q % 12 = 0 := by
  have hlt : q < 144 := by
    by_contra hq
    have h0 : rowM.testBit q = false := by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144 := by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ, q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt, hall q hlt h⟩

/-- bit `12 * e` is set when row `e` of `p` is not empty. -/
def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

/-- the union of the rows of `p` (12 bits). -/
def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

/-- rectangular hull (rows of `p` times columns of `p`) of the cells of `p` below 144. -/
def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j, j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land, Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j, j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land, Bool.and_eq_true, tb4095, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q, p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land, Bool.and_eq_true] at h
  obtain ⟨hR, hC⟩ := h
  have r0 : ∀ q, (rowsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j, hj, hjq, hr⟩ := r4 q hR
  obtain ⟨⟨hb, hm⟩, i, hi, hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q, (colsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j', hj', hjq', hc⟩ := c4 q hC
  obtain ⟨hlt, e', he', hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega, i, e', hi, by omega, hpi, hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q, (Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land, full_tb, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1, i, e', hi, he, ha, hb⟩ := hullC_spec _ hp q h
  rw [tb_land, Bool.and_eq_true] at ha hb
  exact ⟨h1, i, e', hi, he, ha.1, hb.1⟩

-- the test on the list of available cell sets (one 144-bit mask per live word)

/-- cells lying in at least two of the masks (`o`: union so far, `t`: result so far). -/
def tw : List ℕ → ℕ → ℕ → ℕ
  | [], _, t => t
  | a :: l, o, t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

/-- hull of the private cells of `a` (`t`: the cells covered at least twice). -/
def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

/-- every private hull lies inside its own mask and the hulls are pairwise disjoint. -/
def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

/-- one propagation round. -/
def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def orL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (orL l)

/-- remove the other words' private hulls (`nO`: complement of the union of all hulls). -/
def upd (t nO a : ℕ) : ℕ := Nat.lor (Nat.land a nO) (priv t a)

def nextAv (as : List ℕ) : List ℕ :=
  as.map (upd (tw as 0 0) (Nat.xor (orL (as.map (priv (tw as 0 0)))) full))

/-- `n` propagation rounds, with a cover test after every removal. -/
def avOK : ℕ → List ℕ → Bool
  | 0, _ => true
  | n + 1, as => avOK1 as && (covR (orL (nextAv as)) && avOK n (nextAv as))

/-- one-round rectangle test of a state. -/
def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

/-- `n`-round rectangle test of a state. -/
def rectOK (n : ℕ) (l : List ℕ) : Bool := avOK n (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

/-- a partition of the 144 cells into rectangles, one inside each mask. -/
structure Part (zs : List ((ℕ → Prop) × ℕ)) : Prop where
  rect : ∀ z ∈ zs, IsRect z.1
  bnd : ∀ z ∈ zs, ∀ q, z.1 q → q < 144
  disj : zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)
  cov : ∀ q, q < 144 → ∃ z ∈ zs, z.1 q
  sub : ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ), (tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as, a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h, fun _ a ha => by simp at ha, List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1, h2, h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor, Bool.or_eq_false_iff, tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor, ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor, hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z', hz', hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q, (priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) →
    (∀ q, acc.testBit q = true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc = true := by
  intro zs
  induction zs with
  | nil => intros; rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz := hh z List.mem_cons_self
    have e1 := land_sub _ _ (fun q hq => hs z List.mem_cons_self q (hz q hq))
    have e2 := land_disj acc (priv t z.2) (fun q h1 h2 => ha q h1 z List.mem_cons_self (hz q h2))
    have e3 := ih (Nat.lor acc (priv t z.2)) (fun z' hz' => hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q => by
        rw [tb_lor, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1, e2, e3, Nat.beq_refl]
    rfl

theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd) = true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq => by simp at hq)

theorem orL_tb (q : ℕ) : ∀ as : List ℕ, (orL as).testBit q = true →
    ∃ a ∈ as, a.testBit q = true := by
  intro as
  induction as with
  | nil => intro h; simp [orL] at h
  | cons a l ih =>
    intro h
    have h' : (Nat.lor a (orL l)).testBit q = true := h
    rw [tb_lor, Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact ⟨a, List.mem_cons_self, h'⟩
    · obtain ⟨b, hb, hbq⟩ := ih h'
      exact ⟨b, List.mem_cons_of_mem _ hb, hbq⟩

theorem orL_tb' (q : ℕ) : ∀ as : List ℕ, ∀ a ∈ as, a.testBit q = true →
    (orL as).testBit q = true := by
  intro as
  induction as with
  | nil => intro a ha; simp at ha
  | cons b l ih =>
    intro a ha h
    show (Nat.lor b (orL l)).testBit q = true
    rw [tb_lor]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [h]; rfl
    · rw [ih a ha h]; simp

/-- the partition survives a propagation round. -/
theorem Part.next {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    ∃ zs' : List ((ℕ → Prop) × ℕ), zs'.map Prod.snd = nextAv (zs.map Prod.snd) ∧ Part zs' := by
  refine ⟨zs.map (fun z => (z.1, upd (tw (zs.map Prod.snd) 0 0)
    (Nat.xor (orL ((zs.map Prod.snd).map (priv (tw (zs.map Prod.snd) 0 0)))) full) z.2)), ?_, ?_⟩
  · unfold nextAv
    simp only [List.map_map]
    rfl
  · constructor
    · intro z hz
      obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp hz
      exact hP.rect z0 hz0
    · intro z hz
      obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp hz
      exact hP.bnd z0 hz0
    · rw [List.pairwise_map]
      exact hP.disj
    · intro q hq
      obtain ⟨z, hz, hzq⟩ := hP.cov q hq
      exact ⟨_, List.mem_map.mpr ⟨z, hz, rfl⟩, hzq⟩
    · intro z hz q hzq
      obtain ⟨z0, hz0, rfl⟩ := List.mem_map.mp hz
      have hzq0 : z0.1 q := hzq
      show (upd (tw (zs.map Prod.snd) 0 0)
        (Nat.xor (orL ((zs.map Prod.snd).map (priv (tw (zs.map Prod.snd) 0 0)))) full)
        z0.2).testBit q = true
      unfold upd
      rw [tb_lor, tb_land, tb_xor, full_tb, hP.sub z0 hz0 q hzq0]
      have hq := hP.bnd z0 hz0 q hzq0
      cases hO : (orL ((zs.map Prod.snd).map (priv (tw (zs.map Prod.snd) 0 0)))).testBit q
      · simp [hq]
      · obtain ⟨a, ha, haq⟩ := orL_tb q _ hO
        rw [List.map_map] at ha
        obtain ⟨z1, hz1, rfl⟩ := List.mem_map.mp ha
        have h1 : z1.1 q := priv_in hP z1 hz1 q haq
        have hzz : z1 = z0 := by
          by_contra hne
          exact pw_forall (fun a b h q h1 h2 => h q h2 h1) zs hP.disj z1 hz1 z0 hz0 hne q h1 hzq0
        rw [hzz] at haq
        have haq' : (priv (tw (zs.map Prod.snd) 0 0) z0.2).testBit q = true := haq
        rw [haq']
        simp

theorem Part.covR {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    covR (orL (zs.map Prod.snd)) = true := by
  apply covR_of
  intro q hq
  obtain ⟨z, hz, hzq⟩ := hP.cov q hq
  exact orL_tb' q _ z.2 (List.mem_map.mpr ⟨z, hz, rfl⟩) (hP.sub z hz q hzq)

theorem avOK_sound : ∀ (n : ℕ) (zs : List ((ℕ → Prop) × ℕ)), Part zs →
    avOK n (zs.map Prod.snd) = true := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro zs hP
    obtain ⟨zs', he, hP'⟩ := hP.next
    show (avOK1 (zs.map Prod.snd) && (covR (orL (nextAv (zs.map Prod.snd))) &&
      avOK n (nextAv (zs.map Prod.snd)))) = true
    rw [avOK1_sound hP, ← he, ih zs' hP', hP'.covR]
    rfl

/-- a tight reachable state has a rectangle partition inside the rectangles of its words. -/
theorem part_of_reach {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hlen : l.length = k + 1)
    (hR : Reach m l.toFinset k) :
    ∃ zs : List ((ℕ → Prop) × ℕ), zs.map Prod.snd = l.map rectW ∧ Part zs := by
  have hc : l.toFinset.card = k + 1 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  obtain ⟨f, hf, hr⟩ := hR.kw hc
  refine ⟨l.map (fun w => ((fun q => q < 144 ∧ f (q / 12) (12 + q % 12) = w), rectW w)), ?_, ?_⟩
  · rw [List.map_map]
    rfl
  · constructor
    · intro z hz
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      intro e i e' i' he hi he' hi' h1 h2
      have h1' : f ((12 * e + i) / 12) (12 + (12 * e + i) % 12) = w := h1.2
      have h2' : f ((12 * e' + i') / 12) (12 + (12 * e' + i') % 12) = w := h2.2
      have e1 : (12 * e + i) / 12 = e := by omega
      have e2 : (12 * e + i) % 12 = i := by omega
      have e3 : (12 * e' + i') / 12 = e' := by omega
      have e4 : (12 * e' + i') % 12 = i' := by omega
      have e5 : (12 * e + i') / 12 = e := by omega
      have e6 : (12 * e + i') % 12 = i' := by omega
      rw [e1, e2] at h1'
      rw [e3, e4] at h2'
      show 12 * e + i' < 144 ∧ f ((12 * e + i') / 12) (12 + (12 * e + i') % 12) = w
      rw [e5, e6]
      exact ⟨by omega, (hr e (12 + i) e' (12 + i') he he' (by omega) (by omega)
        (h1'.trans h2'.symm)).trans h1'⟩
    · intro z hz q hq
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) hnd
    · intro q hq
      have h := (hf (q / 12) (12 + q % 12) (by omega) (by omega)).1
      exact ⟨_, List.mem_map.mpr ⟨_, List.mem_toFinset.mp h, rfl⟩, hq, rfl⟩
    · intro z hz q hq
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      have hq1 : q < 144 := hq.1
      have hq2 : f (q / 12) (12 + q % 12) = w := hq.2
      have h := hf (q / 12) (12 + q % 12) (by omega) (by omega)
      rw [hq2] at h
      have h3 := rectW_tb w (q / 12) (q % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h.2.1 h.2.2
      rwa [Nat.div_add_mod] at h3

theorem rectOK1_sound {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hlen : l.length = k + 1)
    (hR : Reach m l.toFinset k) : rectOK1 l = true := by
  obtain ⟨zs, he, hP⟩ := part_of_reach hnd hlen hR
  unfold rectOK1
  rw [← he]
  exact avOK1_sound hP

theorem rectOK_sound {m : Bool} {l : List ℕ} {k : ℕ} (n : ℕ) (hnd : l.Nodup)
    (hlen : l.length = k + 1) (hR : Reach m l.toFinset k) : rectOK n l = true := by
  obtain ⟨zs, he, hP⟩ := part_of_reach hnd hlen hR
  unfold rectOK
  rw [← he]
  exact avOK_sound n zs hP

/-- prune test: a tight state must pass the one-round rectangle test. -/
def rectP1 (l : List ℕ) (k : ℕ) : Bool := !(Nat.beq l.length (Nat.succ k)) || rectOK1 l

/-- prune test: a tight state must pass the `n`-round rectangle test. -/
def rectP (n : ℕ) (l : List ℕ) (k : ℕ) : Bool := !(Nat.beq l.length (Nat.succ k)) || rectOK n l

theorem rectP1_ok (m : Bool) : PruneOK m rectP1 := by
  intro l k hnd hR
  unfold rectP1
  cases h : Nat.beq l.length (Nat.succ k)
  · rfl
  · rw [rectOK1_sound hnd (Nat.eq_of_beq_eq_true h) hR]
    rfl

theorem rectP_ok (m : Bool) (n : ℕ) : PruneOK m (rectP n) := by
  intro l k hnd hR
  unfold rectP
  cases h : Nat.beq l.length (Nat.succ k)
  · rfl
  · rw [rectOK_sound n hnd (Nat.eq_of_beq_eq_true h) hR]
    rfl

-- kernel-friendly form of the one-round test (raw recursors, as the primed functions above)

def tw' (l : List ℕ) : ℕ → ℕ → ℕ :=
  @List.rec ℕ (fun _ => ℕ → ℕ → ℕ) (fun _ t => t)
    (fun a _ ih o t => ih (Nat.lor o a) (Nat.lor t (Nat.land o a))) l

theorem tw'_eq (l : List ℕ) : ∀ o t : ℕ, tw' l o t = tw l o t := by
  induction l with
  | nil => intro o t; rfl
  | cons a l ih =>
    intro o t
    show tw' l (Nat.lor o a) (Nat.lor t (Nat.land o a)) = tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))
    exact ih _ _

def hullsOK' (t : ℕ) (l : List ℕ) : ℕ → Bool :=
  @List.rec ℕ (fun _ => ℕ → Bool) (fun _ => true)
    (fun a _ ih acc => (fun h => band (Nat.beq (Nat.land h a) h)
      (band (Nat.beq (Nat.land acc h) 0) (ih (Nat.lor acc h)))) (priv t a)) l

theorem hullsOK'_eq (t : ℕ) (l : List ℕ) : ∀ acc : ℕ, hullsOK' t l acc = hullsOK t l acc := by
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
    intro acc
    show band (Nat.beq (Nat.land (priv t a) a) (priv t a))
      (band (Nat.beq (Nat.land acc (priv t a)) 0) (hullsOK' t l (Nat.lor acc (priv t a)))) =
      (Nat.beq (Nat.land (priv t a) a) (priv t a) &&
        (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a))))
    rw [ih, band_eq, band_eq]

def mapW' (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun x _ ih => rectW' x :: ih) l

theorem mapW'_eq (l : List ℕ) : mapW' l = l.map rectW := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show rectW' x :: mapW' l = rectW x :: l.map rectW
    rw [ih, rectW'_eq]

/-- `rectP1` in kernel-friendly form. -/
def rectP1' (l : List ℕ) (k : ℕ) : Bool :=
  bor (bnot (Nat.beq (len' l) (Nat.succ k)))
    ((fun as => hullsOK' (tw' as 0 0) as 0) (mapW' l))

theorem rectP1'_eq (l : List ℕ) (k : ℕ) : rectP1' l k = rectP1 l k := by
  show bor (bnot (Nat.beq (len' l) (Nat.succ k))) (hullsOK' (tw' (mapW' l) 0 0) (mapW' l) 0) =
    (!(Nat.beq l.length (Nat.succ k)) || hullsOK (tw (l.map rectW) 0 0) (l.map rectW) 0)
  rw [bor_eq, bnot_eq, len'_eq, mapW'_eq, hullsOK'_eq, tw'_eq]

theorem rectP1'_ok (m : Bool) : PruneOK m rectP1' := by
  intro l k hnd hR
  rw [rectP1'_eq]
  exact rectP1_ok m l k hnd hR

-- ===== class rule (labels for words below a re-read word); K = 0 is the rectangle rule =====

/-- the cell (edge row `e`, independent row `i`) is separated by `x`. -/
def Pc (x e i : ℕ) : Prop := x.testBit e = true ∧ x.testBit i = false

def IsRect2 (S : ℕ → ℕ → Prop) : Prop := ∀ e i e' i' : ℕ, S e i → S e' i' → S e i'

theorem pc_rect (x : ℕ) : IsRect2 (Pc x) := fun _ _ _ _ h1 h2 => ⟨h1.1, h2.2⟩

/-- a structure of width `j` on the live set `D` (NOTES-search.md, section 4): owner `f` of every
cell, rectangular envelopes `env`, labels `c`, one rectangle `Pi n` per positive label. -/
structure KS (D : Finset ℕ) (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ)
    (Pi : ℕ → ℕ → ℕ → Prop) : Prop where
  own : ∀ e i, e < 12 → 12 ≤ i → f e i ∈ D ∧ env (f e i) e i
  envR : ∀ x ∈ D, IsRect2 (env x)
  envP : ∀ x ∈ D, ∀ e i, env x e i → Pc x e i
  s1 : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → c x = c y → ∀ e i, env x e i → env y e i → False
  s2 : ∀ x ∈ D, 1 ≤ c x → ∀ e i, env x e i → Pi (c x) e i
  piR : ∀ n, IsRect2 (Pi n)
  s3 : ∀ n e i, 1 ≤ n → Pi n e i → ∃ y ∈ D, 1 ≤ c y ∧ c y ≤ n ∧ Pc y e i
  lab : ∀ x ∈ D, c x ≤ j

theorem ks_done : KS {4095} 0 (fun _ _ => 4095) (fun _ e i => Pc 4095 e i) (fun _ => 0)
    (fun _ _ _ => False) := by
  constructor
  · intro e i he hi
    refine ⟨by simp, ?_, ?_⟩
    · rw [tb4095]; simpa using he
    · rw [tb4095]; simpa using hi
  · intro x _; exact pc_rect 4095
  · intro x hx e i h
    rw [Finset.mem_singleton.mp hx]; exact h
  · intro x hx y hy hxy
    exact absurd ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm) hxy
  · intro x _ h; omega
  · intro n e i e' i' h; exact h.elim
  · intro n e i _ h; exact h.elim
  · intro x _; exact le_rfl

/-- labels after `x` became label 1: positive labels move up by one. -/
def shiftL (c : ℕ → ℕ) (x y : ℕ) : ℕ := if y = x then 1 else if c y = 0 then 0 else c y + 1

theorem shiftL_self (c : ℕ → ℕ) (x : ℕ) : shiftL c x x = 1 := by
  unfold shiftL; exact ite_p _ _ rfl

theorem shiftL_ne (c : ℕ → ℕ) (x y : ℕ) (h : y ≠ x) :
    (c y = 0 ∧ shiftL c x y = 0) ∨ (1 ≤ c y ∧ shiftL c x y = c y + 1) := by
  unfold shiftL
  rw [ite_n _ _ h]
  by_cases h0 : c y = 0
  · rw [ite_p _ _ h0]; exact Or.inl ⟨h0, rfl⟩
  · rw [ite_n _ _ h0]; exact Or.inr ⟨by omega, rfl⟩

/-- `x` is re-read: it gets a new label 1, its whole rectangle as envelope and as `Pi 1`. -/
theorem KS.promote {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) (x : ℕ) (hxD : x ∈ D) :
    KS D (j + 1) f (fun y e i => (y = x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x)
      (fun n e i => (n = 1 ∧ Pc x e i) ∨ (2 ≤ n ∧ Pi (n - 1) e i)) := by
  constructor
  · intro e i he hi
    obtain ⟨h1, h2⟩ := h.own e i he hi
    refine ⟨h1, ?_⟩
    by_cases hx : f e i = x
    · exact Or.inl ⟨hx, hx ▸ h.envP _ h1 e i h2⟩
    · exact Or.inr ⟨hx, h2⟩
  · intro y hy e i e' i' h1 h2
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1⟩ <;> rcases h2 with ⟨hx', h2⟩ | ⟨hx', h2⟩
    · exact Or.inl ⟨hx, pc_rect x e i e' i' h1 h2⟩
    · exact absurd hx hx'
    · exact absurd hx' hx
    · exact Or.inr ⟨hx, h.envR y hy e i e' i' h1 h2⟩
  · intro y hy e i h1
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1⟩
    · rw [hx]; exact h1
    · exact h.envP y hy e i h1
  · intro y hy z hz hyz hc e i h1 h2
    by_cases hyx : y = x
    · have hzx : z ≠ x := fun hh => hyz (hyx.trans hh.symm)
      rw [hyx, shiftL_self] at hc
      rcases shiftL_ne c x z hzx with ⟨_, h3⟩ | ⟨_, h3⟩ <;> omega
    · by_cases hzx : z = x
      · rw [hzx, shiftL_self] at hc
        rcases shiftL_ne c x y hyx with ⟨_, h3⟩ | ⟨_, h3⟩ <;> omega
      · have hcc : c y = c z := by
          rcases shiftL_ne c x y hyx with ⟨_, h3⟩ | ⟨_, h3⟩ <;>
            rcases shiftL_ne c x z hzx with ⟨_, h4⟩ | ⟨_, h4⟩ <;> omega
        rcases h1 with ⟨hx, _⟩ | ⟨_, h1⟩
        · exact hyx hx
        · rcases h2 with ⟨hx, _⟩ | ⟨_, h2⟩
          · exact hzx hx
          · exact h.s1 y hy z hz hyz hcc e i h1 h2
  · intro y hy hc e i h1
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1⟩
    · rw [hx, shiftL_self]; exact Or.inl ⟨rfl, h1⟩
    · rcases shiftL_ne c x y hx with ⟨_, h3⟩ | ⟨h4, h3⟩
      · omega
      · rw [h3]
        refine Or.inr ⟨by omega, ?_⟩
        rw [Nat.add_sub_cancel]
        exact h.s2 y hy h4 e i h1
  · intro n e i e' i' h1 h2
    rcases h1 with ⟨hn, h1⟩ | ⟨hn, h1⟩ <;> rcases h2 with ⟨hn', h2⟩ | ⟨hn', h2⟩
    · exact Or.inl ⟨hn, pc_rect x e i e' i' h1 h2⟩
    · omega
    · omega
    · exact Or.inr ⟨hn, h.piR _ e i e' i' h1 h2⟩
  · intro n e i hn h1
    rcases h1 with ⟨hn1, h1⟩ | ⟨hn2, h1⟩
    · exact ⟨x, hxD, by rw [shiftL_self], by rw [shiftL_self]; omega, h1⟩
    · obtain ⟨y, hy, h3, h4, h5⟩ := h.s3 (n - 1) e i (by omega) h1
      by_cases hyx : y = x
      · exact ⟨y, hy, by rw [hyx, shiftL_self], by rw [hyx, shiftL_self]; omega, h5⟩
      · rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩
        · omega
        · exact ⟨y, hy, by omega, by omega, h5⟩
  · intro y hy
    have := h.lab y hy
    by_cases hyx : y = x
    · rw [hyx, shiftL_self]; omega
    · rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩ <;> omega

/-- `x` is ready to absorb cells of the gate `w`: full envelope, positive label not above `w`'s. -/
def Prom (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) : Prop :=
  (∀ e i, Pc x e i → env x e i) ∧ 1 ≤ c x ∧ (1 ≤ c w → c x ≤ c w)

theorem prom_self (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) :
    Prom (fun y e i => (y = x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x) w x := by
  refine ⟨fun e i h => Or.inl ⟨rfl, h⟩, by rw [shiftL_self], fun h => by rw [shiftL_self]; exact h⟩

theorem prom_other (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x y : ℕ) (hyx : y ≠ x) (hwx : w ≠ x)
    (h : Prom env c w y) :
    Prom (fun y e i => (y = x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x) w y := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e i hp => Or.inr ⟨hyx, h1 e i hp⟩, ?_, ?_⟩
  · rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩ <;> omega
  · intro hw
    rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩ <;>
      rcases shiftL_ne c x w hwx with ⟨_, h7⟩ | ⟨_, h7⟩ <;> omega

/-- promote the kept operands of a step. -/
theorem ks_prom {D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (hK : KS D' j f env c Pi) (u v w : ℕ) (_huw : u ≠ w) (hvw : v ≠ w)
    (huv : u ≠ v) (ka kb : Bool) (hua : u ∈ D' ↔ ka = true) (hvb : v ∈ D' ↔ kb = true) :
    ∃ (j2 : ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ) (Pi2 : ℕ → ℕ → ℕ → Prop),
      KS D' j2 f env2 c2 Pi2 ∧ j2 = j + (cond ka 1 0 + cond kb 1 0) ∧
      (u ∈ D' → Prom env2 c2 w u) ∧ (v ∈ D' → Prom env2 c2 w v) := by
  cases ka <;> cases kb
  · exact ⟨j, env, c, Pi, hK, rfl, fun h => Bool.noConfusion (hua.mp h),
      fun h => Bool.noConfusion (hvb.mp h)⟩
  · exact ⟨_, _, _, _, hK.promote v (hvb.mpr rfl), rfl, fun h => Bool.noConfusion (hua.mp h),
      fun _ => prom_self env c w v⟩
  · exact ⟨_, _, _, _, hK.promote u (hua.mpr rfl), rfl, fun _ => prom_self env c w u,
      fun h => Bool.noConfusion (hvb.mp h)⟩
  · exact ⟨_, _, _, _, (hK.promote u (hua.mpr rfl)).promote v (hvb.mpr rfl), rfl,
      fun _ => prom_other _ _ w v u huv (Ne.symm hvw) (prom_self env c w u),
      fun _ => prom_self _ _ w v⟩

/-- one backward step: the gate `w` hands its cells, envelope and label to its operands. -/
theorem KS.step {D D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D' j f env c Pi) (u v w : ℕ) (hu : u ∈ D) (hv : v ∈ D)
    (huv : u ≠ v) (hwD : w ∉ D) (hw : w ∈ D') (hD' : ∀ x ∈ D', x ≠ w → x ∈ D)
    (cc : ℕ → ℕ → Bool)
    (hcu : ∀ e i, Pc w e i → cc e i = true → Pc u e i)
    (hcv : ∀ e i, Pc w e i → cc e i = false → Pc v e i)
    (hcr : ∀ (b : Bool) (e i e' i' : ℕ), cc e i = b → cc e' i' = b → cc e i' = b)
    (hku : u ∈ D' → Prom env c w u) (hkv : v ∈ D' → Prom env c w v) :
    ∃ (f2 : ℕ → ℕ → ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ), KS D j f2 env2 c2 Pi := by
  have hc2a : ∀ x, x ∈ D' → (if x ∈ D' then c x else c w) = c x := fun x hx => ite_p _ _ hx
  have hc2b : ∀ x, x ∉ D' → (if x ∈ D' then c x else c w) = c w := fun x hx => ite_n _ _ hx
  refine ⟨fun e i => if f e i = w then cond (cc e i) u v else f e i,
    fun x e i => (x ∈ D' ∧ env x e i) ∨
      (x ∉ D' ∧ env w e i ∧ ((x = u ∧ cc e i = true) ∨ (x = v ∧ cc e i = false))),
    fun x => if x ∈ D' then c x else c w, ?_⟩
  constructor
  · intro e i he hi
    obtain ⟨h1, h2⟩ := h.own e i he hi
    show (if f e i = w then cond (cc e i) u v else f e i) ∈ D ∧
      (((if f e i = w then cond (cc e i) u v else f e i) ∈ D' ∧
        env (if f e i = w then cond (cc e i) u v else f e i) e i) ∨
      ((if f e i = w then cond (cc e i) u v else f e i) ∉ D' ∧ env w e i ∧
        (((if f e i = w then cond (cc e i) u v else f e i) = u ∧ cc e i = true) ∨
         ((if f e i = w then cond (cc e i) u v else f e i) = v ∧ cc e i = false))))
    by_cases hfw : f e i = w
    · rw [ite_p _ _ hfw]
      rw [hfw] at h2
      have hpw := h.envP w hw e i h2
      cases hcc : cc e i
      · refine ⟨hv, ?_⟩
        by_cases hvD : v ∈ D'
        · exact Or.inl ⟨hvD, (hkv hvD).1 e i (hcv e i hpw hcc)⟩
        · exact Or.inr ⟨hvD, h2, Or.inr ⟨rfl, rfl⟩⟩
      · refine ⟨hu, ?_⟩
        by_cases huD : u ∈ D'
        · exact Or.inl ⟨huD, (hku huD).1 e i (hcu e i hpw hcc)⟩
        · exact Or.inr ⟨huD, h2, Or.inl ⟨rfl, rfl⟩⟩
    · rw [ite_n _ _ hfw]
      exact ⟨hD' _ h1 hfw, Or.inl ⟨h1, h2⟩⟩
  · intro x _ e i e' i' h1 h2
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1, h1c⟩ <;> rcases h2 with ⟨hx', h2⟩ | ⟨hx', h2, h2c⟩
    · exact Or.inl ⟨hx, h.envR x hx e i e' i' h1 h2⟩
    · exact absurd hx hx'
    · exact absurd hx' hx
    · refine Or.inr ⟨hx, h.envR w hw e i e' i' h1 h2, ?_⟩
      rcases h1c with ⟨hxu, hc1⟩ | ⟨hxv, hc1⟩ <;> rcases h2c with ⟨hxu', hc2⟩ | ⟨hxv', hc2⟩
      · exact Or.inl ⟨hxu, hcr true e i e' i' hc1 hc2⟩
      · exact absurd (hxu.symm.trans hxv') huv
      · exact absurd (hxu'.symm.trans hxv) huv
      · exact Or.inr ⟨hxv, hcr false e i e' i' hc1 hc2⟩
  · intro x _ e i h1
    rcases h1 with ⟨hx, h1⟩ | ⟨_, h1, h1c⟩
    · exact h.envP x hx e i h1
    · have hpw := h.envP w hw e i h1
      rcases h1c with ⟨hxu, hc1⟩ | ⟨hxv, hc1⟩
      · rw [hxu]; exact hcu e i hpw hc1
      · rw [hxv]; exact hcv e i hpw hc1
  · intro x hx y hy hxy hc e i h1 h2
    have hxw : x ≠ w := fun hh => hwD (hh ▸ hx)
    have hyw : y ≠ w := fun hh => hwD (hh ▸ hy)
    have hc' : (if x ∈ D' then c x else c w) = (if y ∈ D' then c y else c w) := hc
    rcases h1 with ⟨hx', h1⟩ | ⟨hx', h1, h1c⟩ <;> rcases h2 with ⟨hy', h2⟩ | ⟨hy', h2, h2c⟩
    · rw [hc2a x hx', hc2a y hy'] at hc'
      exact h.s1 x hx' y hy' hxy hc' e i h1 h2
    · rw [hc2a x hx', hc2b y hy'] at hc'
      exact h.s1 x hx' w hw hxw hc' e i h1 h2
    · rw [hc2b x hx', hc2a y hy'] at hc'
      exact h.s1 w hw y hy' (Ne.symm hyw) hc' e i h1 h2
    · rcases h1c with ⟨hxu, hc1⟩ | ⟨hxv, hc1⟩ <;> rcases h2c with ⟨hyu, hc2⟩ | ⟨hyv, hc2⟩
      · exact hxy (hxu.trans hyu.symm)
      · rw [hc1] at hc2; exact Bool.noConfusion hc2
      · rw [hc1] at hc2; exact Bool.noConfusion hc2
      · exact hxy (hxv.trans hyv.symm)
  · intro x _ hc e i h1
    have hc' : 1 ≤ (if x ∈ D' then c x else c w) := hc
    show Pi (if x ∈ D' then c x else c w) e i
    rcases h1 with ⟨hx', h1⟩ | ⟨hx', h1, _⟩
    · rw [hc2a x hx'] at hc' ⊢
      exact h.s2 x hx' hc' e i h1
    · rw [hc2b x hx'] at hc' ⊢
      exact h.s2 w hw hc' e i h1
  · exact h.piR
  · intro n e i hn h1
    obtain ⟨y, hy, h3, h4, h5⟩ := h.s3 n e i hn h1
    show ∃ y ∈ D, 1 ≤ (if y ∈ D' then c y else c w) ∧ (if y ∈ D' then c y else c w) ≤ n ∧ Pc y e i
    by_cases hyw : y = w
    · rw [hyw] at h3 h4 h5
      cases hcc : cc e i
      · refine ⟨v, hv, ?_, ?_, hcv e i h5 hcc⟩
        · by_cases hvD : v ∈ D'
          · rw [hc2a v hvD]; exact (hkv hvD).2.1
          · rw [hc2b v hvD]; exact h3
        · by_cases hvD : v ∈ D'
          · rw [hc2a v hvD]; exact le_trans ((hkv hvD).2.2 h3) h4
          · rw [hc2b v hvD]; exact h4
      · refine ⟨u, hu, ?_, ?_, hcu e i h5 hcc⟩
        · by_cases huD : u ∈ D'
          · rw [hc2a u huD]; exact (hku huD).2.1
          · rw [hc2b u huD]; exact h3
        · by_cases huD : u ∈ D'
          · rw [hc2a u huD]; exact le_trans ((hku huD).2.2 h3) h4
          · rw [hc2b u huD]; exact h4
    · exact ⟨y, hD' y hy hyw, by rw [hc2a y hy]; exact h3, by rw [hc2a y hy]; exact h4, h5⟩
  · intro x _
    show (if x ∈ D' then c x else c w) ≤ j
    by_cases hx' : x ∈ D'
    · rw [hc2a x hx']; exact h.lab x hx'
    · rw [hc2b x hx']; exact h.lab w hw

theorem cond_sum (b : Bool) : (cond b 1 0 : ℕ) + cond b 0 1 = 1 := by cases b <;> rfl

/-- **Lemma A.**  A state that reaches the target in `k` steps carries a structure whose width is
at most the number of spare reads `k + 1 - |D|`. -/
theorem Reach.ks {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) :
    ∃ (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (Pi : ℕ → ℕ → ℕ → Prop),
      KS D j f env c Pi ∧ j + D.card ≤ k + 1 := by
  induction h with
  | done k => exact ⟨0, _, _, _, _, ks_done, by simp⟩
  | step D k u v w ka kb hu hv hw hd hb hR ih =>
    obtain ⟨j, f, env, c, Pi, hK, hj⟩ := ih
    have hwD : w ∉ D := fun hm => by
      have := hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwu : w ≠ u := fun h => hwD (h ▸ hu)
    have hwv : w ≠ v := fun h => hwD (h ▸ hv)
    have huv : u ≠ v := by
      rintro rfl
      rcases hw with hw | hw
      · rw [Nat.and_self] at hw; exact hwu hw
      · rw [Nat.or_self] at hw; exact hwu hw
    have hwF : w ∉ D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwD (Finset.mem_of_mem_filter _ hm)
    rw [Finset.card_insert_of_notMem hwF] at hj
    have hsz := size_lb2 D u v ka kb
    have hua : u ∈ insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ↔
        ka = true := by
      rw [Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (h | ⟨_, h, _⟩)
        · exact absurd h.symm hwu
        · exact h.resolve_right (fun hh => hh rfl)
      · intro h
        exact Or.inr ⟨hu, Or.inl h, Or.inr huv⟩
    have hvb : v ∈ insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ↔
        kb = true := by
      rw [Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (h | ⟨_, _, h⟩)
        · exact absurd h.symm hwv
        · exact h.resolve_right (fun hh => hh rfl)
      · intro h
        exact Or.inr ⟨hv, Or.inr (Ne.symm huv), Or.inl h⟩
    obtain ⟨j2, env2, c2, Pi2, hK2, hj2, hpu, hpv⟩ :=
      ks_prom hK u v w (Ne.symm hwu) (Ne.symm hwv) huv ka kb hua hvb
    have hD' : ∀ x ∈ insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))),
        x ≠ w → x ∈ D := by
      intro x hx hxw
      rcases Finset.mem_insert.mp hx with h | h
      · exact absurd h hxw
      · exact Finset.mem_of_mem_filter _ h
    have hfin : ∃ (f2 : ℕ → ℕ → ℕ) (env3 : ℕ → ℕ → ℕ → Prop) (c3 : ℕ → ℕ),
        KS D j2 f2 env3 c3 Pi2 := by
      rcases hw with rfl | rfl
      · exact hK2.step u v (u &&& v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
          (fun _ i => !(u.testBit i))
          (fun e i h1 h3 => and_cu u v e i h1.1 h1.2 h3)
          (fun e i h1 h3 => and_cv u v e i h1.1 h1.2 h3)
          (fun b e i e' i' _ h2 => h2) hpu hpv
      · exact hK2.step u v (u ||| v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
          (fun e _ => u.testBit e)
          (fun e i h1 h3 => or_cu u v e i h1.1 h1.2 h3)
          (fun e i h1 h3 => or_cv u v e i h1.1 h1.2 h3)
          (fun b e i e' i' h1 _ => h1) hpu hpv
    obtain ⟨f2, env3, c3, hK3⟩ := hfin
    refine ⟨j2, f2, env3, c3, Pi2, hK3, ?_⟩
    have e1 := cond_sum ka
    have e2 := cond_sum kb
    omega

-- the structure in mask coordinates (cell `q = 12 * e + i'`, `i = 12 + i'`), keyed by the words of a list

structure MS (l : List ℕ) (j : ℕ) (Env : ℕ → ℕ → Prop) (c : ℕ → ℕ) (PiM : ℕ → ℕ → Prop) : Prop where
  own : ∀ q, q < 144 → ∃ x ∈ l, Env x q
  envR : ∀ x ∈ l, IsRect (Env x)
  envB : ∀ x ∈ l, ∀ q, Env x q → q < 144 ∧ (rectW x).testBit q = true
  s1 : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → c x = c y → ∀ q, Env x q → Env y q → False
  s2 : ∀ x ∈ l, 1 ≤ c x → ∀ q, Env x q → PiM (c x) q
  piR : ∀ n, IsRect (PiM n)
  s3 : ∀ n q, 1 ≤ n → PiM n q → ∃ y ∈ l, 1 ≤ c y ∧ c y ≤ n ∧ (rectW y).testBit q = true
  lab : ∀ x ∈ l, c x ≤ j

theorem rect_conv (S : ℕ → ℕ → Prop) (hS : IsRect2 S) :
    IsRect (fun q => q < 144 ∧ S (q / 12) (12 + q % 12)) := by
  intro e i e' i' he hi he' hi' h1 h2
  have h1' : S ((12 * e + i) / 12) (12 + (12 * e + i) % 12) := h1.2
  have h2' : S ((12 * e' + i') / 12) (12 + (12 * e' + i') % 12) := h2.2
  have e1 : (12 * e + i) / 12 = e := by omega
  have e2 : (12 * e + i) % 12 = i := by omega
  have e3 : (12 * e' + i') / 12 = e' := by omega
  have e4 : (12 * e' + i') % 12 = i' := by omega
  have e5 : (12 * e + i') / 12 = e := by omega
  have e6 : (12 * e + i') % 12 = i' := by omega
  rw [e1, e2] at h1'
  rw [e3, e4] at h2'
  show 12 * e + i' < 144 ∧ S ((12 * e + i') / 12) (12 + (12 * e + i') % 12)
  rw [e5, e6]
  exact ⟨by omega, hS _ _ _ _ h1' h2'⟩

theorem pc_bit (x q : ℕ) (hq : q < 144) (h : Pc x (q / 12) (12 + q % 12)) :
    (rectW x).testBit q = true := by
  have h3 := rectW_tb x (q / 12) (q % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h.1 h.2
  rwa [Nat.div_add_mod] at h3

theorem KS.toMS {l : List ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS l.toFinset j f env c Pi) :
    MS l j (fun x q => q < 144 ∧ env x (q / 12) (12 + q % 12)) c
      (fun n q => q < 144 ∧ Pi n (q / 12) (12 + q % 12)) := by
  constructor
  · intro q hq
    obtain ⟨h1, h2⟩ := h.own (q / 12) (12 + q % 12) (by omega) (by omega)
    exact ⟨_, List.mem_toFinset.mp h1, hq, h2⟩
  · intro x hx
    exact rect_conv _ (h.envR x (List.mem_toFinset.mpr hx))
  · intro x hx q hq
    exact ⟨hq.1, pc_bit x q hq.1 (h.envP x (List.mem_toFinset.mpr hx) _ _ hq.2)⟩
  · intro x hx y hy hxy hc q h1 h2
    exact h.s1 x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy) hxy hc _ _ h1.2 h2.2
  · intro x hx hc q h1
    exact ⟨h1.1, h.s2 x (List.mem_toFinset.mpr hx) hc _ _ h1.2⟩
  · intro n
    exact rect_conv _ (h.piR n)
  · intro n q hn h1
    obtain ⟨y, hy, h3, h4, h5⟩ := h.s3 n _ _ hn h1.2
    exact ⟨y, List.mem_toFinset.mp hy, h3, h4, pc_bit y q h1.1 h5⟩
  · intro x hx
    exact h.lab x (List.mem_toFinset.mpr hx)

/-- the private hull of a word lies in its envelope. -/
theorem MS.priv_env {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
    (hM : MS l j Env c PiM) : ∀ y ∈ l, ∀ q,
    (priv (tw (l.map rectW) 0 0) (rectW y)).testBit q = true → Env y q := by
  intro y hy q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land (rectW y) (Nat.xor (tw (l.map rectW) 0 0) full)).testBit x = true → Env y x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (l.map rectW) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z, hz, hzq⟩ := hM.own x hx
    by_cases hzz : z = y
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) l hpw z hz y hy hzz
        ⟨(hM.envB z hz x hzq).2, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hM.envR y hy (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

/-- **(K+1)-colourability.**  With `K = k + 1 - |l|` spare reads the conflict graph of the private
hulls (two words are adjacent when their private hulls meet) has a proper colouring with the
colours `0, ..., K`. -/
theorem reach_colour {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hR : Reach m l.toFinset k) :
    ∃ c : ℕ → ℕ, (∀ x ∈ l, c x + l.length ≤ k + 1) ∧
      ∀ x ∈ l, ∀ y ∈ l, x ≠ y → c x = c y →
        Nat.land (priv (tw (l.map rectW) 0 0) (rectW x)) (priv (tw (l.map rectW) 0 0) (rectW y)) = 0 := by
  obtain ⟨j, f, env, c, Pi, hK, hj⟩ := hR.ks
  rw [List.toFinset_card_of_nodup hnd] at hj
  have hM := hK.toMS
  refine ⟨c, fun x hx => ?_, ?_⟩
  · have := hM.lab x hx
    omega
  · intro x hx y hy hxy hc
    exact land_disj _ _ (fun q h1 h2 =>
      hM.s1 x hx y hy hxy hc q (hM.priv_env x hx q h1) (hM.priv_env y hy q h2))

/-- a valid labelling of the words of `l` with `K` spare reads (`T` = cells in at least two
rectangles, `priv T (rectW x)` = hull of the private cells of `x`):
labels at most `K`; words with the same label have disjoint private hulls; for every label `i ≥ 1`
the hull of any cell set inside the private hulls of the words labelled `i` is covered by the
rectangles of the words labelled `1..i`; every private hull lies in its own rectangle.
(Conditions (1), (2) of the class rule follow: restrict `c` to the conflict words; the rule's cover
set additionally contains the conflict-free words.) -/
def ValidLab (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ x ∈ l, c x ≤ K) ∧
  (∀ x ∈ l, ∀ y ∈ l, x ≠ y → c x = c y →
    Nat.land (priv (tw (l.map rectW) 0 0) (rectW x)) (priv (tw (l.map rectW) 0 0) (rectW y)) = 0) ∧
  (∀ i U : ℕ, 1 ≤ i →
    (∀ q, U.testBit q = true →
      ∃ x ∈ l, c x = i ∧ (priv (tw (l.map rectW) 0 0) (rectW x)).testBit q = true) →
    ∀ q, (hull U).testBit q = true → ∃ y ∈ l, 1 ≤ c y ∧ c y ≤ i ∧ (rectW y).testBit q = true) ∧
  (∀ x ∈ l, ∀ q, (priv (tw (l.map rectW) 0 0) (rectW x)).testBit q = true →
    (rectW x).testBit q = true)

theorem MS.validLab {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
    (hM : MS l j Env c PiM) (K : ℕ) (hK : j ≤ K) : ValidLab l K c := by
  refine ⟨fun x hx => le_trans (hM.lab x hx) hK, ?_, ?_, ?_⟩
  · intro x hx y hy hxy hc
    exact land_disj _ _ (fun q h1 h2 =>
      hM.s1 x hx y hy hxy hc q (hM.priv_env x hx q h1) (hM.priv_env y hy q h2))
  · intro i U hi hU q hq
    obtain ⟨_, a, e', ha, he', h1, h2⟩ := hull_spec _ q hq
    obtain ⟨x1, hx1, hc1, hb1⟩ := hU _ h1
    obtain ⟨x2, hx2, hc2, hb2⟩ := hU _ h2
    have hp1 := hM.s2 x1 hx1 (by omega) _ (hM.priv_env x1 hx1 _ hb1)
    have hp2 := hM.s2 x2 hx2 (by omega) _ (hM.priv_env x2 hx2 _ hb2)
    rw [hc1] at hp1
    rw [hc2] at hp2
    have h3 := hM.piR i (q / 12) a e' (q % 12) (by omega) ha he' (Nat.mod_lt _ (by norm_num))
      hp1 hp2
    rw [Nat.div_add_mod] at h3
    exact hM.s3 i q hi h3
  · intro x hx q hq
    exact (hM.envB x hx q (hM.priv_env x hx q hq)).2

/-- **Lemma A + B, statement form.**  A state that reaches the target (either mode `m`) has a valid
labelling with `K = k + 1 - |l|` labels above 0. -/
theorem reach_validLab {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hR : Reach m l.toFinset k) :
    ∃ c : ℕ → ℕ, ValidLab l (Nat.sub (Nat.succ k) l.length) c := by
  obtain ⟨j, f, env, c, Pi, hK, hj⟩ := hR.ks
  rw [List.toFinset_card_of_nodup hnd] at hj
  exact ⟨c, hK.toMS.validLab _ (by
    show j ≤ (k + 1) - l.length
    omega)⟩


-- CLASS RULE as a Bool function (specification: cert/spec.py `class_rule`, NOTES-search.md 3.4).
-- Uses `rectW`, `full`, `band`, `bor`, `bnot`, `len'` (Core) and `tw`, `priv`, `hull` (RectPart).
-- Packed fields: field `i` of `x` = bits `144 * i .. 144 * i + 143`.

def fld (x i : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 144 i)) full

def put (x i v : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft v (Nat.mul 144 i))

/-- `h ⊆ c` as cell sets. -/
def subM (h c : ℕ) : Bool := Nat.beq (Nat.land h c) h

/-- condition (2) for the labels `K - n + 1 .. K`: the hull of class `i` (field `i` of `hs`) is
covered by `bc` (free words and words not labelled yet) and the classes `1 .. i` (fields of `cs`);
`pre` = union of the fields `1 .. K - n` of `cs`. -/
def chkA (bc hs cs K : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, pre =>
    subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))) &&
    chkA bc hs cs K n (Nat.lor pre (fld cs (Nat.sub K n)))

/-- try the labels `K - n + 1 .. K` (so `n = K + 1` tries `0 .. K`) for a word with mask `a` and
private hull `h`.  `us`: union of the private hulls per label, `hs`: hull of that union,
`cs`: union of the masks per label. -/
def tryL (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 =>
    (Nat.beq (Nat.land (fld us (Nat.sub K n)) h) 0 &&
      (chkA bc (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
          (put cs (Nat.sub K n) a) K K 0 &&
        cont (put us (Nat.sub K n) h)
          (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
          (put cs (Nat.sub K n) a))) ||
    tryL K bc a h cont us hs cs n

/-- union of the masks (field 0) of the items. -/
def orA : List ℕ → ℕ
  | [] => 0
  | it :: r => Nat.lor (fld it 0) (orA r)

/-- branch and bound over the labels of the conflict words; item = mask (field 0), private hull
(field 1). -/
def go (K base : ℕ) : List ℕ → ℕ → ℕ → ℕ → Bool
  | [] => fun _ _ _ => true
  | it :: rest => fun us hs cs =>
    tryL K (Nat.lor base (orA rest)) (fld it 0) (fld it 1) (go K base rest) us hs cs (Nat.succ K)

/-- items of the words whose private hull meets another private hull (`t2`: cells in at least two
private hulls). -/
def vs (t t2 : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: l => cond (Nat.beq (Nat.land (priv t a) t2) 0) (vs t t2 l)
      (put (Nat.land a full) 1 (priv t a) :: vs t t2 l)

/-- union of the masks of the other (free) words. -/
def fcov (t t2 : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => cond (Nat.beq (Nat.land (priv t a) t2) 0) (Nat.lor a (fcov t t2 l)) (fcov t t2 l)

/-- number of items of `all` whose private hull meets that of `x`. -/
def degI (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | y :: l => cond (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0) (degI x l) (Nat.succ (degI x l))

def insD (all : List ℕ) (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: l => cond (Nat.blt (degI y all) (degI x all)) (x :: y :: l) (y :: insD all x l)

/-- the items by decreasing degree (only a heuristic order; any permutation is sound). -/
def sortD (all : List ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: l => insD all x (sortD all l)

theorem insD_perm (all : List ℕ) (x : ℕ) : ∀ l : List ℕ, (insD all x l).Perm (x :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons y l ih =>
    unfold insD
    cases Nat.blt (degI y all) (degI x all)
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y l)
    · exact List.Perm.refl _

theorem sortD_perm (all : List ℕ) : ∀ l : List ℕ, (sortD all l).Perm l := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih => exact (insD_perm all x _).trans (List.Perm.cons x ih)

def classP3 (K t t2 : ℕ) (as : List ℕ) : Bool :=
  go K (fcov t t2 as)
    (cond (Nat.blt 1 K) (sortD (vs t t2 as) (vs t t2 as)) (vs t t2 as)) 0 0 0

def classP2 (K : ℕ) (as : List ℕ) (t : ℕ) : Bool := classP3 K t (tw (as.map (priv t)) 0 0) as

/-- the class rule on a live list `l` with `k` steps left (`K = k + 1 - |l|`). -/
def classP (l : List ℕ) (k : ℕ) : Bool :=
  classP2 (Nat.sub (Nat.succ k) l.length) (l.map rectW) (tw (l.map rectW) 0 0)

-- kernel-friendly twins (raw recursors)

def chkA' (bc hs cs K n : ℕ) : ℕ → Bool :=
  @Nat.rec (fun _ => ℕ → Bool) (fun _ => true)
    (fun n ih pre => band (subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))))
      (ih (Nat.lor pre (fld cs (Nat.sub K n))))) n

theorem chkA'_eq (bc hs cs K n : ℕ) : ∀ pre : ℕ, chkA' bc hs cs K n pre = chkA bc hs cs K n pre := by
  induction n with
  | zero => intro pre; rfl
  | succ n ih =>
    intro pre
    show band (subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))))
      (chkA' bc hs cs K n (Nat.lor pre (fld cs (Nat.sub K n)))) =
      (subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))) &&
        chkA bc hs cs K n (Nat.lor pre (fld cs (Nat.sub K n))))
    rw [ih, band_eq]

def tryL' (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs n : ℕ) : Bool :=
  @Nat.rec (fun _ => Bool) false
    (fun n ih => bor
      (band (Nat.beq (Nat.land (fld us (Nat.sub K n)) h) 0)
        (band (chkA' bc (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a) K K 0)
          (cont (put us (Nat.sub K n) h)
            (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a))))
      ih) n

theorem tryL'_eq (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs n : ℕ) :
    tryL' K bc a h cont us hs cs n = tryL K bc a h cont us hs cs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show bor
      (band (Nat.beq (Nat.land (fld us (Nat.sub K n)) h) 0)
        (band (chkA' bc (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a) K K 0)
          (cont (put us (Nat.sub K n) h)
            (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a))))
      (tryL' K bc a h cont us hs cs n) = tryL K bc a h cont us hs cs (n + 1)
    rw [ih, bor_eq, band_eq, band_eq, chkA'_eq]
    rfl

def orA' (l : List ℕ) : ℕ := @List.rec ℕ (fun _ => ℕ) 0 (fun it _ ih => Nat.lor (fld it 0) ih) l

theorem orA'_eq (l : List ℕ) : orA' l = orA l := by
  induction l with
  | nil => rfl
  | cons it r ih => show Nat.lor (fld it 0) (orA' r) = Nat.lor (fld it 0) (orA r); rw [ih]

def go' (K base : ℕ) (l : List ℕ) : ℕ → ℕ → ℕ → Bool :=
  @List.rec ℕ (fun _ => ℕ → ℕ → ℕ → Bool) (fun _ _ _ => true)
    (fun it rest ih us hs cs =>
      tryL' K (Nat.lor base (orA' rest)) (fld it 0) (fld it 1) ih us hs cs (Nat.succ K)) l

theorem go'_eq (K base : ℕ) (l : List ℕ) : go' K base l = go K base l := by
  induction l with
  | nil => rfl
  | cons it rest ih =>
    funext us hs cs
    show tryL' K (Nat.lor base (orA' rest)) (fld it 0) (fld it 1) (go' K base rest) us hs cs
      (Nat.succ K) = tryL K (Nat.lor base (orA rest)) (fld it 0) (fld it 1) (go K base rest) us hs cs
      (Nat.succ K)
    rw [ih, orA'_eq, tryL'_eq]

def vs' (t t2 : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) []
    (fun a _ ih => @Bool.rec (fun _ => List ℕ) (put (Nat.land a full) 1 (priv t a) :: ih) ih
      (Nat.beq (Nat.land (priv t a) t2) 0)) l

theorem vs'_eq (t t2 : ℕ) (l : List ℕ) : vs' t t2 l = vs t t2 l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show @Bool.rec (fun _ => List ℕ) (put (Nat.land a full) 1 (priv t a) :: vs' t t2 l) (vs' t t2 l)
      (Nat.beq (Nat.land (priv t a) t2) 0) =
      cond (Nat.beq (Nat.land (priv t a) t2) 0) (vs t t2 l)
        (put (Nat.land a full) 1 (priv t a) :: vs t t2 l)
    rw [ih]
    cases Nat.beq (Nat.land (priv t a) t2) 0 <;> rfl

def fcov' (t t2 : ℕ) (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0
    (fun a _ ih => @Bool.rec (fun _ => ℕ) ih (Nat.lor a ih) (Nat.beq (Nat.land (priv t a) t2) 0)) l

theorem fcov'_eq (t t2 : ℕ) (l : List ℕ) : fcov' t t2 l = fcov t t2 l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show @Bool.rec (fun _ => ℕ) (fcov' t t2 l) (Nat.lor a (fcov' t t2 l))
      (Nat.beq (Nat.land (priv t a) t2) 0) =
      cond (Nat.beq (Nat.land (priv t a) t2) 0) (Nat.lor a (fcov t t2 l)) (fcov t t2 l)
    rw [ih]
    cases Nat.beq (Nat.land (priv t a) t2) 0 <;> rfl

def degI' (x : ℕ) (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0
    (fun y _ ih => @Bool.rec (fun _ => ℕ) (Nat.succ ih) ih
      (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0)) l

theorem degI'_eq (x : ℕ) (l : List ℕ) : degI' x l = degI x l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    show @Bool.rec (fun _ => ℕ) (Nat.succ (degI' x l)) (degI' x l)
      (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0) =
      cond (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0) (degI x l) (Nat.succ (degI x l))
    rw [ih]
    cases Nat.beq (Nat.land (fld y 1) (fld x 1)) 0 <;> rfl

def insD' (all : List ℕ) (x : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [x]
    (fun y t ih => @Bool.rec (fun _ => List ℕ) (y :: ih) (x :: y :: t)
      (Nat.blt (degI' y all) (degI' x all))) l

theorem insD'_eq (all : List ℕ) (x : ℕ) (l : List ℕ) : insD' all x l = insD all x l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    show @Bool.rec (fun _ => List ℕ) (y :: insD' all x l) (x :: y :: l)
      (Nat.blt (degI' y all) (degI' x all)) =
      cond (Nat.blt (degI y all) (degI x all)) (x :: y :: l) (y :: insD all x l)
    rw [ih, degI'_eq, degI'_eq]
    cases Nat.blt (degI y all) (degI x all) <;> rfl

def sortD' (all : List ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun x _ ih => insD' all x ih) l

theorem sortD'_eq (all : List ℕ) (l : List ℕ) : sortD' all l = sortD all l := by
  induction l with
  | nil => rfl
  | cons x l ih => show insD' all x (sortD' all l) = insD all x (sortD all l); rw [ih, insD'_eq]

def mapP' (t : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun a _ ih => priv t a :: ih) l

theorem mapP'_eq (t : ℕ) (l : List ℕ) : mapP' t l = l.map (priv t) := by
  induction l with
  | nil => rfl
  | cons a l ih => show priv t a :: mapP' t l = priv t a :: l.map (priv t); rw [ih]

/-- `classP` in kernel-friendly form (`as`: evaluated mask list). -/
def classQ (K : ℕ) (as : List ℕ) : Bool :=
  (fun t => (fun t2 => (fun items =>
      go' K (fcov' t t2 as)
        (@Bool.rec (fun _ => List ℕ) items (sortD' items items) (Nat.blt 1 K)) 0 0 0)
    (vs' t t2 as)) (tw' (mapP' t as) 0 0)) (tw' as 0 0)

def classP' (l : List ℕ) (k : ℕ) : Bool := classQ (Nat.sub (Nat.succ k) (len' l)) (mapW' l)

theorem classP'_eq (l : List ℕ) (k : ℕ) : classP' l k = classP l k := by
  show go' _ (fcov' _ _ (mapW' l))
    (@Bool.rec (fun _ => List ℕ) (vs' _ _ (mapW' l)) (sortD' (vs' _ _ (mapW' l)) (vs' _ _ (mapW' l)))
      (Nat.blt 1 (Nat.sub (Nat.succ k) (len' l)))) 0 0 0 = classP l k
  rw [mapW'_eq, len'_eq, tw'_eq, mapP'_eq, tw'_eq, go'_eq, fcov'_eq, vs'_eq, sortD'_eq]
  unfold classP classP2 classP3
  cases Nat.blt 1 (Nat.sub (Nat.succ k) l.length) <;> rfl

theorem classP'_ok {m : Bool} (h : PruneOK m classP) : PruneOK m classP' := by
  intro l k hnd hR
  rw [classP'_eq]
  exact h l k hnd hR

-- COMPLETENESS OF THE CLASS-RULE SEARCH: a valid labelling makes `classP` (and `classP'`) true.
-- Uses `fld`, `put`, `subM`, `chkA`, `tryL`, `orA`, `go`, `vs`, `fcov`, `sortD_perm`, `classP`
-- (ClassPart), `hull_spec`, `tw`, `priv`, `tb_land`, `tb_lor`, `full_tb`, `land_sub`, `land_disj`
-- (RectPart), `rectW`, `full` (Core).

/-- private hull of the word `x` in the live list `l`. -/
def privH (l : List ℕ) (x : ℕ) : ℕ := priv (tw (l.map rectW) 0 0) (rectW x)

/-- cells lying in at least two private hulls. -/
def t2Of (l : List ℕ) : ℕ := tw ((l.map rectW).map (priv (tw (l.map rectW) 0 0))) 0 0

/-- `x` is a conflict word (its private hull meets another private hull). -/
def isConf (l : List ℕ) (x : ℕ) : Prop := Nat.land (privH l x) (t2Of l) ≠ 0

/-- a valid labelling of the conflict words (NOTES-search.md 3.4): labels `0..K` on the conflict
words, (1) conflicting words get different labels, (2) for `i ≥ 1` the hull of any cell set inside
the private hulls of class `i` is covered by the free words and the classes `1..i`. -/
structure ClassLab (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop where
  le : ∀ x ∈ l, isConf l x → c x ≤ K
  ne : l.Pairwise (fun x y => isConf l x → isConf l y → c x = c y →
        Nat.land (privH l x) (privH l y) = 0)
  cov : ∀ i U : ℕ, 1 ≤ i → i ≤ K →
        (∀ r, U.testBit r = true →
          ∃ x ∈ l, isConf l x ∧ c x = i ∧ (privH l x).testBit r = true) →
        ∀ q, (hull U).testBit q = true →
        ∃ y ∈ l, (rectW y).testBit q = true ∧ (isConf l y → 1 ≤ c y ∧ c y ≤ i)

/-- `ValidLab` (ClassPartA: labels on all words, cover by the classes `1..i` only) gives a
labelling in the sense of the rule. -/
theorem ValidLab.classLab {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (hnd : l.Nodup)
    (h : ValidLab l K c) : ClassLab l K c := by
  obtain ⟨h1, h2, h3, _⟩ := h
  refine ⟨fun x hx _ => h1 x hx, ?_, ?_⟩
  · have hnd' : l.Pairwise (fun x y => x ≠ y) := hnd
    exact List.Pairwise.imp_of_mem (fun hx hy hxy _ _ hc => h2 _ hx _ hy hxy hc) hnd'
  · intro i U hi1 _ hU q hq
    obtain ⟨y, hy, hc1, hc2, hb⟩ :=
      h3 i U hi1 (fun r hr => (hU r hr).imp (fun x hx => ⟨hx.1, hx.2.2⟩)) q hq
    exact ⟨y, hy, hb, fun _ => ⟨hc1, hc2⟩⟩

-- bits of the packed fields

theorem fld_tb (x i q : ℕ) :
    (fld x i).testBit q = (x.testBit (144 * i + q) && decide (q < 144)) := by
  unfold fld
  rw [tb_land, full_tb]
  show ((x >>> (144 * i)).testBit q && decide (q < 144)) = _
  rw [Nat.testBit_shiftRight]

theorem put_tb (x i v r : ℕ) :
    (put x i v).testBit r = (x.testBit r || (decide (144 * i ≤ r) && v.testBit (r - 144 * i))) := by
  unfold put
  rw [tb_lor]
  show (x.testBit r || (v <<< (144 * i)).testBit r) = _
  rw [Nat.testBit_shiftLeft]

theorem fld_lt (x i q : ℕ) (h : (fld x i).testBit q = true) : q < 144 := by
  rw [fld_tb, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem fld_zero (j q : ℕ) : (fld 0 j).testBit q = false := by
  rw [fld_tb, Nat.zero_testBit]
  rfl

theorem fld_put_same (x i v q : ℕ) (hv : ∀ r, v.testBit r = true → r < 144) :
    (fld (put x i v) i).testBit q = ((fld x i).testBit q || v.testBit q) := by
  rw [fld_tb, put_tb, fld_tb]
  have e : 144 * i + q - 144 * i = q := by omega
  have e2 : decide (144 * i ≤ 144 * i + q) = true := decide_eq_true (by omega)
  rw [e, e2]
  cases h : v.testBit q
  · simp
  · have e3 : decide (q < 144) = true := decide_eq_true (hv q h)
    rw [e3]
    simp

theorem fld_put_ne (x i j v q : ℕ) (hv : ∀ r, v.testBit r = true → r < 144) (hij : j ≠ i) :
    (fld (put x i v) j).testBit q = (fld x j).testBit q := by
  rw [fld_tb, put_tb, fld_tb]
  by_cases hq : q < 144
  · have e : (decide (144 * i ≤ 144 * j + q) && v.testBit (144 * j + q - 144 * i)) = false := by
      by_cases hle : 144 * i ≤ 144 * j + q
      · have hb : v.testBit (144 * j + q - 144 * i) = false := by
          cases hc : v.testBit (144 * j + q - 144 * i)
          · rfl
          · have := hv _ hc
            omega
        rw [hb]
        exact Bool.and_false _
      · rw [decide_eq_false hle]
        rfl
    rw [e, Bool.or_false]
  · rw [decide_eq_false hq, Bool.and_false, Bool.and_false]

theorem land_zero_tb (a b q : ℕ) (h : Nat.land a b = 0) (ha : a.testBit q = true)
    (hb : b.testBit q = true) : False := by
  have e := tb_land a b q
  rw [h, ha, hb, Nat.zero_testBit] at e
  exact Bool.noConfusion e

-- the three layers of the search

theorem chkA_true (bc hs cs K : ℕ)
    (G : ∀ i, 1 ≤ i → i ≤ K → ∀ q, (fld hs i).testBit q = true →
      bc.testBit q = true ∨ ∃ j, 1 ≤ j ∧ j ≤ i ∧ (fld cs j).testBit q = true) :
    ∀ n pre : ℕ, n ≤ K →
      (∀ j, 1 ≤ j → j + n ≤ K → ∀ q, (fld cs j).testBit q = true → pre.testBit q = true) →
      chkA bc hs cs K n pre = true := by
  intro n
  induction n with
  | zero => intro pre _ _; rfl
  | succ n ih =>
    intro pre hn hpre
    show (subM (fld hs (K - n)) (Nat.lor bc (Nat.lor pre (fld cs (K - n)))) &&
      chkA bc hs cs K n (Nat.lor pre (fld cs (K - n)))) = true
    rw [Bool.and_eq_true]
    constructor
    · have e : Nat.land (fld hs (K - n)) (Nat.lor bc (Nat.lor pre (fld cs (K - n)))) =
          fld hs (K - n) := by
        apply land_sub
        intro q hq
        rw [tb_lor, tb_lor]
        rcases G (K - n) (by omega) (by omega) q hq with h | ⟨j, hj1, hj2, hj⟩
        · rw [h]; rfl
        · by_cases hj' : j = K - n
          · subst hj'; rw [hj]; simp
          · rw [hpre j hj1 (by omega) q hj]; simp
      unfold subM
      rw [e]
      exact Nat.beq_refl _
    · apply ih _ (by omega)
      intro j hj1 hj2 q hq
      rw [tb_lor]
      by_cases hj' : j = K - n
      · subst hj'; rw [hq]; simp
      · rw [hpre j hj1 (by omega) q hq]; simp

theorem tryL_true (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs j : ℕ)
    (h1 : Nat.land (fld us j) h = 0)
    (h2 : chkA bc (put hs j (hull (Nat.lor (fld us j) h))) (put cs j a) K K 0 = true)
    (h3 : cont (put us j h) (put hs j (hull (Nat.lor (fld us j) h))) (put cs j a) = true) :
    ∀ n : ℕ, j ≤ K → K - j < n → tryL K bc a h cont us hs cs n = true := by
  intro n
  induction n with
  | zero => intro _ hn; omega
  | succ n ih =>
    intro hj hn
    show ((Nat.beq (Nat.land (fld us (K - n)) h) 0 &&
      (chkA bc (put hs (K - n) (hull (Nat.lor (fld us (K - n)) h)))
          (put cs (K - n) a) K K 0 &&
        cont (put us (K - n) h)
          (put hs (K - n) (hull (Nat.lor (fld us (K - n)) h)))
          (put cs (K - n) a))) ||
      tryL K bc a h cont us hs cs n) = true
    by_cases e : K - j = n
    · have e2 : K - n = j := by omega
      rw [e2, h1, h2, h3]
      rfl
    · rw [ih hj (by omega)]
      exact Bool.or_true _

theorem orA_tb (q : ℕ) : ∀ (rest : List (ℕ × ℕ)), ∀ p ∈ rest, (fld p.1 0).testBit q = true →
    (orA (rest.map Prod.fst)).testBit q = true := by
  intro rest
  induction rest with
  | nil => intro p hp; simp at hp
  | cons r rest ih =>
    intro p hp hb
    show (Nat.lor (fld r.1 0) (orA (rest.map Prod.fst))).testBit q = true
    rw [tb_lor]
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [hb]; rfl
    · rw [ih p hp hb]; exact Bool.or_true _

/-- invariant form: `rest` = items (with their labels) still to be placed, `M` = all items. -/
theorem go_inv (K base : ℕ) (M : ℕ × ℕ → Prop)
    (h2 : ∀ i, 1 ≤ i → i ≤ K → ∀ q,
      (∃ U : ℕ, (∀ r, U.testBit r = true → ∃ p, M p ∧ p.2 = i ∧ (fld p.1 1).testBit r = true) ∧
        (hull U).testBit q = true) →
      base.testBit q = true ∨ ∃ p, M p ∧ 1 ≤ p.2 ∧ p.2 ≤ i ∧ (fld p.1 0).testBit q = true) :
    ∀ (rest : List (ℕ × ℕ)) (us hs cs : ℕ),
      (∀ p ∈ rest, M p) → (∀ p ∈ rest, p.2 ≤ K) →
      rest.Pairwise (fun p r => p.2 = r.2 → Nat.land (fld p.1 1) (fld r.1 1) = 0) →
      (∀ r ∈ rest, ∀ q, (fld us r.2).testBit q = true → (fld r.1 1).testBit q = true → False) →
      (∀ j q, (fld us j).testBit q = true → ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit q = true) →
      (∀ j q, (fld hs j).testBit q = true →
        ∃ U : ℕ, (∀ r, U.testBit r = true → ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit r = true) ∧
          (hull U).testBit q = true) →
      (∀ p, M p → p ∈ rest ∨ ∀ q, (fld p.1 0).testBit q = true → (fld cs p.2).testBit q = true) →
      go K base (rest.map Prod.fst) us hs cs = true := by
  intro rest
  induction rest with
  | nil => intro us hs cs _ _ _ _ _ _ _; rfl
  | cons it rest ih =>
    intro us hs cs hM hK hP Ius Ius2 Ihs Ics
    show tryL K (Nat.lor base (orA (rest.map Prod.fst))) (fld it.1 0) (fld it.1 1)
      (go K base (rest.map Prod.fst)) us hs cs (Nat.succ K) = true
    have hit : it ∈ it :: rest := List.mem_cons_self
    have bh : ∀ r, (fld it.1 1).testBit r = true → r < 144 := fun r => fld_lt _ _ r
    have ba : ∀ r, (fld it.1 0).testBit r = true → r < 144 := fun r => fld_lt _ _ r
    have bH : ∀ r, (hull (Nat.lor (fld us it.2) (fld it.1 1))).testBit r = true → r < 144 :=
      fun r hr => (hull_spec _ r hr).1
    have Fus : ∀ j q, (fld (put us it.2 (fld it.1 1)) j).testBit q = true →
        ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit q = true := by
      intro j q hq
      by_cases hj : j = it.2
      · subst hj
        rw [fld_put_same _ _ _ _ bh, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact Ius2 _ q hq
        · exact ⟨it, hM it hit, rfl, hq⟩
      · rw [fld_put_ne _ _ _ _ _ bh hj] at hq
        exact Ius2 j q hq
    have Fhs : ∀ j q,
        (fld (put hs it.2 (hull (Nat.lor (fld us it.2) (fld it.1 1)))) j).testBit q = true →
        ∃ U : ℕ, (∀ r, U.testBit r = true → ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit r = true) ∧
          (hull U).testBit q = true := by
      intro j q hq
      by_cases hj : j = it.2
      · subst hj
        rw [fld_put_same _ _ _ _ bH, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact Ihs _ q hq
        · refine ⟨Nat.lor (fld us it.2) (fld it.1 1), ?_, hq⟩
          intro r hr
          rw [tb_lor, Bool.or_eq_true] at hr
          rcases hr with hr | hr
          · exact Ius2 _ r hr
          · exact ⟨it, hM it hit, rfl, hr⟩
      · rw [fld_put_ne _ _ _ _ _ bH hj] at hq
        exact Ihs j q hq
    have Fcs : ∀ p, M p → p ∈ rest ∨
        ∀ q, (fld p.1 0).testBit q = true →
          (fld (put cs it.2 (fld it.1 0)) p.2).testBit q = true := by
      intro p hp
      have key : (∀ q, (fld p.1 0).testBit q = true → (fld cs p.2).testBit q = true) →
          ∀ q, (fld p.1 0).testBit q = true →
            (fld (put cs it.2 (fld it.1 0)) p.2).testBit q = true := by
        intro hold q hq
        by_cases hj : p.2 = it.2
        · rw [hj, fld_put_same _ _ _ _ ba, ← hj, hold q hq]
          rfl
        · rw [fld_put_ne _ _ _ _ _ ba hj]
          exact hold q hq
      rcases Ics p hp with hin | hold
      · rcases List.mem_cons.mp hin with rfl | hin
        · right
          intro q hq
          rw [fld_put_same _ _ _ _ ba, hq]
          exact Bool.or_true _
        · exact Or.inl hin
      · exact Or.inr (key hold)
    have hP' := List.pairwise_cons.mp hP
    apply tryL_true K _ _ _ _ us hs cs it.2 ?_ ?_ ?_ (Nat.succ K) (hK it hit)
      (Nat.lt_succ_of_le (Nat.sub_le _ _))
    · exact land_disj _ _ (Ius it hit)
    · apply chkA_true _ _ _ _ ?_ K 0 (Nat.le_refl _)
      · intro j hj1 hj2; omega
      · intro i hi1 hi2 q hq
        rcases h2 i hi1 hi2 q (Fhs i q hq) with hb | ⟨p, hp, hp1, hp2, hpq⟩
        · left
          rw [tb_lor, hb]
          rfl
        · rcases Fcs p hp with hin | hc
          · left
            rw [tb_lor, orA_tb q rest p hin hpq]
            exact Bool.or_true _
          · exact Or.inr ⟨p.2, hp1, hp2, hc q hpq⟩
    · apply ih _ _ _ (fun p hp => hM p (List.mem_cons_of_mem _ hp))
        (fun p hp => hK p (List.mem_cons_of_mem _ hp)) hP'.2 ?_ Fus Fhs Fcs
      intro r hr q hq hrq
      by_cases hj : r.2 = it.2
      · rw [hj, fld_put_same _ _ _ _ bh, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · rw [← hj] at hq
          exact Ius r (List.mem_cons_of_mem _ hr) q hq hrq
        · exact land_zero_tb _ _ q (hP'.1 r hr hj.symm) hq hrq
      · rw [fld_put_ne _ _ _ _ _ bh hj] at hq
        exact Ius r (List.mem_cons_of_mem _ hr) q hq hrq

theorem perm_map_lift {α β : Type} (f : α → β) {l1 l2 : List β} (h : l1.Perm l2) :
    ∀ ps : List α, ps.map f = l1 → ∃ ps' : List α, ps'.Perm ps ∧ ps'.map f = l2 := by
  induction h with
  | nil => intro ps hps; exact ⟨ps, List.Perm.refl _, hps⟩
  | cons x _ ih =>
    intro ps hps
    rcases ps with _ | ⟨p, ps⟩
    · simp at hps
    · rw [List.map_cons, List.cons.injEq] at hps
      obtain ⟨qs, hq1, hq2⟩ := ih ps hps.2
      refine ⟨p :: qs, List.Perm.cons p hq1, ?_⟩
      rw [List.map_cons, hq2, hps.1]
  | swap x y l =>
    intro ps hps
    rcases ps with _ | ⟨p, _ | ⟨q, r⟩⟩
    · simp at hps
    · rw [List.map_cons, List.cons.injEq] at hps
      simp at hps
    · rw [List.map_cons, List.map_cons, List.cons.injEq, List.cons.injEq] at hps
      refine ⟨q :: p :: r, List.Perm.swap _ _ _, ?_⟩
      rw [List.map_cons, List.map_cons, hps.1, hps.2.1, hps.2.2]
  | trans _ _ ih1 ih2 =>
    intro ps hps
    obtain ⟨qs, a, b⟩ := ih1 ps hps
    obtain ⟨rs, c, d⟩ := ih2 qs b
    exact ⟨rs, c.trans a, d⟩

/-- `go` succeeds on any ordering of the items of a validly labelled item list `all`. -/
theorem go_complete (K base : ℕ) (all : List (ℕ × ℕ)) (its : List ℕ)
    (hperm : its.Perm (all.map Prod.fst))
    (hK : ∀ p ∈ all, p.2 ≤ K)
    (h1 : all.Pairwise (fun p r => p.2 = r.2 → Nat.land (fld p.1 1) (fld r.1 1) = 0))
    (h2 : ∀ i, 1 ≤ i → i ≤ K → ∀ q,
      (∃ U : ℕ, (∀ r, U.testBit r = true →
          ∃ p, p ∈ all ∧ p.2 = i ∧ (fld p.1 1).testBit r = true) ∧
        (hull U).testBit q = true) →
      base.testBit q = true ∨
        ∃ p, p ∈ all ∧ 1 ≤ p.2 ∧ p.2 ≤ i ∧ (fld p.1 0).testBit q = true) :
    go K base its 0 0 0 = true := by
  obtain ⟨ps, hps, hmap⟩ := perm_map_lift Prod.fst hperm.symm all rfl
  rw [← hmap]
  have hsym : ∀ {p r : ℕ × ℕ}, (p.2 = r.2 → Nat.land (fld p.1 1) (fld r.1 1) = 0) →
      (r.2 = p.2 → Nat.land (fld r.1 1) (fld p.1 1) = 0) := by
    intro p r h e
    have h' := h e.symm
    apply land_disj
    intro q ha hb
    exact land_zero_tb _ _ q h' hb ha
  apply go_inv K base (fun p => p ∈ all) h2 ps 0 0 0
  · exact fun p hp => hps.mem_iff.mp hp
  · exact fun p hp => hK p (hps.mem_iff.mp hp)
  · exact (hps.pairwise_iff hsym).mpr h1
  · intro r _ q hq
    rw [fld_zero] at hq
    exact Bool.noConfusion hq
  · intro j q hq
    rw [fld_zero] at hq
    exact Bool.noConfusion hq
  · intro j q hq
    rw [fld_zero] at hq
    exact Bool.noConfusion hq
  · exact fun p hp => Or.inl (hps.mem_iff.mpr hp)

-- the items of classP

theorem vs_eq (t t2 : ℕ) : ∀ l : List ℕ, vs t t2 (l.map rectW) =
    (l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
      (fun x => put (Nat.land (rectW x) full) 1 (priv t (rectW x))) := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    show cond (Nat.beq (Nat.land (priv t (rectW x)) t2) 0) (vs t t2 (l.map rectW))
      (put (Nat.land (rectW x) full) 1 (priv t (rectW x)) :: vs t t2 (l.map rectW)) = _
    rw [ih]
    cases hb : Nat.beq (Nat.land (priv t (rectW x)) t2) 0
    · rw [List.filter_cons_of_pos (by rw [hb]; rfl)]
      rfl
    · rw [List.filter_cons_of_neg (by rw [hb]; exact Bool.noConfusion)]
      rfl

theorem fcov_tb (t t2 q : ℕ) : ∀ as : List ℕ, ∀ a ∈ as,
    Nat.beq (Nat.land (priv t a) t2) 0 = true → a.testBit q = true →
    (fcov t t2 as).testBit q = true := by
  intro as
  induction as with
  | nil => intro a ha; simp at ha
  | cons b as ih =>
    intro a ha hb hq
    show (cond (Nat.beq (Nat.land (priv t b) t2) 0) (Nat.lor b (fcov t t2 as))
      (fcov t t2 as)).testBit q = true
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hb]
      show (Nat.lor a (fcov t t2 as)).testBit q = true
      rw [tb_lor, hq]
      rfl
    · have := ih a ha hb hq
      cases Nat.beq (Nat.land (priv t b) t2) 0
      · exact this
      · show (Nat.lor b (fcov t t2 as)).testBit q = true
        rw [tb_lor, this]
        exact Bool.or_true _

theorem item_tb1 (a h q : ℕ) (hh : (fld (put (Nat.land a full) 1 h) 1).testBit q = true) :
    h.testBit q = true := by
  rw [fld_tb, put_tb, tb_land, full_tb] at hh
  have e : 144 * 1 + q - 144 * 1 = q := by omega
  have e1 : decide (144 * 1 + q < 144) = false := decide_eq_false (by omega)
  rw [e, e1, Bool.and_false, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at hh
  exact hh.1.2

theorem item_tb0 (a h q : ℕ) (hq : q < 144) (ha : a.testBit q = true) :
    (fld (put (Nat.land a full) 1 h) 0).testBit q = true := by
  rw [fld_tb, put_tb, tb_land, full_tb]
  have e : 144 * 0 + q = q := by omega
  rw [e, ha, decide_eq_true hq]
  rfl

theorem beq0_false {n : ℕ} (h : Nat.beq n 0 = false) : n ≠ 0 := by
  intro e
  rw [e] at h
  exact Bool.noConfusion h

theorem beq0_of_ne {n : ℕ} (h : n ≠ 0) : Nat.beq n 0 = false := by
  cases n with
  | zero => exact (h rfl).elim
  | succ n => rfl

theorem classP3_of_lab (K t t2 : ℕ) (l : List ℕ) (c : ℕ → ℕ)
    (hle : ∀ x ∈ l, Nat.land (priv t (rectW x)) t2 ≠ 0 → c x ≤ K)
    (hne : l.Pairwise (fun x y => Nat.land (priv t (rectW x)) t2 ≠ 0 →
      Nat.land (priv t (rectW y)) t2 ≠ 0 → c x = c y →
      Nat.land (priv t (rectW x)) (priv t (rectW y)) = 0))
    (hcov : ∀ i U : ℕ, 1 ≤ i → i ≤ K →
      (∀ r, U.testBit r = true → ∃ x ∈ l, Nat.land (priv t (rectW x)) t2 ≠ 0 ∧ c x = i ∧
        (priv t (rectW x)).testBit r = true) →
      ∀ q, (hull U).testBit q = true → ∃ y ∈ l, (rectW y).testBit q = true ∧
        (Nat.land (priv t (rectW y)) t2 ≠ 0 → 1 ≤ c y ∧ c y ≤ i)) :
    classP3 K t t2 (l.map rectW) = true := by
  have hmem : ∀ p : ℕ × ℕ,
      p ∈ (l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
        (fun x => (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)) →
      ∃ x ∈ l, Nat.land (priv t (rectW x)) t2 ≠ 0 ∧
        p = (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x) := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
    refine ⟨x, hx1, ?_, rfl⟩
    apply beq0_false
    cases hb : Nat.beq (Nat.land (priv t (rectW x)) t2) 0
    · rfl
    · rw [hb] at hx2
      exact Bool.noConfusion hx2
  unfold classP3
  apply go_complete K _
    ((l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
      (fun x => (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)))
  · have e : ((l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
        (fun x => (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x))).map Prod.fst =
        vs t t2 (l.map rectW) := by
      rw [vs_eq, List.map_map]
      rfl
    rw [e]
    cases Nat.blt 1 K
    · exact List.Perm.refl _
    · exact sortD_perm _ _
  · intro p hp
    obtain ⟨x, hx, hc, rfl⟩ := hmem p hp
    exact hle x hx hc
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter _ hne)
    intro x y hx hy hxy hc
    have hx' := hmem _ (List.mem_map_of_mem (f := fun x =>
      (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)) hx)
    have hy' := hmem _ (List.mem_map_of_mem (f := fun x =>
      (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)) hy)
    obtain ⟨x', _, hcx, ex⟩ := hx'
    obtain ⟨y', _, hcy, ey⟩ := hy'
    have ex1 := congrArg Prod.fst ex
    have ey1 := congrArg Prod.fst ey
    have ex2 := congrArg Prod.snd ex
    have ey2 := congrArg Prod.snd ey
    have hcx' : Nat.land (priv t (rectW x)) t2 ≠ 0 := by
      have hx2 := (List.mem_filter.mp hx).2
      apply beq0_false
      cases hb : Nat.beq (Nat.land (priv t (rectW x)) t2) 0
      · rfl
      · rw [hb] at hx2
        exact Bool.noConfusion hx2
    have hcy' : Nat.land (priv t (rectW y)) t2 ≠ 0 := by
      have hy2 := (List.mem_filter.mp hy).2
      apply beq0_false
      cases hb : Nat.beq (Nat.land (priv t (rectW y)) t2) 0
      · rfl
      · rw [hb] at hy2
        exact Bool.noConfusion hy2
    have h0 := hxy hcx' hcy' hc
    apply land_disj
    intro q ha hb
    exact land_zero_tb _ _ q h0 (item_tb1 _ _ q ha) (item_tb1 _ _ q hb)
  · intro i hi1 hi2 q hq
    obtain ⟨U, hU, hUq⟩ := hq
    have hq144 : q < 144 := (hull_spec U q hUq).1
    obtain ⟨y, hy, hyq, hyc⟩ := hcov i U hi1 hi2 (by
      intro r hr
      obtain ⟨p, hp, hpi, hpr⟩ := hU r hr
      obtain ⟨x, hx, hc, rfl⟩ := hmem p hp
      exact ⟨x, hx, hc, hpi, item_tb1 _ _ r hpr⟩) q hUq
    cases hb : Nat.beq (Nat.land (priv t (rectW y)) t2) 0
    · right
      have hc := hyc (beq0_false hb)
      refine ⟨(put (Nat.land (rectW y) full) 1 (priv t (rectW y)), c y), ?_, hc.1, hc.2,
        item_tb0 _ _ q hq144 hyq⟩
      apply List.mem_map_of_mem
      apply List.mem_filter.mpr
      refine ⟨hy, ?_⟩
      rw [hb]
      rfl
    · left
      exact fcov_tb t t2 q _ (rectW y) (List.mem_map_of_mem hy) hb hyq

theorem classP_of_classLab (l : List ℕ) (k : ℕ) (c : ℕ → ℕ)
    (h : ClassLab l (Nat.sub (Nat.succ k) l.length) c) : classP l k = true :=
  classP3_of_lab _ _ _ l c h.le h.ne h.cov

theorem classP_of_validLab (l : List ℕ) (k : ℕ) (c : ℕ → ℕ) (hnd : l.Nodup)
    (h : ValidLab l (Nat.sub (Nat.succ k) l.length) c) : classP l k = true :=
  classP_of_classLab l k c (h.classLab hnd)


theorem classP'_of_validLab (l : List ℕ) (k : ℕ) (c : ℕ → ℕ) (hnd : l.Nodup)
    (h : ValidLab l (Nat.sub (Nat.succ k) l.length) c) : classP' l k = true := by
  rw [classP'_eq]
  exact classP_of_validLab l k c hnd h

/-- the checker's class rule is a sound pruning rule (with `reach_validLab` of ClassPartA). -/
theorem classP'_sound (m : Bool) : PruneOK m classP' := by
  intro l k hnd hR
  obtain ⟨c, hc⟩ := reach_validLab hnd hR
  exact classP'_of_validLab l k c hnd hc

theorem classP_sound (m : Bool) : PruneOK m classP := by
  intro l k hnd hR
  obtain ⟨c, hc⟩ := reach_validLab hnd hR
  exact classP_of_validLab l k c hnd hc

def T1 : Tree := .nil
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T1_ok : tall (expFast false (classP') BinaryTree.nil 0) T1 = true := by decide +kernel
def T2 : Tree := .nil
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T2_ok : tall (expFast false (classP') T1 1) T2 = true := by decide +kernel
def T3 : Tree := .nil
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T3_ok : tall (expFast false (classP') T2 2) T3 = true := by decide +kernel
def T4 : Tree := .nil
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T4_ok : tall (expFast false (classP') T3 3) T4 = true := by decide +kernel
def T5 : Tree := .nil
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T5_ok : tall (expFast false (classP') T4 4) T5 = true := by decide +kernel
def T6 : Tree := (.node [3395,506668,3275430,5689661,7684279,11083800,13501056] (.node [2726,902208,5689661,8827215,11083800,15875395,16010545] .nil .nil) .nil)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T6_ok : tall (expFast false (classP') T5 5) T6 = true := by decide +kernel
def T7 : Tree := (.node [2726,902208,5689661,8532035,8827215,11083800,15731968,16010545] (.node [134,2592,902208,5689661,8827215,11083800,15875395,16010545] (.node [67,3328,506668,3275430,5689661,7684279,11083800,13501056] .nil .nil) .nil) (.node [3395,113184,506668,3227782,5689661,7684279,11083800,13501056] .nil .nil))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T7_ok : tall (expFast false (classP') T6 6) T7 = true := by decide +kernel
def T8 : Tree := (.node [134,113184,902208,5689661,8827215,11083800,15875395,16010545,16666545] (.node [67,506668,1048428,3275430,5689661,7684279,11083800,13501056,15731968] (.node [67,3328,113184,506668,3227782,5689661,7684279,11083800,13501056] .nil .nil) (.node [134,2592,902208,5689661,8532035,8827215,11083800,15731968,16010545] .nil .nil)) (.node [3328,506668,3275430,5689661,7684279,8242423,8532035,11083800,13501056] (.node [2592,902208,3227782,5689661,8827215,11083800,13546447,15875395,16010545] .nil .nil) .nil))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T8_ok : tall (expFast false (classP') T7 7) T8 = true := by decide +kernel
def T9aa : Tree := (.node [1728,113184,430348,3227782,5521457,5689661,8532035,11083800,15731968,15875395] (.node [284,113184,902208,3227782,5521457,8532035,8632931,13501056,15731968,15814022] (.node [67,506668,902208,3275430,5689661,7684279,11083800,13501056,15731968] (.node [67,113184,506668,1037644,3227782,5689661,7684279,11083800,13501056,15731968] (.node [57,113184,430348,902208,3227782,8532035,8632931,13501056,15731968,15814022] (.node [24,430348,902208,3275430,5521457,8632931,13501056,15814022,15875395] .nil .nil) .nil) (.node [67,113184,506668,1048428,3227782,5689661,7684279,11083800,13501056,15731968] .nil .nil)) (.node [134,113184,902208,5689661,8532035,8827215,11083800,15731968,16010545,16666545] (.node [134,113184,902208,5689661,8532035,8827215,11083800,14566065,15731968,16010545] .nil .nil) (.node [134,113184,902208,5689661,8827215,11083800,13501056,15875395,16010545] .nil .nil))) (.node [1088,506668,3275430,5689661,7684279,8532035,11083800,13501056,15731968] (.node [664,113184,430348,902208,3227782,3275430,5521457,8532035,15731968,15875395] (.node [640,113184,902208,3227782,5689661,8827215,11083800,15875395,16010545] .nil .nil) (.node [664,113184,430348,902208,3227782,5521457,5689661,8532035,15731968,15875395] .nil .nil)) (.node [1112,113184,430348,3227782,3275430,5521457,8532035,13501056,15731968,15875395] (.node [1112,113184,430348,3227782,3275430,5521457,5689661,8532035,13501056,15731968] .nil .nil) (.node [1728,113184,430348,3227782,3275430,5521457,5689661,8532035,11083800,15731968] .nil .nil)))) (.node [113184,430348,902208,3227782,3275430,5521457,8532059,13501056,15731992,15875419] (.node [3328,113184,506668,3227782,5689661,6145137,7684279,8532035,11083800,13501056] (.node [2592,902208,3227782,5689661,8532035,8827215,11083800,13546447,15731968,16010545] (.node [2592,902208,3227782,5689661,8532035,8827215,11083800,13538188,15731968,16010545] .nil .nil) (.node [2592,902208,3227782,5689661,8827215,11083800,13501056,15875395,16010545] .nil .nil)) (.node [3328,506668,902208,3275430,5689661,7684279,8532035,11083800,13501056] (.node [3328,113184,506668,3227782,5689661,7684279,8242423,8532035,11083800,13501056] .nil .nil) (.node [113184,430348,902208,3227782,3275430,5521457,8532059,13501056,15731992,15875395] .nil .nil))) (.node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,15732480,15875395] (.node [113184,430348,902208,3227782,3275430,5521465,8532059,13501056,15731968,15875419] (.node [113184,430348,902208,3227782,3275430,5521465,8532059,13501056,15731968,15875395] .nil .nil) (.node [113184,430348,902208,3227782,3275454,5521457,8532035,13501080,15731968,15875395] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,15732480,15875907] (.node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,15732480,15875523] .nil .nil) (.node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,15732480,15876035] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T9aa_ok : tall (expFast false (classP') T8 8) T9aa = true := by decide +kernel
def T9ab : Tree := (.node [113184,430348,902208,3227806,5521457,8532035,8632931,13501080,15731968,15814022] (.node [113184,430348,902208,3227782,5521969,5689661,8532163,11083800,15731968,15875523] (.node [113184,430348,902208,3227782,5521457,8532059,8632955,13501056,15731968,15814046] (.node [113184,430348,902208,3227782,5521457,8532035,8632955,13501056,15731968,15814046] (.node [113184,430348,902208,3227782,5521457,5690301,8532035,11084440,15731968,15875395] (.node [113184,430348,902208,3227782,5521457,5689661,8532675,11083800,15732608,15876035] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632955,13501056,15731992,15814046] .nil .nil)) (.node [113184,430348,902208,3227782,5521465,8532035,8632955,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532059,8632955,13501056,15731992,15814046] .nil .nil) (.node [113184,430348,902208,3227782,5521465,8532059,8632955,13501056,15731968,15814022] .nil .nil))) (.node [113184,430348,902208,3227806,3275430,5521457,8532059,13501056,15731968,15875419] (.node [113184,430348,902208,3227782,5522097,5689661,8532675,11083800,15731968,15876035] (.node [113184,430348,902208,3227782,5522097,5689661,8532675,11083800,15731968,15875395] .nil .nil) (.node [113184,430348,902208,3227806,3275430,5521457,8532059,13501056,15731968,15875395] .nil .nil)) (.node [113184,430348,902208,3227806,3275454,5521457,8532059,13501056,15731968,15875395] (.node [113184,430348,902208,3227806,3275454,5521457,8532035,13501080,15731968,15875395] .nil .nil) (.node [113184,430348,902208,3227806,3275454,5521457,8532059,13501056,15731968,15875419] .nil .nil)))) (.node [113184,430348,902232,3227782,3275430,5521457,8532059,13501056,15731968,15875419] (.node [113184,430348,902208,3228294,5521457,5689661,8532675,11083800,15731968,15875395] (.node [113184,430348,902208,3227806,5521457,8532035,8632955,13501056,15731968,15814046] (.node [113184,430348,902208,3227806,5521457,8532035,8632931,13501080,15731968,15814046] .nil .nil) (.node [113184,430348,902208,3227806,5521457,8532059,8632955,13501056,15731968,15814046] .nil .nil)) (.node [113184,430348,902232,3227782,3275430,5521457,8532035,13501056,15731968,15875419] (.node [113184,430348,902208,3228294,5521457,5689661,8532675,11083800,15731968,15876035] .nil .nil) (.node [113184,430348,902232,3227782,3275430,5521457,8532035,13501056,15731992,15875419] .nil .nil))) (.node [113184,430348,902232,3227782,5521457,8532059,8632955,13501056,15731968,15814022] (.node [113184,430348,902232,3227782,5521457,8532035,8632931,13501056,15731992,15814046] (.node [113184,430348,902232,3227782,5521457,8532035,8632931,13501056,15731992,15814022] .nil .nil) (.node [113184,430348,902232,3227782,5521457,8532059,8632931,13501056,15731968,15814022] .nil .nil)) (.node [113184,430348,902848,3227782,5521457,5689661,8532035,11083800,15732608,15876035] (.node [113184,430348,902848,3227782,5521457,5689661,8532035,11083800,15731968,15876035] .nil .nil) (.node [113184,430348,902848,3227782,5521457,5689661,8532675,11083800,15731968,15876035] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T9ab_ok : tall (expFast false (classP') T8 8) T9ab = true := by decide +kernel
def T9a : Tree := .node [113184,430348,902208,3227782,5521457,5689661,8532675,11083800,15732608,15875395] T9aa T9ab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T9a_ok : tall (expFast false (classP') T8 8) T9a = true :=
  tall_node _ _ _ _ T9aa_ok (by decide +kernel) T9ab_ok
def T9ba : Tree := (.node [113184,430988,902208,3227782,5522097,5689661,8532035,11083800,15731968,15875395] (.node [113184,430364,902208,3227782,5521457,8532035,8632931,13501056,15731992,15814046] (.node [113184,430348,3228870,3276518,5521457,5689661,8533059,11083800,13501056,15731968] (.node [113184,430348,3228870,3275430,5521457,5689661,8533059,11083800,13501056,15731968] (.node [113184,430348,3227782,3276518,5521457,5689661,8532035,11083800,13502144,15731968] (.node [113184,430348,3227782,3275430,5522545,5689661,8533059,11083800,13501056,15731968] .nil .nil) .nil) (.node [113184,430348,3228870,3276518,5521457,5689661,8532035,11083800,13502144,15731968] .nil .nil)) (.node [113184,430364,902208,3227782,3275430,5521457,8532035,13501056,15731992,15875419] (.node [113184,430364,902208,3227782,3275430,5521457,8532035,13501056,15731992,15875395] .nil .nil) (.node [113184,430364,902208,3227782,5521457,8532035,8632931,13501056,15731968,15814046] .nil .nil))) (.node [113184,430476,902208,3227782,5521457,5689661,8532035,11083800,15732480,15875907] (.node [113184,430364,902208,3227806,3275454,5521457,8532035,13501056,15731968,15875395] (.node [113184,430364,902208,3227806,3275430,5521457,8532035,13501056,15731968,15875395] .nil .nil) (.node [113184,430364,902208,3227806,5521457,8532035,8632931,13501056,15731968,15814046] .nil .nil)) (.node [113184,430988,902208,3227782,5521457,5689661,8532035,11083800,15732608,15875395] (.node [113184,430476,902208,3227782,5521969,5689661,8532035,11083800,15731968,15875395] .nil .nil) (.node [113184,430988,902208,3227782,5521457,5689661,8532035,11083800,15732608,15876035] .nil .nil)))) (.node [113184,902208,3227782,5689661,8532035,8632931,11084060,13501056,15731968,16076215] (.node [113184,431436,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15732032] (.node [113184,431372,3227782,3275430,5521521,5689661,8532035,11083800,13501056,15731968] (.node [113184,430988,902208,3228294,5521457,5689661,8532035,11083800,15731968,15875395] .nil .nil) (.node [113184,431372,3227846,3275494,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,431436,3228870,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,431436,3227782,3275430,5522545,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,431436,3228870,3276518,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil))) (.node [113184,902208,3227782,5689661,8532035,8895343,11083833,13501056,15731968,15814022] (.node [113184,902208,3227782,5689661,8532035,8895343,11083800,13501056,15731968,15814055] (.node [113184,902208,3227782,5689661,8532035,8633191,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,902208,3227782,5689661,8532035,8895343,11083800,13501056,15732001,15814055] .nil .nil)) (.node [113184,902208,3227782,5689661,8827215,11083800,13546447,15875395,16010545,16666545] (.node [113184,902208,3227782,5689661,8532295,8633191,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,902208,3227815,5689661,8532035,8895343,11083800,13501056,15731968,15814055] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T9ba_ok : tall (expFast false (classP') T8 8) T9ba = true := by decide +kernel
def T9bb : Tree := (.node [113312,430348,902208,3227782,5521457,5689661,8532035,11083800,15732608,15876035] (.node [113208,430348,902208,3227782,5521457,8532035,8632955,13501056,15731968,15814046] (.node [113208,430348,902208,3227782,3275454,5521457,8532035,13501056,15731992,15875419] (.node [113208,430348,902208,3227782,3275430,5521465,8532035,13501056,15731968,15875395] (.node [113208,430348,902208,3227782,3275430,5521457,8532035,13501056,15731992,15875419] .nil .nil) (.node [113208,430348,902208,3227782,3275454,5521457,8532035,13501056,15731992,15875395] .nil .nil)) (.node [113208,430348,902208,3227782,3275454,5521465,8532035,13501056,15731968,15875395] (.node [113208,430348,902208,3227782,3275454,5521457,8532035,13501080,15731968,15875395] .nil .nil) (.node [113208,430348,902208,3227782,5521457,8532035,8632931,13501080,15731968,15814022] .nil .nil))) (.node [113208,430348,902208,3227806,3275430,5521457,8532035,13501056,15731968,15875395] (.node [113208,430348,902208,3227782,5521457,8532035,8632955,13501080,15731968,15814022] (.node [113208,430348,902208,3227782,5521457,8532035,8632955,13501056,15731992,15814046] .nil .nil) (.node [113208,430348,902208,3227782,5521465,8532035,8632955,13501056,15731968,15814022] .nil .nil)) (.node [113208,430348,902208,3227806,5521457,8532035,8632955,13501056,15731968,15814046] (.node [113208,430348,902208,3227806,3275454,5521457,8532035,13501056,15731968,15875395] .nil .nil) (.node [113312,430348,902208,3227782,5521457,5689661,8532035,11083800,15732608,15875395] .nil .nil)))) (.node [114272,430348,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15732032] (.node [114208,430348,3227846,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113444,902208,3227782,5689661,8532035,8633191,11083800,13501056,15731968,16076215] (.node [113312,430348,902208,3227782,5522097,5689661,8532035,11083800,15731968,15875395] .nil .nil) (.node [114208,430348,3227782,3276454,5521521,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [114208,430348,3227846,3276454,5521457,5689661,8532035,11083800,13501056,15731968] (.node [114208,430348,3227846,3275494,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [114208,430348,3227846,3276518,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil))) (.node [114272,430348,3227782,3276518,5522545,5689661,8532035,11083800,13501056,15731968] (.node [114272,430348,3227782,3276518,5521457,5689661,8532035,11083800,13501056,15732032] (.node [114272,430348,3227782,3275430,5522545,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [114272,430348,3227782,3276518,5521457,5689661,8532035,11083800,13502144,15731968] .nil .nil)) (.node [114272,430348,3228870,3276518,5521457,5689661,8532035,11083800,13501056,15731968] (.node [114272,430348,3228870,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [506668,1048428,3275430,5689661,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T9bb_ok : tall (expFast false (classP') T8 8) T9bb = true := by decide +kernel
def T9b : Tree := .node [113208,430348,902208,3227782,3275430,5521457,8532035,13501056,15731992,15875395] T9ba T9bb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T9b_ok : tall (expFast false (classP') T8 8) T9b = true :=
  tall_node _ _ _ _ T9ba_ok (by decide +kernel) T9bb_ok
def T9 : Tree := .node [113184,430348,3227782,3275430,5521457,5690749,8532035,11084888,13501056,15731968] T9a T9b
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T9_ok : tall (expFast false (classP') T8 8) T9 = true :=
  tall_node _ _ _ _ T9a_ok (by decide +kernel) T9b_ok
def T10aaaa : Tree := (.node [24,113184,430348,902208,3227782,3275430,5521465,8532035,13501056,15731968,15875395] (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501056,15731968,15875419] (.node [24,640,113184,430348,902208,3227782,5521457,5689661,8532035,15731968,15875395] (.node [24,260,113184,902208,3227782,5521457,8532035,8632931,13501056,15731968,15814022] (.node [24,33,113184,430348,902208,3227782,8532035,8632931,13501056,15731968,15814022] .nil .nil) (.node [24,640,113184,430348,902208,3227782,3275430,5521457,8532035,15731968,15875395] .nil .nil)) (.node [24,1088,113184,430348,3227782,3275430,5521457,8532035,13501056,15731968,15875395] (.node [24,1088,113184,430348,3227782,3275430,5521457,5689661,8532035,13501056,15731968] .nil .nil) .nil)) (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501080,15731968,15875395] (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501056,15731992,15875419] (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501056,15731992,15875395] .nil .nil) .nil) (.node [24,113184,430348,902208,3227782,3275430,5521457,8532059,13501056,15731968,15875419] (.node [24,113184,430348,902208,3227782,3275430,5521457,8532059,13501056,15731968,15875395] .nil .nil) .nil))) (.node [24,113184,430348,902208,3227782,5521457,8532059,8632931,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501056,15731992,15814046] (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501056,15731968,15814046] (.node [24,113184,430348,902208,3227782,3275454,5521457,8532035,13501056,15731968,15875395] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501056,15731992,15814022] .nil .nil)) (.node [24,113184,430348,902208,3227782,5521457,8532035,8632955,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501080,15731968,15814022] .nil .nil) .nil)) (.node [24,113184,430348,902208,3227782,5521465,8532035,8632931,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227782,5521457,8632931,13501056,15814022,15875395] (.node [24,113184,430348,902208,3227782,5521457,8532059,8632955,13501056,15731968,15814022] .nil .nil) .nil) (.node [24,113184,430348,902208,3227806,3275454,5521457,8532035,13501056,15731968,15875395] (.node [24,113184,430348,902208,3227806,3275430,5521457,8532035,13501056,15731968,15875395] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10aaaa_ok : tall (expFast false (classP') T9 9) T10aaaa = true := by decide +kernel
def T10aaab : Tree := (.node [33,113184,902208,3227782,5689661,8532035,8895343,11083800,13501056,15731968,15814022] (.node [24,113208,430348,902208,3227782,3275430,5521457,8532035,13501056,15731968,15875395] (.node [24,113184,430348,902232,3227782,5521457,8532035,8632931,13501056,15731968,15814022] (.node [24,113184,430348,902208,3275430,5521457,8532035,13501056,15814022,15875395] (.node [24,113184,430348,902208,3227806,5521457,8532035,8632931,13501056,15731968,15814046] .nil .nil) (.node [24,113184,430348,902232,3227782,3275430,5521457,8532035,13501056,15731968,15875395] .nil .nil)) (.node [24,113184,430364,902208,3227782,5521457,8532035,8632931,13501056,15731968,15814022] (.node [24,113184,430364,902208,3227782,3275430,5521457,8532035,13501056,15731968,15875395] .nil .nil) .nil)) (.node [24,113208,430348,902208,3227782,5521457,8532035,8632955,13501056,15731968,15814022] (.node [24,113208,430348,902208,3227782,5521457,8532035,8632931,13501056,15731968,15814022] (.node [24,113208,430348,902208,3227782,3275454,5521457,8532035,13501056,15731968,15875395] .nil .nil) .nil) (.node [24,430348,902208,3275430,5521457,8532035,8632931,13501056,15731968,15814022] (.node [24,430348,902208,3227782,3275430,5521457,8632931,13501056,15731968,15875395] .nil .nil) .nil))) (.node [67,113184,430348,506668,902208,3227782,5521457,7684279,11083800,13501056,15731968] (.node [64,113184,431372,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [57,113184,430348,902208,3227782,8532035,8632931,13501056,15731968] (.node [49,113184,430348,902208,3227782,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil) .nil) (.node [64,114208,430348,3227782,3276454,5521457,5689661,8532035,11083800,13501056,15731968] (.node [64,114208,430348,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [67,113184,430348,1037644,3227782,5689661,7684279,11083800,13501056,15731968] (.node [67,113184,430348,902208,3275430,5689661,7684279,11083800,13501056,15731968] (.node [67,113184,430348,506668,902208,3227782,5689661,7684279,11083800,13501056,15731968] .nil .nil) .nil) (.node [128,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15732480,15875395] (.node [67,113184,506668,902208,3227782,5689661,7684279,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10aaab_ok : tall (expFast false (classP') T9 9) T10aaab = true := by decide +kernel
def T10aaa : Tree := .node [24,113184,430348,902208,3227806,5521457,8532035,8632931,13501056,15731968,15814022] T10aaaa T10aaab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10aaa_ok : tall (expFast false (classP') T9 9) T10aaa = true :=
  tall_node _ _ _ _ T10aaaa_ok (by decide +kernel) T10aaab_ok
def T10aaba : Tree := (.node [640,1088,113184,430348,3227782,3275430,5521457,5689661,8532035,11083800,15731968] (.node [260,113184,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,16076215] (.node [134,113184,902208,5521457,5689661,8532035,8827215,11083800,14566065,15731968] (.node [134,113184,430348,902208,5521457,8532035,8827215,11083800,13501056,15731968,16010545] (.node [128,113184,430348,902208,3227782,5521969,5689661,8532035,11083800,15731968,15875395] .nil .nil) (.node [134,113184,902208,5521457,5689661,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil)) (.node [134,113184,902208,5689661,8532035,8827215,11083800,13501056,15731968,16010545] (.node [134,113184,902208,5521457,5689661,8827215,11083800,13501056,15731968,15875395] .nil .nil) .nil)) (.node [512,113184,430348,902208,3227782,5521457,5689661,8532163,11083800,15731968,15875395] (.node [284,113184,902208,3227782,5521457,8532035,13501056,15731968,15814022] (.node [268,113184,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil) .nil) (.node [512,113184,430476,902208,3227782,5521457,5689661,8532035,11083800,15731968,15875395] (.node [512,113184,430348,902208,3227782,5521457,5689661,8532163,11083800,15731968,15875523] .nil .nil) .nil))) (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11084440,15731968,15875395] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968,15876035] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968,15875395] (.node [640,1088,113184,430348,3227782,5521457,5689661,8532035,11083800,15731968,15875395] .nil .nil) .nil) (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15732608,15876035] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15732608,15875395] .nil .nil) .nil)) (.node [640,113184,430348,902208,3227782,5521457,5690301,8532035,11083800,15731968,15875395] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532675,11083800,15731968,15876035] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532675,11083800,15731968,15875395] .nil .nil) .nil) (.node [640,113184,430348,902208,3227782,5522097,5689661,8532035,11083800,15731968,15875395] (.node [640,113184,430348,902208,3227782,5521457,8532035,8827215,11083800,15731968,16010545] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10aaba_ok : tall (expFast false (classP') T9 9) T10aaba = true := by decide +kernel
def T10aabb : Tree := (.node [1088,113184,430348,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [664,113184,430348,902208,3227782,3275430,5521457,8532035,15731968] (.node [640,113184,902208,3227782,5521457,5689661,8827215,11083800,15731968,15875395] (.node [640,113184,430348,902848,3227782,5521457,5689661,8532035,11083800,15731968,15875395] (.node [640,113184,430348,902208,3228294,5521457,5689661,8532035,11083800,15731968,15875395] .nil .nil) (.node [640,113184,430988,902208,3227782,5521457,5689661,8532035,11083800,15731968,15875395] .nil .nil)) (.node [640,113312,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968,15875395] (.node [640,113184,902208,3227782,5689661,8532035,8827215,11083800,15731968,16010545] .nil .nil) .nil)) (.node [1024,113184,430348,3227846,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,3227782,3275430,5521521,5689661,8532035,11083800,13501056,15731968] (.node [664,113184,430348,902208,3227782,5521457,5689661,8532035,15731968] .nil .nil) .nil) (.node [1088,113184,430348,506668,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,3227846,3275494,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [1088,113184,430348,3227782,3275430,5522545,5689661,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,3275430,5521457,5689661,8532035,11084888,13501056,15731968] (.node [1088,113184,430348,3227782,3275430,5521457,5689661,8532035,11083800,13502144,15731968] (.node [1088,113184,430348,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15732032] .nil .nil) .nil) (.node [1088,113184,430348,3227782,3275430,5521457,5690749,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,3275430,5521457,5689661,8533059,11083800,13501056,15731968] .nil .nil) .nil)) (.node [1088,113184,430348,3228870,3276518,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3228870,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,3276518,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [1088,113184,431436,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3275430,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10aabb_ok : tall (expFast false (classP') T9 9) T10aabb = true := by decide +kernel
def T10aab : Tree := .node [640,113184,430348,902208,3227782,5689661,8532035,11083800,15875395,16010545] T10aaba T10aabb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10aab_ok : tall (expFast false (classP') T9 9) T10aab = true :=
  tall_node _ _ _ _ T10aaba_ok (by decide +kernel) T10aabb_ok
def T10aa : Tree := .node [128,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15732480,15875907] T10aaa T10aab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10aa_ok : tall (expFast false (classP') T9 9) T10aa = true :=
  tall_node _ _ _ _ T10aaa_ok (by decide +kernel) T10aab_ok
def T10abaa : Tree := (.node [3328,113184,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056] (.node [2592,430348,902208,3227782,5689661,8532035,8827215,11083800,13501056,15731968,16010545] (.node [1112,113184,430348,3227782,5521457,5689661,8532035,13501056,15731968] (.node [1088,114272,430348,3227782,3276518,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1088,114272,430348,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [1088,506668,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [2592,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545] (.node [1112,113184,430348,3227782,5521457,8532035,13501056,15731968,15875395] .nil .nil) .nil)) (.node [2592,902208,3227782,5689661,8532035,8827215,11083800,13501056,15731968,16010545] (.node [2592,430348,902208,3227782,5689661,8532035,11083800,13538188,15731968,16010545] (.node [2592,430348,902208,3227782,5689661,8532035,11083800,13501056,15875395,16010545] .nil .nil) .nil) (.node [3328,113184,506668,902208,3227782,5521457,5689661,7684279,8532035,11083800,13501056] (.node [3328,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056] .nil .nil) .nil))) (.node [113184,113208,430348,902208,3227782,5521457,8532035,13501056,15731992,15875395] (.node [113184,113208,430348,902208,3227782,3227806,5521457,8532035,13501056,15731968,15875395] (.node [3328,506668,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056] (.node [3328,113184,506668,3227782,5521457,5689661,6145137,8532035,11083800,13501056] .nil .nil) .nil) (.node [113184,113208,430348,902208,3227782,5521457,8532035,13501056,15731992,15814046] (.node [113184,113208,430348,902208,3227782,5521457,8532035,13501056,15731968,15814046] .nil .nil) .nil)) (.node [113184,113208,430348,902208,3227782,5521457,8532035,13501080,15731968,15875395] (.node [113184,113208,430348,902208,3227782,5521457,8532035,13501080,15731968,15814022] (.node [113184,113208,430348,902208,3227782,5521457,8532035,13501056,15731992,15875419] .nil .nil) .nil) (.node [113184,113208,430348,902208,3227782,5521465,8532035,13501056,15731968,15875395] (.node [113184,113208,430348,902208,3227782,5521465,8532035,13501056,15731968,15814022] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10abaa_ok : tall (expFast false (classP') T9 9) T10abaa = true := by decide +kernel
def T10abab : Tree := (.node [113184,430348,506668,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] (.node [113184,114272,430348,3227782,5521457,5689661,8532035,11083800,13501056,15732032] (.node [113184,114208,430348,3227782,5521521,5689661,8532035,11083800,13501056,15731968] (.node [113184,113444,902208,3227782,5689661,8532035,11083800,13501056,15731968,16076215] (.node [113184,113208,430348,902208,3227806,5521457,8532035,13501056,15731968,15875395] .nil .nil) (.node [113184,114208,430348,3227782,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,114272,430348,3227782,3228870,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,114208,430348,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,114272,430348,3228870,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,114272,430348,3227782,5522545,5689661,8532035,11083800,13501056,15731968] (.node [113184,114272,430348,3227782,5521457,5689661,8532035,11083800,13502144,15731968] .nil .nil) .nil) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,3227806,5521457,8532035,8632931,13501080,15731968] (.node [113184,430348,506668,902208,3227846,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521521,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [113184,430348,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227846,5521457,7684343,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,3227806,5521457,8532059,8632955,13501056,15731968] (.node [113184,430348,902208,3227782,3227806,5521457,8532035,13501080,15731968,15875395] (.node [113184,430348,902208,3227782,3227806,5521457,8532035,8632955,13501056,15731968] .nil .nil) .nil) (.node [113184,430348,902208,3227782,3227806,5521457,8532059,13501056,15731968,15875419] (.node [113184,430348,902208,3227782,3227806,5521457,8532059,13501056,15731968,15875395] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10abab_ok : tall (expFast false (classP') T9 9) T10abab = true := by decide +kernel
def T10aba : Tree := .node [113184,113208,430348,902208,3227806,5521457,8532035,13501056,15731968,15814046] T10abaa T10abab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10aba_ok : tall (expFast false (classP') T9 9) T10aba = true :=
  tall_node _ _ _ _ T10abaa_ok (by decide +kernel) T10abab_ok
def T10abba : Tree := (.node [113184,430348,902208,3227782,5521457,5689661,8532675,11083800,15731968,15732608] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8532163,11083800,15731968,15732480] (.node [113184,430348,902208,3227782,3275430,5521465,8532035,8532059,13501056,15731968] (.node [113184,430348,902208,3227782,3275430,5521457,8532059,13501056,15731968,15731992] (.node [113184,430348,902208,3227782,3275430,5521457,8532035,8532059,13501056,15731992] .nil .nil) (.node [113184,430348,902208,3227782,3275430,5521457,8532059,13501056,15731992] .nil .nil)) (.node [113184,430348,902208,3227782,3275454,5521457,8532035,13501080,15731968] (.node [113184,430348,902208,3227782,3275430,5521465,8532059,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8532675,11083800,15732608] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8532675,11083800,15731968,15732608] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8532163,11083800,15732480] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,15732480] (.node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,15731968,15732480] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814046] (.node [113184,430348,902208,3227782,5521457,8532035,8532059,13501056,15731968,15814046] (.node [113184,430348,902208,3227782,5521457,5690301,8532035,11084440,15731968] (.node [113184,430348,902208,3227782,5521457,5689661,8532675,11083800,15732608] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814030] (.node [113184,430348,902208,3227782,5521457,8532035,8532059,13501056,15731992,15814046] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731992,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731976,15814030] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731976,15814022] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632947,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731992,15814046] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10abba_ok : tall (expFast false (classP') T9 9) T10abba = true := by decide +kernel
def T10abbb : Tree := (.node [113184,430348,902208,3227782,5521457,8532059,13501056,15731968,15814046] (.node [113184,430348,902208,3227782,5521457,8532051,8632931,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15732480,16010545] (.node [113184,430348,902208,3227782,5521457,8532035,8632955,13501056,15731992] (.node [113184,430348,902208,3227782,5521457,8532035,8632955,13501056,15731968,15731992] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16011057] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8827343,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15732480,16011057] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,8532059,8632955,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532059,8632931,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532051,8632947,11083800,13501056,15731968,15814022] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5521457,8532059,8632955,13501056,15731992] (.node [113184,430348,902208,3227782,5521457,8532059,8632955,13501056,15731968,15731992] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5521465,8532035,8532059,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532059,13501056,15731992,15875419] (.node [113184,430348,902208,3227782,5521457,8532059,13501056,15731992,15875395] (.node [113184,430348,902208,3227782,5521457,8532059,13501056,15731992,15814046] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5521457,8532163,8827343,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5521457,8532163,8827215,11083800,13501056,15731968,16010545] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521465,8532059,8632955,13501056,15731968] (.node [113184,430348,902208,3227782,5521465,8532035,8632955,13501056,15731968] (.node [113184,430348,902208,3227782,5521465,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5521465,8532059,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,5521465,8532059,13501056,15731968,15814022] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10abbb_ok : tall (expFast false (classP') T9 9) T10abbb = true := by decide +kernel
def T10abb : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8632955,11083800,13501056,15731968,15814022] T10abba T10abbb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10abb_ok : tall (expFast false (classP') T9 9) T10abb = true :=
  tall_node _ _ _ _ T10abba_ok (by decide +kernel) T10abbb_ok
def T10ab : Tree := .node [113184,430348,902208,3227782,3275430,5521457,8532035,8532059,13501056,15731968,15731992] T10aba T10abb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10ab_ok : tall (expFast false (classP') T9 9) T10ab = true :=
  tall_node _ _ _ _ T10aba_ok (by decide +kernel) T10abb_ok
def T10a : Tree := .node [1088,113184,506668,3227782,5689661,7684279,8532035,11083800,13501056,15731968] T10aa T10ab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10a_ok : tall (expFast false (classP') T9 9) T10a = true :=
  tall_node _ _ _ _ T10aa_ok (by decide +kernel) T10ab_ok
def T10baaa : Tree := (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13538188,15731968,16011057] (.node [113184,430348,902208,3227782,5689661,8456227,8532035,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521969,8532035,8827215,11083800,13501056,15731968,16011057] (.node [113184,430348,902208,3227782,5521969,5689661,8532163,11083800,15731968] (.node [113184,430348,902208,3227782,5521969,5689661,8532035,8532163,11083800,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521969,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil)) (.node [113184,430348,902208,3227782,5522097,5689661,8532675,11083800,15731968] (.node [113184,430348,902208,3227782,5522097,5689661,8532035,8532675,11083800,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083833,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15732001,15814055] (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,15814055] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15875907,16011057] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15875395,16011057] .nil .nil) .nil))) (.node [113184,430348,902208,3227806,3275454,5521457,8532035,13501080,15731968] (.node [113184,430348,902208,3227806,3275430,5521457,8532035,8532059,13501056,15731968] (.node [113184,430348,902208,3227790,5521457,8532035,8632931,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13538188,15732480,16011057] .nil .nil) (.node [113184,430348,902208,3227790,5521457,8532035,8632931,11083800,13501056,15731968,15814030] .nil .nil)) (.node [113184,430348,902208,3227806,3275454,5521457,8532035,8532059,13501056,15731968] (.node [113184,430348,902208,3227806,3275430,5521457,8532059,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227806,5521457,8532035,8632931,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227806,5521457,8532035,8532059,13501056,15731968,15814046] (.node [113184,430348,902208,3227806,3275454,5521457,8532059,13501056,15731968] .nil .nil) .nil) (.node [113184,430348,902208,3227806,5521457,8532035,8632931,13501080,15731968] (.node [113184,430348,902208,3227806,5521457,8532035,8632931,11083800,13501056,15731968,15814046] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10baaa_ok : tall (expFast false (classP') T9 9) T10baaa = true := by decide +kernel
def T10baab : Tree := (.node [113184,430348,902208,3228294,5689661,8532035,11083800,13538188,15731968,16010545] (.node [113184,430348,902208,3227806,5521457,8532059,13501056,15731968,15875419] (.node [113184,430348,902208,3227806,5521457,8532059,8632955,13501056,15731968] (.node [113184,430348,902208,3227806,5521457,8532035,13501080,15731968,15814046] (.node [113184,430348,902208,3227806,5521457,8532035,13501080,15731968,15814022] .nil .nil) (.node [113184,430348,902208,3227806,5521457,8532035,13501080,15731968,15875395] .nil .nil)) (.node [113184,430348,902208,3227806,5521457,8532059,13501056,15731968,15875395] (.node [113184,430348,902208,3227806,5521457,8532059,13501056,15731968,15814046] .nil .nil) .nil)) (.node [113184,430348,902208,3228294,5521457,5689661,8532675,11083800,15731968] (.node [113184,430348,902208,3228294,5521457,5689661,8532035,8532675,11083800,15731968] (.node [113184,430348,902208,3227815,5689661,8532035,8632931,11083800,13501056,15731968,15814055] .nil .nil) .nil) (.node [113184,430348,902208,3228294,5689661,8532035,11083800,13501056,15875395,16010545] (.node [113184,430348,902208,3228294,5521457,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil) .nil))) (.node [113184,430348,902232,3227782,3275430,5521457,8532035,13501056,15731968,15731992] (.node [113184,430348,902208,3275430,5689661,8532035,11083800,13501056,15875395,16076215] (.node [113184,430348,902208,3275430,5689661,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3275430,5689661,7684279,8532035,11083800,13501056,15732032] .nil .nil) .nil) (.node [113184,430348,902232,3227782,3275430,5521457,8532035,8532059,13501056,15731968] (.node [113184,430348,902208,3275494,5689661,7684343,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902232,3227782,5521457,8532035,8532059,13501056,15731968,15814022] (.node [113184,430348,902232,3227782,3275430,5521457,8532059,13501056,15731968] (.node [113184,430348,902232,3227782,3275430,5521457,8532035,13501056,15731992] .nil .nil) .nil) (.node [113184,430348,902232,3227782,5521457,8532035,8632931,13501056,15731992] (.node [113184,430348,902232,3227782,5521457,8532035,8632931,13501056,15731968,15731992] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10baab_ok : tall (expFast false (classP') T9 9) T10baab = true := by decide +kernel
def T10baa : Tree := .node [113184,430348,902208,3227806,5521457,8532035,8632955,13501056,15731968] T10baaa T10baab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10baa_ok : tall (expFast false (classP') T9 9) T10baa = true :=
  tall_node _ _ _ _ T10baaa_ok (by decide +kernel) T10baab_ok
def T10baba : Tree := (.node [113184,430348,1037644,3227782,5689661,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,902232,3227782,5521457,8532059,13501056,15731968,15875419] (.node [113184,430348,902232,3227782,5521457,8532059,8632931,13501056,15731968] (.node [113184,430348,902232,3227782,5521457,8532035,13501056,15731992,15814046] (.node [113184,430348,902232,3227782,5521457,8532035,13501056,15731992,15814022] .nil .nil) (.node [113184,430348,902232,3227782,5521457,8532035,13501056,15731992,15875419] .nil .nil)) (.node [113184,430348,902232,3227782,5521457,8532059,13501056,15731968,15814022] (.node [113184,430348,902232,3227782,5521457,8532059,8632955,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902848,3227782,5521457,5689661,8532035,11083800,15732608] (.node [113184,430348,902848,3227782,5521457,5689661,8532035,11083800,15731968,15732608] (.node [113184,430348,902848,3227782,5521457,5689661,8532035,8532675,11083800,15731968] .nil .nil) .nil) (.node [113184,430348,1037644,3227782,5689661,7684279,8532035,11083800,13501056,15732032] (.node [113184,430348,902848,3227782,5521457,5689661,8532675,11083800,15731968] .nil .nil) .nil))) (.node [113184,430348,3228870,5521457,5689661,8532035,11083800,13502144,15731968] (.node [113184,430348,3227782,3228870,5521457,5689661,8533059,11083800,13501056,15731968] (.node [113184,430348,3227782,3228870,5521457,5689661,8532035,11083800,13502144,15731968] (.node [113184,430348,1037644,3227846,5689661,7684343,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [113184,430348,3227782,5522545,5689661,8533059,11083800,13501056,15731968] (.node [113184,430348,3227782,5521457,5690749,8532035,11084888,13501056,15731968] .nil .nil) .nil)) (.node [113184,430364,902208,3227782,3227806,5521457,8532035,13501056,15731968,15875395] (.node [113184,430364,902208,3227782,3227806,5521457,8532035,8632931,13501056,15731968] (.node [113184,430348,3228870,5521457,5689661,8533059,11083800,13501056,15731968] .nil .nil) .nil) (.node [113184,430364,902208,3227782,3275430,5521457,8532035,13501056,15731992] (.node [113184,430364,902208,3227782,3275430,5521457,8532035,13501056,15731968,15731992] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10baba_ok : tall (expFast false (classP') T9 9) T10baba = true := by decide +kernel
def T10babb : Tree := (.node [113184,430476,902208,3227782,5521457,5689661,8532035,11083800,15732480] (.node [113184,430364,902208,3227806,3275430,5521457,8532035,13501056,15731968] (.node [113184,430364,902208,3227782,5521457,8532035,13501056,15731992,15814046] (.node [113184,430364,902208,3227782,5521457,8532035,8632931,13501056,15731992] (.node [113184,430364,902208,3227782,5521457,8532035,8632931,13501056,15731968,15731992] .nil .nil) (.node [113184,430364,902208,3227782,5521457,8532035,13501056,15731968,15814046] .nil .nil)) (.node [113184,430364,902208,3227782,5521457,8532035,13501056,15731992,15875419] (.node [113184,430364,902208,3227782,5521457,8532035,13501056,15731992,15875395] .nil .nil) .nil)) (.node [113184,430364,902208,3227806,5521457,8532035,13501056,15731968,15814046] (.node [113184,430364,902208,3227806,5521457,8532035,8632931,13501056,15731968] (.node [113184,430364,902208,3227806,3275454,5521457,8532035,13501056,15731968] .nil .nil) .nil) (.node [113184,430476,902208,3227782,5521457,5689661,8532035,11083800,15731968,15732480] (.node [113184,430364,902208,3227806,5521457,8532035,13501056,15731968,15875395] .nil .nil) .nil))) (.node [113184,430988,902208,3227782,5522097,5689661,8532035,11083800,15731968] (.node [113184,430476,902208,3227782,5521969,5689661,8532035,11083800,15731968] (.node [113184,430476,902208,3227782,5521457,8532035,8827343,11083800,13501056,15731968,16010545] (.node [113184,430476,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil) .nil) (.node [113184,430988,902208,3227782,5521457,5689661,8532035,11083800,15732608] (.node [113184,430988,902208,3227782,5521457,5689661,8532035,11083800,15731968,15732608] .nil .nil) .nil)) (.node [113184,431372,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,431372,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430988,902208,3228294,5521457,5689661,8532035,11083800,15731968] .nil .nil) .nil) (.node [113184,431372,3227782,5521521,5689661,8532035,11083800,13501056,15731968] (.node [113184,431372,3227782,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10babb_ok : tall (expFast false (classP') T9 9) T10babb = true := by decide +kernel
def T10bab : Tree := .node [113184,430364,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] T10baba T10babb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10bab_ok : tall (expFast false (classP') T9 9) T10bab = true :=
  tall_node _ _ _ _ T10baba_ok (by decide +kernel) T10babb_ok
def T10ba : Tree := .node [113184,430348,902232,3227782,5521457,8532035,13501056,15731968,15875419] T10baa T10bab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10ba_ok : tall (expFast false (classP') T9 9) T10ba = true :=
  tall_node _ _ _ _ T10baa_ok (by decide +kernel) T10bab_ok
def T10bbaa : Tree := (.node [113184,902208,3227782,5521457,5689661,8456454,8532035,8632931,11083800,13501056,15731968] (.node [113184,506668,1048428,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] (.node [113184,431436,3228870,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,431436,3227782,5521457,5689661,8532035,11083800,13501056,15732032] (.node [113184,431436,3227782,3228870,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,431436,3227782,5522545,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,506668,1037644,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,506668,1037644,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,507692,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [113184,506668,3227782,5521457,5689661,6145137,8533059,11083800,13501056,15731968] (.node [113184,506668,1048428,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [113184,902208,3227782,3275430,5689661,8827215,11083800,13501056,15875395,16010545] (.node [113184,902208,3227782,3227815,5689661,8532035,8895343,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,902208,3227782,5521457,5689661,8827343,11083800,13501056,15731968,15875395] (.node [113184,902208,3227782,5521457,5689661,8532035,8827343,11083800,14566065,15731968] (.node [113184,902208,3227782,5521457,5689661,8532035,8633191,11083800,13501056,15731968,15814022] (.node [113184,902208,3227782,5521457,5689661,8532035,8632931,11084060,13501056,15731968,15814022] .nil .nil) .nil) (.node [113184,902208,3227782,5521457,5689661,8532295,8633191,11083800,13501056,15731968,15814022] (.node [113184,902208,3227782,5521457,5689661,8532163,8827343,11083800,14566065,15731968] .nil .nil) .nil)) (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13538188,14566065,15731968,16010545] (.node [113184,902208,3227782,5689661,8532035,8532295,11083800,13501056,15731968,16076215] (.node [113184,902208,3227782,5521457,5689661,8827343,11083800,13501056,15731968,15875523] .nil .nil) .nil) (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13546447,14566065,15731968,16010545] (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13538188,15731968,16010545,16666545] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10bbaa_ok : tall (expFast false (classP') T9 9) T10bbaa = true := by decide +kernel
def T10bbab : Tree := (.node [113200,430348,902208,3227782,5521457,8532035,8632947,11083800,13501056,15731968,15814022] (.node [113184,902208,3227782,5689661,8827215,11083800,13501056,13546447,15875395,16010545] (.node [113184,902208,3227782,5689661,8532035,11084060,13501056,15731968,16076215] (.node [113184,902208,3227782,5689661,8532035,8895343,11083800,13501056,15732001] (.node [113184,902208,3227782,5689661,8532035,8895343,11083800,13501056,15731968,15732001] .nil .nil) (.node [113184,902208,3227782,5689661,8532035,8895343,11083833,13501056,15731968] .nil .nil)) (.node [113184,902208,3227782,5689661,8651009,8827215,11083800,13501056,15875395,16010545] (.node [113184,902208,3227782,5689661,8532295,11083800,13501056,15731968,16076215] .nil .nil) .nil)) (.node [113184,902208,3275430,5521457,5689661,8827215,11083800,13501056,15814022,15875395] (.node [113184,902208,3227815,5689661,8532035,8895343,11083800,13501056,15731968] (.node [113184,902208,3227782,5689661,8827215,11083800,13501056,15875395,16010545,16666545] .nil .nil) .nil) (.node [113200,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] (.node [113184,902208,3275430,5689661,7684279,8827215,11083800,13501056,15731968,15875395] .nil .nil) .nil))) (.node [113208,430348,902208,3227782,3275454,5521457,8532035,13501056,15731968,15731992] (.node [113208,430348,902208,3227782,3275430,5521457,8532035,13501056,15731968,15731992] (.node [113208,430348,902208,3227782,3227806,5521457,8532035,13501056,15731968,15875395] (.node [113208,430348,902208,3227782,3227806,5521457,8532035,8632955,13501056,15731968] .nil .nil) .nil) (.node [113208,430348,902208,3227782,3275430,5521465,8532035,13501056,15731968] (.node [113208,430348,902208,3227782,3275430,5521457,8532035,13501056,15731992] .nil .nil) .nil)) (.node [113208,430348,902208,3227782,3275454,5521465,8532035,13501056,15731968] (.node [113208,430348,902208,3227782,3275454,5521457,8532035,13501080,15731968] (.node [113208,430348,902208,3227782,3275454,5521457,8532035,13501056,15731992] .nil .nil) .nil) (.node [113208,430348,902208,3227782,5521457,8532035,8632931,13501080,15731968] (.node [113208,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10bbab_ok : tall (expFast false (classP') T9 9) T10bbab = true := by decide +kernel
def T10bba : Tree := .node [113184,902208,3227782,5689661,8532035,8827215,11083800,13546447,15731968,16010545,16666545] T10bbaa T10bbab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10bba_ok : tall (expFast false (classP') T9 9) T10bba = true :=
  tall_node _ _ _ _ T10bbaa_ok (by decide +kernel) T10bbab_ok
def T10bbba : Tree := (.node [113208,430348,902208,3227806,3275430,5521457,8532035,13501056,15731968] (.node [113208,430348,902208,3227782,5521457,8532035,13501056,15731992,15875419] (.node [113208,430348,902208,3227782,5521457,8532035,13501056,15731968,15814046] (.node [113208,430348,902208,3227782,5521457,8532035,8632955,13501056,15731992] (.node [113208,430348,902208,3227782,5521457,8532035,8632955,13501056,15731968,15731992] .nil .nil) (.node [113208,430348,902208,3227782,5521457,8532035,8632955,13501080,15731968] .nil .nil)) (.node [113208,430348,902208,3227782,5521457,8532035,13501056,15731992,15875395] (.node [113208,430348,902208,3227782,5521457,8532035,13501056,15731992,15814046] .nil .nil) .nil)) (.node [113208,430348,902208,3227782,5521465,8532035,8632955,13501056,15731968] (.node [113208,430348,902208,3227782,5521457,8532035,13501080,15731968,15875395] (.node [113208,430348,902208,3227782,5521457,8532035,13501080,15731968,15814022] .nil .nil) .nil) (.node [113208,430348,902208,3227782,5521465,8532035,13501056,15731968,15875395] (.node [113208,430348,902208,3227782,5521465,8532035,13501056,15731968,15814022] .nil .nil) .nil))) (.node [113312,430348,902208,3227782,5521457,5689661,8532035,11083800,15732608] (.node [113208,430348,902208,3227806,5521457,8532035,13501056,15731968,15814046] (.node [113208,430348,902208,3227806,5521457,8532035,8632955,13501056,15731968] (.node [113208,430348,902208,3227806,3275454,5521457,8532035,13501056,15731968] .nil .nil) .nil) (.node [113312,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968,15732608] (.node [113208,430348,902208,3227806,5521457,8532035,13501056,15731968,15875395] .nil .nil) .nil)) (.node [113312,902208,3227782,5521457,5689661,8532035,8827215,11083800,14566065,15731968] (.node [113312,430348,902208,3227782,5522097,5689661,8532035,11083800,15731968] (.node [113312,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil) .nil) (.node [113444,902208,3227782,5521457,5689661,8532035,8633191,11083800,13501056,15731968,15814022] (.node [113312,902208,3227782,5521457,5689661,8827215,11083800,13501056,15731968,15875395] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10bbba_ok : tall (expFast false (classP') T9 9) T10bbba = true := by decide +kernel
def T10bbbb : Tree := (.node [430348,902208,3227782,3275430,5689661,8632931,11083800,13501056,15875395,16010545] (.node [114272,430348,3227782,3228870,5521457,5689661,8532035,11083800,13501056,15731968] (.node [114208,430348,3227782,5521521,5689661,8532035,11083800,13501056,15731968] (.node [114208,430348,507692,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [114208,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [114208,430348,3227782,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [114208,507692,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [114208,430348,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [114272,430348,3227782,5522545,5689661,8532035,11083800,13501056,15731968] (.node [114272,430348,3227782,5521457,5689661,8532035,11083800,13502144,15731968] (.node [114272,430348,3227782,5521457,5689661,8532035,11083800,13501056,15732032] .nil .nil) .nil) (.node [327716,506668,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968] (.node [114272,430348,3228870,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [506668,902208,3275430,5521457,5689661,8532035,11083800,13501056,15814022,15875395] (.node [506668,902208,1048428,3275430,5689661,7684279,8532035,11083800,13501056,15731968] (.node [430348,902208,3275430,5689661,7684279,8632931,11083800,13501056,15731968,15875395] (.node [430348,902208,3275430,5521457,5689661,8632931,11083800,13501056,15814022,15875395] .nil .nil) .nil) (.node [506668,902208,3227782,3275430,5689661,8532035,11083800,13501056,15875395,16010545] (.node [506668,902208,3227782,3275430,5521457,5689661,8533059,11083800,13501056,15731968] .nil .nil) .nil)) (.node [507692,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [506668,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968,15875395] (.node [506668,902208,3275430,5689661,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [902208,3227782,3275430,5521457,5689661,8895343,11083800,13501056,15731968,15875395] (.node [507692,902208,3227782,3276454,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10bbbb_ok : tall (expFast false (classP') T9 9) T10bbbb = true := by decide +kernel
def T10bbb : Tree := .node [113444,902208,3227782,5689661,8532035,11083800,13501056,15731968,16076215] T10bbba T10bbbb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10bbb_ok : tall (expFast false (classP') T9 9) T10bbb = true :=
  tall_node _ _ _ _ T10bbba_ok (by decide +kernel) T10bbbb_ok
def T10bb : Tree := .node [113208,430348,902208,3227782,5521457,8532035,8632955,11083800,13501056,15731968,15814022] T10bba T10bbb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10bb_ok : tall (expFast false (classP') T9 9) T10bb = true :=
  tall_node _ _ _ _ T10bba_ok (by decide +kernel) T10bbb_ok
def T10b : Tree := .node [113184,431372,3227846,5521457,5689661,8532035,11083800,13501056,15731968] T10ba T10bb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10b_ok : tall (expFast false (classP') T9 9) T10b = true :=
  tall_node _ _ _ _ T10ba_ok (by decide +kernel) T10bb_ok
def T10 : Tree := .node [113184,430348,902208,3227782,5521465,8532059,13501056,15731968,15875419] T10a T10b
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T10_ok : tall (expFast false (classP') T9 9) T10 = true :=
  tall_node _ _ _ _ T10a_ok (by decide +kernel) T10b_ok
def T11aaaa : Tree := (.node [24,113184,430348,902208,1037644,3227782,5521457,7684279,8532035,13501056,15731968] (.node [24,1088,113184,430348,3227782,5521457,8532035,13501056,15731968,15875395] (.node [24,260,113184,902208,3227782,5521457,8532035,13501056,15731968,15814022] (.node [16,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] (.node [8,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil) (.node [24,33,113184,430348,902208,3227782,8532035,8632931,13501056,15731968] .nil .nil)) (.node [24,640,113184,430348,902208,3227782,5521457,5689661,8532035,15731968] (.node [24,640,113184,430348,902208,3227782,3275430,5521457,8532035,15731968] .nil .nil) (.node [24,1088,113184,430348,3227782,5521457,5689661,8532035,13501056,15731968] .nil .nil))) (.node [24,113184,430348,506668,902208,3227782,5521457,7684279,8532035,13501056,15731968] (.node [24,113184,113208,430348,902208,3227782,5521457,8532035,13501056,15731968,15875395] (.node [24,113184,113208,430348,902208,3227782,5521457,8532035,13501056,15731968,15814022] .nil .nil) (.node [24,113184,430348,506668,902208,3227782,5521457,6145137,8532035,13501056,15731968] .nil .nil)) (.node [24,113184,430348,902208,917088,3227782,5521457,8532035,13501056,13538188,15731968] (.node [24,113184,430348,902208,917088,3227782,5521457,8532035,13501056,13513411,15731968] .nil .nil) .nil))) (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501056,15731968,15731992] (.node [24,113184,430348,902208,3227782,3275430,5521457,5689661,8532035,13501056,15731968,15875395] (.node [24,113184,430348,902208,3227782,3227806,5521457,8532035,8632931,13501056,15731968] (.node [24,113184,430348,902208,1037644,3227782,5521457,8532035,13501056,13513411,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,3227806,5521457,8532035,13501056,15731968,15875395] .nil .nil)) (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968,15875395] (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,8532059,13501056,15731968] .nil .nil) .nil)) (.node [24,113184,430348,902208,3227782,3275430,5521457,8532059,13501056,15731968] (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501056,15731992] (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501056,15731968,15875395] .nil .nil) (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501080,15731968] .nil .nil)) (.node [24,113184,430348,902208,3227782,3275454,5521457,8532035,13501056,15731968] (.node [24,113184,430348,902208,3227782,3275430,5521465,8532035,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11aaaa_ok : tall (expFast false (classP') T10 10) T11aaaa = true := by decide +kernel
def T11aaab : Tree := (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,15814046] (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227782,5521457,8532035,8532059,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227782,5521457,5689661,8532035,8632931,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227782,4048070,5521457,8532035,13501056,15731968,16650112] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,6145137,8532035,13501056,15731968,16650112] .nil .nil)) (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501056,15731968,15731992] (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil) .nil)) (.node [24,113184,430348,902208,3227782,5521457,8532035,8827215,13501056,14566065,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501080,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501056,15731992] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,8532035,8632955,13501056,15731968] .nil .nil)) (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,13538188,15731968,16010545] (.node [24,113184,430348,902208,3227782,5521457,8532035,8827215,13501056,15731968,16010545] .nil .nil) .nil))) (.node [24,113184,430348,902208,3227782,5521457,8532035,13501080,15731968,15814022] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731992,15875395] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731992,15814022] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,15875419] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731992,15814046] .nil .nil)) (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15814022,15875395] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731992,15875419] .nil .nil) .nil)) (.node [24,113184,430348,902208,3227782,5521457,8532059,8632955,13501056,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,13538188,14566065,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501080,15731968,15875395] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,8532059,8632931,13501056,15731968] .nil .nil)) (.node [24,113184,430348,902208,3227782,5521457,8532059,13501056,15731968,15875395] (.node [24,113184,430348,902208,3227782,5521457,8532059,13501056,15731968,15814022] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11aaab_ok : tall (expFast false (classP') T10 10) T11aaab = true := by decide +kernel
def T11aaa : Tree := .node [24,113184,430348,902208,3227782,4048070,5521457,8532035,13501056,14566065,15731968] T11aaaa T11aaab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11aaa_ok : tall (expFast false (classP') T10 10) T11aaa = true :=
  tall_node _ _ _ _ T11aaaa_ok (by decide +kernel) T11aaab_ok
def T11aaba : Tree := (.node [24,113184,430348,902232,3227782,5521457,8532035,8632931,13501056,15731968] (.node [24,113184,430348,902208,3227806,3275454,5521457,8532035,13501056,15731968] (.node [24,113184,430348,902208,3227782,5521465,8532035,13501056,15731968,15875395] (.node [24,113184,430348,902208,3227782,5521465,8532035,8632931,13501056,15731968] (.node [24,113184,430348,902208,3227782,5521457,8632931,13501056,15731968,15875395] .nil .nil) (.node [24,113184,430348,902208,3227782,5521465,8532035,13501056,15731968,15814022] .nil .nil)) (.node [24,113184,430348,902208,3227806,3275430,5521457,8532035,13501056,15731968] (.node [24,113184,430348,902208,3227782,6145137,8532035,13501056,14566065,15731968] .nil .nil) .nil)) (.node [24,113184,430348,902208,3227806,5521457,8532035,13501056,15731968,15875395] (.node [24,113184,430348,902208,3227806,5521457,8532035,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227806,5521457,8532035,8632931,13501056,15731968] .nil .nil) (.node [24,113184,430348,902208,3227806,5521457,8532035,13501056,15731968,15814046] .nil .nil)) (.node [24,113184,430348,902232,3227782,3275430,5521457,8532035,13501056,15731968] (.node [24,113184,430348,902208,3275430,5521457,8532035,13501056,15731968,15814022] .nil .nil) .nil))) (.node [24,113184,430364,902208,3227782,5521457,8532035,13501056,15731968,15875395] (.node [24,113184,430364,902208,3227782,3275430,5521457,8532035,13501056,15731968] (.node [24,113184,430348,902232,3227782,5521457,8532035,13501056,15731968,15875395] (.node [24,113184,430348,902232,3227782,5521457,8532035,13501056,15731968,15814022] .nil .nil) (.node [24,113184,430348,1037644,3227782,5521457,6145137,8532035,13501056,15731968] .nil .nil)) (.node [24,113184,430364,902208,3227782,5521457,8532035,13501056,15731968,15814022] (.node [24,113184,430364,902208,3227782,5521457,8532035,8632931,13501056,15731968] .nil .nil) .nil)) (.node [24,113208,430348,902208,3227782,5521457,8532035,8632931,13501056,15731968] (.node [24,113208,430348,902208,3227782,3275430,5521457,8532035,13501056,15731968] (.node [24,113184,902208,1037644,3227782,5521457,8532035,13501056,13538188,15731968] .nil .nil) (.node [24,113208,430348,902208,3227782,3275454,5521457,8532035,13501056,15731968] .nil .nil)) (.node [24,113208,430348,902208,3227782,5521457,8532035,13501056,15731968,15814022] (.node [24,113208,430348,902208,3227782,5521457,8532035,8632955,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11aaba_ok : tall (expFast false (classP') T10 10) T11aaba = true := by decide +kernel
def T11aabb : Tree := (.node [128,512,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968,15875395] (.node [64,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [49,113184,430348,902208,3227782,8532035,8632931,11083800,13501056,15731968] (.node [33,113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,15814022] (.node [24,430348,902208,3227782,3275430,5521457,8532035,8632931,13501056,15731968] .nil .nil) (.node [33,113184,902208,3227782,5689661,8532035,8895343,11083800,13501056,15731968] .nil .nil)) (.node [64,113184,114208,430348,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [64,1024,113184,430348,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [64,114208,430348,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [64,113184,430348,1037644,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [64,113184,430348,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [64,113184,431372,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [67,113184,430348,902208,3227782,5689661,7684279,11083800,13501056,15731968] (.node [67,113184,430348,902208,3227782,5521457,7684279,11083800,13501056,15731968] .nil .nil) .nil))) (.node [134,113184,430348,902208,5521457,8532035,8827215,11083800,13501056,15731968] (.node [128,113184,430348,902208,3227782,5521969,5689661,8532035,11083800,15731968] (.node [128,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15732480] (.node [128,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968,15732480] .nil .nil) (.node [128,113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil)) (.node [128,113184,902208,3227782,5521457,5689661,8827215,11083800,13501056,15731968,15875395] (.node [128,113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,14566065,15731968] .nil .nil) .nil)) (.node [268,113184,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [260,113184,902208,3227782,5521457,5689661,8532035,8632931,11083800,13501056,15731968,15814022] (.node [134,113184,902208,5521457,5689661,8532035,8827215,11083800,13501056,15731968] .nil .nil) (.node [260,113184,902208,3227782,5689661,8532035,11083800,13501056,15731968,16076215] .nil .nil)) (.node [512,113184,430348,902208,3227782,5521457,5689661,8532163,11083800,15731968] (.node [512,113184,430348,902208,3227782,5521457,5689661,8532035,8532163,11083800,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11aabb_ok : tall (expFast false (classP') T10 10) T11aabb = true := by decide +kernel
def T11aab : Tree := .node [24,113208,430348,902208,3227782,5521457,8532035,13501056,15731968,15875395] T11aaba T11aabb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11aab_ok : tall (expFast false (classP') T10 10) T11aab = true :=
  tall_node _ _ _ _ T11aaba_ok (by decide +kernel) T11aabb_ok
def T11aa : Tree := .node [24,113184,430348,902208,3227782,5521457,8532059,13501056,15731968,15875419] T11aaa T11aab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11aa_ok : tall (expFast false (classP') T10 10) T11aa = true :=
  tall_node _ _ _ _ T11aaa_ok (by decide +kernel) T11aab_ok
def T11abaa : Tree := (.node [640,113184,430348,902208,3227782,5521457,8532035,11083800,15731968,15875395] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968,15732608] (.node [640,113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,15731968,15875395] (.node [512,113184,430348,902208,3227782,5689661,8532035,11083800,13538188,15731968,16010545] (.node [512,113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15875395,16010545] .nil .nil) (.node [512,113184,430476,902208,3227782,5521457,5689661,8532035,11083800,15731968] .nil .nil)) (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15875395] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,8532675,11083800,15731968] .nil .nil) (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968] .nil .nil))) (.node [640,113184,430348,902208,3227782,5521457,5689661,8532675,11083800,15731968] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15732608] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968,15875395] .nil .nil) (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11084440,15731968] .nil .nil)) (.node [640,113184,430348,902208,3227782,5521457,8532035,8827215,11083800,15731968] (.node [640,113184,430348,902208,3227782,5521457,5690301,8532035,11083800,15731968] .nil .nil) .nil))) (.node [640,113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,15731968] (.node [640,113184,430348,902208,3228294,5521457,5689661,8532035,11083800,15731968] (.node [640,113184,430348,902208,3227782,5522097,5689661,8532035,11083800,15731968] (.node [640,113184,430348,902208,3227782,5521457,8532035,11083800,15731968,16010545] .nil .nil) (.node [640,113184,430348,902208,3227782,5689661,8532035,11083800,15731968,16010545] .nil .nil)) (.node [640,113184,430988,902208,3227782,5521457,5689661,8532035,11083800,15731968] (.node [640,113184,430348,902848,3227782,5521457,5689661,8532035,11083800,15731968] .nil .nil) .nil)) (.node [1024,113184,430348,3227782,5521521,5689661,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [640,113312,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968] .nil .nil) (.node [1024,113184,430348,3227782,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1024,113184,506668,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11abaa_ok : tall (expFast false (classP') T10 10) T11abaa = true := by decide +kernel
def T11abab : Tree := (.node [1088,113184,430348,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,3275430,5521457,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,3228870,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,506668,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1088,113184,114272,430348,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [1088,113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1088,113184,430348,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968,15875395] (.node [1088,113184,430348,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [1088,113184,430348,3227782,5521457,5689661,8532035,11084888,13501056,15731968] (.node [1088,113184,430348,3227782,5521457,5689661,8532035,11083800,13501056,15732032] (.node [1088,113184,430348,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [1088,113184,430348,3227782,5521457,5689661,8532035,11083800,13502144,15731968] .nil .nil)) (.node [1088,113184,430348,3227782,5521457,5690749,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,5521457,5689661,8533059,11083800,13501056,15731968] .nil .nil) .nil))) (.node [2592,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] (.node [1088,113184,431436,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,5522545,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [1088,113184,430348,3228870,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1088,114272,430348,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1088,113184,506668,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,113200,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [3328,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056] (.node [2592,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16010545] .nil .nil) (.node [3328,113184,506668,902208,3227782,5521457,5689661,8532035,11083800,13501056] .nil .nil)) (.node [113184,113208,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [113184,113208,430348,902208,3227782,3227806,5521457,8532035,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11abab_ok : tall (expFast false (classP') T10 10) T11abab = true := by decide +kernel
def T11aba : Tree := .node [1024,506668,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] T11abaa T11abab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11aba_ok : tall (expFast false (classP') T10 10) T11aba = true :=
  tall_node _ _ _ _ T11abaa_ok (by decide +kernel) T11abab_ok
def T11abba : Tree := (.node [113184,430348,506668,902208,1048428,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,114208,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,113208,430348,902208,3227806,5521457,8532035,13501056,15731968] (.node [113184,113208,430348,902208,3227782,5521457,8532035,13501080,15731968] (.node [113184,113208,430348,902208,3227782,5521457,8532035,13501056,15731992] .nil .nil) (.node [113184,113208,430348,902208,3227782,5521465,8532035,13501056,15731968] .nil .nil)) (.node [113184,113444,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15814022] (.node [113184,113312,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15875395] .nil .nil) .nil)) (.node [113184,430348,431372,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,327716,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [113184,114208,430348,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,430476,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] .nil .nil)) (.node [113184,430348,506668,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,506668,902208,3227782,5521457,6145137,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,3227846,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,5521521,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,506668,902208,3227782,5521521,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,8533059,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15732032] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521461,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11abba_ok : tall (expFast false (classP') T10 10) T11abba = true := by decide +kernel
def T11abbb : Tree := (.node [113184,430348,902208,3227782,3275430,5521521,5689661,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3227815,5689661,8532035,8632931,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3227806,5521457,8532035,8632931,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3227790,5521457,8532035,8632931,11083800,13501056,15731968] (.node [113184,430348,507692,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,3227806,5521457,8532035,8532059,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,3227806,5521457,8532059,13501056,15731968] (.node [113184,430348,902208,3227782,3227806,5521457,8532035,13501080,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15732032] (.node [113184,430348,902208,3227782,3275430,5521457,5689661,8532035,8533059,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3228294,5521457,5689661,8532035,11083800,13501056,15731968,15875395] .nil .nil) (.node [113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968,15732032] .nil .nil)) (.node [113184,430348,902208,3227782,3275430,5521457,8532035,8827215,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,3275430,5521457,5689661,8533059,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13538188,15732480] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15732480,15875395] (.node [113184,430348,902208,3227782,5521457,5521969,8532035,8827215,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3275430,5689661,8532035,11083800,13501056,15875395,16010545] .nil .nil) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8532163,11083800,14566065,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13538188,15731968,15732480] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15732480,15875907] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,5689661,8632931,11083800,13501056,15814022,15875395] (.node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,13501056,15731968,15875523] (.node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,13501056,15731968,15875395] .nil .nil) (.node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,14566065,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15732032] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8895343,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11abbb_ok : tall (expFast false (classP') T10 10) T11abbb = true := by decide +kernel
def T11abb : Tree := .node [113184,430348,506668,902208,3227846,5521457,8532035,11083800,13501056,15731968] T11abba T11abbb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11abb_ok : tall (expFast false (classP') T10 10) T11abb = true :=
  tall_node _ _ _ _ T11abba_ok (by decide +kernel) T11abbb_ok
def T11ab : Tree := .node [113184,113208,430348,902208,3227782,5521457,8532035,13501056,15731968,15731992] T11aba T11abb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11ab_ok : tall (expFast false (classP') T10 10) T11ab = true :=
  tall_node _ _ _ _ T11aba_ok (by decide +kernel) T11abb_ok
def T11a : Tree := .node [512,113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545] T11aa T11ab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11a_ok : tall (expFast false (classP') T10 10) T11a = true :=
  tall_node _ _ _ _ T11aa_ok (by decide +kernel) T11ab_ok
def T11baaa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11219035,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8532059,13501056,15731968,15731992] (.node [113184,430348,902208,3227782,5521457,8532035,8532051,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,7684343,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8532059,11083800,13501056,15731968,15814022] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8532163,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5521457,8532035,8532059,13501056,15731992] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11123256,13501056,15731968,15814022] .nil .nil))) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15731992] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,12148894,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11254395,13501056,15731968,15814022] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15731976] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022,16346526] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022,16330008] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,13546447,15731968,16010545] (.node [113184,430348,902208,3227782,5521457,8532035,8632955,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731992] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731976] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632947,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,13538188,15731968,16010545] (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,13513411,15731968,16010545] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545,16666545] (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,15732480] (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,14566065,15731968,16010545] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545,16650112] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15732480] (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16076215] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11baaa_ok : tall (expFast false (classP') T10 10) T11baaa = true := by decide +kernel
def T11baab : Tree := (.node [113184,430348,902208,3227782,5521457,8532051,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731976,15814030] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814046] (.node [113184,430348,902208,3227782,5521457,8532035,8895343,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5521457,8532035,8895343,11083800,13501056,15731968,15814022] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814030] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731976,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16011057] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15732480,16011057] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731992,15814046] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731992,15814022] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15732480,16010545] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532051,8632947,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532051,8632931,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5521457,8532163,8827343,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532059,13501056,15731968,15731992] (.node [113184,430348,902208,3227782,5521457,8532059,8632955,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532059,8632931,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532059,11083800,13501056,15731968,15814022] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532163,8827215,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532059,13501056,15731992] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521465,8532035,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521465,8532035,8532059,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532163,11083800,13501056,15731968,16010545] .nil .nil) (.node [113184,430348,902208,3227782,5521465,8532035,8632931,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521521,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521465,8532059,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11baab_ok : tall (expFast false (classP') T10 10) T11baab = true := by decide +kernel
def T11baa : Tree := .node [113184,430348,902208,3227782,5521457,8532035,8827343,11083800,13501056,15731968] T11baaa T11baab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11baa_ok : tall (expFast false (classP') T10 10) T11baa = true :=
  tall_node _ _ _ _ T11baaa_ok (by decide +kernel) T11baab_ok
def T11baba : Tree := (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,15814022,16076215] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,8632931,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521969,8532035,8827215,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521969,5689661,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,5521713,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil) (.node [113184,430348,902208,3227782,5521969,5689661,8532035,11083800,13538188,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521969,8532035,11083800,13501056,15731968,16011057] (.node [113184,430348,902208,3227782,5521969,8532035,11083800,13501056,15731968,16010545] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5689661,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15814022,15875395] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15732032] .nil .nil) (.node [113184,430348,902208,3227782,5689661,7684279,8632931,11083800,13501056,15731968,15875395] .nil .nil)) (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,15814022,16010545] (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,15732001] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16011057] (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083833,13501056,15731968] (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,15814022,16605241] .nil .nil) (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15732001] .nil .nil)) (.node [113184,430348,902208,3227782,5689661,8532035,8827215,11083800,13501056,15731968,16010545,16666545] (.node [113184,430348,902208,3227782,5689661,8532035,8827215,11083800,13501056,14566065,15731968,16010545] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15875395,16076215] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15732480,16011057] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15732480,16010545] .nil .nil) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15875395,16010545,16666545] .nil .nil)) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13538188,15731968,16010545,16666545] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13538188,14566065,15731968,16010545] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11baba_ok : tall (expFast false (classP') T10 10) T11baba = true := by decide +kernel
def T11babb : Tree := (.node [113184,430348,902208,3227846,5521457,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227806,5521457,8532035,11083800,13501056,15731968,15814046] (.node [113184,430348,902208,3227806,5521457,8532035,8532059,13501056,15731968] (.node [113184,430348,902208,3227790,5521457,8532035,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227790,5521457,8532035,8632931,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227790,5521457,8532035,11083800,13501056,15731968,15814030] .nil .nil)) (.node [113184,430348,902208,3227806,5521457,8532035,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227806,5521457,8532035,8632931,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227846,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227806,5521457,8532059,13501056,15731968] (.node [113184,430348,902208,3227806,5521457,8532035,13501080,15731968] .nil .nil) (.node [113184,430348,902208,3227815,5689661,8532035,8632931,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227846,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227846,3275494,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,902208,3228294,5689661,8532035,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3228294,5521457,5689661,8532035,11083800,13538188,15731968] (.node [113184,430348,902208,3227846,5689661,7684343,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227846,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3228294,5521457,5689661,8532035,11083800,13501056,15731968,15875395] .nil .nil)) (.node [113184,430348,902208,3228294,5521457,8532035,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3228294,5521457,8532035,8827215,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3275430,5689661,8532035,11083800,13501056,15731968,15814022,16010545] (.node [113184,430348,902208,3275430,5689661,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3275430,5521457,5689661,8532035,11083800,13501056,15814022,15875395] .nil .nil) (.node [113184,430348,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968,15875395] .nil .nil)) (.node [113184,430348,902232,3227782,5521457,8532035,8532059,13501056,15731968] (.node [113184,430348,902208,3275430,5689661,8532035,11083800,13501056,15731968,16076215] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11babb_ok : tall (expFast false (classP') T10 10) T11babb = true := by decide +kernel
def T11bab : Tree := .node [113184,430348,902208,3227782,5689661,8632931,11083800,13501056,15875395,16010545] T11baba T11babb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11bab_ok : tall (expFast false (classP') T10 10) T11bab = true :=
  tall_node _ _ _ _ T11baba_ok (by decide +kernel) T11babb_ok
def T11ba : Tree := .node [113184,430348,902208,3227782,5521521,7684343,8532035,11083800,13501056,15731968] T11baa T11bab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11ba_ok : tall (expFast false (classP') T10 10) T11ba = true :=
  tall_node _ _ _ _ T11baa_ok (by decide +kernel) T11bab_ok
def T11bbaa : Tree := (.node [113184,430364,902208,3227782,5521457,8532035,13501056,15731968,15731992] (.node [113184,430348,1037644,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,1037644,3227782,5521457,5689661,8532035,11083800,13501056,15732032] (.node [113184,430348,902232,3227782,5521457,8532059,13501056,15731968] (.node [113184,430348,902232,3227782,5521457,8532035,13501056,15731992] .nil .nil) (.node [113184,430348,1037644,3227782,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,1037644,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,1037644,3227782,5521521,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430364,902208,3227782,3227806,5521457,8532035,13501056,15731968] (.node [113184,430348,3227782,5521457,5689661,6145137,8533059,11083800,13501056,15731968] (.node [113184,430348,1037644,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430349,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil)) (.node [113184,430364,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [113184,430364,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430476,902208,3227782,5521457,8532035,8827343,11083800,13501056,15731968] (.node [113184,430476,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15875395] (.node [113184,430364,902208,3227806,5521457,8532035,13501056,15731968] (.node [113184,430364,902208,3227782,5521457,8532035,13501056,15731992] .nil .nil) (.node [113184,430380,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430476,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968] (.node [113184,430476,902208,3227782,5521457,5689661,8532035,11083800,14566065,15731968] .nil .nil) .nil)) (.node [113184,431372,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,431372,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430476,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] .nil .nil) (.node [113184,431372,507692,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,431372,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [113184,431372,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11bbaa_ok : tall (expFast false (classP') T10 10) T11bbaa = true := by decide +kernel
def T11bbab : Tree := (.node [113184,506668,1048428,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [113184,506668,902208,3227782,5521457,5689661,8632931,11083800,13501056,15731968,15875395] (.node [113184,506668,902208,3227782,5521457,5689661,8532035,8632931,11083800,13501056,15731968,15814022] (.node [113184,506668,902208,1048428,3227782,5521457,5689661,7684279,8532035,11083800,13501056,15731968] (.node [113184,506668,902208,1037644,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,506668,902208,1048428,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,506668,902208,3227782,5521457,5689661,8533059,11083800,13501056,15731968] (.node [113184,506668,902208,3227782,5521457,5689661,8532035,11083800,13501056,15814022,15875395] .nil .nil) .nil)) (.node [113184,506668,902208,3227782,5689661,8532035,11083800,13501056,15731968,16076215] (.node [113184,506668,902208,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,506668,902208,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,15875395] .nil .nil)) (.node [113184,506668,1037644,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [113184,506668,902208,3227782,5689661,8532035,11083800,13501056,15875395,16010545] .nil .nil) .nil))) (.node [113184,902208,3227782,5521457,5689661,8532035,8632931,11083800,11514140,13501056,15731968,15814022] (.node [113184,902208,3227782,5521457,5689661,8532035,8532295,11083800,13501056,15731968,15814022] (.node [113184,902208,3227782,3275430,5521457,5689661,8827215,11083800,13501056,15731968,15875395] (.node [113184,507692,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,902208,3227782,3275430,5689661,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil)) (.node [113184,902208,3227782,5521457,5689661,8532035,8632931,8895343,11083800,13501056,15731968,15814022] (.node [113184,902208,3227782,5521457,5689661,8532035,8632931,8827215,11083800,13501056,15731968,15814022] .nil .nil) .nil)) (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13546447,14566065,15731968] (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,13546447,15731968,16010545] (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,13538188,15731968,16010545] .nil .nil) (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13538188,14566065,15731968] .nil .nil)) (.node [113184,902208,3227782,5521457,5689661,8532035,8895343,11083800,13501056,15731968,15814022] (.node [113184,902208,3227782,5521457,5689661,8532035,8827343,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11bbab_ok : tall (expFast false (classP') T10 10) T11bbab = true := by decide +kernel
def T11bba : Tree := .node [113184,506668,902208,1037644,3227782,5521457,5689661,7684279,8532035,11083800,13501056,15731968] T11bbaa T11bbab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11bba_ok : tall (expFast false (classP') T10 10) T11bba = true :=
  tall_node _ _ _ _ T11bbaa_ok (by decide +kernel) T11bbab_ok
def T11bbba : Tree := (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13501056,15731968,16076215] (.node [113184,902208,3227782,5689661,7684279,8532035,8895343,11083800,13501056,15731968] (.node [113184,902208,3227782,5521457,5689661,8827215,11083800,13501056,13546447,15731968,15875395] (.node [113184,902208,3227782,5521457,5689661,8532163,8827343,11083800,13501056,15731968] (.node [113184,902208,3227782,5521457,5689661,8532163,8827215,11083800,13501056,15731968] .nil .nil) (.node [113184,902208,3227782,5521457,5689661,8532295,11083800,13501056,15731968,15814022] .nil .nil)) (.node [113184,902208,3227782,5521457,5689661,8895343,11083800,13501056,15731968,15875395] (.node [113184,902208,3227782,5521457,5689661,8827215,11083800,13501056,15814022,15875395] .nil .nil) .nil)) (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13501056,13546447,15731968,16010545] (.node [113184,902208,3227782,5689661,8532035,8651009,8827215,11083800,13501056,15731968,16010545] (.node [113184,902208,3227782,5689661,7684279,8827215,11083800,13501056,15731968,15875395] .nil .nil) (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13501056,13538188,15731968,16010545] .nil .nil)) (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13501056,15731968,16010545,16666545] (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13501056,14566065,15731968,16010545] .nil .nil) .nil))) (.node [113200,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [113184,902208,3275430,5689661,7684279,8532035,8827215,11083800,13501056,15731968] (.node [113184,902208,3227782,5689661,8827215,11083800,13501056,15875395,16010545] (.node [113184,902208,3227782,5689661,8532035,8895343,11083800,13501056,15731968,16010545] .nil .nil) (.node [113184,902208,3275430,5521457,5689661,8532035,8827215,11083800,13501056,15731968,15814022] .nil .nil)) (.node [113200,430348,902208,3227782,5521457,8532035,8632947,11083800,13501056,15731968] (.node [113200,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113208,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [113208,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] (.node [113208,430348,902208,3227782,3227806,5521457,8532035,13501056,15731968] .nil .nil) (.node [113208,430348,902208,3227782,5521457,8532035,8632955,11083800,13501056,15731968] .nil .nil)) (.node [113208,430348,902208,3227782,5521457,8532035,13501056,15731992] (.node [113208,430348,902208,3227782,5521457,8532035,13501056,15731968,15731992] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11bbba_ok : tall (expFast false (classP') T10 10) T11bbba = true := by decide +kernel
def T11bbbb : Tree := (.node [114208,430348,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [113312,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,15731968] (.node [113312,430348,902208,3227782,5521457,5689661,8532035,11083800,14566065,15731968] (.node [113208,430348,902208,3227806,5521457,8532035,13501056,15731968] (.node [113208,430348,902208,3227782,5521465,8532035,13501056,15731968] .nil .nil) (.node [113312,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15875395] .nil .nil)) (.node [113312,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] (.node [113312,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968] .nil .nil) .nil)) (.node [114208,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [114208,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113444,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15814022] .nil .nil) (.node [114208,430348,507692,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [114208,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [114208,430348,902208,3227782,3276454,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [506668,902208,1048428,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [430348,902208,3227782,3275430,5689661,8532035,8632931,11083800,13501056,15731968,16010545] (.node [114208,507692,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [114208,506668,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [430348,902208,3227782,3275430,5521457,5689661,8632931,11083800,13501056,15731968,15875395] .nil .nil)) (.node [430348,902208,3275430,5689661,7684279,8532035,8632931,11083800,13501056,15731968] (.node [430348,902208,3275430,5521457,5689661,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil) .nil)) (.node [506668,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968] (.node [506668,902208,3227782,3275430,5689661,8532035,11083800,13501056,15731968,16010545] (.node [506668,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968,15875395] .nil .nil) (.node [506668,902208,3275430,5521457,5689661,8532035,11083800,13501056,15731968,15814022] .nil .nil)) (.node [902208,3227782,3275430,5521457,5689661,8532035,8895343,11083800,13501056,15731968] (.node [902208,3227782,3275430,5521457,5689661,8532035,8632931,8827215,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11bbbb_ok : tall (expFast false (classP') T10 10) T11bbbb = true := by decide +kernel
def T11bbb : Tree := .node [113208,430348,902208,3227782,5521457,8532035,13501080,15731968] T11bbba T11bbbb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11bbb_ok : tall (expFast false (classP') T10 10) T11bbb = true :=
  tall_node _ _ _ _ T11bbba_ok (by decide +kernel) T11bbbb_ok
def T11bb : Tree := .node [113184,902208,3227782,5521457,5689661,8532035,11084060,13501056,15731968,15814022] T11bba T11bbb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11bb_ok : tall (expFast false (classP') T10 10) T11bb = true :=
  tall_node _ _ _ _ T11bba_ok (by decide +kernel) T11bbb_ok
def T11b : Tree := .node [113184,430348,902232,3227782,5521457,8532035,13501056,15731968,15731992] T11ba T11bb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11b_ok : tall (expFast false (classP') T10 10) T11b = true :=
  tall_node _ _ _ _ T11ba_ok (by decide +kernel) T11bb_ok
def T11 : Tree := .node [113184,430348,902208,3227782,5521457,7684279,8533059,11083800,13501056,15731968] T11a T11b
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T11_ok : tall (expFast false (classP') T10 10) T11 = true :=
  tall_node _ _ _ _ T11a_ok (by decide +kernel) T11b_ok
def T12aaa : Tree := (.node [24,113184,430348,902208,3227782,5521457,6145137,8532035,13501056,15731968] (.node [24,113184,430348,902208,3227782,3227806,5521457,8532035,13501056,15731968] (.node [24,113184,113208,430348,902208,3227782,5521457,8532035,13501056,15731968] (.node [16,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] (.node [8,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [8,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] .nil .nil) .nil) (.node [16,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] .nil .nil)) (.node [24,113184,430348,902208,917088,3227782,5521457,8532035,13501056,15731968] (.node [24,113184,430348,506668,902208,3227782,5521457,8532035,13501056,15731968] .nil .nil) (.node [24,113184,430348,902208,1037644,3227782,5521457,8532035,13501056,15731968] .nil .nil))) (.node [24,113184,430348,902208,3227782,4048070,5521457,8532035,13501056,15731968] (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968] (.node [24,113184,430348,902208,3227782,3275430,5521457,5689661,8532035,13501056,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,3275430,5521457,8532035,13501056,15731968] .nil .nil)) (.node [24,113184,430348,902208,3227782,5521457,5689661,8532035,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227782,5521457,5689661,8532035,8632931,13501056,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,5689661,8532035,13501056,15731968,15875395] .nil .nil)))) (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,13513411,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,13501056,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,8532059,13501056,15731968] (.node [24,113184,430348,902208,3227782,5521457,7684279,8532035,13501056,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] .nil .nil)) (.node [24,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227782,5521457,8532035,8827215,13501056,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15875395] .nil .nil))) (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,15814022] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,14566065,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,13538188,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,15731992] .nil .nil)) (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,16010545] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,15875395] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968,16650112] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12aaa_ok : tall (expFast false (classP') T11 11) T12aaa = true := by decide +kernel
def T12aab : Tree := (.node [128,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15875395] (.node [33,113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968] (.node [24,113184,430348,902208,3227806,5521457,8532035,13501056,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532059,13501056,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501080,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,5521465,8532035,13501056,15731968] .nil .nil)) (.node [24,113184,430364,902208,3227782,5521457,8532035,13501056,15731968] (.node [24,113184,430348,902232,3227782,5521457,8532035,13501056,15731968] .nil .nil) (.node [24,113208,430348,902208,3227782,5521457,8532035,13501056,15731968] .nil .nil))) (.node [64,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [64,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [64,1024,113184,430348,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [64,113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [64,113184,430348,1037644,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [64,113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [128,512,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968] .nil .nil)))) (.node [512,113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968] (.node [128,113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,15731968] (.node [128,113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968] (.node [128,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,14566065,15731968] .nil .nil) (.node [128,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] .nil .nil)) (.node [512,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15875395] (.node [260,113184,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15814022] .nil .nil) (.node [512,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13538188,15731968] .nil .nil))) (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [512,113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16010545] (.node [512,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] .nil .nil) (.node [640,113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,15731968] .nil .nil)) (.node [640,113184,430348,902208,3227782,5521457,8532035,11083800,15731968] (.node [640,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,15731968] .nil .nil) (.node [1024,113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12aab_ok : tall (expFast false (classP') T11 11) T12aab = true := by decide +kernel
def T12aa : Tree := .node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731992] T12aaa T12aab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12aa_ok : tall (expFast false (classP') T11 11) T12aa = true :=
  tall_node _ _ _ _ T12aaa_ok (by decide +kernel) T12aab_ok
def T12aba : Tree := (.node [113184,430348,506668,902208,1048428,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,113208,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1024,113184,506668,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) .nil) (.node [1088,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1088,113184,430348,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1088,113184,430348,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15875395] .nil .nil) (.node [113184,113200,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil))) (.node [113184,430348,430476,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,114208,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,113312,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,114208,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,917088,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,431372,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,1037644,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)))) (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] (.node [113184,430348,506668,902208,3227782,5521457,6145137,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] (.node [113184,430348,506668,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968,15875395] .nil .nil))) (.node [113184,430348,902208,917088,3227782,5521457,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,5521457,5689661,8532035,11083800,13501056,13513411,15731968] (.node [113184,430348,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,917088,3227782,5521457,5689661,8532035,11083800,13501056,13538188,15731968] .nil .nil)) (.node [113184,430348,902208,1037644,3227782,5521457,5689661,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,13513411,15731968] .nil .nil) (.node [113184,430348,902208,1037644,3227782,5521457,5689661,8532035,11083800,13501056,13513411,15731968] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12aba_ok : tall (expFast false (classP') T11 11) T12aba = true := by decide +kernel
def T12abb : Tree := (.node [113184,430348,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968,16650112] (.node [113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,3227806,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,1037644,3227782,5689661,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,1037644,3227782,5521457,8532035,11083800,11219035,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,3227790,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,3227846,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,3227846,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,3228294,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil))) (.node [113184,430348,902208,3227782,3275430,5689661,8532035,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,3275430,5521457,8532035,8827215,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968,16010545] .nil .nil)) (.node [113184,430348,902208,3227782,4048070,5521457,5689661,8532035,11083800,13501056,15731968,16650112] (.node [113184,430348,902208,3227782,4048070,5521457,5689661,8532035,11083800,13501056,14566065,15731968] .nil .nil) (.node [113184,430348,902208,3227782,4048070,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil)))) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8532163,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,5521969,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,5521521,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968,16650112] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8632931,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8533059,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,14566065,15731968] .nil .nil))) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15732032] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15732032] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,13538188,15731968,16010545] .nil .nil) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15732480] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15814022,15875395] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15732480] .nil .nil) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13538188,14566065,15731968] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12abb_ok : tall (expFast false (classP') T11 11) T12abb = true := by decide +kernel
def T12ab : Tree := .node [113184,430348,902208,1037644,3227782,5521457,7684279,8532035,11083800,13501056,15731968] T12aba T12abb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12ab_ok : tall (expFast false (classP') T11 11) T12ab = true :=
  tall_node _ _ _ _ T12aba_ok (by decide +kernel) T12abb_ok
def T12a : Tree := .node [1024,113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] T12aa T12ab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12a_ok : tall (expFast false (classP') T11 11) T12a = true :=
  tall_node _ _ _ _ T12aa_ok (by decide +kernel) T12ab_ok
def T12baa : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5521457,8532035,8532051,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8242423,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,6145137,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,5689661,8632931,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,5521457,5689661,8533059,11083800,13501056,15731968] .nil .nil) .nil) (.node [113184,430348,902208,3227782,5521457,6145137,8532035,11083800,13501056,15731968,16330008] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8827215,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,8632931,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968,15875395] .nil .nil))) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11219035,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,8532163,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,8532059,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11123256,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,12148894,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,11254395,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,15814022] .nil .nil)))) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16650112] (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,13546447,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,13513411,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968,16330008] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,13538188,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,14566065,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil))) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,13538188,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,8895343,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968,15814022] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968,15814022] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,14566065,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,13513411,15731968,16010545] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12baa_ok : tall (expFast false (classP') T11 11) T12baa = true := by decide +kernel
def T12bab : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11123256,12148894,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545,16666545] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15732480] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15731976] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,14566065,15731968,16010545] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15731992] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022,16346526] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022,16330008] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545,16650112] .nil .nil))) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15732032] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731976] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731992] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13513411,15731968,16650112] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15732480] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13538188,14566065,15731968] .nil .nil)))) (.node [113184,430348,902208,3227782,5521521,5689661,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532163,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532051,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11219035,13501056,15731968,16330008] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532059,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521461,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8533059,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521465,8532035,11083800,13501056,15731968] .nil .nil))) (.node [113184,430348,902208,3227782,5521969,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521713,8532035,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5521521,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521969,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5689661,6145137,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,3227782,5689661,6145137,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5689661,7684279,8242423,8532035,11083800,13501056,15731968] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12bab_ok : tall (expFast false (classP') T11 11) T12bab = true := by decide +kernel
def T12ba : Tree := .node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,13538188,15731968,16010545] T12baa T12bab
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12ba_ok : tall (expFast false (classP') T11 11) T12ba = true :=
  tall_node _ _ _ _ T12baa_ok (by decide +kernel) T12bab_ok
def T12bba : Tree := (.node [113184,430348,902208,3227846,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,15814022,16010545] (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,16605241] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968,15814022] .nil .nil) (.node [113184,430348,902208,3227782,5689661,8532035,8632931,11083800,13501056,15731968,16010545] .nil .nil)) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,13538188,15731968,16010545] (.node [113184,430348,902208,3227782,5689661,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,14566065,15731968,16010545] .nil .nil))) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16076215] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,15814022,16605241] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,15814022,16076215] .nil .nil) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16010545,16666545] .nil .nil)) (.node [113184,430348,902208,3227790,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15875395,16010545] .nil .nil) (.node [113184,430348,902208,3227806,5521457,8532035,11083800,13501056,15731968] .nil .nil)))) (.node [113184,430348,1037644,3227782,5521457,6145137,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3275430,5521457,5689661,8532035,11083800,13501056,15731968,15814022] (.node [113184,430348,902208,3228294,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227846,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3228294,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,917088,3227782,4048070,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3275430,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,1037644,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] .nil .nil))) (.node [113184,430476,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,430364,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430349,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968] .nil .nil) (.node [113184,430380,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,431372,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,430476,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,431372,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12bba_ok : tall (expFast false (classP') T11 11) T12bba = true := by decide +kernel
def T12bbb : Tree := (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,14566065,15731968] (.node [113184,506668,902208,3227782,5689661,8532035,11083800,13501056,15731968,16010545] (.node [113184,506668,902208,3227782,5521457,5689661,8532035,8632931,11083800,13501056,15731968] (.node [113184,506668,902208,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] (.node [113184,506668,902208,1048428,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,506668,902208,3227782,5521457,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,506668,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15875395] (.node [113184,506668,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15814022] .nil .nil) (.node [113184,506668,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil))) (.node [113184,902208,3227782,5521457,5689661,8532035,8632931,8895343,11083800,13501056,15731968] (.node [113184,902208,3227782,3275430,5521457,5689661,8532035,8827215,11083800,13501056,15731968] (.node [113184,902208,1037644,3227782,5521457,5689661,8532035,11083800,13501056,13538188,15731968] .nil .nil) (.node [113184,902208,3227782,5521457,5689661,8532035,8632931,8827215,11083800,13501056,15731968] .nil .nil)) (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,13538188,15731968] (.node [113184,902208,3227782,5521457,5689661,8532035,8632931,11083800,11514140,13501056,15731968] .nil .nil) (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,13546447,15731968] .nil .nil)))) (.node [113200,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,902208,3227782,5521457,5689661,8532035,11083800,11514140,13501056,15731968,15814022] (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,15731968,16010545] (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,15731968,15814022] .nil .nil) (.node [113184,902208,3227782,5521457,5689661,8532035,8895343,11083800,13501056,15731968] .nil .nil)) (.node [113184,902208,3227782,5689661,7684279,8532035,8827215,11083800,13501056,15731968] (.node [113184,902208,3227782,5521457,5689661,8827215,11083800,13501056,15731968,15875395] .nil .nil) (.node [113184,902208,3227782,5689661,8532035,8827215,11083800,13501056,15731968,16010545] .nil .nil))) (.node [114208,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113312,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113208,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113312,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [430348,902208,3227782,3275430,5521457,5689661,8532035,8632931,11083800,13501056,15731968] (.node [114208,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [506668,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12bbb_ok : tall (expFast false (classP') T11 11) T12bbb = true := by decide +kernel
def T12bb : Tree := .node [113184,506668,902208,1037644,3227782,5521457,5689661,8532035,11083800,13501056,15731968] T12bba T12bbb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12bb_ok : tall (expFast false (classP') T11 11) T12bb = true :=
  tall_node _ _ _ _ T12bba_ok (by decide +kernel) T12bbb_ok
def T12b : Tree := .node [113184,430348,902208,3227782,5689661,7684279,8532035,8632931,11083800,13501056,15731968] T12ba T12bb
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12b_ok : tall (expFast false (classP') T11 11) T12b = true :=
  tall_node _ _ _ _ T12ba_ok (by decide +kernel) T12bb_ok
def T12 : Tree := .node [113184,430348,902208,3227782,5521457,5689661,8532163,11083800,13501056,15731968] T12a T12b
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T12_ok : tall (expFast false (classP') T11 11) T12 = true :=
  tall_node _ _ _ _ T12a_ok (by decide +kernel) T12b_ok
def T13a : Tree := (.node [113184,430348,506668,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [64,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [16,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [8,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [24,113184,430348,902208,3227782,5521457,5689661,8532035,13501056,15731968] .nil .nil)) (.node [64,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [24,113184,430348,902208,3227782,5521457,8532035,13501056,15731968] .nil .nil) .nil)) (.node [512,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [128,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [128,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [512,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil)) (.node [1024,113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [1024,113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,3275430,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,1037644,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,917088,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,430348,506668,902208,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,917088,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,3275430,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,1037644,3227782,5521457,8532035,11083800,13501056,15731968] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,5689661,7684279,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,4048070,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,4048070,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,5689661,6145137,8532035,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,8632931,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T13a_ok : tall (expFast false (classP') T12 12) T13a = true := by decide +kernel
def T13b : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,13513411,15731968] (.node [113184,430348,902208,3227782,5521457,6145137,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,13538188,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,15814022] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,16650112] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968,16010545] .nil .nil) .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11123256,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,8632931,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,8827215,11083800,13501056,15731968] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,12148894,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,11219035,13501056,15731968] .nil .nil) .nil))) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16650112] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15875395] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,14566065,15731968] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,13538188,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,15814022] .nil .nil)) (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16330008] (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968,16010545] .nil .nil) .nil)) (.node [113184,506668,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16010545] (.node [113184,430348,902208,3227782,5689661,7684279,8532035,11083800,13501056,15731968] .nil .nil) (.node [113184,430348,902208,3227782,5689661,8532035,11083800,13501056,15731968,16605241] .nil .nil)) (.node [113184,902208,3227782,5521457,5689661,8532035,11083800,11514140,13501056,15731968] (.node [113184,902208,3227782,5521457,5689661,8532035,8827215,11083800,13501056,15731968] .nil .nil) .nil))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T13b_ok : tall (expFast false (classP') T12 12) T13b = true := by decide +kernel
def T13 : Tree := .node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,13513411,15731968] T13a T13b
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T13_ok : tall (expFast false (classP') T12 12) T13 = true :=
  tall_node _ _ _ _ T13a_ok (by decide +kernel) T13b_ok
def T14 : Tree := (.node [113184,430348,902208,3227782,5521457,8532035,11083800,13501056,15731968] (.node [113184,430348,902208,3227782,5521457,5689661,8532035,11083800,13501056,15731968] .nil .nil) .nil)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem T14_ok : tall (expFast false (classP') T13 13) T14 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem start_ok : subsAll base10 (closed T14 14) = true := by decide +kernel

theorem noStart : NoStart false 14 :=
  start_sound (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (level_fast (classP'_sound false) (inv_leaf false) T1_ok) T2_ok) T3_ok) T4_ok) T5_ok) T6_ok) T7_ok) T8_ok) T9_ok) T10_ok) T11_ok) T12_ok) T13_ok) T14_ok) start_ok

-- bridge to the original L-meta-3420 statement (pairwise distinct words instead of dominance)

theorem take10_mem {x : BitVec 24}
    (h : x ∈ ([5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056, 15731968,
      5689661] : List (BitVec 24))) : x.toNat ∈ base10 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem base10_mem {y : ℕ} (h : y ∈ base10) :
    BitVec.ofNat 24 y ∈ ([5521457, 8532035, 3227782, 430348, 11083800, 113184, 902208, 13501056,
      15731968, 5689661] : List (BitVec 24)) ∧ (BitVec.ofNat 24 y).toNat = y := by
  simp only [base10, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, rfl⟩

theorem orig_sound (hc : NoStartH false 14) :
    ¬∃ (x1 : List (BitVec (24 : ℕ))),     x1.length = (24 : ℕ) ∧       List.take (10 : ℕ) x1 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧         x1.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧           ((0 : BitVec (24 : ℕ)) :: x1).Nodup ∧             ∀ (x2 : ℕ),               (0 : ℕ) < x2 →                 x2 < (15 : ℕ) →                   have x5 : BitVec (24 : ℕ) := x1.getD ((9 : ℕ) + x2) (0 : BitVec (24 : ℕ));                   x5 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take ((9 : ℕ) + x2) x1 ∧ x7 ∈ List.take ((9 : ℕ) + x2) x1 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7) := by
  rintro ⟨x1, hlen, htake, hlast, hnd, hstep⟩
  have hnd1 : x1.Nodup := (List.nodup_cons.mp hnd).2
  have h0 : (0 : BitVec 24) ∉ x1 := (List.nodup_cons.mp hnd).1
  have hf : ∀ i, i < 24 → ∃ h : i < x1.length, x1.getD i 0 = x1[i] := by
    intro i hi
    have h : i < x1.length := by omega
    exact ⟨h, by simp [List.getD_eq_getElem?_getD, h]⟩
  have hinj : ∀ i j, i < 24 → j < 24 → x1.getD i 0 = x1.getD j 0 → i = j := by
    intro i j hi hj he
    obtain ⟨h1, e1⟩ := hf i hi
    obtain ⟨h2, e2⟩ := hf j hj
    rw [e1, e2] at he
    exact (List.Nodup.getElem_inj_iff hnd1).mp he
  have hmem : ∀ i, i < 24 → x1.getD i 0 ∈ x1 := by
    intro i hi
    obtain ⟨h1, e1⟩ := hf i hi
    rw [e1]; exact List.getElem_mem h1
  have htk : ∀ (n : ℕ) (y : BitVec 24), y ∈ x1.take n → ∃ i, i < n ∧ i < 24 ∧ y = x1.getD i 0 := by
    intro n y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hy
    have hj' : j < n ∧ j < 24 := by rw [hlen] at hj; omega
    obtain ⟨h1, e1⟩ := hf j hj'.2
    exact ⟨j, hj'.1, hj'.2, e1.symm⟩
  have hbase : ∀ i, i < 10 → (x1.getD i 0).toNat ∈ base10 := by
    intro i hi
    obtain ⟨h1, e1⟩ := hf i (by omega)
    apply take10_mem
    rw [← htake, e1]
    exact List.mem_take_iff_getElem.mpr ⟨i, by rw [hlen]; omega, rfl⟩
  have key : ∀ j, j ≤ 14 → ∃ s : List ℕ, Tr false s ∧ s.length ≤ j ∧
      (∀ i, i < j → (x1.getD (10 + i) 0).toNat ∈ s ∨ x1.getD (10 + i) 0 = 16777215) ∧
      (∀ y ∈ s, ∃ i, i < j ∧ y = (x1.getD (10 + i) 0).toNat) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨[], Tr.nil, le_rfl, fun i hi => absurd hi (Nat.not_lt_zero i), fun y hy => by simp at hy⟩
    | succ j ih =>
      intro hj
      obtain ⟨s, hs, hl, h1, h2⟩ := ih (by omega)
      have hstepj : x1.getD (10 + j) 0 = 16777215 ∨ ∃ x6 x7 : BitVec 24,
          x6 ∈ x1.take (10 + j) ∧ x7 ∈ x1.take (10 + j) ∧
          (x1.getD (10 + j) 0 = x6 &&& x7 ∨ x1.getD (10 + j) 0 = x6 ||| x7) := by
        have h := hstep (j + 1) (by omega) (by omega)
        have e9 : 9 + (j + 1) = 10 + j := by omega
        rw [e9] at h
        exact h
      by_cases hones : x1.getD (10 + j) 0 = 16777215
      · refine ⟨s, hs, by omega, ?_, ?_⟩
        · intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · exact h1 i hi
          · exact Or.inr hones
        · intro y hy
          obtain ⟨i, hi, e⟩ := h2 y hy
          exact ⟨i, by omega, e⟩
      · obtain ⟨x6, x7, h6, h7, hop⟩ := hstepj.resolve_left hones
        have hop_mem : ∀ y : BitVec 24, y ∈ x1.take (10 + j) → y.toNat ∈ base12 ++ s := by
          intro y hy
          obtain ⟨i, hi, hi24, rfl⟩ := htk _ y hy
          by_cases h10 : i < 10
          · exact List.mem_append_left _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hbase i h10)))
          · obtain ⟨i', rfl⟩ : ∃ i', i = 10 + i' := ⟨i - 10, by omega⟩
            rcases h1 i' (by omega) with h | h
            · exact List.mem_append_right _ h
            · rw [h]; exact List.mem_append_left _ (by decide)
        refine ⟨s ++ [(x1.getD (10 + j) 0).toNat], ?_, by simp; omega, ?_, ?_⟩
        · refine Tr.snoc s _ hs (BitVec.isLt _) ?_ ?_
          · intro d hd
            show Nat.beq _ d = false
            rw [beq_false_iff]
            intro he
            rcases List.mem_append.mp hd with hd | hd
            · rcases mem12 hd with hd | hd | hd
              · apply h0
                have : x1.getD (10 + j) 0 = 0 := BitVec.eq_of_toNat_eq (by rw [he, hd]; rfl)
                rw [← this]; exact hmem _ (by omega)
              · exact hones (BitVec.eq_of_toNat_eq (by rw [he, hd]; rfl))
              · obtain ⟨hb1, hb2⟩ := base10_mem hd
                rw [← htake] at hb1
                obtain ⟨i, hi, hi24, e⟩ := htk _ _ hb1
                have : x1.getD (10 + j) 0 = x1.getD i 0 := by
                  rw [← e]; exact BitVec.eq_of_toNat_eq (by rw [he, hb2])
                have := hinj _ _ (by omega) hi24 this
                omega
            · obtain ⟨i, hi, e⟩ := h2 d hd
              have : x1.getD (10 + j) 0 = x1.getD (10 + i) 0 :=
                BitVec.eq_of_toNat_eq (by rw [he, e])
              have := hinj _ _ (by omega) (by omega) this
              omega
          · refine ⟨x6.toNat, hop_mem x6 h6, x7.toNat, hop_mem x7 h7, ?_⟩
            rcases hop with h | h
            · left; rw [h, BitVec.toNat_and]
            · right; rw [h, BitVec.toNat_or]
        · intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · rcases h1 i hi with h | h
            · exact Or.inl (List.mem_append_left _ h)
            · exact Or.inr h
          · exact Or.inl (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        · intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · obtain ⟨i, hi, e⟩ := h2 y hy
            exact ⟨i, by omega, e⟩
          · exact ⟨j, Nat.lt_succ_self j, List.mem_singleton.mp hy⟩
  obtain ⟨s, hs, hl, h1, _⟩ := key 14 le_rfl
  refine no_trace hc hs hl ?_
  have e : x1.getD (10 + 13) 0 = 4095 := hlast
  rcases h1 13 (by omega) with h | h
  · rw [e] at h; exact h
  · rw [e] at h; exact absurd h (by decide)

end PEqualNP.Outside.L_meta_3420

theorem PEqualNP.Outside.L_meta_3420 :
    ¬∃ (x1 : List (BitVec (24 : ℕ))),     x1.length = (24 : ℕ) ∧       List.take (10 : ℕ) x1 = [(5521457 : BitVec (24 : ℕ)), (8532035 : BitVec (24 : ℕ)), (3227782 : BitVec (24 : ℕ)), (430348 : BitVec (24 : ℕ)), (11083800 : BitVec (24 : ℕ)), (113184 : BitVec (24 : ℕ)), (902208 : BitVec (24 : ℕ)), (13501056 : BitVec (24 : ℕ)), (15731968 : BitVec (24 : ℕ)), (5689661 : BitVec (24 : ℕ))] ∧         x1.getD (23 : ℕ) (0 : BitVec (24 : ℕ)) = (4095 : BitVec (24 : ℕ)) ∧           ((0 : BitVec (24 : ℕ)) :: x1).Nodup ∧             ∀ (x2 : ℕ),               (0 : ℕ) < x2 →                 x2 < (15 : ℕ) →                   have x5 : BitVec (24 : ℕ) := x1.getD ((9 : ℕ) + x2) (0 : BitVec (24 : ℕ));                   x5 = (16777215 : BitVec (24 : ℕ)) ∨ ∃ (x6 : BitVec (24 : ℕ)) (x7 : BitVec (24 : ℕ)), x6 ∈ List.take ((9 : ℕ) + x2) x1 ∧ x7 ∈ List.take ((9 : ℕ) + x2) x1 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7) :=
  PEqualNP.Outside.L_meta_3420.orig_sound PEqualNP.Outside.L_meta_3420.noStart.toH
