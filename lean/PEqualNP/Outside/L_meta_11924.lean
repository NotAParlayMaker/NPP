import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11924


def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

-- A run: a list of live wire values that some gates turn into the single value y.
def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

section
variable {α : Type} {inv : α → α} {meet join : α → α → α} {y : α}
theorem Run.done : Run inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : Run inv meet join y s xs) :
    Run inv meet join y s zs := fun P d q u b => q p (h P d q u b)

theorem Run.one {s a r} (neg save : Bool)
    (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {s a b r} (c ka kb : Bool)
    (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {P : ∀ t ws, Run inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp
end

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (w :: ra) || (slack ≥ 2 && f (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (w :: r) || (slack ≥ 1 && (f (w :: a :: r) || f (w :: b :: r))) ||
            (slack ≥ 2 && f (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht := hf _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht := hf _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : List Nat → Bool)
    (hf : ∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : List Nat → Bool,
      (∀ ys, NatRun (mask k) (goal k) s ys → f ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  Nat.ble ws.length (s+1) &&
    (if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k)

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  have hl : Nat.ble ws.length (s+1) = true := Nat.ble_eq_true_of_le (run_len h)
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, hl, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

-- Each successor must fail the necessary condition or match a state of the next layer.
def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s zs))

theorem bar_sound {k S N idx pool} {s i : Nat} (hb : bar k S N idx pool s i = true)
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (zs : List Nat) := covers k s zs && !(scr k s pool zs) && !(found S N idx s zs)
    have hF (zs) (hz : NatRun (mask k) (goal k) s zs) : F zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p hz)
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx pool} {cap : Nat}
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)


open PEqualNP.CircuitLowerBounds

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool
abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl, ih, stepW, List.length_append, List.length_cons,
      List.length_nil]; omega

theorem foldl_stepW_getD (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl]
    rw [ih _ (by simp [stepW]; omega)]
    simp only [stepW]
    rw [List.getD_append _ _ _ _ h]

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (gs.foldl stepW (List.ofFn x)).getD a false

theorem eval_val (gs : List Gate) (n o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = val gs n o x := rfl

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [foldl_stepW_getD _ _ _ (by simp)]
  simp

theorem val_gate (gs : List Gate) (n p : ℕ) (hp : p < gs.length) (x : Fin n → Bool) :
    val gs n (n + p) x = (gs[p]).op.eval
      ((gs[p]).inputs.map fun i => if i < n + p then val gs n i x else false) := by
  have hsplit : gs = gs.take p ++ gs[p] :: gs.drop (p + 1) := by
    simp
  have hl : ((gs.take p).foldl stepW (List.ofFn x)).length = n + p := by
    rw [foldl_stepW_length]; simp; omega
  have key : ∀ i, i ≤ n + p → val gs n i x =
      (((gs.take p).foldl stepW (List.ofFn x)) ++
        [(gs[p]).op.eval ((gs[p]).inputs.map fun j =>
          ((gs.take p).foldl stepW (List.ofFn x)).getD j false)]).getD i false := by
    intro i hi
    unfold val
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    rw [foldl_stepW_getD _ _ _ (by simp [stepW, hl]; omega)]
    rfl
  rw [key (n + p) le_rfl, List.getD_append_right _ _ _ _ (by omega)]
  rw [hl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < n + p
  · rw [if_pos hi, key i (by omega), List.getD_append _ _ _ _ (by omega)]
  · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]

def IsConst {n : ℕ} (h : BFn n) : Prop := ∀ x y, h x = h y

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def ins (g : Gate) : List ℕ := if isNot g.op then g.inputs.take 1 else g.inputs

def Eff (gs : List Gate) (n p i : ℕ) : Prop :=
  ∃ h : p < gs.length, ¬ IsConst (val gs n (n + p)) ∧ i ∈ ins (gs[p]) ∧ i < n + p ∧
    ¬ IsConst (val gs n i)

inductive Rel (gs : List Gate) (n o : ℕ) : ℕ → Prop
  | out : Rel gs n o o
  | step (p i : ℕ) : Rel gs n o (n + p) → Eff gs n p i → Rel gs n o i

def Need (gs : List Gate) (n o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ Rel gs n o (n + q) ∧ Eff gs n q a

open Classical in
noncomputable def live (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Need gs n o p a))

theorem mem_live (gs : List Gate) (n o p a : ℕ) :
    a ∈ live gs n o p ↔ a < n + p ∧ Need gs n o p a := by
  simp [live]

theorem nodup_live (gs : List Gate) (n o p : ℕ) : (live gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem eff_lt {gs : List Gate} {n p i : ℕ} (h : Eff gs n p i) : i < n + p := h.2.2.2.1

theorem eff_nc {gs : List Gate} {n p i : ℕ} (h : Eff gs n p i) : ¬ IsConst (val gs n i) :=
  h.2.2.2.2

theorem eff_gate_nc {gs : List Gate} {n p i : ℕ} (h : Eff gs n p i) :
    ¬ IsConst (val gs n (n + p)) := h.2.1

theorem need_iff (gs : List Gate) (n o p a : ℕ) :
    Need gs n o p a ↔ Need gs n o (p + 1) a ∨ (Rel gs n o (n + p) ∧ Eff gs n p a) := by
  unfold Need
  constructor
  · rintro (h | ⟨q, hq, hr, he⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.eq_or_lt_of_le hq with rfl | hq
      · exact Or.inr ⟨hr, he⟩
      · exact Or.inl (Or.inr ⟨q, hq, hr, he⟩)
  · rintro ((h | ⟨q, hq, hr, he⟩) | ⟨hr, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, hr, he⟩
    · exact Or.inr ⟨p, le_rfl, hr, he⟩

theorem need_rel {gs : List Gate} {n o p a : ℕ} (h : Need gs n o p a) : Rel gs n o a := by
  rcases h with rfl | ⟨q, _, hr, he⟩
  · exact Rel.out
  · exact Rel.step q a hr he

theorem need_nc {gs : List Gate} {n o p a : ℕ} (hnc : ¬ IsConst (val gs n o))
    (h : Need gs n o p a) : ¬ IsConst (val gs n a) := by
  rcases h with rfl | ⟨q, _, _, he⟩
  · exact hnc
  · exact eff_nc he

theorem Run.ne_nil {α : Type} {inv : α → α} {meet join : α → α → α} {y : α} {s : ℕ}
    {ws : List α} (h : Run inv meet join y s ws) : ws ≠ [] := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => intro e; subst e; exact ih (List.Perm.eq_nil hp)
  | one => simp
  | two => simp

theorem Run.idle {α : Type} {inv : α → α} {meet join : α → α → α} {y : α} {s : ℕ}
    {ws : List α} (h : Run inv meet join y s ws) : Run inv meet join y (s + 1) ws := by
  obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  exact Run.one false false h

section shape
variable {n : ℕ} (v : BFn n) (rd val' : ℕ → BFn n) (U : ℕ → Prop) (EffP : ℕ → Prop)

def ShapeOK : Prop :=
  (∃ j, ∃ neg : Bool, (∀ i, EffP i ↔ i = j) ∧
        v = (if neg then invF (val' j) else val' j)) ∨
    (∃ j k, ∃ c : Bool, j ≠ k ∧ (∀ i, EffP i ↔ i = j ∨ i = k) ∧
        v = (if c then meetF (val' j) (val' k) else joinF (val' j) (val' k)))

theorem shape_one (hnc : ¬ IsConst v) (rd_u : ∀ i, U i → rd i = val' i)
    (rd_c : ∀ i, ¬ U i → ∃ c : Bool, rd i = fun _ => c)
    (i : ℕ) (neg : Bool) (hv : v = if neg then invF (rd i) else rd i)
    (he : ∀ a, EffP a ↔ a = i ∧ U a) : ShapeOK v val' EffP := by
  by_cases hu : U i
  · left
    refine ⟨i, neg, fun a => ?_, by rw [hv, rd_u i hu]⟩
    rw [he]
    constructor
    · rintro ⟨rfl, _⟩; rfl
    · rintro rfl; exact ⟨rfl, hu⟩
  · exfalso
    obtain ⟨c, hc⟩ := rd_c i hu
    apply hnc
    intro x y
    rw [hv, hc]
    cases neg <;> rfl

theorem shape_two (hnc : ¬ IsConst v) (rd_u : ∀ i, U i → rd i = val' i)
    (rd_c : ∀ i, ¬ U i → ∃ c : Bool, rd i = fun _ => c)
    (i j : ℕ) (c : Bool) (hv : v = if c then meetF (rd i) (rd j) else joinF (rd i) (rd j))
    (he : ∀ a, EffP a ↔ (a = i ∨ a = j) ∧ U a) : ShapeOK v val' EffP := by
  by_cases hui : U i <;> by_cases huj : U j
  · by_cases hij : i = j
    · subst hij
      left
      refine ⟨i, false, fun a => ?_, ?_⟩
      · rw [he]
        constructor
        · rintro ⟨h | h, _⟩ <;> exact h
        · rintro rfl; exact ⟨Or.inl rfl, hui⟩
      · rw [hv, rd_u i hui]
        funext x
        cases c <;> simp
    · right
      refine ⟨i, j, c, hij, fun a => ?_, by rw [hv, rd_u i hui, rd_u j huj]⟩
      rw [he]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, hui⟩
        · exact ⟨Or.inr rfl, huj⟩
  · obtain ⟨d, hd⟩ := rd_c j huj
    by_cases hcd : c = d
    · left
      refine ⟨i, false, fun a => ?_, ?_⟩
      · rw [he]
        constructor
        · rintro ⟨rfl | rfl, hh⟩
          · rfl
          · exact absurd hh huj
        · rintro rfl; exact ⟨Or.inl rfl, hui⟩
      · rw [hv, rd_u i hui, hd]
        funext x
        subst hcd
        cases c <;> simp
    · exfalso
      apply hnc
      intro x y
      rw [hv, hd]
      cases c <;> cases d <;> simp_all
  · obtain ⟨d, hd⟩ := rd_c i hui
    by_cases hcd : c = d
    · left
      refine ⟨j, false, fun a => ?_, ?_⟩
      · rw [he]
        constructor
        · rintro ⟨rfl | rfl, hh⟩
          · exact absurd hh hui
          · rfl
        · rintro rfl; exact ⟨Or.inr rfl, huj⟩
      · rw [hv, rd_u j huj, hd]
        funext x
        subst hcd
        cases c <;> simp
    · exfalso
      apply hnc
      intro x y
      rw [hv, hd]
      cases c <;> cases d <;> simp_all
  · exfalso
    obtain ⟨d, hd⟩ := rd_c i hui
    obtain ⟨e, he'⟩ := rd_c j huj
    apply hnc
    intro x y
    rw [hv, hd, he']
    cases c <;> rfl
end shape

-- The shape of a relevant gate that is not constant.
theorem gate_shape (gs : List Gate) (n p : ℕ) (hp : p < gs.length)
    (hg : (gs[p].op = GateOp.and ∨ gs[p].op = GateOp.or ∨ gs[p].op = GateOp.not) ∧
      gs[p].inputs.length ≤ 2)
    (hnc : ¬ IsConst (val gs n (n + p))) :
    ShapeOK (val gs n (n + p)) (val gs n) (Eff gs n p) := by
  classical
  set g := gs[p] with hgdef
  let rd : ℕ → BFn n := fun i x => if i < n + p then val gs n i x else false
  have hv : val gs n (n + p) = fun x => g.op.eval (g.inputs.map fun i => rd i x) := by
    funext x; exact val_gate gs n p hp x
  let U : ℕ → Prop := fun i => i < n + p ∧ ¬ IsConst (val gs n i)
  have rd_u : ∀ i, U i → rd i = val gs n i := by
    intro i hi; funext x; simp [rd, hi.1]
  have rd_c : ∀ i, ¬ U i → ∃ c : Bool, rd i = fun _ => c := by
    intro i hi
    by_cases hlt : i < n + p
    · have hc : IsConst (val gs n i) := by
        by_contra hc; exact hi ⟨hlt, hc⟩
      by_cases hn : Nonempty (Fin n → Bool)
      · obtain ⟨x0⟩ := hn
        refine ⟨val gs n i x0, ?_⟩
        funext x; simp only [rd, if_pos hlt]; exact hc x x0
      · exact ⟨false, funext fun x => (hn ⟨x⟩).elim⟩
    · exact ⟨false, by funext x; simp [rd, hlt]⟩
  have effI : ∀ i, Eff gs n p i ↔ i ∈ ins g ∧ U i := by
    intro i
    constructor
    · rintro ⟨_, _, h1, h2, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨hp, hnc, h1, h2, h3⟩
  obtain ⟨hop, hlen⟩ := hg
  rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · exfalso
    apply hnc
    intro x y
    rw [hv]
    rcases hop with h | h | h <;> simp [hin, h, GateOp.eval]
  · have hins : ins g = [i] := by rcases hop with h | h | h <;> simp [ins, h, hin, isNot]
    refine shape_one _ rd _ U _ hnc rd_u rd_c i (isNot g.op) ?_ ?_
    · rw [hv]; funext x
      rcases hop with h | h | h <;> simp [hin, h, GateOp.eval, isNot]
    · intro a; rw [effI, hins, List.mem_singleton]
  · rcases hop with h | h | h
    · refine shape_two _ rd _ U _ hnc rd_u rd_c i j true ?_ ?_
      · rw [hv]; funext x; simp [hin, h, GateOp.eval]
      · intro a; rw [effI]; simp [ins, h, hin, isNot]
    · refine shape_two _ rd _ U _ hnc rd_u rd_c i j false ?_ ?_
      · rw [hv]; funext x; simp [hin, h, GateOp.eval]
      · intro a; rw [effI]; simp [ins, h, hin, isNot]
    · refine shape_one _ rd _ U _ hnc rd_u rd_c i true ?_ ?_
      · rw [hv]; funext x; simp [hin, h, GateOp.eval]
      · intro a; rw [effI]; simp [ins, h, hin, isNot]
  · exfalso
    simp [hin] at hlen
theorem live_top (gs : List Gate) (n o : ℕ) (ho : o < n + gs.length) :
    (live gs n o gs.length).Perm [o] := by
  refine (List.perm_ext_iff_of_nodup (nodup_live _ _ _ _) (List.nodup_singleton o)).2 ?_
  intro a
  rw [mem_live, List.mem_singleton]
  constructor
  · rintro ⟨_, h | ⟨q, hq, _, he⟩⟩
    · exact h
    · exact absurd he.1 (by omega)
  · rintro rfl; exact ⟨ho, Or.inl rfl⟩

theorem need_new (gs : List Gate) (n o p : ℕ) (hnc : ¬ IsConst (val gs n o))
    (h : Need gs n o (p + 1) (n + p)) : Rel gs n o (n + p) ∧ ¬ IsConst (val gs n (n + p)) :=
  ⟨need_rel h, need_nc hnc h⟩

theorem live_idle (gs : List Gate) (n o p : ℕ) (hnc : ¬ IsConst (val gs n o))
    (hidle : ¬ (Rel gs n o (n + p) ∧ ¬ IsConst (val gs n (n + p)))) :
    (live gs n o (p + 1)).Perm (live gs n o p) := by
  refine (List.perm_ext_iff_of_nodup (nodup_live _ _ _ _) (nodup_live _ _ _ _)).2 ?_
  intro a
  rw [mem_live, mem_live, need_iff gs n o p a]
  constructor
  · rintro ⟨hlt, hn⟩
    by_cases ha : a = n + p
    · subst ha; exact absurd (need_new gs n o p hnc hn) hidle
    · exact ⟨by omega, Or.inl hn⟩
  · rintro ⟨hlt, hn | ⟨hr, he⟩⟩
    · exact ⟨by omega, hn⟩
    · exact absurd ⟨hr, eff_gate_nc he⟩ hidle

theorem live_succ (gs : List Gate) (n o p : ℕ) (hnc : ¬ IsConst (val gs n o))
    (hr : Rel gs n o (n + p)) (a : ℕ) :
    a ∈ live gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ live gs n o p ∧ (Eff gs n p a → Need gs n o (p + 1) a)) := by
  rw [mem_live, mem_live, need_iff gs n o p a]
  constructor
  · rintro ⟨hlt, hn⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · exact Or.inr ⟨⟨by omega, Or.inl hn⟩, fun _ => hn⟩
  · rintro (rfl | ⟨⟨hlt, hn⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hr with _ | ⟨q, _, hq, he⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨q, by have := eff_lt he; omega, hq, he⟩
    · refine ⟨by omega, ?_⟩
      rcases hn with hn | ⟨hr', he⟩
      · exact hn
      · exact himp he

open Classical in
theorem run_live (gs : List Gate) (n o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnc : ¬ IsConst (val gs n o)) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((live gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hpl : p = gs.length := by omega
    subst hpl
    exact Run.perm ((live_top gs n o ho).map (val gs n)).symm Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    have IH := ih (p + 1) (by omega)
    by_cases hact : Rel gs n o (n + p) ∧ ¬ IsConst (val gs n (n + p))
    · obtain ⟨hr, hgnc⟩ := hact
      have hstep := live_succ gs n o p hnc hr
      have hin : ∀ a, Eff gs n p a → a ∈ live gs n o p := fun a ha =>
        (mem_live _ _ _ _ _).2 ⟨eff_lt ha, Or.inr ⟨p, le_rfl, hr, ha⟩⟩
      have hnew : ∀ a ∈ live gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_live _ _ _ _ _).1 ha).1
      have hnd0 := nodup_live gs n o p
      have hshape := gate_shape gs n p hplt (hg _ (List.getElem_mem hplt)) hgnc
      rcases hshape with ⟨j, neg, hmem, hval⟩ | ⟨j, k, c, hjk, hmem, hval⟩
      · have hj := hin j ((hmem j).2 rfl)
        have hp1 : (live gs n o p).Perm (j :: (live gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((live gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (live gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Need gs n o (p + 1) j)) j ((live gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_live _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      · have hjm := hin j ((hmem j).2 (Or.inl rfl))
        have hkm := hin k ((hmem k).2 (Or.inr rfl))
        have hke : k ∈ (live gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((live gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((live gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (live gs n o p).Perm
            (j :: k :: ((live gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((live gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ live gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (live gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Need gs n o (p + 1) j)) j
              (kept (decide (Need gs n o (p + 1) k)) k
                (((live gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_live _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp3 := live_idle gs n o p hnc hact
      exact (Run.perm (hp3.map (val gs n)) IH).idle

theorem exists_run {n : ℕ} (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (f : BFn n) (hf : ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') :
    ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f gs.length ws := by
  have hvo : val gs n o = f := funext fun x => (eval_val gs n o x).symm.trans (hf x)
  have hnc' : ¬ IsConst (val gs n o) := by
    rw [hvo]; obtain ⟨y, y', h⟩ := hnc; exact fun hc => h (hc y y')
  have ho : o < n + gs.length := by
    by_contra hout
    apply hnc'
    intro x y
    simp only [val]
    rw [List.getD_eq_default _ _ (by rw [foldl_stepW_length]; simp; omega),
      List.getD_eq_default _ _ (by rw [foldl_stepW_length]; simp; omega)]
  refine ⟨(live gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · rw [← hvo]
    exact run_live gs n o hg hnc' ho gs.length 0 (by omega)

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

-- The edge function of the graph with edges 0-4 1-4 2-4 0-5 1-5 3-5 0-6 1-6 2-6 4-6 5-6.
abbrev fG : BFn 7 := fun x => (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) ||
  (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) ||
  (x 4 && x 6) || (x 5 && x 6)

theorem rhs_eq : ∀ x : Fin 7 → Bool,
    decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = fG x := by decide +kernel

-- Ten AND and OR gates: a = x0 or x1, b = a or x2, c = a or x3, then
-- (x4 and b) or (x5 and c) or (x6 and (b or x4 or x5)).
def upGates : List Gate :=
  [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [4, 8]⟩,
   ⟨GateOp.and, [5, 9]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [13, 5]⟩,
   ⟨GateOp.and, [6, 14]⟩, ⟨GateOp.or, [12, 15]⟩]

theorem upMono : ∀ g ∈ upGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

theorem upLen : upGates.length = 10 := rfl

theorem upper_eval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨upGates, 16⟩ (List.ofFn x) = fG x := by
  decide +kernel
def kk : Nat := 75

def rowsG : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 12, 12, 12, 13, 13, 13, 14, 14, 14, 15, 15, 15, 16, 16, 16, 16, 24, 24, 24, 24, 24, 32, 32, 32, 32, 36, 36, 36, 36, 36, 48, 48, 48, 48, 48, 64, 64, 64, 64, 64, 72, 72, 72, 72, 72, 17, 33, 65, 18, 34, 66, 19, 35, 67, 20, 68, 21, 37, 69, 22, 38, 70, 23, 39, 71, 40, 25, 41, 73, 26, 42, 74, 27, 43, 75, 28, 44, 76, 29, 45, 77, 30, 46, 78, 31, 47, 79, 17, 18, 20, 80, 25, 26, 28, 56, 88, 33, 34, 40, 96, 37, 38, 44, 52, 100, 49, 50, 52, 56, 112, 65, 66, 68, 80, 96, 73, 74, 76, 88, 104]

def xsG : List Nat := [0x21084423c71c771ce38000000038e38ee39c7, 0x42108845f81f87e0fc000000003f03f0fc1f8, 0x8427c089ffe007ff000000f8003ffc00ffe00, 0x3e04113e1fffff800007c00007c3fffff00000, 0x108fa03fe4924912524801f007fc0000000000, 0x210fffd0092492a4849001fff8000000000000, 0x3ff84221124924492927fe0000000000000000]

def NN : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 4
  | 5 => 72
  | 6 => 366
  | 7 => 361
  | 8 => 73
  | 9 => 1
  | _ => 0

def HT : Nat → Nat
  | 4 => 0xc0b98a3c3bbc1d3e21efd0bb0371f804
  | 5 => 0xfecfee04fd0fcebbfbf00d79fb5a7697faecc504f6dcf6b4f1c1fb79ea5cb830e6f1f1fce4613287e39c7f64e18de119ddb7b9c4dae2c82edac81346d8ea3ad9d3876154d350edb8cebf2dd7cc00beb2c7262e91be68e190b401f72db06c23e8ab2e0166a7ea6cf2a184f7c699e08f8a984f7f869733cdc29542d46c92ba241b8f1fe69c8ed5a4358897f09687f9d3fd81f7301c81282b447d65703b7bc878957a626e6179da3c8378fd72b47809eba976f7a82d7193974a70b799f0705f6ce26b54c06b6acdc97767028ef25fa5f99a5bba1c424c7a4ac444f3b80d44efe523434b378c42fab434404eb14c3eee00433e17061d37aa92e72cc7a00d1f98abe91b284b3a19f008bc1546513c12fb538a0d6b266c062b1f9200bd502100652313
  | 6 => 0xffc27e60ffbf7e4cff2f1b84fbfaf0affbb5d5dffafe072ffa6196b6f807ee04f736a25cf6cbb2a6f603e3b3f4de660cf45608eaf3f4950df2e6fec8f0929b17f0245e4defb0ca25ef377d46ee49dc78ed5e4c4bed476f80ece52c44ecb23d2cec8abb7eebf847d3eb8731d3eb5a17b9eb01eaabeab9df5cea93dbe0ea6f31d6ea3c22fee9c60993e9b92823e93fd1cae82adf4be7dbfe16e752e83ee6e3ae65e6021bffe5f90902e5f73e34e4ef0334e4c16400e47379b9e42c91f1e412b75ae3d81fd3e364887ae34ba794e271377fde226089dd924bd8dc16a447dbd880c9db3ec193dad55403dacfaa6dd96433a2d94676cad8ea3ad9d75dfb24d7577a51d74e1dd8d67f1900d545f24fd530c96dd48a1c0ed3767331d368c842d29963e8cffe020ecfb95c1dcf312a3fcf030a9ece21d422cdc9a714cc92d7cdcc771b38cc4e95e9cc245352cc0dcbeccbd5a448cb44e555caecb847ca99f12bc9f5bda8c99d909ac98c92ffc90247b5c8befa9dc8a3f1f4c5e20bd0c5b14d65c537f70cc492e423c4792aa5c3d42358c3a3e537c2cbbea2c270ef8ec2407d20c16f41eac024b733bfd1c46abf59b17dbdef8402bdedb555bdb8cf22bd0e1609bc400f40bb85f5b3bac22f08b839cb51b7cb3de9b74f5bd4b71fef03b58185a8b55b70f9b4fce756b422ebeeb3d43a17b3a7e6b4b2aee292b1e62dcaaff89774ad5a42feac8c99e2ac1371d8ab30574eaad90f9daa732e8ea860179ba82696b4a7842077a70ba3dda6c9414da653d8c8a618925da5f2fee1a59be367a41341caa3557792a33a03b1a2cf4d50a260b6b5a1a87637a1a45777a0b571be9f4889fc9d5727529cfefa449cb374d59b81404f9ade89a49ad87ea497f44dcd95cac903954cd1a9944d7d2093ddadb0934153c092ec4e8f92d4ec0292907a9591a55c8990ff4272907ad3588f5b4b588f14832e8c4283048938eb5c88d6857288ce611488c40cc38867584d87c6140c878f817686ee67eb8373abed8210b79f81b88a917da35e3a7d78234b7d3a64b97d2a07e17cadde1a7bc6342d7b8925867b2316c17ab0eaaa7a58bd9c79accb1079a3736579726bd2792b18567892856c7607d23075febf3375b5969f754e112574666ef27362bc857354deed717a9af370e914df70b799f06ff396c26f397e416f21e08e6eea21b56a08f583698748306900af976892e9b567f770686671804d655476db64ff35fe6391b829635b5f2f631ae19962c2142861946fca5f6926015d3f3c4f5c3a283b5ba0d40f5b48a7015b277db65ac9903f59c3aa02596b7cf4580e11c157ec14f256bc5dd2563dfa8a56143ddd55d40fc255c4a43155bc10cf55b2baad556a91145460d07d54476127541d31a252d09a79527c6c215269b66f5266bc7c50b16458509bce63508943a74fd168364e4b29bc4e34bced4e2d20424e2ba9f04d338b6b4cc59f114bc9632f4b3f7d9b4abe285d49bc4fe34961aba548a619cb481a3dbf47df06a947c7d89c47c6f26745a4123d44ea039a445c2c33442df9ab44132570439adbed4373c51242c8c1e342b498c341d15b68411de1ba40864835403b724740171b253da616523da5f17c3cfbad1d3c1b2c833adbf1ab3acc04d63a02c87439aa9b6638324d7d35ff3adc35da0a783559e64435555eb0349feeef3406370330ce104e30b2d4e13075e340301fe16e2ff983122f14d5e52e44b8fd2df591bb2d8731622c8168e92c57479e2c29680e2b6f7b6b2b6b36c92b69404928c2a47e28bda78d28a7db7928750f0127c587bd25def04125219bf424ae149424256a6723b05a97237592c1218d139a216dadaf20ade6991fbdb0a21f6bea541dc103f11c7d1c521ae183801a34908c18003e4917a8113b16fc459716eed98b16b60662151f471e1326ff73129d64c4124537b611ed88060fe5523a0f89eab00ee57b200e2d6e800d5ca1e90d0851130cfcc0710b4499140a87279108c93ec307a74abc0767a0ad072d10ef06d902760611855904345b4c0200e2be0138d3a6011be9f500bd50210084ef27
  | 7 => 0xffca1c4afe17f484fdd8069ffd4bede7fcdb0e33fc629199fb6f8019faf2d123f96a2f86f9076af2f8ac654ef8a93d6af8263b0cf75226b1f6a5c6a7f5084afff2ae150ef255e800f20a6291f10d7f31f0357760effb6cb9eff259bcef9cbba3ef183a88edef0e79ed78f269ed4b3b89eb5a17b9eaa3bf65e9349b6ce898417ce87c360ae80fdaffe79309e0e757ff8ee71c3482e6fc4a45e699f4fbe656302ee5d1c114e503fa3be1a58feee19970c0e09a2ec4e0511c30df4e6ff4de767ca1de2d732edde0f6bddd451034dba634c5db7ab4a5d8d962ddd870d7c8d7a84ce7d767a55bd70f784dd39ca52bd36de004d2fa4bf6d2efb237d204cbd6d11d21e9d0eb561ed0e24321d0e21516d071ffc5d007d866cfafab58cf0e2c11cf051914ce21d422cc118fdbcb707356cb5ebfeccb44e555cacdce14caa4fee1ca20db20c9f5bda8c8abcca9c7a3277fc61d8da3c54a847ec4b1c2e6c4906bfdc478ce4ac4410f71c4080041c3f7b946c349b8e8c270ef8ebfa305c3bf4ad8b5bede35ecbe579d53be4e9205bde9d771bca8334cbbc86e09ba402c3eb8b24cebb89c5fa1b5f1af11b55b70f9b5479b49b4c013bdb44cf043b0f7c1cbb0dd4739b09f94bdb0207dfbaf443786af1a97beaec26ab0ad4302aeac4360a9ac134b8eab94e846ab2afd7eab09a869a9b7be39a99e4ee3a9741f5ea8278835a76545dfa6d0b74da618925da60f7f60a5e03163a5a1ac4ba56f97bca46a4b5fa41d69b5a3c4823ea3840dfea382b507a2680586a208225fa12050eba11a34e3a0966b579e16236c9dfd07879d981cb19d712b7b9d5727529d35f4659d1ec6589c9e87c59c71d3649bbaf2a49b440861999849b49984e767996a132c981faf9f972849249674cf7695dd35f19592600392fd040e91a55c899032df678f6730cb8f59b6308f0189228e6889c28e13fdac8d7007ca8d4ac0588d41ad5b8ce9804d8b30f8348ab0d40089f6dcab88d6857288d2acb287ded3d687cec8b08624fe0a86027c7c85ccd0fc852fc1ef846bc3a1840eb90e8403a0b082de1f1e82a3b5688210b79f8207771881eb97db81d856a581ae355a80c6692780c224857fd2c2aa7bfa11167b193ab07acee88a7ab0eaaa7a7889b07a05025079e2084176c49b6b76524b3975149e5e733e1d4272c558f071abdf8870c34b876e83a61a6d572c056cfefef76c5333536afc35b96a13b70d67f45280679c257264e0d86c6253ae2d6201168561a8e977615ffa0060a499cd609b86d05fde154d5fd878c35eeda0f85e202c7f5cbe8e695c9e3d005c83feab5c3712275c2ff0325ba0d40f5b6873155b277db659f786eb59c3aa02599f59dd598b4908594a93f758f266e95757d07a5692bb55568fc1625672d7b156143ddd55be8cfa55196c2155166c0d5494ad66548609455151de70510cc3a05054f4f050342f9a4c22a0674b5ad1744a3553cd49acf6ab45e988d84558a0b54507b7e644f9eed143a0ca39436c56364086546c3feac9a13f403fbc3f372cbf3f238d633f1015e43d81cd0c3d32ebd73c2613423a45f0f53a1851c13a02c87439ca677a39683a5139482408392f0d9437c8254037b25ea5379b93ac377bcc0f36af950c35ac93e133d078b13363d87b32e939993203b7ac30ce104e3095af54302c41c42ebb21632d26af522aabdfab2aa5f30d2a9ce0102a72e5ec29e109cf29b37f1e28cd60f228bfb60327dbcb602554efcf2459f85f24115fd32278f1db225f82852253b229217b41132164b9ad212ff338212c92091faba1fb1f4cab691f1fa3e61e5935761b6d78f31b5a01741b083b26192b111918fad2f818003e4917c7dd4f17a8113b14b09f3e134671c3130fbce312a1a966129d64c412989669126503ca1196fd0110dce37410467d2010191cc90dff51c10d3c2dfc0d222baa0ca649950c76dcc40c71c7cf0bed064f098c26a508fed47507418c9706e6cba0057962890468383503bb4541038548db03439b8e02b130bf016671810087450f
  | 8 => 0xfb6f8019f9745771f75f101bf36d1128f2ae150ef09af61de6fc4a45e3bf777ee2a1ae14e2989b17d767a55bd7428597d007d866cf38f5fdbfa305c3b6b6e7bcb4448eb4b18dffe3b0f7c1cbaf4e74a7af1a97beaea181b3ae4954a5ab157ab6917d00fe8f59b6308ebf280d8d41ad5b8b03819d875aa5688624fe0a8002cd677d32b91c77cfdf9777b670417686e0f475028fb7747691a270c466af6d572c056cfefef767f8972267f45280620116855ee314615c987a535ad0504559f786eb591232fd58dc36974e5e58b34e002b2b46646cf245525a7a446f28493c7322433bf0e2bc35f11c8535a809f13337e47e2e30509e2cff3aa828c4cdc528469ff8264243df263902d7246519d220c7611718003e4917c7dd4f13a57fc60df34d62019a4e6a
  | _ => 0

def IW : Nat := 8

def SW : Nat := 150

def DD : Nat := 0x2e77fddefffffffffff8000f8003ffffefffff9cf77f59ffd7ffff3fe00000000ff8ffbfe7fce73eccefffbff7ffff800000003fe3feff9ffb8d67779ffffffff3fe00000000fffffbfe7fe10ddfd0092492a48490000000000000000000672988a600280000c01ffffffff00700401803ffddff11b6db6edadb7fe0000000000000000843fff59b6d36edb1b6007ffe000000000000108facffedb2db36d6d801f007fc0000000000294b912afbef1deff8e00000000e38e3b8e71e4259dd45fa5fafe8fd000000003f03f0fc1f8981044587fd7fe0000000000000ff8ff8000037bd8ff77ff1ffffcffffff07ffffe3ffff9fffff35dc46db6dba6b4dff80000000000000000843fcc89ffe927ff490000f8003ffc00ffe00fff56ec46db6dbb4b69ff80000000000000002739cec67ff1ff7fcff800000003fe3feff9ff77adaab70a28a038c71ffffffff1c71c4718e3e34113e1fffffc90927c00007c3fffff000008c735d48f5d75fc738e00000000e38e3b8e71dbdae66ba05a0501f03ffffffffc0fc0f03e079cffff406d96dbb636c007ffe0000000000000c63688cdfdbf87f7fc000000003f03f0fc1f85ae6339dffc7fdff3fe00000000ff8ffbfe7fce427c0e9fffff7ff000000f8003ffffeffe00b19df6737fffebffff00003e000ffffc3fffe318c0331000000800007fff07ffc00001000008016774024924a9212400000000000000000008427008800e00003000000f800001c0000600989466597fd7fff83f000000000ff8ffbf07e22159dd23d75d7f5ceb8000000038e38ee39c71fefbb1fffc7fdffffe0ffffe0fff8ffbfffffe059dfe1fffffa48497c00007c3fffff00000210ff03bfff925ffc920003e000fff003ff802c25199c5ffffafe0fc000000003ffff0fc1f85afe80ffdb4db56d6da007c01ff00000000000e71ccc67ff9ff7feff800000003fe3feff9fffff77ffdffffffffbffff8001f0fffffffe7fea14955a3fffd7f1ce3800000003fff8ee39c739c9f0227ffc91ffe480003e000fff003ff803e041d3e1fffffffc007c00007c3fffffff80038c67339fffffdff3fe00000000fffffbfe7fc1ca62018000000030003ffff83c0000000600e01044e000380200001f00001f000700400003ff9cee11b69b66dadb7fe0000000000000000f81644f9fffffe49093f00001f0fffffc0000252d5b945fa5fafe0fc000000003f03f0fc1f898d67759ffd7ffff3fe00000000ff8ffbfe7fc633accefff3ff7fdff800000003fe3feff9ff000eb33b924924db5b6007fffffffffffffffe61495563ff5fff1ce3800000003fe3fee39c7ffe7089ddb65b56dadbff80000000000000002a56fd5abfffd7fffe38000f8003fff8efffc7f81466f87ffffe90121f00001f0fffffc000021ffffd1e92492fffff83ffff83c00000fffff000eb303800000db5b6007ffe0f000003ffffc8427808838e000e3000000f800071c001c6004a62118cf1c71dc738e00000000e38e3b8e71c423288cdf93f87e5fc000000003f03f0fc1f8210bf02afff905ffc820003e000fff003ff80000180066490491242480000000000000000008012554024924a8210400000000000000000020051990092492a40480000000000000000000f7bdeef77e3fe3f8ff1fffffffffc7fc7f1fe00018cc0092092248490000000000000000000042fbb0000000092124007ffe0000000000000630000012412449092000000000000000000018c21108f9c79de73ce00000000e38e3b8e71fe06313e9fffff925007c00007c3fffff00000fbd044ffffffff6dedbff8001ffffffffffffc3fbeec3fc71c77ffff83ffff83f8e38effffff89044f87fffff20241f00001f0fffffc000002108c423ff1c77fce3800000003fe38eff9c7210980225b68016dc0000000000000000000000000c001ff0007fc00000000003fe000ff8004a7e80ffd34d354d69a007c01ff0000000000240411141fa5fa80000000000003f03f0000007fefbbbfdb6db5fffffffffffffffffffffffd8cfe03ff6da495b724801f007fc0000000000f81064f87ffffff8001f00001f0fffffff000042188867f91f97e4fc800000003f03f0fc1f83109f0327fffe1ffc000003e000ffffc3ff800a50c4423e79c779ee38000000038e38ee39c794bfff406c96cbb2364007ffe0000000000000c21188c5ffff87e0fc000000003ffff0fc1f8c63f88ff92492449492007c01ff00000000003e04957e1fffffa08417c00007c3fffff0000047ffbbff924925ffffe0fffffff000003fffff7bd87f77c71fff1cffffff07fff8e3ffe39ff180000187fc7fc0000000000000ff8ff80000062108865ff1ff7e0fc000000003fe3fefc1f884314c4024924a00000000000000000000000280411181ffe9280000000000003ffc0000000210df2227ffa41ffd200003e000fff003ff803e04153e1ffffff1c007c00007c3fffffe3800843fff5136936ada1b4007ffe0000000000003e8c113f1fffff800007c00007c3fffff000003189f0227ffc81ffe400003e000fff003ff803c04113c038e38800007c00007c071c7100000ffe3088cd9659565acbff80000000000000003ffcd77f3ffffff9ef3ffe0007c3fffffe39c739cff33bfffffdffffe0003e000fffffbffffe5294a845f81f87e0fc000000003f03f0fc1f8ef7bddeef1ff1fc7f8fffffffffe3fe3f8ff1fffd5bbf5fffffff2fe7fe0007c3ffffffc1f818c422117f07f1fc3f800000000fc0fc3f07e05fbeec5ff81f87ffff83ffff83ff03f0fffff318522117f27e1fcbf000000000fc0fc3f07e308fb13fedb6db92524801f007fc0000000000f85044f87fffff04209f00001f0fffffc00000212a44abcf3c773de38000000038e38ee39c70842110881c01c0700e000000000380380e01c61084463ff1ff71ce3800000003fe3fee39c75afeb3ffffcffdff7fe007c01ffff8ffbfe7fc42108844380380e01c000000000700701c038ffe508955b25b16cad9ff800000000000000035ad03b54000388001c7fff07ffc000710003888525548f5d75fc738e00000000e38e3b8e71fffa622996db245b7927fe0000000000000000f81244f8fffffe41083f00001f0fffffc0000318ffff1092492a4849001fff8000000000000843fff48b4d34ed31a6007ffe00000000000014a908a55f81f87e0fc000000003f03f0fc1f86329f0a67ff801ffc000003e000fff003ff803f0c533e1fffff800007c00007c3fffff00000e81044e801f81e00001f00001f003f03c00000a427c0a9fffc77ff000000f8003fff8effe00210df0337ff921ffc900003e000fff003ff803e04113e1ffffff00e07c00007c3fffffe01c003c000078000016deda0f80000f000003ffffe318c6423c71c771ce38000000038e38ee39c7c01044f836db6e00000000001f000000000003ff94aa11b49b46d2da7fe0000000000000000210bf1227ffa09ffd040003e000fff003ff8004218cc45fa1fa7e8fd000000003f03f0fc1f8ce720dcc80001e0000ffffc1fff00003c0001e8467d189ffe92fff000000f8003ffc00ffe008810444875d75e0000000000000e38e38000008427c089fffc07ffe00000f8003fff80fffc052be80ffda4da5696d2007c01ff0000000000273fffd67ff5ffffcff801fff803fe3feff9ffffe73b9dffe7fdffbffff800000ff8ffbfe7fc1dae641a0000001f0383ffff83c0000003e078c7fff4065965b9632c007ffe00000000000002118cc23d71d775ceb8000000038e38ee39c7423e91ffb2cb2ccb596007c01ff000000000008427408807e0001f000000f80000fc0003e0007adaa0700000038c700ffffe0f000000718e04210c845ff1f87fcfc000000003fe3f0ff9f8ffe3198469a699a6b4dff80000000000000003e05113e5fffff920247c00007c3fffff00000843fff6236da4adb524007ffe00000000000037bd8bf77f81fffe0ffffff07ffff03fffc1ff2949f0227ffc11ffe080003e000fff003ff80108fa8bfed92d93656c801f007fc0000000000a53fff406db24bb6924007ffe0000000000003e44513e1fffffc92007c00007c3fffff0000028425128ffff1dc738e00000000fffe3b8e71e42519945fa5fafe0fc000000003f03f0fc1f808461119f3c73dcf39e00000000e38e3b8e71f9ce7339800e00803007fffffffc01c0100600fff14cc46db6db24a49ff80000000000000000004111e0db6db800000000007c3fffff00000ffefbb87c92491ffffffffffe0f000003fffffe359dfe7fffffffcfffc00007c3fffffff9fff81044c06db6da00001f00000000000000000294a7e089ffe007ff000000f8003ffc00ffe00ffe3198cf9e79de7bcfff800000e38e3b8e71d4afa8bfff93f97e5fc801f007fff03f0fc1f8c63fffffb6db6edb5b6007fffff000000000021084200000000000000000000000000000000200040207ff8000000000000000fff0000000231fffd23d75d7f5ceb801fff8038e38ee39c70000100071c001c700000000000e380038e001004003e049249000000000007c00000000000003e804000000000000007c00000000000000000100044480481202400000000000000000004a7e91fff3cf3dcf79e007c01ffe38e3b8e71d8cffc3ffffe497ff24801ff87ffffc00ffe0007efbb07800001ffffe0ffffe0f000003ffffc0010880090090240480000000000000000000fc3ffff87ffffe92125f07ffff0fffffc00003ffffff11b6db6edadb7fffff8000000000000a53fff627ffa4bffd24007ffe00fff003ff80021000001041044108200000000000000000000800000871c71c0000000000000e38e38000037bd83f76001ff800ffffff07ffc003ff001fff89466f97ffffff83f1f00001f0fffffff07e1ef0002ff6db6d5b7b6ffe0007fffffffffffff7bdeef70e38e238c71ffffffff1c71c4718e3ffa7e299fff247ff927fe0f8003ffc00ffe00f800008049249000001f000000000000000003ff94aa55fc9fc7f2fe7fe000003f03f0fc1f8ffff88ffdb6db56dedbfffc01ff00000000001088002100000000000000000000000000000000000000700701c038000000000e00e03807000008002241041104208000000000000000000fff14cfc7fffff24a49ff8001f0fffffc0000040000041f81f800000000000003f03f00000094bfff517e97ebfa3f4007ffe00fc0fc3f07e000008001f80007e000000000003f0000fc00000088022124800494000000000000000000000007bddeedb6dbb6d6d801ffffffffffffffff000211002082088210400000000000000000004200000120120480900000000000000000000fa3ec4fffffffe49493f07c01fffffffc00003e467d3e9ffffffff007c00f87c3fffffffe00294bf12affff1dfff8e0003e000fffe3bfff1fe14957e3ffffff1ce3fc00007c3fffffe39c7210100004920012480000000000000000000020041110092492800000000000000000000000bdc17f006db6dbb6b6dff83fe00ffffffffffc6318cc67ff1ff7fcff800000003fe3feff9ff318df2337fffe1ffff00003e000ffffc3fffe00027c00092400248000000f80000000000000ffe1088449249124a49ff8000000000000000210fffd0092492a4849001fff8000000000000423e80ff92492449492007c01ff00000000003e04113e1fffff800007c00007c3fffff000002109f0227ff801ffc000003e000fff003ff80021084423c71c771ce38000000038e38ee39c7108422117e07e1f83f000000000fc0fc3f07e3bdef77ba07e0781f03ffffffffc0fc0f03e07

def LS : Nat → Nat
  | 4 => 0x604d953000608db7a000607d97a00060429de
  | 5 => 0x80604072cb0000705640b1e00080607b0df0006043e0b23000706157a3b00080706c73b0008061007d50008060710b00008040636b000080706c53b0008060a07c1000806077ab000060504b35300060207d210000804070cb0000807067a3b000806237a3b0006073e570b00060407b03e00060504ca52000604070bae00070504ac6e000604073e3f0006040807de0006073e0a0b000705041ec800080607c47a000705690b2d0006040233d20006040b842900080607abb00006041507b00007050806dd0604073e0b2c00080607bf7a00070504bc5200080b0757730006040b07d200080407b07300060403b1290006073e0b100006040b07d0000706087aba0008060704dc00043e0b06360006073e0b7a0008060407b00008062507b00008060423b00004073e0b0c0807067a2c3b000705910b2100080706b77a0006040318d000080706b57a0008070611b600080607b0570008070c3b7a0008060453c400060507b37a00080607b0c60006030a07d0000604080bdb0006050429cf0008060a07b00008060407da00060402cc290006040b07d90004073e730b0008057a07d7000604073e0b0006073e0b25
  | 6 => 0x8070604620b00080706050b61000807050b066000080706045f0b000807050c100b0806040b05075e00080504060bd800080402076a7300080504070bd700080407065c0b000605040b075b000705040b1e1d000706081a100b000705020806d6000807050c0b7a00080605075a0b000604030741150008070605580b0007050203692d000605040b2935000806040307d50007060504153f000706030a087700080706043b860006040203298400070604150b3b000706081a0b7a0008060402076a0008060225076a000806021007a20008060507570b000806057a079f00070504027c2e00070504021ea6080706040b2c0f08070603242c0a0008060407560b080604070d2c0b00080604070bd40008070603248e000806040507b0000806040703b00008060402236a0008070605550b000704081a0c0b000706050a150b06040203072c3e00080706042c3f0008070604510b00080706043fb400060504024a330007050408540b0007060504529d0006040b07291a00080706050bc300060504032979000807060a2c0b000706050b210e0008040307417300060504080b5000080604076ab000000807067a3b0007060215100f00080706050bd300080203075773000604020307d2000807060b100f00080605070bd100080504074e0b00080706054d0b000806070d100b00080604070bb00008040d06360b0006020703103e000604030207d000080706044c0b0008060403074100080603250741000605040807cf000807060f0b7a0004020306363e00060504074a0b0008070406490b0008050604480b0008070605043f0008070605253f000806070d0b7a00080706040b3b00080706250b3b000806040207ce0008070605470b0008060403234100060504035b180008060504233f000807040f0c0b000807030a240c00080604230b3b00070604080bcd000804070d0c0b000706040b201a0008060422074100080706050b0a000604020807cc0008060407416a00040203070c3e0008070605957a0007060415240b0007060508460b0008060207576a0008050407450b000806050a230b0006050804440b0007060804430b0008060407410b000806040307cb000604070d3e0b00070604153d0b00070604083c0b00060504080bca00080706020f100007050203219100080706046f2400060503075b0a0007060515100b000806040702b0000705030806c900080602230f1000060408073a0b00080706020f7a000705040806c80006050807390b00070605150b7a000807060b102c0006040307013e000806040233a2000806040b07aa0006040b07083e00080706050bc700060504031f8c080706040b052c00080706038b1100080706050ba7000705040b150c0806040b0507a90006050402295d000706040b08a8000806020710890008070603510a000807062c0b7a00080603075741000605040250380008070604240b000807060b2524000706040b1a15000806030741c6000807040b2c0c00080706028110000806040b2324000806020a076a000706040b083d00080706050bc50008070506a40b000807060b341100080605074f0a00080705046ea3000806040b07c400080706050b10000806040b07a2000806040b07a100080706053fc30007060208107b00080605230b100008060504539f00080706050b7a000806040703c2000806040741b00008070603582400080706033b0a0008060407533b0706050852047a00080605230b7a00080705040b0c000807050b250c000706040b0f1500080705066e7a00080706043f3b0007060315240a000805040b230c0006040b15070d0008050307450a000806040207c1000706040b081a0007060b25081a00080706040bc000080604070bbf08060402072c6a00080705060bbe0008060307410a00060405073e0b000604073e030b00080706053f0a0006040b23081a000807060b3b0a000806030704bd000806040b079e00070504080bbc000706050804bb000008060407b0000807050b2d1600080706049b0b000806050b2809000806040b079a00070604080bba000806040b239a000805040b303600080706040b9900080706040f850008040b070d73000806030a07aa0008060207106a00070504036c370007060408980b000806040318a100040203073e730008040206366a0007050b080696080706040b3bb508060403072c4100080706040b0f000807060b0f2500080706030a2400070504080b94000806040b070d0008060b25070d080706040b3b2c0008060407930b000807040b3112000806040b0f230006040203073e000806040b0792000806030a232400060203073e250007050804910b00080402070c6a000806040b230d000806040b2a0d0008070604900b000706040b2c15000806020704b900070504031e6500070502031e6400060402033e2300080706043f240807060a052c0b000807060a2224000806030a07a100080706053b7a00080706058e0b00080706033b7a00070605080bb800080706040bb700060504088c0b0005040b08078a00060402073e220008060507105900060402073e6a0008060407890b0807040506880b00080706050b87000807060a0b24000806070310410007060508527a00080706053f10000804030636410006040b08078400080706040b7d000807060b3b10080706020f102c0008060b070483000604073e020b000806050b0782000807060b0481000805040b068005040b081e0736000807060504b600070408067f0b0008060407016a00070504031f5400080706053f7a00070605087e0b000807067a0b3b00070605040b15000706050b251500080403070c4100080706040bb500070504067c0b000706040b087b00080705040c3f000605040b2315000807040c0b3b00080706040b2c00080706026b0f000807060b252c00080706040bb400060504070bb3000706040b087700080502074e1000070604081a3f00080706040b75000807050a0c0b0008060b070d5700060403073e41080706040b242c000806040b232c00080704060bb2000604030807b100080706024c1000060203073e5700080706054b1000080604070db000060502074a100007060a081a0b0008040507730b000807050604af00080706023b1000080706020f610008070603247a00070604080b72000705040294380807060b052c10000807020f0c1000080706050a97000604020307ae00080706023b7a000807063b047a000705040b080600080706050b25000807060b24100807060b7a052c000806040702ad0008070602421100070504060bac00080605040b23000806050b232500080706030a9000080602076aab000705040b066c00080706043f0f00080706240b7a0006040215076a00080604070d3f00080706056b0b00080604076a0b0007050604690b070604081a2c0b000807060f0110000807040c240b0008070406680b0005040806670b000807060a0b0f0008060a070d0b0008050406660b0007050806640b0006040807630b00000604073e0b000603073e020a
  | 7 => 0x80706022c03100008070605030b7a0007060502100838000806050403182b00080604030702aa000604020307083e080706040203052c00080706050203a7000705040203150c000705040b08061d08060402030507a90008070605041c0b00070604020308a80008070504030b0c000807060204100f000806050402143300080706040302240008070603250224000706040203151a0008070504061b0b0008070402032c0c000706040b08051a00070604030b081a00080706050222a7000807060405190b00070504020806a600080705030604a50008060403230224000008060402076a000706040203083d00080705020603a4000807060203113400080605030a072b08070604020b052c0008070504060ba30008070604220224000806050407180b0008070605020310000807060504170b00080604020307a200080604030207a1000706050402273800070605040315010008060502230310000807050b06041600070605040b081500080706040b022400080706050402a0000807060502037a000806050407140b0807060402030f4c00080706050222100008060504070b9f000706050408130b0008070604032c01000807040b050612000807050402030c000807050203250c0008070605020b10000807060b050411000706040215030f000807060504100b000805040203230c000604020315070d0008070604050f0b00080706040b030f000706050b08040e00080706030a0524000706040203081a000706020325081a000806040b05070d00080604030b070d0000080604030741000807050402220c00080705040b060c000604020305073e000008070605043f0008070605020b7a000604020323081a0008070605040b7a0000080706040b3b000806040203079e0007060504080b9d000706050408029c000807050203162d000706040222081a000807020306049b0008060502030928000806040203079a0008070504020b0c000807060504017000070605030a081f0000080706050a0b00080706050403010008070605032501000806040203239a0008050402033036000706050408080b000807060402039900070604020b081a0008040203070d7300080605040323010007060403080298000806050704090b00080706050210320000080706020f10000807060504029700070502030806960008070605042201000807060402030f0008070605040b95000807060225030f00070504020803940007060504030b15000806040203070d000806020325070d0008060403070293000807060504010b0008070402031231000806040223030f00080604020307920007050203080491000806040203230d0008060402030d2a00080706030402900007060402032c150008070604030162000807050406038f00080706040b052c00080706042c030b08070603020a052c0008070604020f220008070504021b2e000807060503170a00070605040b0838000806040222070d000807060305028e000706050208048d0008060402070d6a00080705040b0637000605040308028c000807060305048b000504020308078a000805040b070636000806040207038900080706040f020b08070402030506880000080706040b24000807060502038700080706030a02240008070604050b860008070603040a2400080604020b070d000605040b08073500080706040503850006040203080784000807060402037d000806020307048300080605030702820008070602040381000805040306028005040203081e0736000704020308067f0000080706050b10000706050308027e0008070502062e1000070605040203150007060502032515000807060b050434000807060402227d0008070504032f3700080706040b0505000807060504030b000807060525030b000705040206037c000706040203087b00060504020323150000080706050b7a0006050403080779000806050423030b0008070604031924000807060402032c0008070605040378000807060203252c0008060403070d41000706040308027700070605040803760007060504022215000807060403027500080604020f07330000080705040b0c00070605030804740008070605040b220008070503020a0c0008060203070d57080706040302242c000806040203232c00080604030718240007060504020b15000807060503014d000807060402222c00000706040b081a00070603020a081a00080402030507730008070605040b0b0007060402080372000807060504036d080706020310052c00080705020604710008070604020b2c0008070605040270000807060405026f0008070504060b6e000806050203070400080706050203250008070603100224000807060504226d000807060503010a00080605040203230008060502032325000705040306026c000807060502036b0008070605040222000807060502222500080705040b0606000806040205076a000806040207036a000705020306046900080705030a063700080605040b07330706040203081a2c00080704030c02240008060504022223000807040206036800080706050b043200050402030806670000080706040b0f00080706020a030f0000080706030a24000807060504020b00000806040b070d0008070605020b2500080603020a070d00080706050b040400080706050b04250008050402060366000705040308066500070502030806640006040203080763000006040203073e000807040b050631000807060403026200080706020503610008060504020b230008070503060260000807060402035f00080705020c0310080604020305075e000605040208075d000804020307065c000605040307025b0007050402031d1e00070602081a0310000806050207035a00080605040703590008070605030258000807060403012400060504020329350008060403050741000807060504033f00080602030507570008070604050b3b0008070604030b3b0008070604020f260807060402030f2c00080604020703560806040203070d2c000805040b07063000080706050203550007040203081a0c0000070605040b150007060503020a1500080705040b062f00080706050103100008070604030251000705040308025400080706050a030b00080605020714100008060504070b530007060504080b520008070504062e0b0807060403022451000706050403131f000604020307291a000807050b06042d0000080706040b2c0008070603020a2c0007060502030e2100060504020803500008070605040b3f00080605040b072b0008070602050f1000080706020f0310000806050407024f000805040207034e000807050403010c000807060503024d00080602070d031000080605040b070700080402030d0636000807060402034c000807060504034b00080605040b0723000806040b05072a000706040301081a000605040207034a0008070403060249000605040b0807290008050203060448000806050b070428000807060403023b000706050408270b0008070605030247000807060405260b08070604030b052c0008070402030f0c0008040203070d0c0007060402031a20000008070605040b000807060503020a0000080706050b2500070604031502240007060502080346000805040307024500080706040b05240000080605040b230008070604030b240008060503020a2300060502030804440007060203080443000807060205044200080604030702410008070504060240000807060504023f0006040203070d3e000706040203153d000706040203083c0008070605020a220008070604020b3b000706050b0804210007060502150310000706040b08052000080706050b031000070605040b081f00080706050a020b0008070605040a0b000705040b08061e0008070604030f01000604020308073a0008060403070d010006050203080739
  | 8 => 0x80706040203052c00070605040208033800080705040306023700080504020307063600000807060403022400060504020308073500000807060502031000080706020305043400080706040203050500080706050402030300000807050402030c00080706050402032200000706040203081a00080706050402030b00000807060504030100080705040203060600080605040207033300080706050204033200000807060402030f00080706050403020200000806040203070d00080706050203040400080706050203042500080704020305063100080504020307063000000706050402031500080705040306022f00000807060504030b00080705040206032e00080705020306042d00000807060402032c00080605040307022b00080605040203070700080605040203072300080604020305072a00060504020308072900080605020307042800070605040208032700080706040205032600000807060504020300000807060502032500080706040305022400000806050402032300000807060504022200070605020308042100070604020308052000070605040308021f00000807060504020b00080706050304020a00070504020308061e00070504020308061d00080706050402031c00080705040206031b00070604020308051a00080706040305021900080605040307021800080706050304021700080705020306041600070605040203081500080605040207031400070605040308021300080704020305061200080706020305041100080706050204031000080706040205030f00070605020308040e00080604020305070d00080705040203060c00000008070605040b00000807060503020a000706050402030808000806050203070409000807060504030201
  | _ => 0

def poolG : List Nat := [0x1182e09c4d12c78, 0x1182e09c5013878, 0x1182e09c5512c78, 0x1183709c5013c81, 0x1183709c5513c81, 0x1183709c4d13081, 0xf0371187815454, 0xdc2e1187815454, 0xb8271187815454, 0xf0270b85f12c4c, 0xf0270b85f1384f, 0xdc270b85f12c4c, 0x118370f07815055, 0x118270b87815055, 0x118270f07815055, 0xdc27118811344c, 0xf027118811344c, 0xdc27118811404f, 0x1183c0b87817c81, 0xf0270dc4c1504b, 0xf0270dc4f1504e, 0x118270b87812c4d, 0x118270b87813850, 0x118270dc551304d, 0x118270f07815050, 0x118270f08115050, 0x118270f0781504d, 0xb8270dc4c1504e, 0x118270dc5513050, 0x118270dc8113050, 0xb8270dc4f1504b, 0x118270dc5513c4d, 0x118270dc8113c4d]

def dec (c : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 =>
    let v := c &&& (2 ^ IW - 1)
    if v = 0 then [] else fld DD SW (v - 1) :: dec (c >>> IW) n

def S (s j : Nat) : List Nat :=
  if s = 9 then xsG else dec (fld (LS s) (IW * (s + 1)) j) (s + 1)

def idx (s : Nat) (zs : List Nat) : Nat := bsr (HT s) 32 (hk zs) 20 0 (NN s)

def Z (s : Nat) := bar kk S NN idx poolG s

theorem h9y0 : span (Z 9) 1 0 = true := by decide +kernel
theorem z9 : span (Z 9) 1 0 = true := h9y0
theorem h8y0 : span (Z 8) 25 0 = true := by decide +kernel
theorem h8y25 : span (Z 8) 25 25 = true := by decide +kernel
theorem h8y50 : span (Z 8) 23 50 = true := by decide +kernel
theorem z8 : span (Z 8) 73 0 = true := (@span_join (Z 8) 50 0 23 (@span_join (Z 8) 25 0 25 h8y0 h8y25) h8y50)
theorem h7y0 : span (Z 7) 25 0 = true := by decide +kernel
theorem h7y25 : span (Z 7) 25 25 = true := by decide +kernel
theorem h7y50 : span (Z 7) 25 50 = true := by decide +kernel
theorem h7y75 : span (Z 7) 25 75 = true := by decide +kernel
theorem h7y100 : span (Z 7) 25 100 = true := by decide +kernel
theorem h7y125 : span (Z 7) 25 125 = true := by decide +kernel
theorem h7y150 : span (Z 7) 25 150 = true := by decide +kernel
theorem h7y175 : span (Z 7) 25 175 = true := by decide +kernel
theorem h7y200 : span (Z 7) 25 200 = true := by decide +kernel
theorem h7y225 : span (Z 7) 25 225 = true := by decide +kernel
theorem h7y250 : span (Z 7) 25 250 = true := by decide +kernel
theorem h7y275 : span (Z 7) 25 275 = true := by decide +kernel
theorem h7y300 : span (Z 7) 25 300 = true := by decide +kernel
theorem h7y325 : span (Z 7) 25 325 = true := by decide +kernel
theorem h7y350 : span (Z 7) 11 350 = true := by decide +kernel
theorem z7 : span (Z 7) 361 0 = true := (@span_join (Z 7) 350 0 11 (@span_join (Z 7) 325 0 25 (@span_join (Z 7) 300 0 25 (@span_join (Z 7) 275 0 25 (@span_join (Z 7) 250 0 25 (@span_join (Z 7) 225 0 25 (@span_join (Z 7) 200 0 25 (@span_join (Z 7) 175 0 25 (@span_join (Z 7) 150 0 25 (@span_join (Z 7) 125 0 25 (@span_join (Z 7) 100 0 25 (@span_join (Z 7) 75 0 25 (@span_join (Z 7) 50 0 25 (@span_join (Z 7) 25 0 25 h7y0 h7y25) h7y50) h7y75) h7y100) h7y125) h7y150) h7y175) h7y200) h7y225) h7y250) h7y275) h7y300) h7y325) h7y350)
theorem h6y0 : span (Z 6) 25 0 = true := by decide +kernel
theorem h6y25 : span (Z 6) 25 25 = true := by decide +kernel
theorem h6y50 : span (Z 6) 25 50 = true := by decide +kernel
theorem h6y75 : span (Z 6) 25 75 = true := by decide +kernel
theorem h6y100 : span (Z 6) 25 100 = true := by decide +kernel
theorem h6y125 : span (Z 6) 25 125 = true := by decide +kernel
theorem h6y150 : span (Z 6) 25 150 = true := by decide +kernel
theorem h6y175 : span (Z 6) 25 175 = true := by decide +kernel
theorem h6y200 : span (Z 6) 25 200 = true := by decide +kernel
theorem h6y225 : span (Z 6) 25 225 = true := by decide +kernel
theorem h6y250 : span (Z 6) 25 250 = true := by decide +kernel
theorem h6y275 : span (Z 6) 25 275 = true := by decide +kernel
theorem h6y300 : span (Z 6) 25 300 = true := by decide +kernel
theorem h6y325 : span (Z 6) 25 325 = true := by decide +kernel
theorem h6y350 : span (Z 6) 16 350 = true := by decide +kernel
theorem z6 : span (Z 6) 366 0 = true := (@span_join (Z 6) 350 0 16 (@span_join (Z 6) 325 0 25 (@span_join (Z 6) 300 0 25 (@span_join (Z 6) 275 0 25 (@span_join (Z 6) 250 0 25 (@span_join (Z 6) 225 0 25 (@span_join (Z 6) 200 0 25 (@span_join (Z 6) 175 0 25 (@span_join (Z 6) 150 0 25 (@span_join (Z 6) 125 0 25 (@span_join (Z 6) 100 0 25 (@span_join (Z 6) 75 0 25 (@span_join (Z 6) 50 0 25 (@span_join (Z 6) 25 0 25 h6y0 h6y25) h6y50) h6y75) h6y100) h6y125) h6y150) h6y175) h6y200) h6y225) h6y250) h6y275) h6y300) h6y325) h6y350)
theorem h5y0 : span (Z 5) 25 0 = true := by decide +kernel
theorem h5y25 : span (Z 5) 25 25 = true := by decide +kernel
theorem h5y50 : span (Z 5) 22 50 = true := by decide +kernel
theorem z5 : span (Z 5) 72 0 = true := (@span_join (Z 5) 50 0 22 (@span_join (Z 5) 25 0 25 h5y0 h5y25) h5y50)
theorem h4y0 : span (Z 4) 4 0 = true := by decide +kernel
theorem z4 : span (Z 4) 4 0 = true := h4y0
theorem z0 : span (Z 0) 0 0 = true := rfl
theorem z1 : span (Z 1) 0 0 = true := rfl
theorem z2 : span (Z 2) 0 0 = true := rfl
theorem z3 : span (Z 3) 0 0 = true := rfl

theorem checked (s : Nat) (hs : s ≤ 9) : ∀ i < NN s, Z s i = true := by
  interval_cases s
  · exact fun i hi => span_ok z0 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z1 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z2 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z3 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z4 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z5 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z6 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z7 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z8 i (Nat.zero_le i) hi
  · exact fun i hi => span_ok z9 i (Nat.zero_le i) hi

theorem noRunFull (s : Nat) (hs : s ≤ 9) (h : NatRun (mask kk) (goal kk) s xsG) : False := by
  have h9 : NatRun (mask kk) (goal kk) 9 xsG := extend_run h hs
  have p : xsG.Perm (S 9 0) := List.Perm.refl _
  exact bar_all checked 9 (by decide) 0 (by decide) (Run.perm p h9)

theorem rowsG_len : rowsG.length = 150 := by decide +kernel

theorem enc_inputsG :
    (List.ofFn fun (i : Fin 7) => (fun x : Fin 7 → Bool => x i)).map (fun a => encL a rowsG)
      = xsG := by decide +kernel

theorem enc_goalG : encL fG rowsG = goal kk := by decide +kernel

theorem maskG : mask kk = 2 ^ rowsG.length - 1 := by rw [rowsG_len]; rfl

theorem proper_failG : ∀ zs ∈ xsG.sublists, zs ≠ xsG →
    (cov kk zs &&& lo kk) ≠ lo kk := by decide +kernel

theorem no_subG : ∀ s ≤ 9, ∀ zs : List ℕ, zs.Sublist xsG →
    NatRun (mask kk) (goal kk) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsG
  · subst e; exact noRunFull s hs h
  · exact proper_failG zs (List.mem_sublists.2 hz) e (required h)

-- Every list of AND, OR and NOT gates of fan-in at most two computing the function has at
-- least ten gates.
theorem lower (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = fG x) : 10 ≤ gs.length := by
  by_contra hlt
  obtain ⟨ws, hsub, hrun⟩ := exists_run gs o hg fG he ⟨fun _ => false, fun _ => true, by decide⟩
  have hr : NatRun (mask kk) (encL fG rowsG) gs.length (ws.map fun a => encL a rowsG) :=
    Run.map (fun a : BFn 7 => encL a rowsG)
      (fun a => by rw [maskG]; exact encL_inv a rowsG)
      (fun a b => encL_and a b rowsG) (fun a b => encL_or a b rowsG) hrun
  rw [enc_goalG] at hr
  refine no_subG gs.length (by omega) _ ?_ hr
  rw [← enc_inputsG]
  exact hsub.map _
end PEqualNP.Outside.L_meta_11924

open PEqualNP.Outside.L_meta_11924 in
theorem PEqualNP.Outside.L_meta_11924 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hg _ he
  have he' : ∀ x : Fin 7 → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = fG x :=
    fun x => (he x).trans (rhs_eq x)
  have hlen := lower gates o hg he'
  refine ⟨upGates, 16, upMono, by rw [upLen]; exact hlen, fun x => ?_⟩
  exact (upper_eval x).trans (rhs_eq x).symm