import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_618

def FULL : ℕ := 2 ^ 54 - 1
def ALLV : ℕ := 2 ^ 108 - 1

def sepv (v : ℕ) : ℕ := (v &&& FULL) &&& ((v >>> 54) ^^^ FULL)

def covN (L : List ℕ) : ℕ := L.foldr (fun v acc => sepv v ||| acc) 0

def passes (s : ℕ) (L : List ℕ) : Bool := decide (L.length ≤ s + 1) && (covN L == FULL)

def opv (o : Bool) (a b : ℕ) : ℕ := if o then a &&& b else a ||| b

def kept (k : Bool) (x : ℕ) (xs : List ℕ) : List ℕ := if k then x :: xs else xs

def splits : List ℕ → List (ℕ × List ℕ)
  | [] => []
  | x :: xs => (x, xs) :: (splits xs).map (fun q => (q.1, x :: q.2))

def twoCh (a b : ℕ) (r : List ℕ) : List (List ℕ) :=
  [true, false].flatMap fun o => [true, false].flatMap fun ka => [true, false].map fun kb =>
    opv o a b :: kept ka a (kept kb b r)

def children (L : List ℕ) : List (List ℕ) :=
  ((splits L).flatMap fun q => (splits q.2).flatMap fun q' => twoCh q.1 q'.1 q'.2) ++
  ((splits L).flatMap fun q => [q.1 :: q.1 :: q.2, 0 :: q.2, 0 :: q.1 :: q.2]) ++
  [0 :: L, ALLV :: L]

def eqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && eqL xs ys
  | _, _ => false

def memL (L : List ℕ) (Ls : List (List ℕ)) : Bool := Ls.any fun M => eqL L M

def chk (Lv : ℕ → List (List ℕ)) : ℕ → List ℕ → Bool
  | 0, L => !(eqL L [FULL])
  | s + 1, L => !(eqL L [FULL]) && (children L).all fun ch =>
      !(passes s ch) || memL (List.insertionSort (· ≤ ·) ch) (Lv s)

def Run (s : ℕ) (L : List ℕ) : Prop :=
  ∀ P : ℕ → List ℕ → Prop,
    (∀ s, P s [FULL]) →
    (∀ s L₁ L₂, L₁.Perm L₂ → P s L₁ → P s L₂) →
    (∀ s a b r o ka kb, P s (opv o a b :: kept ka a (kept kb b r)) → P (s + 1) (a :: b :: r)) →
    (∀ s a r, P s (a :: a :: r) → P (s + 1) (a :: r)) →
    (∀ s a r ka, P s (0 :: kept ka a r) → P (s + 1) (a :: r)) →
    (∀ s r w, (w = 0 ∨ w = ALLV) → P s (w :: r) → P (s + 1) r) →
    P s L

theorem Run.done (s : ℕ) : Run s [FULL] := fun _ h0 _ _ _ _ _ => h0 s

theorem Run.perm {s : ℕ} {L₁ L₂ : List ℕ} (p : L₁.Perm L₂) (h : Run s L₁) : Run s L₂ :=
  fun P h0 h1 h2 h3 h4 h5 => h1 s L₁ L₂ p (h P h0 h1 h2 h3 h4 h5)

theorem Run.two {s a b : ℕ} {r : List ℕ} {o ka kb : Bool}
    (h : Run s (opv o a b :: kept ka a (kept kb b r))) : Run (s + 1) (a :: b :: r) :=
  fun P h0 h1 h2 h3 h4 h5 => h2 s a b r o ka kb (h P h0 h1 h2 h3 h4 h5)

theorem Run.copy {s a : ℕ} {r : List ℕ} (h : Run s (a :: a :: r)) : Run (s + 1) (a :: r) :=
  fun P h0 h1 h2 h3 h4 h5 => h3 s a r (h P h0 h1 h2 h3 h4 h5)

theorem Run.zap {s a : ℕ} {r : List ℕ} {ka : Bool} (h : Run s (0 :: kept ka a r)) :
    Run (s + 1) (a :: r) :=
  fun P h0 h1 h2 h3 h4 h5 => h4 s a r ka (h P h0 h1 h2 h3 h4 h5)

theorem Run.const {s w : ℕ} {r : List ℕ} (hw : w = 0 ∨ w = ALLV) (h : Run s (w :: r)) :
    Run (s + 1) r :=
  fun P h0 h1 h2 h3 h4 h5 => h5 s r w hw (h P h0 h1 h2 h3 h4 h5)

theorem Run.mono {s : ℕ} {L : List ℕ} (h : Run s L) : Run (s + 1) L :=
  h (fun s L => Run (s + 1) L) (fun s => Run.done _) (fun _ _ _ p h => Run.perm p h)
    (fun _ _ _ _ _ _ _ h => Run.two h) (fun _ _ _ h => Run.copy h) (fun _ _ _ _ h => Run.zap h)
    (fun _ _ _ hw h => Run.const hw h)

theorem Run.mono_le {s s' : ℕ} {L : List ℕ} (hs : s ≤ s') (h : Run s L) : Run s' L := by
  induction hs with
  | refl => exact h
  | step _ ih => exact ih.mono

def Cov (L : List ℕ) : Prop := ∀ i < 54, ∃ v ∈ L, (sepv v).testBit i = true

theorem sepv_bit (v i : ℕ) :
    (sepv v).testBit i = (decide (i < 54) && v.testBit i && !v.testBit (i + 54)) := by
  have h1 : (sepv v).testBit i = ((v.testBit i && decide (i < 54)) && (v.testBit (54 + i) ^^ decide (i < 54))) := by
    simp only [sepv, FULL, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight,
      Nat.testBit_two_pow_sub_one]
  rw [h1, Nat.add_comm 54 i]
  cases v.testBit i <;> cases v.testBit (i + 54) <;> cases decide (i < 54) <;> rfl

theorem sepv_opv (o : Bool) (a b i : ℕ) (h : (sepv (opv o a b)).testBit i = true) :
    (sepv a).testBit i = true ∨ (sepv b).testBit i = true := by
  rw [sepv_bit] at h
  rw [sepv_bit, sepv_bit]
  have e1 : (opv o a b).testBit i = (if o then (a.testBit i && b.testBit i) else (a.testBit i || b.testBit i)) := by
    cases o <;> simp [opv, Nat.testBit_and, Nat.testBit_or]
  have e2 : (opv o a b).testBit (i + 54) = (if o then (a.testBit (i + 54) && b.testBit (i + 54)) else (a.testBit (i + 54) || b.testBit (i + 54))) := by
    cases o <;> simp [opv, Nat.testBit_and, Nat.testBit_or]
  rw [e1, e2] at h
  revert h
  cases o <;> cases decide (i < 54) <;> cases a.testBit i <;> cases b.testBit i <;>
    cases a.testBit (i + 54) <;> cases b.testBit (i + 54) <;> decide

theorem sepv_zero : sepv 0 = 0 := by decide +kernel
theorem sepv_all : sepv ALLV = 0 := by decide +kernel
theorem sepv_full : sepv FULL = FULL := by decide +kernel

theorem mem_kept {k : Bool} {x v : ℕ} {xs : List ℕ} (h : v ∈ kept k x xs) : v = x ∨ v ∈ xs := by
  cases k <;> simp [kept] at h <;> tauto

theorem length_kept (k : Bool) (x : ℕ) (xs : List ℕ) : xs.length ≤ (kept k x xs).length ∧
    (kept k x xs).length ≤ xs.length + 1 := by
  cases k <;> simp [kept]

theorem kept_perm {k : Bool} {x : ℕ} {l₁ l₂ : List ℕ} (p : l₁.Perm l₂) :
    (kept k x l₁).Perm (kept k x l₂) := by
  cases k <;> simp [kept, p]

theorem map_kept (f : ℕ → ℕ) (k : Bool) (x : ℕ) (xs : List ℕ) :
    (kept k x xs).map f = kept k (f x) (xs.map f) := by
  cases k <;> simp [kept]

theorem Run.inv {s : ℕ} {L : List ℕ} (h : Run s L) : L.length ≤ s + 1 ∧ Cov L := by
  apply h (fun s L => L.length ≤ s + 1 ∧ Cov L)
  · intro s
    refine ⟨by simp, fun i hi => ⟨FULL, by simp, ?_⟩⟩
    rw [sepv_full, FULL, Nat.testBit_two_pow_sub_one]
    simp [hi]
  · intro s L₁ L₂ p h
    refine ⟨p.length_eq ▸ h.1, fun i hi => ?_⟩
    obtain ⟨v, hv, hb⟩ := h.2 i hi
    exact ⟨v, p.mem_iff.1 hv, hb⟩
  · intro s a b r o ka kb h
    refine ⟨?_, fun i hi => ?_⟩
    · have h1 := length_kept kb b r
      have h2 := length_kept ka a (kept kb b r)
      have h3 := h.1
      simp only [List.length_cons] at h3 ⊢
      omega
    · obtain ⟨v, hv, hb⟩ := h.2 i hi
      rcases List.mem_cons.1 hv with rfl | hv
      · rcases sepv_opv o a b i hb with h' | h'
        · exact ⟨a, by simp, h'⟩
        · exact ⟨b, by simp, h'⟩
      · rcases mem_kept hv with rfl | hv
        · exact ⟨_, by simp, hb⟩
        · rcases mem_kept hv with rfl | hv
          · exact ⟨_, by simp, hb⟩
          · exact ⟨v, by simp [hv], hb⟩
  · intro s a r h
    refine ⟨?_, fun i hi => ?_⟩
    · have h3 := h.1
      simp only [List.length_cons] at h3 ⊢
      omega
    · obtain ⟨v, hv, hb⟩ := h.2 i hi
      exact ⟨v, by simp at hv ⊢; tauto, hb⟩
  · intro s a r ka h
    refine ⟨?_, fun i hi => ?_⟩
    · have h1 := length_kept ka a r
      have h3 := h.1
      simp only [List.length_cons] at h3 ⊢
      omega
    · obtain ⟨v, hv, hb⟩ := h.2 i hi
      rcases List.mem_cons.1 hv with rfl | hv
      · rw [sepv_zero] at hb
        simp at hb
      · rcases mem_kept hv with rfl | hv
        · exact ⟨_, by simp, hb⟩
        · exact ⟨v, by simp [hv], hb⟩
  · intro s r w hw h
    refine ⟨?_, fun i hi => ?_⟩
    · have h3 := h.1
      simp only [List.length_cons] at h3 ⊢
      omega
    · obtain ⟨v, hv, hb⟩ := h.2 i hi
      rcases List.mem_cons.1 hv with rfl | hv
      · rcases hw with rfl | rfl
        · rw [sepv_zero] at hb
          simp at hb
        · rw [sepv_all] at hb
          simp at hb
      · exact ⟨v, hv, hb⟩

theorem covN_bit (L : List ℕ) (i : ℕ) :
    (covN L).testBit i = L.any (fun v => (sepv v).testBit i) := by
  induction L with
  | nil => simp [covN]
  | cons v L ih =>
    simp only [covN, List.foldr_cons, Nat.testBit_or, List.any_cons] at ih ⊢
    rw [ih]

theorem cov_full {L : List ℕ} (h : Cov L) : covN L = FULL := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [covN_bit]
  simp only [FULL, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 54
  · obtain ⟨v, hv, hb⟩ := h i hi
    simp only [hi, decide_true, List.any_eq_true]
    exact ⟨v, hv, hb⟩
  · simp [hi, sepv_bit]

theorem Run.passOk {s : ℕ} {L : List ℕ} (h : Run s L) : passes s L = true := by
  have := h.inv
  simp [passes, this.1, cov_full this.2]

theorem splits_perm : ∀ {L : List ℕ} {a : ℕ} {r : List ℕ}, (a, r) ∈ splits L → L.Perm (a :: r)
  | [], _, _, h => by simp [splits] at h
  | x :: xs, a, r, h => by
    simp only [splits, List.mem_cons, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨⟨b, r'⟩, hq, rfl, rfl⟩
    · exact List.Perm.refl _
    · exact ((splits_perm hq).cons x).trans (List.Perm.swap _ _ _)

theorem splits_mem : ∀ {L : List ℕ} {a : ℕ}, a ∈ L → ∃ r, (a, r) ∈ splits L
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨xs, by simp [splits]⟩
    · obtain ⟨r, hr⟩ := splits_mem h
      exact ⟨x :: r, by simp only [splits, List.mem_cons, List.mem_map]; exact Or.inr ⟨_, hr, rfl⟩⟩

theorem splits_head (x : ℕ) (xs : List ℕ) : (x, xs) ∈ splits (x :: xs) := by simp [splits]

theorem mem_twoCh {a b : ℕ} {r ch : List ℕ} (h : ch ∈ twoCh a b r) :
    ∃ o ka kb, ch = opv o a b :: kept ka a (kept kb b r) := by
  simp only [twoCh, List.mem_flatMap, List.mem_map] at h
  obtain ⟨o, -, ka, -, kb, -, h⟩ := h
  exact ⟨o, ka, kb, h.symm⟩

theorem mem_two {L r1 r2 : List ℕ} {a b : ℕ} (o ka kb : Bool) (h1 : (a, r1) ∈ splits L)
    (h2 : (b, r2) ∈ splits r1) : opv o a b :: kept ka a (kept kb b r2) ∈ children L := by
  simp only [children, List.mem_append, List.mem_flatMap]
  refine Or.inl (Or.inl ⟨(a, r1), h1, (b, r2), h2, ?_⟩)
  cases o <;> cases ka <;> cases kb <;> simp [twoCh]

theorem mem_one {L r : List ℕ} {a : ℕ} (h1 : (a, r) ∈ splits L) :
    a :: a :: r ∈ children L ∧ 0 :: r ∈ children L ∧ 0 :: a :: r ∈ children L := by
  simp only [children, List.mem_append, List.mem_flatMap]
  refine ⟨Or.inl (Or.inr ⟨(a, r), h1, by simp⟩), Or.inl (Or.inr ⟨(a, r), h1, by simp⟩),
    Or.inl (Or.inr ⟨(a, r), h1, by simp⟩)⟩

theorem mem_zero (L : List ℕ) : 0 :: L ∈ children L ∧ ALLV :: L ∈ children L := by
  simp [children]

theorem children_perm {L₁ L₂ ch : List ℕ} (p : L₁.Perm L₂) (h : ch ∈ children L₁) :
    ∃ ch' ∈ children L₂, ch.Perm ch' := by
  simp only [children, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with (⟨⟨a, r1⟩, h1, ⟨b, r2⟩, h2, h3⟩ | ⟨⟨a, r⟩, h1, h3⟩) | h3 | h3
  · obtain ⟨o, ka, kb, rfl⟩ := mem_twoCh h3
    have pa := splits_perm h1
    obtain ⟨r1', h1'⟩ := splits_mem (p.mem_iff.1 (pa.mem_iff.2 (List.mem_cons_self ..)))
    have q1 : r1.Perm r1' := ((pa.symm.trans p).trans (splits_perm h1')).cons_inv
    have pb := splits_perm h2
    obtain ⟨r2', h2'⟩ := splits_mem (q1.mem_iff.1 (pb.mem_iff.2 (List.mem_cons_self ..)))
    have q2 : r2.Perm r2' := ((pb.symm.trans q1).trans (splits_perm h2')).cons_inv
    exact ⟨_, mem_two o ka kb h1' h2', (kept_perm (kept_perm q2)).cons _⟩
  · have pa := splits_perm h1
    obtain ⟨r', h1'⟩ := splits_mem (p.mem_iff.1 (pa.mem_iff.2 (List.mem_cons_self ..)))
    have q1 : r.Perm r' := ((pa.symm.trans p).trans (splits_perm h1')).cons_inv
    have hm := mem_one h1'
    simp only at h3
    rcases h3 with rfl | rfl | rfl
    · exact ⟨_, hm.1, (q1.cons _).cons _⟩
    · exact ⟨_, hm.2.1, q1.cons _⟩
    · exact ⟨_, hm.2.2, (q1.cons _).cons _⟩
  · subst h3
    exact ⟨_, (mem_zero L₂).1, p.cons _⟩
  · subst h3
    exact ⟨_, (mem_zero L₂).2, p.cons _⟩

theorem Run.inv2 {s : ℕ} {L : List ℕ} (h : Run s L) :
    L = [FULL] ∨ ∃ s', s = s' + 1 ∧ ∃ ch ∈ children L, Run s' ch := by
  refine (h (fun s L => Run s L ∧ (L = [FULL] ∨ ∃ s', s = s' + 1 ∧ ∃ ch ∈ children L, Run s' ch))
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact fun s => ⟨Run.done s, Or.inl rfl⟩
  · intro s L₁ L₂ p ⟨hr, hq⟩
    refine ⟨Run.perm p hr, ?_⟩
    rcases hq with rfl | ⟨s', hs, ch, hch, hr'⟩
    · exact Or.inl (List.perm_singleton.1 p.symm)
    · obtain ⟨ch', hch', pc⟩ := children_perm p hch
      exact Or.inr ⟨s', hs, ch', hch', Run.perm pc hr'⟩
  · intro s a b r o ka kb ⟨hr, _⟩
    exact ⟨Run.two hr, Or.inr ⟨s, rfl, _, mem_two o ka kb (splits_head _ _) (splits_head _ _), hr⟩⟩
  · intro s a r ⟨hr, _⟩
    exact ⟨Run.copy hr, Or.inr ⟨s, rfl, _, (mem_one (splits_head _ _)).1, hr⟩⟩
  · intro s a r ka ⟨hr, _⟩
    refine ⟨Run.zap hr, Or.inr ⟨s, rfl, _, ?_, hr⟩⟩
    cases ka
    · exact (mem_one (splits_head _ _)).2.1
    · exact (mem_one (splits_head _ _)).2.2
  · intro s r w hw ⟨hr, _⟩
    refine ⟨Run.const hw hr, Or.inr ⟨s, rfl, _, ?_, hr⟩⟩
    rcases hw with rfl | rfl
    · exact (mem_zero r).1
    · exact (mem_zero r).2

theorem eqL_sound : ∀ {a b : List ℕ}, eqL a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eqL_sound h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

theorem eqL_self : ∀ (a : List ℕ), eqL a a = true
  | [] => rfl
  | x :: xs => by simp [eqL, eqL_self xs]

theorem memL_sound {L : List ℕ} {Ls : List (List ℕ)} (h : memL L Ls = true) : L ∈ Ls := by
  simp only [memL, List.any_eq_true] at h
  obtain ⟨M, hM, he⟩ := h
  rw [eqL_sound he]
  exact hM

theorem cert (Lv : ℕ → List (List ℕ)) (hc : ∀ s, ∀ L ∈ Lv s, chk Lv s L = true) :
    ∀ s, ∀ L ∈ Lv s, ¬ Run s L := by
  intro s
  induction s with
  | zero =>
    intro L hL hr
    rcases hr.inv2 with h | ⟨s', hs, _⟩
    · subst h
      have := hc 0 _ hL
      simp [chk, eqL_self] at this
    · omega
  | succ s ih =>
    intro L hL hr
    have hk := hc (s + 1) L hL
    simp only [chk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true] at hk
    rcases hr.inv2 with h | ⟨s', hs, ch, hch, hr'⟩
    · subst h
      rw [eqL_self] at hk
      simp at hk
    · cases hs
      rcases hk.2 ch hch with h1 | h1
      · rw [hr'.passOk] at h1
        simp at h1
      · exact ih _ (memL_sound h1) (Run.perm (List.perm_insertionSort _ _).symm hr')

open PEqualNP.CircuitLowerBounds

def EL : List (ℕ × ℕ) := [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)]
def ML : List (ℕ × ℕ) := [(0, 4), (0, 5), (1, 3), (1, 5), (2, 3), (2, 4)]

def ptOf (q : ℕ × ℕ) : Fin 6 → Bool := fun i => decide (i.val = q.1 ∨ i.val = q.2)

def pts : List (Fin 6 → Bool) :=
  (List.range 108).map fun i =>
    ptOf (if i < 54 then EL.getD (i / 6) (0, 0) else ML.getD ((i - 54) % 6) (0, 0))

def encL (g : (Fin 6 → Bool) → Bool) : List (Fin 6 → Bool) → ℕ
  | [] => 0
  | p :: ps => (g p).toNat + 2 * encL g ps

theorem encL_bit (g : (Fin 6 → Bool) → Bool) :
    ∀ (l : List (Fin 6 → Bool)) (j : ℕ), (encL g l).testBit j = ((l[j]?).map g).getD false
  | [], j => by simp [encL]
  | p :: ps, 0 => by
    cases h : g p <;> simp [encL, h, Nat.testBit_zero]
  | p :: ps, j + 1 => by
    have e : ((g p).toNat + 2 * encL g ps) / 2 = encL g ps := by
      cases g p <;> simp <;> omega
    simp only [encL, Nat.testBit_succ, e, encL_bit g ps j, List.getElem?_cons_succ]

theorem encL_and (g h : (Fin 6 → Bool) → Bool) (l : List (Fin 6 → Bool)) :
    encL (fun x => g x && h x) l = encL g l &&& encL h l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_bit, encL_bit, encL_bit]
  cases l[j]? <;> simp

theorem encL_or (g h : (Fin 6 → Bool) → Bool) (l : List (Fin 6 → Bool)) :
    encL (fun x => g x || h x) l = encL g l ||| encL h l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_bit, encL_bit, encL_bit]
  cases l[j]? <;> simp

theorem encL_false (l : List (Fin 6 → Bool)) : encL (fun _ => false) l = 0 := by
  induction l with
  | nil => rfl
  | cons p ps ih => simp [encL, ih]

theorem encL_true : encL (fun _ => true) pts = ALLV := by decide +kernel

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem foldl_len : ∀ (gs : List Gate) (x : List Bool),
    (gs.foldl stepF x).length = x.length + gs.length
  | [], x => by simp
  | g :: gs, x => by
    rw [List.foldl_cons, foldl_len gs]
    simp [stepF]
    omega

theorem foldl_pre : ∀ (gs : List Gate) (x : List Bool) (i : ℕ), i < x.length →
    (gs.foldl stepF x).getD i false = x.getD i false
  | [], x, i, _ => by simp
  | g :: gs, x, i, hi => by
    rw [List.foldl_cons, foldl_pre gs _ i (by simp [stepF]; omega)]
    simp only [stepF]
    rw [List.getD_append _ _ _ _ hi]

theorem foldl_gate : ∀ (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate), gs[j]? = some g →
    (gs.foldl stepF x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < x.length + j then (gs.foldl stepF x).getD i false
        else false)
  | [], x, j, g, h => by simp at h
  | g0 :: gs, x, 0, g, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [List.foldl_cons, foldl_pre gs _ _ (by simp [stepF])]
    simp only [stepF, Nat.add_zero]
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp only [Nat.sub_self, List.getD_cons_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    by_cases hi : i < x.length
    · rw [if_pos hi, foldl_pre gs _ _ (by simp; omega), List.getD_append _ _ _ _ hi]
    · rw [if_neg hi]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega)]
      rfl
  | g0 :: gs, x, j + 1, g, h => by
    simp only [List.getElem?_cons_succ] at h
    have := foldl_gate gs (stepF x g0) j g h
    have hl : (stepF x g0).length = x.length + 1 := by simp [stepF]
    rw [hl, show x.length + 1 + j = x.length + (j + 1) by omega] at this
    rw [List.foldl_cons]
    exact this

def W (C : Circuit) (i : ℕ) (x : Fin 6 → Bool) : Bool := (C.wires (List.ofFn x)).getD i false

def val (C : Circuit) (i : ℕ) : ℕ := encL (W C i) pts

theorem W_input (C : Circuit) (i : ℕ) (hi : i < 6) (x : Fin 6 → Bool) : W C i x = x ⟨i, hi⟩ := by
  rw [W, wires_eq, foldl_pre _ _ _ (by simp [hi])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  interval_cases i <;> rfl

theorem W_gate (C : Circuit) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (x : Fin 6 → Bool) :
    W C (6 + j) x = g.op.eval (g.inputs.map fun i => if i < 6 + j then W C i x else false) := by
  have := foldl_gate C.gates (List.ofFn x) j g hg
  simp only [List.length_ofFn] at this
  simp only [W, wires_eq]
  exact this

def rdv (C : Circuit) (j i : ℕ) : ℕ := if i < 6 + j then val C i else 0

theorem enc_rd (C : Circuit) (j i : ℕ) :
    encL (fun x => if i < 6 + j then W C i x else false) pts = rdv C j i := by
  unfold rdv
  by_cases h : i < 6 + j
  · simp only [h, if_true]
    rfl
  · simp only [h, if_false]
    exact encL_false _

theorem val_gate (C : Circuit) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (g.inputs = [] → val C (6 + j) = 0 ∨ val C (6 + j) = ALLV) ∧
    (∀ i, g.inputs = [i] → val C (6 + j) = rdv C j i) ∧
    (∀ i1 i2, g.inputs = [i1, i2] →
      ∃ o, val C (6 + j) = opv o (rdv C j i1) (rdv C j i2)) := by
  have e : W C (6 + j) = fun x =>
      g.op.eval (g.inputs.map fun i => if i < 6 + j then W C i x else false) :=
    funext fun x => W_gate C j g hg x
  refine ⟨fun hin => ?_, fun i hin => ?_, fun i1 i2 hin => ?_⟩
  · simp only [val, e, hin, List.map_nil]
    rcases hop with h | h <;> rw [h]
    · right
      exact encL_true
    · left
      exact encL_false _
  · simp only [val, e, hin, List.map_cons, List.map_nil]
    rcases hop with h | h <;> rw [h] <;>
      simp only [GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
        Bool.and_true, Bool.or_false, id] <;> exact enc_rd C j i
  · simp only [val, e, hin, List.map_cons, List.map_nil]
    rcases hop with h | h <;> rw [h] <;>
      simp only [GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil,
        Bool.and_true, Bool.or_false, id]
    · exact ⟨true, by rw [encL_and, enc_rd, enc_rd]; rfl⟩
    · exact ⟨false, by rw [encL_or, enc_rd, enc_rd]; rfl⟩

def Useful (C : Circuit) (w : ℕ) : Prop :=
  ∀ U : ℕ → Prop, U C.output →
    (∀ j g i, U (6 + j) → C.gates[j]? = some g → i ∈ g.inputs → i < 6 + j → U i) → U w

theorem useful_out (C : Circuit) : Useful C C.output := fun _ h0 _ => h0

theorem useful_step {C : Circuit} {j : ℕ} {g : Gate} {i : ℕ} (hu : Useful C (6 + j))
    (hg : C.gates[j]? = some g) (hi : i ∈ g.inputs) (hlt : i < 6 + j) : Useful C i :=
  fun U h0 h1 => h1 j g i (hu U h0 h1) hg hi hlt

theorem useful_inv {C : Circuit} {w : ℕ} (hu : Useful C w) : w = C.output ∨
    ∃ j g, Useful C (6 + j) ∧ C.gates[j]? = some g ∧ w ∈ g.inputs ∧ w < 6 + j :=
  (hu (fun w => Useful C w ∧ (w = C.output ∨
      ∃ j g, Useful C (6 + j) ∧ C.gates[j]? = some g ∧ w ∈ g.inputs ∧ w < 6 + j))
    ⟨useful_out C, Or.inl rfl⟩
    (fun j g i hU hg hi hlt => ⟨useful_step hU.1 hg hi hlt, Or.inr ⟨j, g, hU.1, hg, hi, hlt⟩⟩)).2

def LiveP (C : Circuit) (t w : ℕ) : Prop :=
  w = C.output ∨ ∃ j g, t ≤ j ∧ Useful C (6 + j) ∧ C.gates[j]? = some g ∧ w ∈ g.inputs

open Classical in
noncomputable def Live (C : Circuit) (t : ℕ) : List ℕ :=
  (List.range (6 + t)).filter fun w => decide (LiveP C t w)

open Classical in
noncomputable def Aset (C : Circuit) (t : ℕ) : List ℕ :=
  (List.range (6 + t)).filter fun w => decide (LiveP C (t + 1) w)

theorem mem_Live {C : Circuit} {t w : ℕ} : w ∈ Live C t ↔ w < 6 + t ∧ LiveP C t w := by
  simp [Live]

theorem mem_A {C : Circuit} {t w : ℕ} : w ∈ Aset C t ↔ w < 6 + t ∧ LiveP C (t + 1) w := by
  simp [Aset]

theorem nodup_Live (C : Circuit) (t : ℕ) : (Live C t).Nodup := List.Nodup.filter _ List.nodup_range

theorem nodup_A (C : Circuit) (t : ℕ) : (Aset C t).Nodup := List.Nodup.filter _ List.nodup_range

noncomputable def St (C : Circuit) (t : ℕ) : List ℕ := (Live C t).map (val C)

theorem mem_kept_iff {k : Bool} {x v : ℕ} {xs : List ℕ} : v ∈ kept k x xs ↔ (k = true ∧ v = x) ∨ v ∈ xs := by
  cases k <;> simp [kept]

theorem F1 {C : Circuit} {t : ℕ} (hu : Useful C (6 + t)) :
    (Live C (t + 1)).Perm ((6 + t) :: Aset C t) := by
  have hn : ((6 + t) :: Aset C t).Nodup :=
    List.nodup_cons.2 ⟨fun h => by have := (mem_A.1 h).1; omega, nodup_A C t⟩
  rw [List.perm_ext_iff_of_nodup (nodup_Live C (t + 1)) hn]
  intro w
  rw [mem_Live, List.mem_cons, mem_A]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hw : w = 6 + t
    · exact Or.inl hw
    · exact Or.inr ⟨by omega, h2⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · refine ⟨by omega, ?_⟩
      rcases useful_inv hu with h | ⟨j, g, hj, hg, hi, hlt⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, g, by omega, hj, hg, hi⟩
    · exact ⟨by omega, h2⟩

theorem F2 {C : Circuit} {t : ℕ} {g : Gate} (hg : C.gates[t]? = some g) (hu : Useful C (6 + t))
    {w : ℕ} : w ∈ Live C t ↔ w < 6 + t ∧ (LiveP C (t + 1) w ∨ w ∈ g.inputs) := by
  rw [mem_Live]
  apply and_congr_right
  intro _
  constructor
  · rintro (h | ⟨j, g', hj, hu', hg', hi⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · rw [hg] at hg'
        cases hg'
        exact Or.inr hi
      · exact Or.inl (Or.inr ⟨j, g', hj, hu', hg', hi⟩)
  · rintro ((h | ⟨j, g', hj, hu', hg', hi⟩) | hi)
    · exact Or.inl h
    · exact Or.inr ⟨j, g', by omega, hu', hg', hi⟩
    · exact Or.inr ⟨t, g, le_refl _, hu, hg, hi⟩

theorem step_two {C : Circuit} {t d : ℕ} {g : Gate} (hg : C.gates[t]? = some g)
    (hu : Useful C (6 + t)) (hd : Run d (St C (t + 1))) {a b : ℕ} (hab : a ≠ b) (ha : a < 6 + t)
    (hb : b < 6 + t) (hai : a ∈ g.inputs) (hbi : b ∈ g.inputs)
    (hall : ∀ w ∈ g.inputs, w < 6 + t → w = a ∨ w = b) {o : Bool}
    (hv : val C (6 + t) = opv o (val C a) (val C b)) : Run (d + 1) (St C t) := by
  let A := Aset C t
  let R := A.filter (fun w => decide (w ≠ a ∧ w ≠ b))
  have hR : ∀ w, w ∈ R ↔ w ∈ A ∧ w ≠ a ∧ w ≠ b := by simp [R]
  have nR : R.Nodup := List.Nodup.filter _ (nodup_A C t)
  have p1 : (Live C t).Perm (a :: b :: R) := by
    have hn : (a :: b :: R).Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, nR⟩⟩
      · rw [List.mem_cons, hR]
        rintro (h | ⟨_, h, _⟩)
        · exact hab h
        · exact h rfl
      · rw [hR]
        rintro ⟨_, _, h⟩
        exact h rfl
    rw [List.perm_ext_iff_of_nodup (nodup_Live C t) hn]
    intro w
    rw [F2 hg hu, List.mem_cons, List.mem_cons, hR, mem_A]
    constructor
    · rintro ⟨hw, h | h⟩
      · by_cases hwa : w = a
        · exact Or.inl hwa
        · by_cases hwb : w = b
          · exact Or.inr (Or.inl hwb)
          · exact Or.inr (Or.inr ⟨⟨hw, h⟩, hwa, hwb⟩)
      · rcases hall w h hw with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
    · rintro (rfl | rfl | ⟨⟨hw, h⟩, _, _⟩)
      · exact ⟨ha, Or.inr hai⟩
      · exact ⟨hb, Or.inr hbi⟩
      · exact ⟨hw, Or.inl h⟩
  have p2 : A.Perm (kept (decide (a ∈ A)) a (kept (decide (b ∈ A)) b R)) := by
    have hn : (kept (decide (a ∈ A)) a (kept (decide (b ∈ A)) b R)).Nodup := by
      have h1 : (kept (decide (b ∈ A)) b R).Nodup := by
        cases decide (b ∈ A)
        · exact nR
        · refine List.nodup_cons.2 ⟨?_, nR⟩
          rw [hR]
          rintro ⟨_, _, h⟩
          exact h rfl
      cases decide (a ∈ A)
      · exact h1
      · refine List.nodup_cons.2 ⟨?_, h1⟩
        rw [mem_kept_iff, hR]
        rintro (⟨_, h⟩ | ⟨_, h, _⟩)
        · exact hab h
        · exact h rfl
    rw [List.perm_ext_iff_of_nodup (nodup_A C t) hn]
    intro w
    rw [mem_kept_iff, mem_kept_iff, hR, decide_eq_true_iff, decide_eq_true_iff]
    constructor
    · intro h
      by_cases hwa : w = a
      · subst hwa
        exact Or.inl ⟨h, rfl⟩
      · by_cases hwb : w = b
        · subst hwb
          exact Or.inr (Or.inl ⟨h, rfl⟩)
        · exact Or.inr (Or.inr ⟨h, hwa, hwb⟩)
    · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, _⟩) <;> exact h
  have q1 : (St C t).Perm (val C a :: val C b :: R.map (val C)) := by
    have := p1.map (val C)
    simpa only [St, List.map_cons] using this
  have q2 : (St C (t + 1)).Perm (opv o (val C a) (val C b) ::
      kept (decide (a ∈ A)) (val C a) (kept (decide (b ∈ A)) (val C b) (R.map (val C)))) := by
    have := ((F1 hu).trans (p2.cons (6 + t))).map (val C)
    simp only [List.map_cons, map_kept] at this
    rw [hv] at this
    exact this
  exact Run.perm q1.symm (Run.two (Run.perm q2 hd))

theorem step_one {C : Circuit} {t d : ℕ} {g : Gate} (hg : C.gates[t]? = some g)
    (hu : Useful C (6 + t)) (hd : Run d (St C (t + 1))) {a : ℕ} (ha : a < 6 + t)
    (hai : a ∈ g.inputs) (hall : ∀ w ∈ g.inputs, w < 6 + t → w = a)
    (hv : val C (6 + t) = val C a ∨ val C (6 + t) = 0) : Run (d + 1) (St C t) := by
  let A := Aset C t
  let R := A.filter (fun w => decide (w ≠ a))
  have hR : ∀ w, w ∈ R ↔ w ∈ A ∧ w ≠ a := by simp [R]
  have nR : R.Nodup := List.Nodup.filter _ (nodup_A C t)
  have p1 : (Live C t).Perm (a :: R) := by
    have hn : (a :: R).Nodup := List.nodup_cons.2 ⟨by rw [hR]; rintro ⟨_, h⟩; exact h rfl, nR⟩
    rw [List.perm_ext_iff_of_nodup (nodup_Live C t) hn]
    intro w
    rw [F2 hg hu, List.mem_cons, hR, mem_A]
    constructor
    · rintro ⟨hw, h | h⟩
      · by_cases hwa : w = a
        · exact Or.inl hwa
        · exact Or.inr ⟨⟨hw, h⟩, hwa⟩
      · exact Or.inl (hall w h hw)
    · rintro (rfl | ⟨⟨hw, h⟩, _⟩)
      · exact ⟨ha, Or.inr hai⟩
      · exact ⟨hw, Or.inl h⟩
  have p2 : A.Perm (kept (decide (a ∈ A)) a R) := by
    have hn : (kept (decide (a ∈ A)) a R).Nodup := by
      cases decide (a ∈ A)
      · exact nR
      · exact List.nodup_cons.2 ⟨by rw [hR]; rintro ⟨_, h⟩; exact h rfl, nR⟩
    rw [List.perm_ext_iff_of_nodup (nodup_A C t) hn]
    intro w
    rw [mem_kept_iff, hR, decide_eq_true_iff]
    constructor
    · intro h
      by_cases hwa : w = a
      · subst hwa
        exact Or.inl ⟨h, rfl⟩
      · exact Or.inr ⟨h, hwa⟩
    · rintro (⟨h, rfl⟩ | ⟨h, _⟩) <;> exact h
  have q1 : (St C t).Perm (val C a :: R.map (val C)) := by
    have := p1.map (val C)
    simpa only [St, List.map_cons] using this
  have q2 : (St C (t + 1)).Perm (val C (6 + t) ::
      kept (decide (a ∈ A)) (val C a) (R.map (val C))) := by
    have := ((F1 hu).trans (p2.cons (6 + t))).map (val C)
    simp only [List.map_cons, map_kept] at this
    exact this
  rcases hv with hv | hv
  · rw [hv] at q2
    by_cases haA : a ∈ A
    · have e : decide (a ∈ A) = true := decide_eq_true haA
      rw [e] at q2
      exact Run.perm q1.symm (Run.copy (Run.perm q2 hd))
    · have e : decide (a ∈ A) = false := decide_eq_false haA
      rw [e] at q2
      exact (Run.perm (q2.trans q1.symm) hd).mono
  · rw [hv] at q2
    exact Run.perm q1.symm (Run.zap (Run.perm q2 hd))

theorem step_zero {C : Circuit} {t d : ℕ} {g : Gate} (hg : C.gates[t]? = some g)
    (hu : Useful C (6 + t)) (hd : Run d (St C (t + 1))) (hall : ∀ w ∈ g.inputs, ¬ w < 6 + t)
    (hv : val C (6 + t) = 0 ∨ val C (6 + t) = ALLV) : Run (d + 1) (St C t) := by
  have p1 : (Live C t).Perm (Aset C t) := by
    rw [List.perm_ext_iff_of_nodup (nodup_Live C t) (nodup_A C t)]
    intro w
    rw [F2 hg hu, mem_A]
    constructor
    · rintro ⟨hw, h | h⟩
      · exact ⟨hw, h⟩
      · exact absurd hw (hall w h)
    · rintro ⟨hw, h⟩
      exact ⟨hw, Or.inl h⟩
  have q2 : (St C (t + 1)).Perm (val C (6 + t) :: (Aset C t).map (val C)) := by
    have := (F1 hu).map (val C)
    simpa only [St, List.map_cons] using this
  have q1 : (St C t).Perm ((Aset C t).map (val C)) := by
    have := p1.map (val C)
    simpa only [St] using this
  exact Run.perm q1.symm (Run.const hv (Run.perm q2 hd))

theorem step_useful {C : Circuit} (hM : PEqualNP.MetaComplexity.Monotone2 C) {t d : ℕ} {g : Gate}
    (hg : C.gates[t]? = some g) (hu : Useful C (6 + t)) (hd : Run d (St C (t + 1))) :
    Run (d + 1) (St C t) := by
  have hmem : g ∈ C.gates := List.mem_of_getElem? hg
  obtain ⟨hop, hlen⟩ := hM g hmem
  have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hop
  obtain ⟨v0, v1, v2⟩ := val_gate C t g hg hop'
  rcases hin : g.inputs with _ | ⟨i, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
  · exact step_zero hg hu hd (by simp [hin]) (v0 hin)
  · by_cases hi : i < 6 + t
    · refine step_one hg hu hd hi (by simp [hin]) (by simp [hin]) (Or.inl ?_)
      rw [v1 i hin, rdv, if_pos hi]
    · refine step_zero hg hu hd (by simp [hin]; omega) (Or.inl ?_)
      rw [v1 i hin, rdv, if_neg hi]
  · obtain ⟨o, ho⟩ := v2 i i2 hin
    have r1 : ∀ k, rdv C t k = if k < 6 + t then val C k else 0 := fun k => rfl
    by_cases h1 : i < 6 + t <;> by_cases h2 : i2 < 6 + t
    · by_cases h12 : i = i2
      · subst h12
        refine step_one hg hu hd h1 (by simp [hin]) (by simp [hin]) (Or.inl ?_)
        rw [ho, r1, if_pos h1]
        cases o <;> simp [opv]
      · exact step_two hg hu hd h12 h1 h2 (by simp [hin]) (by simp [hin]) (by simp [hin])
          (by rw [ho, r1, r1, if_pos h1, if_pos h2])
    · refine step_one hg hu hd h1 (by simp [hin]) (by simp [hin, h2]) ?_
      rw [ho, r1, r1, if_pos h1, if_neg h2]
      cases o <;> simp [opv]
    · refine step_one hg hu hd h2 (by simp [hin]) (by simp [hin, h1]) ?_
      rw [ho, r1, r1, if_neg h1, if_pos h2]
      cases o <;> simp [opv]
    · refine step_zero hg hu hd (by simp [hin]; omega) (Or.inl ?_)
      rw [ho, r1, r1, if_neg h1, if_neg h2]
      cases o <;> simp [opv]
  · rw [hin] at hlen
    simp at hlen

theorem run_all (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (ho : C.output < 6 + C.gates.length) (hT : val C C.output = FULL) :
    ∀ d t, t + d = C.gates.length → Run d (St C t)
  | 0, t, h => by
    have p : (Live C t).Perm [C.output] := by
      rw [List.perm_ext_iff_of_nodup (nodup_Live C t) (List.nodup_singleton _)]
      intro w
      rw [mem_Live, List.mem_singleton]
      constructor
      · rintro ⟨_, h' | ⟨j, g, hj, _, hg, _⟩⟩
        · exact h'
        · rw [List.getElem?_eq_none (by omega)] at hg
          cases hg
      · rintro rfl
        exact ⟨by omega, Or.inl rfl⟩
    have q := p.map (val C)
    simp only [List.map_cons, List.map_nil, hT] at q
    exact Run.perm q.symm (Run.done 0)
  | d + 1, t, h => by
    have ht : t < C.gates.length := by omega
    have hg : C.gates[t]? = some C.gates[t] := List.getElem?_eq_getElem ht
    have hd := run_all C hM ho hT d (t + 1) (by omega)
    by_cases hu : Useful C (6 + t)
    · exact step_useful hM hg hu hd
    · have p : (Live C t).Perm (Live C (t + 1)) := by
        rw [List.perm_ext_iff_of_nodup (nodup_Live C t) (nodup_Live C (t + 1))]
        intro w
        rw [mem_Live, mem_Live]
        constructor
        · rintro ⟨hw, h' | ⟨j, g', hj, hu', hg', hi⟩⟩
          · exact ⟨by omega, Or.inl h'⟩
          · rcases Nat.eq_or_lt_of_le hj with rfl | hj'
            · exact absurd hu' hu
            · exact ⟨by omega, Or.inr ⟨j, g', hj', hu', hg', hi⟩⟩
        · rintro ⟨hw, h'⟩
          by_cases hwt : w = 6 + t
          · exfalso
            subst hwt
            rcases h' with h' | ⟨j, g', hj, hu', hg', hi⟩
            · exact hu (h' ▸ useful_out C)
            · exact hu (useful_step hu' hg' hi (by omega))
          · refine ⟨by omega, ?_⟩
            rcases h' with h' | ⟨j, g', hj, hu', hg', hi⟩
            · exact Or.inl h'
            · exact Or.inr ⟨j, g', by omega, hu', hg', hi⟩
      exact (Run.perm (p.map (val C)).symm hd).mono

def Xv (i : ℕ) : ℕ := encL (fun x => if h : i < 6 then x ⟨i, h⟩ else false) pts

def XL : List ℕ := (List.range 6).map Xv

theorem range_val (C : Circuit) : (List.range 6).map (val C) = XL := by
  apply List.map_congr_left
  intro i hi
  have hi' : i < 6 := List.mem_range.1 hi
  have e : W C i = fun x => if h : i < 6 then x ⟨i, h⟩ else false := by
    funext x
    rw [W_input C i hi' x, dif_pos hi']
  rw [val, e]
  rfl

theorem goalT : encL (fun x => decide (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) pts = FULL := by
  decide +kernel

theorem goal01 : decide (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ ptOf (0, 1) u = true ∧ ptOf (0, 1) v = true) = true := by
  decide +kernel

def L8 : List (List ℕ) := [
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0]]

def L7 : List (List ℕ) := [
  [0x82082082082080000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x3cf3cf3cf3cf3c0fff00003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x5d75d75d75d75c003ffc0fff03f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x41041041041040000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xcf3cf3cf3cf3cff03f00003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x208208208208200000000000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x79e79e79e79e7bf03fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xaebaebaebaebafffc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xebaebaebaebaebf000fff03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x104104104104100000000000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xb6db6db6db6db40fc003ffc0fff, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xf3cf3cf3cf3cf3ffc000003ffff],
  [0xfc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd75d75d75d75d40fffffffc0000],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x410410410410400000000000000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x820820820820800000000000000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xfffffffffffffffffffffffffff]]

def L6 : List (List ℕ) := [
  [0x82082082082080000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e380fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x59659659659658003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xcb2cb2cb2cb2cbf00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f, 0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x5d75d75d75d75c003ffc0fff03f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xcf3cf3cf3cf3cff03f00003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x79e79e79e79e7bf03fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000, 0xc30c30c30c30c003f00003f03f, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xebaebaebaebaebf000fff03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x20820820820820000000000003f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x3cf3cf3cf3cf3ffffffff03ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3ffc0000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x7df7df7df7df7ff03fffffff03f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x4104104104104000003f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xaebaebaebaebafffffffffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f00000003f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xefbefbefbefbeff03ffff03ffff],
  [0x3f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff00003f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x28a28a28a28a2bf000fff00003f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff00003f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc30c30c30c30c3f00000003ffff],
  [0x3f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffff],
  [0x3f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x3cf3cf3cf3cf3c0fff00003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x3cf3cf3cf3cf3c0fff00003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x3cf3cf3cf3cf3c0fff00003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xcf3cf3cf3cf3cff03f00003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a280000000000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x3cf3cf3cf3cf3c0fff00003ffff, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x3cf3cf3cf3cf3c0fff00003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xf3cf3cf3cf3cf3ffc000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x10410410410410003f000000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x7df7df7df7df7c0ffffc0ffffff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x41041041041040fc0000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xbefbefbefbefbc0fff03fffffff, 0xc30c30c30c30c3f00000003ffc0],
  [0x3ffc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xffffffffffffffffff00003ffff],
  [0x3f000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf03ffff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x28a28a28a28a2bf03ffff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf03ffff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fff000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x30c30c30c30c300fff000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fff000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fff03ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x861861861861840fff03ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fff03ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f03f00003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc30c30c30c30c3f03f00003ffc0],
  [0x3f000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f03f00003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x5d75d75d75d75c003ffc0fff03f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x5d75d75d75d75c003ffc0fff03f, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x82082082082080000fc0000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x5d75d75d75d75c003ffc0fff03f, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x10410410410410000000000003f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x5d75d75d75d75c003ffc0fff03f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0x41041041041040000000fc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xdf7df7df7df7dc0fffffffff03f],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x41041041041040000000003f000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xdf7df7df7df7dff03ffc0ffffff],
  [0x41041041041040000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x34d34d34d34d340fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x55555555555554003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x8208208208208000003f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xb6db6db6db6db40fc003ffc0fff, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc000000003f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0, 0xd75d75d75d75d40fffffffc0000],
  [0x3f000fc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x82082082082080000000003f000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xcf3cf3cf3cf3cfffff03fffffff],
  [0x3f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fff000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x51451451451450003ffc0fff000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fff000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffff000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x861861861861840fc003ffff000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffff000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xcf3cf3cf3cf3cff03f00003ffff],
  [0x820820820820bf000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xcf3cf3cf3cf3cff03f00003ffff, 0xf3cf3cf3cf3cf3ffc000003ffff],
  [0xfff, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xcf3cf3cf3cf3cff03f00003ffff, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x41041041041040003f000000000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840000000000000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2c003f00003f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x208208208208200000000000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c70003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xa69a69a69a69a40fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xe38e38e38e38e3f00000003ffc0],
  [0x8208208208208000000000003f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000, 0xc30c30c30c30c003f00003f03f, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xaebaebaebaebafffc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xebaebaebaebaebf000fff03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xb6db6db6db6db40fc003ffc0fff, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xf3cf3cf3cf3cf3ffc000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x104104104104100000fc0000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x79e79e79e79e7bffffffffc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc003f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xbefbefbefbefbfffc0ffffc0fff, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000fc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xfbefbefbefbefbffc0fff03ffff],
  [0xc30c30c30c30c003ffc003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0xc30c30c30c30c003ffc003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000, 0xc30c30c30c30c003ffc003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0fc0000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x30c30c30c30c300fc0fc0000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0fc0000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fc003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc30c30c30c30c3f000fc003ffc0],
  [0xfc0000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fc003ffc0],
  [0xfc0000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x8208208208208003f000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x79e79e79e79e7bf03fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x79e79e79e79e7bf03fffffc0000, 0x861861861861840fc003ffc0000, 0xaebaebaebaebafffc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300000000000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x79e79e79e79e7bf03fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd75d75d75d75d40fffffffc0000],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x79e79e79e79e7bf03fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0x3ffc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xffffffffffffffffffffffc0000],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x41041041041043f000000000000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xfbefbefbefbefbf03ffffffffc0],
  [0xc30c30c30c30c003f03f03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0xc30c30c30c30c003f03f03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000, 0xc30c30c30c30c003f03f03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x51451451451450003fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00003f03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc30c30c30c30c3f00003f03ffc0],
  [0x3f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00003f03ffc0],
  [0xc30c30c30c30c0000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xaebaebaebaebafffc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x208208208208200fc0000000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0xaebaebaebaebafffc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd75d75d75d75d40fffffffc0000],
  [0xfc0fc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0xaebaebaebaebafffc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x82082082082083f000000000000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xefbefbefbefbefffc0fffffffc0],
  [0xc30c30c30c30ff03f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0xc30c30c30c30ff03f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000000, 0xc30c30c30c30ff03f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c33ffc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x30c30c30c30c33ffc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c33ffc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451453f03ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x51451451451453f03ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451453f03ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x86186186186187ffc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x86186186186187ffc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x86186186186187ffc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x8208208208208000000003f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xebaebaebaebaebf000fff03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x208208208208200000000000fc0, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xd34d34d34d34d3f03ffc0ffffc0, 0xebaebaebaebaebf000fff03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x410410410410400000fc0000000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc71c71c71c71c7ffc003fffffc0, 0xebaebaebaebaebf000fff03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x82082082082080000003f000000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x1c71c71c71c71c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bf000fff000000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x104104104104100000000000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x965965965965940fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f00000003ffc0],
  [0x3f00000003f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x208208208208200000fc0000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xb6db6db6db6db40fc003ffc0fff, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd75d75d75d75d40fffffffc0000],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xfc0000fc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xf7df7df7df7df40fffffffc0fff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x410410410410400000000000fc0, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xf3cf3cf3cf3cf3fffffc0ffffff],
  [0xc30c30c30c30c0fff00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0xc30c30c30c30c0fff00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000000, 0xc30c30c30c30c0fff00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bffc0fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x28a28a28a28a2bffc0fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bffc0fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500ffffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x514514514514500ffffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500ffffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3ffc000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc30c30c30c30c3ffc000003ffc0],
  [0xfc0000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3ffc000003ffc0],
  [0x4104104104104000000000003f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x20820820820820000003f000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xb6db6db6db6db40fc003ffc0fff, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x104104104104100000000fc0000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0xb6db6db6db6db40fc003ffc0fff, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x820820820820800000000000fc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xf7df7df7df7df7ffc003fffffff],
  [0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0, 0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000fc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x28a28a28a28a2bf000fff000fc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000fc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0fc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x51451451451450003ffc0fc0fc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0fc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0fc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x861861861861840fc003ffc0fc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0fc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0x3f03f, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x20820820820823f000000000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xf3cf3cf3cf3cf3ffc000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500000000000000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc71c71c71c71c7ffc003fffffc0, 0xf3cf3cf3cf3cf3ffc000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x820820820820800fc0000000000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000, 0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000fc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x30c30c30c30c300fc0000fc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000fc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000000ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc30c30c30c30c3f000000ffffc0],
  [0xfc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000000ffffc0],
  [0xfc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xfc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7ffc003fffffc0],
  [0x4104104104104003f000000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfff000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x104104104104100fc0000000000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd75d75d75d75d40fffffffc0000],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c00000000000000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd75d75d75d75d7fffffffffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x4d34d34d34d34c003f00003f03f, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x69a69a69a69a6bf000fff000000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700fc0000000fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x410410410410400000000000000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c40fc003ffc0000],
  [0x3f00003f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000fc0000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x104104104104100000000000fc0, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc71c71c71c71c7ffc003fffffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x820820820820800000000fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c003f00003f03f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xaaaaaaaaaaaaabf000fff000000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xb2cb2cb2cb2cb00fc0000000fff, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d0003ffc0fc0000],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x820820820820800000000000000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x4104104104104000000003f000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f00003f000000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000fc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x410410410410400000000fc0000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xfffffffffffffffffffffffffff]]

def L5 : List (List ℕ) := [
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffff],
  [0x3f, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003ffc003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000000, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f03f03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30ff03f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff00003f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf03ffff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00003f03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f00000003ffc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300ffffc0000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fffffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f03ffc003ffc0],
  [0x3ffc0fc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c33ffc000003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451453f03ffc0fff000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x86186186186187ffc003ffff000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff00003f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff00003f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff00003f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffff],
  [0xc30c30c30c30c0fff00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x3cf3cf3cf3cf3c0fff00003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xcf3cf3cf3cf3cff03f00003ffff, 0xf3cf3cf3cf3cf3ffc000003ffff],
  [0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fff000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff03ffc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0ffffc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003fffffc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fff03ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f03f00003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf03ffff000000, 0x30c30c30c30c300fff000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf03ffff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fff03ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf03ffff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f03f00003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fff000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fff03ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fff000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f03f00003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fff03ffc0000, 0xc30c30c30c30c3f03f00003ffc0],
  [0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fff000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fff000, 0x861861861861840fc003ffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x3f000, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003fffffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00003f03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bffc0fff00003f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500ffffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3ffc000003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf03fffffc0000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fff000fc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f03f000ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffff000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0000000fff, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fff000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffff000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fff000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffff000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fff000, 0x861861861861840fc003ffc0000, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fff000, 0x861861861861840fc003ffff000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000fff, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0fff, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003ffc003f03f, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x30c30c30c30c300fc0000000fff, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fc003ffc0],
  [0xfc0000000, 0xc30c30c30c30c003f00003f03f, 0x38e38e38e38e3bffc0fff000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bffc0fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000fc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0fc0000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c33ffc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc003ffc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c0fff03f03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500fffffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3ffc003f03ffc0],
  [0xc30c30c30c30ff03f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451453f03ffc0fc0fc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x86186186186187ffc003ffc0fc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003ffc003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003ffc003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0fc0000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003ffc003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003ffc003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fc003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fc003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0fc0000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0fc0000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fc003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f000fc003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fc003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x30c30c30c30c300fc0000000fff, 0x79e79e79e79e7bf03fffffc0000, 0xaebaebaebaebafffc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd75d75d75d75d40fffffffc0000],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451453f03ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f03ffff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc003ffc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00003fffffc0],
  [0xc30c30c30c30c003f03f03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f03f03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f03f03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00003f03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00003f03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00003f03ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00003f03ffc0],
  [0xc30c30c30c30c003ffc0fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0fc0fc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x86186186186187ffc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30ff03f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c33ffc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30ff03f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451453f03ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30ff03f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x86186186186187ffc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c33ffc0000000fff, 0x51451451451453f03ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c33ffc0000000fff, 0x51451451451450003ffc0fc0000, 0x86186186186187ffc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451453f03ffc0fc0000, 0x86186186186187ffc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf03ffff00003f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fff03ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f03f00003ffff],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000fc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000fc0, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x51451451451450003ffc0fc0000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0fc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xfc0, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500ffffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0fc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c0fff000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bffc0ffffc0000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3ffc0000ffffc0],
  [0x3f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c0fff00003f03f, 0x28a28a28a28a2bffc0fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c0fff00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500ffffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c0fff00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3ffc000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bffc0fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500ffffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bffc0fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3ffc000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3ffc000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500ffffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3ffc000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0fc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000fc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0fc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0fc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000fc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000fc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0fc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000fc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0fc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0fc0, 0x861861861861840fc003ffc0fc0, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0fc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fff03f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000fc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000000ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000000fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000fc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000000ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000fc0fff, 0x51451451451450003ffc0fc0000, 0xc30c30c30c30c3f00000003ffc0, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000fc0fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000000ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000000ffffc0],
  [0xfc0000, 0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0xc71c71c71c71c7ffc003fffffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003ffff03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fff03ffc0],
  [0x3f000fff000000, 0xc30c30c30c30c003f00003f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf03ffff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fff00003ffff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fff03ffff000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30ff03ffc003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c33ffc0fc0000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x86186186186187ffc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30ff03f03f03f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c33ffc003f000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451453f03fffffc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c0fff00003ffff, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bffc0fff000fc0, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x514514514514500ffffc0fc0fc0, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0]]

def L4 : List (List ℕ) := [
  [0x2cb2cb2cb2cb2ff03ffff03f03f, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc003f, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0x2cb2cb2cb2cb2ff03ffff03f03f, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc003f, 0xc30c30c30c30c3f00000003ffc0],
  [0x2cb2cb2cb2cb2ff03ffff03f03f, 0x38e38e38e38e3bffc0fff000fff, 0x51451451451450003ffc0fc0000, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffff],
  [0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc003f000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003fffffc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00000003ffc0],
  [0x2cb2cb2cb2cb2ff03ffff03f03f, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc30c30c30c30c3f00003f03ffc0],
  [0x28a28a28a28a2bf000fff03f000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc71c71c71c71c7ffc003fffffc0],
  [0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc000003ffff, 0x51451451451450003ffc0fc0000, 0x8e38e38e38e38c0fff03ffff03f, 0xc71c71c71c71c7ffc003fffffc0],
  [0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0x51451451451450003ffc0fff000, 0x8e38e38e38e38c0fff03ffff03f, 0xc71c71c71c71c7ffc003fffffc0],
  [0xc30c30c30c30c003ffc003f03f, 0x38e38e38e38e3bffc0fff000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x38e38e38e38e3bffc0fff000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc0ffffc0000, 0xc30c30c30c30c3f00000003ffc0],
  [0xc30c30c30c30c003f00003f03f, 0x38e38e38e38e3bffc0fff000fff, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xc30c30c30c30c3f000fc003ffc0],
  [0xc30c30c30c30c003f00003ffff, 0x28a28a28a28a2bf000fff000000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000fc0, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0000, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x71c71c71c71c700ffffc0fc0fff, 0x861861861861840fc003ffc0fc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f000fff03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000000fff, 0xc71c71c71c71c7ffc003fffffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000ffffc0000, 0x30c30c30c30c300fc0000000fff, 0xc71c71c71c71c7ffc003fffffc0, 0xd34d34d34d34d3f03ffc0ffffc0],
  [0xc30c30c30c30c003f00003f03f, 0x28a28a28a28a2bf000fff000000, 0x30c30c30c30c300fc0000fc0fff, 0xc71c71c71c71c7ffc003fffffc0, 0xd34d34d34d34d3f03ffc0ffffc0]]

def Lv (s : ℕ) : List (List ℕ) := ([[], [], [], [], L4, L5, L6, L7, L8] : List (List (List ℕ))).getD s []

theorem c8 : (Lv 8).all (chk Lv 8) = true := by decide +kernel
theorem c7 : (Lv 7).all (chk Lv 7) = true := by decide +kernel
theorem c6 : (Lv 6).all (chk Lv 6) = true := by decide +kernel
theorem c5 : (Lv 5).all (chk Lv 5) = true := by decide +kernel
theorem c4 : (Lv 4).all (chk Lv 4) = true := by decide +kernel

theorem top_ok : ∀ L ∈ XL.sublists, covN L = FULL → List.insertionSort (· ≤ ·) L ∈ Lv 8 := by
  decide +kernel

theorem chk_all : ∀ s, ∀ L ∈ Lv s, chk Lv s L = true := by
  have key : ∀ s, (Lv s).all (chk Lv s) = true := by
    intro s
    rcases s with _ | _ | _ | _ | _ | _ | _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c4
    · exact c5
    · exact c6
    · exact c7
    · exact c8
    · rfl
  intro s L hL
  exact List.all_eq_true.1 (key s) L hL

theorem main : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hM, hs, hf⟩
  have e : ∀ x, W C C.output x = decide (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hf x
  have hT : val C C.output = FULL := by
    have h1 : W C C.output = fun x => decide (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := funext e
    rw [val, h1]
    exact goalT
  have ho : C.output < 6 + C.gates.length := by
    by_contra hcon
    have h1 := e (ptOf (0, 1))
    have h2 : W C C.output (ptOf (0, 1)) = false := by
      rw [W, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
      · rfl
      · rw [wires_eq, foldl_len, List.length_ofFn]
        omega
    rw [h2, goal01] at h1
    cases h1
  have hrun : Run C.gates.length (St C 0) := run_all C hM ho hT _ 0 (by simp)
  have h8 : Run 8 (St C 0) := Run.mono_le hs hrun
  have hsub : St C 0 ∈ XL.sublists := by
    rw [List.mem_sublists, ← range_val C]
    exact List.Sublist.map _ List.filter_sublist
  have hin := top_ok (St C 0) hsub (cov_full h8.inv.2)
  exact cert Lv chk_all 8 _ hin (Run.perm (List.perm_insertionSort _ _).symm h8)

end PEqualNP.Outside.L_meta_618

theorem PEqualNP.Outside.L_meta_618 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) :=
  PEqualNP.Outside.L_meta_618.main
