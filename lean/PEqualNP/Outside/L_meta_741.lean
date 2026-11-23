import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_741

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

theorem eqL_sound : ∀ {a b : List ℕ}, eqL a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [eqL, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eqL_sound h.2]
  | [], _ :: _, h => by simp [eqL] at h
  | _ :: _, [], h => by simp [eqL] at h

inductive T where
  | e : T
  | n : T → List ℕ → T → T

def toL : T → List (List ℕ)
  | .e => []
  | .n l k r => k :: (toL l ++ toL r)

def cpK : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, v => (v >>> p) % 2 + 2 * cpK ps v

def exK : List ℕ → ℕ → ℕ
  | [], _ => 0
  | k :: ks, c => (c % 2) * k + exK ks (c / 2)

def cpP : List ℕ := [0, 6, 12, 18, 24, 30, 36, 42, 48, 54, 55, 56, 57, 58, 59]

def KL : List ℕ := [0x3f, 0xfc0, 0x3f000, 0xfc0000, 0x3f000000, 0xfc0000000, 0x3f000000000, 0xfc0000000000, 0x3f000000000000, 0x41041041041040000000000000, 0x82082082082080000000000000, 0x104104104104100000000000000, 0x208208208208200000000000000, 0x410410410410400000000000000, 0x820820820820800000000000000]

def cp (v : ℕ) : ℕ := cpK cpP v

def ex (c : ℕ) : ℕ := exK KL c

def ltL : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => Nat.blt x y || (Nat.beq x y && ltL xs ys)

def memT (L kc : List ℕ) : T → Bool
  | .e => false
  | .n l k r => cond (eqL kc k) (eqL L (k.map ex)) (cond (ltL kc k) (memT L kc l) (memT L kc r))

def dec (t : T) : List (List ℕ) := (toL t).map (List.map ex)

theorem memT_sound (L kc : List ℕ) : ∀ t : T, memT L kc t = true → L ∈ dec t
  | .e, h => by simp [memT] at h
  | .n l k r, h => by
    simp only [memT] at h
    cases h1 : eqL kc k <;> cases h2 : ltL kc k <;> simp only [h1, h2, cond_true, cond_false] at h
    · have := memT_sound L kc r h
      simp only [dec, toL, List.map_cons, List.map_append, List.mem_cons, List.mem_append] at this ⊢
      tauto
    · have := memT_sound L kc l h
      simp only [dec, toL, List.map_cons, List.map_append, List.mem_cons, List.mem_append] at this ⊢
      tauto
    · simp [dec, toL, eqL_sound h]
    · simp [dec, toL, eqL_sound h]

def chk (Tv : ℕ → T) : ℕ → List ℕ → Bool
  | 0, L => !(eqL L [FULL])
  | s + 1, L => !(eqL L [FULL]) && (children L).all fun ch =>
      !(passes s ch) || (let S := List.insertionSort (· ≤ ·) ch; memT S (S.map cp) (Tv s))

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

theorem eqL_self : ∀ (a : List ℕ), eqL a a = true
  | [] => rfl
  | x :: xs => by simp [eqL, eqL_self xs]

theorem memL_sound {L : List ℕ} {Ls : List (List ℕ)} (h : memL L Ls = true) : L ∈ Ls := by
  simp only [memL, List.any_eq_true] at h
  obtain ⟨M, hM, he⟩ := h
  rw [eqL_sound he]
  exact hM

theorem cert (Tv : ℕ → T) (hc : ∀ s, ∀ L ∈ dec (Tv s), chk Tv s L = true) :
    ∀ s, ∀ L ∈ dec (Tv s), ¬ Run s L := by
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
      · exact ih _ (memT_sound _ _ _ h1) (Run.perm (List.perm_insertionSort _ _).symm hr')

open PEqualNP.CircuitLowerBounds

def EL : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)]
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

theorem goalT : encL (fun x => decide (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) pts = FULL := by
  decide +kernel

theorem goal01 : decide (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ ptOf (0, 1) u = true ∧ ptOf (0, 1) v = true) = true := by
  decide +kernel

def T4 : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [201, 5424, 7879, 24838, 27384] .e) [356, 6275, 15736, 17048, 26439]
 (.n .e [402, 1605, 10344, 22456, 31111] .e)) [1605, 5424, 6275, 10348, 17306]
 (.n
 (.n .e [1605, 5424, 6275, 10604, 17050] .e) [1605, 5424, 6275, 10606, 17310]
 (.n .e [1605, 5424, 6279, 10344, 17306] .e))) [1605, 5424, 6279, 10344, 17310]
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 10344, 24990] .e) [1605, 5424, 6283, 10348, 25502]
 (.n .e [1605, 5424, 6283, 17048, 24934] .e)) [1605, 5424, 6283, 17050, 26990]
 (.n
 (.n .e [1605, 5424, 6283, 25502, 26990] .e) [1605, 5424, 6287, 10344, 25502] .e))) [1605, 5424, 6299, 10344, 24990]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6299, 25502, 26990] .e) [1605, 5424, 6315, 25502, 26990]
 (.n .e [1605, 5424, 6347, 17048, 24870] .e)) [1605, 5424, 6347, 17080, 24838]
 (.n
 (.n .e [1605, 5424, 6347, 25502, 26990] .e) [1605, 5424, 6379, 17048, 24942] .e)) [1605, 5424, 6379, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6379, 17144, 24838] .e) [1605, 5424, 6535, 10344, 17310]
 (.n .e [1605, 5424, 10475, 17050, 24838] .e)) [1605, 5424, 10475, 17051, 24838]
 (.n
 (.n .e [1605, 5424, 14571, 17050, 24870] .e) [1605, 5424, 14571, 17050, 26990] .e)))) [1605, 5424, 14571, 17051, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 14571, 17054, 26990] .e) [1605, 5424, 14571, 17082, 24838]
 (.n .e [1605, 5424, 14571, 17306, 26990] .e)) [1605, 5426, 6275, 10606, 17048]
 (.n
 (.n .e [1605, 5426, 6283, 17048, 26990] .e) [1605, 5426, 10473, 17048, 24838]
 (.n .e [1605, 5426, 14571, 17048, 24870] .e))) [1605, 5426, 14571, 17048, 26990]
 (.n
 (.n
 (.n .e [1605, 5426, 14571, 17050, 26990] .e) [1605, 5426, 14571, 17080, 24838]
 (.n .e [1605, 5427, 14571, 17048, 26990] .e)) [1605, 5428, 6275, 10344, 17310]
 (.n
 (.n .e [1605, 5428, 6283, 10344, 25502] .e) [1605, 5430, 6275, 10344, 17310] .e))) [1605, 5430, 6275, 10606, 17048]
 (.n
 (.n
 (.n
 (.n .e [1605, 5430, 14571, 17048, 26990] .e) [1605, 5432, 6275, 10344, 24982]
 (.n .e [1605, 5432, 6275, 10344, 24990] .e)) [1605, 5432, 6275, 10348, 25502]
 (.n
 (.n .e [1605, 5432, 6275, 17048, 24934] .e) [1605, 5432, 6275, 17048, 24942] .e)) [1605, 5432, 6275, 17050, 26990]
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 25502, 26990] .e) [1605, 5432, 6279, 10344, 25502]
 (.n .e [1605, 5432, 6283, 25502, 26990] .e)) [1605, 5434, 6275, 17048, 26990]
 (.n
 (.n .e [1605, 5436, 6275, 10344, 25502] .e) [1605, 5496, 6275, 17048, 24942] .e))))) [1605, 5496, 6275, 17144, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5496, 6275, 25502, 26990] .e) [1605, 5554, 10344, 17048, 24839]
 (.n .e [1605, 5554, 10345, 17048, 24838] .e)) [1605, 5554, 14571, 17048, 26990]
 (.n
 (.n .e [1605, 5555, 10344, 17048, 24839] .e) [1605, 5555, 10344, 17048, 24967]
 (.n .e [1605, 5555, 10344, 17049, 24838] .e))) [1605, 5555, 10344, 17051, 24838]
 (.n
 (.n
 (.n .e [1605, 5555, 10475, 17048, 24838] .e) [1605, 5560, 6275, 10344, 24990]
 (.n .e [1605, 5560, 6275, 10488, 24838] .e)) [1605, 5560, 6275, 25502, 26990]
 (.n
 (.n .e [1605, 5625, 6275, 24838, 27384] .e) [1605, 6275, 10616, 17336, 24838] .e))) [1605, 6275, 10746, 22456, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 6275, 15736, 17404, 24838] .e) [1605, 6547, 10344, 17080, 24838]
 (.n .e [1605, 6579, 10344, 17048, 24870] .e)) [1605, 6579, 10344, 17048, 24886]
 (.n
 (.n .e [1605, 6579, 10344, 17080, 24838] .e) [1605, 6579, 10344, 17336, 24838] .e)) [1605, 7603, 10344, 17048, 24871]
 (.n
 (.n
 (.n .e [1605, 7603, 10344, 17049, 24870] .e) [1605, 7603, 10344, 17080, 24839]
 (.n .e [1605, 7603, 10344, 17081, 24838] .e)) [1605, 7603, 10345, 17048, 24870]
 (.n
 (.n .e [1605, 7603, 10345, 17080, 24838] .e) [1605, 7603, 14571, 17048, 24870] .e)))) [1605, 7603, 14571, 17048, 24878]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 7603, 14571, 17048, 24886] .e) [1605, 7603, 14571, 17048, 24934]
 (.n .e [1605, 7603, 14571, 17080, 24838] .e)) [1605, 7603, 14571, 17080, 24870]
 (.n
 (.n .e [1605, 7603, 14571, 17144, 24838] .e) [1605, 7603, 14571, 17336, 24838]
 (.n .e [1607, 5424, 6275, 10604, 17048] .e))) [1607, 5424, 6275, 10606, 17048]
 (.n
 (.n
 (.n .e [1607, 5424, 6283, 17048, 26990] .e) [1607, 5424, 10473, 17048, 24838]
 (.n .e [1607, 5424, 10475, 17048, 24838] .e)) [1607, 5424, 14571, 17048, 24870]
 (.n
 (.n .e [1607, 5424, 14571, 17048, 26990] .e) [1607, 5424, 14571, 17050, 26990] .e))) [1607, 5424, 14571, 17080, 24838]
 (.n
 (.n
 (.n
 (.n .e [1607, 5426, 14571, 17048, 26990] .e) [1607, 5432, 6275, 17048, 26990]
 (.n .e [1613, 5424, 6275, 10344, 24982] .e)) [1613, 5424, 6275, 10348, 25502]
 (.n
 (.n .e [1613, 5424, 6275, 17048, 24942] .e) [1613, 5424, 6275, 17050, 26990] .e)) [1613, 5424, 6275, 25502, 26990]
 (.n
 (.n
 (.n .e [1613, 5424, 6279, 10344, 25502] .e) [1613, 5424, 6283, 25502, 26990]
 (.n .e [1613, 5426, 6275, 17048, 26990] .e)) [1613, 5428, 6275, 10344, 25502]
 (.n
 (.n .e [1613, 5432, 6275, 25502, 26990] .e) [1615, 5424, 6275, 17048, 26990] .e)))))) [1629, 5424, 6275, 25502, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1637, 5424, 6379, 17048, 24838] .e) [1637, 5424, 14571, 17050, 24838]
 (.n .e [1637, 5426, 14571, 17048, 24838] .e)) [1637, 6547, 10344, 17048, 24838]
 (.n
 (.n .e [1637, 7603, 10344, 17048, 24839] .e) [1637, 7603, 10344, 17049, 24838]
 (.n .e [1637, 7603, 10345, 17048, 24838] .e))) [1637, 7603, 14571, 17048, 24838]
 (.n
 (.n
 (.n .e [1637, 7603, 14571, 17048, 24870] .e) [1637, 7603, 14571, 17080, 24838]
 (.n .e [1639, 5424, 14571, 17048, 24838] .e)) [1645, 5424, 6275, 17048, 24942]
 (.n
 (.n .e [1645, 5424, 6275, 25502, 26990] .e) [1645, 5424, 6379, 17048, 24838] .e))) [1645, 7603, 14571, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1653, 7603, 14571, 17048, 24838] .e) [1735, 5424, 10344, 17048, 24967]
 (.n .e [1735, 5424, 10475, 17048, 24838] .e)) [1735, 5424, 14571, 17048, 26990]
 (.n
 (.n .e [1741, 5424, 6275, 10344, 24854] .e) [1741, 5424, 6275, 10360, 24838] .e)) [1741, 5424, 6275, 25502, 26990]
 (.n
 (.n
 (.n .e [1757, 5424, 6275, 10344, 24990] .e) [1757, 5424, 6275, 10360, 24838]
 (.n .e [1757, 5424, 6275, 10488, 24838] .e)) [1757, 5424, 6291, 10344, 24838]
 (.n
 (.n .e [1757, 5424, 6299, 10344, 24838] .e) [1863, 5424, 6275, 10606, 17048] .e)))) [1863, 5424, 6535, 10344, 17048]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1863, 5424, 14571, 17048, 26990] .e) [1893, 6275, 10360, 17048, 24838]
 (.n .e [1893, 6291, 10344, 17048, 24838] .e)) [1893, 7603, 14571, 17048, 24838]
 (.n
 (.n .e [1909, 6275, 10344, 17048, 24854] .e) [1909, 6275, 10344, 17048, 24886]
 (.n .e [1909, 6275, 10360, 17048, 24838] .e))) [1909, 6275, 10616, 17048, 24838]
 (.n
 (.n
 (.n .e [1909, 6579, 10344, 17048, 24838] .e) [2007, 5424, 10344, 17048, 31111]
 (.n .e [5424, 6275, 10348, 17117, 24838] .e)) [5424, 6275, 10348, 18141, 24854]
 (.n
 (.n .e [5424, 6275, 10348, 18141, 25502] .e) [5424, 6275, 10349, 17117, 24838] .e))) [5424, 6275, 10349, 18141, 25502]
 (.n
 (.n
 (.n
 (.n .e [5424, 6275, 10350, 18141, 25502] .e) [5424, 6275, 10364, 18141, 24838]
 (.n .e [5424, 6275, 10604, 18141, 25502] .e)) [5424, 6279, 10344, 17113, 24838]
 (.n
 (.n .e [5424, 6279, 10344, 17117, 24838] .e) [5424, 6279, 10344, 18141, 24854] .e)) [5424, 6279, 10344, 18141, 25502]
 (.n
 (.n
 (.n .e [5424, 6279, 10348, 18141, 25502] .e) [5424, 6279, 10360, 18141, 24838]
 (.n .e [5424, 6291, 10348, 18141, 24838] .e)) [5424, 6295, 10344, 18141, 24838]
 (.n
 (.n .e [5424, 6343, 10344, 17048, 24903] .e) [5424, 6343, 10344, 17117, 24838] .e))))) [5424, 6343, 10344, 18141, 25502]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [5424, 6535, 10344, 18141, 25502] .e) [5424, 6631, 10344, 17048, 26439]
 (.n .e [5424, 7879, 10344, 17048, 25039] .e)) [5428, 6275, 10344, 17113, 24838]
 (.n
 (.n .e [5428, 6275, 10344, 18141, 24854] .e) [5428, 6275, 10344, 18141, 25502]
 (.n .e [5428, 6275, 10348, 18141, 25502] .e))) [5428, 6275, 10360, 18141, 24838]
 (.n
 (.n
 (.n .e [5428, 6279, 10344, 18141, 25502] .e) [5428, 6291, 10344, 18141, 24838]
 (.n .e [5429, 6275, 10344, 18141, 25502] .e)) [5430, 6275, 10344, 18141, 25502]
 (.n
 (.n .e [5492, 6275, 10344, 17048, 24839] .e) [5492, 6275, 10344, 17049, 24838] .e))) [5492, 6275, 10344, 18141, 25502]
 (.n
 (.n
 (.n
 (.n .e [5493, 6275, 10344, 17048, 24839] .e) [5493, 6275, 10344, 17048, 24903]
 (.n .e [5493, 6275, 10344, 17117, 24838] .e)) [5493, 6275, 10345, 17048, 24838]
 (.n
 (.n .e [5493, 6275, 10349, 17048, 24838] .e) [6005, 6275, 10344, 17048, 24855] .e)) [6005, 6275, 10344, 17049, 24854]
 (.n
 (.n
 (.n .e [6005, 6275, 10344, 18141, 24854] .e) [6005, 6275, 10344, 18141, 24862]
 (.n .e [6005, 6275, 10344, 18141, 24886] .e)) [6005, 6275, 10344, 18141, 24982]
 (.n
 (.n .e [6005, 6275, 10345, 17048, 24854] .e) [6005, 6275, 10360, 17048, 24839] .e)))) [6005, 6275, 10360, 17049, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [6005, 6275, 10360, 18141, 24838] .e) [6005, 6275, 10360, 18141, 24854]
 (.n .e [6005, 6275, 10361, 17048, 24838] .e)) [6005, 6275, 10488, 18141, 24838]
 (.n
 (.n .e [6005, 6275, 10616, 18141, 24838] .e) [6005, 6291, 10344, 17048, 24839]
 (.n .e [6005, 6291, 10344, 17049, 24838] .e))) [6005, 6291, 10344, 18141, 24838]
 (.n
 (.n
 (.n .e [6005, 6291, 10344, 18141, 24854] .e) [6005, 6291, 10345, 17048, 24838]
 (.n .e [6005, 6291, 10360, 18141, 24838] .e)) [6005, 6299, 10344, 18141, 24838]
 (.n
 (.n .e [6005, 6323, 10344, 18141, 24838] .e) [6005, 6547, 10344, 18141, 24838] .e))) [6005, 7603, 10344, 17048, 24839]
 (.n
 (.n
 (.n
 (.n .e [6005, 7603, 10344, 17048, 24903] .e) [6005, 7603, 10344, 17048, 24967]
 (.n .e [6005, 7603, 10344, 17049, 24838] .e)) [6005, 7603, 10344, 17049, 24839]
 (.n
 (.n .e [6005, 7603, 10344, 17051, 24838] .e) [6005, 7603, 10344, 17053, 24838] .e)) [6005, 7603, 10344, 17113, 24838]
 (.n
 (.n
 (.n .e [6005, 7603, 10345, 17048, 24838] .e) [6005, 7603, 10345, 17048, 24839]
 (.n .e [6005, 7603, 10345, 17049, 24838] .e)) [6005, 7603, 10347, 17048, 24838]
 (.n
 (.n .e [6005, 7603, 10349, 17048, 24838] .e) [6005, 7603, 10473, 17048, 24838] .e)))))))

def T5aaaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1, 1605, 5554, 10344, 17048, 24838] .e) [1, 1605, 7603, 10344, 17048, 24870]
 (.n .e [1, 1605, 7603, 10344, 17080, 24838] .e)) [1, 1637, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [1, 5492, 6275, 10344, 17048, 24838] .e) [1, 6005, 6275, 10344, 17048, 24854] .e)) [1, 6005, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1, 6005, 6291, 10344, 17048, 24838] .e) [1, 6005, 7603, 10344, 17048, 24838] .e) [1, 6005, 7603, 10344, 17048, 24839]
 (.n
 (.n .e [1, 6005, 7603, 10344, 17049, 24838] .e) [1, 6005, 7603, 10345, 17048, 24838] .e))) [2, 1605, 5424, 6275, 10604, 17048]
 (.n
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6283, 17048, 26990] .e) [2, 1605, 5424, 10473, 17048, 24838]
 (.n .e [2, 1605, 5424, 14571, 17048, 24870] .e)) [2, 1605, 5424, 14571, 17048, 26990]
 (.n
 (.n .e [2, 1605, 5424, 14571, 17050, 26990] .e) [2, 1605, 5424, 14571, 17080, 24838] .e)) [2, 1605, 5426, 14571, 17048, 26990]
 (.n
 (.n
 (.n .e [2, 1605, 5432, 6275, 17048, 26990] .e) [2, 1607, 5424, 14571, 17048, 26990] .e) [2, 1613, 5424, 6275, 17048, 26990]
 (.n
 (.n .e [2, 1637, 5424, 14571, 17048, 24838] .e) [3, 1605, 5424, 10472, 17048, 24838] .e)))) [3, 1605, 5424, 14571, 17048, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n .e [3, 1605, 5552, 10344, 17048, 24838] .e) [3, 6005, 7603, 10344, 17048, 24838]
 (.n .e [4, 1605, 5424, 6275, 10344, 17306] .e)) [4, 1605, 5424, 6283, 10344, 25502]
 (.n
 (.n .e [4, 1605, 5432, 6275, 10344, 25502] .e) [4, 1613, 5424, 6275, 10344, 25502] .e)) [4, 5424, 6275, 10344, 17113, 24838]
 (.n
 (.n
 (.n .e [4, 5424, 6275, 10344, 18141, 24854] .e) [4, 5424, 6275, 10344, 18141, 25502] .e) [4, 5424, 6275, 10348, 18141, 25502]
 (.n
 (.n .e [4, 5424, 6275, 10360, 18141, 24838] .e) [4, 5424, 6279, 10344, 18141, 25502] .e))) [4, 5424, 6291, 10344, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [4, 5428, 6275, 10344, 18141, 25502] .e) [5, 5424, 6275, 10344, 17112, 24838]
 (.n .e [5, 5424, 6275, 10344, 18141, 25502] .e)) [5, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [5, 6005, 7603, 10344, 17048, 24838] .e) [6, 1605, 5424, 6275, 10344, 17304] .e)) [6, 1605, 5424, 6275, 10600, 17048]
 (.n
 (.n
 (.n .e [6, 1605, 5424, 14571, 17048, 26990] .e) [6, 5424, 6275, 10344, 18141, 25502] .e) [8, 1605, 5424, 6275, 10344, 24982]
 (.n
 (.n .e [8, 1605, 5424, 6275, 10348, 25502] .e) [8, 1605, 5424, 6275, 17048, 24934] .e))))) [8, 1605, 5424, 6275, 17050, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 25502, 26990] .e) [8, 1605, 5424, 6279, 10344, 25502]
 (.n .e [8, 1605, 5424, 6283, 25502, 26990] .e)) [8, 1605, 5426, 6275, 17048, 26990]
 (.n
 (.n .e [8, 1605, 5428, 6275, 10344, 25502] .e) [8, 1605, 5432, 6275, 25502, 26990] .e)) [8, 1607, 5424, 6275, 17048, 26990]
 (.n
 (.n
 (.n .e [8, 1613, 5424, 6275, 25502, 26990] .e) [10, 1605, 5424, 6275, 17048, 26990] .e) [12, 1605, 5424, 6275, 10344, 25502]
 (.n
 (.n .e [16, 1741, 5424, 6275, 10344, 24838] .e) [16, 1893, 6275, 10344, 17048, 24838] .e))) [16, 5424, 6275, 10348, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [16, 5424, 6279, 10344, 18141, 24838] .e) [16, 5428, 6275, 10344, 18141, 24838]
 (.n .e [16, 6005, 6275, 10344, 17048, 24839] .e)) [16, 6005, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [16, 6005, 6275, 10344, 18141, 24838] .e) [16, 6005, 6275, 10344, 18141, 24854] .e)) [16, 6005, 6275, 10345, 17048, 24838]
 (.n
 (.n
 (.n .e [16, 6005, 6275, 10360, 18141, 24838] .e) [16, 6005, 6291, 10344, 18141, 24838] .e) [17, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [20, 5424, 6275, 10344, 18141, 24838] .e) [24, 1605, 5424, 6275, 10344, 24966] .e)))) [24, 1605, 5424, 6275, 25502, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n .e [24, 1733, 5424, 6275, 10344, 24838] .e) [24, 6005, 6275, 10344, 18141, 24838]
 (.n .e [32, 1605, 5424, 6347, 17048, 24838] .e)) [32, 1605, 5424, 14571, 17050, 24838]
 (.n
 (.n .e [32, 1605, 5426, 14571, 17048, 24838] .e) [32, 1605, 6547, 10344, 17048, 24838] .e)) [32, 1605, 7603, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [32, 1605, 7603, 10344, 17049, 24838] .e) [32, 1605, 7603, 10345, 17048, 24838] .e) [32, 1605, 7603, 14571, 17048, 24838]
 (.n
 (.n .e [32, 1605, 7603, 14571, 17048, 24870] .e) [32, 1605, 7603, 14571, 17080, 24838] .e))) [32, 1607, 5424, 14571, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [32, 1637, 7603, 14571, 17048, 24838] .e) [33, 1605, 7603, 10344, 17048, 24838] .e) [34, 1605, 5424, 14571, 17048, 24838]
 (.n
 (.n .e [40, 1605, 5424, 6275, 17048, 24902] .e) [40, 1605, 5424, 6275, 25502, 26990] .e)) [40, 1605, 5424, 6339, 17048, 24838]
 (.n
 (.n
 (.n .e [40, 1605, 7603, 14571, 17048, 24838] .e) [48, 1605, 6531, 10344, 17048, 24838] .e) [48, 1605, 7603, 14571, 17048, 24838]
 (.n
 (.n .e [48, 1861, 6275, 10344, 17048, 24838] .e) [48, 6005, 6275, 10344, 18141, 24838] .e))))))

def T5aaab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [65, 5428, 6275, 10344, 17048, 24838] .e) [65, 6005, 7603, 10344, 17048, 24838]
 (.n .e [68, 5424, 6275, 10344, 17048, 24839] .e)) [68, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [68, 5424, 6275, 10344, 18141, 25502] .e) [69, 5424, 6275, 10344, 17048, 24838] .e)) [69, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [69, 5424, 6275, 10344, 17048, 24902] .e) [69, 5424, 6275, 10344, 17048, 24903] .e) [69, 5424, 6275, 10344, 17048, 25502]
 (.n
 (.n .e [69, 5424, 6275, 10344, 17117, 24838] .e) [69, 5424, 6275, 10345, 17048, 24838] .e))) [69, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [69, 5424, 6275, 10349, 17048, 24838] .e) [69, 5424, 6279, 10344, 17048, 24838]
 (.n .e [69, 5424, 6339, 10344, 17048, 24838] .e)) [69, 5424, 6343, 10344, 17048, 24838]
 (.n
 (.n .e [69, 5424, 7603, 10344, 17048, 24838] .e) [69, 5493, 6275, 10344, 17048, 24838] .e)) [72, 1605, 5424, 6275, 17048, 24870]
 (.n
 (.n
 (.n .e [72, 1605, 5424, 6275, 17080, 24838] .e) [72, 1605, 5424, 6275, 25502, 26990] .e) [96, 1605, 5424, 6283, 17048, 24838]
 (.n
 (.n .e [96, 1605, 5432, 6275, 17048, 24838] .e) [96, 1605, 7603, 14571, 17048, 24838] .e)))) [104, 1605, 5424, 6275, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [104, 1605, 5424, 6275, 17048, 24942] .e) [104, 1605, 5424, 6275, 17080, 24838]
 (.n .e [104, 1605, 5424, 6275, 17112, 24838] .e)) [104, 1605, 5424, 6275, 17144, 24838]
 (.n
 (.n .e [104, 1605, 5424, 6275, 24838, 25502] .e) [104, 1605, 5424, 6379, 17048, 24838] .e)) [104, 1605, 5432, 6275, 17048, 24838]
 (.n
 (.n
 (.n .e [104, 1605, 5488, 6275, 17048, 24838] .e) [104, 1605, 5496, 6275, 17048, 24838] .e) [104, 1605, 6275, 7603, 17048, 24838]
 (.n
 (.n .e [104, 1613, 5424, 6275, 17048, 24838] .e) [104, 1637, 5424, 6275, 17048, 24838] .e))) [104, 1645, 5424, 6275, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [129, 1605, 5426, 10344, 17048, 24838] .e) [129, 1607, 5424, 10344, 17048, 24838]
 (.n .e [129, 6005, 7603, 10344, 17048, 24838] .e)) [130, 1605, 5424, 10344, 17048, 24839]
 (.n
 (.n .e [130, 1605, 5424, 10345, 17048, 24838] .e) [130, 1605, 5424, 14571, 17048, 26990] .e)) [131, 1605, 5424, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [131, 1605, 5424, 10344, 17048, 24839] .e) [131, 1605, 5424, 10344, 17048, 24966] .e) [131, 1605, 5424, 10344, 17048, 24967]
 (.n
 (.n .e [131, 1605, 5424, 10344, 17048, 26990] .e) [131, 1605, 5424, 10344, 17049, 24838] .e))))) [131, 1605, 5424, 10344, 17050, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [131, 1605, 5424, 10344, 17051, 24838] .e) [131, 1605, 5424, 10475, 17048, 24838]
 (.n .e [131, 1605, 5555, 10344, 17048, 24838] .e)) [131, 1607, 5424, 10344, 17048, 24838]
 (.n
 (.n .e [131, 1733, 5424, 10344, 17048, 24838] .e) [131, 1735, 5424, 10344, 17048, 24838] .e)) [131, 5424, 6005, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [136, 1605, 5424, 6275, 10344, 24854] .e) [136, 1605, 5424, 6275, 10360, 24838] .e) [136, 1605, 5424, 6275, 25502, 26990]
 (.n
 (.n .e [144, 1605, 5432, 6275, 10344, 24838] .e) [144, 1613, 5424, 6275, 10344, 24838] .e))) [144, 6005, 6275, 10344, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [152, 1605, 5424, 6275, 10344, 24838] .e) [152, 1605, 5424, 6275, 10344, 24990]
 (.n .e [152, 1605, 5424, 6275, 10360, 24838] .e)) [152, 1605, 5424, 6275, 10472, 24838]
 (.n
 (.n .e [152, 1605, 5424, 6275, 10488, 24838] .e) [152, 1605, 5424, 6275, 24838, 26990] .e)) [152, 1605, 5424, 6283, 10344, 24838]
 (.n
 (.n
 (.n .e [152, 1605, 5424, 6291, 10344, 24838] .e) [152, 1605, 5424, 6299, 10344, 24838] .e) [152, 1605, 5432, 6275, 10344, 24838]
 (.n
 (.n .e [152, 1605, 5552, 6275, 10344, 24838] .e) [152, 1605, 5560, 6275, 10344, 24838] .e)))) [152, 1605, 6005, 6275, 10344, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [152, 1757, 5424, 6275, 10344, 24838] .e) [201, 1605, 5424, 6275, 24838, 27384]
 (.n .e [201, 5424, 7879, 10344, 17048, 24838] .e)) [258, 1605, 5424, 6275, 10348, 17048]
 (.n
 (.n .e [258, 1605, 5424, 6279, 10344, 17048] .e) [258, 1605, 5424, 14571, 17048, 26990] .e)) [260, 1605, 5424, 6275, 10344, 17050]
 (.n
 (.n
 (.n .e [260, 1607, 5424, 6275, 10344, 17048] .e) [260, 5424, 6275, 10344, 18141, 25502] .e) [262, 1605, 5424, 6275, 10344, 17048]
 (.n
 (.n .e [262, 1605, 5424, 6275, 10344, 17310] .e) [262, 1605, 5424, 6275, 10606, 17048] .e))) [262, 1605, 5424, 6279, 10344, 17048]
 (.n
 (.n
 (.n
 (.n .e [262, 1605, 5424, 6531, 10344, 17048] .e) [262, 1605, 5424, 6535, 10344, 17048] .e) [262, 1605, 5424, 10344, 14571, 17048]
 (.n
 (.n .e [262, 1605, 5426, 6275, 10344, 17048] .e) [262, 1605, 5428, 6275, 10344, 17048] .e)) [262, 1605, 5430, 6275, 10344, 17048]
 (.n
 (.n
 (.n .e [262, 1607, 5424, 6275, 10344, 17048] .e) [262, 1861, 5424, 6275, 10344, 17048] .e) [262, 1863, 5424, 6275, 10344, 17048]
 (.n
 (.n .e [262, 5424, 6275, 10344, 17048, 18141] .e) [272, 1605, 6275, 10344, 17080, 24838] .e))))))

def T5aaa : T := .n T5aaaa [65, 5424, 6279, 10344, 17048, 24838] T5aaab

def T5aaba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [272, 6005, 6275, 10344, 18141, 24838] .e) [288, 1605, 6275, 10360, 17048, 24838]
 (.n .e [288, 1605, 6291, 10344, 17048, 24838] .e)) [288, 1605, 7603, 14571, 17048, 24838]
 (.n
 (.n .e [304, 1605, 6275, 10344, 17048, 24838] .e) [304, 1605, 6275, 10344, 17048, 24854] .e)) [304, 1605, 6275, 10344, 17048, 24870]
 (.n
 (.n
 (.n .e [304, 1605, 6275, 10344, 17048, 24886] .e) [304, 1605, 6275, 10344, 17080, 24838] .e) [304, 1605, 6275, 10344, 17304, 24838]
 (.n
 (.n .e [304, 1605, 6275, 10344, 17336, 24838] .e) [304, 1605, 6275, 10344, 18141, 24838] .e))) [304, 1605, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [304, 1605, 6275, 10600, 17048, 24838] .e) [304, 1605, 6275, 10616, 17048, 24838]
 (.n .e [304, 1605, 6275, 14571, 17048, 24838] .e)) [304, 1605, 6579, 10344, 17048, 24838]
 (.n
 (.n .e [304, 1909, 6275, 10344, 17048, 24838] .e) [356, 1605, 6275, 15736, 17048, 24838] .e)) [356, 5424, 6275, 10344, 17048, 26439]
 (.n
 (.n
 (.n .e [402, 1605, 5424, 10344, 17048, 31111] .e) [402, 1605, 6275, 10344, 22456, 24838] .e) [513, 6005, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [520, 1605, 5424, 6275, 25502, 26990] .e) [581, 5424, 6275, 10344, 17048, 24838] .e)))) [664, 1605, 5424, 6275, 10344, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [788, 5424, 6275, 10344, 18141, 24838] .e) [1028, 5424, 6275, 10344, 18141, 25502]
 (.n .e [1056, 1605, 7603, 14571, 17048, 24838] .e)) [1093, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1169, 6005, 6275, 10344, 17048, 24838] .e) [1328, 1605, 6275, 10344, 17048, 24838] .e)) [1605, 1607, 5424, 14571, 17048, 26990]
 (.n
 (.n
 (.n .e [1605, 1613, 5424, 6275, 25502, 26990] .e) [1605, 1637, 7603, 14571, 17048, 24838] .e) [1605, 2056, 5424, 6275, 25502, 26990]
 (.n
 (.n .e [1605, 2152, 5424, 6275, 17048, 24838] .e) [1605, 2179, 5424, 10344, 17048, 24838] .e))) [1605, 2338, 5424, 14571, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 4098, 5424, 14571, 17048, 26990] .e) [1605, 4193, 7603, 10344, 17048, 24838]
 (.n .e [1605, 4227, 5424, 10344, 17048, 24838] .e)) [1605, 4400, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 5426, 14571, 17048, 26990] .e) [1605, 5424, 5432, 6275, 25502, 26990] .e)) [1605, 5424, 6275, 6283, 25502, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8296, 17048, 24838] .e) [1605, 5424, 6275, 8330, 17048, 26990] .e) [1605, 5424, 6275, 8454, 10344, 17048]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16460, 25502] .e) [1605, 5424, 6275, 10344, 16536, 24838] .e))))) [1605, 5424, 6275, 10344, 16646, 17048]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24839]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24846] .e)) [1605, 5424, 6275, 10344, 17048, 24847]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24854] .e) [1605, 5424, 6275, 10344, 17048, 24855] .e)) [1605, 5424, 6275, 10344, 17048, 24862]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24870] .e) [1605, 5424, 6275, 10344, 17048, 24871] .e) [1605, 5424, 6275, 10344, 17048, 24878]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24886] .e) [1605, 5424, 6275, 10344, 17048, 24902] .e))) [1605, 5424, 6275, 10344, 17048, 24903]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24910] .e) [1605, 5424, 6275, 10344, 17048, 24918]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24934] .e)) [1605, 5424, 6275, 10344, 17048, 24942]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24966] .e) [1605, 5424, 6275, 10344, 17048, 24967] .e)) [1605, 5424, 6275, 10344, 17048, 24974]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24982] .e) [1605, 5424, 6275, 10344, 17048, 24990] .e) [1605, 5424, 6275, 10344, 17048, 24998]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 25030] .e) [1605, 5424, 6275, 10344, 17048, 25039] .e)))) [1605, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17049, 24839] .e) [1605, 5424, 6275, 10344, 17049, 24846]
 (.n .e [1605, 5424, 6275, 10344, 17049, 24854] .e)) [1605, 5424, 6275, 10344, 17049, 24870]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17049, 24902] .e) [1605, 5424, 6275, 10344, 17049, 24966] .e)) [1605, 5424, 6275, 10344, 17049, 24967]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17050, 24838] .e) [1605, 5424, 6275, 10344, 17050, 24839] .e) [1605, 5424, 6275, 10344, 17050, 24846]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17050, 24854] .e) [1605, 5424, 6275, 10344, 17050, 24870] .e))) [1605, 5424, 6275, 10344, 17050, 24902]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17050, 24966] .e) [1605, 5424, 6275, 10344, 17050, 26886] .e) [1605, 5424, 6275, 10344, 17050, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17051, 24838] .e) [1605, 5424, 6275, 10344, 17051, 24839] .e)) [1605, 5424, 6275, 10344, 17051, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17052, 24838] .e) [1605, 5424, 6275, 10344, 17052, 24839] .e) [1605, 5424, 6275, 10344, 17052, 24846]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17052, 24854] .e) [1605, 5424, 6275, 10344, 17052, 24870] .e))))))

def T5aabb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17052, 24966] .e) [1605, 5424, 6275, 10344, 17053, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17053, 24839] .e)) [1605, 5424, 6275, 10344, 17054, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17054, 26990] .e) [1605, 5424, 6275, 10344, 17080, 24838] .e)) [1605, 5424, 6275, 10344, 17080, 24839]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17080, 24846] .e) [1605, 5424, 6275, 10344, 17080, 24854] .e) [1605, 5424, 6275, 10344, 17080, 24870]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17080, 24878] .e) [1605, 5424, 6275, 10344, 17080, 24886] .e))) [1605, 5424, 6275, 10344, 17080, 24902]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17080, 24966] .e) [1605, 5424, 6275, 10344, 17081, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17082, 24838] .e)) [1605, 5424, 6275, 10344, 17084, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 24838] .e) [1605, 5424, 6275, 10344, 17112, 24839] .e)) [1605, 5424, 6275, 10344, 17112, 24846]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 24854] .e) [1605, 5424, 6275, 10344, 17112, 24870] .e) [1605, 5424, 6275, 10344, 17112, 24902]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 24910] .e) [1605, 5424, 6275, 10344, 17112, 24966] .e)))) [1605, 5424, 6275, 10344, 17113, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17113, 24903] .e) [1605, 5424, 6275, 10344, 17114, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17116, 24838] .e)) [1605, 5424, 6275, 10344, 17116, 24902]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17117, 24838] .e) [1605, 5424, 6275, 10344, 17144, 24838] .e)) [1605, 5424, 6275, 10344, 17144, 24934]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17304, 24838] .e) [1605, 5424, 6275, 10344, 17304, 24839] .e) [1605, 5424, 6275, 10344, 17304, 24846]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17304, 24854] .e) [1605, 5424, 6275, 10344, 17304, 24870] .e))) [1605, 5424, 6275, 10344, 17304, 24902]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17304, 24966] .e) [1605, 5424, 6275, 10344, 17305, 24838] .e) [1605, 5424, 6275, 10344, 17306, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17306, 26990] .e) [1605, 5424, 6275, 10344, 17306, 31111] .e)) [1605, 5424, 6275, 10344, 17308, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17310, 24838] .e) [1605, 5424, 6275, 10344, 17336, 24838] .e) [1605, 5424, 6275, 10344, 17336, 24870]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17368, 24838] .e) [1605, 5424, 6275, 10344, 17404, 24838] .e))))) [1605, 5424, 6275, 10344, 18072, 24854]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 18141, 24854] .e) [1605, 5424, 6275, 10344, 18141, 24862]
 (.n .e [1605, 5424, 6275, 10344, 18141, 24886] .e)) [1605, 5424, 6275, 10344, 18141, 24982]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 22456, 24982] .e) [1605, 5424, 6275, 10345, 17048, 24838] .e)) [1605, 5424, 6275, 10345, 17048, 24839]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17048, 24846] .e) [1605, 5424, 6275, 10345, 17048, 24854] .e) [1605, 5424, 6275, 10345, 17048, 24870]
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17048, 24902] .e) [1605, 5424, 6275, 10345, 17048, 24903] .e))) [1605, 5424, 6275, 10345, 17048, 24966]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17049, 24838] .e) [1605, 5424, 6275, 10345, 17049, 24839]
 (.n .e [1605, 5424, 6275, 10345, 17050, 24838] .e)) [1605, 5424, 6275, 10345, 17052, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17080, 24838] .e) [1605, 5424, 6275, 10345, 17112, 24838] .e)) [1605, 5424, 6275, 10345, 17113, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17304, 24838] .e) [1605, 5424, 6275, 10346, 17048, 24838] .e) [1605, 5424, 6275, 10346, 17048, 24839]
 (.n
 (.n .e [1605, 5424, 6275, 10346, 17048, 24846] .e) [1605, 5424, 6275, 10346, 17048, 24854] .e)))) [1605, 5424, 6275, 10346, 17048, 24870]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10346, 17048, 24902] .e) [1605, 5424, 6275, 10346, 17048, 24966]
 (.n .e [1605, 5424, 6275, 10346, 17049, 24838] .e)) [1605, 5424, 6275, 10346, 17050, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10346, 17050, 26990] .e) [1605, 5424, 6275, 10346, 17052, 24838] .e)) [1605, 5424, 6275, 10346, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10346, 17112, 24838] .e) [1605, 5424, 6275, 10346, 17304, 24838] .e) [1605, 5424, 6275, 10347, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10347, 17048, 24839] .e) [1605, 5424, 6275, 10347, 17051, 24838] .e))) [1605, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17048, 24839] .e) [1605, 5424, 6275, 10348, 17048, 24846] .e) [1605, 5424, 6275, 10348, 17048, 24854]
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17048, 24870] .e) [1605, 5424, 6275, 10348, 17048, 24902] .e)) [1605, 5424, 6275, 10348, 17048, 24966]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17048, 25350] .e) [1605, 5424, 6275, 10348, 17048, 25502] .e) [1605, 5424, 6275, 10348, 17049, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17050, 24838] .e) [1605, 5424, 6275, 10348, 17052, 24838] .e))))))

def T5aab : T := .n T5aaba [1605, 5424, 6275, 10344, 17052, 24902] T5aabb

def T5aa : T := .n T5aaa [272, 1637, 6275, 10344, 17048, 24838] T5aab

def T5abaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17080, 24838] .e) [1605, 5424, 6275, 10348, 17112, 24838]
 (.n .e [1605, 5424, 6275, 10348, 17116, 24838] .e)) [1605, 5424, 6275, 10348, 17304, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10348, 18141, 25502] .e) [1605, 5424, 6275, 10348, 22456, 25502] .e)) [1605, 5424, 6275, 10348, 23195, 25502]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10349, 17048, 24838] .e) [1605, 5424, 6275, 10349, 17048, 24839] .e) [1605, 5424, 6275, 10349, 17048, 25502]
 (.n
 (.n .e [1605, 5424, 6275, 10349, 17053, 24838] .e) [1605, 5424, 6275, 10350, 17048, 24838] .e))) [1605, 5424, 6275, 10350, 17048, 25502]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10350, 17054, 24838] .e) [1605, 5424, 6275, 10360, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10360, 17048, 24839] .e)) [1605, 5424, 6275, 10360, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6275, 10360, 17048, 24854] .e) [1605, 5424, 6275, 10360, 17048, 24862] .e)) [1605, 5424, 6275, 10360, 17048, 24870]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10360, 17048, 24886] .e) [1605, 5424, 6275, 10360, 17048, 24902] .e) [1605, 5424, 6275, 10360, 17048, 24966]
 (.n
 (.n .e [1605, 5424, 6275, 10360, 17049, 24838] .e) [1605, 5424, 6275, 10360, 17050, 24838] .e)))) [1605, 5424, 6275, 10360, 17052, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10360, 17080, 24838] .e) [1605, 5424, 6275, 10360, 17112, 24838]
 (.n .e [1605, 5424, 6275, 10360, 17304, 24838] .e)) [1605, 5424, 6275, 10360, 18072, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10360, 18141, 24838] .e) [1605, 5424, 6275, 10360, 18141, 24854] .e)) [1605, 5424, 6275, 10361, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10362, 17048, 24838] .e) [1605, 5424, 6275, 10364, 17048, 24838] .e) [1605, 5424, 6275, 10472, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10472, 17048, 24839] .e) [1605, 5424, 6275, 10472, 17048, 24846] .e))) [1605, 5424, 6275, 10472, 17048, 24854]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10472, 17048, 24870] .e) [1605, 5424, 6275, 10472, 17048, 24902]
 (.n .e [1605, 5424, 6275, 10472, 17048, 24966] .e)) [1605, 5424, 6275, 10472, 17048, 24974]
 (.n
 (.n .e [1605, 5424, 6275, 10472, 17049, 24838] .e) [1605, 5424, 6275, 10472, 17050, 24838] .e)) [1605, 5424, 6275, 10472, 17052, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10472, 17080, 24838] .e) [1605, 5424, 6275, 10472, 17112, 24838] .e) [1605, 5424, 6275, 10472, 17304, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10473, 17048, 24838] .e) [1605, 5424, 6275, 10473, 17048, 24967] .e))))) [1605, 5424, 6275, 10473, 17049, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10474, 17048, 24838] .e) [1605, 5424, 6275, 10474, 17048, 24966]
 (.n .e [1605, 5424, 6275, 10474, 17050, 24838] .e)) [1605, 5424, 6275, 10475, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10476, 17048, 24838] .e) [1605, 5424, 6275, 10488, 17048, 24838] .e)) [1605, 5424, 6275, 10488, 17048, 24982]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10488, 18141, 24838] .e) [1605, 5424, 6275, 10488, 22456, 24838] .e) [1605, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10600, 17048, 24839] .e) [1605, 5424, 6275, 10600, 17048, 24846] .e))) [1605, 5424, 6275, 10600, 17048, 24854]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10600, 17048, 24870] .e) [1605, 5424, 6275, 10600, 17048, 24902]
 (.n .e [1605, 5424, 6275, 10600, 17048, 24966] .e)) [1605, 5424, 6275, 10600, 17049, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10600, 17050, 24838] .e) [1605, 5424, 6275, 10600, 17052, 24838] .e)) [1605, 5424, 6275, 10600, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10600, 17112, 24838] .e) [1605, 5424, 6275, 10600, 17304, 24838] .e) [1605, 5424, 6275, 10600, 17336, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10601, 17048, 24838] .e) [1605, 5424, 6275, 10602, 17048, 24838] .e)))) [1605, 5424, 6275, 10602, 17306, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10604, 17048, 24838] .e) [1605, 5424, 6275, 10604, 17048, 25502]
 (.n .e [1605, 5424, 6275, 10604, 17048, 26439] .e)) [1605, 5424, 6275, 10604, 17308, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10606, 17048, 24838] .e) [1605, 5424, 6275, 10616, 17048, 24838] .e)) [1605, 5424, 6275, 10616, 17048, 24854]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10616, 17304, 24838] .e) [1605, 5424, 6275, 10616, 18141, 24838] .e) [1605, 5424, 6275, 10728, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10746, 17048, 24838] .e) [1605, 5424, 6275, 11885, 17050, 26990] .e))) [1605, 5424, 6275, 14440, 17048, 24870]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 14440, 17080, 24838] .e) [1605, 5424, 6275, 14571, 17048, 24870] .e) [1605, 5424, 6275, 14571, 17048, 24878]
 (.n
 (.n .e [1605, 5424, 6275, 14571, 17048, 24886] .e) [1605, 5424, 6275, 14571, 17048, 24934] .e)) [1605, 5424, 6275, 14571, 17050, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 14571, 17080, 24838] .e) [1605, 5424, 6275, 14571, 17080, 24870] .e) [1605, 5424, 6275, 14571, 17144, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 14571, 17336, 24838] .e) [1605, 5424, 6275, 15736, 17048, 24934] .e))))))

def T5abab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 15736, 17144, 24838] .e) [1605, 5424, 6279, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6279, 10344, 17048, 24839] .e)) [1605, 5424, 6279, 10344, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17048, 24854] .e) [1605, 5424, 6279, 10344, 17048, 24870] .e)) [1605, 5424, 6279, 10344, 17048, 24902]
 (.n
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17048, 24966] .e) [1605, 5424, 6279, 10344, 17048, 25350] .e) [1605, 5424, 6279, 10344, 17048, 25502]
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17049, 24838] .e) [1605, 5424, 6279, 10344, 17050, 24838] .e))) [1605, 5424, 6279, 10344, 17052, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17052, 25502] .e) [1605, 5424, 6279, 10344, 17053, 24838]
 (.n .e [1605, 5424, 6279, 10344, 17054, 24838] .e)) [1605, 5424, 6279, 10344, 17080, 24838]
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17112, 24838] .e) [1605, 5424, 6279, 10344, 17304, 24838] .e)) [1605, 5424, 6279, 10344, 18141, 25502]
 (.n
 (.n
 (.n .e [1605, 5424, 6279, 10344, 22456, 25502] .e) [1605, 5424, 6279, 10344, 23195, 25502] .e) [1605, 5424, 6279, 10344, 23199, 25502]
 (.n
 (.n .e [1605, 5424, 6279, 10345, 17048, 24838] .e) [1605, 5424, 6279, 10346, 17048, 24838] .e)))) [1605, 5424, 6279, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6279, 10348, 17048, 25502] .e) [1605, 5424, 6279, 10348, 17052, 24838]
 (.n .e [1605, 5424, 6279, 10349, 17048, 24838] .e)) [1605, 5424, 6279, 10350, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6279, 10360, 17048, 24838] .e) [1605, 5424, 6279, 10472, 17048, 24838] .e)) [1605, 5424, 6279, 10600, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17048, 24838] .e) [1605, 5424, 6283, 10344, 17048, 24839] .e) [1605, 5424, 6283, 10344, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17048, 24854] .e) [1605, 5424, 6283, 10344, 17048, 24870] .e))) [1605, 5424, 6283, 10344, 17048, 24902]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17048, 24966] .e) [1605, 5424, 6283, 10344, 17048, 24974] .e) [1605, 5424, 6283, 10344, 17049, 24838]
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17050, 24838] .e) [1605, 5424, 6283, 10344, 17052, 24838] .e)) [1605, 5424, 6283, 10344, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17112, 24838] .e) [1605, 5424, 6283, 10344, 17304, 24838] .e) [1605, 5424, 6283, 10344, 24838, 25240]
 (.n
 (.n .e [1605, 5424, 6283, 10344, 24838, 25502] .e) [1605, 5424, 6283, 10344, 24846, 25502] .e))))) [1605, 5424, 6283, 10344, 25502, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 10344, 25502, 30006] .e) [1605, 5424, 6283, 10344, 25502, 31111]
 (.n .e [1605, 5424, 6283, 10344, 25502, 31119] .e)) [1605, 5424, 6283, 10345, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6283, 10346, 17048, 24838] .e) [1605, 5424, 6283, 10348, 17048, 24838] .e)) [1605, 5424, 6283, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 10472, 17048, 24838] .e) [1605, 5424, 6283, 10600, 17048, 24838] .e) [1605, 5424, 6283, 17048, 24838, 26728]
 (.n
 (.n .e [1605, 5424, 6283, 17048, 24838, 26990] .e) [1605, 5424, 6283, 17048, 24846, 26990] .e))) [1605, 5424, 6283, 17048, 25502, 26990]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 17048, 26439, 26990] .e) [1605, 5424, 6283, 17048, 26990, 30006]
 (.n .e [1605, 5424, 6283, 24838, 25502, 26990] .e)) [1605, 5424, 6283, 25502, 26990]
 (.n
 (.n .e [1605, 5424, 6287, 10344, 17048, 24838] .e) [1605, 5424, 6291, 10344, 17048, 24838] .e)) [1605, 5424, 6291, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [1605, 5424, 6291, 10344, 17048, 24846] .e) [1605, 5424, 6291, 10344, 17048, 24854] .e) [1605, 5424, 6291, 10344, 17048, 24870]
 (.n
 (.n .e [1605, 5424, 6291, 10344, 17048, 24902] .e) [1605, 5424, 6291, 10344, 17048, 24966] .e)))) [1605, 5424, 6291, 10344, 17048, 24982]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6291, 10344, 17049, 24838] .e) [1605, 5424, 6291, 10344, 17050, 24838]
 (.n .e [1605, 5424, 6291, 10344, 17052, 24838] .e)) [1605, 5424, 6291, 10344, 17080, 24838]
 (.n
 (.n .e [1605, 5424, 6291, 10344, 17112, 24838] .e) [1605, 5424, 6291, 10344, 17304, 24838] .e)) [1605, 5424, 6291, 10344, 18072, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6291, 10344, 18141, 24838] .e) [1605, 5424, 6291, 10344, 18141, 24854] .e) [1605, 5424, 6291, 10345, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6291, 10346, 17048, 24838] .e) [1605, 5424, 6291, 10348, 17048, 24838] .e))) [1605, 5424, 6291, 10360, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6291, 10360, 17048, 24854] .e) [1605, 5424, 6291, 10360, 18141, 24838] .e) [1605, 5424, 6291, 10472, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6291, 10488, 17048, 24838] .e) [1605, 5424, 6291, 10600, 17048, 24838] .e)) [1605, 5424, 6295, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6299, 10344, 17048, 24838] .e) [1605, 5424, 6299, 10344, 17048, 24862] .e) [1605, 5424, 6299, 10344, 18141, 24838]
 (.n
 (.n .e [1605, 5424, 6299, 10344, 24838, 25502] .e) [1605, 5424, 6299, 10360, 17048, 24838] .e))))))

def T5aba : T := .n T5abaa [1605, 5424, 6275, 15736, 17050, 26990] T5abab

def T5abba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17048, 24838] .e) [1605, 5424, 6307, 10344, 17048, 24839]
 (.n .e [1605, 5424, 6307, 10344, 17048, 24846] .e)) [1605, 5424, 6307, 10344, 17048, 24854]
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17048, 24870] .e) [1605, 5424, 6307, 10344, 17048, 24902] .e)) [1605, 5424, 6307, 10344, 17048, 24966]
 (.n
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17049, 24838] .e) [1605, 5424, 6307, 10344, 17050, 24838] .e) [1605, 5424, 6307, 10344, 17052, 24838]
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17080, 24838] .e) [1605, 5424, 6307, 10344, 17080, 24870] .e))) [1605, 5424, 6307, 10344, 17112, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17304, 24838] .e) [1605, 5424, 6307, 10345, 17048, 24838]
 (.n .e [1605, 5424, 6307, 10346, 17048, 24838] .e)) [1605, 5424, 6307, 10348, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6307, 10360, 17048, 24838] .e) [1605, 5424, 6307, 10472, 17048, 24838] .e)) [1605, 5424, 6307, 10600, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6307, 14571, 17048, 24870] .e) [1605, 5424, 6307, 14571, 17080, 24838] .e) [1605, 5424, 6311, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6315, 10344, 17048, 24838] .e) [1605, 5424, 6315, 10344, 17048, 24878] .e)))) [1605, 5424, 6315, 10344, 17080, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6315, 10344, 24838, 25502] .e) [1605, 5424, 6315, 17048, 24838, 26990]
 (.n .e [1605, 5424, 6323, 10344, 17048, 24838] .e)) [1605, 5424, 6323, 10344, 17048, 24886]
 (.n
 (.n .e [1605, 5424, 6323, 10344, 17080, 24838] .e) [1605, 5424, 6323, 10344, 18141, 24838] .e)) [1605, 5424, 6323, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 24838] .e) [1605, 5424, 6339, 10344, 17048, 24839] .e) [1605, 5424, 6339, 10344, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 24854] .e) [1605, 5424, 6339, 10344, 17048, 24870] .e))) [1605, 5424, 6339, 10344, 17048, 24902]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 24903] .e) [1605, 5424, 6339, 10344, 17048, 24966]
 (.n .e [1605, 5424, 6339, 10344, 17049, 24838] .e)) [1605, 5424, 6339, 10344, 17050, 24838]
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17052, 24838] .e) [1605, 5424, 6339, 10344, 17080, 24838] .e)) [1605, 5424, 6339, 10344, 17112, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17112, 24902] .e) [1605, 5424, 6339, 10344, 17113, 24838] .e) [1605, 5424, 6339, 10344, 17304, 24838]
 (.n
 (.n .e [1605, 5424, 6339, 10345, 17048, 24838] .e) [1605, 5424, 6339, 10346, 17048, 24838] .e))))) [1605, 5424, 6339, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6339, 10360, 17048, 24838] .e) [1605, 5424, 6339, 10472, 17048, 24838]
 (.n .e [1605, 5424, 6339, 10600, 17048, 24838] .e)) [1605, 5424, 6343, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6343, 10344, 17048, 24902] .e) [1605, 5424, 6343, 10344, 17048, 25502] .e)) [1605, 5424, 6343, 10344, 17116, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6343, 10348, 17048, 24838] .e) [1605, 5424, 6347, 10344, 17048, 24838] .e) [1605, 5424, 6347, 10344, 17048, 24910]
 (.n
 (.n .e [1605, 5424, 6347, 10344, 17112, 24838] .e) [1605, 5424, 6347, 10344, 24838, 25502] .e))) [1605, 5424, 6347, 17048, 24838, 26990]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6347, 17048, 24838, 27384] .e) [1605, 5424, 6347, 18141, 24838, 27384]
 (.n .e [1605, 5424, 6355, 10344, 17048, 24838] .e)) [1605, 5424, 6371, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6371, 10344, 17048, 24934] .e) [1605, 5424, 6371, 10344, 17144, 24838] .e)) [1605, 5424, 6379, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17048, 24838] .e) [1605, 5424, 6531, 10344, 17048, 24839] .e) [1605, 5424, 6531, 10344, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17048, 24854] .e) [1605, 5424, 6531, 10344, 17048, 24870] .e)))) [1605, 5424, 6531, 10344, 17048, 24902]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17048, 24966] .e) [1605, 5424, 6531, 10344, 17049, 24838]
 (.n .e [1605, 5424, 6531, 10344, 17050, 24838] .e)) [1605, 5424, 6531, 10344, 17052, 24838]
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17080, 24838] .e) [1605, 5424, 6531, 10344, 17112, 24838] .e)) [1605, 5424, 6531, 10344, 17304, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17306, 24838] .e) [1605, 5424, 6531, 10345, 17048, 24838] .e) [1605, 5424, 6531, 10346, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6531, 10348, 17048, 24838] .e) [1605, 5424, 6531, 10360, 17048, 24838] .e))) [1605, 5424, 6531, 10472, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6531, 10600, 17048, 24838] .e) [1605, 5424, 6531, 10600, 17304, 24838] .e) [1605, 5424, 6531, 10602, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6535, 10344, 17048, 24838] .e) [1605, 5424, 6535, 10344, 17048, 25502] .e)) [1605, 5424, 6535, 10344, 17048, 26439]
 (.n
 (.n
 (.n .e [1605, 5424, 6535, 10344, 17308, 24838] .e) [1605, 5424, 6535, 10604, 17048, 24838] .e) [1605, 5424, 6539, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6547, 10344, 17048, 24838] .e) [1605, 5424, 6547, 10344, 17048, 24854] .e))))))

def T5abbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6547, 10344, 18141, 24838] .e) [1605, 5424, 6547, 10616, 17048, 24838]
 (.n .e [1605, 5424, 6563, 10344, 17048, 24838] .e)) [1605, 5424, 6563, 10344, 17048, 24870]
 (.n
 (.n .e [1605, 5424, 6563, 10344, 17336, 24838] .e) [1605, 5424, 6563, 10600, 17048, 24838] .e)) [1605, 5424, 6579, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6595, 10344, 17048, 24838] .e) [1605, 5424, 6631, 10344, 17048, 24838] .e) [1605, 5424, 7299, 10344, 17048, 24839]
 (.n
 (.n .e [1605, 5424, 7299, 10344, 17049, 24838] .e) [1605, 5424, 7299, 10345, 17048, 24838] .e))) [1605, 5424, 7603, 10344, 17048, 24839]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 7603, 10344, 17048, 24903] .e) [1605, 5424, 7603, 10344, 17048, 24967]
 (.n .e [1605, 5424, 7603, 10344, 17049, 24838] .e)) [1605, 5424, 7603, 10344, 17049, 24839]
 (.n
 (.n .e [1605, 5424, 7603, 10344, 17051, 24838] .e) [1605, 5424, 7603, 10344, 17053, 24838] .e)) [1605, 5424, 7603, 10344, 17113, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 7603, 10344, 17306, 31111] .e) [1605, 5424, 7603, 10345, 17048, 24838] .e) [1605, 5424, 7603, 10345, 17048, 24839]
 (.n
 (.n .e [1605, 5424, 7603, 10345, 17049, 24838] .e) [1605, 5424, 7603, 10347, 17048, 24838] .e)))) [1605, 5424, 7603, 10349, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 7603, 10473, 17048, 24838] .e) [1605, 5424, 7603, 14571, 17048, 24870]
 (.n .e [1605, 5424, 7603, 14571, 17080, 24838] .e)) [1605, 5424, 7879, 10344, 17048, 24967]
 (.n
 (.n .e [1605, 5424, 7879, 10473, 17048, 24838] .e) [1605, 5424, 7879, 14571, 17048, 24870] .e)) [1605, 5424, 7879, 14571, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 10344, 14467, 17050, 24838] .e) [1605, 5424, 10344, 14571, 17050, 24838] .e) [1605, 5424, 10344, 14571, 17050, 26990]
 (.n
 (.n .e [1605, 5424, 10344, 14571, 17051, 24838] .e) [1605, 5424, 10344, 14571, 17054, 24838] .e))) [1605, 5424, 10344, 14571, 17306, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 10346, 14571, 17050, 24838] .e) [1605, 5424, 11885, 14571, 17050, 24838] .e) [1605, 5424, 14571, 16386, 17048, 26990]
 (.n
 (.n .e [1605, 5424, 14571, 17048, 17050, 26990] .e) [1605, 5424, 14571, 17048, 23195, 24870] .e)) [1605, 5424, 14571, 17050, 24838, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 14571, 17050, 24838, 27384] .e) [1605, 5424, 14571, 17050, 24838, 27386] .e) [1605, 5424, 14571, 17050, 26990]
 (.n
 (.n .e [1605, 5424, 14571, 17080, 23195, 24838] .e) [1605, 5424, 14571, 17080, 23227, 24838] .e))))) [1605, 5424, 14571, 23195, 25502, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17048, 24838] .e) [1605, 5425, 6275, 10344, 17048, 24839]
 (.n .e [1605, 5425, 6275, 10344, 17048, 24846] .e)) [1605, 5425, 6275, 10344, 17048, 24854]
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17048, 24870] .e) [1605, 5425, 6275, 10344, 17048, 24902] .e)) [1605, 5425, 6275, 10344, 17048, 24966]
 (.n
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17049, 24838] .e) [1605, 5425, 6275, 10344, 17049, 24839] .e) [1605, 5425, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17052, 24838] .e) [1605, 5425, 6275, 10344, 17080, 24838] .e))) [1605, 5425, 6275, 10344, 17112, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17304, 24838] .e) [1605, 5425, 6275, 10345, 17048, 24838]
 (.n .e [1605, 5425, 6275, 10345, 17048, 24839] .e)) [1605, 5425, 6275, 10345, 17049, 24838]
 (.n
 (.n .e [1605, 5425, 6275, 10346, 17048, 24838] .e) [1605, 5425, 6275, 10348, 17048, 24838] .e)) [1605, 5425, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5425, 6275, 10472, 17048, 24838] .e) [1605, 5425, 6275, 10600, 17048, 24838] .e) [1605, 5425, 6279, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5425, 6283, 10344, 17048, 24838] .e) [1605, 5425, 6291, 10344, 17048, 24838] .e)))) [1605, 5425, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5425, 6339, 10344, 17048, 24838] .e) [1605, 5425, 6531, 10344, 17048, 24838]
 (.n .e [1605, 5425, 7603, 10344, 17048, 24839] .e)) [1605, 5425, 7603, 10344, 17049, 24838]
 (.n
 (.n .e [1605, 5425, 7603, 10345, 17048, 24838] .e) [1605, 5426, 6275, 10344, 17048, 24838] .e)) [1605, 5426, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17048, 24846] .e) [1605, 5426, 6275, 10344, 17048, 24854] .e) [1605, 5426, 6275, 10344, 17048, 24870]
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17048, 24902] .e) [1605, 5426, 6275, 10344, 17048, 24966] .e))) [1605, 5426, 6275, 10344, 17048, 26886]
 (.n
 (.n
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17048, 26990] .e) [1605, 5426, 6275, 10344, 17049, 24838] .e) [1605, 5426, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17050, 26990] .e) [1605, 5426, 6275, 10344, 17052, 24838] .e)) [1605, 5426, 6275, 10344, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17112, 24838] .e) [1605, 5426, 6275, 10344, 17304, 24838] .e) [1605, 5426, 6275, 10344, 17306, 24838]
 (.n
 (.n .e [1605, 5426, 6275, 10345, 17048, 24838] .e) [1605, 5426, 6275, 10346, 17048, 24838] .e))))))

def T5abb : T := .n T5abba [1605, 5424, 6547, 10344, 17304, 24838] T5abbb

def T5ab : T := .n T5aba [1605, 5424, 6299, 17048, 24838, 26990] T5abb

def T5a : T := .n T5aa [1605, 5424, 6275, 10348, 17052, 25502] T5ab

def T5baaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5426, 6275, 10346, 17050, 24838] .e) [1605, 5426, 6275, 10348, 17048, 24838]
 (.n .e [1605, 5426, 6275, 10360, 17048, 24838] .e)) [1605, 5426, 6275, 10472, 17048, 24838]
 (.n
 (.n .e [1605, 5426, 6275, 10600, 17048, 24838] .e) [1605, 5426, 6275, 10602, 17048, 24838] .e)) [1605, 5426, 6275, 11885, 17048, 26990]
 (.n
 (.n
 (.n .e [1605, 5426, 6275, 14571, 17048, 26990] .e) [1605, 5426, 6275, 15736, 17048, 26990] .e) [1605, 5426, 6275, 15738, 17048, 26990]
 (.n
 (.n .e [1605, 5426, 6279, 10344, 17048, 24838] .e) [1605, 5426, 6283, 10344, 17048, 24838] .e))) [1605, 5426, 6291, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5426, 6307, 10344, 17048, 24838] .e) [1605, 5426, 6339, 10344, 17048, 24838]
 (.n .e [1605, 5426, 6531, 10344, 17048, 24838] .e)) [1605, 5426, 10344, 14467, 17048, 24838]
 (.n
 (.n .e [1605, 5426, 10344, 14571, 17048, 24838] .e) [1605, 5426, 10344, 14571, 17048, 26990] .e)) [1605, 5426, 10344, 14571, 17050, 24838]
 (.n
 (.n
 (.n .e [1605, 5426, 10346, 14571, 17048, 24838] .e) [1605, 5426, 11885, 14571, 17048, 24838] .e) [1605, 5426, 14571, 17048, 24838, 26990]
 (.n
 (.n .e [1605, 5426, 14571, 17048, 24838, 27384] .e) [1605, 5426, 14571, 17048, 26990] .e)))) [1605, 5427, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5427, 6275, 10344, 17048, 24839] .e) [1605, 5427, 6275, 10344, 17048, 26990]
 (.n .e [1605, 5427, 6275, 10344, 17051, 24838] .e)) [1605, 5427, 6275, 10347, 17048, 24838]
 (.n
 (.n .e [1605, 5427, 10344, 14571, 17048, 24838] .e) [1605, 5428, 6275, 10344, 17048, 24838] .e)) [1605, 5428, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17048, 24846] .e) [1605, 5428, 6275, 10344, 17048, 24854] .e) [1605, 5428, 6275, 10344, 17048, 24870]
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17048, 24902] .e) [1605, 5428, 6275, 10344, 17048, 24966] .e))) [1605, 5428, 6275, 10344, 17048, 25350]
 (.n
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17048, 25502] .e) [1605, 5428, 6275, 10344, 17049, 24838]
 (.n .e [1605, 5428, 6275, 10344, 17050, 24838] .e)) [1605, 5428, 6275, 10344, 17052, 24838]
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17052, 25502] .e) [1605, 5428, 6275, 10344, 17080, 24838] .e)) [1605, 5428, 6275, 10344, 17112, 24838]
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17304, 24838] .e) [1605, 5428, 6275, 10344, 17308, 24838] .e) [1605, 5428, 6275, 10344, 18141, 25502]
 (.n
 (.n .e [1605, 5428, 6275, 10344, 22456, 25502] .e) [1605, 5428, 6275, 10344, 22460, 25502] .e))))) [1605, 5428, 6275, 10344, 23195, 25502]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 10345, 17048, 24838] .e) [1605, 5428, 6275, 10346, 17048, 24838]
 (.n .e [1605, 5428, 6275, 10348, 17048, 24838] .e)) [1605, 5428, 6275, 10348, 17048, 25502]
 (.n
 (.n .e [1605, 5428, 6275, 10348, 17052, 24838] .e) [1605, 5428, 6275, 10360, 17048, 24838] .e)) [1605, 5428, 6275, 10472, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 10600, 17048, 24838] .e) [1605, 5428, 6275, 10604, 17048, 24838] .e) [1605, 5428, 6279, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5428, 6279, 10344, 17048, 25502] .e) [1605, 5428, 6279, 10344, 17052, 24838] .e))) [1605, 5428, 6279, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5428, 6283, 10344, 17048, 24838] .e) [1605, 5428, 6291, 10344, 17048, 24838]
 (.n .e [1605, 5428, 6307, 10344, 17048, 24838] .e)) [1605, 5428, 6339, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5428, 6531, 10344, 17048, 24838] .e) [1605, 5428, 6535, 10344, 17048, 24838] .e)) [1605, 5429, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5429, 6275, 10344, 17048, 24839] .e) [1605, 5429, 6275, 10344, 17048, 25502] .e) [1605, 5429, 6275, 10344, 17053, 24838]
 (.n
 (.n .e [1605, 5429, 6275, 10349, 17048, 24838] .e) [1605, 5429, 6279, 10344, 17048, 24838] .e)))) [1605, 5430, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5430, 6275, 10344, 17048, 25502] .e) [1605, 5430, 6275, 10344, 17048, 26990]
 (.n .e [1605, 5430, 6275, 10344, 17054, 24838] .e)) [1605, 5430, 6275, 10350, 17048, 24838]
 (.n
 (.n .e [1605, 5430, 6279, 10344, 17048, 24838] .e) [1605, 5430, 10344, 14571, 17048, 24838] .e)) [1605, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17048, 24839] .e) [1605, 5432, 6275, 10344, 17048, 24846] .e) [1605, 5432, 6275, 10344, 17048, 24854]
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17048, 24862] .e) [1605, 5432, 6275, 10344, 17048, 24870] .e))) [1605, 5432, 6275, 10344, 17048, 24878]
 (.n
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17048, 24902] .e) [1605, 5432, 6275, 10344, 17048, 24966] .e) [1605, 5432, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17050, 24838] .e) [1605, 5432, 6275, 10344, 17052, 24838] .e)) [1605, 5432, 6275, 10344, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17112, 24838] .e) [1605, 5432, 6275, 10344, 17304, 24838] .e) [1605, 5432, 6275, 10344, 24838, 25240]
 (.n
 (.n .e [1605, 5432, 6275, 10344, 24838, 25502] .e) [1605, 5432, 6275, 10344, 24846, 25502] .e))))))

def T5baab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 10344, 25502, 30006] .e) [1605, 5432, 6275, 10344, 25502, 30014]
 (.n .e [1605, 5432, 6275, 10344, 25502, 31111] .e)) [1605, 5432, 6275, 10345, 17048, 24838]
 (.n
 (.n .e [1605, 5432, 6275, 10346, 17048, 24838] .e) [1605, 5432, 6275, 10348, 17048, 24838] .e)) [1605, 5432, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 10472, 17048, 24838] .e) [1605, 5432, 6275, 10600, 17048, 24838] .e) [1605, 5432, 6275, 17048, 24838, 26728]
 (.n
 (.n .e [1605, 5432, 6275, 17048, 24838, 26990] .e) [1605, 5432, 6275, 17048, 24846, 26990] .e))) [1605, 5432, 6275, 17048, 25502, 26990]
 (.n
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 17048, 26439, 26990] .e) [1605, 5432, 6275, 17048, 26990, 30006]
 (.n .e [1605, 5432, 6275, 17048, 26990, 30014] .e)) [1605, 5432, 6275, 24838, 25502, 26990]
 (.n
 (.n .e [1605, 5432, 6275, 25502, 26990] .e) [1605, 5432, 6279, 10344, 17048, 24838] .e)) [1605, 5432, 6283, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5432, 6283, 10344, 17048, 24846] .e) [1605, 5432, 6283, 10344, 24838, 25502] .e) [1605, 5432, 6283, 17048, 24838, 26990]
 (.n
 (.n .e [1605, 5432, 6291, 10344, 17048, 24838] .e) [1605, 5432, 6299, 10344, 17048, 24838] .e)))) [1605, 5432, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5432, 6315, 10344, 17048, 24838] .e) [1605, 5432, 6339, 10344, 17048, 24838]
 (.n .e [1605, 5432, 6531, 10344, 17048, 24838] .e)) [1605, 5433, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5434, 6275, 10344, 17048, 24838] .e) [1605, 5436, 6275, 10344, 17048, 24838] .e)) [1605, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17048, 24839] .e) [1605, 5488, 6275, 10344, 17048, 24846] .e) [1605, 5488, 6275, 10344, 17048, 24854]
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17048, 24870] .e) [1605, 5488, 6275, 10344, 17048, 24902] .e))) [1605, 5488, 6275, 10344, 17048, 24934]
 (.n
 (.n
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17048, 24966] .e) [1605, 5488, 6275, 10344, 17049, 24838]
 (.n .e [1605, 5488, 6275, 10344, 17050, 24838] .e)) [1605, 5488, 6275, 10344, 17052, 24838]
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17080, 24838] .e) [1605, 5488, 6275, 10344, 17112, 24838] .e)) [1605, 5488, 6275, 10344, 17112, 24902]
 (.n
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17144, 24838] .e) [1605, 5488, 6275, 10344, 17304, 24838] .e) [1605, 5488, 6275, 10345, 17048, 24838]
 (.n
 (.n .e [1605, 5488, 6275, 10346, 17048, 24838] .e) [1605, 5488, 6275, 10348, 17048, 24838] .e))))) [1605, 5488, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5488, 6275, 10472, 17048, 24838] .e) [1605, 5488, 6275, 10600, 17048, 24838]
 (.n .e [1605, 5488, 6279, 10344, 17048, 24838] .e)) [1605, 5488, 6283, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5488, 6291, 10344, 17048, 24838] .e) [1605, 5488, 6307, 10344, 17048, 24838] .e)) [1605, 5488, 6339, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5488, 6339, 10344, 17048, 24902] .e) [1605, 5488, 6339, 10344, 17112, 24838] .e) [1605, 5488, 6371, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5488, 6531, 10344, 17048, 24838] .e) [1605, 5489, 6275, 10344, 17048, 24838] .e))) [1605, 5489, 6275, 10344, 17048, 24903]
 (.n
 (.n
 (.n
 (.n .e [1605, 5489, 6275, 10344, 17113, 24838] .e) [1605, 5489, 6275, 10345, 17048, 24838]
 (.n .e [1605, 5489, 6339, 10344, 17048, 24838] .e)) [1605, 5490, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5492, 6275, 10344, 17048, 24838] .e) [1605, 5492, 6275, 10344, 17048, 24902] .e)) [1605, 5492, 6275, 10344, 17048, 25502]
 (.n
 (.n
 (.n .e [1605, 5492, 6275, 10344, 17116, 24838] .e) [1605, 5492, 6275, 10348, 17048, 24838] .e) [1605, 5492, 6343, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5493, 6275, 10344, 17048, 24838] .e) [1605, 5496, 6275, 10344, 17048, 24838] .e)))) [1605, 5496, 6275, 10344, 17048, 24910]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5496, 6275, 10344, 17112, 24838] .e) [1605, 5496, 6275, 10344, 24838, 25502]
 (.n .e [1605, 5496, 6275, 17048, 24838, 26990] .e)) [1605, 5496, 6275, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5496, 6275, 18141, 24838, 27384] .e) [1605, 5496, 6347, 10344, 17048, 24838] .e)) [1605, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17048, 24839] .e) [1605, 5552, 6275, 10344, 17048, 24846] .e) [1605, 5552, 6275, 10344, 17048, 24854]
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17048, 24870] .e) [1605, 5552, 6275, 10344, 17048, 24902] .e))) [1605, 5552, 6275, 10344, 17048, 24966]
 (.n
 (.n
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17048, 24982] .e) [1605, 5552, 6275, 10344, 17049, 24838] .e) [1605, 5552, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17052, 24838] .e) [1605, 5552, 6275, 10344, 17080, 24838] .e)) [1605, 5552, 6275, 10344, 17112, 24838]
 (.n
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17304, 24838] .e) [1605, 5552, 6275, 10345, 17048, 24838] .e) [1605, 5552, 6275, 10346, 17048, 24838]
 (.n
 (.n .e [1605, 5552, 6275, 10348, 17048, 24838] .e) [1605, 5552, 6275, 10360, 17048, 24838] .e))))))

def T5baa : T := .n T5baaa [1605, 5432, 6275, 10344, 25502, 26990] T5baab

def T5baba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5552, 6275, 10472, 17048, 24966] .e) [1605, 5552, 6275, 10488, 17048, 24838]
 (.n .e [1605, 5552, 6275, 10600, 17048, 24838] .e)) [1605, 5552, 6279, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5552, 6283, 10344, 17048, 24838] .e) [1605, 5552, 6291, 10344, 17048, 24838] .e)) [1605, 5552, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5552, 6339, 10344, 17048, 24838] .e) [1605, 5552, 6531, 10344, 17048, 24838] .e) [1605, 5553, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5553, 6275, 10344, 17048, 24967] .e) [1605, 5553, 6275, 10344, 17049, 24838] .e))) [1605, 5553, 6275, 10473, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5554, 6275, 10344, 17048, 24838] .e) [1605, 5554, 6275, 10344, 17048, 24966]
 (.n .e [1605, 5554, 6275, 10344, 17048, 26990] .e)) [1605, 5554, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [1605, 5554, 6275, 10474, 17048, 24838] .e) [1605, 5554, 10344, 14571, 17048, 24838] .e)) [1605, 5554, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n .e [1605, 5554, 10344, 17048, 25502, 31111] .e) [1605, 5555, 6275, 10344, 17048, 24838] .e) [1605, 5556, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5560, 6275, 10344, 17048, 24838] .e) [1605, 5560, 6275, 10344, 17048, 24974] .e)))) [1605, 5560, 6275, 10344, 24838, 25502]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5560, 6275, 10344, 24838, 27384] .e) [1605, 5560, 6275, 10472, 17048, 24838]
 (.n .e [1605, 5560, 6275, 14571, 24838, 27384] .e)) [1605, 5560, 6275, 17048, 24838, 26990]
 (.n
 (.n .e [1605, 5560, 6283, 10344, 17048, 24838] .e) [1605, 5616, 6275, 10344, 17048, 24838] .e)) [1605, 5625, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5936, 6275, 10344, 17048, 24854] .e) [1605, 5936, 6275, 10360, 17048, 24838] .e) [1605, 5936, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 6005, 6275, 10344, 17048, 24854] .e) [1605, 6005, 6275, 10344, 17048, 24862] .e))) [1605, 6005, 6275, 10344, 17048, 24886]
 (.n
 (.n
 (.n
 (.n .e [1605, 6005, 6275, 10344, 17048, 24982] .e) [1605, 6005, 6275, 10344, 18141, 24854]
 (.n .e [1605, 6005, 6275, 10360, 17048, 24838] .e)) [1605, 6005, 6275, 10360, 17048, 24854]
 (.n
 (.n .e [1605, 6005, 6275, 10360, 18141, 24838] .e) [1605, 6005, 6275, 10488, 17048, 24838] .e)) [1605, 6005, 6275, 10616, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 6005, 6275, 15736, 17048, 24934] .e) [1605, 6005, 6275, 15736, 17144, 24838] .e) [1605, 6005, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 6005, 6291, 10344, 17048, 24854] .e) [1605, 6005, 6291, 10344, 18141, 24838] .e))))) [1605, 6005, 6291, 10360, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 6005, 6299, 10344, 17048, 24838] .e) [1605, 6005, 6323, 10344, 17048, 24838]
 (.n .e [1605, 6005, 6547, 10344, 17048, 24838] .e)) [1605, 6005, 7603, 10344, 17048, 24839]
 (.n
 (.n .e [1605, 6005, 7603, 10344, 17049, 24838] .e) [1605, 6005, 7603, 10345, 17048, 24838] .e)) [1605, 6275, 7472, 10344, 17048, 24870]
 (.n
 (.n
 (.n .e [1605, 6275, 7472, 10344, 17080, 24838] .e) [1605, 6275, 7603, 10344, 17048, 24870] .e) [1605, 6275, 7603, 10344, 17048, 24878]
 (.n
 (.n .e [1605, 6275, 7603, 10344, 17048, 24886] .e) [1605, 6275, 7603, 10344, 17048, 24934] .e))) [1605, 6275, 7603, 10344, 17080, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 6275, 7603, 10344, 17080, 24870] .e) [1605, 6275, 7603, 10344, 17144, 24838]
 (.n .e [1605, 6275, 7603, 10344, 17336, 24838] .e)) [1605, 6275, 7603, 10344, 22456, 24982]
 (.n
 (.n .e [1605, 6275, 7603, 10488, 22456, 24838] .e) [1605, 6275, 7603, 14571, 17048, 24870] .e)) [1605, 6275, 7603, 14571, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 6275, 10344, 15736, 17336, 24838] .e) [1605, 6275, 10616, 17048, 22456, 24838] .e) [1605, 6275, 10616, 22456, 24838, 25502]
 (.n
 (.n .e [1605, 6275, 15736, 17336, 24838, 26990] .e) [1605, 6275, 15736, 22456, 24838, 27384] .e)))) [1605, 6275, 15736, 22456, 24838, 27646]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 6275, 15736, 22456, 25502, 26990] .e) [1605, 6275, 15736, 22525, 24838, 27384]
 (.n .e [1605, 6275, 15867, 22456, 24838, 27384] .e)) [1605, 6307, 7603, 10344, 17048, 24870]
 (.n
 (.n .e [1605, 6307, 7603, 10344, 17080, 24838] .e) [1605, 6547, 10344, 17048, 22456, 24838] .e)) [1605, 6547, 10344, 22456, 24838, 25502]
 (.n
 (.n
 (.n .e [1605, 7603, 8224, 14571, 17048, 24838] .e) [1605, 7603, 10344, 14571, 17048, 24870] .e) [1605, 7603, 10344, 14571, 17080, 24838]
 (.n
 (.n .e [1605, 7603, 10344, 17048, 22456, 24839] .e) [1605, 7603, 10344, 17048, 23195, 24870] .e))) [1605, 7603, 10344, 17048, 24839, 30006]
 (.n
 (.n
 (.n
 (.n .e [1605, 7603, 10344, 17048, 24839, 30007] .e) [1605, 7603, 10344, 17048, 24870, 31111] .e) [1605, 7603, 10344, 17048, 24870, 31143]
 (.n
 (.n .e [1605, 7603, 10344, 17049, 22456, 24838] .e) [1605, 7603, 10344, 17049, 22457, 24838] .e)) [1605, 7603, 10344, 17049, 24838, 30006]
 (.n
 (.n
 (.n .e [1605, 7603, 10344, 17080, 23195, 24838] .e) [1605, 7603, 10344, 17080, 23227, 24838] .e) [1605, 7603, 10344, 17080, 24838, 31111]
 (.n
 (.n .e [1605, 7603, 10344, 22456, 25502, 31111] .e) [1605, 7603, 10344, 23195, 25502, 30006] .e))))))

def T5babb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 7603, 10345, 17048, 24838, 30006] .e) [1605, 7603, 14571, 17048, 17080, 24838]
 (.n .e [1605, 7603, 14571, 17048, 24838, 24870] .e)) [1605, 7603, 14571, 17048, 24870]
 (.n
 (.n .e [1605, 7603, 14571, 17048, 26990, 30006] .e) [1605, 7603, 14571, 17080, 24838] .e)) [1605, 7603, 14571, 22456, 24838, 27384]
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17048, 24838] .e) [1607, 5424, 6275, 10344, 17048, 24839] .e) [1607, 5424, 6275, 10344, 17048, 24846]
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17048, 24854] .e) [1607, 5424, 6275, 10344, 17048, 24870] .e))) [1607, 5424, 6275, 10344, 17048, 24902]
 (.n
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17048, 24966] .e) [1607, 5424, 6275, 10344, 17048, 26886]
 (.n .e [1607, 5424, 6275, 10344, 17048, 26990] .e)) [1607, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17050, 24838] .e) [1607, 5424, 6275, 10344, 17050, 26990] .e)) [1607, 5424, 6275, 10344, 17051, 24838]
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17052, 24838] .e) [1607, 5424, 6275, 10344, 17054, 24838] .e) [1607, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17112, 24838] .e) [1607, 5424, 6275, 10344, 17304, 24838] .e)))) [1607, 5424, 6275, 10345, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 10346, 17048, 24838] .e) [1607, 5424, 6275, 10346, 17048, 26990]
 (.n .e [1607, 5424, 6275, 10346, 17050, 24838] .e)) [1607, 5424, 6275, 10347, 17048, 24838]
 (.n
 (.n .e [1607, 5424, 6275, 10348, 17048, 24838] .e) [1607, 5424, 6275, 10350, 17048, 24838] .e)) [1607, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 10472, 17048, 24838] .e) [1607, 5424, 6275, 10600, 17048, 24838] .e) [1607, 5424, 6275, 11885, 17048, 26990]
 (.n
 (.n .e [1607, 5424, 6275, 11887, 17048, 26990] .e) [1607, 5424, 6275, 14571, 17048, 26990] .e))) [1607, 5424, 6275, 15736, 17048, 26990]
 (.n
 (.n
 (.n
 (.n .e [1607, 5424, 6279, 10344, 17048, 24838] .e) [1607, 5424, 6283, 10344, 17048, 24838] .e) [1607, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [1607, 5424, 6307, 10344, 17048, 24838] .e) [1607, 5424, 6339, 10344, 17048, 24838] .e)) [1607, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1607, 5424, 10344, 14467, 17048, 24838] .e) [1607, 5424, 10344, 14571, 17048, 24838] .e) [1607, 5424, 10344, 14571, 17048, 26990]
 (.n
 (.n .e [1607, 5424, 10344, 14571, 17050, 24838] .e) [1607, 5424, 10346, 14571, 17048, 24838] .e))))) [1607, 5424, 11885, 14571, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1607, 5424, 11887, 14571, 17048, 24838] .e) [1607, 5424, 14571, 17048, 24838, 26990]
 (.n .e [1607, 5424, 14571, 17048, 24838, 27384] .e)) [1607, 5424, 14571, 17048, 26990]
 (.n
 (.n .e [1607, 5425, 6275, 10344, 17048, 24838] .e) [1607, 5426, 6275, 10344, 17048, 24838] .e)) [1607, 5426, 6275, 10344, 17048, 26990]
 (.n
 (.n
 (.n .e [1607, 5426, 6275, 10344, 17050, 24838] .e) [1607, 5426, 6275, 10346, 17048, 24838] .e) [1607, 5426, 10344, 14571, 17048, 24838]
 (.n
 (.n .e [1607, 5427, 6275, 10344, 17048, 24838] .e) [1607, 5428, 6275, 10344, 17048, 24838] .e))) [1607, 5430, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1607, 5432, 6275, 10344, 17048, 24838] .e) [1607, 5488, 6275, 10344, 17048, 24838]
 (.n .e [1607, 5552, 6275, 10344, 17048, 24838] .e)) [1613, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1613, 5424, 6275, 10344, 17048, 24839] .e) [1613, 5424, 6275, 10344, 17048, 24846] .e)) [1613, 5424, 6275, 10344, 17048, 24854]
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 10344, 17048, 24870] .e) [1613, 5424, 6275, 10344, 17048, 24902] .e) [1613, 5424, 6275, 10344, 17048, 24910]
 (.n
 (.n .e [1613, 5424, 6275, 10344, 17048, 24966] .e) [1613, 5424, 6275, 10344, 17049, 24838] .e)))) [1613, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 10344, 17052, 24838] .e) [1613, 5424, 6275, 10344, 17080, 24838]
 (.n .e [1613, 5424, 6275, 10344, 17112, 24838] .e)) [1613, 5424, 6275, 10344, 17304, 24838]
 (.n
 (.n .e [1613, 5424, 6275, 10344, 24838, 25240] .e) [1613, 5424, 6275, 10344, 24838, 25502] .e)) [1613, 5424, 6275, 10344, 24846, 25502]
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 10344, 25502, 26990] .e) [1613, 5424, 6275, 10344, 25502, 30006] .e) [1613, 5424, 6275, 10344, 25502, 31111]
 (.n
 (.n .e [1613, 5424, 6275, 10345, 17048, 24838] .e) [1613, 5424, 6275, 10346, 17048, 24838] .e))) [1613, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 10360, 17048, 24838] .e) [1613, 5424, 6275, 10472, 17048, 24838] .e) [1613, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n .e [1613, 5424, 6275, 17048, 24838, 26728] .e) [1613, 5424, 6275, 17048, 24838, 26990] .e)) [1613, 5424, 6275, 17048, 24846, 26990]
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 17048, 25502, 26990] .e) [1613, 5424, 6275, 17048, 26439, 26990] .e) [1613, 5424, 6275, 17048, 26447, 26990]
 (.n
 (.n .e [1613, 5424, 6275, 17048, 26990, 30006] .e) [1613, 5424, 6275, 24838, 25502, 26990] .e))))))

def T5bab : T := .n T5baba [1605, 7603, 10345, 17048, 22456, 24838] T5babb

def T5ba : T := .n T5baa [1605, 5552, 6275, 10472, 17048, 24838] T5bab

def T5bbaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1613, 5424, 6279, 10344, 17048, 24838] .e) [1613, 5424, 6283, 10344, 17048, 24838]
 (.n .e [1613, 5424, 6283, 10344, 17048, 24846] .e)) [1613, 5424, 6283, 10344, 24838, 25502]
 (.n
 (.n .e [1613, 5424, 6283, 17048, 24838, 26990] .e) [1613, 5424, 6291, 10344, 17048, 24838] .e)) [1613, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1613, 5424, 6339, 10344, 17048, 24838] .e) [1613, 5424, 6347, 10344, 17048, 24838] .e) [1613, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [1613, 5425, 6275, 10344, 17048, 24838] .e) [1613, 5426, 6275, 10344, 17048, 24838] .e))) [1613, 5428, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1613, 5432, 6275, 10344, 17048, 24838] .e) [1613, 5432, 6275, 10344, 17048, 24846]
 (.n .e [1613, 5432, 6275, 10344, 24838, 25502] .e)) [1613, 5432, 6275, 17048, 24838, 26990]
 (.n
 (.n .e [1613, 5432, 6283, 10344, 17048, 24838] .e) [1613, 5488, 6275, 10344, 17048, 24838] .e)) [1613, 5496, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1613, 5552, 6275, 10344, 17048, 24838] .e) [1615, 5424, 6275, 10344, 17048, 24838] .e) [1621, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1621, 5424, 6275, 10344, 17048, 24839] .e) [1621, 5424, 6275, 10344, 17048, 24846] .e)))) [1621, 5424, 6275, 10344, 17048, 24854]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1621, 5424, 6275, 10344, 17048, 24870] .e) [1621, 5424, 6275, 10344, 17048, 24902]
 (.n .e [1621, 5424, 6275, 10344, 17048, 24966] .e)) [1621, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [1621, 5424, 6275, 10344, 17050, 24838] .e) [1621, 5424, 6275, 10344, 17052, 24838] .e)) [1621, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n
 (.n .e [1621, 5424, 6275, 10344, 17112, 24838] .e) [1621, 5424, 6275, 10344, 17304, 24838] .e) [1621, 5424, 6275, 10344, 18141, 24854]
 (.n
 (.n .e [1621, 5424, 6275, 10345, 17048, 24838] .e) [1621, 5424, 6275, 10346, 17048, 24838] .e))) [1621, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1621, 5424, 6275, 10360, 17048, 24838] .e) [1621, 5424, 6275, 10360, 17048, 24854]
 (.n .e [1621, 5424, 6275, 10360, 18141, 24838] .e)) [1621, 5424, 6275, 10472, 17048, 24838]
 (.n
 (.n .e [1621, 5424, 6275, 10600, 17048, 24838] .e) [1621, 5424, 6279, 10344, 17048, 24838] .e)) [1621, 5424, 6283, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1621, 5424, 6291, 10344, 17048, 24838] .e) [1621, 5424, 6291, 10344, 17048, 24854] .e) [1621, 5424, 6291, 10344, 18141, 24838]
 (.n
 (.n .e [1621, 5424, 6291, 10360, 17048, 24838] .e) [1621, 5424, 6307, 10344, 17048, 24838] .e))))) [1621, 5424, 6339, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1621, 5424, 6531, 10344, 17048, 24838] .e) [1621, 5425, 6275, 10344, 17048, 24838]
 (.n .e [1621, 5426, 6275, 10344, 17048, 24838] .e)) [1621, 5428, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1621, 5432, 6275, 10344, 17048, 24838] .e) [1621, 5488, 6275, 10344, 17048, 24838] .e)) [1621, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1621, 6005, 6275, 10344, 17048, 24854] .e) [1621, 6005, 6275, 10360, 17048, 24838] .e) [1621, 6005, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [1623, 5424, 6275, 10344, 17048, 24838] .e) [1629, 5424, 6275, 10344, 17048, 24838] .e))) [1629, 5424, 6275, 10344, 17048, 24862]
 (.n
 (.n
 (.n
 (.n .e [1629, 5424, 6275, 10344, 24838, 25502] .e) [1629, 5424, 6275, 10360, 17048, 24838]
 (.n .e [1629, 5424, 6275, 17048, 24838, 26990] .e)) [1629, 5424, 6299, 10344, 17048, 24838]
 (.n
 (.n .e [1629, 5432, 6275, 10344, 17048, 24838] .e) [1637, 5424, 6275, 10344, 17048, 24838] .e)) [1637, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17048, 24846] .e) [1637, 5424, 6275, 10344, 17048, 24854] .e) [1637, 5424, 6275, 10344, 17048, 24870]
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17048, 24902] .e) [1637, 5424, 6275, 10344, 17048, 24934] .e)))) [1637, 5424, 6275, 10344, 17048, 24966]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17049, 24838] .e) [1637, 5424, 6275, 10344, 17050, 24838]
 (.n .e [1637, 5424, 6275, 10344, 17052, 24838] .e)) [1637, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17080, 24870] .e) [1637, 5424, 6275, 10344, 17112, 24838] .e)) [1637, 5424, 6275, 10344, 17144, 24838]
 (.n
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17304, 24838] .e) [1637, 5424, 6275, 10345, 17048, 24838] .e) [1637, 5424, 6275, 10346, 17048, 24838]
 (.n
 (.n .e [1637, 5424, 6275, 10348, 17048, 24838] .e) [1637, 5424, 6275, 10360, 17048, 24838] .e))) [1637, 5424, 6275, 10472, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1637, 5424, 6275, 10600, 17048, 24838] .e) [1637, 5424, 6275, 14440, 17048, 24838] .e) [1637, 5424, 6275, 14571, 17048, 24838]
 (.n
 (.n .e [1637, 5424, 6275, 14571, 17048, 24870] .e) [1637, 5424, 6275, 14571, 17080, 24838] .e)) [1637, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1637, 5424, 6283, 10344, 17048, 24838] .e) [1637, 5424, 6291, 10344, 17048, 24838] .e) [1637, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n .e [1637, 5424, 6307, 10344, 17048, 24870] .e) [1637, 5424, 6307, 10344, 17080, 24838] .e))))))

def T5bbab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1637, 5424, 6339, 10344, 17048, 24838] .e) [1637, 5424, 6371, 10344, 17048, 24838]
 (.n .e [1637, 5424, 6531, 10344, 17048, 24838] .e)) [1637, 5424, 7603, 14571, 17048, 24838]
 (.n
 (.n .e [1637, 5424, 7879, 14571, 17048, 24838] .e) [1637, 5424, 7911, 14571, 17048, 24838] .e)) [1637, 5424, 14571, 17048, 23195, 24838]
 (.n
 (.n
 (.n .e [1637, 5425, 6275, 10344, 17048, 24838] .e) [1637, 5426, 6275, 10344, 17048, 24838] .e) [1637, 5428, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1637, 5432, 6275, 10344, 17048, 24838] .e) [1637, 5488, 6275, 10344, 17048, 24838] .e))) [1637, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1637, 6275, 7472, 10344, 17048, 24838] .e) [1637, 6275, 7603, 10344, 17048, 24838]
 (.n .e [1637, 6275, 7603, 10344, 17048, 24870] .e)) [1637, 6275, 7603, 10344, 17080, 24838]
 (.n
 (.n .e [1637, 6275, 7603, 14571, 17048, 24838] .e) [1637, 6307, 7603, 10344, 17048, 24838] .e)) [1637, 7603, 10344, 14571, 17048, 24838]
 (.n
 (.n
 (.n .e [1637, 7603, 10344, 17048, 23195, 24838] .e) [1637, 7603, 10344, 17048, 24838, 31111] .e) [1637, 7603, 14571, 17048, 24838]
 (.n
 (.n .e [1639, 5424, 6275, 10344, 17048, 24838] .e) [1645, 5424, 6275, 10344, 17048, 24838] .e)))) [1645, 5424, 6275, 10344, 17048, 24878]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1645, 5424, 6275, 10344, 17080, 24838] .e) [1645, 5424, 6275, 10344, 24838, 25502]
 (.n .e [1645, 5424, 6275, 14571, 17048, 24838] .e)) [1645, 5424, 6275, 17048, 24838, 26990]
 (.n
 (.n .e [1645, 5424, 6315, 10344, 17048, 24838] .e) [1645, 5432, 6275, 10344, 17048, 24838] .e)) [1645, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1653, 5424, 6275, 10344, 17048, 24838] .e) [1653, 5424, 6275, 10344, 17048, 24886] .e) [1653, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n .e [1653, 5424, 6275, 10360, 17048, 24838] .e) [1653, 5424, 6275, 14571, 17048, 24838] .e))) [1653, 5424, 6323, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1653, 6275, 7603, 10344, 17048, 24838] .e) [1733, 5424, 6275, 10344, 17048, 24838] .e) [1733, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17048, 24846] .e) [1733, 5424, 6275, 10344, 17048, 24854] .e)) [1733, 5424, 6275, 10344, 17048, 24870]
 (.n
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17048, 24902] .e) [1733, 5424, 6275, 10344, 17048, 24966] .e) [1733, 5424, 6275, 10344, 17048, 24967]
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17049, 24838] .e) [1733, 5424, 6275, 10344, 17050, 24838] .e))))) [1733, 5424, 6275, 10344, 17052, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17080, 24838] .e) [1733, 5424, 6275, 10344, 17112, 24838]
 (.n .e [1733, 5424, 6275, 10344, 17304, 24838] .e)) [1733, 5424, 6275, 10345, 17048, 24838]
 (.n
 (.n .e [1733, 5424, 6275, 10346, 17048, 24838] .e) [1733, 5424, 6275, 10348, 17048, 24838] .e)) [1733, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1733, 5424, 6275, 10472, 17048, 24838] .e) [1733, 5424, 6275, 10472, 17048, 24966] .e) [1733, 5424, 6275, 10473, 17048, 24838]
 (.n
 (.n .e [1733, 5424, 6275, 10600, 17048, 24838] .e) [1733, 5424, 6279, 10344, 17048, 24838] .e))) [1733, 5424, 6283, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1733, 5424, 6291, 10344, 17048, 24838] .e) [1733, 5424, 6307, 10344, 17048, 24838]
 (.n .e [1733, 5424, 6339, 10344, 17048, 24838] .e)) [1733, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [1733, 5425, 6275, 10344, 17048, 24838] .e) [1733, 5426, 6275, 10344, 17048, 24838] .e)) [1733, 5428, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1733, 5432, 6275, 10344, 17048, 24838] .e) [1733, 5488, 6275, 10344, 17048, 24838] .e) [1733, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1733, 5552, 6275, 10344, 17048, 24966] .e) [1733, 5552, 6275, 10472, 17048, 24838] .e)))) [1733, 5553, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1735, 5424, 6275, 10344, 17048, 24838] .e) [1735, 5424, 6275, 10344, 17048, 24966]
 (.n .e [1735, 5424, 6275, 10344, 17048, 26990] .e)) [1735, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [1735, 5424, 6275, 10474, 17048, 24838] .e) [1735, 5424, 10344, 14571, 17048, 24838] .e)) [1735, 5424, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n .e [1735, 5424, 10344, 17048, 25502, 31111] .e) [1735, 5554, 6275, 10344, 17048, 24838] .e) [1741, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1741, 5424, 6275, 10344, 17048, 24974] .e) [1741, 5424, 6275, 10344, 24838, 25502] .e))) [1741, 5424, 6275, 10344, 24838, 27384]
 (.n
 (.n
 (.n
 (.n .e [1741, 5424, 6275, 10472, 17048, 24838] .e) [1741, 5424, 6275, 14571, 24838, 27384] .e) [1741, 5424, 6275, 17048, 24838, 26990]
 (.n
 (.n .e [1741, 5424, 6283, 10344, 17048, 24838] .e) [1741, 5560, 6275, 10344, 17048, 24838] .e)) [1749, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1749, 5424, 6275, 10344, 17048, 24982] .e) [1749, 5424, 6275, 10488, 17048, 24838] .e) [1749, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [1749, 5552, 6275, 10344, 17048, 24838] .e) [1757, 5424, 6275, 10344, 17048, 24838] .e))))))

def T5bba : T := .n T5bbaa [1637, 5424, 6307, 14571, 17048, 24838] T5bbab

def T5bbba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17048, 24838] .e) [1861, 5424, 6275, 10344, 17048, 24839]
 (.n .e [1861, 5424, 6275, 10344, 17048, 24846] .e)) [1861, 5424, 6275, 10344, 17048, 24854]
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17048, 24870] .e) [1861, 5424, 6275, 10344, 17048, 24902] .e)) [1861, 5424, 6275, 10344, 17048, 24966]
 (.n
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17049, 24838] .e) [1861, 5424, 6275, 10344, 17050, 24838] .e) [1861, 5424, 6275, 10344, 17052, 24838]
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17080, 24838] .e) [1861, 5424, 6275, 10344, 17112, 24838] .e))) [1861, 5424, 6275, 10344, 17304, 24838]
 (.n
 (.n
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17308, 24838] .e) [1861, 5424, 6275, 10345, 17048, 24838]
 (.n .e [1861, 5424, 6275, 10346, 17048, 24838] .e)) [1861, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n .e [1861, 5424, 6275, 10360, 17048, 24838] .e) [1861, 5424, 6275, 10472, 17048, 24838] .e)) [1861, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n
 (.n .e [1861, 5424, 6275, 10600, 17304, 24838] .e) [1861, 5424, 6275, 10604, 17048, 24838] .e) [1861, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n .e [1861, 5424, 6283, 10344, 17048, 24838] .e) [1861, 5424, 6291, 10344, 17048, 24838] .e)))) [1861, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1861, 5424, 6339, 10344, 17048, 24838] .e) [1861, 5424, 6531, 10344, 17048, 24838]
 (.n .e [1861, 5424, 6531, 10344, 17304, 24838] .e)) [1861, 5424, 6531, 10600, 17048, 24838]
 (.n
 (.n .e [1861, 5424, 6535, 10344, 17048, 24838] .e) [1861, 5425, 6275, 10344, 17048, 24838] .e)) [1861, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1861, 5428, 6275, 10344, 17048, 24838] .e) [1861, 5432, 6275, 10344, 17048, 24838] .e) [1861, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1861, 5552, 6275, 10344, 17048, 24838] .e) [1863, 5424, 6275, 10344, 17048, 24838] .e))) [1863, 5424, 6275, 10344, 17048, 26990]
 (.n
 (.n
 (.n
 (.n .e [1863, 5424, 6275, 10344, 17048, 31111] .e) [1863, 5424, 6275, 10344, 17306, 24838]
 (.n .e [1863, 5424, 6275, 10602, 17048, 24838] .e)) [1863, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [1863, 5424, 7603, 10344, 17048, 31111] .e) [1863, 5424, 10344, 14571, 17048, 24838] .e)) [1863, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1869, 5424, 6275, 10344, 17048, 24838] .e) [1877, 5424, 6275, 10344, 17048, 24838] .e) [1877, 5424, 6275, 10344, 17048, 24854]
 (.n
 (.n .e [1877, 5424, 6275, 10344, 17304, 24838] .e) [1877, 5424, 6275, 10616, 17048, 24838] .e))))) [1877, 5424, 6547, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1893, 5424, 6275, 10344, 17048, 24838] .e) [1893, 5424, 6275, 10344, 17048, 24870]
 (.n .e [1893, 5424, 6275, 10344, 17336, 24838] .e)) [1893, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n .e [1893, 5424, 6275, 14571, 17048, 24838] .e) [1893, 5424, 6563, 10344, 17048, 24838] .e)) [1893, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1893, 6275, 10344, 15736, 17048, 24838] .e) [1893, 6275, 15736, 17048, 24838, 26990] .e) [1909, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1989, 5424, 6275, 10344, 17048, 24838] .e) [2007, 5424, 6275, 10344, 17048, 24838] .e))) [2049, 6005, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [4112, 6005, 6275, 10344, 18141, 24838] .e) [5424, 5428, 6275, 10344, 18141, 25502]
 (.n .e [5424, 5701, 6275, 10344, 17048, 24839] .e)) [5424, 5701, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [5424, 5701, 6275, 10345, 17048, 24838] .e) [5424, 6005, 6275, 10344, 17048, 24839] .e)) [5424, 6005, 6275, 10344, 17048, 24903]
 (.n
 (.n
 (.n .e [5424, 6005, 6275, 10344, 17048, 24967] .e) [5424, 6005, 6275, 10344, 17049, 24838] .e) [5424, 6005, 6275, 10344, 17049, 24839]
 (.n
 (.n .e [5424, 6005, 6275, 10344, 17051, 24838] .e) [5424, 6005, 6275, 10344, 17053, 24838] .e)))) [5424, 6005, 6275, 10344, 17113, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [5424, 6005, 6275, 10344, 18141, 24854] .e) [5424, 6005, 6275, 10345, 17048, 24838]
 (.n .e [5424, 6005, 6275, 10345, 17048, 24839] .e)) [5424, 6005, 6275, 10345, 17049, 24838]
 (.n
 (.n .e [5424, 6005, 6275, 10347, 17048, 24838] .e) [5424, 6005, 6275, 10349, 17048, 24838] .e)) [5424, 6005, 6275, 10360, 18141, 24838]
 (.n
 (.n
 (.n .e [5424, 6005, 6275, 10473, 17048, 24838] .e) [5424, 6005, 6275, 10604, 17048, 26439] .e) [5424, 6005, 6291, 10344, 18141, 24838]
 (.n
 (.n .e [5424, 6005, 6535, 10344, 17048, 26439] .e) [5424, 6005, 7603, 10344, 17048, 24839] .e))) [5424, 6005, 7603, 10344, 17049, 24838]
 (.n
 (.n
 (.n
 (.n .e [5424, 6005, 7603, 10345, 17048, 24838] .e) [5424, 6275, 6279, 10344, 18141, 25502] .e) [5424, 6275, 7879, 10344, 17048, 24903]
 (.n
 (.n .e [5424, 6275, 7879, 10344, 17113, 24838] .e) [5424, 6275, 7879, 10344, 18141, 24854] .e)) [5424, 6275, 7879, 10360, 18141, 24838]
 (.n
 (.n
 (.n .e [5424, 6275, 8196, 10344, 18141, 25502] .e) [5424, 6275, 10344, 10348, 18141, 25502] .e) [5424, 6275, 10344, 11885, 18141, 24854]
 (.n
 (.n .e [5424, 6275, 10348, 17048, 17989, 24838] .e) [5424, 6275, 10348, 17048, 18141, 24838] .e))))))

def T5bbbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [5424, 6275, 10348, 17052, 18141, 24838] .e) [5424, 6275, 10348, 18141, 23195, 24838]
 (.n .e [5424, 6275, 10348, 18141, 24838, 25502] .e)) [5424, 6275, 10348, 18141, 24838, 27384]
 (.n
 (.n .e [5424, 6275, 10348, 18141, 24838, 27388] .e) [5424, 6275, 10348, 18141, 25502] .e)) [5424, 6275, 10349, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [5424, 6275, 10350, 17048, 18141, 24838] .e) [5424, 6275, 10360, 11885, 18141, 24838] .e) [5424, 6275, 10360, 11901, 18141, 24838]
 (.n
 (.n .e [5424, 6275, 10604, 17048, 18141, 24838] .e) [5424, 6275, 11885, 18141, 25502, 26990] .e))) [5424, 6279, 10344, 17048, 17989, 24838]
 (.n
 (.n
 (.n
 (.n .e [5424, 6279, 10344, 17048, 18141, 24838] .e) [5424, 6279, 10344, 17048, 18141, 25502]
 (.n .e [5424, 6279, 10344, 17052, 18141, 24838] .e)) [5424, 6279, 10344, 18141, 23195, 24838]
 (.n
 (.n .e [5424, 6279, 10344, 18141, 23199, 24838] .e) [5424, 6279, 10344, 18141, 24838, 25502] .e)) [5424, 6279, 10344, 18141, 24838, 27384]
 (.n
 (.n
 (.n .e [5424, 6279, 10344, 18141, 25502] .e) [5424, 6279, 10348, 17048, 18141, 24838] .e) [5424, 6291, 7879, 10344, 18141, 24838]
 (.n
 (.n .e [5424, 6291, 7895, 10344, 18141, 24838] .e) [5424, 6291, 10344, 11885, 18141, 24838] .e)))) [5424, 6343, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [5424, 6343, 10344, 17048, 24838, 26439] .e) [5424, 6343, 10344, 17048, 26439, 26990]
 (.n .e [5424, 6535, 10344, 17048, 18141, 24838] .e)) [5424, 7879, 10344, 14571, 17048, 24903]
 (.n
 (.n .e [5424, 7879, 10344, 14571, 17113, 24838] .e) [5424, 7879, 10344, 17048, 18141, 24967] .e)) [5424, 7879, 10344, 17048, 26439, 31111]
 (.n
 (.n
 (.n .e [5424, 7879, 10344, 17048, 26439, 31215] .e) [5424, 7879, 10344, 17048, 26591, 31111] .e) [5424, 7879, 10344, 18141, 25502, 31111]
 (.n
 (.n .e [5424, 7879, 10473, 17048, 18141, 24838] .e) [5424, 7879, 14571, 17048, 26439, 26990] .e))) [5424, 7879, 14571, 18141, 24838, 27384]
 (.n
 (.n
 (.n
 (.n .e [5424, 8183, 10344, 17048, 26439, 31111] .e) [5424, 11885, 14571, 18141, 23195, 24838] .e) [5425, 6005, 6275, 10344, 17048, 24839]
 (.n
 (.n .e [5425, 6005, 6275, 10344, 17049, 24838] .e) [5425, 6005, 6275, 10345, 17048, 24838] .e)) [5428, 6275, 10344, 17048, 17989, 24838]
 (.n
 (.n
 (.n .e [5428, 6275, 10344, 17048, 18141, 24838] .e) [5428, 6275, 10344, 17048, 18141, 25502] .e) [5428, 6275, 10344, 17052, 18141, 24838]
 (.n
 (.n .e [5428, 6275, 10344, 18141, 23195, 24838] .e) [5428, 6275, 10344, 18141, 24838, 25502] .e))))) [5428, 6275, 10344, 18141, 24838, 27384]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [5428, 6275, 10344, 18141, 25502] .e) [5428, 6275, 10348, 17048, 18141, 24838]
 (.n .e [5428, 6279, 10344, 17048, 18141, 24838] .e)) [5429, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n .e [5430, 6275, 10344, 17048, 18141, 24838] .e) [5492, 6275, 10344, 17048, 18141, 24838] .e)) [5492, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n
 (.n .e [5492, 6275, 10344, 17048, 26439, 26990] .e) [6005, 6275, 6291, 10344, 18141, 24838] .e) [6005, 6275, 7603, 10344, 17048, 24839]
 (.n
 (.n .e [6005, 6275, 7603, 10344, 17049, 24838] .e) [6005, 6275, 7603, 10345, 17048, 24838] .e))) [6005, 6275, 10344, 10360, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [6005, 6275, 10344, 11885, 17048, 24854] .e) [6005, 6275, 10344, 15736, 17048, 24839]
 (.n .e [6005, 6275, 10344, 15736, 17049, 24838] .e)) [6005, 6275, 10344, 16400, 18141, 24838]
 (.n
 (.n .e [6005, 6275, 10344, 17048, 18141, 24854] .e) [6005, 6275, 10344, 17048, 24839, 30006] .e)) [6005, 6275, 10344, 17048, 24839, 30007]
 (.n
 (.n
 (.n .e [6005, 6275, 10344, 17048, 24854, 26439] .e) [6005, 6275, 10344, 17048, 24854, 26455] .e) [6005, 6275, 10344, 17049, 24838, 30006]
 (.n
 (.n .e [6005, 6275, 10344, 18141, 24838, 24854] .e) [6005, 6275, 10344, 18141, 24854] .e)))) [6005, 6275, 10344, 18141, 25502, 30006]
 (.n
 (.n
 (.n
 (.n
 (.n .e [6005, 6275, 10345, 15736, 17048, 24838] .e) [6005, 6275, 10345, 15737, 17048, 24838]
 (.n .e [6005, 6275, 10345, 17048, 24838, 30006] .e)) [6005, 6275, 10360, 11885, 17048, 24838]
 (.n
 (.n .e [6005, 6275, 10360, 11901, 17048, 24838] .e) [6005, 6275, 10360, 17048, 18141, 24838] .e)) [6005, 6275, 10360, 17048, 24838, 26439]
 (.n
 (.n
 (.n .e [6005, 6275, 10360, 18141, 24838] .e) [6005, 6275, 11885, 17048, 26990, 30006] .e) [6005, 6275, 15736, 17048, 26439, 26990]
 (.n
 (.n .e [6005, 6275, 15736, 18141, 24838, 27384] .e) [6005, 6291, 10344, 11885, 17048, 24838] .e))) [6005, 6291, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [6005, 6291, 10344, 17048, 24838, 26439] .e) [6005, 6291, 10344, 18141, 24838] .e) [6005, 7603, 10344, 10345, 17048, 24838]
 (.n
 (.n .e [6005, 7603, 10344, 17048, 17049, 24838] .e) [6005, 7603, 10344, 17048, 24838, 24839] .e)) [6005, 7603, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [6005, 7603, 10344, 17048, 26439, 31111] .e) [6005, 7603, 10344, 17049, 24838] .e) [6005, 7603, 10344, 18141, 23195, 24838]
 (.n
 (.n .e [6005, 7603, 10345, 17048, 24838] .e) [6005, 7603, 11885, 14571, 17048, 24838] .e))))))

def T5bbb : T := .n T5bbba [5424, 6275, 10348, 17048, 18141, 25502] T5bbbb

def T5bb : T := .n T5bba [1765, 5424, 6275, 10344, 17048, 24838] T5bbb

def T5b : T := .n T5ba [1613, 5424, 6275, 25502, 26990] T5bb

def T5 : T := .n T5a [1605, 5426, 6275, 10346, 17048, 26990] T5b

def T6aaaaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [0, 1605, 5424, 6275, 10344, 17048, 24838] .e) [0, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n .e [0, 1605, 5424, 6275, 10344, 17048, 24846] .e)) [0, 1605, 5424, 6275, 10344, 17048, 24854]
 (.n
 (.n .e [0, 1605, 5424, 6275, 10344, 17048, 24870] .e) [0, 1605, 5424, 6275, 10344, 17048, 24902] .e)) [0, 1605, 5424, 6275, 10344, 17048, 24966]
 (.n
 (.n
 (.n .e [0, 1605, 5424, 6275, 10344, 17049, 24838] .e) [0, 1605, 5424, 6275, 10344, 17050, 24838] .e) [0, 1605, 5424, 6275, 10344, 17052, 24838]
 (.n
 (.n .e [0, 1605, 5424, 6275, 10344, 17080, 24838] .e) [0, 1605, 5424, 6275, 10344, 17112, 24838] .e))) [0, 1605, 5424, 6275, 10344, 17304, 24838]
 (.n
 (.n
 (.n
 (.n .e [0, 1605, 5424, 6275, 10345, 17048, 24838] .e) [0, 1605, 5424, 6275, 10346, 17048, 24838] .e) [0, 1605, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n .e [0, 1605, 5424, 6275, 10360, 17048, 24838] .e) [0, 1605, 5424, 6275, 10472, 17048, 24838] .e)) [0, 1605, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n
 (.n .e [0, 1605, 5424, 6279, 10344, 17048, 24838] .e) [0, 1605, 5424, 6283, 10344, 17048, 24838] .e) [0, 1605, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [0, 1605, 5424, 6307, 10344, 17048, 24838] .e) [0, 1605, 5424, 6339, 10344, 17048, 24838] .e)))) [0, 1605, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [0, 1605, 5425, 6275, 10344, 17048, 24838] .e) [0, 1605, 5426, 6275, 10344, 17048, 24838]
 (.n .e [0, 1605, 5428, 6275, 10344, 17048, 24838] .e)) [0, 1605, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [0, 1605, 5488, 6275, 10344, 17048, 24838] .e) [0, 1605, 5552, 6275, 10344, 17048, 24838] .e)) [0, 1607, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [0, 1613, 5424, 6275, 10344, 17048, 24838] .e) [0, 1621, 5424, 6275, 10344, 17048, 24838] .e) [0, 1637, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [0, 1733, 5424, 6275, 10344, 17048, 24838] .e) [0, 1861, 5424, 6275, 10344, 17048, 24838] .e))) [1, 16, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1, 32, 1605, 7603, 10344, 17048, 24838] .e) [1, 68, 5424, 6275, 10344, 17048, 24838] .e) [1, 130, 1605, 5424, 10344, 17048, 24838]
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1, 1605, 5424, 6275, 10344, 17048, 24839] .e)) [1, 1605, 5424, 6275, 10344, 17048, 24846]
 (.n
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 24854] .e) [1, 1605, 5424, 6275, 10344, 17048, 24870] .e) [1, 1605, 5424, 6275, 10344, 17048, 24902]
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 24966] .e) [1, 1605, 5424, 6275, 10344, 17049, 24838] .e))))) [1, 1605, 5424, 6275, 10344, 17049, 24839]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 17050, 24838] .e) [1, 1605, 5424, 6275, 10344, 17052, 24838]
 (.n .e [1, 1605, 5424, 6275, 10344, 17080, 24838] .e)) [1, 1605, 5424, 6275, 10344, 17112, 24838]
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 17304, 24838] .e) [1, 1605, 5424, 6275, 10345, 17048, 24838] .e)) [1, 1605, 5424, 6275, 10345, 17048, 24839]
 (.n
 (.n
 (.n .e [1, 1605, 5424, 6275, 10345, 17049, 24838] .e) [1, 1605, 5424, 6275, 10346, 17048, 24838] .e) [1, 1605, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n .e [1, 1605, 5424, 6275, 10360, 17048, 24838] .e) [1, 1605, 5424, 6275, 10472, 17048, 24838] .e))) [1, 1605, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1, 1605, 5424, 6279, 10344, 17048, 24838] .e) [1, 1605, 5424, 6283, 10344, 17048, 24838] .e) [1, 1605, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [1, 1605, 5424, 6307, 10344, 17048, 24838] .e) [1, 1605, 5424, 6339, 10344, 17048, 24838] .e)) [1, 1605, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1, 1605, 5424, 7299, 10344, 17048, 24838] .e) [1, 1605, 5424, 7603, 10344, 17048, 24838] .e) [1, 1605, 5424, 7603, 10344, 17048, 24839]
 (.n
 (.n .e [1, 1605, 5424, 7603, 10344, 17049, 24838] .e) [1, 1605, 5424, 7603, 10345, 17048, 24838] .e)))) [1, 1605, 5425, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1, 1605, 5425, 6275, 10344, 17048, 24839] .e) [1, 1605, 5425, 6275, 10344, 17049, 24838]
 (.n .e [1, 1605, 5425, 6275, 10345, 17048, 24838] .e)) [1, 1605, 5425, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [1, 1605, 5426, 6275, 10344, 17048, 24838] .e) [1, 1605, 5428, 6275, 10344, 17048, 24838] .e)) [1, 1605, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1, 1605, 5488, 6275, 10344, 17048, 24838] .e) [1, 1605, 5552, 6275, 10344, 17048, 24838] .e) [1, 1605, 6005, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [1, 1605, 7603, 10344, 17048, 22456, 24838] .e) [1, 1605, 7603, 10344, 17048, 24838, 30006] .e))) [1, 1607, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1, 1613, 5424, 6275, 10344, 17048, 24838] .e) [1, 1621, 5424, 6275, 10344, 17048, 24838] .e) [1, 1637, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1, 1733, 5424, 6275, 10344, 17048, 24838] .e) [1, 1861, 5424, 6275, 10344, 17048, 24838] .e)) [1, 5424, 5701, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1, 5424, 6005, 6275, 10344, 17048, 24839] .e) [1, 5424, 6005, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [1, 5424, 6005, 6275, 10345, 17048, 24838] .e) [1, 5424, 6005, 7603, 10344, 17048, 24838] .e))))))

def T6aaaab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1, 6005, 6275, 7603, 10344, 17048, 24838] .e) [1, 6005, 6275, 10344, 15736, 17048, 24838]
 (.n .e [1, 6005, 6275, 10344, 17048, 24838, 30006] .e)) [1, 6005, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [2, 8, 1605, 5424, 6275, 17048, 26990] .e) [2, 32, 1605, 5424, 14571, 17048, 24838] .e)) [2, 129, 1605, 5424, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [2, 260, 1605, 5424, 6275, 10344, 17048] .e) [2, 1605, 5424, 6275, 10344, 17048, 24838] .e) [2, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n .e [2, 1605, 5424, 6275, 10344, 17048, 24846] .e) [2, 1605, 5424, 6275, 10344, 17048, 24854] .e))) [2, 1605, 5424, 6275, 10344, 17048, 24870]
 (.n
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6275, 10344, 17048, 24902] .e) [2, 1605, 5424, 6275, 10344, 17048, 24966] .e) [2, 1605, 5424, 6275, 10344, 17048, 26886]
 (.n
 (.n .e [2, 1605, 5424, 6275, 10344, 17048, 26990] .e) [2, 1605, 5424, 6275, 10344, 17049, 24838] .e)) [2, 1605, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6275, 10344, 17050, 26990] .e) [2, 1605, 5424, 6275, 10344, 17052, 24838] .e) [2, 1605, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n .e [2, 1605, 5424, 6275, 10344, 17112, 24838] .e) [2, 1605, 5424, 6275, 10344, 17304, 24838] .e)))) [2, 1605, 5424, 6275, 10345, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6275, 10346, 17048, 24838] .e) [2, 1605, 5424, 6275, 10346, 17048, 26990]
 (.n .e [2, 1605, 5424, 6275, 10346, 17050, 24838] .e)) [2, 1605, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n .e [2, 1605, 5424, 6275, 10360, 17048, 24838] .e) [2, 1605, 5424, 6275, 10472, 17048, 24838] .e)) [2, 1605, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6275, 11885, 17048, 26990] .e) [2, 1605, 5424, 6275, 14571, 17048, 26990] .e) [2, 1605, 5424, 6275, 15736, 17048, 26990]
 (.n
 (.n .e [2, 1605, 5424, 6279, 10344, 17048, 24838] .e) [2, 1605, 5424, 6283, 10344, 17048, 24838] .e))) [2, 1605, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6307, 10344, 17048, 24838] .e) [2, 1605, 5424, 6339, 10344, 17048, 24838] .e) [2, 1605, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [2, 1605, 5424, 10344, 14467, 17048, 24838] .e) [2, 1605, 5424, 10344, 14571, 17048, 24838] .e)) [2, 1605, 5424, 10344, 14571, 17048, 26990]
 (.n
 (.n
 (.n .e [2, 1605, 5424, 10344, 14571, 17050, 24838] .e) [2, 1605, 5424, 10346, 14571, 17048, 24838] .e) [2, 1605, 5424, 11885, 14571, 17048, 24838]
 (.n
 (.n .e [2, 1605, 5424, 14571, 17048, 24838, 26990] .e) [2, 1605, 5424, 14571, 17048, 24838, 27384] .e))))) [2, 1605, 5424, 14571, 17048, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [2, 1605, 5425, 6275, 10344, 17048, 24838] .e) [2, 1605, 5426, 6275, 10344, 17048, 24838]
 (.n .e [2, 1605, 5426, 6275, 10344, 17048, 26990] .e)) [2, 1605, 5426, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [2, 1605, 5426, 6275, 10346, 17048, 24838] .e) [2, 1605, 5426, 10344, 14571, 17048, 24838] .e)) [2, 1605, 5428, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [2, 1605, 5432, 6275, 10344, 17048, 24838] .e) [2, 1605, 5488, 6275, 10344, 17048, 24838] .e) [2, 1605, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [2, 1607, 5424, 6275, 10344, 17048, 24838] .e) [2, 1607, 5424, 6275, 10344, 17048, 26990] .e))) [2, 1607, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n
 (.n
 (.n .e [2, 1607, 5424, 6275, 10346, 17048, 24838] .e) [2, 1607, 5424, 10344, 14571, 17048, 24838] .e) [2, 1607, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [2, 1613, 5424, 6275, 10344, 17048, 24838] .e) [2, 1621, 5424, 6275, 10344, 17048, 24838] .e)) [2, 1637, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [2, 1733, 5424, 6275, 10344, 17048, 24838] .e) [2, 1861, 5424, 6275, 10344, 17048, 24838] .e) [3, 128, 1605, 5424, 10344, 17048, 24838]
 (.n
 (.n .e [3, 1605, 5424, 6275, 10344, 17048, 24838] .e) [3, 1605, 5424, 6275, 10344, 17048, 24839] .e)))) [3, 1605, 5424, 6275, 10344, 17048, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n .e [3, 1605, 5424, 6275, 10344, 17051, 24838] .e) [3, 1605, 5424, 6275, 10347, 17048, 24838]
 (.n .e [3, 1605, 5424, 7603, 10344, 17048, 24838] .e)) [3, 1605, 5424, 10344, 14571, 17048, 24838]
 (.n
 (.n .e [3, 1605, 5427, 6275, 10344, 17048, 24838] .e) [3, 1607, 5424, 6275, 10344, 17048, 24838] .e)) [3, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [4, 8, 1605, 5424, 6275, 10344, 25502] .e) [4, 16, 5424, 6275, 10344, 18141, 24838] .e) [4, 65, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [4, 258, 1605, 5424, 6275, 10344, 17048] .e) [4, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [4, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 24846] .e) [4, 1605, 5424, 6275, 10344, 17048, 24854] .e) [4, 1605, 5424, 6275, 10344, 17048, 24870]
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 24902] .e) [4, 1605, 5424, 6275, 10344, 17048, 24966] .e)) [4, 1605, 5424, 6275, 10344, 17048, 25350]
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 25502] .e) [4, 1605, 5424, 6275, 10344, 17049, 24838] .e) [4, 1605, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 17052, 24838] .e) [4, 1605, 5424, 6275, 10344, 17052, 25502] .e))))))

def T6aaaa : T := .n T6aaaaa [1, 5425, 6005, 6275, 10344, 17048, 24838] T6aaaab

def T6aaaba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 17112, 24838] .e) [4, 1605, 5424, 6275, 10344, 17304, 24838]
 (.n .e [4, 1605, 5424, 6275, 10344, 18141, 25502] .e)) [4, 1605, 5424, 6275, 10344, 22456, 25502]
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 23195, 25502] .e) [4, 1605, 5424, 6275, 10345, 17048, 24838] .e)) [4, 1605, 5424, 6275, 10346, 17048, 24838]
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 10348, 17048, 24838] .e) [4, 1605, 5424, 6275, 10348, 17048, 25502] .e) [4, 1605, 5424, 6275, 10348, 17052, 24838]
 (.n
 (.n .e [4, 1605, 5424, 6275, 10360, 17048, 24838] .e) [4, 1605, 5424, 6275, 10472, 17048, 24838] .e))) [4, 1605, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6279, 10344, 17048, 24838] .e) [4, 1605, 5424, 6279, 10344, 17048, 25502] .e) [4, 1605, 5424, 6279, 10344, 17052, 24838]
 (.n
 (.n .e [4, 1605, 5424, 6279, 10348, 17048, 24838] .e) [4, 1605, 5424, 6283, 10344, 17048, 24838] .e)) [4, 1605, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6307, 10344, 17048, 24838] .e) [4, 1605, 5424, 6339, 10344, 17048, 24838] .e) [4, 1605, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [4, 1605, 5425, 6275, 10344, 17048, 24838] .e) [4, 1605, 5426, 6275, 10344, 17048, 24838] .e)))) [4, 1605, 5428, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [4, 1605, 5428, 6275, 10344, 17048, 25502] .e) [4, 1605, 5428, 6275, 10344, 17052, 24838]
 (.n .e [4, 1605, 5428, 6275, 10348, 17048, 24838] .e)) [4, 1605, 5428, 6279, 10344, 17048, 24838]
 (.n
 (.n .e [4, 1605, 5432, 6275, 10344, 17048, 24838] .e) [4, 1605, 5488, 6275, 10344, 17048, 24838] .e)) [4, 1605, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [4, 1607, 5424, 6275, 10344, 17048, 24838] .e) [4, 1613, 5424, 6275, 10344, 17048, 24838] .e) [4, 1621, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [4, 1637, 5424, 6275, 10344, 17048, 24838] .e) [4, 1733, 5424, 6275, 10344, 17048, 24838] .e))) [4, 1861, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [4, 5424, 6275, 10344, 17048, 17989, 24838] .e) [4, 5424, 6275, 10344, 17048, 18141, 24838] .e) [4, 5424, 6275, 10344, 17048, 18141, 25502]
 (.n
 (.n .e [4, 5424, 6275, 10344, 17052, 18141, 24838] .e) [4, 5424, 6275, 10344, 18141, 23195, 24838] .e)) [4, 5424, 6275, 10344, 18141, 24838, 25502]
 (.n
 (.n
 (.n .e [4, 5424, 6275, 10344, 18141, 24838, 27384] .e) [4, 5424, 6275, 10344, 18141, 25502] .e) [4, 5424, 6275, 10348, 17048, 18141, 24838]
 (.n
 (.n .e [4, 5424, 6279, 10344, 17048, 18141, 24838] .e) [4, 5428, 6275, 10344, 17048, 18141, 24838] .e))))) [5, 64, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [5, 1605, 5424, 6275, 10344, 17048, 24838] .e) [5, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n .e [5, 1605, 5424, 6275, 10344, 17048, 25502] .e)) [5, 1605, 5424, 6275, 10344, 17053, 24838]
 (.n
 (.n .e [5, 1605, 5424, 6275, 10349, 17048, 24838] .e) [5, 1605, 5424, 6279, 10344, 17048, 24838] .e)) [5, 1605, 5424, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [5, 1605, 5429, 6275, 10344, 17048, 24838] .e) [5, 5424, 6005, 6275, 10344, 17048, 24838] .e) [5, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n .e [6, 256, 1605, 5424, 6275, 10344, 17048] .e) [6, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [6, 1605, 5424, 6275, 10344, 17048, 25502]
 (.n
 (.n
 (.n
 (.n .e [6, 1605, 5424, 6275, 10344, 17048, 26990] .e) [6, 1605, 5424, 6275, 10344, 17054, 24838] .e) [6, 1605, 5424, 6275, 10350, 17048, 24838]
 (.n
 (.n .e [6, 1605, 5424, 6279, 10344, 17048, 24838] .e) [6, 1605, 5424, 10344, 14571, 17048, 24838] .e)) [6, 1605, 5430, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [6, 1607, 5424, 6275, 10344, 17048, 24838] .e) [6, 5424, 6275, 10344, 17048, 18141, 24838] .e) [8, 96, 1605, 5424, 6275, 17048, 24838]
 (.n
 (.n .e [8, 144, 1605, 5424, 6275, 10344, 24838] .e) [8, 1605, 5424, 6275, 10344, 17048, 24838] .e)))) [8, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 17048, 24846] .e) [8, 1605, 5424, 6275, 10344, 17048, 24854]
 (.n .e [8, 1605, 5424, 6275, 10344, 17048, 24870] .e)) [8, 1605, 5424, 6275, 10344, 17048, 24902]
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 17048, 24966] .e) [8, 1605, 5424, 6275, 10344, 17049, 24838] .e)) [8, 1605, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 17052, 24838] .e) [8, 1605, 5424, 6275, 10344, 17080, 24838] .e) [8, 1605, 5424, 6275, 10344, 17112, 24838]
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 17304, 24838] .e) [8, 1605, 5424, 6275, 10344, 24838, 25240] .e))) [8, 1605, 5424, 6275, 10344, 24838, 25502]
 (.n
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 24846, 25502] .e) [8, 1605, 5424, 6275, 10344, 25502, 26990] .e) [8, 1605, 5424, 6275, 10344, 25502, 30006]
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 25502, 31111] .e) [8, 1605, 5424, 6275, 10345, 17048, 24838] .e)) [8, 1605, 5424, 6275, 10346, 17048, 24838]
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 10348, 17048, 24838] .e) [8, 1605, 5424, 6275, 10360, 17048, 24838] .e) [8, 1605, 5424, 6275, 10472, 17048, 24838]
 (.n
 (.n .e [8, 1605, 5424, 6275, 10600, 17048, 24838] .e) [8, 1605, 5424, 6275, 17048, 24838, 26728] .e))))))

def T6aaabb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 17048, 24846, 26990] .e) [8, 1605, 5424, 6275, 17048, 25502, 26990]
 (.n .e [8, 1605, 5424, 6275, 17048, 26439, 26990] .e)) [8, 1605, 5424, 6275, 17048, 26990, 30006]
 (.n
 (.n .e [8, 1605, 5424, 6275, 24838, 25502, 26990] .e) [8, 1605, 5424, 6275, 25502, 26990] .e)) [8, 1605, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6283, 10344, 17048, 24838] .e) [8, 1605, 5424, 6283, 10344, 17048, 24846] .e) [8, 1605, 5424, 6283, 10344, 24838, 25502]
 (.n
 (.n .e [8, 1605, 5424, 6283, 17048, 24838, 26990] .e) [8, 1605, 5424, 6291, 10344, 17048, 24838] .e))) [8, 1605, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6339, 10344, 17048, 24838] .e) [8, 1605, 5424, 6531, 10344, 17048, 24838] .e) [8, 1605, 5425, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [8, 1605, 5426, 6275, 10344, 17048, 24838] .e) [8, 1605, 5428, 6275, 10344, 17048, 24838] .e)) [8, 1605, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [8, 1605, 5432, 6275, 10344, 17048, 24846] .e) [8, 1605, 5432, 6275, 10344, 24838, 25502] .e) [8, 1605, 5432, 6275, 17048, 24838, 26990]
 (.n
 (.n .e [8, 1605, 5432, 6283, 10344, 17048, 24838] .e) [8, 1605, 5488, 6275, 10344, 17048, 24838] .e)))) [8, 1605, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [8, 1607, 5424, 6275, 10344, 17048, 24838] .e) [8, 1613, 5424, 6275, 10344, 17048, 24838]
 (.n .e [8, 1613, 5424, 6275, 10344, 17048, 24846] .e)) [8, 1613, 5424, 6275, 10344, 24838, 25502]
 (.n
 (.n .e [8, 1613, 5424, 6275, 17048, 24838, 26990] .e) [8, 1613, 5424, 6283, 10344, 17048, 24838] .e)) [8, 1613, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [8, 1621, 5424, 6275, 10344, 17048, 24838] .e) [8, 1637, 5424, 6275, 10344, 17048, 24838] .e) [8, 1733, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [8, 1861, 5424, 6275, 10344, 17048, 24838] .e) [9, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [10, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [12, 1605, 5424, 6275, 10344, 17048, 24838] .e) [16, 136, 1605, 5424, 6275, 10344, 24838] .e) [16, 288, 1605, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 24838] .e) [16, 1605, 5424, 6275, 10344, 17048, 24839] .e)) [16, 1605, 5424, 6275, 10344, 17048, 24846]
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 24854] .e) [16, 1605, 5424, 6275, 10344, 17048, 24870] .e) [16, 1605, 5424, 6275, 10344, 17048, 24902]
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 24966] .e) [16, 1605, 5424, 6275, 10344, 17049, 24838] .e))))) [16, 1605, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 17052, 24838] .e) [16, 1605, 5424, 6275, 10344, 17080, 24838]
 (.n .e [16, 1605, 5424, 6275, 10344, 17112, 24838] .e)) [16, 1605, 5424, 6275, 10344, 17304, 24838]
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 18072, 24838] .e) [16, 1605, 5424, 6275, 10344, 18141, 24838] .e)) [16, 1605, 5424, 6275, 10344, 18141, 24854]
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6275, 10345, 17048, 24838] .e) [16, 1605, 5424, 6275, 10346, 17048, 24838] .e) [16, 1605, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n .e [16, 1605, 5424, 6275, 10360, 17048, 24838] .e) [16, 1605, 5424, 6275, 10360, 17048, 24854] .e))) [16, 1605, 5424, 6275, 10360, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6275, 10472, 17048, 24838] .e) [16, 1605, 5424, 6275, 10600, 17048, 24838] .e) [16, 1605, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n .e [16, 1605, 5424, 6283, 10344, 17048, 24838] .e) [16, 1605, 5424, 6291, 10344, 17048, 24838] .e)) [16, 1605, 5424, 6291, 10344, 17048, 24854]
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6291, 10344, 18141, 24838] .e) [16, 1605, 5424, 6291, 10360, 17048, 24838] .e) [16, 1605, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n .e [16, 1605, 5424, 6339, 10344, 17048, 24838] .e) [16, 1605, 5424, 6531, 10344, 17048, 24838] .e)))) [16, 1605, 5425, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [16, 1605, 5426, 6275, 10344, 17048, 24838] .e) [16, 1605, 5428, 6275, 10344, 17048, 24838]
 (.n .e [16, 1605, 5432, 6275, 10344, 17048, 24838] .e)) [16, 1605, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [16, 1605, 5552, 6275, 10344, 17048, 24838] .e) [16, 1605, 5936, 6275, 10344, 17048, 24838] .e)) [16, 1605, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [16, 1605, 6005, 6275, 10344, 17048, 24854] .e) [16, 1605, 6005, 6275, 10344, 18141, 24838] .e) [16, 1605, 6005, 6275, 10360, 17048, 24838]
 (.n
 (.n .e [16, 1605, 6005, 6291, 10344, 17048, 24838] .e) [16, 1607, 5424, 6275, 10344, 17048, 24838] .e))) [16, 1613, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [16, 1621, 5424, 6275, 10344, 17048, 24838] .e) [16, 1621, 5424, 6275, 10344, 17048, 24854] .e) [16, 1621, 5424, 6275, 10344, 18141, 24838]
 (.n
 (.n .e [16, 1621, 5424, 6275, 10360, 17048, 24838] .e) [16, 1621, 5424, 6291, 10344, 17048, 24838] .e)) [16, 1621, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [16, 1637, 5424, 6275, 10344, 17048, 24838] .e) [16, 1733, 5424, 6275, 10344, 17048, 24838] .e) [16, 1861, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [16, 5424, 6005, 6275, 10344, 18141, 24838] .e) [16, 5424, 6275, 7879, 10344, 18141, 24838] .e))))))

def T6aaab : T := .n T6aaaba [8, 1605, 5424, 6275, 17048, 24838, 26990] T6aaabb

def T6aaa : T := .n T6aaaa [4, 1605, 5424, 6275, 10344, 17080, 24838] T6aaab

def T6aabaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [16, 6005, 6275, 10344, 11885, 17048, 24838] .e) [16, 6005, 6275, 10344, 17048, 18141, 24838]
 (.n .e [16, 6005, 6275, 10344, 17048, 24838, 26439] .e)) [16, 6005, 6275, 10344, 18141, 24838]
 (.n
 (.n .e [17, 1605, 5424, 6275, 10344, 17048, 24838] .e) [18, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [20, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [24, 128, 1605, 5424, 6275, 10344, 24838] .e) [24, 1605, 5424, 6275, 10344, 17048, 24838] .e) [24, 1605, 5424, 6275, 10344, 17048, 24862]
 (.n
 (.n .e [24, 1605, 5424, 6275, 10344, 18141, 24838] .e) [24, 1605, 5424, 6275, 10344, 24838, 25502] .e))) [24, 1605, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [24, 1605, 5424, 6275, 17048, 24838, 26990] .e) [24, 1605, 5424, 6299, 10344, 17048, 24838] .e) [24, 1605, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [24, 1605, 6005, 6275, 10344, 17048, 24838] .e) [24, 1629, 5424, 6275, 10344, 17048, 24838] .e)) [32, 72, 1605, 5424, 6275, 17048, 24838]
 (.n
 (.n
 (.n .e [32, 272, 1605, 6275, 10344, 17048, 24838] .e) [32, 1605, 5424, 6275, 10344, 17048, 24838] .e) [32, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n .e [32, 1605, 5424, 6275, 10344, 17048, 24846] .e) [32, 1605, 5424, 6275, 10344, 17048, 24854] .e)))) [32, 1605, 5424, 6275, 10344, 17048, 24870]
 (.n
 (.n
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6275, 10344, 17048, 24902] .e) [32, 1605, 5424, 6275, 10344, 17048, 24966]
 (.n .e [32, 1605, 5424, 6275, 10344, 17049, 24838] .e)) [32, 1605, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [32, 1605, 5424, 6275, 10344, 17052, 24838] .e) [32, 1605, 5424, 6275, 10344, 17080, 24838] .e)) [32, 1605, 5424, 6275, 10344, 17080, 24870]
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6275, 10344, 17112, 24838] .e) [32, 1605, 5424, 6275, 10344, 17304, 24838] .e) [32, 1605, 5424, 6275, 10345, 17048, 24838]
 (.n
 (.n .e [32, 1605, 5424, 6275, 10346, 17048, 24838] .e) [32, 1605, 5424, 6275, 10348, 17048, 24838] .e))) [32, 1605, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6275, 10472, 17048, 24838] .e) [32, 1605, 5424, 6275, 10600, 17048, 24838] .e) [32, 1605, 5424, 6275, 14440, 17048, 24838]
 (.n
 (.n .e [32, 1605, 5424, 6275, 14571, 17048, 24838] .e) [32, 1605, 5424, 6275, 14571, 17048, 24870] .e)) [32, 1605, 5424, 6275, 14571, 17080, 24838]
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6279, 10344, 17048, 24838] .e) [32, 1605, 5424, 6283, 10344, 17048, 24838] .e) [32, 1605, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [32, 1605, 5424, 6307, 10344, 17048, 24838] .e) [32, 1605, 5424, 6307, 10344, 17048, 24870] .e))))) [32, 1605, 5424, 6307, 10344, 17080, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6307, 14571, 17048, 24838] .e) [32, 1605, 5424, 6339, 10344, 17048, 24838]
 (.n .e [32, 1605, 5424, 6531, 10344, 17048, 24838] .e)) [32, 1605, 5424, 7603, 14571, 17048, 24838]
 (.n
 (.n .e [32, 1605, 5424, 7879, 14571, 17048, 24838] .e) [32, 1605, 5424, 14571, 17048, 23195, 24838] .e)) [32, 1605, 5425, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [32, 1605, 5426, 6275, 10344, 17048, 24838] .e) [32, 1605, 5428, 6275, 10344, 17048, 24838] .e) [32, 1605, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [32, 1605, 5488, 6275, 10344, 17048, 24838] .e) [32, 1605, 5552, 6275, 10344, 17048, 24838] .e))) [32, 1605, 6275, 7472, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [32, 1605, 6275, 7603, 10344, 17048, 24838] .e) [32, 1605, 6275, 7603, 10344, 17048, 24870] .e) [32, 1605, 6275, 7603, 10344, 17080, 24838]
 (.n
 (.n .e [32, 1605, 6275, 7603, 14571, 17048, 24838] .e) [32, 1605, 6307, 7603, 10344, 17048, 24838] .e)) [32, 1605, 7603, 10344, 14571, 17048, 24838]
 (.n
 (.n
 (.n .e [32, 1605, 7603, 10344, 17048, 23195, 24838] .e) [32, 1605, 7603, 10344, 17048, 24838, 31111] .e) [32, 1605, 7603, 14571, 17048, 24838]
 (.n
 (.n .e [32, 1607, 5424, 6275, 10344, 17048, 24838] .e) [32, 1613, 5424, 6275, 10344, 17048, 24838] .e)))) [32, 1621, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [32, 1637, 5424, 6275, 10344, 17048, 24838] .e) [32, 1637, 5424, 6275, 10344, 17048, 24870]
 (.n .e [32, 1637, 5424, 6275, 10344, 17080, 24838] .e)) [32, 1637, 5424, 6275, 14571, 17048, 24838]
 (.n
 (.n .e [32, 1637, 5424, 6307, 10344, 17048, 24838] .e) [32, 1637, 6275, 7603, 10344, 17048, 24838] .e)) [32, 1733, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [32, 1861, 5424, 6275, 10344, 17048, 24838] .e) [33, 1605, 5424, 6275, 10344, 17048, 24838] .e) [34, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [36, 1605, 5424, 6275, 10344, 17048, 24838] .e) [40, 64, 1605, 5424, 6275, 17048, 24838] .e))) [40, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [40, 1605, 5424, 6275, 10344, 17048, 24878] .e) [40, 1605, 5424, 6275, 10344, 17080, 24838] .e) [40, 1605, 5424, 6275, 10344, 24838, 25502]
 (.n
 (.n .e [40, 1605, 5424, 6275, 14571, 17048, 24838] .e) [40, 1605, 5424, 6275, 17048, 24838, 26990] .e)) [40, 1605, 5424, 6315, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [40, 1605, 5432, 6275, 10344, 17048, 24838] .e) [40, 1605, 6275, 7603, 10344, 17048, 24838] .e) [40, 1645, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [48, 256, 1605, 6275, 10344, 17048, 24838] .e) [48, 1605, 5424, 6275, 10344, 17048, 24838] .e))))))

def T6aabab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [48, 1605, 5424, 6275, 10344, 17080, 24838] .e) [48, 1605, 5424, 6275, 10344, 18141, 24838]
 (.n .e [48, 1605, 5424, 6275, 10360, 17048, 24838] .e)) [48, 1605, 5424, 6275, 14571, 17048, 24838]
 (.n
 (.n .e [48, 1605, 5424, 6323, 10344, 17048, 24838] .e) [48, 1605, 6005, 6275, 10344, 17048, 24838] .e)) [48, 1605, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [48, 1653, 5424, 6275, 10344, 17048, 24838] .e) [64, 1605, 5424, 6275, 10344, 17048, 24838] .e) [64, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n .e [64, 1605, 5424, 6275, 10344, 17048, 24846] .e) [64, 1605, 5424, 6275, 10344, 17048, 24854] .e))) [64, 1605, 5424, 6275, 10344, 17048, 24870]
 (.n
 (.n
 (.n
 (.n .e [64, 1605, 5424, 6275, 10344, 17048, 24902] .e) [64, 1605, 5424, 6275, 10344, 17048, 24966] .e) [64, 1605, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [64, 1605, 5424, 6275, 10344, 17050, 24838] .e) [64, 1605, 5424, 6275, 10344, 17052, 24838] .e)) [64, 1605, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n
 (.n .e [64, 1605, 5424, 6275, 10344, 17112, 24838] .e) [64, 1605, 5424, 6275, 10344, 17112, 24902] .e) [64, 1605, 5424, 6275, 10344, 17304, 24838]
 (.n
 (.n .e [64, 1605, 5424, 6275, 10345, 17048, 24838] .e) [64, 1605, 5424, 6275, 10346, 17048, 24838] .e)))) [64, 1605, 5424, 6275, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [64, 1605, 5424, 6275, 10360, 17048, 24838] .e) [64, 1605, 5424, 6275, 10472, 17048, 24838]
 (.n .e [64, 1605, 5424, 6275, 10600, 17048, 24838] .e)) [64, 1605, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n .e [64, 1605, 5424, 6283, 10344, 17048, 24838] .e) [64, 1605, 5424, 6291, 10344, 17048, 24838] .e)) [64, 1605, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [64, 1605, 5424, 6339, 10344, 17048, 24838] .e) [64, 1605, 5424, 6339, 10344, 17048, 24902] .e) [64, 1605, 5424, 6339, 10344, 17112, 24838]
 (.n
 (.n .e [64, 1605, 5424, 6531, 10344, 17048, 24838] .e) [64, 1605, 5425, 6275, 10344, 17048, 24838] .e))) [64, 1605, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [64, 1605, 5428, 6275, 10344, 17048, 24838] .e) [64, 1605, 5432, 6275, 10344, 17048, 24838] .e) [64, 1605, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [64, 1605, 5488, 6275, 10344, 17048, 24902] .e) [64, 1605, 5488, 6275, 10344, 17112, 24838] .e)) [64, 1605, 5488, 6339, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [64, 1605, 5552, 6275, 10344, 17048, 24838] .e) [64, 1607, 5424, 6275, 10344, 17048, 24838] .e) [64, 1613, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [64, 1621, 5424, 6275, 10344, 17048, 24838] .e) [64, 1637, 5424, 6275, 10344, 17048, 24838] .e))))) [64, 1733, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [64, 1861, 5424, 6275, 10344, 17048, 24838] .e) [65, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [65, 1605, 5424, 6275, 10344, 17048, 24903] .e)) [65, 1605, 5424, 6275, 10344, 17113, 24838]
 (.n
 (.n .e [65, 1605, 5424, 6275, 10345, 17048, 24838] .e) [65, 1605, 5424, 6339, 10344, 17048, 24838] .e)) [65, 1605, 5424, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [65, 1605, 5489, 6275, 10344, 17048, 24838] .e) [65, 5424, 6005, 6275, 10344, 17048, 24838] .e) [65, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n
 (.n .e [65, 5424, 7879, 10344, 14571, 17048, 24838] .e) [66, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [68, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [68, 1605, 5424, 6275, 10344, 17048, 24902] .e) [68, 1605, 5424, 6275, 10344, 17048, 25502] .e) [68, 1605, 5424, 6275, 10344, 17116, 24838]
 (.n
 (.n .e [68, 1605, 5424, 6275, 10348, 17048, 24838] .e) [68, 1605, 5424, 6343, 10344, 17048, 24838] .e)) [68, 1605, 5492, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [68, 5424, 6275, 10344, 17048, 18141, 24838] .e) [68, 5424, 6275, 10344, 17048, 24838, 26439] .e) [68, 5424, 6275, 10344, 17048, 26439, 26990]
 (.n
 (.n .e [69, 1605, 5424, 6275, 10344, 17048, 24838] .e) [69, 5424, 6275, 10344, 14571, 17048, 24838] .e)))) [69, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [69, 5424, 6275, 10344, 17048, 24838, 26990] .e) [69, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n .e [69, 5424, 6275, 10344, 17048, 24838, 31215] .e)) [72, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [72, 1605, 5424, 6275, 10344, 17048, 24910] .e) [72, 1605, 5424, 6275, 10344, 17112, 24838] .e)) [72, 1605, 5424, 6275, 10344, 24838, 25502]
 (.n
 (.n
 (.n .e [72, 1605, 5424, 6275, 17048, 24838, 26990] .e) [72, 1605, 5424, 6275, 17048, 24838, 27384] .e) [72, 1605, 5424, 6275, 18141, 24838, 27384]
 (.n
 (.n .e [72, 1605, 5424, 6347, 10344, 17048, 24838] .e) [72, 1605, 5496, 6275, 10344, 17048, 24838] .e))) [72, 1613, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [80, 1605, 5424, 6275, 10344, 17048, 24838] .e) [96, 1605, 5424, 6275, 10344, 17048, 24838] .e) [96, 1605, 5424, 6275, 10344, 17048, 24934]
 (.n
 (.n .e [96, 1605, 5424, 6275, 10344, 17144, 24838] .e) [96, 1605, 5424, 6275, 14571, 17048, 24838] .e)) [96, 1605, 5424, 6275, 15736, 17048, 24838]
 (.n
 (.n
 (.n .e [96, 1605, 5424, 6371, 10344, 17048, 24838] .e) [96, 1605, 5488, 6275, 10344, 17048, 24838] .e) [96, 1605, 6005, 6275, 15736, 17048, 24838]
 (.n
 (.n .e [96, 1605, 6275, 7603, 10344, 17048, 24838] .e) [96, 1637, 5424, 6275, 10344, 17048, 24838] .e))))))

def T6aaba : T := .n T6aabaa [48, 1605, 5424, 6275, 10344, 17048, 24886] T6aabab

def T6aabba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [104, 1605, 5424, 6275, 10344, 17048, 24838] .e) [104, 1605, 5424, 6275, 17048, 18141, 24838]
 (.n .e [104, 1605, 5424, 6275, 17048, 22456, 24838] .e)) [104, 1605, 5424, 6275, 17048, 22525, 24838]
 (.n
 (.n .e [104, 1605, 5424, 6275, 17048, 24838] .e) [128, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [128, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 24846] .e) [128, 1605, 5424, 6275, 10344, 17048, 24854] .e) [128, 1605, 5424, 6275, 10344, 17048, 24870]
 (.n
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 24902] .e) [128, 1605, 5424, 6275, 10344, 17048, 24966] .e))) [128, 1605, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n
 (.n
 (.n .e [128, 1605, 5424, 6275, 10344, 17050, 24838] .e) [128, 1605, 5424, 6275, 10344, 17052, 24838] .e) [128, 1605, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n .e [128, 1605, 5424, 6275, 10344, 17112, 24838] .e) [128, 1605, 5424, 6275, 10344, 17304, 24838] .e)) [128, 1605, 5424, 6275, 10345, 17048, 24838]
 (.n
 (.n
 (.n .e [128, 1605, 5424, 6275, 10346, 17048, 24838] .e) [128, 1605, 5424, 6275, 10348, 17048, 24838] .e) [128, 1605, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n .e [128, 1605, 5424, 6275, 10472, 17048, 24838] .e) [128, 1605, 5424, 6275, 10472, 17048, 24966] .e)))) [128, 1605, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [128, 1605, 5424, 6279, 10344, 17048, 24838] .e) [128, 1605, 5424, 6283, 10344, 17048, 24838]
 (.n .e [128, 1605, 5424, 6291, 10344, 17048, 24838] .e)) [128, 1605, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n .e [128, 1605, 5424, 6339, 10344, 17048, 24838] .e) [128, 1605, 5424, 6531, 10344, 17048, 24838] .e)) [128, 1605, 5425, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [128, 1605, 5426, 6275, 10344, 17048, 24838] .e) [128, 1605, 5428, 6275, 10344, 17048, 24838] .e) [128, 1605, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [128, 1605, 5488, 6275, 10344, 17048, 24838] .e) [128, 1605, 5552, 6275, 10344, 17048, 24838] .e))) [128, 1605, 5552, 6275, 10344, 17048, 24966]
 (.n
 (.n
 (.n
 (.n .e [128, 1605, 5552, 6275, 10472, 17048, 24838] .e) [128, 1607, 5424, 6275, 10344, 17048, 24838] .e) [128, 1613, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [128, 1621, 5424, 6275, 10344, 17048, 24838] .e) [128, 1637, 5424, 6275, 10344, 17048, 24838] .e)) [128, 1733, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [128, 1733, 5424, 6275, 10344, 17048, 24966] .e) [128, 1733, 5424, 6275, 10472, 17048, 24838] .e) [128, 1733, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [128, 1861, 5424, 6275, 10344, 17048, 24838] .e) [129, 1605, 5424, 6275, 10344, 17048, 24838] .e))))) [129, 1605, 5424, 6275, 10344, 17048, 24967]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [129, 1605, 5424, 6275, 10344, 17049, 24838] .e) [129, 1605, 5424, 6275, 10473, 17048, 24838]
 (.n .e [129, 1605, 5424, 7603, 10344, 17048, 24838] .e)) [129, 1605, 5424, 7879, 10344, 17048, 24838]
 (.n
 (.n .e [129, 1605, 5553, 6275, 10344, 17048, 24838] .e) [129, 1733, 5424, 6275, 10344, 17048, 24838] .e)) [129, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [129, 5424, 7879, 10344, 17048, 18141, 24838] .e) [130, 1605, 5424, 6275, 10344, 17048, 24838] .e) [130, 1605, 5424, 6275, 10344, 17048, 24966]
 (.n
 (.n .e [130, 1605, 5424, 6275, 10344, 17048, 26990] .e) [130, 1605, 5424, 6275, 10344, 17050, 24838] .e))) [130, 1605, 5424, 6275, 10474, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [130, 1605, 5424, 10344, 14571, 17048, 24838] .e) [130, 1605, 5424, 10344, 17048, 24838, 31111] .e) [130, 1605, 5424, 10344, 17048, 25502, 31111]
 (.n
 (.n .e [130, 1605, 5554, 6275, 10344, 17048, 24838] .e) [130, 1735, 5424, 6275, 10344, 17048, 24838] .e)) [131, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [131, 1605, 5424, 10344, 17048, 18141, 24838] .e) [131, 1605, 5424, 10344, 17048, 24838] .e) [131, 1605, 5424, 10344, 17048, 24838, 25502]
 (.n
 (.n .e [131, 1605, 5424, 10344, 17048, 24838, 26439] .e) [131, 1605, 5424, 10344, 17048, 24838, 26591] .e)))) [132, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [136, 1605, 5424, 6275, 10344, 17048, 24838] .e) [136, 1605, 5424, 6275, 10344, 17048, 24974]
 (.n .e [136, 1605, 5424, 6275, 10344, 24838, 25502] .e)) [136, 1605, 5424, 6275, 10344, 24838, 27384]
 (.n
 (.n .e [136, 1605, 5424, 6275, 10472, 17048, 24838] .e) [136, 1605, 5424, 6275, 14571, 24838, 27384] .e)) [136, 1605, 5424, 6275, 17048, 24838, 26990]
 (.n
 (.n
 (.n .e [136, 1605, 5424, 6283, 10344, 17048, 24838] .e) [136, 1605, 5560, 6275, 10344, 17048, 24838] .e) [136, 1741, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [144, 1605, 5424, 6275, 10344, 17048, 24838] .e) [144, 1605, 5424, 6275, 10344, 17048, 24982] .e))) [144, 1605, 5424, 6275, 10344, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [144, 1605, 5424, 6275, 10344, 22456, 24838] .e) [144, 1605, 5424, 6275, 10488, 17048, 24838] .e) [144, 1605, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [144, 1605, 5552, 6275, 10344, 17048, 24838] .e) [144, 1605, 6005, 6275, 10344, 17048, 24838] .e)) [144, 1605, 6275, 7603, 10344, 22456, 24838]
 (.n
 (.n
 (.n .e [144, 1749, 5424, 6275, 10344, 17048, 24838] .e) [152, 1605, 5424, 6275, 7603, 10344, 24838] .e) [152, 1605, 5424, 6275, 10344, 14571, 24838]
 (.n
 (.n .e [152, 1605, 5424, 6275, 10344, 15736, 24838] .e) [152, 1605, 5424, 6275, 10344, 15867, 24838] .e))))))

def T6aabbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [152, 1605, 5424, 6275, 10344, 24838] .e) [160, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [192, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [201, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [256, 1605, 5424, 6275, 10344, 17048, 24838] .e) [256, 1605, 5424, 6275, 10344, 17048, 24839] .e)) [256, 1605, 5424, 6275, 10344, 17048, 24846]
 (.n
 (.n
 (.n .e [256, 1605, 5424, 6275, 10344, 17048, 24854] .e) [256, 1605, 5424, 6275, 10344, 17048, 24870] .e) [256, 1605, 5424, 6275, 10344, 17048, 24902]
 (.n
 (.n .e [256, 1605, 5424, 6275, 10344, 17048, 24966] .e) [256, 1605, 5424, 6275, 10344, 17049, 24838] .e))) [256, 1605, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n
 (.n
 (.n .e [256, 1605, 5424, 6275, 10344, 17052, 24838] .e) [256, 1605, 5424, 6275, 10344, 17080, 24838] .e) [256, 1605, 5424, 6275, 10344, 17112, 24838]
 (.n
 (.n .e [256, 1605, 5424, 6275, 10344, 17304, 24838] .e) [256, 1605, 5424, 6275, 10345, 17048, 24838] .e)) [256, 1605, 5424, 6275, 10346, 17048, 24838]
 (.n
 (.n
 (.n .e [256, 1605, 5424, 6275, 10348, 17048, 24838] .e) [256, 1605, 5424, 6275, 10360, 17048, 24838] .e) [256, 1605, 5424, 6275, 10472, 17048, 24838]
 (.n
 (.n .e [256, 1605, 5424, 6275, 10600, 17048, 24838] .e) [256, 1605, 5424, 6275, 10600, 17304, 24838] .e)))) [256, 1605, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [256, 1605, 5424, 6283, 10344, 17048, 24838] .e) [256, 1605, 5424, 6291, 10344, 17048, 24838]
 (.n .e [256, 1605, 5424, 6307, 10344, 17048, 24838] .e)) [256, 1605, 5424, 6339, 10344, 17048, 24838]
 (.n
 (.n .e [256, 1605, 5424, 6531, 10344, 17048, 24838] .e) [256, 1605, 5424, 6531, 10344, 17304, 24838] .e)) [256, 1605, 5424, 6531, 10600, 17048, 24838]
 (.n
 (.n
 (.n .e [256, 1605, 5425, 6275, 10344, 17048, 24838] .e) [256, 1605, 5426, 6275, 10344, 17048, 24838] .e) [256, 1605, 5428, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [256, 1605, 5432, 6275, 10344, 17048, 24838] .e) [256, 1605, 5488, 6275, 10344, 17048, 24838] .e))) [256, 1605, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [256, 1607, 5424, 6275, 10344, 17048, 24838] .e) [256, 1613, 5424, 6275, 10344, 17048, 24838] .e) [256, 1621, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [256, 1637, 5424, 6275, 10344, 17048, 24838] .e) [256, 1733, 5424, 6275, 10344, 17048, 24838] .e)) [256, 1861, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [256, 1861, 5424, 6275, 10344, 17304, 24838] .e) [256, 1861, 5424, 6275, 10600, 17048, 24838] .e) [256, 1861, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [257, 1605, 5424, 6275, 10344, 17048, 24838] .e) [258, 1605, 5424, 6275, 10344, 17048, 24838] .e))))) [258, 1605, 5424, 6275, 10344, 17048, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [258, 1605, 5424, 6275, 10344, 17048, 31111] .e) [258, 1605, 5424, 6275, 10344, 17306, 24838]
 (.n .e [258, 1605, 5424, 6275, 10602, 17048, 24838] .e)) [258, 1605, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [258, 1605, 5424, 7603, 10344, 17048, 31111] .e) [258, 1605, 5424, 10344, 14571, 17048, 24838] .e)) [258, 1605, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [258, 1863, 5424, 6275, 10344, 17048, 24838] .e) [260, 1605, 5424, 6275, 10344, 17048, 24838] .e) [260, 1605, 5424, 6275, 10344, 17048, 25502]
 (.n
 (.n .e [260, 1605, 5424, 6275, 10344, 17048, 26439] .e) [260, 1605, 5424, 6275, 10344, 17308, 24838] .e))) [260, 1605, 5424, 6275, 10604, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [260, 1605, 5424, 6535, 10344, 17048, 24838] .e) [260, 1605, 5428, 6275, 10344, 17048, 24838] .e) [260, 1861, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [260, 5424, 6005, 6275, 10344, 17048, 26439] .e) [260, 5424, 6275, 10344, 17048, 18141, 24838] .e)) [262, 1605, 5424, 6005, 6275, 10344, 17048]
 (.n
 (.n
 (.n .e [262, 1605, 5424, 6275, 7603, 10344, 17048] .e) [262, 1605, 5424, 6275, 7879, 10344, 17048] .e) [262, 1605, 5424, 6275, 8183, 10344, 17048]
 (.n
 (.n .e [262, 1605, 5424, 6275, 10344, 17048] .e) [262, 1605, 5424, 6275, 10344, 17048, 24838] .e)))) [264, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [272, 1605, 5424, 6275, 10344, 17048, 24838] .e) [272, 1605, 5424, 6275, 10344, 17048, 24854]
 (.n .e [272, 1605, 5424, 6275, 10344, 17304, 24838] .e)) [272, 1605, 5424, 6275, 10344, 18141, 24838]
 (.n
 (.n .e [272, 1605, 5424, 6275, 10616, 17048, 24838] .e) [272, 1605, 5424, 6547, 10344, 17048, 24838] .e)) [272, 1605, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [272, 1605, 6275, 10344, 17048, 22456, 24838] .e) [272, 1605, 6275, 10344, 22456, 24838, 25502] .e) [272, 1877, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [288, 1605, 5424, 6275, 10344, 17048, 24838] .e) [288, 1605, 5424, 6275, 10344, 17048, 24870] .e))) [288, 1605, 5424, 6275, 10344, 17336, 24838]
 (.n
 (.n
 (.n
 (.n .e [288, 1605, 5424, 6275, 10600, 17048, 24838] .e) [288, 1605, 5424, 6275, 14571, 17048, 24838] .e) [288, 1605, 5424, 6563, 10344, 17048, 24838]
 (.n
 (.n .e [288, 1605, 6275, 7603, 10344, 17048, 24838] .e) [288, 1605, 6275, 10344, 15736, 17048, 24838] .e)) [288, 1605, 6275, 15736, 17048, 24838, 26990]
 (.n
 (.n
 (.n .e [288, 1893, 5424, 6275, 10344, 17048, 24838] .e) [304, 1605, 5424, 6275, 10344, 17048, 24838] .e) [304, 1605, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [304, 1605, 6275, 10344, 17048, 24838, 25502] .e) [304, 1605, 6275, 10344, 17048, 24838, 26990] .e))))))

def T6aabb : T := .n T6aabba [152, 1605, 5424, 6275, 10344, 17048, 24838] T6aabbb

def T6aab : T := .n T6aaba [104, 1605, 5424, 6005, 6275, 17048, 24838] T6aabb

def T6aa : T := .n T6aaa [16, 5424, 6275, 10344, 11885, 18141, 24838] T6aab

def T6abaaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [304, 1605, 6275, 10344, 17048, 24838, 27646] .e) [320, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [356, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [384, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [402, 1605, 5424, 6275, 10344, 17048, 24838] .e) [512, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [512, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 17048, 24846] .e) [512, 1605, 5424, 6275, 10344, 17048, 24854] .e) [512, 1605, 5424, 6275, 10344, 17048, 24870]
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 17048, 24902] .e) [512, 1605, 5424, 6275, 10344, 17048, 24966] .e))) [512, 1605, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 17050, 24838] .e) [512, 1605, 5424, 6275, 10344, 17052, 24838] .e) [512, 1605, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 17112, 24838] .e) [512, 1605, 5424, 6275, 10344, 17304, 24838] .e)) [512, 1605, 5424, 6275, 10345, 17048, 24838]
 (.n
 (.n
 (.n .e [512, 1605, 5424, 6275, 10346, 17048, 24838] .e) [512, 1605, 5424, 6275, 10348, 17048, 24838] .e) [512, 1605, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n .e [512, 1605, 5424, 6275, 10472, 17048, 24838] .e) [512, 1605, 5424, 6275, 10600, 17048, 24838] .e)))) [512, 1605, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [512, 1605, 5424, 6283, 10344, 17048, 24838] .e) [512, 1605, 5424, 6291, 10344, 17048, 24838]
 (.n .e [512, 1605, 5424, 6307, 10344, 17048, 24838] .e)) [512, 1605, 5424, 6339, 10344, 17048, 24838]
 (.n
 (.n .e [512, 1605, 5424, 6531, 10344, 17048, 24838] .e) [512, 1605, 5425, 6275, 10344, 17048, 24838] .e)) [512, 1605, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [512, 1605, 5428, 6275, 10344, 17048, 24838] .e) [512, 1605, 5432, 6275, 10344, 17048, 24838] .e) [512, 1605, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [512, 1605, 5552, 6275, 10344, 17048, 24838] .e) [512, 1607, 5424, 6275, 10344, 17048, 24838] .e))) [512, 1613, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [512, 1621, 5424, 6275, 10344, 17048, 24838] .e) [512, 1637, 5424, 6275, 10344, 17048, 24838] .e) [512, 1733, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [512, 1861, 5424, 6275, 10344, 17048, 24838] .e) [513, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [513, 1605, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n
 (.n .e [513, 1605, 5424, 7603, 10344, 17048, 24838] .e) [513, 5424, 6005, 6275, 10344, 17048, 24838] .e) [514, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [516, 1605, 5424, 6275, 10344, 17048, 24838] .e) [516, 1605, 5424, 6275, 10344, 17052, 24838] .e))))) [516, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [516, 5424, 6275, 10344, 18141, 24838, 25502] .e) [517, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [520, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [520, 1605, 5424, 6275, 10344, 24838, 25502]
 (.n
 (.n .e [520, 1605, 5424, 6275, 17048, 24838, 26990] .e) [520, 1613, 5424, 6275, 10344, 17048, 24838] .e)) [528, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [528, 1605, 5424, 6275, 10344, 18141, 24838] .e) [528, 1621, 5424, 6275, 10344, 17048, 24838] .e) [528, 5424, 6005, 6275, 10344, 18141, 24838]
 (.n
 (.n .e [536, 1605, 5424, 6275, 10344, 17048, 24838] .e) [544, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [576, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [576, 1605, 5424, 6275, 10344, 17112, 24838] .e) [577, 1605, 5424, 6275, 10344, 17048, 24838] .e) [580, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [624, 1605, 5424, 6275, 10344, 17048, 24838] .e) [640, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [640, 1733, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [646, 1605, 5424, 6275, 10344, 17048, 24838] .e) [648, 1605, 5424, 6275, 10344, 17048, 24838] .e) [656, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [768, 1605, 5424, 6275, 10344, 17048, 24838] .e) [788, 1605, 5424, 6275, 10344, 17048, 24838] .e)))) [1024, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10344, 17048, 24839] .e) [1024, 1605, 5424, 6275, 10344, 17048, 24846]
 (.n .e [1024, 1605, 5424, 6275, 10344, 17048, 24854] .e)) [1024, 1605, 5424, 6275, 10344, 17048, 24870]
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10344, 17048, 24902] .e) [1024, 1605, 5424, 6275, 10344, 17048, 24966] .e)) [1024, 1605, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10344, 17050, 24838] .e) [1024, 1605, 5424, 6275, 10344, 17052, 24838] .e) [1024, 1605, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10344, 17112, 24838] .e) [1024, 1605, 5424, 6275, 10344, 17304, 24838] .e))) [1024, 1605, 5424, 6275, 10345, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10346, 17048, 24838] .e) [1024, 1605, 5424, 6275, 10348, 17048, 24838] .e) [1024, 1605, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10472, 17048, 24838] .e) [1024, 1605, 5424, 6275, 10600, 17048, 24838] .e)) [1024, 1605, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1024, 1605, 5424, 6283, 10344, 17048, 24838] .e) [1024, 1605, 5424, 6291, 10344, 17048, 24838] .e) [1024, 1605, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n .e [1024, 1605, 5424, 6339, 10344, 17048, 24838] .e) [1024, 1605, 5424, 6531, 10344, 17048, 24838] .e))))))

def T6abaab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1024, 1605, 5426, 6275, 10344, 17048, 24838] .e) [1024, 1605, 5428, 6275, 10344, 17048, 24838]
 (.n .e [1024, 1605, 5432, 6275, 10344, 17048, 24838] .e)) [1024, 1605, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1024, 1605, 5552, 6275, 10344, 17048, 24838] .e) [1024, 1607, 5424, 6275, 10344, 17048, 24838] .e)) [1024, 1613, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1024, 1621, 5424, 6275, 10344, 17048, 24838] .e) [1024, 1637, 5424, 6275, 10344, 17048, 24838] .e) [1024, 1733, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1024, 1861, 5424, 6275, 10344, 17048, 24838] .e) [1025, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [1025, 1605, 5425, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1025, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1025, 6005, 6275, 7603, 10344, 17048, 24838] .e) [1026, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1028, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1028, 1605, 5424, 6275, 10344, 17048, 25502] .e)) [1028, 1605, 5428, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1028, 5424, 6275, 10344, 17048, 18141, 24838] .e) [1029, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1032, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1040, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1040, 1605, 6005, 6275, 10344, 17048, 24838] .e)))) [1040, 1621, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1040, 6005, 6275, 10344, 17048, 18141, 24838] .e) [1056, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1056, 1605, 5424, 6275, 14571, 17048, 24838] .e)) [1056, 1605, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [1056, 1637, 5424, 6275, 10344, 17048, 24838] .e) [1072, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [1088, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1088, 1605, 5488, 6275, 10344, 17048, 24838] .e) [1089, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1092, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1112, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1152, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [1169, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1280, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1280, 1861, 5424, 6275, 10344, 17048, 24838] .e) [1283, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1296, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1312, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [1536, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1537, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1540, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1576, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1600, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1605, 5424, 6275, 10344, 17048, 24838] .e))))) [1605, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 1605, 5424, 6275, 10344, 17048, 24846] .e) [1605, 1605, 5424, 6275, 10344, 17048, 24854]
 (.n .e [1605, 1605, 5424, 6275, 10344, 17048, 24870] .e)) [1605, 1605, 5424, 6275, 10344, 17048, 24902]
 (.n
 (.n .e [1605, 1605, 5424, 6275, 10344, 17048, 24966] .e) [1605, 1605, 5424, 6275, 10344, 17049, 24838] .e)) [1605, 1605, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n
 (.n .e [1605, 1605, 5424, 6275, 10344, 17052, 24838] .e) [1605, 1605, 5424, 6275, 10344, 17080, 24838] .e) [1605, 1605, 5424, 6275, 10344, 17112, 24838]
 (.n
 (.n .e [1605, 1605, 5424, 6275, 10344, 17304, 24838] .e) [1605, 1605, 5424, 6275, 10345, 17048, 24838] .e))) [1605, 1605, 5424, 6275, 10346, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 1605, 5424, 6275, 10348, 17048, 24838] .e) [1605, 1605, 5424, 6275, 10360, 17048, 24838] .e) [1605, 1605, 5424, 6275, 10472, 17048, 24838]
 (.n
 (.n .e [1605, 1605, 5424, 6275, 10600, 17048, 24838] .e) [1605, 1605, 5424, 6279, 10344, 17048, 24838] .e)) [1605, 1605, 5424, 6283, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 1605, 5424, 6291, 10344, 17048, 24838] .e) [1605, 1605, 5424, 6307, 10344, 17048, 24838] .e) [1605, 1605, 5424, 6339, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 1605, 5424, 6531, 10344, 17048, 24838] .e) [1605, 1605, 5425, 6275, 10344, 17048, 24838] .e)))) [1605, 1605, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 1605, 5428, 6275, 10344, 17048, 24838] .e) [1605, 1605, 5432, 6275, 10344, 17048, 24838]
 (.n .e [1605, 1605, 5488, 6275, 10344, 17048, 24838] .e)) [1605, 1605, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 1607, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1607, 5424, 6275, 10344, 17048, 26990] .e)) [1605, 1607, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n
 (.n .e [1605, 1607, 5424, 6275, 10346, 17048, 24838] .e) [1605, 1607, 5424, 10344, 14571, 17048, 24838] .e) [1605, 1607, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 1613, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1613, 5424, 6275, 10344, 17048, 24846] .e))) [1605, 1613, 5424, 6275, 10344, 24838, 25502]
 (.n
 (.n
 (.n
 (.n .e [1605, 1613, 5424, 6275, 17048, 24838, 26990] .e) [1605, 1613, 5424, 6283, 10344, 17048, 24838] .e) [1605, 1613, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 1621, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1621, 5424, 6275, 10344, 17048, 24854] .e)) [1605, 1621, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 1621, 5424, 6291, 10344, 17048, 24838] .e) [1605, 1629, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1637, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 1637, 5424, 6275, 10344, 17048, 24870] .e) [1605, 1637, 5424, 6275, 10344, 17080, 24838] .e))))))

def T6abaa : T := .n T6abaaa [1024, 1605, 5425, 6275, 10344, 17048, 24838] T6abaab

def T6ababa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 1637, 5424, 6307, 10344, 17048, 24838] .e) [1605, 1637, 6275, 7603, 10344, 17048, 24838]
 (.n .e [1605, 1645, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 1653, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 1733, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1733, 5424, 6275, 10344, 17048, 24966] .e)) [1605, 1733, 5424, 6275, 10472, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 1733, 5552, 6275, 10344, 17048, 24838] .e) [1605, 1735, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1741, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 1749, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1861, 5424, 6275, 10344, 17048, 24838] .e))) [1605, 1861, 5424, 6275, 10344, 17304, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 1861, 5424, 6275, 10600, 17048, 24838] .e) [1605, 1861, 5424, 6531, 10344, 17048, 24838] .e) [1605, 1863, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 1877, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1893, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10344, 17048, 24839] .e) [1605, 2048, 5424, 6275, 10344, 17048, 24846] .e) [1605, 2048, 5424, 6275, 10344, 17048, 24854]
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10344, 17048, 24870] .e) [1605, 2048, 5424, 6275, 10344, 17048, 24902] .e)))) [1605, 2048, 5424, 6275, 10344, 17048, 24966]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10344, 17049, 24838] .e) [1605, 2048, 5424, 6275, 10344, 17050, 24838]
 (.n .e [1605, 2048, 5424, 6275, 10344, 17052, 24838] .e)) [1605, 2048, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10344, 17112, 24838] .e) [1605, 2048, 5424, 6275, 10344, 17304, 24838] .e)) [1605, 2048, 5424, 6275, 10345, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10346, 17048, 24838] .e) [1605, 2048, 5424, 6275, 10348, 17048, 24838] .e) [1605, 2048, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10472, 17048, 24838] .e) [1605, 2048, 5424, 6275, 10600, 17048, 24838] .e))) [1605, 2048, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 2048, 5424, 6283, 10344, 17048, 24838] .e) [1605, 2048, 5424, 6291, 10344, 17048, 24838] .e) [1605, 2048, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 2048, 5424, 6339, 10344, 17048, 24838] .e) [1605, 2048, 5424, 6531, 10344, 17048, 24838] .e)) [1605, 2048, 5425, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 2048, 5426, 6275, 10344, 17048, 24838] .e) [1605, 2048, 5428, 6275, 10344, 17048, 24838] .e) [1605, 2048, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 2048, 5488, 6275, 10344, 17048, 24838] .e) [1605, 2048, 5552, 6275, 10344, 17048, 24838] .e))))) [1605, 2049, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 2049, 5424, 6275, 10345, 17048, 24838] .e) [1605, 2049, 5424, 7603, 10344, 17048, 24838]
 (.n .e [1605, 2050, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 2050, 5424, 6275, 10346, 17048, 24838]
 (.n
 (.n .e [1605, 2050, 5424, 10344, 14571, 17048, 24838] .e) [1605, 2050, 5424, 14571, 17048, 24838, 26990] .e)) [1605, 2051, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 2052, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2056, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2056, 5424, 6275, 10344, 24838, 25502]
 (.n
 (.n .e [1605, 2056, 5424, 6275, 17048, 24838, 26990] .e) [1605, 2056, 5424, 6283, 10344, 17048, 24838] .e))) [1605, 2064, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 2080, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2080, 5424, 6275, 14571, 17048, 24838] .e) [1605, 2080, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 2080, 5424, 7603, 14571, 17048, 24838] .e) [1605, 2088, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 2112, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 2112, 5424, 6339, 10344, 17048, 24838] .e) [1605, 2118, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2120, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 2144, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2176, 5424, 6275, 10344, 17048, 24838] .e)))) [1605, 2176, 5424, 6275, 10472, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 2177, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2178, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 2224, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 2304, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 2338, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2560, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 2569, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 2752, 5424, 6275, 10344, 17048, 24838] .e) [1605, 3072, 5424, 6275, 10344, 17048, 24838] .e) [1605, 3105, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 3653, 5424, 6275, 10344, 17048, 24838] .e) [1605, 3655, 5424, 6275, 10344, 17048, 24838] .e))) [1605, 3661, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 3685, 5424, 6275, 10344, 17048, 24838] .e) [1605, 3781, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10344, 17048, 24839] .e) [1605, 4096, 5424, 6275, 10344, 17048, 24846] .e)) [1605, 4096, 5424, 6275, 10344, 17048, 24854]
 (.n
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10344, 17048, 24870] .e) [1605, 4096, 5424, 6275, 10344, 17048, 24902] .e) [1605, 4096, 5424, 6275, 10344, 17048, 24966]
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10344, 17049, 24838] .e) [1605, 4096, 5424, 6275, 10344, 17050, 24838] .e))))))

def T6ababb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10344, 17080, 24838] .e) [1605, 4096, 5424, 6275, 10344, 17112, 24838]
 (.n .e [1605, 4096, 5424, 6275, 10344, 17304, 24838] .e)) [1605, 4096, 5424, 6275, 10345, 17048, 24838]
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10346, 17048, 24838] .e) [1605, 4096, 5424, 6275, 10348, 17048, 24838] .e)) [1605, 4096, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10472, 17048, 24838] .e) [1605, 4096, 5424, 6275, 10600, 17048, 24838] .e) [1605, 4096, 5424, 6279, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 4096, 5424, 6283, 10344, 17048, 24838] .e) [1605, 4096, 5424, 6291, 10344, 17048, 24838] .e))) [1605, 4096, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 4096, 5424, 6339, 10344, 17048, 24838] .e) [1605, 4096, 5424, 6531, 10344, 17048, 24838] .e) [1605, 4096, 5425, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 4096, 5426, 6275, 10344, 17048, 24838] .e) [1605, 4096, 5428, 6275, 10344, 17048, 24838] .e)) [1605, 4096, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 4096, 5488, 6275, 10344, 17048, 24838] .e) [1605, 4096, 5552, 6275, 10344, 17048, 24838] .e) [1605, 4097, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 4097, 5424, 7603, 10344, 17048, 24838] .e) [1605, 4097, 5425, 6275, 10344, 17048, 24838] .e)))) [1605, 4097, 6005, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 4098, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4098, 5424, 6275, 10344, 17048, 26990]
 (.n .e [1605, 4098, 5424, 10344, 14571, 17048, 24838] .e)) [1605, 4098, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 4099, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4100, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 4104, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 4112, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4112, 5424, 6275, 10344, 18141, 24838] .e) [1605, 4112, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 4112, 6005, 6275, 10344, 17048, 24838] .e) [1605, 4128, 5424, 6275, 10344, 17048, 24838] .e))) [1605, 4128, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 4128, 6275, 7603, 10344, 17048, 24838] .e) [1605, 4128, 7603, 10344, 14571, 17048, 24838] .e) [1605, 4144, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 4160, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4193, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 4224, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 4224, 5552, 6275, 10344, 17048, 24838] .e) [1605, 4225, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4226, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 4264, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4352, 5424, 6275, 10344, 17048, 24838] .e))))) [1605, 4352, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 4357, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4368, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 4384, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 4608, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 4625, 5424, 6275, 10344, 17048, 24838] .e) [1605, 5120, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 5126, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5136, 5424, 6275, 10344, 17048, 24838] .e) [1605, 5152, 5424, 6275, 10344, 17048, 24838] .e) [1605, 5376, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5424, 6275, 10344, 17048, 24839] .e))) [1605, 5424, 5424, 6275, 10344, 17048, 24846]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 24854] .e) [1605, 5424, 5424, 6275, 10344, 17048, 24870] .e) [1605, 5424, 5424, 6275, 10344, 17048, 24902]
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 24966] .e) [1605, 5424, 5424, 6275, 10344, 17049, 24838] .e)) [1605, 5424, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 17052, 24838] .e) [1605, 5424, 5424, 6275, 10344, 17080, 24838] .e) [1605, 5424, 5424, 6275, 10344, 17112, 24838]
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 17304, 24838] .e) [1605, 5424, 5424, 6275, 10345, 17048, 24838] .e)))) [1605, 5424, 5424, 6275, 10346, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10348, 17048, 24838] .e) [1605, 5424, 5424, 6275, 10360, 17048, 24838]
 (.n .e [1605, 5424, 5424, 6275, 10472, 17048, 24838] .e)) [1605, 5424, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 5424, 6279, 10344, 17048, 24838] .e) [1605, 5424, 5424, 6283, 10344, 17048, 24838] .e)) [1605, 5424, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 5424, 6307, 10344, 17048, 24838] .e) [1605, 5424, 5424, 6339, 10344, 17048, 24838] .e) [1605, 5424, 5424, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 5425, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5425, 6275, 10344, 17048, 24839] .e))) [1605, 5424, 5425, 6275, 10344, 17049, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 5425, 6275, 10345, 17048, 24838] .e) [1605, 5424, 5426, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5426, 6275, 10344, 17048, 26990]
 (.n
 (.n .e [1605, 5424, 5426, 6275, 10344, 17050, 24838] .e) [1605, 5424, 5426, 6275, 10346, 17048, 24838] .e)) [1605, 5424, 5426, 10344, 14571, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 5427, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5428, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5428, 6275, 10344, 17048, 25502]
 (.n
 (.n .e [1605, 5424, 5428, 6275, 10344, 17052, 24838] .e) [1605, 5424, 5428, 6275, 10348, 17048, 24838] .e))))))

def T6abab : T := .n T6ababa [1605, 4096, 5424, 6275, 10344, 17052, 24838] T6ababb

def T6aba : T := .n T6abaa [1605, 1637, 5424, 6275, 14571, 17048, 24838] T6abab

def T6abbaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 5429, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5430, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5424, 5432, 6275, 10344, 17048, 24838] .e)) [1605, 5424, 5432, 6275, 10344, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 5432, 6275, 10344, 24838, 25502] .e) [1605, 5424, 5432, 6275, 17048, 24838, 26990] .e)) [1605, 5424, 5432, 6283, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 5488, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5488, 6275, 10344, 17048, 24902] .e) [1605, 5424, 5488, 6275, 10344, 17112, 24838]
 (.n
 (.n .e [1605, 5424, 5488, 6339, 10344, 17048, 24838] .e) [1605, 5424, 5489, 6275, 10344, 17048, 24838] .e))) [1605, 5424, 5492, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 5496, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5552, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5552, 6275, 10344, 17048, 24966]
 (.n
 (.n .e [1605, 5424, 5552, 6275, 10472, 17048, 24838] .e) [1605, 5424, 5553, 6275, 10344, 17048, 24838] .e)) [1605, 5424, 5554, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 5560, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5701, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5703, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 5717, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5733, 6275, 10344, 17048, 24838] .e)))) [1605, 5424, 5760, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 5829, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5936, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5424, 5937, 6275, 10344, 17048, 24838] .e)) [1605, 5424, 5940, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 5944, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5957, 6275, 10344, 17048, 24838] .e)) [1605, 5424, 6000, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6005, 6275, 10344, 17048, 24839] .e) [1605, 5424, 6005, 6275, 10344, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 17048, 24854] .e) [1605, 5424, 6005, 6275, 10344, 17048, 24870] .e))) [1605, 5424, 6005, 6275, 10344, 17048, 24902]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 17048, 24934] .e) [1605, 5424, 6005, 6275, 10344, 17048, 24966] .e) [1605, 5424, 6005, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 17050, 24838] .e) [1605, 5424, 6005, 6275, 10344, 17052, 24838] .e)) [1605, 5424, 6005, 6275, 10344, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 17112, 24838] .e) [1605, 5424, 6005, 6275, 10344, 17144, 24838] .e) [1605, 5424, 6005, 6275, 10344, 17304, 24838]
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 17308, 24838] .e) [1605, 5424, 6005, 6275, 10345, 17048, 24838] .e))))) [1605, 5424, 6005, 6275, 10346, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10348, 17048, 24838] .e) [1605, 5424, 6005, 6275, 10360, 17048, 24838]
 (.n .e [1605, 5424, 6005, 6275, 10472, 17048, 24838] .e)) [1605, 5424, 6005, 6275, 10600, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10604, 17048, 24838] .e) [1605, 5424, 6005, 6279, 10344, 17048, 24838] .e)) [1605, 5424, 6005, 6283, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6291, 10344, 17048, 24838] .e) [1605, 5424, 6005, 6307, 10344, 17048, 24838] .e) [1605, 5424, 6005, 6339, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6005, 6371, 10344, 17048, 24838] .e) [1605, 5424, 6005, 6531, 10344, 17048, 24838] .e))) [1605, 5424, 6005, 6535, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6007, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6013, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6064, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6133, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6144, 6275, 10344, 17048, 24838] .e)) [1605, 5424, 6145, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6146, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6168, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6272, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6275, 10344, 17048, 24839] .e)))) [1605, 5424, 6275, 6275, 10344, 17048, 24846]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10344, 17048, 24854] .e) [1605, 5424, 6275, 6275, 10344, 17048, 24870]
 (.n .e [1605, 5424, 6275, 6275, 10344, 17048, 24902] .e)) [1605, 5424, 6275, 6275, 10344, 17048, 24966]
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10344, 17049, 24838] .e) [1605, 5424, 6275, 6275, 10344, 17050, 24838] .e)) [1605, 5424, 6275, 6275, 10344, 17052, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10344, 17080, 24838] .e) [1605, 5424, 6275, 6275, 10344, 17112, 24838] .e) [1605, 5424, 6275, 6275, 10344, 17304, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10345, 17048, 24838] .e) [1605, 5424, 6275, 6275, 10346, 17048, 24838] .e))) [1605, 5424, 6275, 6275, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10360, 17048, 24838] .e) [1605, 5424, 6275, 6275, 10472, 17048, 24838] .e) [1605, 5424, 6275, 6275, 10600, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 6279, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6279, 10344, 17048, 25502] .e)) [1605, 5424, 6275, 6279, 10344, 17052, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6279, 10348, 17048, 24838] .e) [1605, 5424, 6275, 6283, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6283, 10344, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6275, 6283, 10344, 24838, 25502] .e) [1605, 5424, 6275, 6283, 17048, 24838, 26990] .e))))))

def T6abbab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6291, 10344, 17048, 24854] .e) [1605, 5424, 6275, 6291, 10344, 18141, 24838]
 (.n .e [1605, 5424, 6275, 6291, 10360, 17048, 24838] .e)) [1605, 5424, 6275, 6299, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 6307, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6307, 10344, 17048, 24870] .e)) [1605, 5424, 6275, 6307, 10344, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6315, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6323, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6339, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 6339, 10344, 17048, 24902] .e) [1605, 5424, 6275, 6339, 10344, 17112, 24838] .e))) [1605, 5424, 6275, 6343, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6347, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6371, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 6531, 10344, 17304, 24838] .e) [1605, 5424, 6275, 6531, 10600, 17048, 24838] .e)) [1605, 5424, 6275, 6535, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6547, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6563, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6787, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 6791, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6795, 10344, 17048, 24838] .e)))) [1605, 5424, 6275, 6803, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6851, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7232, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 7299, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 7303, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 7315, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7331, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 7363, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7472, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7473, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7474, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 7480, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7536, 10344, 17048, 24838] .e))) [1605, 5424, 6275, 7555, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7600, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7603, 10344, 17048, 24839]
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 24846] .e) [1605, 5424, 6275, 7603, 10344, 17048, 24854] .e)) [1605, 5424, 6275, 7603, 10344, 17048, 24870]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 24902] .e) [1605, 5424, 6275, 7603, 10344, 17048, 24966] .e) [1605, 5424, 6275, 7603, 10344, 17048, 24982]
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10344, 17049, 24838] .e) [1605, 5424, 6275, 7603, 10344, 17050, 24838] .e))))) [1605, 5424, 6275, 7603, 10344, 17052, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10344, 17080, 24838] .e) [1605, 5424, 6275, 7603, 10344, 17112, 24838]
 (.n .e [1605, 5424, 6275, 7603, 10344, 17304, 24838] .e)) [1605, 5424, 6275, 7603, 10344, 17306, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10345, 17048, 24838] .e) [1605, 5424, 6275, 7603, 10346, 17048, 24838] .e)) [1605, 5424, 6275, 7603, 10348, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10360, 17048, 24838] .e) [1605, 5424, 6275, 7603, 10472, 17048, 24838] .e) [1605, 5424, 6275, 7603, 10488, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10600, 17048, 24838] .e) [1605, 5424, 6275, 7603, 10602, 17048, 24838] .e))) [1605, 5424, 6275, 7607, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7611, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7667, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7749, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 7811, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7879, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 7879, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10344, 17048, 24846] .e) [1605, 5424, 6275, 7879, 10344, 17048, 24854] .e) [1605, 5424, 6275, 7879, 10344, 17048, 24870]
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10344, 17048, 24902] .e) [1605, 5424, 6275, 7879, 10344, 17048, 24966] .e)))) [1605, 5424, 6275, 7879, 10344, 17049, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10344, 17050, 24838] .e) [1605, 5424, 6275, 7879, 10344, 17052, 24838]
 (.n .e [1605, 5424, 6275, 7879, 10344, 17054, 24838] .e)) [1605, 5424, 6275, 7879, 10344, 17080, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10344, 17112, 24838] .e) [1605, 5424, 6275, 7879, 10344, 17304, 24838] .e)) [1605, 5424, 6275, 7879, 10345, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10346, 17048, 24838] .e) [1605, 5424, 6275, 7879, 10348, 17048, 24838] .e) [1605, 5424, 6275, 7879, 10350, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10360, 17048, 24838] .e) [1605, 5424, 6275, 7879, 10472, 17048, 24838] .e))) [1605, 5424, 6275, 7879, 10600, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7887, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7895, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7911, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 8053, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8115, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 8135, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8183, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8192, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8192, 10344, 17048, 24839]
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10344, 17048, 24846] .e) [1605, 5424, 6275, 8192, 10344, 17048, 24854] .e))))))

def T6abba : T := .n T6abbaa [1605, 5424, 6275, 6291, 10344, 17048, 24838] T6abbab

def T6abbba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10344, 17048, 24902] .e) [1605, 5424, 6275, 8192, 10344, 17048, 24966]
 (.n .e [1605, 5424, 6275, 8192, 10344, 17049, 24838] .e)) [1605, 5424, 6275, 8192, 10344, 17050, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10344, 17052, 24838] .e) [1605, 5424, 6275, 8192, 10344, 17080, 24838] .e)) [1605, 5424, 6275, 8192, 10344, 17112, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10344, 17304, 24838] .e) [1605, 5424, 6275, 8192, 10345, 17048, 24838] .e) [1605, 5424, 6275, 8192, 10346, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10348, 17048, 24838] .e) [1605, 5424, 6275, 8192, 10360, 17048, 24838] .e))) [1605, 5424, 6275, 8192, 10472, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10600, 17048, 24838] .e) [1605, 5424, 6275, 8193, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8194, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 8194, 10344, 17048, 26990] .e) [1605, 5424, 6275, 8194, 10346, 17048, 24838] .e)) [1605, 5424, 6275, 8194, 14571, 17048, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8196, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8196, 10344, 17048, 25502] .e) [1605, 5424, 6275, 8196, 10348, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 8198, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8200, 10344, 17048, 24838] .e)))) [1605, 5424, 6275, 8200, 10344, 17048, 24846]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8200, 17048, 24838, 26990] .e) [1605, 5424, 6275, 8200, 17048, 25502, 26990]
 (.n .e [1605, 5424, 6275, 8208, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 8224, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 8224, 10344, 17048, 24870] .e) [1605, 5424, 6275, 8224, 14571, 17048, 24838] .e)) [1605, 5424, 6275, 8232, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8256, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8256, 10344, 17048, 24902] .e) [1605, 5424, 6275, 8259, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 8264, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8288, 10344, 17048, 24838] .e))) [1605, 5424, 6275, 8320, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8330, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8448, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8448, 10600, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 8450, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8452, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 8472, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8704, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8716, 10344, 17048, 24838] .e) [1605, 5424, 6275, 9216, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 9252, 10344, 17048, 24838] .e) [1605, 5424, 6275, 9536, 10344, 17048, 24838] .e))))) [1605, 5424, 6275, 9797, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 9799, 10344, 17048, 24838] .e) [1605, 5424, 6275, 9805, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 9829, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 10053, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10240, 10344, 17048, 24838] .e) [1605, 5424, 6275, 10245, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 10248, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10272, 10344, 17048, 24838] .e) [1605, 5424, 6275, 10304, 10344, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10344, 17048, 24839] .e) [1605, 5424, 6275, 10344, 10344, 17048, 24846] .e))) [1605, 5424, 6275, 10344, 10344, 17048, 24854]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10344, 17048, 24870] .e) [1605, 5424, 6275, 10344, 10344, 17048, 24902] .e) [1605, 5424, 6275, 10344, 10344, 17048, 24966]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10344, 17049, 24838] .e) [1605, 5424, 6275, 10344, 10344, 17050, 24838] .e)) [1605, 5424, 6275, 10344, 10344, 17052, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10344, 17080, 24838] .e) [1605, 5424, 6275, 10344, 10344, 17112, 24838] .e) [1605, 5424, 6275, 10344, 10344, 17304, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10345, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10345, 17048, 24839] .e)))) [1605, 5424, 6275, 10344, 10345, 17049, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10346, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10346, 17050, 24838]
 (.n .e [1605, 5424, 6275, 10344, 10347, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 10348, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10348, 17048, 25502] .e) [1605, 5424, 6275, 10344, 10348, 17052, 24838] .e)) [1605, 5424, 6275, 10344, 10349, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10350, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10360, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10360, 17048, 24854]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10360, 18141, 24838] .e) [1605, 5424, 6275, 10344, 10472, 17048, 24838] .e))) [1605, 5424, 6275, 10344, 10472, 17048, 24966]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10473, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10474, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10488, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10600, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10600, 17304, 24838] .e)) [1605, 5424, 6275, 10344, 10602, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10604, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10616, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10856, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10857, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10860, 17048, 24838] .e))))))

def T6abbbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10984, 17048, 24838] .e) [1605, 5424, 6275, 10344, 11368, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 11369, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 11372, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11384, 17048, 24838] .e) [1605, 5424, 6275, 10344, 11624, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 11845, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11880, 17048, 24838] .e) [1605, 5424, 6275, 10344, 11885, 17048, 24838] .e) [1605, 5424, 6275, 10344, 11885, 17048, 24839]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11885, 17048, 24846] .e) [1605, 5424, 6275, 10344, 11885, 17048, 24854] .e))) [1605, 5424, 6275, 10344, 11885, 17048, 24870]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11885, 17048, 24902] .e) [1605, 5424, 6275, 10344, 11885, 17048, 24966] .e) [1605, 5424, 6275, 10344, 11885, 17049, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11885, 17050, 24838] .e) [1605, 5424, 6275, 10344, 11885, 17052, 24838] .e)) [1605, 5424, 6275, 10344, 11885, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11885, 17112, 24838] .e) [1605, 5424, 6275, 10344, 11885, 17304, 24838] .e) [1605, 5424, 6275, 10344, 11887, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11901, 17048, 24838] .e) [1605, 5424, 6275, 10344, 12013, 17048, 24838] .e)))) [1605, 5424, 6275, 10344, 12141, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 12288, 17048, 24838] .e) [1605, 5424, 6275, 10344, 12322, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 13616, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 13618, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 13620, 17048, 24838] .e) [1605, 5424, 6275, 10344, 13624, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 13680, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14197, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14440, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14441, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14442, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14456, 17048, 24838] .e))) [1605, 5424, 6275, 10344, 14467, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14471, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14475, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14499, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14531, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14568, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 14571, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 24839] .e) [1605, 5424, 6275, 10344, 14571, 17048, 24846] .e) [1605, 5424, 6275, 10344, 14571, 17048, 24854]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 24870] .e) [1605, 5424, 6275, 10344, 14571, 17048, 24902] .e))))) [1605, 5424, 6275, 10344, 14571, 17048, 24903]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 24966] .e) [1605, 5424, 6275, 10344, 14571, 17048, 24974]
 (.n .e [1605, 5424, 6275, 10344, 14571, 17049, 24838] .e)) [1605, 5424, 6275, 10344, 14571, 17050, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14571, 17052, 24838] .e) [1605, 5424, 6275, 10344, 14571, 17080, 24838] .e)) [1605, 5424, 6275, 10344, 14571, 17112, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14571, 17113, 24838] .e) [1605, 5424, 6275, 10344, 14571, 17304, 24838] .e) [1605, 5424, 6275, 10344, 14575, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14587, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14592, 17048, 24838] .e))) [1605, 5424, 6275, 10344, 14696, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14723, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14827, 17048, 24838] .e) [1605, 5424, 6275, 10344, 15083, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15464, 17048, 24838] .e) [1605, 5424, 6275, 10344, 15595, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 15664, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15736, 17048, 24838] .e) [1605, 5424, 6275, 10344, 15736, 17048, 24839] .e) [1605, 5424, 6275, 10344, 15736, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15736, 17048, 24854] .e) [1605, 5424, 6275, 10344, 15736, 17048, 24862] .e)))) [1605, 5424, 6275, 10344, 15736, 17048, 24870]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15736, 17048, 24902] .e) [1605, 5424, 6275, 10344, 15736, 17048, 24966] .e) [1605, 5424, 6275, 10344, 15736, 17049, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15736, 17050, 24838] .e) [1605, 5424, 6275, 10344, 15736, 17052, 24838] .e)) [1605, 5424, 6275, 10344, 15736, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15736, 17112, 24838] .e) [1605, 5424, 6275, 10344, 15736, 17304, 24838] .e) [1605, 5424, 6275, 10344, 15737, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15738, 17048, 24838] .e) [1605, 5424, 6275, 10344, 15740, 17048, 24838] .e))) [1605, 5424, 6275, 10344, 15795, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15864, 17048, 24838] .e) [1605, 5424, 6275, 10344, 15867, 17048, 24838] .e) [1605, 5424, 6275, 10344, 15981, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16071, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16111, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 16248, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16253, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16383, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 24839] .e) [1605, 5424, 6275, 10344, 16384, 17048, 24846] .e))))))

def T6abbb : T := .n T6abbba [1605, 5424, 6275, 10344, 10872, 17048, 24838] T6abbbb

def T6abb : T := .n T6abba [1605, 5424, 6275, 8192, 10344, 17048, 24870] T6abbb

def T6ab : T := .n T6aba [1605, 5424, 5428, 6279, 10344, 17048, 24838] T6abb

def T6a : T := .n T6aa [304, 1605, 6275, 10344, 17048, 24838, 27384] T6ab

def T6baaaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 24870] .e) [1605, 5424, 6275, 10344, 16384, 17048, 24902]
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 24966] .e)) [1605, 5424, 6275, 10344, 16384, 17049, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16384, 17050, 24838] .e) [1605, 5424, 6275, 10344, 16384, 17052, 24838] .e)) [1605, 5424, 6275, 10344, 16384, 17080, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16384, 17112, 24838] .e) [1605, 5424, 6275, 10344, 16384, 17304, 24838] .e) [1605, 5424, 6275, 10344, 16385, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16386, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16386, 17048, 26990] .e))) [1605, 5424, 6275, 10344, 16386, 17050, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16388, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16388, 17048, 25502] .e) [1605, 5424, 6275, 10344, 16388, 17052, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16388, 18141, 25502] .e) [1605, 5424, 6275, 10344, 16390, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 16392, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16392, 17048, 24846] .e) [1605, 5424, 6275, 10344, 16392, 24838, 25502] .e) [1605, 5424, 6275, 10344, 16392, 25502, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16400, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16400, 17048, 24854] .e)))) [1605, 5424, 6275, 10344, 16400, 18141, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16408, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16416, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 16448, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 16460, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16512, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16512, 17048, 24966] .e)) [1605, 5424, 6275, 10344, 16517, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16520, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16528, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16640, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16640, 17304, 24838] .e) [1605, 5424, 6275, 10344, 16642, 17048, 24838] .e))) [1605, 5424, 6275, 10344, 16644, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16680, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16896, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16899, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16904, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16912, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 17024, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17048, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17048, 24839] .e) [1605, 5424, 6275, 10344, 17048, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17048, 24854] .e) [1605, 5424, 6275, 10344, 17048, 17048, 24870] .e))))) [1605, 5424, 6275, 10344, 17048, 17048, 24902]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17048, 24966] .e) [1605, 5424, 6275, 10344, 17048, 17049, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 17049, 24839] .e)) [1605, 5424, 6275, 10344, 17048, 17050, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17050, 26990] .e) [1605, 5424, 6275, 10344, 17048, 17051, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 17052, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17053, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17054, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17080, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17080, 24870] .e) [1605, 5424, 6275, 10344, 17048, 17112, 24838] .e))) [1605, 5424, 6275, 10344, 17048, 17112, 24902]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17113, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17116, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17144, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17304, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17306, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 17308, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17336, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17408, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17428, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17989, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17991, 24838] .e)))) [1605, 5424, 6275, 10344, 17048, 17997, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18005, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18072, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 18073, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 18076, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18104, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18117, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 18136, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24839] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24846]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 24854] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24870] .e))) [1605, 5424, 6275, 10344, 17048, 18141, 24902]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 24910] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24966] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24967]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18143, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18173, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 18176, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18245, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18328, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18397, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18432, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18442, 24838] .e))))))

def T6baaab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 19097, 24838] .e) [1605, 5424, 6275, 10344, 17048, 19098, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 19128, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 19160, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 20189, 24838] .e) [1605, 5424, 6275, 10344, 17048, 20480, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 20498, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 20864, 24838] .e) [1605, 5424, 6275, 10344, 17048, 21144, 24838] .e) [1605, 5424, 6275, 10344, 17048, 21145, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 21146, 24838] .e) [1605, 5424, 6275, 10344, 17048, 21176, 24838] .e))) [1605, 5424, 6275, 10344, 17048, 21400, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 21808, 24838] .e) [1605, 5424, 6275, 10344, 17048, 21810, 24838] .e) [1605, 5424, 6275, 10344, 17048, 21812, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 21816, 24838] .e) [1605, 5424, 6275, 10344, 17048, 21936, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 22168, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22237, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22320, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22389, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22456, 24839] .e)))) [1605, 5424, 6275, 10344, 17048, 22456, 24846]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24854] .e) [1605, 5424, 6275, 10344, 17048, 22456, 24870]
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24878] .e)) [1605, 5424, 6275, 10344, 17048, 22456, 24902]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24966] .e) [1605, 5424, 6275, 10344, 17048, 22457, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 22458, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22460, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22520, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22525, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22659, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22663, 24838] .e))) [1605, 5424, 6275, 10344, 17048, 22667, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22675, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22915, 24838] .e) [1605, 5424, 6275, 10344, 17048, 23171, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 23192, 24838] .e) [1605, 5424, 6275, 10344, 17048, 23195, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 23195, 24839]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 23195, 24846] .e) [1605, 5424, 6275, 10344, 17048, 23195, 24854] .e) [1605, 5424, 6275, 10344, 17048, 23195, 24870]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 23195, 24902] .e) [1605, 5424, 6275, 10344, 17048, 23195, 24966] .e))))) [1605, 5424, 6275, 10344, 17048, 23199, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 23227, 24838] .e) [1605, 5424, 6275, 10344, 17048, 23259, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 23451, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 23987, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24219, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24263, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 24287, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24504, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24507, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24575, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24576, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24578, 24838] .e))) [1605, 5424, 6275, 10344, 17048, 24580, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24624, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24832, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24839] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 24846]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24854] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24862] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24870]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24878] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24886] .e)))) [1605, 5424, 6275, 10344, 17048, 24838, 24902]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24903] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24910]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24934] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 24966]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24967] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24974] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 24982]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25152] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25240] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25242]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25244] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25272] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 25304]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25350] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25351] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25358]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25366] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25414] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 25478]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25496] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25503]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25534] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25566] .e))))))

def T6baaa : T := .n T6baaaa [1605, 5424, 6275, 10344, 17048, 19096, 24838] T6baaab

def T6baaba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25863] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25878]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25894] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 25926]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26181] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26333] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 26374]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26439] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26447] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26455]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26471] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26526] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 26567]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26591] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26728] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26730]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26732] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26744] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 26752]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26856] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26886] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26887]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26894] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26918] .e)))) [1605, 5424, 6275, 10344, 17048, 24838, 26950]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26984] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26990]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26991] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 27006]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 27014] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27118] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 27240]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 27288] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27384] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27385]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 27386] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27388] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 27502]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 27550] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27640] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27646]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 28014] .e) [1605, 5424, 6275, 10344, 17048, 24838, 28269] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 28408]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 28413] .e) [1605, 5424, 6275, 10344, 17048, 24838, 28487] .e) [1605, 5424, 6275, 10344, 17048, 24838, 28527]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 28671] .e) [1605, 5424, 6275, 10344, 17048, 24838, 28934] .e))))) [1605, 5424, 6275, 10344, 17048, 24838, 28935]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 28950] .e) [1605, 5424, 6275, 10344, 17048, 24838, 28966]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 29062] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 29598]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 29958] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30000] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 30006]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30007] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30014] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30070]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30134] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30518] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 30535]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30583] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30648] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30654]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30719] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30851] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 30955]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30982] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31086] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 31119] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31127] .e)))) [1605, 5424, 6275, 10344, 17048, 24838, 31143]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 31175] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31215]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 31387] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 31480]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 31483] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31623] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 31647]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 31743] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32054] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32120]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 32126] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32135] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 32183]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 32255] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32511] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32639]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 32703] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32711] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 32735]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 32751] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32759] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32760]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 32763] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32765] .e))))))

def T6baabb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 32767] .e) [1605, 5424, 6275, 10344, 17048, 24839]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24839, 24839] .e)) [1605, 5424, 6275, 10344, 17048, 24839, 25502]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24839, 25503] .e) [1605, 5424, 6275, 10344, 17048, 24839, 26439] .e)) [1605, 5424, 6275, 10344, 17048, 24839, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24839, 26991] .e) [1605, 5424, 6275, 10344, 17048, 24839, 27384] .e) [1605, 5424, 6275, 10344, 17048, 24839, 30006]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24839, 30007] .e) [1605, 5424, 6275, 10344, 17048, 24839, 31111] .e))) [1605, 5424, 6275, 10344, 17048, 24839, 32767]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24846] .e) [1605, 5424, 6275, 10344, 17048, 24846, 24846] .e) [1605, 5424, 6275, 10344, 17048, 24846, 25502]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24846, 26439] .e) [1605, 5424, 6275, 10344, 17048, 24846, 26447] .e)) [1605, 5424, 6275, 10344, 17048, 24846, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24846, 27384] .e) [1605, 5424, 6275, 10344, 17048, 24846, 30006] .e) [1605, 5424, 6275, 10344, 17048, 24846, 30014]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24846, 31111] .e) [1605, 5424, 6275, 10344, 17048, 24846, 31119] .e)))) [1605, 5424, 6275, 10344, 17048, 24846, 32767]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24854] .e) [1605, 5424, 6275, 10344, 17048, 24854, 24854]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24854, 25502] .e)) [1605, 5424, 6275, 10344, 17048, 24854, 26439]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24854, 26455] .e) [1605, 5424, 6275, 10344, 17048, 24854, 26990] .e)) [1605, 5424, 6275, 10344, 17048, 24854, 27006]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24854, 27384] .e) [1605, 5424, 6275, 10344, 17048, 24854, 30006] .e) [1605, 5424, 6275, 10344, 17048, 24854, 31111]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24854, 31127] .e) [1605, 5424, 6275, 10344, 17048, 24854, 32767] .e))) [1605, 5424, 6275, 10344, 17048, 24862]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24870] .e) [1605, 5424, 6275, 10344, 17048, 24870, 24870] .e) [1605, 5424, 6275, 10344, 17048, 24870, 25502]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24870, 25534] .e) [1605, 5424, 6275, 10344, 17048, 24870, 26439] .e)) [1605, 5424, 6275, 10344, 17048, 24870, 26471]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24870, 26990] .e) [1605, 5424, 6275, 10344, 17048, 24870, 27384] .e) [1605, 5424, 6275, 10344, 17048, 24870, 30006]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24870, 31111] .e) [1605, 5424, 6275, 10344, 17048, 24870, 31143] .e))))) [1605, 5424, 6275, 10344, 17048, 24870, 32767]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24878] .e) [1605, 5424, 6275, 10344, 17048, 24886]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24886, 27384] .e)) [1605, 5424, 6275, 10344, 17048, 24902]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24902, 24902] .e) [1605, 5424, 6275, 10344, 17048, 24902, 25502] .e)) [1605, 5424, 6275, 10344, 17048, 24902, 25566]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24902, 26439] .e) [1605, 5424, 6275, 10344, 17048, 24902, 26990] .e) [1605, 5424, 6275, 10344, 17048, 24902, 27384]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24902, 30006] .e) [1605, 5424, 6275, 10344, 17048, 24902, 30070] .e))) [1605, 5424, 6275, 10344, 17048, 24902, 31111]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24902, 31175] .e) [1605, 5424, 6275, 10344, 17048, 24902, 32767] .e) [1605, 5424, 6275, 10344, 17048, 24903]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24910] .e) [1605, 5424, 6275, 10344, 17048, 24934] .e)) [1605, 5424, 6275, 10344, 17048, 24966]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24966, 24966] .e) [1605, 5424, 6275, 10344, 17048, 24966, 25502] .e) [1605, 5424, 6275, 10344, 17048, 24966, 26439]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24966, 26567] .e) [1605, 5424, 6275, 10344, 17048, 24966, 26990] .e)))) [1605, 5424, 6275, 10344, 17048, 24966, 27118]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24966, 27384] .e) [1605, 5424, 6275, 10344, 17048, 24966, 30006]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24966, 30134] .e)) [1605, 5424, 6275, 10344, 17048, 24966, 31111]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24966, 32767] .e) [1605, 5424, 6275, 10344, 17048, 24967] .e)) [1605, 5424, 6275, 10344, 17048, 24974]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24982] .e) [1605, 5424, 6275, 10344, 17048, 25350, 26990] .e) [1605, 5424, 6275, 10344, 17048, 25350, 30006]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 25350, 31111] .e) [1605, 5424, 6275, 10344, 17048, 25502, 25862] .e))) [1605, 5424, 6275, 10344, 17048, 25502, 26886]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 25502, 26990] .e) [1605, 5424, 6275, 10344, 17048, 25502, 28934] .e) [1605, 5424, 6275, 10344, 17048, 25502, 30006]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 25502, 31111] .e) [1605, 5424, 6275, 10344, 17048, 25502, 31215] .e)) [1605, 5424, 6275, 10344, 17048, 25502, 32126]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 25502, 32183] .e) [1605, 5424, 6275, 10344, 17048, 25862, 26990] .e) [1605, 5424, 6275, 10344, 17048, 25862, 31111]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 26439, 26886] .e) [1605, 5424, 6275, 10344, 17048, 26439, 26990] .e))))))

def T6baab : T := .n T6baaba [1605, 5424, 6275, 10344, 17048, 24838, 32766] T6baabb

def T6baa : T := .n T6baaa [1605, 5424, 6275, 10344, 17048, 24838, 25862] T6baab

def T6babaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 26439, 31111] .e) [1605, 5424, 6275, 10344, 17048, 26439, 31215]
 (.n .e [1605, 5424, 6275, 10344, 17048, 26591, 26990] .e)) [1605, 5424, 6275, 10344, 17048, 26591, 31111]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 26886, 30006] .e) [1605, 5424, 6275, 10344, 17048, 26990, 28934] .e)) [1605, 5424, 6275, 10344, 17048, 26990, 30006]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 26990, 30583] .e) [1605, 5424, 6275, 10344, 17048, 26990, 30654] .e) [1605, 5424, 6275, 10344, 17048, 27646, 30006]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17049, 17049, 24838] .e) [1605, 5424, 6275, 10344, 17049, 18141, 24838] .e))) [1605, 5424, 6275, 10344, 17049, 22456, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17049, 22457, 24838] .e) [1605, 5424, 6275, 10344, 17049, 23195, 24838] .e) [1605, 5424, 6275, 10344, 17049, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17049, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17049, 24838, 24839] .e)) [1605, 5424, 6275, 10344, 17049, 24838, 25502]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17049, 24838, 25503] .e) [1605, 5424, 6275, 10344, 17049, 24838, 26439] .e) [1605, 5424, 6275, 10344, 17049, 24838, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17049, 24838, 27384] .e) [1605, 5424, 6275, 10344, 17049, 24838, 27385] .e)))) [1605, 5424, 6275, 10344, 17049, 24838, 30006]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17049, 24838, 31111] .e) [1605, 5424, 6275, 10344, 17049, 24838, 32767]
 (.n .e [1605, 5424, 6275, 10344, 17049, 24839] .e)) [1605, 5424, 6275, 10344, 17050, 17050, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17050, 18141, 24838] .e) [1605, 5424, 6275, 10344, 17050, 18143, 24838] .e)) [1605, 5424, 6275, 10344, 17050, 22456, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17050, 22458, 24838] .e) [1605, 5424, 6275, 10344, 17050, 23195, 24838] .e) [1605, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17050, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17050, 24838, 25502] .e))) [1605, 5424, 6275, 10344, 17050, 24838, 26439]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17050, 24838, 26990] .e) [1605, 5424, 6275, 10344, 17050, 24838, 27384] .e) [1605, 5424, 6275, 10344, 17050, 24838, 27386]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17050, 24838, 30006] .e) [1605, 5424, 6275, 10344, 17050, 24838, 31111] .e)) [1605, 5424, 6275, 10344, 17050, 24838, 32767]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17050, 26990] .e) [1605, 5424, 6275, 10344, 17051, 24838] .e) [1605, 5424, 6275, 10344, 17051, 24838, 26439]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17052, 17052, 24838] .e) [1605, 5424, 6275, 10344, 17052, 18141, 24838] .e))))) [1605, 5424, 6275, 10344, 17052, 22456, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17052, 22460, 24838] .e) [1605, 5424, 6275, 10344, 17052, 23195, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17052, 23199, 24838] .e)) [1605, 5424, 6275, 10344, 17052, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17052, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17052, 24838, 25502] .e)) [1605, 5424, 6275, 10344, 17052, 24838, 26439]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17052, 24838, 26990] .e) [1605, 5424, 6275, 10344, 17052, 24838, 27384] .e) [1605, 5424, 6275, 10344, 17052, 24838, 27388]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17052, 24838, 30006] .e) [1605, 5424, 6275, 10344, 17052, 24838, 31111] .e))) [1605, 5424, 6275, 10344, 17052, 24838, 32767]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17053, 24838] .e) [1605, 5424, 6275, 10344, 17053, 24838, 31111] .e) [1605, 5424, 6275, 10344, 17054, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17080, 17080, 24838] .e) [1605, 5424, 6275, 10344, 17080, 18141, 24838] .e)) [1605, 5424, 6275, 10344, 17080, 18173, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17080, 22456, 24838] .e) [1605, 5424, 6275, 10344, 17080, 23195, 24838] .e) [1605, 5424, 6275, 10344, 17080, 23227, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17080, 24838] .e) [1605, 5424, 6275, 10344, 17080, 24838, 24838] .e)))) [1605, 5424, 6275, 10344, 17080, 24838, 24870]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17080, 24838, 25502] .e) [1605, 5424, 6275, 10344, 17080, 24838, 25534]
 (.n .e [1605, 5424, 6275, 10344, 17080, 24838, 26439] .e)) [1605, 5424, 6275, 10344, 17080, 24838, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17080, 24838, 27384] .e) [1605, 5424, 6275, 10344, 17080, 24838, 30006] .e)) [1605, 5424, 6275, 10344, 17080, 24838, 31111]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17080, 24838, 32767] .e) [1605, 5424, 6275, 10344, 17080, 24870] .e) [1605, 5424, 6275, 10344, 17112, 17112, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 18141, 24838] .e) [1605, 5424, 6275, 10344, 17112, 22456, 24838] .e))) [1605, 5424, 6275, 10344, 17112, 22520, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 23195, 24838] .e) [1605, 5424, 6275, 10344, 17112, 23259, 24838] .e) [1605, 5424, 6275, 10344, 17112, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17112, 24838, 24902] .e)) [1605, 5424, 6275, 10344, 17112, 24838, 25502]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 24838, 25566] .e) [1605, 5424, 6275, 10344, 17112, 24838, 26439] .e) [1605, 5424, 6275, 10344, 17112, 24838, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 24838, 27384] .e) [1605, 5424, 6275, 10344, 17112, 24838, 30006] .e))))))

def T6babab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 24838, 32767] .e) [1605, 5424, 6275, 10344, 17112, 24902]
 (.n .e [1605, 5424, 6275, 10344, 17113, 24838] .e)) [1605, 5424, 6275, 10344, 17116, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17116, 24838, 26990] .e) [1605, 5424, 6275, 10344, 17144, 24838] .e)) [1605, 5424, 6275, 10344, 17304, 17304, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17304, 18141, 24838] .e) [1605, 5424, 6275, 10344, 17304, 18397, 24838] .e) [1605, 5424, 6275, 10344, 17304, 22456, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17304, 23195, 24838] .e) [1605, 5424, 6275, 10344, 17304, 23451, 24838] .e))) [1605, 5424, 6275, 10344, 17304, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17304, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17304, 24838, 25502] .e) [1605, 5424, 6275, 10344, 17304, 24838, 26439]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17304, 24838, 26990] .e) [1605, 5424, 6275, 10344, 17304, 24838, 27384] .e)) [1605, 5424, 6275, 10344, 17304, 24838, 27640]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17304, 24838, 30006] .e) [1605, 5424, 6275, 10344, 17304, 24838, 31111] .e) [1605, 5424, 6275, 10344, 17304, 24838, 32767]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17306, 24838] .e) [1605, 5424, 6275, 10344, 17308, 24838] .e)))) [1605, 5424, 6275, 10344, 17336, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17336, 24838, 26990] .e) [1605, 5424, 6275, 10344, 18072, 23195, 24838]
 (.n .e [1605, 5424, 6275, 10344, 18072, 24838, 25502] .e)) [1605, 5424, 6275, 10344, 18072, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 18141, 19096, 24838] .e) [1605, 5424, 6275, 10344, 18141, 21144, 24838] .e)) [1605, 5424, 6275, 10344, 18141, 23195, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 18141, 24838, 24854] .e) [1605, 5424, 6275, 10344, 18141, 24838, 25240] .e) [1605, 5424, 6275, 10344, 18141, 24838, 25502]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 18141, 24838, 27384] .e) [1605, 5424, 6275, 10344, 18141, 24838, 27646] .e))) [1605, 5424, 6275, 10344, 18141, 24838, 31483]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 18141, 24838, 31647] .e) [1605, 5424, 6275, 10344, 18141, 24854] .e) [1605, 5424, 6275, 10344, 18141, 25502, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 18141, 25502, 30006] .e) [1605, 5424, 6275, 10344, 18141, 25502, 31111] .e)) [1605, 5424, 6275, 10344, 19096, 22456, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 19096, 24838, 25502] .e) [1605, 5424, 6275, 10344, 21144, 24838, 25502] .e) [1605, 5424, 6275, 10344, 21144, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 22456, 24838, 25240] .e) [1605, 5424, 6275, 10344, 22456, 24838, 25502] .e))))) [1605, 5424, 6275, 10344, 22456, 24838, 27384]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 22456, 24838, 27646] .e) [1605, 5424, 6275, 10344, 22456, 25502, 26990]
 (.n .e [1605, 5424, 6275, 10344, 22456, 25502, 30006] .e)) [1605, 5424, 6275, 10344, 22456, 25502, 31111]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 22525, 24838, 25502] .e) [1605, 5424, 6275, 10344, 22525, 24838, 27384] .e)) [1605, 5424, 6275, 10344, 23195, 24838, 25240]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 23195, 24838, 25502] .e) [1605, 5424, 6275, 10344, 23195, 24838, 26591] .e) [1605, 5424, 6275, 10344, 23195, 25502, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 23195, 25502, 30006] .e) [1605, 5424, 6275, 10344, 23195, 25502, 31111] .e))) [1605, 5424, 6275, 10344, 24287, 24838, 25502]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 24507, 24838, 25502] .e) [1605, 5424, 6275, 10345, 10345, 17048, 24838] .e) [1605, 5424, 6275, 10345, 11885, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10345, 14571, 17048, 24838] .e) [1605, 5424, 6275, 10345, 15736, 17048, 24838] .e)) [1605, 5424, 6275, 10345, 15737, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10345, 16384, 17048, 24838] .e) [1605, 5424, 6275, 10345, 17048, 17048, 24838] .e) [1605, 5424, 6275, 10345, 17048, 17049, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17048, 18141, 24838] .e) [1605, 5424, 6275, 10345, 17048, 22456, 24838] .e)))) [1605, 5424, 6275, 10345, 17048, 23195, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17048, 24838] .e) [1605, 5424, 6275, 10345, 17048, 24838, 24838]
 (.n .e [1605, 5424, 6275, 10345, 17048, 24838, 24839] .e)) [1605, 5424, 6275, 10345, 17048, 24838, 25502]
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17048, 24838, 26439] .e) [1605, 5424, 6275, 10345, 17048, 24838, 26990] .e)) [1605, 5424, 6275, 10345, 17048, 24838, 26991]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17048, 24838, 27384] .e) [1605, 5424, 6275, 10345, 17048, 24838, 27385] .e) [1605, 5424, 6275, 10345, 17048, 24838, 30006]
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17048, 24838, 31111] .e) [1605, 5424, 6275, 10345, 17048, 24838, 32767] .e))) [1605, 5424, 6275, 10345, 17048, 24839]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10345, 17049, 24838] .e) [1605, 5424, 6275, 10346, 10346, 17048, 24838] .e) [1605, 5424, 6275, 10346, 11885, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10346, 11887, 17048, 24838] .e) [1605, 5424, 6275, 10346, 14571, 17048, 24838] .e)) [1605, 5424, 6275, 10346, 15736, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10346, 15738, 17048, 24838] .e) [1605, 5424, 6275, 10346, 16384, 17048, 24838] .e) [1605, 5424, 6275, 10346, 17048, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10346, 17048, 17050, 24838] .e) [1605, 5424, 6275, 10346, 17048, 18141, 24838] .e))))))

def T6baba : T := .n T6babaa [1605, 5424, 6275, 10344, 17112, 24838, 31111] T6babab

def T6babba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10346, 17048, 23195, 24838] .e) [1605, 5424, 6275, 10346, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10346, 17048, 24838, 24838] .e)) [1605, 5424, 6275, 10346, 17048, 24838, 25502]
 (.n
 (.n .e [1605, 5424, 6275, 10346, 17048, 24838, 26439] .e) [1605, 5424, 6275, 10346, 17048, 24838, 26990] .e)) [1605, 5424, 6275, 10346, 17048, 24838, 27384]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10346, 17048, 24838, 27386] .e) [1605, 5424, 6275, 10346, 17048, 24838, 30006] .e) [1605, 5424, 6275, 10346, 17048, 24838, 31111]
 (.n
 (.n .e [1605, 5424, 6275, 10346, 17048, 24838, 32767] .e) [1605, 5424, 6275, 10346, 17050, 24838] .e))) [1605, 5424, 6275, 10347, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10347, 17048, 24838, 26439] .e) [1605, 5424, 6275, 10348, 10348, 17048, 24838] .e) [1605, 5424, 6275, 10348, 11885, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10348, 14571, 17048, 24838] .e) [1605, 5424, 6275, 10348, 14575, 17048, 24838] .e)) [1605, 5424, 6275, 10348, 15736, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10348, 15740, 17048, 24838] .e) [1605, 5424, 6275, 10348, 16384, 17048, 24838] .e) [1605, 5424, 6275, 10348, 17048, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17048, 17052, 24838] .e) [1605, 5424, 6275, 10348, 17048, 18141, 24838] .e)))) [1605, 5424, 6275, 10348, 17048, 22456, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17048, 23195, 24838] .e) [1605, 5424, 6275, 10348, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10348, 17048, 24838, 24838] .e)) [1605, 5424, 6275, 10348, 17048, 24838, 25502]
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17048, 24838, 26439] .e) [1605, 5424, 6275, 10348, 17048, 24838, 26990] .e)) [1605, 5424, 6275, 10348, 17048, 24838, 27384]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17048, 24838, 27388] .e) [1605, 5424, 6275, 10348, 17048, 24838, 30006] .e) [1605, 5424, 6275, 10348, 17048, 24838, 31111]
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17048, 24838, 32767] .e) [1605, 5424, 6275, 10348, 17048, 25502] .e))) [1605, 5424, 6275, 10348, 17052, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10349, 17048, 24838] .e) [1605, 5424, 6275, 10349, 17048, 24838, 31111] .e) [1605, 5424, 6275, 10350, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10360, 10360, 17048, 24838] .e) [1605, 5424, 6275, 10360, 11885, 17048, 24838] .e)) [1605, 5424, 6275, 10360, 11901, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10360, 14571, 17048, 24838] .e) [1605, 5424, 6275, 10360, 14587, 17048, 24838] .e) [1605, 5424, 6275, 10360, 15736, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10360, 16384, 17048, 24838] .e) [1605, 5424, 6275, 10360, 17048, 17048, 24838] .e))))) [1605, 5424, 6275, 10360, 17048, 18141, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10360, 17048, 22456, 24838] .e) [1605, 5424, 6275, 10360, 17048, 23195, 24838]
 (.n .e [1605, 5424, 6275, 10360, 17048, 24838] .e)) [1605, 5424, 6275, 10360, 17048, 24838, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10360, 17048, 24838, 24854] .e) [1605, 5424, 6275, 10360, 17048, 24838, 25502] .e)) [1605, 5424, 6275, 10360, 17048, 24838, 26439]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10360, 17048, 24838, 26990] .e) [1605, 5424, 6275, 10360, 17048, 24838, 27006] .e) [1605, 5424, 6275, 10360, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6275, 10360, 17048, 24838, 30006] .e) [1605, 5424, 6275, 10360, 17048, 24838, 31111] .e))) [1605, 5424, 6275, 10360, 17048, 24838, 32767]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10360, 17048, 24854] .e) [1605, 5424, 6275, 10360, 18141, 24838] .e) [1605, 5424, 6275, 10472, 10472, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10472, 11885, 17048, 24838] .e) [1605, 5424, 6275, 10472, 12013, 17048, 24838] .e)) [1605, 5424, 6275, 10472, 14571, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10472, 15736, 17048, 24838] .e) [1605, 5424, 6275, 10472, 15864, 17048, 24838] .e) [1605, 5424, 6275, 10472, 16384, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10472, 17048, 17048, 24838] .e) [1605, 5424, 6275, 10472, 17048, 18141, 24838] .e)))) [1605, 5424, 6275, 10472, 17048, 22456, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10472, 17048, 23195, 24838] .e) [1605, 5424, 6275, 10472, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10472, 17048, 24838, 24838] .e)) [1605, 5424, 6275, 10472, 17048, 24838, 24966]
 (.n
 (.n .e [1605, 5424, 6275, 10472, 17048, 24838, 25502] .e) [1605, 5424, 6275, 10472, 17048, 24838, 26439] .e)) [1605, 5424, 6275, 10472, 17048, 24838, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10472, 17048, 24838, 27118] .e) [1605, 5424, 6275, 10472, 17048, 24838, 27384] .e) [1605, 5424, 6275, 10472, 17048, 24838, 30006]
 (.n
 (.n .e [1605, 5424, 6275, 10472, 17048, 24838, 31111] .e) [1605, 5424, 6275, 10472, 17048, 24838, 32767] .e))) [1605, 5424, 6275, 10472, 17048, 24966]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10473, 17048, 18141, 24838] .e) [1605, 5424, 6275, 10473, 17048, 24838] .e) [1605, 5424, 6275, 10474, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10474, 17048, 24838, 25502] .e) [1605, 5424, 6275, 10488, 17048, 24838] .e)) [1605, 5424, 6275, 10600, 10600, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10600, 11885, 17048, 24838] .e) [1605, 5424, 6275, 10600, 12141, 17048, 24838] .e) [1605, 5424, 6275, 10600, 14571, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10600, 14827, 17048, 24838] .e) [1605, 5424, 6275, 10600, 15736, 17048, 24838] .e))))))

def T6babbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10600, 17048, 17048, 24838] .e) [1605, 5424, 6275, 10600, 17048, 17304, 24838]
 (.n .e [1605, 5424, 6275, 10600, 17048, 18141, 24838] .e)) [1605, 5424, 6275, 10600, 17048, 22456, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10600, 17048, 23195, 24838] .e) [1605, 5424, 6275, 10600, 17048, 24838] .e)) [1605, 5424, 6275, 10600, 17048, 24838, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10600, 17048, 24838, 25502] .e) [1605, 5424, 6275, 10600, 17048, 24838, 26439] .e) [1605, 5424, 6275, 10600, 17048, 24838, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 10600, 17048, 24838, 27384] .e) [1605, 5424, 6275, 10600, 17048, 24838, 27640] .e))) [1605, 5424, 6275, 10600, 17048, 24838, 30006]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10600, 17048, 24838, 31111] .e) [1605, 5424, 6275, 10600, 17048, 24838, 32767] .e) [1605, 5424, 6275, 10600, 17304, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10602, 17048, 24838] .e) [1605, 5424, 6275, 10604, 17048, 24838] .e)) [1605, 5424, 6275, 10616, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10616, 17048, 24838, 25502] .e) [1605, 5424, 6275, 10856, 14571, 17048, 24838] .e) [1605, 5424, 6275, 10856, 15736, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10856, 17048, 24838, 26990] .e) [1605, 5424, 6275, 11368, 14571, 17048, 24838] .e)))) [1605, 5424, 6275, 11368, 17048, 24838, 26990]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 11368, 17048, 24838, 27384] .e) [1605, 5424, 6275, 11885, 14440, 17048, 24838]
 (.n .e [1605, 5424, 6275, 11885, 14571, 17048, 24838] .e)) [1605, 5424, 6275, 11885, 17048, 24838, 26728]
 (.n
 (.n .e [1605, 5424, 6275, 11885, 17048, 24838, 26990] .e) [1605, 5424, 6275, 11885, 17048, 24838, 31215] .e)) [1605, 5424, 6275, 11885, 17048, 25502, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 11885, 17048, 26439, 26990] .e) [1605, 5424, 6275, 11885, 17048, 26990, 30006] .e) [1605, 5424, 6275, 14440, 17048, 24838, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 14440, 17048, 24838, 27384] .e) [1605, 5424, 6275, 14571, 17048, 17080, 24838] .e))) [1605, 5424, 6275, 14571, 17048, 24838, 24870]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 14571, 17048, 24838, 26728] .e) [1605, 5424, 6275, 14571, 17048, 24838, 26990] .e) [1605, 5424, 6275, 14571, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6275, 14571, 17048, 24838, 27646] .e) [1605, 5424, 6275, 14571, 17048, 24838, 28413] .e)) [1605, 5424, 6275, 14571, 17048, 24838, 28527]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 14571, 17048, 24870] .e) [1605, 5424, 6275, 14571, 17048, 25502, 26990] .e) [1605, 5424, 6275, 14571, 17048, 26439, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 14571, 17048, 26990, 30006] .e) [1605, 5424, 6275, 14571, 17080, 24838] .e))))) [1605, 5424, 6275, 14571, 18141, 24838, 27384]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 14571, 22456, 24838, 27384] .e) [1605, 5424, 6275, 15736, 17048, 24838, 26728]
 (.n .e [1605, 5424, 6275, 15736, 17048, 24838, 26990] .e)) [1605, 5424, 6275, 15736, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6275, 15736, 17048, 24838, 27646] .e) [1605, 5424, 6275, 15736, 17048, 25502, 26990] .e)) [1605, 5424, 6275, 15736, 17048, 26439, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 15736, 17048, 26990, 30006] .e) [1605, 5424, 6275, 15736, 18141, 24838, 27384] .e) [1605, 5424, 6275, 15736, 22456, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6275, 15867, 17048, 24838, 26990] .e) [1605, 5424, 6275, 15867, 17048, 24838, 27384] .e))) [1605, 5424, 6275, 16111, 17048, 24838, 26990]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 16253, 17048, 24838, 26990] .e) [1605, 5424, 6279, 6279, 10344, 17048, 24838] .e) [1605, 5424, 6279, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6279, 7607, 10344, 17048, 24838] .e) [1605, 5424, 6279, 7879, 10344, 17048, 24838] .e)) [1605, 5424, 6279, 8192, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6279, 10344, 10344, 17048, 24838] .e) [1605, 5424, 6279, 10344, 10348, 17048, 24838] .e) [1605, 5424, 6279, 10344, 11885, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6279, 10344, 14571, 17048, 24838] .e) [1605, 5424, 6279, 10344, 14575, 17048, 24838] .e)))) [1605, 5424, 6279, 10344, 15736, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6279, 10344, 16384, 17048, 24838] .e) [1605, 5424, 6279, 10344, 17048, 17048, 24838] .e) [1605, 5424, 6279, 10344, 17048, 17052, 24838]
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17048, 18141, 24838] .e) [1605, 5424, 6279, 10344, 17048, 22456, 24838] .e)) [1605, 5424, 6279, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17048, 23199, 24838] .e) [1605, 5424, 6279, 10344, 17048, 24838] .e) [1605, 5424, 6279, 10344, 17048, 24838, 24838]
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6279, 10344, 17048, 24838, 26439] .e))) [1605, 5424, 6279, 10344, 17048, 24838, 26990]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17048, 24838, 27384] .e) [1605, 5424, 6279, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6279, 10344, 17048, 24838, 31111]
 (.n
 (.n .e [1605, 5424, 6279, 10344, 17048, 24838, 32767] .e) [1605, 5424, 6279, 10344, 17048, 25502] .e)) [1605, 5424, 6279, 10344, 17052, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6279, 10348, 17048, 24838] .e) [1605, 5424, 6283, 6283, 10344, 17048, 24838] .e) [1605, 5424, 6283, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6283, 7611, 10344, 17048, 24838] .e) [1605, 5424, 6283, 7879, 10344, 17048, 24838] .e))))))

def T6babb : T := .n T6babba [1605, 5424, 6275, 10600, 16384, 17048, 24838] T6babbb

def T6bab : T := .n T6baba [1605, 5424, 6275, 10346, 17048, 22456, 24838] T6babb

def T6ba : T := .n T6baa [1605, 5424, 6275, 10344, 17048, 26439, 28934] T6bab

def T6bbaaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 8192, 10344, 17048, 24838] .e) [1605, 5424, 6283, 10344, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6283, 10344, 11885, 17048, 24838] .e)) [1605, 5424, 6283, 10344, 14571, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6283, 10344, 15736, 17048, 24838] .e) [1605, 5424, 6283, 10344, 16384, 17048, 24838] .e)) [1605, 5424, 6283, 10344, 17048, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17048, 18141, 24838] .e) [1605, 5424, 6283, 10344, 17048, 22456, 24838] .e) [1605, 5424, 6283, 10344, 17048, 23195, 24838]
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17048, 24838] .e) [1605, 5424, 6283, 10344, 17048, 24838, 24838] .e))) [1605, 5424, 6283, 10344, 17048, 24838, 24846]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6283, 10344, 17048, 24838, 26439] .e) [1605, 5424, 6283, 10344, 17048, 24838, 26990]
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17048, 24838, 27384] .e) [1605, 5424, 6283, 10344, 17048, 24838, 30006] .e)) [1605, 5424, 6283, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n .e [1605, 5424, 6283, 10344, 17048, 24838, 31119] .e) [1605, 5424, 6283, 10344, 17048, 24838, 32767] .e) [1605, 5424, 6283, 10344, 17048, 24846]
 (.n
 (.n .e [1605, 5424, 6283, 10344, 24838, 25502] .e) [1605, 5424, 6283, 17048, 24838, 26990] .e)))) [1605, 5424, 6291, 6291, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6291, 7603, 10344, 17048, 24838] .e) [1605, 5424, 6291, 7879, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6291, 7895, 10344, 17048, 24838] .e)) [1605, 5424, 6291, 8192, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6291, 10344, 10344, 17048, 24838] .e) [1605, 5424, 6291, 10344, 10360, 17048, 24838] .e)) [1605, 5424, 6291, 10344, 11885, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6291, 10344, 14571, 17048, 24838] .e) [1605, 5424, 6291, 10344, 14587, 17048, 24838] .e) [1605, 5424, 6291, 10344, 15736, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6291, 10344, 16384, 17048, 24838] .e) [1605, 5424, 6291, 10344, 17048, 17048, 24838] .e))) [1605, 5424, 6291, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6291, 10344, 17048, 22456, 24838] .e) [1605, 5424, 6291, 10344, 17048, 23195, 24838] .e) [1605, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6291, 10344, 17048, 24838, 24838] .e) [1605, 5424, 6291, 10344, 17048, 24838, 24854] .e)) [1605, 5424, 6291, 10344, 17048, 24838, 25502]
 (.n
 (.n
 (.n .e [1605, 5424, 6291, 10344, 17048, 24838, 26439] .e) [1605, 5424, 6291, 10344, 17048, 24838, 26990] .e) [1605, 5424, 6291, 10344, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6291, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6291, 10344, 17048, 24838, 31111] .e))))) [1605, 5424, 6291, 10344, 17048, 24838, 31127]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6291, 10344, 17048, 24838, 32767] .e) [1605, 5424, 6291, 10344, 17048, 24854]
 (.n .e [1605, 5424, 6291, 10344, 18141, 24838] .e)) [1605, 5424, 6291, 10360, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6299, 10344, 15736, 17048, 24838] .e) [1605, 5424, 6299, 10344, 17048, 24838] .e)) [1605, 5424, 6307, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6307, 7603, 10344, 17048, 24838] .e) [1605, 5424, 6307, 7879, 10344, 17048, 24838] .e) [1605, 5424, 6307, 7911, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6307, 8192, 10344, 17048, 24838] .e) [1605, 5424, 6307, 10344, 10344, 17048, 24838] .e))) [1605, 5424, 6307, 10344, 11885, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6307, 10344, 14571, 17048, 24838] .e) [1605, 5424, 6307, 10344, 15736, 17048, 24838] .e) [1605, 5424, 6307, 10344, 16384, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17048, 17048, 24838] .e) [1605, 5424, 6307, 10344, 17048, 17080, 24838] .e)) [1605, 5424, 6307, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17048, 22456, 24838] .e) [1605, 5424, 6307, 10344, 17048, 23195, 24838] .e) [1605, 5424, 6307, 10344, 17048, 23227, 24838]
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17048, 24838] .e) [1605, 5424, 6307, 10344, 17048, 24838, 24838] .e)))) [1605, 5424, 6307, 10344, 17048, 24838, 24870]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6307, 10344, 17048, 24838, 26439]
 (.n .e [1605, 5424, 6307, 10344, 17048, 24838, 26990] .e)) [1605, 5424, 6307, 10344, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6307, 10344, 17048, 24838, 31111] .e)) [1605, 5424, 6307, 10344, 17048, 24838, 31143]
 (.n
 (.n
 (.n .e [1605, 5424, 6307, 10344, 17048, 24838, 32767] .e) [1605, 5424, 6307, 10344, 17048, 24870] .e) [1605, 5424, 6307, 10344, 17080, 24838]
 (.n
 (.n .e [1605, 5424, 6315, 10344, 17048, 22456, 24838] .e) [1605, 5424, 6315, 10344, 17048, 24838] .e))) [1605, 5424, 6323, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6323, 10344, 17048, 24838, 27384] .e) [1605, 5424, 6339, 6339, 10344, 17048, 24838] .e) [1605, 5424, 6339, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6339, 7667, 10344, 17048, 24838] .e) [1605, 5424, 6339, 7879, 10344, 17048, 24838] .e)) [1605, 5424, 6339, 8192, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6339, 10344, 10344, 17048, 24838] .e) [1605, 5424, 6339, 10344, 11885, 17048, 24838] .e) [1605, 5424, 6339, 10344, 14571, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6339, 10344, 15736, 17048, 24838] .e) [1605, 5424, 6339, 10344, 16384, 17048, 24838] .e))))))

def T6bbaab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 17112, 24838] .e) [1605, 5424, 6339, 10344, 17048, 18141, 24838]
 (.n .e [1605, 5424, 6339, 10344, 17048, 22456, 24838] .e)) [1605, 5424, 6339, 10344, 17048, 23195, 24838]
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 23259, 24838] .e) [1605, 5424, 6339, 10344, 17048, 24838] .e)) [1605, 5424, 6339, 10344, 17048, 24838, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 24838, 24902] .e) [1605, 5424, 6339, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6339, 10344, 17048, 24838, 26439]
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 24838, 26990] .e) [1605, 5424, 6339, 10344, 17048, 24838, 27384] .e))) [1605, 5424, 6339, 10344, 17048, 24838, 30006]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 24838, 31111] .e) [1605, 5424, 6339, 10344, 17048, 24838, 31175] .e) [1605, 5424, 6339, 10344, 17048, 24838, 32767]
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 24902] .e) [1605, 5424, 6339, 10344, 17112, 24838] .e)) [1605, 5424, 6343, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6343, 10344, 17048, 24838, 26990] .e) [1605, 5424, 6347, 10344, 17048, 18141, 24838] .e) [1605, 5424, 6347, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6371, 10344, 17048, 24838] .e) [1605, 5424, 6531, 6531, 10344, 17048, 24838] .e)))) [1605, 5424, 6531, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6531, 7879, 10344, 17048, 24838] .e) [1605, 5424, 6531, 8135, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6531, 8192, 10344, 17048, 24838] .e)) [1605, 5424, 6531, 10344, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6531, 10344, 10600, 17048, 24838] .e) [1605, 5424, 6531, 10344, 11885, 17048, 24838] .e)) [1605, 5424, 6531, 10344, 14571, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6531, 10344, 14827, 17048, 24838] .e) [1605, 5424, 6531, 10344, 15736, 17048, 24838] .e) [1605, 5424, 6531, 10344, 16384, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17048, 17048, 24838] .e) [1605, 5424, 6531, 10344, 17048, 17304, 24838] .e))) [1605, 5424, 6531, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17048, 22456, 24838] .e) [1605, 5424, 6531, 10344, 17048, 23195, 24838] .e) [1605, 5424, 6531, 10344, 17048, 23451, 24838]
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17048, 24838] .e) [1605, 5424, 6531, 10344, 17048, 24838, 24838] .e)) [1605, 5424, 6531, 10344, 17048, 24838, 25502]
 (.n
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17048, 24838, 26439] .e) [1605, 5424, 6531, 10344, 17048, 24838, 26990] .e) [1605, 5424, 6531, 10344, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6531, 10344, 17048, 24838, 31111] .e))))) [1605, 5424, 6531, 10344, 17048, 24838, 32767]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6531, 10344, 17304, 24838] .e) [1605, 5424, 6531, 10600, 17048, 24838]
 (.n .e [1605, 5424, 6535, 10344, 17048, 24838] .e)) [1605, 5424, 6547, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6547, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6563, 10344, 17048, 24838] .e)) [1605, 5424, 6563, 10344, 17048, 24838, 26990]
 (.n
 (.n
 (.n .e [1605, 5424, 6787, 7603, 10344, 17048, 24838] .e) [1605, 5424, 6787, 10344, 14571, 17048, 24838] .e) [1605, 5424, 6787, 10344, 17048, 24838, 31111]
 (.n
 (.n .e [1605, 5424, 7299, 10344, 14571, 17048, 24838] .e) [1605, 5424, 7299, 10344, 17048, 23195, 24838] .e))) [1605, 5424, 7299, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 7603, 10344, 10345, 17048, 24838] .e) [1605, 5424, 7603, 10344, 14467, 17048, 24838] .e) [1605, 5424, 7603, 10344, 14571, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 7603, 10344, 17048, 17049, 24838] .e) [1605, 5424, 7603, 10344, 17048, 22659, 24838] .e)) [1605, 5424, 7603, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 7603, 10344, 17048, 24838, 24839] .e) [1605, 5424, 7603, 10344, 17048, 24838, 31111] .e) [1605, 5424, 7603, 10344, 17048, 24838, 31215]
 (.n
 (.n .e [1605, 5424, 7603, 10344, 17048, 24838, 31483] .e) [1605, 5424, 7603, 10344, 17048, 24838, 31647] .e)))) [1605, 5424, 7603, 10344, 17048, 24839]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 7603, 10344, 17048, 25502, 31111] .e) [1605, 5424, 7603, 10344, 17048, 26439, 31111]
 (.n .e [1605, 5424, 7603, 10344, 17049, 24838] .e)) [1605, 5424, 7603, 10344, 18141, 23195, 24838]
 (.n
 (.n .e [1605, 5424, 7603, 10344, 23195, 24838, 25502] .e) [1605, 5424, 7603, 10345, 17048, 24838] .e)) [1605, 5424, 7603, 11885, 14571, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 7603, 14571, 17048, 24838, 26990] .e) [1605, 5424, 7603, 14571, 17048, 24838, 27384] .e) [1605, 5424, 7879, 10344, 14467, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 7879, 10344, 14571, 17048, 24838] .e) [1605, 5424, 7879, 10344, 17048, 22659, 24838] .e))) [1605, 5424, 7879, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 7879, 10344, 17048, 24838, 31215] .e) [1605, 5424, 7879, 10344, 17048, 25502, 31111] .e) [1605, 5424, 7879, 10344, 17048, 26439, 31111]
 (.n
 (.n .e [1605, 5424, 7879, 11885, 14571, 17048, 24838] .e) [1605, 5424, 7879, 14571, 17048, 24838, 26990] .e)) [1605, 5424, 7879, 14571, 17048, 24838, 27384]
 (.n
 (.n
 (.n .e [1605, 5424, 8183, 10344, 14571, 17048, 24838] .e) [1605, 5424, 8183, 10344, 17048, 24838, 31111] .e) [1605, 5424, 10344, 14467, 17048, 23195, 24838]
 (.n
 (.n .e [1605, 5424, 10344, 14571, 16386, 17048, 24838] .e) [1605, 5424, 10344, 14571, 17048, 17050, 24838] .e))))))

def T6bbaa : T := .n T6bbaaa [1605, 5424, 6339, 10344, 17048, 17048, 24838] T6bbaab

def T6bbaba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 10344, 14571, 17048, 23195, 24838] .e) [1605, 5424, 10344, 14571, 17048, 24287, 24838]
 (.n .e [1605, 5424, 10344, 14571, 17048, 24507, 24838] .e)) [1605, 5424, 10344, 14571, 17050, 24838]
 (.n
 (.n .e [1605, 5424, 10344, 14571, 18141, 23195, 24838] .e) [1605, 5424, 10344, 14571, 23195, 24838, 25502] .e)) [1605, 5424, 10344, 15867, 17048, 23195, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 11885, 14571, 17048, 23195, 24838] .e) [1605, 5424, 14571, 17048, 23195, 24838, 26990] .e) [1605, 5424, 14571, 17048, 23195, 24838, 27384]
 (.n
 (.n .e [1605, 5425, 5425, 6275, 10344, 17048, 24838] .e) [1605, 5425, 6005, 6275, 10344, 17048, 24838] .e))) [1605, 5425, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5425, 6275, 7603, 10344, 17048, 24838] .e) [1605, 5425, 6275, 7879, 10344, 17048, 24838] .e) [1605, 5425, 6275, 8192, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5425, 6275, 10344, 10344, 17048, 24838] .e) [1605, 5425, 6275, 10344, 10345, 17048, 24838] .e)) [1605, 5425, 6275, 10344, 11885, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5425, 6275, 10344, 14571, 17048, 24838] .e) [1605, 5425, 6275, 10344, 15736, 17048, 24838] .e) [1605, 5425, 6275, 10344, 15737, 17048, 24838]
 (.n
 (.n .e [1605, 5425, 6275, 10344, 16384, 17048, 24838] .e) [1605, 5425, 6275, 10344, 17048, 17048, 24838] .e)))) [1605, 5425, 6275, 10344, 17048, 17049, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17048, 18141, 24838] .e) [1605, 5425, 6275, 10344, 17048, 22456, 24838]
 (.n .e [1605, 5425, 6275, 10344, 17048, 22457, 24838] .e)) [1605, 5425, 6275, 10344, 17048, 23195, 24838]
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17048, 24838] .e) [1605, 5425, 6275, 10344, 17048, 24838, 24838] .e)) [1605, 5425, 6275, 10344, 17048, 24838, 24839]
 (.n
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17048, 24838, 25502] .e) [1605, 5425, 6275, 10344, 17048, 24838, 26439] .e) [1605, 5425, 6275, 10344, 17048, 24838, 26990]
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17048, 24838, 27384] .e) [1605, 5425, 6275, 10344, 17048, 24838, 30006] .e))) [1605, 5425, 6275, 10344, 17048, 24838, 30007]
 (.n
 (.n
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17048, 24838, 31111] .e) [1605, 5425, 6275, 10344, 17048, 24838, 32767] .e) [1605, 5425, 6275, 10344, 17048, 24839]
 (.n
 (.n .e [1605, 5425, 6275, 10344, 17049, 24838] .e) [1605, 5425, 6275, 10345, 17048, 24838] .e)) [1605, 5426, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5426, 6005, 6275, 10344, 17048, 24838] .e) [1605, 5426, 6007, 6275, 10344, 17048, 24838] .e) [1605, 5426, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5426, 6275, 7603, 10344, 17048, 24838] .e) [1605, 5426, 6275, 7879, 10344, 17048, 24838] .e))))) [1605, 5426, 6275, 8192, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5426, 6275, 10344, 10344, 17048, 24838] .e) [1605, 5426, 6275, 10344, 10346, 17048, 24838]
 (.n .e [1605, 5426, 6275, 10344, 11885, 17048, 24838] .e)) [1605, 5426, 6275, 10344, 14571, 17048, 24838]
 (.n
 (.n .e [1605, 5426, 6275, 10344, 15736, 17048, 24838] .e) [1605, 5426, 6275, 10344, 15738, 17048, 24838] .e)) [1605, 5426, 6275, 10344, 16384, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17048, 17048, 24838] .e) [1605, 5426, 6275, 10344, 17048, 17050, 24838] .e) [1605, 5426, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17048, 22456, 24838] .e) [1605, 5426, 6275, 10344, 17048, 22458, 24838] .e))) [1605, 5426, 6275, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17048, 24838] .e) [1605, 5426, 6275, 10344, 17048, 24838, 24838] .e) [1605, 5426, 6275, 10344, 17048, 24838, 25502]
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17048, 24838, 26439] .e) [1605, 5426, 6275, 10344, 17048, 24838, 26990] .e)) [1605, 5426, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17048, 24838, 30006] .e) [1605, 5426, 6275, 10344, 17048, 24838, 31111] .e) [1605, 5426, 6275, 10344, 17048, 24838, 32767]
 (.n
 (.n .e [1605, 5426, 6275, 10344, 17048, 26990] .e) [1605, 5426, 6275, 10344, 17050, 24838] .e)))) [1605, 5426, 6275, 10346, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5426, 10344, 14571, 17048, 24838] .e) [1605, 5427, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5427, 6275, 10344, 17048, 24838, 26439] .e)) [1605, 5428, 5428, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5428, 6005, 6275, 10344, 17048, 24838] .e) [1605, 5428, 6275, 6275, 10344, 17048, 24838] .e)) [1605, 5428, 6275, 6279, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 7603, 10344, 17048, 24838] .e) [1605, 5428, 6275, 7607, 10344, 17048, 24838] .e) [1605, 5428, 6275, 7879, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5428, 6275, 8192, 10344, 17048, 24838] .e) [1605, 5428, 6275, 10344, 10344, 17048, 24838] .e))) [1605, 5428, 6275, 10344, 10348, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 10344, 11885, 17048, 24838] .e) [1605, 5428, 6275, 10344, 14571, 17048, 24838] .e) [1605, 5428, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n .e [1605, 5428, 6275, 10344, 15740, 17048, 24838] .e) [1605, 5428, 6275, 10344, 16384, 17048, 24838] .e)) [1605, 5428, 6275, 10344, 17048, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17048, 17052, 24838] .e) [1605, 5428, 6275, 10344, 17048, 18141, 24838] .e) [1605, 5428, 6275, 10344, 17048, 22456, 24838]
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17048, 22460, 24838] .e) [1605, 5428, 6275, 10344, 17048, 23195, 24838] .e))))))

def T6bbabb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17048, 24838, 24838] .e) [1605, 5428, 6275, 10344, 17048, 24838, 25502]
 (.n .e [1605, 5428, 6275, 10344, 17048, 24838, 26439] .e)) [1605, 5428, 6275, 10344, 17048, 24838, 26990]
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17048, 24838, 27384] .e) [1605, 5428, 6275, 10344, 17048, 24838, 30006] .e)) [1605, 5428, 6275, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17048, 24838, 32767] .e) [1605, 5428, 6275, 10344, 17048, 25502] .e) [1605, 5428, 6275, 10344, 17052, 24838]
 (.n
 (.n .e [1605, 5428, 6275, 10348, 17048, 24838] .e) [1605, 5428, 6279, 10344, 17048, 24838] .e))) [1605, 5429, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5429, 6275, 10344, 17048, 24838, 31111] .e) [1605, 5430, 6275, 7879, 10344, 17048, 24838] .e) [1605, 5430, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5432, 5432, 6275, 10344, 17048, 24838] .e) [1605, 5432, 6005, 6275, 10344, 17048, 24838] .e)) [1605, 5432, 6013, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 6275, 10344, 17048, 24838] .e) [1605, 5432, 6275, 6283, 10344, 17048, 24838] .e) [1605, 5432, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5432, 6275, 7611, 10344, 17048, 24838] .e) [1605, 5432, 6275, 7879, 10344, 17048, 24838] .e)))) [1605, 5432, 6275, 8192, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 10344, 10344, 17048, 24838] .e) [1605, 5432, 6275, 10344, 11885, 17048, 24838]
 (.n .e [1605, 5432, 6275, 10344, 14571, 17048, 24838] .e)) [1605, 5432, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n .e [1605, 5432, 6275, 10344, 16384, 17048, 24838] .e) [1605, 5432, 6275, 10344, 17048, 17048, 24838] .e)) [1605, 5432, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17048, 22456, 24838] .e) [1605, 5432, 6275, 10344, 17048, 23195, 24838] .e) [1605, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17048, 24838, 24838] .e) [1605, 5432, 6275, 10344, 17048, 24838, 24846] .e))) [1605, 5432, 6275, 10344, 17048, 24838, 25502]
 (.n
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17048, 24838, 26439] .e) [1605, 5432, 6275, 10344, 17048, 24838, 26990] .e) [1605, 5432, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17048, 24838, 30006] .e) [1605, 5432, 6275, 10344, 17048, 24838, 30014] .e)) [1605, 5432, 6275, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n .e [1605, 5432, 6275, 10344, 17048, 24838, 32767] .e) [1605, 5432, 6275, 10344, 17048, 24846] .e) [1605, 5432, 6275, 10344, 24838, 25502]
 (.n
 (.n .e [1605, 5432, 6275, 17048, 24838, 26990] .e) [1605, 5432, 6283, 10344, 17048, 24838] .e))))) [1605, 5488, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5488, 6005, 6275, 10344, 17048, 24838] .e) [1605, 5488, 6275, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5488, 6275, 6339, 10344, 17048, 24838] .e)) [1605, 5488, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5488, 6275, 7667, 10344, 17048, 24838] .e) [1605, 5488, 6275, 7879, 10344, 17048, 24838] .e)) [1605, 5488, 6275, 8192, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5488, 6275, 10344, 10344, 17048, 24838] .e) [1605, 5488, 6275, 10344, 11885, 17048, 24838] .e) [1605, 5488, 6275, 10344, 14571, 17048, 24838]
 (.n
 (.n .e [1605, 5488, 6275, 10344, 15736, 17048, 24838] .e) [1605, 5488, 6275, 10344, 16384, 17048, 24838] .e))) [1605, 5488, 6275, 10344, 17048, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17048, 17112, 24838] .e) [1605, 5488, 6275, 10344, 17048, 18141, 24838] .e) [1605, 5488, 6275, 10344, 17048, 22456, 24838]
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17048, 22520, 24838] .e) [1605, 5488, 6275, 10344, 17048, 23195, 24838] .e)) [1605, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17048, 24838, 24838] .e) [1605, 5488, 6275, 10344, 17048, 24838, 24902] .e) [1605, 5488, 6275, 10344, 17048, 24838, 25502]
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17048, 24838, 26439] .e) [1605, 5488, 6275, 10344, 17048, 24838, 26990] .e)))) [1605, 5488, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17048, 24838, 30006] .e) [1605, 5488, 6275, 10344, 17048, 24838, 30070]
 (.n .e [1605, 5488, 6275, 10344, 17048, 24838, 31111] .e)) [1605, 5488, 6275, 10344, 17048, 24838, 32767]
 (.n
 (.n .e [1605, 5488, 6275, 10344, 17048, 24902] .e) [1605, 5488, 6275, 10344, 17112, 24838] .e)) [1605, 5488, 6339, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5489, 6275, 10344, 14571, 17048, 24838] .e) [1605, 5489, 6275, 10344, 17048, 24838] .e) [1605, 5492, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5492, 6275, 10344, 17048, 24838, 26990] .e) [1605, 5496, 6275, 10344, 17048, 18141, 24838] .e))) [1605, 5496, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5552, 5552, 6275, 10344, 17048, 24838] .e) [1605, 5552, 6005, 6275, 10344, 17048, 24838] .e) [1605, 5552, 6133, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5552, 6275, 6275, 10344, 17048, 24838] .e) [1605, 5552, 6275, 7603, 10344, 17048, 24838] .e)) [1605, 5552, 6275, 7879, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5552, 6275, 8192, 10344, 17048, 24838] .e) [1605, 5552, 6275, 10344, 10344, 17048, 24838] .e) [1605, 5552, 6275, 10344, 10472, 17048, 24838]
 (.n
 (.n .e [1605, 5552, 6275, 10344, 11885, 17048, 24838] .e) [1605, 5552, 6275, 10344, 14571, 17048, 24838] .e))))))

def T6bbab : T := .n T6bbaba [1605, 5428, 6275, 10344, 17048, 24838] T6bbabb

def T6bba : T := .n T6bbaa [1605, 5424, 10344, 14571, 17048, 22659, 24838] T6bbab

def T6bbbaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5552, 6275, 10344, 15864, 17048, 24838] .e) [1605, 5552, 6275, 10344, 16384, 17048, 24838]
 (.n .e [1605, 5552, 6275, 10344, 17048, 17048, 24838] .e)) [1605, 5552, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17048, 22456, 24838] .e) [1605, 5552, 6275, 10344, 17048, 23195, 24838] .e)) [1605, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17048, 24838, 24838] .e) [1605, 5552, 6275, 10344, 17048, 24838, 24966] .e) [1605, 5552, 6275, 10344, 17048, 24838, 25502]
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17048, 24838, 26439] .e) [1605, 5552, 6275, 10344, 17048, 24838, 26990] .e))) [1605, 5552, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17048, 24838, 30006] .e) [1605, 5552, 6275, 10344, 17048, 24838, 30134] .e) [1605, 5552, 6275, 10344, 17048, 24838, 31111]
 (.n
 (.n .e [1605, 5552, 6275, 10344, 17048, 24838, 32767] .e) [1605, 5552, 6275, 10344, 17048, 24966] .e)) [1605, 5552, 6275, 10472, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5553, 6275, 10344, 17048, 18141, 24838] .e) [1605, 5553, 6275, 10344, 17048, 24838] .e) [1605, 5554, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5554, 6275, 10344, 17048, 24838, 25502] .e) [1605, 5560, 6275, 10344, 14571, 17048, 24838] .e)))) [1605, 5560, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5936, 6275, 7603, 10344, 17048, 24838] .e) [1605, 5936, 6275, 10344, 15736, 17048, 24838]
 (.n .e [1605, 5936, 6275, 10344, 17048, 24838, 30006] .e)) [1605, 6005, 6275, 6291, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 6005, 6275, 7472, 10344, 17048, 24838] .e) [1605, 6005, 6275, 7603, 10344, 17048, 24838] .e)) [1605, 6005, 6275, 10344, 10360, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 6005, 6275, 10344, 13616, 17048, 24838] .e) [1605, 6005, 6275, 10344, 15736, 17048, 24838] .e) [1605, 6005, 6275, 10344, 15867, 17048, 24838]
 (.n
 (.n .e [1605, 6005, 6275, 10344, 16400, 17048, 24838] .e) [1605, 6005, 6275, 10344, 17048, 21808, 24838] .e))) [1605, 6005, 6275, 10344, 17048, 24838, 24854]
 (.n
 (.n
 (.n
 (.n .e [1605, 6005, 6275, 10344, 17048, 24838, 30006] .e) [1605, 6005, 6275, 10344, 17048, 24838, 32126] .e) [1605, 6005, 6275, 10344, 17048, 24838, 32183]
 (.n
 (.n .e [1605, 6005, 6275, 10344, 17048, 24854] .e) [1605, 6005, 6275, 10344, 17048, 25502, 30006] .e)) [1605, 6005, 6275, 10344, 17048, 26990, 30006]
 (.n
 (.n
 (.n .e [1605, 6005, 6275, 10360, 17048, 24838] .e) [1605, 6005, 6275, 15736, 17048, 24838, 26990] .e) [1605, 6005, 6275, 15736, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 6005, 6291, 10344, 17048, 24838] .e) [1605, 6005, 7603, 10344, 14571, 17048, 24838] .e))))) [1605, 6005, 7603, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 6005, 7603, 10344, 17048, 24838, 31111] .e) [1605, 6275, 7472, 10344, 17048, 22456, 24838]
 (.n .e [1605, 6275, 7472, 10344, 17048, 24838, 30006] .e)) [1605, 6275, 7603, 8224, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 6275, 7603, 10344, 13616, 17048, 24838] .e) [1605, 6275, 7603, 10344, 17048, 17080, 24838] .e)) [1605, 6275, 7603, 10344, 17048, 21808, 24838]
 (.n
 (.n
 (.n .e [1605, 6275, 7603, 10344, 17048, 22456, 24838] .e) [1605, 6275, 7603, 10344, 17048, 22525, 24838] .e) [1605, 6275, 7603, 10344, 17048, 24838, 24870]
 (.n
 (.n .e [1605, 6275, 7603, 10344, 17048, 24838, 30006] .e) [1605, 6275, 7603, 10344, 17048, 24838, 30583] .e))) [1605, 6275, 7603, 10344, 17048, 24838, 30654]
 (.n
 (.n
 (.n
 (.n .e [1605, 6275, 7603, 10344, 17048, 24870] .e) [1605, 6275, 7603, 10344, 17048, 25502, 30006] .e) [1605, 6275, 7603, 10344, 17048, 26990, 30006]
 (.n
 (.n .e [1605, 6275, 7603, 10344, 17080, 24838] .e) [1605, 6275, 7603, 10344, 22456, 24838, 25502] .e)) [1605, 6275, 7603, 10344, 22456, 24838, 27384]
 (.n
 (.n
 (.n .e [1605, 6275, 8183, 10344, 17048, 24838, 30006] .e) [1605, 6275, 10344, 13616, 17048, 22456, 24838] .e) [1605, 6275, 10344, 15736, 17048, 21808, 24838]
 (.n
 (.n .e [1605, 6275, 10344, 15736, 17048, 22456, 24838] .e) [1605, 6275, 10344, 15736, 17048, 22525, 24838] .e)))) [1605, 6275, 10344, 15736, 22456, 24838, 25502]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 6275, 10344, 15736, 22456, 24838, 27384] .e) [1605, 6275, 10344, 15867, 17048, 22456, 24838]
 (.n .e [1605, 6275, 15736, 17048, 22456, 24838, 26990] .e)) [1605, 6275, 15736, 17048, 22456, 24838, 27384]
 (.n
 (.n .e [1605, 6275, 15736, 22456, 24838, 27384] .e) [1605, 7603, 10344, 14571, 17048, 22456, 24838] .e)) [1605, 7603, 10344, 14571, 17048, 24838, 30006]
 (.n
 (.n
 (.n .e [1605, 7603, 10344, 17048, 22456, 23195, 24838] .e) [1605, 7603, 10344, 17048, 22456, 24838, 31111] .e) [1605, 7603, 10344, 17048, 23195, 24838, 30006]
 (.n
 (.n .e [1605, 7603, 10344, 17048, 24838, 30006, 31111] .e) [1607, 1607, 5424, 6275, 10344, 17048, 24838] .e))) [1607, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1607, 4096, 5424, 6275, 10344, 17048, 24838] .e) [1607, 5424, 5424, 6275, 10344, 17048, 24838] .e) [1607, 5424, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1607, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1607, 5424, 6007, 6275, 10344, 17048, 24838] .e)) [1607, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1607, 5424, 6275, 7879, 10344, 17048, 24838] .e) [1607, 5424, 6275, 8192, 10344, 17048, 24838]
 (.n
 (.n .e [1607, 5424, 6275, 10344, 10344, 17048, 24838] .e) [1607, 5424, 6275, 10344, 10346, 17048, 24838] .e))))))

def T6bbbab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 10344, 11887, 17048, 24838] .e) [1607, 5424, 6275, 10344, 14571, 17048, 24838]
 (.n .e [1607, 5424, 6275, 10344, 15736, 17048, 24838] .e)) [1607, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17048, 17048, 24838] .e) [1607, 5424, 6275, 10344, 17048, 17050, 24838] .e)) [1607, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17048, 18143, 24838] .e) [1607, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1607, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17048, 24838] .e) [1607, 5424, 6275, 10344, 17048, 24838, 24838] .e))) [1607, 5424, 6275, 10344, 17048, 24838, 25502]
 (.n
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17048, 24838, 26439] .e) [1607, 5424, 6275, 10344, 17048, 24838, 26990] .e) [1607, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17048, 24838, 30006] .e) [1607, 5424, 6275, 10344, 17048, 24838, 31111] .e)) [1607, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n
 (.n
 (.n .e [1607, 5424, 6275, 10344, 17048, 26990] .e) [1607, 5424, 6275, 10344, 17050, 24838] .e) [1607, 5424, 6275, 10346, 17048, 24838]
 (.n
 (.n .e [1607, 5424, 10344, 14571, 17048, 24838] .e) [1607, 5426, 6275, 10344, 17048, 24838] .e)))) [1613, 1613, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1613, 2048, 5424, 6275, 10344, 17048, 24838] .e) [1613, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1613, 5424, 5424, 6275, 10344, 17048, 24838] .e)) [1613, 5424, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1613, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1613, 5424, 6013, 6275, 10344, 17048, 24838] .e)) [1613, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 6283, 10344, 17048, 24838] .e) [1613, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1613, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n
 (.n .e [1613, 5424, 6275, 7887, 10344, 17048, 24838] .e) [1613, 5424, 6275, 8192, 10344, 17048, 24838] .e))) [1613, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 10344, 11885, 17048, 24838] .e) [1613, 5424, 6275, 10344, 14571, 17048, 24838] .e) [1613, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n .e [1613, 5424, 6275, 10344, 16384, 17048, 24838] .e) [1613, 5424, 6275, 10344, 17048, 17048, 24838] .e)) [1613, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1613, 5424, 6275, 10344, 17048, 23195, 24838] .e) [1613, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1613, 5424, 6275, 10344, 17048, 24838, 24838] .e) [1613, 5424, 6275, 10344, 17048, 24838, 24846] .e))))) [1613, 5424, 6275, 10344, 17048, 24838, 25502]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 10344, 17048, 24838, 26439] .e) [1613, 5424, 6275, 10344, 17048, 24838, 26447]
 (.n .e [1613, 5424, 6275, 10344, 17048, 24838, 26990] .e)) [1613, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n .e [1613, 5424, 6275, 10344, 17048, 24838, 30006] .e) [1613, 5424, 6275, 10344, 17048, 24838, 31111] .e)) [1613, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n
 (.n
 (.n .e [1613, 5424, 6275, 10344, 17048, 24846] .e) [1613, 5424, 6275, 10344, 24838, 25502] .e) [1613, 5424, 6275, 17048, 24838, 26990]
 (.n
 (.n .e [1613, 5424, 6283, 10344, 17048, 24838] .e) [1613, 5432, 6275, 10344, 17048, 24838] .e))) [1621, 1621, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1621, 2048, 5424, 6275, 10344, 17048, 24838] .e) [1621, 4096, 5424, 6275, 10344, 17048, 24838] .e) [1621, 5424, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1621, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1621, 5424, 6275, 6275, 10344, 17048, 24838] .e)) [1621, 5424, 6275, 6291, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1621, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1621, 5424, 6275, 7879, 10344, 17048, 24838] .e) [1621, 5424, 6275, 7895, 10344, 17048, 24838]
 (.n
 (.n .e [1621, 5424, 6275, 8192, 10344, 17048, 24838] .e) [1621, 5424, 6275, 10344, 10344, 17048, 24838] .e)))) [1621, 5424, 6275, 10344, 10360, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1621, 5424, 6275, 10344, 11885, 17048, 24838] .e) [1621, 5424, 6275, 10344, 11901, 17048, 24838]
 (.n .e [1621, 5424, 6275, 10344, 14571, 17048, 24838] .e)) [1621, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n .e [1621, 5424, 6275, 10344, 16384, 17048, 24838] .e) [1621, 5424, 6275, 10344, 17048, 17048, 24838] .e)) [1621, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [1621, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1621, 5424, 6275, 10344, 17048, 23195, 24838] .e) [1621, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1621, 5424, 6275, 10344, 17048, 24838, 24838] .e) [1621, 5424, 6275, 10344, 17048, 24838, 24854] .e))) [1621, 5424, 6275, 10344, 17048, 24838, 25502]
 (.n
 (.n
 (.n
 (.n .e [1621, 5424, 6275, 10344, 17048, 24838, 26439] .e) [1621, 5424, 6275, 10344, 17048, 24838, 26455] .e) [1621, 5424, 6275, 10344, 17048, 24838, 26990]
 (.n
 (.n .e [1621, 5424, 6275, 10344, 17048, 24838, 27384] .e) [1621, 5424, 6275, 10344, 17048, 24838, 30006] .e)) [1621, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n .e [1621, 5424, 6275, 10344, 17048, 24838, 32767] .e) [1621, 5424, 6275, 10344, 17048, 24854] .e) [1621, 5424, 6275, 10360, 17048, 24838]
 (.n
 (.n .e [1621, 5424, 6291, 10344, 17048, 24838] .e) [1629, 5424, 6275, 10344, 15736, 17048, 24838] .e))))))

def T6bbba : T := .n T6bbbaa [1607, 5424, 6275, 10344, 11885, 17048, 24838] T6bbbab

def T6bbbba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1637, 1637, 5424, 6275, 10344, 17048, 24838] .e) [1637, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1637, 4096, 5424, 6275, 10344, 17048, 24838] .e)) [1637, 5424, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1637, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1637, 5424, 6275, 6275, 10344, 17048, 24838] .e)) [1637, 5424, 6275, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1637, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1637, 5424, 6275, 7879, 10344, 17048, 24838] .e) [1637, 5424, 6275, 7911, 10344, 17048, 24838]
 (.n
 (.n .e [1637, 5424, 6275, 8192, 10344, 17048, 24838] .e) [1637, 5424, 6275, 10344, 10344, 17048, 24838] .e))) [1637, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1637, 5424, 6275, 10344, 14571, 17048, 24838] .e) [1637, 5424, 6275, 10344, 15736, 17048, 24838] .e) [1637, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17048, 17048, 24838] .e) [1637, 5424, 6275, 10344, 17048, 17080, 24838] .e)) [1637, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17048, 18173, 24838] .e) [1637, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1637, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17048, 24838] .e) [1637, 5424, 6275, 10344, 17048, 24838, 24838] .e)))) [1637, 5424, 6275, 10344, 17048, 24838, 24870]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17048, 24838, 25502] .e) [1637, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n .e [1637, 5424, 6275, 10344, 17048, 24838, 26471] .e)) [1637, 5424, 6275, 10344, 17048, 24838, 26990]
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17048, 24838, 27384] .e) [1637, 5424, 6275, 10344, 17048, 24838, 30006] .e)) [1637, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n .e [1637, 5424, 6275, 10344, 17048, 24838, 32767] .e) [1637, 5424, 6275, 10344, 17048, 24870] .e) [1637, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n .e [1637, 5424, 6275, 14571, 17048, 24838] .e) [1637, 5424, 6307, 10344, 17048, 24838] .e))) [1637, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1645, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1645, 5424, 6275, 10344, 17048, 24838] .e) [1653, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1653, 5424, 6275, 10344, 17048, 24838, 27384] .e) [1733, 1733, 5424, 6275, 10344, 17048, 24838] .e)) [1733, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1733, 4096, 5424, 6275, 10344, 17048, 24838] .e) [1733, 5424, 5424, 6275, 10344, 17048, 24838] .e) [1733, 5424, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1733, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1733, 5424, 6133, 6275, 10344, 17048, 24838] .e))))) [1733, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1733, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1733, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n .e [1733, 5424, 6275, 8192, 10344, 17048, 24838] .e)) [1733, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n
 (.n .e [1733, 5424, 6275, 10344, 10472, 17048, 24838] .e) [1733, 5424, 6275, 10344, 11885, 17048, 24838] .e)) [1733, 5424, 6275, 10344, 12013, 17048, 24838]
 (.n
 (.n
 (.n .e [1733, 5424, 6275, 10344, 14571, 17048, 24838] .e) [1733, 5424, 6275, 10344, 15736, 17048, 24838] .e) [1733, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17048, 17048, 24838] .e) [1733, 5424, 6275, 10344, 17048, 18141, 24838] .e))) [1733, 5424, 6275, 10344, 17048, 22456, 24838]
 (.n
 (.n
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17048, 23195, 24838] .e) [1733, 5424, 6275, 10344, 17048, 24838] .e) [1733, 5424, 6275, 10344, 17048, 24838, 24838]
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17048, 24838, 24966] .e) [1733, 5424, 6275, 10344, 17048, 24838, 25502] .e)) [1733, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17048, 24838, 26567] .e) [1733, 5424, 6275, 10344, 17048, 24838, 26990] .e) [1733, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17048, 24838, 30006] .e) [1733, 5424, 6275, 10344, 17048, 24838, 31111] .e)))) [1733, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17048, 24966] .e) [1733, 5424, 6275, 10472, 17048, 24838]
 (.n .e [1733, 5552, 6275, 10344, 17048, 24838] .e)) [1735, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1735, 5424, 6275, 10344, 17048, 24838, 25502] .e) [1741, 5424, 6275, 10344, 14571, 17048, 24838] .e)) [1741, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1749, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1749, 5424, 6275, 10344, 17048, 24838] .e) [1861, 1861, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1861, 2048, 5424, 6275, 10344, 17048, 24838] .e) [1861, 4096, 5424, 6275, 10344, 17048, 24838] .e))) [1861, 5424, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1861, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1861, 5424, 6275, 6275, 10344, 17048, 24838] .e) [1861, 5424, 6275, 6531, 10344, 17048, 24838]
 (.n
 (.n .e [1861, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1861, 5424, 6275, 7879, 10344, 17048, 24838] .e)) [1861, 5424, 6275, 8135, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1861, 5424, 6275, 8192, 10344, 17048, 24838] .e) [1861, 5424, 6275, 10344, 10344, 17048, 24838] .e) [1861, 5424, 6275, 10344, 10600, 17048, 24838]
 (.n
 (.n .e [1861, 5424, 6275, 10344, 11885, 17048, 24838] .e) [1861, 5424, 6275, 10344, 12141, 17048, 24838] .e))))))

def T6bbbbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1861, 5424, 6275, 10344, 15736, 17048, 24838] .e) [1861, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n .e [1861, 5424, 6275, 10344, 17048, 17048, 24838] .e)) [1861, 5424, 6275, 10344, 17048, 17304, 24838]
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17048, 18141, 24838] .e) [1861, 5424, 6275, 10344, 17048, 18397, 24838] .e)) [1861, 5424, 6275, 10344, 17048, 22456, 24838]
 (.n
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17048, 23195, 24838] .e) [1861, 5424, 6275, 10344, 17048, 24838] .e) [1861, 5424, 6275, 10344, 17048, 24838, 24838]
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17048, 24838, 25502] .e) [1861, 5424, 6275, 10344, 17048, 24838, 26439] .e))) [1861, 5424, 6275, 10344, 17048, 24838, 26990]
 (.n
 (.n
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17048, 24838, 27384] .e) [1861, 5424, 6275, 10344, 17048, 24838, 30006] .e) [1861, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n
 (.n .e [1861, 5424, 6275, 10344, 17048, 24838, 32767] .e) [1861, 5424, 6275, 10344, 17304, 24838] .e)) [1861, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n
 (.n .e [1861, 5424, 6531, 10344, 17048, 24838] .e) [1863, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1863, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1877, 5424, 6275, 10344, 17048, 24838] .e) [1877, 5424, 6275, 10344, 17048, 24838, 25502] .e)))) [1893, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1893, 5424, 6275, 10344, 17048, 24838, 26990] .e) [2049, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n .e [3653, 5424, 6005, 6275, 10344, 17048, 24838] .e)) [3653, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n .e [3653, 5424, 6275, 10344, 17048, 24838, 26439] .e) [5424, 5428, 6275, 10344, 17048, 18141, 24838] .e)) [5424, 5701, 6275, 10344, 11885, 17048, 24838]
 (.n
 (.n
 (.n .e [5424, 5701, 6275, 10344, 17048, 18141, 24838] .e) [5424, 5701, 6275, 10344, 17048, 24838, 26439] .e) [5424, 6005, 6275, 9797, 10344, 17048, 24838]
 (.n
 (.n .e [5424, 6005, 6275, 10344, 10345, 17048, 24838] .e) [5424, 6005, 6275, 10344, 11885, 17048, 24838] .e))) [5424, 6005, 6275, 10344, 17048, 17049, 24838]
 (.n
 (.n
 (.n
 (.n .e [5424, 6005, 6275, 10344, 17048, 17989, 24838] .e) [5424, 6005, 6275, 10344, 17048, 18141, 24838] .e) [5424, 6005, 6275, 10344, 17048, 24838, 24839]
 (.n
 (.n .e [5424, 6005, 6275, 10344, 17048, 24838, 26439] .e) [5424, 6005, 6275, 10344, 17048, 24838, 26591] .e)) [5424, 6005, 6275, 10344, 17048, 24838, 28413]
 (.n
 (.n
 (.n .e [5424, 6005, 6275, 10344, 17048, 24838, 28527] .e) [5424, 6005, 6275, 10344, 17048, 24839] .e) [5424, 6005, 6275, 10344, 17048, 26439, 26990]
 (.n
 (.n .e [5424, 6005, 6275, 10344, 17048, 26439, 31111] .e) [5424, 6005, 6275, 10344, 17049, 24838] .e))))) [5424, 6005, 6275, 10344, 18141, 23195, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [5424, 6005, 6275, 10344, 18141, 24838, 25502] .e) [5424, 6005, 6275, 10344, 18141, 24838, 27384]
 (.n .e [5424, 6005, 6275, 10345, 17048, 24838] .e)) [5424, 6005, 6275, 11885, 14571, 17048, 24838]
 (.n
 (.n .e [5424, 6005, 6275, 11885, 17048, 24838, 26990] .e) [5424, 6275, 6279, 10344, 17048, 18141, 24838] .e)) [5424, 6275, 7879, 9797, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [5424, 6275, 7879, 10344, 17048, 17989, 24838] .e) [5424, 6275, 7879, 10344, 17048, 18141, 24838] .e) [5424, 6275, 7879, 10344, 17048, 24838, 26439]
 (.n
 (.n .e [5424, 6275, 7879, 10344, 17048, 24838, 26591] .e) [5424, 6275, 7879, 10344, 17048, 26439, 26990] .e))) [5424, 6275, 7879, 10344, 17048, 26439, 31111]
 (.n
 (.n
 (.n
 (.n .e [5424, 6275, 7879, 10344, 18141, 23195, 24838] .e) [5424, 6275, 7879, 10344, 18141, 24838, 25502] .e) [5424, 6275, 7879, 10344, 18141, 24838, 27384]
 (.n
 (.n .e [5424, 6275, 8183, 10344, 17048, 18141, 24838] .e) [5424, 6275, 8183, 10344, 17048, 24838, 26439] .e)) [5424, 6275, 8196, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [5424, 6275, 9797, 10344, 17048, 18141, 24838] .e) [5424, 6275, 10344, 10348, 17048, 18141, 24838] .e) [5424, 6275, 10344, 11885, 17048, 17989, 24838]
 (.n
 (.n .e [5424, 6275, 10344, 11885, 17048, 18141, 24838] .e) [5424, 6275, 10344, 11885, 17048, 22525, 24838] .e)))) [5424, 6275, 10344, 11885, 18141, 23195, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [5424, 6275, 10344, 11885, 18141, 24838, 25502] .e) [5424, 6275, 10344, 11885, 18141, 24838, 27384] .e) [5424, 6275, 10344, 16111, 17048, 18141, 24838]
 (.n
 (.n .e [5424, 6275, 10344, 16253, 17048, 18141, 24838] .e) [5424, 6275, 10348, 17048, 18141, 24838] .e)) [5424, 6275, 11885, 14571, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [5424, 6275, 11885, 17048, 18141, 24838, 26990] .e) [5424, 6279, 10344, 17048, 18141, 24838] .e) [5424, 7879, 10344, 14571, 17048, 18141, 24838]
 (.n
 (.n .e [5424, 7879, 10344, 14571, 17048, 24838, 26439] .e) [5424, 7879, 10344, 17048, 18141, 24838, 31111] .e))) [5424, 7879, 10344, 17048, 24838, 26439, 31111]
 (.n
 (.n
 (.n
 (.n .e [5424, 7879, 10344, 17048, 26439, 31111] .e) [5428, 6275, 10344, 17048, 18141, 24838] .e) [6005, 6275, 7603, 10344, 11885, 17048, 24838]
 (.n
 (.n .e [6005, 6275, 7603, 10344, 17048, 18141, 24838] .e) [6005, 6275, 7603, 10344, 17048, 24838, 26439] .e)) [6005, 6275, 10344, 11885, 15736, 17048, 24838]
 (.n
 (.n
 (.n .e [6005, 6275, 10344, 11885, 17048, 24838, 30006] .e) [6005, 6275, 10344, 15736, 17048, 18141, 24838] .e) [6005, 6275, 10344, 15736, 17048, 24838, 26439]
 (.n
 (.n .e [6005, 6275, 10344, 17048, 18141, 24838, 30006] .e) [6005, 6275, 10344, 17048, 24838, 26439, 30006] .e))))))

def T6bbbb : T := .n T6bbbba [1861, 5424, 6275, 10344, 14571, 17048, 24838] T6bbbbb

def T6bbb : T := .n T6bbba [1629, 5424, 6275, 10344, 17048, 24838] T6bbbb

def T6bb : T := .n T6bba [1605, 5552, 6275, 10344, 15736, 17048, 24838] T6bbb

def T6b : T := .n T6ba [1605, 5424, 6283, 7887, 10344, 17048, 24838] T6bb

def T6 : T := .n T6a [1605, 5424, 6275, 10344, 16384, 17048, 24854] T6b

def T7aaaaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [0, 0, 1605, 5424, 6275, 10344, 17048, 24838] .e) [0, 1, 1605, 5424, 6275, 10344, 17048, 24838] .e) [0, 2, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [0, 4, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [0, 8, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [0, 16, 1605, 5424, 6275, 10344, 17048, 24838] .e) [0, 32, 1605, 5424, 6275, 10344, 17048, 24838] .e) [0, 64, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [0, 128, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [0, 256, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [0, 512, 1605, 5424, 6275, 10344, 17048, 24838] .e) [0, 1024, 1605, 5424, 6275, 10344, 17048, 24838] .e) [0, 1605, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [0, 1605, 2048, 5424, 6275, 10344, 17048, 24838] .e)) [0, 1605, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [0, 1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [0, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e) [0, 1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n .e [0, 1605, 5424, 6275, 7603, 10344, 17048, 24838] .e)))) [0, 1605, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [0, 1605, 5424, 6275, 8192, 10344, 17048, 24838] .e) [0, 1605, 5424, 6275, 10344, 10344, 17048, 24838] .e) [0, 1605, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n .e [0, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e)) [0, 1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n
 (.n .e [0, 1605, 5424, 6275, 10344, 16384, 17048, 24838] .e) [0, 1605, 5424, 6275, 10344, 17048, 17048, 24838] .e) [0, 1605, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n .e [0, 1605, 5424, 6275, 10344, 17048, 22456, 24838] .e))) [0, 1605, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n
 (.n .e [0, 1605, 5424, 6275, 10344, 17048, 24838] .e) [0, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [0, 1605, 5424, 6275, 10344, 17048, 24838, 25502]
 (.n .e [0, 1605, 5424, 6275, 10344, 17048, 24838, 26439] .e)) [0, 1605, 5424, 6275, 10344, 17048, 24838, 26990]
 (.n
 (.n .e [0, 1605, 5424, 6275, 10344, 17048, 24838, 27384] .e) [0, 1605, 5424, 6275, 10344, 17048, 24838, 30006]
 (.n .e [0, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e)))))

def T7aaaab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1, 1, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1, 2, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1, 4, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1, 8, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [1, 16, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1, 32, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1, 64, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1, 128, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1, 256, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [1, 512, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1, 1024, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1, 1605, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1, 1605, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1, 1605, 4096, 5424, 6275, 10344, 17048, 24838] .e)) [1, 1605, 5424, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1, 1605, 5424, 5425, 6275, 10344, 17048, 24838] .e) [1, 1605, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n .e [1, 1605, 5424, 6275, 6275, 10344, 17048, 24838] .e)))) [1, 1605, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e) [1, 1605, 5424, 6275, 8192, 10344, 17048, 24838] .e) [1, 1605, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n .e [1, 1605, 5424, 6275, 10344, 10345, 17048, 24838] .e)) [1, 1605, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e) [1, 1605, 5424, 6275, 10344, 15736, 17048, 24838] .e) [1, 1605, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 17048, 24838] .e))) [1, 1605, 5424, 6275, 10344, 17048, 17049, 24838]
 (.n
 (.n
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 18141, 24838] .e) [1, 1605, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1, 1605, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [1, 1605, 5424, 6275, 10344, 17048, 24838, 24838]
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 24838, 24839] .e) [1, 1605, 5424, 6275, 10344, 17048, 24838, 25502]
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 24838, 26439] .e)))))

def T7aaaa : T := .n T7aaaaa [0, 1605, 5424, 6275, 10344, 17048, 24838, 32767] T7aaaab

def T7aaaba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 24838, 27384] .e) [1, 1605, 5424, 6275, 10344, 17048, 24838, 30006] .e) [1, 1605, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n .e [1, 1605, 5424, 6275, 10344, 17048, 24838, 32767] .e)) [1, 1605, 5424, 6275, 10344, 17048, 24839]
 (.n
 (.n
 (.n .e [1, 1605, 5424, 6275, 10344, 17049, 24838] .e) [1, 1605, 5424, 6275, 10345, 17048, 24838] .e) [1, 1605, 5424, 7603, 10344, 17048, 24838]
 (.n .e [1, 1605, 5425, 6275, 10344, 17048, 24838] .e))) [1, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [2, 2, 1605, 5424, 6275, 10344, 17048, 24838] .e) [2, 4, 1605, 5424, 6275, 10344, 17048, 24838] .e) [2, 8, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [2, 16, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [2, 32, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [2, 64, 1605, 5424, 6275, 10344, 17048, 24838] .e) [2, 128, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [2, 256, 1605, 5424, 6275, 10344, 17048, 24838] .e)))) [2, 512, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [2, 1024, 1605, 5424, 6275, 10344, 17048, 24838] .e) [2, 1605, 1605, 5424, 6275, 10344, 17048, 24838] .e) [2, 1605, 1607, 5424, 6275, 10344, 17048, 24838]
 (.n .e [2, 1605, 2048, 5424, 6275, 10344, 17048, 24838] .e)) [2, 1605, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [2, 1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [2, 1605, 5424, 5426, 6275, 10344, 17048, 24838] .e) [2, 1605, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n .e [2, 1605, 5424, 6275, 6275, 10344, 17048, 24838] .e))) [2, 1605, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e) [2, 1605, 5424, 6275, 8192, 10344, 17048, 24838] .e) [2, 1605, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n .e [2, 1605, 5424, 6275, 10344, 10346, 17048, 24838] .e)) [2, 1605, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n
 (.n .e [2, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e) [2, 1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n .e [2, 1605, 5424, 6275, 10344, 16384, 17048, 24838] .e)))))

def T7aaabb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6275, 10344, 17048, 17050, 24838] .e) [2, 1605, 5424, 6275, 10344, 17048, 18141, 24838] .e) [2, 1605, 5424, 6275, 10344, 17048, 22456, 24838]
 (.n .e [2, 1605, 5424, 6275, 10344, 17048, 23195, 24838] .e)) [2, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [2, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e) [2, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n .e [2, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e))) [2, 1605, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n
 (.n .e [2, 1605, 5424, 6275, 10344, 17048, 24838, 30006] .e) [2, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e) [2, 1605, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n .e [2, 1605, 5424, 6275, 10344, 17048, 26990] .e)) [2, 1605, 5424, 6275, 10344, 17050, 24838]
 (.n
 (.n .e [2, 1605, 5424, 6275, 10346, 17048, 24838] .e) [2, 1605, 5424, 10344, 14571, 17048, 24838]
 (.n .e [2, 1605, 5426, 6275, 10344, 17048, 24838] .e)))) [2, 1607, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [3, 1605, 5424, 6275, 10344, 17048, 24838] .e) [3, 1605, 5424, 6275, 10344, 17048, 24838, 26439] .e) [4, 4, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [4, 8, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [4, 16, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [4, 32, 1605, 5424, 6275, 10344, 17048, 24838] .e) [4, 64, 1605, 5424, 6275, 10344, 17048, 24838] .e) [4, 128, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [4, 256, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [4, 512, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [4, 1024, 1605, 5424, 6275, 10344, 17048, 24838] .e) [4, 1605, 1605, 5424, 6275, 10344, 17048, 24838] .e) [4, 1605, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n .e [4, 1605, 4096, 5424, 6275, 10344, 17048, 24838] .e)) [4, 1605, 5424, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [4, 1605, 5424, 5428, 6275, 10344, 17048, 24838] .e) [4, 1605, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n .e [4, 1605, 5424, 6275, 6275, 10344, 17048, 24838] .e)))))

def T7aaab : T := .n T7aaaba [2, 1605, 5424, 6275, 10344, 17048, 17048, 24838] T7aaabb

def T7aaa : T := .n T7aaaa [1, 1605, 5424, 6275, 10344, 17048, 24838, 26990] T7aaab

def T7aabaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 7603, 10344, 17048, 24838] .e) [4, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e) [4, 1605, 5424, 6275, 8192, 10344, 17048, 24838]
 (.n .e [4, 1605, 5424, 6275, 10344, 10344, 17048, 24838] .e)) [4, 1605, 5424, 6275, 10344, 10348, 17048, 24838]
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 11885, 17048, 24838] .e) [4, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e) [4, 1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n .e [4, 1605, 5424, 6275, 10344, 16384, 17048, 24838] .e))) [4, 1605, 5424, 6275, 10344, 17048, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 17052, 24838] .e) [4, 1605, 5424, 6275, 10344, 17048, 18141, 24838] .e) [4, 1605, 5424, 6275, 10344, 17048, 22456, 24838]
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 23195, 24838] .e)) [4, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [4, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e) [4, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e)))) [4, 1605, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 24838, 30006] .e) [4, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e) [4, 1605, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 25502] .e)) [4, 1605, 5424, 6275, 10344, 17052, 24838]
 (.n
 (.n
 (.n .e [4, 1605, 5424, 6275, 10348, 17048, 24838] .e) [4, 1605, 5424, 6279, 10344, 17048, 24838] .e) [4, 1605, 5428, 6275, 10344, 17048, 24838]
 (.n .e [4, 5424, 6275, 10344, 17048, 18141, 24838] .e))) [5, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [5, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e) [6, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e) [6, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [8, 8, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [8, 16, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [8, 32, 1605, 5424, 6275, 10344, 17048, 24838] .e) [8, 64, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [8, 128, 1605, 5424, 6275, 10344, 17048, 24838] .e)))))

def T7aabab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [8, 512, 1605, 5424, 6275, 10344, 17048, 24838] .e) [8, 1024, 1605, 5424, 6275, 10344, 17048, 24838] .e) [8, 1605, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [8, 1605, 1613, 5424, 6275, 10344, 17048, 24838] .e)) [8, 1605, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [8, 1605, 4096, 5424, 6275, 10344, 17048, 24838] .e) [8, 1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [8, 1605, 5424, 5432, 6275, 10344, 17048, 24838]
 (.n .e [8, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e))) [8, 1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 6283, 10344, 17048, 24838] .e) [8, 1605, 5424, 6275, 7603, 10344, 17048, 24838] .e) [8, 1605, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n .e [8, 1605, 5424, 6275, 8192, 10344, 17048, 24838] .e)) [8, 1605, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 11885, 17048, 24838] .e) [8, 1605, 5424, 6275, 10344, 14571, 17048, 24838]
 (.n .e [8, 1605, 5424, 6275, 10344, 15736, 17048, 24838] .e)))) [8, 1605, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 17048, 17048, 24838] .e) [8, 1605, 5424, 6275, 10344, 17048, 18141, 24838] .e) [8, 1605, 5424, 6275, 10344, 17048, 22456, 24838]
 (.n .e [8, 1605, 5424, 6275, 10344, 17048, 23195, 24838] .e)) [8, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [8, 1605, 5424, 6275, 10344, 17048, 24838, 24846] .e) [8, 1605, 5424, 6275, 10344, 17048, 24838, 25502]
 (.n .e [8, 1605, 5424, 6275, 10344, 17048, 24838, 26439] .e))) [8, 1605, 5424, 6275, 10344, 17048, 24838, 26990]
 (.n
 (.n
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 17048, 24838, 27384] .e) [8, 1605, 5424, 6275, 10344, 17048, 24838, 30006] .e) [8, 1605, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n .e [8, 1605, 5424, 6275, 10344, 17048, 24838, 32767] .e)) [8, 1605, 5424, 6275, 10344, 17048, 24846]
 (.n
 (.n .e [8, 1605, 5424, 6275, 10344, 24838, 25502] .e) [8, 1605, 5424, 6275, 17048, 24838, 26990]
 (.n .e [8, 1605, 5424, 6283, 10344, 17048, 24838] .e)))))

def T7aaba : T := .n T7aabaa [8, 256, 1605, 5424, 6275, 10344, 17048, 24838] T7aabab

def T7aabba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [8, 1613, 5424, 6275, 10344, 17048, 24838] .e) [16, 16, 1605, 5424, 6275, 10344, 17048, 24838] .e) [16, 32, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [16, 64, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [16, 128, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [16, 256, 1605, 5424, 6275, 10344, 17048, 24838] .e) [16, 512, 1605, 5424, 6275, 10344, 17048, 24838] .e) [16, 1024, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [16, 1605, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [16, 1605, 1621, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [16, 1605, 2048, 5424, 6275, 10344, 17048, 24838] .e) [16, 1605, 4096, 5424, 6275, 10344, 17048, 24838] .e) [16, 1605, 5424, 5424, 6275, 10344, 17048, 24838]
 (.n .e [16, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e)) [16, 1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [16, 1605, 5424, 6275, 6291, 10344, 17048, 24838] .e) [16, 1605, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n .e [16, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e)))) [16, 1605, 5424, 6275, 8192, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 10344, 17048, 24838] .e) [16, 1605, 5424, 6275, 10344, 10360, 17048, 24838] .e) [16, 1605, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n .e [16, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e)) [16, 1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 16384, 17048, 24838] .e) [16, 1605, 5424, 6275, 10344, 17048, 17048, 24838] .e) [16, 1605, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 22456, 24838] .e))) [16, 1605, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 24838] .e) [16, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [16, 1605, 5424, 6275, 10344, 17048, 24838, 24854]
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e)) [16, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e) [16, 1605, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 24838, 30006] .e)))))

def T7aabbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 24838, 32767] .e) [16, 1605, 5424, 6275, 10344, 17048, 24854] .e) [16, 1605, 5424, 6275, 10344, 18141, 24838]
 (.n .e [16, 1605, 5424, 6275, 10360, 17048, 24838] .e)) [16, 1605, 5424, 6291, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [16, 1605, 6005, 6275, 10344, 17048, 24838] .e) [16, 1621, 5424, 6275, 10344, 17048, 24838] .e) [24, 1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n .e [24, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [32, 32, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [32, 64, 1605, 5424, 6275, 10344, 17048, 24838] .e) [32, 128, 1605, 5424, 6275, 10344, 17048, 24838] .e) [32, 256, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [32, 512, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [32, 1024, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [32, 1605, 1605, 5424, 6275, 10344, 17048, 24838] .e) [32, 1605, 1637, 5424, 6275, 10344, 17048, 24838]
 (.n .e [32, 1605, 2048, 5424, 6275, 10344, 17048, 24838] .e)))) [32, 1605, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [32, 1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [32, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e) [32, 1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n .e [32, 1605, 5424, 6275, 6307, 10344, 17048, 24838] .e)) [32, 1605, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e) [32, 1605, 5424, 6275, 8192, 10344, 17048, 24838] .e) [32, 1605, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n .e [32, 1605, 5424, 6275, 10344, 11885, 17048, 24838] .e))) [32, 1605, 5424, 6275, 10344, 14571, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6275, 10344, 15736, 17048, 24838] .e) [32, 1605, 5424, 6275, 10344, 16384, 17048, 24838] .e) [32, 1605, 5424, 6275, 10344, 17048, 17048, 24838]
 (.n .e [32, 1605, 5424, 6275, 10344, 17048, 17080, 24838] .e)) [32, 1605, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n .e [32, 1605, 5424, 6275, 10344, 17048, 22456, 24838] .e) [32, 1605, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n .e [32, 1605, 5424, 6275, 10344, 17048, 24838] .e)))))

def T7aabb : T := .n T7aabba [16, 1605, 5424, 6275, 10344, 17048, 24838, 31111] T7aabbb

def T7aab : T := .n T7aaba [8, 1605, 5432, 6275, 10344, 17048, 24838] T7aabb

def T7aa : T := .n T7aaa [4, 1605, 5424, 6275, 6279, 10344, 17048, 24838] T7aab

def T7abaaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6275, 10344, 17048, 24838, 24870] .e) [32, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e) [32, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n .e [32, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e)) [32, 1605, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6275, 10344, 17048, 24838, 30006] .e) [32, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e) [32, 1605, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n .e [32, 1605, 5424, 6275, 10344, 17048, 24870] .e))) [32, 1605, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n
 (.n
 (.n .e [32, 1605, 5424, 6275, 14571, 17048, 24838] .e) [32, 1605, 5424, 6307, 10344, 17048, 24838] .e) [32, 1605, 6275, 7603, 10344, 17048, 24838]
 (.n .e [32, 1637, 5424, 6275, 10344, 17048, 24838] .e)) [40, 1605, 5424, 6275, 10344, 17048, 22456, 24838]
 (.n
 (.n
 (.n .e [40, 1605, 5424, 6275, 10344, 17048, 24838] .e) [48, 1605, 5424, 6275, 10344, 17048, 24838] .e) [48, 1605, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n .e [64, 64, 1605, 5424, 6275, 10344, 17048, 24838] .e)))) [64, 128, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [64, 256, 1605, 5424, 6275, 10344, 17048, 24838] .e) [64, 512, 1605, 5424, 6275, 10344, 17048, 24838] .e) [64, 1024, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [64, 1605, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [64, 1605, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [64, 1605, 4096, 5424, 6275, 10344, 17048, 24838] .e) [64, 1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [64, 1605, 5424, 5488, 6275, 10344, 17048, 24838]
 (.n .e [64, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e))) [64, 1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [64, 1605, 5424, 6275, 6339, 10344, 17048, 24838] .e) [64, 1605, 5424, 6275, 7603, 10344, 17048, 24838] .e) [64, 1605, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n .e [64, 1605, 5424, 6275, 8192, 10344, 17048, 24838] .e)) [64, 1605, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n
 (.n .e [64, 1605, 5424, 6275, 10344, 11885, 17048, 24838] .e) [64, 1605, 5424, 6275, 10344, 14571, 17048, 24838]
 (.n .e [64, 1605, 5424, 6275, 10344, 15736, 17048, 24838] .e)))))

def T7abaab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [64, 1605, 5424, 6275, 10344, 17048, 17048, 24838] .e) [64, 1605, 5424, 6275, 10344, 17048, 17112, 24838] .e) [64, 1605, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n .e [64, 1605, 5424, 6275, 10344, 17048, 22456, 24838] .e)) [64, 1605, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n .e [64, 1605, 5424, 6275, 10344, 17048, 24838] .e) [64, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [64, 1605, 5424, 6275, 10344, 17048, 24838, 24902]
 (.n .e [64, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e))) [64, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n
 (.n
 (.n .e [64, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e) [64, 1605, 5424, 6275, 10344, 17048, 24838, 27384] .e) [64, 1605, 5424, 6275, 10344, 17048, 24838, 30006]
 (.n .e [64, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e)) [64, 1605, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n
 (.n .e [64, 1605, 5424, 6275, 10344, 17048, 24902] .e) [64, 1605, 5424, 6275, 10344, 17112, 24838]
 (.n .e [64, 1605, 5424, 6339, 10344, 17048, 24838] .e)))) [64, 1605, 5488, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [65, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e) [65, 1605, 5424, 6275, 10344, 17048, 24838] .e) [68, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [68, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e)) [72, 1605, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [72, 1605, 5424, 6275, 10344, 17048, 24838] .e) [96, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e) [96, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [128, 128, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [128, 256, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [128, 512, 1605, 5424, 6275, 10344, 17048, 24838] .e) [128, 1024, 1605, 5424, 6275, 10344, 17048, 24838] .e) [128, 1605, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [128, 1605, 1733, 5424, 6275, 10344, 17048, 24838] .e)) [128, 1605, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [128, 1605, 4096, 5424, 6275, 10344, 17048, 24838] .e) [128, 1605, 5424, 5424, 6275, 10344, 17048, 24838]
 (.n .e [128, 1605, 5424, 5552, 6275, 10344, 17048, 24838] .e)))))

def T7abaa : T := .n T7abaaa [64, 1605, 5424, 6275, 10344, 16384, 17048, 24838] T7abaab

def T7ababa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [128, 1605, 5424, 6275, 6275, 10344, 17048, 24838] .e) [128, 1605, 5424, 6275, 7603, 10344, 17048, 24838] .e) [128, 1605, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n .e [128, 1605, 5424, 6275, 8192, 10344, 17048, 24838] .e)) [128, 1605, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [128, 1605, 5424, 6275, 10344, 10472, 17048, 24838] .e) [128, 1605, 5424, 6275, 10344, 11885, 17048, 24838] .e) [128, 1605, 5424, 6275, 10344, 14571, 17048, 24838]
 (.n .e [128, 1605, 5424, 6275, 10344, 15736, 17048, 24838] .e))) [128, 1605, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 17048, 24838] .e) [128, 1605, 5424, 6275, 10344, 17048, 18141, 24838] .e) [128, 1605, 5424, 6275, 10344, 17048, 22456, 24838]
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 23195, 24838] .e)) [128, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [128, 1605, 5424, 6275, 10344, 17048, 24838, 24966]
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e)))) [128, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n
 (.n
 (.n
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e) [128, 1605, 5424, 6275, 10344, 17048, 24838, 27384] .e) [128, 1605, 5424, 6275, 10344, 17048, 24838, 30006]
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e)) [128, 1605, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n
 (.n
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 24966] .e) [128, 1605, 5424, 6275, 10472, 17048, 24838] .e) [128, 1605, 5552, 6275, 10344, 17048, 24838]
 (.n .e [128, 1733, 5424, 6275, 10344, 17048, 24838] .e))) [129, 1605, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n
 (.n
 (.n
 (.n .e [129, 1605, 5424, 6275, 10344, 17048, 24838] .e) [130, 1605, 5424, 6275, 10344, 17048, 24838] .e) [130, 1605, 5424, 6275, 10344, 17048, 24838, 25502]
 (.n .e [136, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e)) [136, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [144, 1605, 5424, 6275, 7603, 10344, 17048, 24838] .e) [144, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [256, 256, 1605, 5424, 6275, 10344, 17048, 24838] .e)))))

def T7ababb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [256, 1024, 1605, 5424, 6275, 10344, 17048, 24838] .e) [256, 1605, 1605, 5424, 6275, 10344, 17048, 24838] .e) [256, 1605, 1861, 5424, 6275, 10344, 17048, 24838]
 (.n .e [256, 1605, 2048, 5424, 6275, 10344, 17048, 24838] .e)) [256, 1605, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [256, 1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [256, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e) [256, 1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n .e [256, 1605, 5424, 6275, 6531, 10344, 17048, 24838] .e))) [256, 1605, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [256, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e) [256, 1605, 5424, 6275, 8192, 10344, 17048, 24838] .e) [256, 1605, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n .e [256, 1605, 5424, 6275, 10344, 10600, 17048, 24838] .e)) [256, 1605, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n
 (.n .e [256, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e) [256, 1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n .e [256, 1605, 5424, 6275, 10344, 16384, 17048, 24838] .e)))) [256, 1605, 5424, 6275, 10344, 17048, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [256, 1605, 5424, 6275, 10344, 17048, 17304, 24838] .e) [256, 1605, 5424, 6275, 10344, 17048, 18141, 24838] .e) [256, 1605, 5424, 6275, 10344, 17048, 22456, 24838]
 (.n .e [256, 1605, 5424, 6275, 10344, 17048, 23195, 24838] .e)) [256, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [256, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [256, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e) [256, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n .e [256, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e))) [256, 1605, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n
 (.n .e [256, 1605, 5424, 6275, 10344, 17048, 24838, 30006] .e) [256, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e) [256, 1605, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n .e [256, 1605, 5424, 6275, 10344, 17304, 24838] .e)) [256, 1605, 5424, 6275, 10600, 17048, 24838]
 (.n
 (.n .e [256, 1605, 5424, 6531, 10344, 17048, 24838] .e) [256, 1861, 5424, 6275, 10344, 17048, 24838]
 (.n .e [258, 1605, 5424, 6275, 7603, 10344, 17048, 24838] .e)))))

def T7abab : T := .n T7ababa [256, 512, 1605, 5424, 6275, 10344, 17048, 24838] T7ababb

def T7aba : T := .n T7abaa [128, 1605, 5424, 6005, 6275, 10344, 17048, 24838] T7abab

def T7abbaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [260, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e) [260, 1605, 5424, 6275, 10344, 17048, 24838] .e) [272, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [272, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e)) [288, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [288, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e) [512, 512, 1605, 5424, 6275, 10344, 17048, 24838] .e) [512, 1024, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [512, 1605, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [512, 1605, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [512, 1605, 4096, 5424, 6275, 10344, 17048, 24838] .e) [512, 1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [512, 1605, 5424, 5936, 6275, 10344, 17048, 24838]
 (.n .e [512, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e)) [512, 1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [512, 1605, 5424, 6275, 6787, 10344, 17048, 24838] .e) [512, 1605, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n .e [512, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e)))) [512, 1605, 5424, 6275, 8192, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 10344, 17048, 24838] .e) [512, 1605, 5424, 6275, 10344, 10856, 17048, 24838] .e) [512, 1605, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n .e [512, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e)) [512, 1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 16384, 17048, 24838] .e) [512, 1605, 5424, 6275, 10344, 17048, 17048, 24838] .e) [512, 1605, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n .e [512, 1605, 5424, 6275, 10344, 17048, 22456, 24838] .e))) [512, 1605, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 17048, 24838] .e) [512, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [512, 1605, 5424, 6275, 10344, 17048, 24838, 25350]
 (.n .e [512, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e)) [512, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e) [512, 1605, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n .e [512, 1605, 5424, 6275, 10344, 17048, 24838, 30006] .e)))))

def T7abbab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 17048, 24838, 32767] .e) [513, 1605, 5424, 6275, 10344, 17048, 23195, 24838] .e) [513, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [516, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [516, 1605, 5424, 6275, 10344, 17048, 24838, 25502]
 (.n
 (.n
 (.n .e [520, 1605, 5424, 6275, 10344, 11885, 17048, 24838] .e) [520, 1605, 5424, 6275, 10344, 17048, 24838] .e) [528, 1605, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n .e [528, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [576, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [576, 1605, 5424, 6275, 10344, 17048, 24838, 27384] .e) [640, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e) [640, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1024, 1024, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [1024, 1605, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1024, 1605, 2048, 5424, 6275, 10344, 17048, 24838] .e) [1024, 1605, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1024, 1605, 5424, 5424, 6275, 10344, 17048, 24838] .e)))) [1024, 1605, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1024, 1605, 5424, 6275, 6275, 10344, 17048, 24838] .e) [1024, 1605, 5424, 6275, 7299, 10344, 17048, 24838] .e) [1024, 1605, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n .e [1024, 1605, 5424, 6275, 7879, 10344, 17048, 24838] .e)) [1024, 1605, 5424, 6275, 8192, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10344, 10344, 17048, 24838] .e) [1024, 1605, 5424, 6275, 10344, 11368, 17048, 24838] .e) [1024, 1605, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n .e [1024, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e))) [1024, 1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10344, 16384, 17048, 24838] .e) [1024, 1605, 5424, 6275, 10344, 17048, 17048, 24838] .e) [1024, 1605, 5424, 6275, 10344, 17048, 18072, 24838]
 (.n .e [1024, 1605, 5424, 6275, 10344, 17048, 18141, 24838] .e)) [1024, 1605, 5424, 6275, 10344, 17048, 22456, 24838]
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10344, 17048, 23195, 24838] .e) [1024, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1024, 1605, 5424, 6275, 10344, 17048, 24838, 24838] .e)))))

def T7abba : T := .n T7abbaa [512, 1605, 5424, 6275, 10344, 17048, 24838, 31111] T7abbab

def T7abbba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10344, 17048, 24838, 25862] .e) [1024, 1605, 5424, 6275, 10344, 17048, 24838, 26439] .e) [1024, 1605, 5424, 6275, 10344, 17048, 24838, 26990]
 (.n .e [1024, 1605, 5424, 6275, 10344, 17048, 24838, 27384] .e)) [1024, 1605, 5424, 6275, 10344, 17048, 24838, 30006]
 (.n
 (.n
 (.n .e [1024, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e) [1024, 1605, 5424, 6275, 10344, 17048, 24838, 32767] .e) [1025, 1605, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n .e [1025, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [1028, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1028, 1605, 5424, 6275, 10344, 17048, 24838, 30006] .e) [1040, 1605, 5424, 6275, 10344, 17048, 18141, 24838] .e) [1040, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1056, 1605, 5424, 6275, 10344, 11885, 17048, 24838] .e)) [1056, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1088, 1605, 5424, 6275, 10344, 15736, 17048, 24838] .e) [1088, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1280, 1605, 5424, 6275, 10344, 17048, 24838] .e)))) [1280, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1536, 1605, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1536, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1605, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 1605, 2048, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 1605, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1605, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1605, 1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n .e [1605, 1605, 5424, 6275, 7603, 10344, 17048, 24838] .e))) [1605, 1605, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 1605, 5424, 6275, 8192, 10344, 17048, 24838] .e) [1605, 1605, 5424, 6275, 10344, 10344, 17048, 24838] .e) [1605, 1605, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n .e [1605, 1605, 5424, 6275, 10344, 14571, 17048, 24838] .e)) [1605, 1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n .e [1605, 1605, 5424, 6275, 10344, 16384, 17048, 24838] .e) [1605, 1605, 5424, 6275, 10344, 17048, 17048, 24838]
 (.n .e [1605, 1605, 5424, 6275, 10344, 17048, 18141, 24838] .e)))))

def T7abbbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 1605, 5424, 6275, 10344, 17048, 23195, 24838] .e) [1605, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1605, 5424, 6275, 10344, 17048, 24838, 24838]
 (.n .e [1605, 1605, 5424, 6275, 10344, 17048, 24838, 25502] .e)) [1605, 1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n
 (.n .e [1605, 1605, 5424, 6275, 10344, 17048, 24838, 26990] .e) [1605, 1605, 5424, 6275, 10344, 17048, 24838, 27384] .e) [1605, 1605, 5424, 6275, 10344, 17048, 24838, 30006]
 (.n .e [1605, 1605, 5424, 6275, 10344, 17048, 24838, 31111] .e))) [1605, 1605, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n
 (.n
 (.n
 (.n .e [1605, 1607, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1613, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1621, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 1637, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 1733, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 1861, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2048, 2048, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 2048, 3653, 5424, 6275, 10344, 17048, 24838] .e)))) [1605, 2048, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 2048, 5424, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2048, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1605, 2048, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n .e [1605, 2048, 5424, 6275, 7472, 10344, 17048, 24838] .e)) [1605, 2048, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 2048, 5424, 6275, 7879, 10344, 17048, 24838] .e) [1605, 2048, 5424, 6275, 8192, 10344, 17048, 24838] .e) [1605, 2048, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n .e [1605, 2048, 5424, 6275, 10344, 11885, 17048, 24838] .e))) [1605, 2048, 5424, 6275, 10344, 14571, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10344, 15736, 17048, 24838] .e) [1605, 2048, 5424, 6275, 10344, 16384, 17048, 24838] .e) [1605, 2048, 5424, 6275, 10344, 17048, 17048, 24838]
 (.n .e [1605, 2048, 5424, 6275, 10344, 17048, 18141, 24838] .e)) [1605, 2048, 5424, 6275, 10344, 17048, 19096, 24838]
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1605, 2048, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n .e [1605, 2048, 5424, 6275, 10344, 17048, 24838] .e)))))

def T7abbb : T := .n T7abbba [1605, 1605, 5424, 6275, 10344, 17048, 22456, 24838] T7abbbb

def T7abb : T := .n T7abba [1024, 1605, 5424, 6275, 10344, 17048, 24838, 25502] T7abbb

def T7ab : T := .n T7aba [258, 1605, 5424, 6275, 10344, 17048, 24838] T7abb

def T7a : T := .n T7aa [32, 1605, 5424, 6275, 10344, 17048, 24838, 24838] T7ab

def T7baaaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10344, 17048, 24838, 25502] .e) [1605, 2048, 5424, 6275, 10344, 17048, 24838, 26439] .e) [1605, 2048, 5424, 6275, 10344, 17048, 24838, 26886]
 (.n .e [1605, 2048, 5424, 6275, 10344, 17048, 24838, 26990] .e)) [1605, 2048, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n .e [1605, 2048, 5424, 6275, 10344, 17048, 24838, 30006] .e) [1605, 2048, 5424, 6275, 10344, 17048, 24838, 31111] .e) [1605, 2048, 5424, 6275, 10344, 17048, 24838, 32767]
 (.n .e [1605, 2049, 5424, 6275, 10344, 11885, 17048, 24838] .e))) [1605, 2049, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 2050, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2050, 5424, 6275, 10344, 17048, 24838, 26990] .e) [1605, 2056, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n .e [1605, 2056, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 2080, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 2080, 5424, 6275, 10344, 17048, 24838] .e) [1605, 2112, 5424, 6275, 7879, 10344, 17048, 24838] .e) [1605, 2112, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 2176, 5424, 6275, 10344, 17048, 24838] .e)))) [1605, 2176, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 3653, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4096, 4096, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4096, 5424, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 4096, 5424, 5701, 6275, 10344, 17048, 24838] .e)) [1605, 4096, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 4096, 5424, 6275, 6275, 10344, 17048, 24838] .e) [1605, 4096, 5424, 6275, 7603, 10344, 17048, 24838] .e) [1605, 4096, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n .e [1605, 4096, 5424, 6275, 8192, 10344, 17048, 24838] .e))) [1605, 4096, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10344, 11885, 17048, 24838] .e) [1605, 4096, 5424, 6275, 10344, 14440, 17048, 24838] .e) [1605, 4096, 5424, 6275, 10344, 14571, 17048, 24838]
 (.n .e [1605, 4096, 5424, 6275, 10344, 15736, 17048, 24838] .e)) [1605, 4096, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10344, 17048, 17048, 24838] .e) [1605, 4096, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n .e [1605, 4096, 5424, 6275, 10344, 17048, 21144, 24838] .e)))))

def T7baaab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10344, 17048, 23195, 24838] .e) [1605, 4096, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4096, 5424, 6275, 10344, 17048, 24838, 24838]
 (.n .e [1605, 4096, 5424, 6275, 10344, 17048, 24838, 25502] .e)) [1605, 4096, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10344, 17048, 24838, 26990] .e) [1605, 4096, 5424, 6275, 10344, 17048, 24838, 27384] .e) [1605, 4096, 5424, 6275, 10344, 17048, 24838, 28934]
 (.n .e [1605, 4096, 5424, 6275, 10344, 17048, 24838, 30006] .e))) [1605, 4096, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n
 (.n .e [1605, 4096, 5424, 6275, 10344, 17048, 24838, 32767] .e) [1605, 4097, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1605, 4097, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 4098, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 4098, 5424, 6275, 10344, 17048, 24838, 30006]
 (.n
 (.n .e [1605, 4112, 5424, 6275, 10344, 17048, 23195, 24838] .e) [1605, 4112, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 4128, 5424, 6275, 10344, 14571, 17048, 24838] .e)))) [1605, 4128, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 4224, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1605, 4224, 5424, 6275, 10344, 17048, 24838] .e) [1605, 4352, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 4352, 5424, 6275, 10344, 17048, 24838, 31111] .e)) [1605, 5120, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5120, 5424, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5424, 5424, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5424, 6005, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5424, 5424, 6275, 6275, 10344, 17048, 24838] .e))) [1605, 5424, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 5424, 6275, 7879, 10344, 17048, 24838] .e) [1605, 5424, 5424, 6275, 8192, 10344, 17048, 24838] .e) [1605, 5424, 5424, 6275, 10344, 10344, 17048, 24838]
 (.n .e [1605, 5424, 5424, 6275, 10344, 11885, 17048, 24838] .e)) [1605, 5424, 5424, 6275, 10344, 14571, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 15736, 17048, 24838] .e) [1605, 5424, 5424, 6275, 10344, 16384, 17048, 24838]
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 17048, 24838] .e)))))

def T7baaa : T := .n T7baaaa [1605, 4096, 5424, 6275, 10344, 17048, 22456, 24838] T7baaab

def T7baaba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1605, 5424, 5424, 6275, 10344, 17048, 23195, 24838] .e) [1605, 5424, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 24838, 24838] .e)) [1605, 5424, 5424, 6275, 10344, 17048, 24838, 25502]
 (.n
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 24838, 26439] .e) [1605, 5424, 5424, 6275, 10344, 17048, 24838, 26990] .e) [1605, 5424, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 24838, 30006] .e))) [1605, 5424, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 24838, 32767] .e) [1605, 5424, 5425, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5426, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5424, 5428, 6275, 10344, 17048, 24838] .e)) [1605, 5424, 5432, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 5488, 6275, 10344, 17048, 24838] .e) [1605, 5424, 5552, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5424, 5701, 6275, 10344, 17048, 24838] .e)))) [1605, 5424, 5936, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6005, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6005, 6275, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6005, 6275, 7603, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6005, 6275, 7879, 10344, 17048, 24838] .e)) [1605, 5424, 6005, 6275, 8183, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6275, 8192, 10344, 17048, 24838] .e) [1605, 5424, 6005, 6275, 10344, 10344, 17048, 24838] .e) [1605, 5424, 6005, 6275, 10344, 11885, 17048, 24838]
 (.n .e [1605, 5424, 6005, 6275, 10344, 14571, 17048, 24838] .e))) [1605, 5424, 6005, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 16253, 17048, 24838] .e) [1605, 5424, 6005, 6275, 10344, 16384, 17048, 24838] .e) [1605, 5424, 6005, 6275, 10344, 17048, 17048, 24838]
 (.n .e [1605, 5424, 6005, 6275, 10344, 17048, 18141, 24838] .e)) [1605, 5424, 6005, 6275, 10344, 17048, 22456, 24838]
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 17048, 22525, 24838] .e) [1605, 5424, 6005, 6275, 10344, 17048, 23195, 24838]
 (.n .e [1605, 5424, 6005, 6275, 10344, 17048, 24838] .e)))))

def T7baabb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6005, 6275, 10344, 17048, 24838, 26439] .e) [1605, 5424, 6005, 6275, 10344, 17048, 24838, 26990]
 (.n .e [1605, 5424, 6005, 6275, 10344, 17048, 24838, 27384] .e)) [1605, 5424, 6005, 6275, 10344, 17048, 24838, 30006]
 (.n
 (.n
 (.n .e [1605, 5424, 6005, 6275, 10344, 17048, 24838, 30583] .e) [1605, 5424, 6005, 6275, 10344, 17048, 24838, 31111] .e) [1605, 5424, 6005, 6275, 10344, 17048, 24838, 32767]
 (.n .e [1605, 5424, 6144, 6275, 10344, 15736, 17048, 24838] .e))) [1605, 5424, 6144, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6275, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6275, 7603, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6275, 7879, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 6275, 8192, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 6275, 10344, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10344, 11885, 17048, 24838] .e) [1605, 5424, 6275, 6275, 10344, 14571, 17048, 24838]
 (.n .e [1605, 5424, 6275, 6275, 10344, 15736, 17048, 24838] .e)))) [1605, 5424, 6275, 6275, 10344, 16384, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10344, 17048, 17048, 24838] .e) [1605, 5424, 6275, 6275, 10344, 17048, 18141, 24838] .e) [1605, 5424, 6275, 6275, 10344, 17048, 22456, 24838]
 (.n .e [1605, 5424, 6275, 6275, 10344, 17048, 23195, 24838] .e)) [1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10344, 17048, 24838, 24838] .e) [1605, 5424, 6275, 6275, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6275, 6275, 10344, 17048, 24838, 26439]
 (.n .e [1605, 5424, 6275, 6275, 10344, 17048, 24838, 26990] .e))) [1605, 5424, 6275, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6275, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6275, 6275, 10344, 17048, 24838, 31111] .e) [1605, 5424, 6275, 6275, 10344, 17048, 24838, 32767]
 (.n .e [1605, 5424, 6275, 6279, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 6283, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 6291, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6307, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 6339, 10344, 17048, 24838] .e)))))

def T7baab : T := .n T7baaba [1605, 5424, 6005, 6275, 10344, 17048, 24838, 24838] T7baabb

def T7baa : T := .n T7baaa [1605, 5424, 5424, 6275, 10344, 17048, 18141, 24838] T7baab

def T7babaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 6787, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7299, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7472, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 7603, 7603, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 7603, 7879, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7603, 8183, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7603, 8192, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7603, 10344, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 7603, 10344, 11885, 17048, 24838] .e))) [1605, 5424, 6275, 7603, 10344, 14571, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10344, 15736, 17048, 24838] .e) [1605, 5424, 6275, 7603, 10344, 15867, 17048, 24838] .e) [1605, 5424, 6275, 7603, 10344, 16384, 17048, 24838]
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 17048, 24838] .e)) [1605, 5424, 6275, 7603, 10344, 17048, 18141, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 22456, 24838] .e) [1605, 5424, 6275, 7603, 10344, 17048, 23195, 24838]
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 24507, 24838] .e)))) [1605, 5424, 6275, 7603, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 24838, 24838] .e) [1605, 5424, 6275, 7603, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6275, 7603, 10344, 17048, 24838, 26439]
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 24838, 26990] .e)) [1605, 5424, 6275, 7603, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6275, 7603, 10344, 17048, 24838, 31111] .e) [1605, 5424, 6275, 7603, 10344, 17048, 24838, 32183]
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 24838, 32767] .e))) [1605, 5424, 6275, 7879, 7879, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7879, 8183, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7879, 8192, 10344, 17048, 24838] .e) [1605, 5424, 6275, 7879, 10344, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 7879, 10344, 11885, 17048, 24838] .e)) [1605, 5424, 6275, 7879, 10344, 14571, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10344, 15736, 17048, 24838] .e) [1605, 5424, 6275, 7879, 10344, 16111, 17048, 24838]
 (.n .e [1605, 5424, 6275, 7879, 10344, 16384, 17048, 24838] .e)))))

def T7babab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10344, 17048, 18141, 24838] .e) [1605, 5424, 6275, 7879, 10344, 17048, 22456, 24838] .e) [1605, 5424, 6275, 7879, 10344, 17048, 23195, 24838]
 (.n .e [1605, 5424, 6275, 7879, 10344, 17048, 24287, 24838] .e)) [1605, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10344, 17048, 24838, 24838] .e) [1605, 5424, 6275, 7879, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6275, 7879, 10344, 17048, 24838, 26439]
 (.n .e [1605, 5424, 6275, 7879, 10344, 17048, 24838, 26990] .e))) [1605, 5424, 6275, 7879, 10344, 17048, 24838, 27384]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 7879, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6275, 7879, 10344, 17048, 24838, 31111] .e) [1605, 5424, 6275, 7879, 10344, 17048, 24838, 32711]
 (.n .e [1605, 5424, 6275, 7879, 10344, 17048, 24838, 32767] .e)) [1605, 5424, 6275, 8183, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 8192, 8192, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8192, 9797, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 8192, 10344, 10344, 17048, 24838] .e)))) [1605, 5424, 6275, 8192, 10344, 11885, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10344, 13616, 17048, 24838] .e) [1605, 5424, 6275, 8192, 10344, 14467, 17048, 24838] .e) [1605, 5424, 6275, 8192, 10344, 14571, 17048, 24838]
 (.n .e [1605, 5424, 6275, 8192, 10344, 15736, 17048, 24838] .e)) [1605, 5424, 6275, 8192, 10344, 16384, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10344, 17048, 17048, 24838] .e) [1605, 5424, 6275, 8192, 10344, 17048, 18141, 24838] .e) [1605, 5424, 6275, 8192, 10344, 17048, 22456, 24838]
 (.n .e [1605, 5424, 6275, 8192, 10344, 17048, 23195, 24838] .e))) [1605, 5424, 6275, 8192, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10344, 17048, 24838, 24838] .e) [1605, 5424, 6275, 8192, 10344, 17048, 24838, 25240] .e) [1605, 5424, 6275, 8192, 10344, 17048, 24838, 25502]
 (.n .e [1605, 5424, 6275, 8192, 10344, 17048, 24838, 26439] .e)) [1605, 5424, 6275, 8192, 10344, 17048, 24838, 26990]
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10344, 17048, 24838, 27384] .e) [1605, 5424, 6275, 8192, 10344, 17048, 24838, 30006]
 (.n .e [1605, 5424, 6275, 8192, 10344, 17048, 24838, 31111] .e)))))

def T7baba : T := .n T7babaa [1605, 5424, 6275, 7879, 10344, 17048, 17048, 24838] T7babab

def T7babba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8194, 10344, 14571, 17048, 24838] .e) [1605, 5424, 6275, 8194, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8196, 10344, 11885, 17048, 24838]
 (.n .e [1605, 5424, 6275, 8196, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 8200, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8200, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6275, 8224, 10344, 17048, 24838] .e) [1605, 5424, 6275, 8224, 10344, 17048, 24838, 30006]
 (.n .e [1605, 5424, 6275, 8256, 10344, 17048, 24838] .e))) [1605, 5424, 6275, 8256, 10344, 17048, 24838, 26439]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8448, 10344, 15736, 17048, 24838] .e) [1605, 5424, 6275, 8448, 10344, 17048, 24838] .e) [1605, 5424, 6275, 9797, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10240, 10344, 17048, 24838] .e)) [1605, 5424, 6275, 10240, 10344, 17048, 24838, 31111]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10344, 10344, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10344, 11885, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 10344, 14571, 17048, 24838] .e)))) [1605, 5424, 6275, 10344, 10344, 15736, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10344, 16384, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10344, 17048, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10344, 17048, 18141, 24838]
 (.n .e [1605, 5424, 6275, 10344, 10344, 17048, 22456, 24838] .e)) [1605, 5424, 6275, 10344, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10344, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10344, 17048, 24838, 24838] .e) [1605, 5424, 6275, 10344, 10344, 17048, 24838, 25502]
 (.n .e [1605, 5424, 6275, 10344, 10344, 17048, 24838, 26439] .e))) [1605, 5424, 6275, 10344, 10344, 17048, 24838, 26990]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10344, 17048, 24838, 27384] .e) [1605, 5424, 6275, 10344, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6275, 10344, 10344, 17048, 24838, 31111]
 (.n .e [1605, 5424, 6275, 10344, 10344, 17048, 24838, 32767] .e)) [1605, 5424, 6275, 10344, 10345, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10346, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10348, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 10360, 17048, 24838] .e)))))

def T7babbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 10600, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10856, 17048, 24838] .e) [1605, 5424, 6275, 10344, 11368, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 11885, 11885, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 11885, 14571, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11885, 15736, 17048, 24838] .e) [1605, 5424, 6275, 10344, 11885, 16111, 17048, 24838] .e) [1605, 5424, 6275, 10344, 11885, 16253, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 11885, 16384, 17048, 24838] .e))) [1605, 5424, 6275, 10344, 11885, 17048, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11885, 17048, 18141, 24838] .e) [1605, 5424, 6275, 10344, 11885, 17048, 22456, 24838] .e) [1605, 5424, 6275, 10344, 11885, 17048, 23195, 24838]
 (.n .e [1605, 5424, 6275, 10344, 11885, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 11885, 17048, 24838, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11885, 17048, 24838, 25502] .e) [1605, 5424, 6275, 10344, 11885, 17048, 24838, 26439]
 (.n .e [1605, 5424, 6275, 10344, 11885, 17048, 24838, 26990] .e)))) [1605, 5424, 6275, 10344, 11885, 17048, 24838, 27384]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 11885, 17048, 24838, 28413] .e) [1605, 5424, 6275, 10344, 11885, 17048, 24838, 28527] .e) [1605, 5424, 6275, 10344, 11885, 17048, 24838, 30006]
 (.n .e [1605, 5424, 6275, 10344, 11885, 17048, 24838, 31111] .e)) [1605, 5424, 6275, 10344, 11885, 17048, 24838, 32767]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 13616, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14440, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14467, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 14571, 14571, 17048, 24838] .e))) [1605, 5424, 6275, 10344, 14571, 15736, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14571, 15867, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14571, 16111, 17048, 24838] .e) [1605, 5424, 6275, 10344, 14571, 16384, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 14571, 17048, 18141, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 22456, 24838] .e) [1605, 5424, 6275, 10344, 14571, 17048, 23195, 24838]
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 24838] .e)))))

def T7babb : T := .n T7babba [1605, 5424, 6275, 10344, 10472, 17048, 24838] T7babbb

def T7bab : T := .n T7baba [1605, 5424, 6275, 8192, 10344, 17048, 24838, 32767] T7babb

def T7ba : T := .n T7baa [1605, 5424, 6275, 6531, 10344, 17048, 24838] T7bab

def T7bbaaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 24838, 25502] .e) [1605, 5424, 6275, 10344, 14571, 17048, 24838, 26439] .e) [1605, 5424, 6275, 10344, 14571, 17048, 24838, 26990]
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 24838, 27384] .e)) [1605, 5424, 6275, 10344, 14571, 17048, 24838, 30006]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 24838, 31111] .e) [1605, 5424, 6275, 10344, 14571, 17048, 24838, 31215] .e) [1605, 5424, 6275, 10344, 14571, 17048, 24838, 31483]
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 24838, 32767] .e))) [1605, 5424, 6275, 10344, 15736, 15736, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15736, 15867, 17048, 24838] .e) [1605, 5424, 6275, 10344, 15736, 16253, 17048, 24838] .e) [1605, 5424, 6275, 10344, 15736, 16384, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 15736, 17048, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 15736, 17048, 18141, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15736, 17048, 22456, 24838] .e) [1605, 5424, 6275, 10344, 15736, 17048, 23195, 24838] .e) [1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 15736, 17048, 24838, 24838] .e)))) [1605, 5424, 6275, 10344, 15736, 17048, 24838, 25502]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15736, 17048, 24838, 26439] .e) [1605, 5424, 6275, 10344, 15736, 17048, 24838, 26990] .e) [1605, 5424, 6275, 10344, 15736, 17048, 24838, 27384]
 (.n .e [1605, 5424, 6275, 10344, 15736, 17048, 24838, 30006] .e)) [1605, 5424, 6275, 10344, 15736, 17048, 24838, 31111]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 15736, 17048, 24838, 32126] .e) [1605, 5424, 6275, 10344, 15736, 17048, 24838, 32760] .e) [1605, 5424, 6275, 10344, 15736, 17048, 24838, 32767]
 (.n .e [1605, 5424, 6275, 10344, 15867, 17048, 24838] .e))) [1605, 5424, 6275, 10344, 16111, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16253, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16384, 16384, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16384, 17048, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 17989, 24838] .e)) [1605, 5424, 6275, 10344, 16384, 17048, 18141, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 21808, 24838] .e) [1605, 5424, 6275, 10344, 16384, 17048, 22456, 24838]
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 22659, 24838] .e)))))

def T7bbaab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16384, 17048, 24838, 24838] .e) [1605, 5424, 6275, 10344, 16384, 17048, 24838, 25502]
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 24838, 26439] .e)) [1605, 5424, 6275, 10344, 16384, 17048, 24838, 26728]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 24838, 26990] .e) [1605, 5424, 6275, 10344, 16384, 17048, 24838, 27384] .e) [1605, 5424, 6275, 10344, 16384, 17048, 24838, 30006]
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 24838, 31111] .e))) [1605, 5424, 6275, 10344, 16384, 17048, 24838, 32767]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16386, 17048, 23195, 24838] .e) [1605, 5424, 6275, 10344, 16386, 17048, 24838] .e) [1605, 5424, 6275, 10344, 16388, 17048, 18141, 24838]
 (.n .e [1605, 5424, 6275, 10344, 16388, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 16392, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16392, 17048, 24838, 26990] .e) [1605, 5424, 6275, 10344, 16400, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 16400, 17048, 24838, 30006] .e)))) [1605, 5424, 6275, 10344, 16512, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16512, 17048, 24838, 31111] .e) [1605, 5424, 6275, 10344, 16640, 17048, 22456, 24838] .e) [1605, 5424, 6275, 10344, 16640, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 16896, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 16896, 17048, 24838, 26439]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17048, 17048, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17048, 18141, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17048, 22456, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 17048, 23195, 24838] .e))) [1605, 5424, 6275, 10344, 17048, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17048, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17048, 24838, 25502] .e) [1605, 5424, 6275, 10344, 17048, 17048, 24838, 26439]
 (.n .e [1605, 5424, 6275, 10344, 17048, 17048, 24838, 26990] .e)) [1605, 5424, 6275, 10344, 17048, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17048, 24838, 30006] .e) [1605, 5424, 6275, 10344, 17048, 17048, 24838, 31111]
 (.n .e [1605, 5424, 6275, 10344, 17048, 17048, 24838, 32767] .e)))))

def T7bbaa : T := .n T7bbaaa [1605, 5424, 6275, 10344, 16384, 17048, 23195, 24838] T7bbaab

def T7bbaba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17050, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17052, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17080, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 17112, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 17304, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 17989, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18072, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18141, 18141, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 22456, 24838] .e))) [1605, 5424, 6275, 10344, 17048, 18141, 22525, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 23195, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24287, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 24838, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 18141, 24838, 25502]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 24838, 26439] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24838, 26591]
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 24838, 26990] .e)))) [1605, 5424, 6275, 10344, 17048, 18141, 24838, 27384]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 24838, 28413] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24838, 30006] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24838, 31111]
 (.n .e [1605, 5424, 6275, 10344, 17048, 18141, 24838, 32767] .e)) [1605, 5424, 6275, 10344, 17048, 19096, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 21144, 24838] .e) [1605, 5424, 6275, 10344, 17048, 21808, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22456, 22456, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 22525, 24838] .e))) [1605, 5424, 6275, 10344, 17048, 22456, 23195, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24507, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22456, 24838] .e) [1605, 5424, 6275, 10344, 17048, 22456, 24838, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24838, 25502] .e)) [1605, 5424, 6275, 10344, 17048, 22456, 24838, 26439]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24838, 26990] .e) [1605, 5424, 6275, 10344, 17048, 22456, 24838, 27384]
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24838, 30006] .e)))))

def T7bbabb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24838, 31111] .e) [1605, 5424, 6275, 10344, 17048, 22456, 24838, 32760] .e) [1605, 5424, 6275, 10344, 17048, 22456, 24838, 32767]
 (.n .e [1605, 5424, 6275, 10344, 17048, 22525, 24838] .e)) [1605, 5424, 6275, 10344, 17048, 22659, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 23195, 23195, 24838] .e) [1605, 5424, 6275, 10344, 17048, 23195, 24287, 24838] .e) [1605, 5424, 6275, 10344, 17048, 23195, 24507, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 23195, 24838] .e))) [1605, 5424, 6275, 10344, 17048, 23195, 24838, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 23195, 24838, 25502] .e) [1605, 5424, 6275, 10344, 17048, 23195, 24838, 26439] .e) [1605, 5424, 6275, 10344, 17048, 23195, 24838, 26990]
 (.n .e [1605, 5424, 6275, 10344, 17048, 23195, 24838, 27384] .e)) [1605, 5424, 6275, 10344, 17048, 23195, 24838, 30006]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 23195, 24838, 31111] .e) [1605, 5424, 6275, 10344, 17048, 23195, 24838, 31483]
 (.n .e [1605, 5424, 6275, 10344, 17048, 23195, 24838, 31647] .e)))) [1605, 5424, 6275, 10344, 17048, 23195, 24838, 32767]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24287, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24507, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24576, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24576, 24838, 27384] .e)) [1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24838, 25502]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24838, 26439] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 24838, 26990]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24838, 27384] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24838, 30006] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24838, 31111]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24838, 32767] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 24839]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24846] .e) [1605, 5424, 6275, 10344, 17048, 24838, 24854]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24870] .e)))))

def T7bbab : T := .n T7bbaba [1605, 5424, 6275, 10344, 17048, 22456, 24838, 30654] T7bbabb

def T7bba : T := .n T7bbaa [1605, 5424, 6275, 10344, 17048, 17049, 24838] T7bbab

def T7bbbaa : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24966] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25240] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25350]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25502] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 25502, 25502]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25502, 26439] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25502, 26591] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25502, 26990]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25502, 27384] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 25502, 27646]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25502, 30006] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25502, 30654] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25502, 31111]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25502, 31647] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 25502, 32767]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 25862] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26439, 26439] .e)))) [1605, 5424, 6275, 10344, 17048, 24838, 26439, 26591]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26439, 26990] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26439, 27384] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26439, 28527]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26439, 30006] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 26439, 30583]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26439, 31111] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26439, 32711] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26439, 32767]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26591] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 26728]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26886] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26990] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26990, 26990]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26990, 27384] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 26990, 27646]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26990, 28527] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26990, 30006]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26990, 31111] .e)))))

def T7bbbab : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26990, 32126] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26990, 32767] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 27384, 27384] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 27384, 27646]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 27384, 28413] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27384, 30006] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27384, 31111]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 27384, 31483] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 27384, 32760]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 27384, 32767] .e) [1605, 5424, 6275, 10344, 17048, 24838, 27646] .e) [1605, 5424, 6275, 10344, 17048, 24838, 28413]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 28527] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 28934]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30006, 30006]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30006, 30583] .e)))) [1605, 5424, 6275, 10344, 17048, 24838, 30006, 30654]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30006, 31111] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30006, 32126] .e) [1605, 5424, 6275, 10344, 17048, 24838, 30006, 32183]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30006, 32767] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 30583]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30654] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31111] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31111, 31111]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 31111, 31215] .e))) [1605, 5424, 6275, 10344, 17048, 24838, 31111, 31647]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 31111, 32183] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31111, 32711] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31111, 32767]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 31215] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 31483]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 31647] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32126]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 32183] .e)))))

def T7bbba : T := .n T7bbbaa [1605, 5424, 6275, 10344, 17048, 24838, 26990, 31215] T7bbbab

def T7bbbba : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 32760] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32767] .e) [1605, 5424, 6275, 10344, 17048, 24838, 32767, 32767]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24839] .e)) [1605, 5424, 6275, 10344, 17048, 24846]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24854] .e) [1605, 5424, 6275, 10344, 17048, 24870] .e) [1605, 5424, 6275, 10344, 17048, 24902]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24966] .e))) [1605, 5424, 6275, 10344, 17048, 25502, 26990]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 25502, 30006] .e) [1605, 5424, 6275, 10344, 17048, 25502, 31111] .e) [1605, 5424, 6275, 10344, 17048, 26439, 26990]
 (.n .e [1605, 5424, 6275, 10344, 17048, 26439, 31111] .e)) [1605, 5424, 6275, 10344, 17048, 26990, 30006]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17049, 24838] .e) [1605, 5424, 6275, 10344, 17050, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17052, 24838] .e)))) [1605, 5424, 6275, 10344, 17080, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17112, 24838] .e) [1605, 5424, 6275, 10344, 17304, 24838] .e) [1605, 5424, 6275, 10344, 18141, 23195, 24838]
 (.n .e [1605, 5424, 6275, 10344, 18141, 24838, 25502] .e)) [1605, 5424, 6275, 10344, 18141, 24838, 27384]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 22456, 24838, 25502] .e) [1605, 5424, 6275, 10344, 22456, 24838, 27384] .e) [1605, 5424, 6275, 10344, 23195, 24838, 25502]
 (.n .e [1605, 5424, 6275, 10345, 17048, 24838] .e))) [1605, 5424, 6275, 10346, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10348, 17048, 24838] .e) [1605, 5424, 6275, 10360, 17048, 24838] .e) [1605, 5424, 6275, 10472, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10600, 17048, 24838] .e)) [1605, 5424, 6275, 11885, 14571, 17048, 24838]
 (.n
 (.n .e [1605, 5424, 6275, 11885, 17048, 24838, 26990] .e) [1605, 5424, 6275, 14571, 17048, 24838, 26990]
 (.n .e [1605, 5424, 6275, 14571, 17048, 24838, 27384] .e)))))

def T7bbbbb : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 15736, 17048, 24838, 27384] .e) [1605, 5424, 6279, 10344, 17048, 24838] .e) [1605, 5424, 6283, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6291, 10344, 17048, 24838] .e)) [1605, 5424, 6307, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6339, 10344, 17048, 24838] .e) [1605, 5424, 6531, 10344, 17048, 24838] .e) [1605, 5424, 7603, 10344, 14571, 17048, 24838]
 (.n .e [1605, 5424, 7603, 10344, 17048, 23195, 24838] .e))) [1605, 5424, 7603, 10344, 17048, 24838, 31111]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 7879, 10344, 14571, 17048, 24838] .e) [1605, 5424, 7879, 10344, 17048, 24838, 31111] .e) [1605, 5424, 10344, 14571, 17048, 23195, 24838]
 (.n .e [1605, 5425, 6275, 10344, 17048, 24838] .e)) [1605, 5426, 6275, 10344, 17048, 24838]
 (.n
 (.n .e [1605, 5428, 6275, 10344, 17048, 24838] .e) [1605, 5432, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5488, 6275, 10344, 17048, 24838] .e)))) [1605, 5552, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 6005, 6275, 7603, 10344, 17048, 24838] .e) [1605, 6005, 6275, 10344, 15736, 17048, 24838] .e) [1605, 6005, 6275, 10344, 17048, 24838, 30006]
 (.n .e [1605, 6275, 7603, 10344, 17048, 22456, 24838] .e)) [1605, 6275, 7603, 10344, 17048, 24838, 30006]
 (.n
 (.n
 (.n .e [1605, 6275, 10344, 15736, 17048, 22456, 24838] .e) [1607, 5424, 6275, 10344, 17048, 24838] .e) [1613, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1621, 5424, 6275, 10344, 17048, 24838] .e))) [1637, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [1733, 5424, 6275, 10344, 17048, 24838] .e) [1861, 5424, 6275, 10344, 17048, 24838] .e) [5424, 6005, 6275, 10344, 11885, 17048, 24838]
 (.n .e [5424, 6005, 6275, 10344, 17048, 18141, 24838] .e)) [5424, 6005, 6275, 10344, 17048, 24838, 26439]
 (.n
 (.n .e [5424, 6275, 7879, 10344, 17048, 18141, 24838] .e) [5424, 6275, 7879, 10344, 17048, 24838, 26439]
 (.n .e [5424, 6275, 10344, 11885, 17048, 18141, 24838] .e)))))

def T7bbbb : T := .n T7bbbba [1605, 5424, 6275, 15736, 17048, 24838, 26990] T7bbbbb

def T7bbb : T := .n T7bbba [1605, 5424, 6275, 10344, 17048, 24838, 32711] T7bbbb

def T7bb : T := .n T7bba [1605, 5424, 6275, 10344, 17048, 24838, 24902] T7bbb

def T7b : T := .n T7ba [1605, 5424, 6275, 10344, 14571, 17048, 24838, 24838] T7bb

def T7 : T := .n T7a [1605, 2048, 5424, 6275, 10344, 17048, 24838, 24838] T7b

def T8 : T := (.n
 (.n
 (.n
 (.n
 (.n
 (.n .e [0, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1, 1605, 5424, 6275, 10344, 17048, 24838] .e) [2, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [4, 1605, 5424, 6275, 10344, 17048, 24838] .e)) [8, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [16, 1605, 5424, 6275, 10344, 17048, 24838] .e) [32, 1605, 5424, 6275, 10344, 17048, 24838] .e) [64, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [128, 1605, 5424, 6275, 10344, 17048, 24838] .e))) [256, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n .e [512, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1024, 1605, 5424, 6275, 10344, 17048, 24838] .e) [1605, 1605, 5424, 6275, 10344, 17048, 24838]
 (.n .e [1605, 2048, 5424, 6275, 10344, 17048, 24838] .e)) [1605, 4096, 5424, 6275, 10344, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 5424, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6005, 6275, 10344, 17048, 24838] .e) [1605, 5424, 6275, 6275, 10344, 17048, 24838]
 (.n .e [1605, 5424, 6275, 7603, 10344, 17048, 24838] .e)))) [1605, 5424, 6275, 7879, 10344, 17048, 24838]
 (.n
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 8192, 10344, 17048, 24838] .e) [1605, 5424, 6275, 10344, 10344, 17048, 24838] .e) [1605, 5424, 6275, 10344, 11885, 17048, 24838]
 (.n .e [1605, 5424, 6275, 10344, 14571, 17048, 24838] .e)) [1605, 5424, 6275, 10344, 15736, 17048, 24838]
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 16384, 17048, 24838] .e) [1605, 5424, 6275, 10344, 17048, 17048, 24838] .e) [1605, 5424, 6275, 10344, 17048, 18141, 24838]
 (.n .e [1605, 5424, 6275, 10344, 17048, 22456, 24838] .e))) [1605, 5424, 6275, 10344, 17048, 23195, 24838]
 (.n
 (.n
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 24838] .e) [1605, 5424, 6275, 10344, 17048, 24838, 25502] .e) [1605, 5424, 6275, 10344, 17048, 24838, 26439]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 26990] .e)) [1605, 5424, 6275, 10344, 17048, 24838, 27384]
 (.n
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 30006] .e) [1605, 5424, 6275, 10344, 17048, 24838, 31111]
 (.n .e [1605, 5424, 6275, 10344, 17048, 24838, 32767] .e)))))

def T9 : T := (.n .e [1605, 5424, 6275, 10344, 17048, 24838] .e)

def Tv (s : ℕ) : T := ([.e, .e, .e, .e, T4, T5, T6, T7, T8, T9] : List T).getD s .e

theorem all_n {f : List ℕ → Bool} (l : T) (k : List ℕ) (r : T) (h0 : f (k.map ex) = true)
    (h1 : (dec l).all f = true) (h2 : (dec r).all f = true) : (dec (.n l k r)).all f = true := by
  simp only [dec] at h1 h2 ⊢
  simp only [toL, List.map_cons, List.map_append, List.all_cons, List.all_append, h0, h1, h2,
    Bool.and_self]

theorem c_T4 : (dec T4).all (chk Tv 4) = true := by decide +kernel

theorem c_T5aaaa : (dec T5aaaa).all (chk Tv 5) = true := by decide +kernel

theorem c_T5aaab : (dec T5aaab).all (chk Tv 5) = true := by decide +kernel

theorem c_T5aaa : (dec T5aaa).all (chk Tv 5) = true :=
  all_n T5aaaa [65, 5424, 6279, 10344, 17048, 24838] T5aaab (by decide +kernel) c_T5aaaa c_T5aaab

theorem c_T5aaba : (dec T5aaba).all (chk Tv 5) = true := by decide +kernel

theorem c_T5aabb : (dec T5aabb).all (chk Tv 5) = true := by decide +kernel

theorem c_T5aab : (dec T5aab).all (chk Tv 5) = true :=
  all_n T5aaba [1605, 5424, 6275, 10344, 17052, 24902] T5aabb (by decide +kernel) c_T5aaba c_T5aabb

theorem c_T5aa : (dec T5aa).all (chk Tv 5) = true :=
  all_n T5aaa [272, 1637, 6275, 10344, 17048, 24838] T5aab (by decide +kernel) c_T5aaa c_T5aab

theorem c_T5abaa : (dec T5abaa).all (chk Tv 5) = true := by decide +kernel

theorem c_T5abab : (dec T5abab).all (chk Tv 5) = true := by decide +kernel

theorem c_T5aba : (dec T5aba).all (chk Tv 5) = true :=
  all_n T5abaa [1605, 5424, 6275, 15736, 17050, 26990] T5abab (by decide +kernel) c_T5abaa c_T5abab

theorem c_T5abba : (dec T5abba).all (chk Tv 5) = true := by decide +kernel

theorem c_T5abbb : (dec T5abbb).all (chk Tv 5) = true := by decide +kernel

theorem c_T5abb : (dec T5abb).all (chk Tv 5) = true :=
  all_n T5abba [1605, 5424, 6547, 10344, 17304, 24838] T5abbb (by decide +kernel) c_T5abba c_T5abbb

theorem c_T5ab : (dec T5ab).all (chk Tv 5) = true :=
  all_n T5aba [1605, 5424, 6299, 17048, 24838, 26990] T5abb (by decide +kernel) c_T5aba c_T5abb

theorem c_T5a : (dec T5a).all (chk Tv 5) = true :=
  all_n T5aa [1605, 5424, 6275, 10348, 17052, 25502] T5ab (by decide +kernel) c_T5aa c_T5ab

theorem c_T5baaa : (dec T5baaa).all (chk Tv 5) = true := by decide +kernel

theorem c_T5baab : (dec T5baab).all (chk Tv 5) = true := by decide +kernel

theorem c_T5baa : (dec T5baa).all (chk Tv 5) = true :=
  all_n T5baaa [1605, 5432, 6275, 10344, 25502, 26990] T5baab (by decide +kernel) c_T5baaa c_T5baab

theorem c_T5baba : (dec T5baba).all (chk Tv 5) = true := by decide +kernel

theorem c_T5babb : (dec T5babb).all (chk Tv 5) = true := by decide +kernel

theorem c_T5bab : (dec T5bab).all (chk Tv 5) = true :=
  all_n T5baba [1605, 7603, 10345, 17048, 22456, 24838] T5babb (by decide +kernel) c_T5baba c_T5babb

theorem c_T5ba : (dec T5ba).all (chk Tv 5) = true :=
  all_n T5baa [1605, 5552, 6275, 10472, 17048, 24838] T5bab (by decide +kernel) c_T5baa c_T5bab

theorem c_T5bbaa : (dec T5bbaa).all (chk Tv 5) = true := by decide +kernel

theorem c_T5bbab : (dec T5bbab).all (chk Tv 5) = true := by decide +kernel

theorem c_T5bba : (dec T5bba).all (chk Tv 5) = true :=
  all_n T5bbaa [1637, 5424, 6307, 14571, 17048, 24838] T5bbab (by decide +kernel) c_T5bbaa c_T5bbab

theorem c_T5bbba : (dec T5bbba).all (chk Tv 5) = true := by decide +kernel

theorem c_T5bbbb : (dec T5bbbb).all (chk Tv 5) = true := by decide +kernel

theorem c_T5bbb : (dec T5bbb).all (chk Tv 5) = true :=
  all_n T5bbba [5424, 6275, 10348, 17048, 18141, 25502] T5bbbb (by decide +kernel) c_T5bbba c_T5bbbb

theorem c_T5bb : (dec T5bb).all (chk Tv 5) = true :=
  all_n T5bba [1765, 5424, 6275, 10344, 17048, 24838] T5bbb (by decide +kernel) c_T5bba c_T5bbb

theorem c_T5b : (dec T5b).all (chk Tv 5) = true :=
  all_n T5ba [1613, 5424, 6275, 25502, 26990] T5bb (by decide +kernel) c_T5ba c_T5bb

theorem c_T5 : (dec T5).all (chk Tv 5) = true :=
  all_n T5a [1605, 5426, 6275, 10346, 17048, 26990] T5b (by decide +kernel) c_T5a c_T5b

theorem c_T6aaaaa : (dec T6aaaaa).all (chk Tv 6) = true := by decide +kernel

theorem c_T6aaaab : (dec T6aaaab).all (chk Tv 6) = true := by decide +kernel

theorem c_T6aaaa : (dec T6aaaa).all (chk Tv 6) = true :=
  all_n T6aaaaa [1, 5425, 6005, 6275, 10344, 17048, 24838] T6aaaab (by decide +kernel) c_T6aaaaa c_T6aaaab

theorem c_T6aaaba : (dec T6aaaba).all (chk Tv 6) = true := by decide +kernel

theorem c_T6aaabb : (dec T6aaabb).all (chk Tv 6) = true := by decide +kernel

theorem c_T6aaab : (dec T6aaab).all (chk Tv 6) = true :=
  all_n T6aaaba [8, 1605, 5424, 6275, 17048, 24838, 26990] T6aaabb (by decide +kernel) c_T6aaaba c_T6aaabb

theorem c_T6aaa : (dec T6aaa).all (chk Tv 6) = true :=
  all_n T6aaaa [4, 1605, 5424, 6275, 10344, 17080, 24838] T6aaab (by decide +kernel) c_T6aaaa c_T6aaab

theorem c_T6aabaa : (dec T6aabaa).all (chk Tv 6) = true := by decide +kernel

theorem c_T6aabab : (dec T6aabab).all (chk Tv 6) = true := by decide +kernel

theorem c_T6aaba : (dec T6aaba).all (chk Tv 6) = true :=
  all_n T6aabaa [48, 1605, 5424, 6275, 10344, 17048, 24886] T6aabab (by decide +kernel) c_T6aabaa c_T6aabab

theorem c_T6aabba : (dec T6aabba).all (chk Tv 6) = true := by decide +kernel

theorem c_T6aabbb : (dec T6aabbb).all (chk Tv 6) = true := by decide +kernel

theorem c_T6aabb : (dec T6aabb).all (chk Tv 6) = true :=
  all_n T6aabba [152, 1605, 5424, 6275, 10344, 17048, 24838] T6aabbb (by decide +kernel) c_T6aabba c_T6aabbb

theorem c_T6aab : (dec T6aab).all (chk Tv 6) = true :=
  all_n T6aaba [104, 1605, 5424, 6005, 6275, 17048, 24838] T6aabb (by decide +kernel) c_T6aaba c_T6aabb

theorem c_T6aa : (dec T6aa).all (chk Tv 6) = true :=
  all_n T6aaa [16, 5424, 6275, 10344, 11885, 18141, 24838] T6aab (by decide +kernel) c_T6aaa c_T6aab

theorem c_T6abaaa : (dec T6abaaa).all (chk Tv 6) = true := by decide +kernel

theorem c_T6abaab : (dec T6abaab).all (chk Tv 6) = true := by decide +kernel

theorem c_T6abaa : (dec T6abaa).all (chk Tv 6) = true :=
  all_n T6abaaa [1024, 1605, 5425, 6275, 10344, 17048, 24838] T6abaab (by decide +kernel) c_T6abaaa c_T6abaab

theorem c_T6ababa : (dec T6ababa).all (chk Tv 6) = true := by decide +kernel

theorem c_T6ababb : (dec T6ababb).all (chk Tv 6) = true := by decide +kernel

theorem c_T6abab : (dec T6abab).all (chk Tv 6) = true :=
  all_n T6ababa [1605, 4096, 5424, 6275, 10344, 17052, 24838] T6ababb (by decide +kernel) c_T6ababa c_T6ababb

theorem c_T6aba : (dec T6aba).all (chk Tv 6) = true :=
  all_n T6abaa [1605, 1637, 5424, 6275, 14571, 17048, 24838] T6abab (by decide +kernel) c_T6abaa c_T6abab

theorem c_T6abbaa : (dec T6abbaa).all (chk Tv 6) = true := by decide +kernel

theorem c_T6abbab : (dec T6abbab).all (chk Tv 6) = true := by decide +kernel

theorem c_T6abba : (dec T6abba).all (chk Tv 6) = true :=
  all_n T6abbaa [1605, 5424, 6275, 6291, 10344, 17048, 24838] T6abbab (by decide +kernel) c_T6abbaa c_T6abbab

theorem c_T6abbba : (dec T6abbba).all (chk Tv 6) = true := by decide +kernel

theorem c_T6abbbb : (dec T6abbbb).all (chk Tv 6) = true := by decide +kernel

theorem c_T6abbb : (dec T6abbb).all (chk Tv 6) = true :=
  all_n T6abbba [1605, 5424, 6275, 10344, 10872, 17048, 24838] T6abbbb (by decide +kernel) c_T6abbba c_T6abbbb

theorem c_T6abb : (dec T6abb).all (chk Tv 6) = true :=
  all_n T6abba [1605, 5424, 6275, 8192, 10344, 17048, 24870] T6abbb (by decide +kernel) c_T6abba c_T6abbb

theorem c_T6ab : (dec T6ab).all (chk Tv 6) = true :=
  all_n T6aba [1605, 5424, 5428, 6279, 10344, 17048, 24838] T6abb (by decide +kernel) c_T6aba c_T6abb

theorem c_T6a : (dec T6a).all (chk Tv 6) = true :=
  all_n T6aa [304, 1605, 6275, 10344, 17048, 24838, 27384] T6ab (by decide +kernel) c_T6aa c_T6ab

theorem c_T6baaaa : (dec T6baaaa).all (chk Tv 6) = true := by decide +kernel

theorem c_T6baaab : (dec T6baaab).all (chk Tv 6) = true := by decide +kernel

theorem c_T6baaa : (dec T6baaa).all (chk Tv 6) = true :=
  all_n T6baaaa [1605, 5424, 6275, 10344, 17048, 19096, 24838] T6baaab (by decide +kernel) c_T6baaaa c_T6baaab

theorem c_T6baaba : (dec T6baaba).all (chk Tv 6) = true := by decide +kernel

theorem c_T6baabb : (dec T6baabb).all (chk Tv 6) = true := by decide +kernel

theorem c_T6baab : (dec T6baab).all (chk Tv 6) = true :=
  all_n T6baaba [1605, 5424, 6275, 10344, 17048, 24838, 32766] T6baabb (by decide +kernel) c_T6baaba c_T6baabb

theorem c_T6baa : (dec T6baa).all (chk Tv 6) = true :=
  all_n T6baaa [1605, 5424, 6275, 10344, 17048, 24838, 25862] T6baab (by decide +kernel) c_T6baaa c_T6baab

theorem c_T6babaa : (dec T6babaa).all (chk Tv 6) = true := by decide +kernel

theorem c_T6babab : (dec T6babab).all (chk Tv 6) = true := by decide +kernel

theorem c_T6baba : (dec T6baba).all (chk Tv 6) = true :=
  all_n T6babaa [1605, 5424, 6275, 10344, 17112, 24838, 31111] T6babab (by decide +kernel) c_T6babaa c_T6babab

theorem c_T6babba : (dec T6babba).all (chk Tv 6) = true := by decide +kernel

theorem c_T6babbb : (dec T6babbb).all (chk Tv 6) = true := by decide +kernel

theorem c_T6babb : (dec T6babb).all (chk Tv 6) = true :=
  all_n T6babba [1605, 5424, 6275, 10600, 16384, 17048, 24838] T6babbb (by decide +kernel) c_T6babba c_T6babbb

theorem c_T6bab : (dec T6bab).all (chk Tv 6) = true :=
  all_n T6baba [1605, 5424, 6275, 10346, 17048, 22456, 24838] T6babb (by decide +kernel) c_T6baba c_T6babb

theorem c_T6ba : (dec T6ba).all (chk Tv 6) = true :=
  all_n T6baa [1605, 5424, 6275, 10344, 17048, 26439, 28934] T6bab (by decide +kernel) c_T6baa c_T6bab

theorem c_T6bbaaa : (dec T6bbaaa).all (chk Tv 6) = true := by decide +kernel

theorem c_T6bbaab : (dec T6bbaab).all (chk Tv 6) = true := by decide +kernel

theorem c_T6bbaa : (dec T6bbaa).all (chk Tv 6) = true :=
  all_n T6bbaaa [1605, 5424, 6339, 10344, 17048, 17048, 24838] T6bbaab (by decide +kernel) c_T6bbaaa c_T6bbaab

theorem c_T6bbaba : (dec T6bbaba).all (chk Tv 6) = true := by decide +kernel

theorem c_T6bbabb : (dec T6bbabb).all (chk Tv 6) = true := by decide +kernel

theorem c_T6bbab : (dec T6bbab).all (chk Tv 6) = true :=
  all_n T6bbaba [1605, 5428, 6275, 10344, 17048, 24838] T6bbabb (by decide +kernel) c_T6bbaba c_T6bbabb

theorem c_T6bba : (dec T6bba).all (chk Tv 6) = true :=
  all_n T6bbaa [1605, 5424, 10344, 14571, 17048, 22659, 24838] T6bbab (by decide +kernel) c_T6bbaa c_T6bbab

theorem c_T6bbbaa : (dec T6bbbaa).all (chk Tv 6) = true := by decide +kernel

theorem c_T6bbbab : (dec T6bbbab).all (chk Tv 6) = true := by decide +kernel

theorem c_T6bbba : (dec T6bbba).all (chk Tv 6) = true :=
  all_n T6bbbaa [1607, 5424, 6275, 10344, 11885, 17048, 24838] T6bbbab (by decide +kernel) c_T6bbbaa c_T6bbbab

theorem c_T6bbbba : (dec T6bbbba).all (chk Tv 6) = true := by decide +kernel

theorem c_T6bbbbb : (dec T6bbbbb).all (chk Tv 6) = true := by decide +kernel

theorem c_T6bbbb : (dec T6bbbb).all (chk Tv 6) = true :=
  all_n T6bbbba [1861, 5424, 6275, 10344, 14571, 17048, 24838] T6bbbbb (by decide +kernel) c_T6bbbba c_T6bbbbb

theorem c_T6bbb : (dec T6bbb).all (chk Tv 6) = true :=
  all_n T6bbba [1629, 5424, 6275, 10344, 17048, 24838] T6bbbb (by decide +kernel) c_T6bbba c_T6bbbb

theorem c_T6bb : (dec T6bb).all (chk Tv 6) = true :=
  all_n T6bba [1605, 5552, 6275, 10344, 15736, 17048, 24838] T6bbb (by decide +kernel) c_T6bba c_T6bbb

theorem c_T6b : (dec T6b).all (chk Tv 6) = true :=
  all_n T6ba [1605, 5424, 6283, 7887, 10344, 17048, 24838] T6bb (by decide +kernel) c_T6ba c_T6bb

theorem c_T6 : (dec T6).all (chk Tv 6) = true :=
  all_n T6a [1605, 5424, 6275, 10344, 16384, 17048, 24854] T6b (by decide +kernel) c_T6a c_T6b

theorem c_T7aaaaa : (dec T7aaaaa).all (chk Tv 7) = true := by decide +kernel

theorem c_T7aaaab : (dec T7aaaab).all (chk Tv 7) = true := by decide +kernel

theorem c_T7aaaa : (dec T7aaaa).all (chk Tv 7) = true :=
  all_n T7aaaaa [0, 1605, 5424, 6275, 10344, 17048, 24838, 32767] T7aaaab (by decide +kernel) c_T7aaaaa c_T7aaaab

theorem c_T7aaaba : (dec T7aaaba).all (chk Tv 7) = true := by decide +kernel

theorem c_T7aaabb : (dec T7aaabb).all (chk Tv 7) = true := by decide +kernel

theorem c_T7aaab : (dec T7aaab).all (chk Tv 7) = true :=
  all_n T7aaaba [2, 1605, 5424, 6275, 10344, 17048, 17048, 24838] T7aaabb (by decide +kernel) c_T7aaaba c_T7aaabb

theorem c_T7aaa : (dec T7aaa).all (chk Tv 7) = true :=
  all_n T7aaaa [1, 1605, 5424, 6275, 10344, 17048, 24838, 26990] T7aaab (by decide +kernel) c_T7aaaa c_T7aaab

theorem c_T7aabaa : (dec T7aabaa).all (chk Tv 7) = true := by decide +kernel

theorem c_T7aabab : (dec T7aabab).all (chk Tv 7) = true := by decide +kernel

theorem c_T7aaba : (dec T7aaba).all (chk Tv 7) = true :=
  all_n T7aabaa [8, 256, 1605, 5424, 6275, 10344, 17048, 24838] T7aabab (by decide +kernel) c_T7aabaa c_T7aabab

theorem c_T7aabba : (dec T7aabba).all (chk Tv 7) = true := by decide +kernel

theorem c_T7aabbb : (dec T7aabbb).all (chk Tv 7) = true := by decide +kernel

theorem c_T7aabb : (dec T7aabb).all (chk Tv 7) = true :=
  all_n T7aabba [16, 1605, 5424, 6275, 10344, 17048, 24838, 31111] T7aabbb (by decide +kernel) c_T7aabba c_T7aabbb

theorem c_T7aab : (dec T7aab).all (chk Tv 7) = true :=
  all_n T7aaba [8, 1605, 5432, 6275, 10344, 17048, 24838] T7aabb (by decide +kernel) c_T7aaba c_T7aabb

theorem c_T7aa : (dec T7aa).all (chk Tv 7) = true :=
  all_n T7aaa [4, 1605, 5424, 6275, 6279, 10344, 17048, 24838] T7aab (by decide +kernel) c_T7aaa c_T7aab

theorem c_T7abaaa : (dec T7abaaa).all (chk Tv 7) = true := by decide +kernel

theorem c_T7abaab : (dec T7abaab).all (chk Tv 7) = true := by decide +kernel

theorem c_T7abaa : (dec T7abaa).all (chk Tv 7) = true :=
  all_n T7abaaa [64, 1605, 5424, 6275, 10344, 16384, 17048, 24838] T7abaab (by decide +kernel) c_T7abaaa c_T7abaab

theorem c_T7ababa : (dec T7ababa).all (chk Tv 7) = true := by decide +kernel

theorem c_T7ababb : (dec T7ababb).all (chk Tv 7) = true := by decide +kernel

theorem c_T7abab : (dec T7abab).all (chk Tv 7) = true :=
  all_n T7ababa [256, 512, 1605, 5424, 6275, 10344, 17048, 24838] T7ababb (by decide +kernel) c_T7ababa c_T7ababb

theorem c_T7aba : (dec T7aba).all (chk Tv 7) = true :=
  all_n T7abaa [128, 1605, 5424, 6005, 6275, 10344, 17048, 24838] T7abab (by decide +kernel) c_T7abaa c_T7abab

theorem c_T7abbaa : (dec T7abbaa).all (chk Tv 7) = true := by decide +kernel

theorem c_T7abbab : (dec T7abbab).all (chk Tv 7) = true := by decide +kernel

theorem c_T7abba : (dec T7abba).all (chk Tv 7) = true :=
  all_n T7abbaa [512, 1605, 5424, 6275, 10344, 17048, 24838, 31111] T7abbab (by decide +kernel) c_T7abbaa c_T7abbab

theorem c_T7abbba : (dec T7abbba).all (chk Tv 7) = true := by decide +kernel

theorem c_T7abbbb : (dec T7abbbb).all (chk Tv 7) = true := by decide +kernel

theorem c_T7abbb : (dec T7abbb).all (chk Tv 7) = true :=
  all_n T7abbba [1605, 1605, 5424, 6275, 10344, 17048, 22456, 24838] T7abbbb (by decide +kernel) c_T7abbba c_T7abbbb

theorem c_T7abb : (dec T7abb).all (chk Tv 7) = true :=
  all_n T7abba [1024, 1605, 5424, 6275, 10344, 17048, 24838, 25502] T7abbb (by decide +kernel) c_T7abba c_T7abbb

theorem c_T7ab : (dec T7ab).all (chk Tv 7) = true :=
  all_n T7aba [258, 1605, 5424, 6275, 10344, 17048, 24838] T7abb (by decide +kernel) c_T7aba c_T7abb

theorem c_T7a : (dec T7a).all (chk Tv 7) = true :=
  all_n T7aa [32, 1605, 5424, 6275, 10344, 17048, 24838, 24838] T7ab (by decide +kernel) c_T7aa c_T7ab

theorem c_T7baaaa : (dec T7baaaa).all (chk Tv 7) = true := by decide +kernel

theorem c_T7baaab : (dec T7baaab).all (chk Tv 7) = true := by decide +kernel

theorem c_T7baaa : (dec T7baaa).all (chk Tv 7) = true :=
  all_n T7baaaa [1605, 4096, 5424, 6275, 10344, 17048, 22456, 24838] T7baaab (by decide +kernel) c_T7baaaa c_T7baaab

theorem c_T7baaba : (dec T7baaba).all (chk Tv 7) = true := by decide +kernel

theorem c_T7baabb : (dec T7baabb).all (chk Tv 7) = true := by decide +kernel

theorem c_T7baab : (dec T7baab).all (chk Tv 7) = true :=
  all_n T7baaba [1605, 5424, 6005, 6275, 10344, 17048, 24838, 24838] T7baabb (by decide +kernel) c_T7baaba c_T7baabb

theorem c_T7baa : (dec T7baa).all (chk Tv 7) = true :=
  all_n T7baaa [1605, 5424, 5424, 6275, 10344, 17048, 18141, 24838] T7baab (by decide +kernel) c_T7baaa c_T7baab

theorem c_T7babaa : (dec T7babaa).all (chk Tv 7) = true := by decide +kernel

theorem c_T7babab : (dec T7babab).all (chk Tv 7) = true := by decide +kernel

theorem c_T7baba : (dec T7baba).all (chk Tv 7) = true :=
  all_n T7babaa [1605, 5424, 6275, 7879, 10344, 17048, 17048, 24838] T7babab (by decide +kernel) c_T7babaa c_T7babab

theorem c_T7babba : (dec T7babba).all (chk Tv 7) = true := by decide +kernel

theorem c_T7babbb : (dec T7babbb).all (chk Tv 7) = true := by decide +kernel

theorem c_T7babb : (dec T7babb).all (chk Tv 7) = true :=
  all_n T7babba [1605, 5424, 6275, 10344, 10472, 17048, 24838] T7babbb (by decide +kernel) c_T7babba c_T7babbb

theorem c_T7bab : (dec T7bab).all (chk Tv 7) = true :=
  all_n T7baba [1605, 5424, 6275, 8192, 10344, 17048, 24838, 32767] T7babb (by decide +kernel) c_T7baba c_T7babb

theorem c_T7ba : (dec T7ba).all (chk Tv 7) = true :=
  all_n T7baa [1605, 5424, 6275, 6531, 10344, 17048, 24838] T7bab (by decide +kernel) c_T7baa c_T7bab

theorem c_T7bbaaa : (dec T7bbaaa).all (chk Tv 7) = true := by decide +kernel

theorem c_T7bbaab : (dec T7bbaab).all (chk Tv 7) = true := by decide +kernel

theorem c_T7bbaa : (dec T7bbaa).all (chk Tv 7) = true :=
  all_n T7bbaaa [1605, 5424, 6275, 10344, 16384, 17048, 23195, 24838] T7bbaab (by decide +kernel) c_T7bbaaa c_T7bbaab

theorem c_T7bbaba : (dec T7bbaba).all (chk Tv 7) = true := by decide +kernel

theorem c_T7bbabb : (dec T7bbabb).all (chk Tv 7) = true := by decide +kernel

theorem c_T7bbab : (dec T7bbab).all (chk Tv 7) = true :=
  all_n T7bbaba [1605, 5424, 6275, 10344, 17048, 22456, 24838, 30654] T7bbabb (by decide +kernel) c_T7bbaba c_T7bbabb

theorem c_T7bba : (dec T7bba).all (chk Tv 7) = true :=
  all_n T7bbaa [1605, 5424, 6275, 10344, 17048, 17049, 24838] T7bbab (by decide +kernel) c_T7bbaa c_T7bbab

theorem c_T7bbbaa : (dec T7bbbaa).all (chk Tv 7) = true := by decide +kernel

theorem c_T7bbbab : (dec T7bbbab).all (chk Tv 7) = true := by decide +kernel

theorem c_T7bbba : (dec T7bbba).all (chk Tv 7) = true :=
  all_n T7bbbaa [1605, 5424, 6275, 10344, 17048, 24838, 26990, 31215] T7bbbab (by decide +kernel) c_T7bbbaa c_T7bbbab

theorem c_T7bbbba : (dec T7bbbba).all (chk Tv 7) = true := by decide +kernel

theorem c_T7bbbbb : (dec T7bbbbb).all (chk Tv 7) = true := by decide +kernel

theorem c_T7bbbb : (dec T7bbbb).all (chk Tv 7) = true :=
  all_n T7bbbba [1605, 5424, 6275, 15736, 17048, 24838, 26990] T7bbbbb (by decide +kernel) c_T7bbbba c_T7bbbbb

theorem c_T7bbb : (dec T7bbb).all (chk Tv 7) = true :=
  all_n T7bbba [1605, 5424, 6275, 10344, 17048, 24838, 32711] T7bbbb (by decide +kernel) c_T7bbba c_T7bbbb

theorem c_T7bb : (dec T7bb).all (chk Tv 7) = true :=
  all_n T7bba [1605, 5424, 6275, 10344, 17048, 24838, 24902] T7bbb (by decide +kernel) c_T7bba c_T7bbb

theorem c_T7b : (dec T7b).all (chk Tv 7) = true :=
  all_n T7ba [1605, 5424, 6275, 10344, 14571, 17048, 24838, 24838] T7bb (by decide +kernel) c_T7ba c_T7bb

theorem c_T7 : (dec T7).all (chk Tv 7) = true :=
  all_n T7a [1605, 2048, 5424, 6275, 10344, 17048, 24838, 24838] T7b (by decide +kernel) c_T7a c_T7b

theorem c_T8 : (dec T8).all (chk Tv 8) = true := by decide +kernel

theorem c_T9 : (dec T9).all (chk Tv 9) = true := by decide +kernel

theorem top_ok : ∀ L ∈ XL.sublists, covN L = FULL → List.insertionSort (· ≤ ·) L ∈ dec (Tv 9) := by
  decide +kernel

theorem chk_all : ∀ s, ∀ L ∈ dec (Tv s), chk Tv s L = true := by
  have key : ∀ s, (dec (Tv s)).all (chk Tv s) = true := by
    intro s
    rcases s with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | s
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_T4
    · exact c_T5
    · exact c_T6
    · exact c_T7
    · exact c_T8
    · exact c_T9
    · rfl
  intro s L hL
  exact List.all_eq_true.1 (key s) L hL

theorem main : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hM, hs, hf⟩
  have e : ∀ x, W C C.output x = decide (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
    intro x
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hf x
  have hT : val C C.output = FULL := by
    have h1 : W C C.output = fun x => decide (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := funext e
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
  have h8 : Run 9 (St C 0) := Run.mono_le hs hrun
  have hsub : St C 0 ∈ XL.sublists := by
    rw [List.mem_sublists, ← range_val C]
    exact List.Sublist.map _ List.filter_sublist
  have hin := top_ok (St C 0) hsub (cov_full h8.inv.2)
  exact cert Tv chk_all 9 _ hin (Run.perm (List.perm_insertionSort _ _).symm h8)

end PEqualNP.Outside.L_meta_741

theorem PEqualNP.Outside.L_meta_741 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) :=
  PEqualNP.Outside.L_meta_741.main
