import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_743

def T : ℕ := 1023
def ALLV : ℕ := 65535

def accm (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: vs => if v.testBit (10 + m) then accm m vs else v ||| accm m vs

def covB (L : List ℕ) : Bool :=
  (List.range 6).all fun m => (accm m L &&& T) == T

def passes (s : ℕ) (L : List ℕ) : Bool := Nat.ble L.length (s + 1) && covB L

def opv (o : Bool) (a b : ℕ) : ℕ := if o then a &&& b else a ||| b

def kept (k : Bool) (x : ℕ) (xs : List ℕ) : List ℕ := if k then x :: xs else xs

def picks : List ℕ → List (ℕ × List ℕ)
  | [] => []
  | x :: xs => (x, xs) :: (picks xs).map fun q => (q.1, x :: q.2)

def pairsOf : List ℕ → List (ℕ × ℕ × List ℕ)
  | [] => []
  | x :: xs => (picks xs).map (fun q => (x, q.1, q.2)) ++
      (pairsOf xs).map fun q => (q.1, q.2.1, x :: q.2.2)

def twoCh (a b : ℕ) (r : List ℕ) : List (List ℕ) :=
  [true, false].flatMap fun o => [true, false].flatMap fun ka => [true, false].map fun kb =>
    opv o a b :: kept ka a (kept kb b r)

def children (L : List ℕ) : List (List ℕ) :=
  (pairsOf L).flatMap (fun q => twoCh q.1 q.2.1 q.2.2) ++
  (picks L).flatMap (fun q => [q.1 :: q.1 :: q.2, 0 :: q.2, 0 :: q.1 :: q.2]) ++
  [0 :: L, ALLV :: L]

inductive Tr where
  | E : Tr
  | N : Tr → List ℕ → ℕ → Tr → Tr

def cmpL : List ℕ → List ℕ → Ordering
  | [], [] => Ordering.eq
  | [], _ :: _ => Ordering.lt
  | _ :: _, [] => Ordering.gt
  | a :: as, b :: bs => if Nat.blt a b then Ordering.lt else if Nat.blt b a then Ordering.gt else cmpL as bs

def look : Tr → List ℕ → ℕ → Bool
  | Tr.E, _, _ => false
  | Tr.N l k v r, x, s =>
    match cmpL x k with
    | Ordering.lt => look l x s
    | Ordering.gt => look r x s
    | Ordering.eq => Nat.ble s v

def srt (L : List ℕ) : List ℕ := List.insertionSort (fun a b => a ≤ b) L

def rot (v : ℕ) : ℕ := ((v &&& 15855) <<< 1) ||| ((v &&& 16912) >>> 4) ||| (v &&& 32768)

def lookR (t : Tr) (s : ℕ) : ℕ → List ℕ → Bool
  | 0, _ => false
  | k + 1, L => look t (srt L) s || lookR t s k (L.map rot)

def chkE (t : Tr) (K : List ℕ) (lev : ℕ) : Bool :=
  Nat.ble 1 lev && !(cmpL K [T] == Ordering.eq) &&
    (children K).all fun ch => !(passes (lev - 1) ch) || lookR t (lev - 1) 5 ch

def allE (t : Tr) : Tr → Bool
  | Tr.E => true
  | Tr.N l k v r => chkE t k v && allE t l && allE t r


/-! ## Cover semantics -/

def Cov (L : List ℕ) : Prop :=
  ∀ m < 6, ∀ e < 10, ∃ v ∈ L, v.testBit (10 + m) = false ∧ v.testBit e = true

theorem accm_bit (m e : ℕ) : ∀ L : List ℕ, (accm m L).testBit e = true →
    ∃ v ∈ L, v.testBit (10 + m) = false ∧ v.testBit e = true
  | [], h => by simp [accm] at h
  | v :: vs, h => by
    unfold accm at h
    by_cases hv : v.testBit (10 + m) = true
    · rw [if_pos hv] at h
      obtain ⟨w, hw, h1, h2⟩ := accm_bit m e vs h
      exact ⟨w, List.mem_cons_of_mem _ hw, h1, h2⟩
    · rw [if_neg hv, Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨v, List.mem_cons_self .., by simpa using hv, h⟩
      · obtain ⟨w, hw, h1, h2⟩ := accm_bit m e vs h
        exact ⟨w, List.mem_cons_of_mem _ hw, h1, h2⟩

theorem bit_accm (m e : ℕ) : ∀ L : List ℕ, (∃ v ∈ L, v.testBit (10 + m) = false ∧ v.testBit e = true) →
    (accm m L).testBit e = true
  | [], ⟨v, hv, _⟩ => by simp at hv
  | x :: xs, ⟨v, hv, h1, h2⟩ => by
    unfold accm
    rcases List.mem_cons.1 hv with rfl | hv
    · rw [if_neg (by simp [h1]), Nat.testBit_or, h2, Bool.true_or]
    · have := bit_accm m e xs ⟨v, hv, h1, h2⟩
      split
      · exact this
      · rw [Nat.testBit_or, this, Bool.or_true]

theorem T_eq : T = 2 ^ 10 - 1 := rfl

theorem covB_of_cov {L : List ℕ} (h : Cov L) : covB L = true := by
  unfold covB
  rw [List.all_eq_true]
  intro m hm
  have hm' : m < 6 := List.mem_range.1 hm
  rw [beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, T_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 10
  · rw [bit_accm m i L (h m hm' i hi)]
    simp [hi]
  · simp [hi]

theorem cov_T : Cov [T] := by
  unfold Cov
  decide

/-! ## Runs -/

inductive Run : ℕ → List ℕ → Prop
  | done (s : ℕ) : Run s [T]
  | perm {s : ℕ} {L₁ L₂ : List ℕ} : L₁.Perm L₂ → Run s L₁ → Run s L₂
  | mono {s : ℕ} {L : List ℕ} : Run s L → Run (s + 1) L
  | two {s a b : ℕ} {r : List ℕ} (o ka kb : Bool) :
      Run s (opv o a b :: kept ka a (kept kb b r)) → Run (s + 1) (a :: b :: r)
  | one {s a w : ℕ} {r : List ℕ} (ka : Bool) : (w = a ∨ w = 0) →
      Run s (w :: kept ka a r) → Run (s + 1) (a :: r)
  | const {s w : ℕ} {r : List ℕ} : (w = 0 ∨ w = ALLV) → Run s (w :: r) → Run (s + 1) r

theorem mem_kept {k : Bool} {x v : ℕ} {xs : List ℕ} (h : v ∈ kept k x xs) : v = x ∨ v ∈ xs := by
  cases k
  · exact Or.inr h
  · simpa [kept] using h

theorem len_kept (k : Bool) (x : ℕ) (xs : List ℕ) : xs.length ≤ (kept k x xs).length := by
  cases k <;> simp [kept]

theorem bit_zero (i : ℕ) : (0 : ℕ).testBit i = false := Nat.zero_testBit i

theorem allv_bit : ∀ m < 6, ALLV.testBit (10 + m) = true := by decide

theorem Run.inv {s : ℕ} {L : List ℕ} (h : Run s L) : L.length ≤ s + 1 ∧ Cov L := by
  induction h with
  | done s => exact ⟨by simp, cov_T⟩
  | perm p _ ih =>
    refine ⟨p.length_eq ▸ ih.1, fun m hm e he => ?_⟩
    obtain ⟨v, hv, h1, h2⟩ := ih.2 m hm e he
    exact ⟨v, p.subset hv, h1, h2⟩
  | mono _ ih => exact ⟨by omega, ih.2⟩
  | @two s a b r o ka kb _ ih =>
    obtain ⟨hl, hc⟩ := ih
    refine ⟨?_, fun m hm e he => ?_⟩
    · have h1 := len_kept ka a (kept kb b r)
      have h2 := len_kept kb b r
      simp only [List.length_cons] at hl ⊢
      omega
    · obtain ⟨v, hv, h1, h2⟩ := hc m hm e he
      rcases List.mem_cons.1 hv with rfl | hv
      · cases o
        · simp only [opv, Bool.false_eq_true, if_false, Nat.testBit_or, Bool.or_eq_false_iff,
            Bool.or_eq_true] at h1 h2
          rcases h2 with h2 | h2
          · exact ⟨a, by simp, h1.1, h2⟩
          · exact ⟨b, by simp, h1.2, h2⟩
        · simp only [opv, if_true, Nat.testBit_and, Bool.and_eq_false_iff, Bool.and_eq_true] at h1 h2
          rcases h1 with h1 | h1
          · exact ⟨a, by simp, h1, h2.1⟩
          · exact ⟨b, by simp, h1, h2.2⟩
      · rcases mem_kept hv with rfl | hv
        · exact ⟨v, by simp, h1, h2⟩
        · rcases mem_kept hv with rfl | hv
          · exact ⟨v, by simp, h1, h2⟩
          · exact ⟨v, by simp [hv], h1, h2⟩
  | @one s a w r ka hw _ ih =>
    obtain ⟨hl, hc⟩ := ih
    refine ⟨?_, fun m hm e he => ?_⟩
    · have h1 := len_kept ka a r
      simp only [List.length_cons] at hl ⊢
      omega
    · obtain ⟨v, hv, h1, h2⟩ := hc m hm e he
      rcases List.mem_cons.1 hv with rfl | hv
      · rcases hw with rfl | rfl
        · exact ⟨v, by simp, h1, h2⟩
        · rw [bit_zero] at h2
          exact absurd h2 (by simp)
      · rcases mem_kept hv with rfl | hv
        · exact ⟨v, by simp, h1, h2⟩
        · exact ⟨v, by simp [hv], h1, h2⟩
  | @const s w r hw _ ih =>
    obtain ⟨hl, hc⟩ := ih
    refine ⟨?_, fun m hm e he => ?_⟩
    · simp only [List.length_cons] at hl
      omega
    · obtain ⟨v, hv, h1, h2⟩ := hc m hm e he
      rcases List.mem_cons.1 hv with rfl | hv
      · rcases hw with rfl | rfl
        · rw [bit_zero] at h2
          exact absurd h2 (by simp)
        · rw [allv_bit m hm] at h1
          exact absurd h1 (by simp)
      · exact ⟨v, hv, h1, h2⟩

theorem Run.passOk {s : ℕ} {L : List ℕ} (h : Run s L) {s' : ℕ} (hs : s ≤ s') :
    passes s' L = true := by
  obtain ⟨hl, hc⟩ := h.inv
  unfold passes
  rw [Bool.and_eq_true, Nat.ble_eq]
  exact ⟨by omega, covB_of_cov hc⟩

/-! ## Rotation -/

theorem rot_and_dummy : True := trivial

def src (i : ℕ) : ℕ := if i = 15 then 15 else if i % 5 = 0 then i + 4 else i - 1

theorem bm1 (k : ℕ) (hk : k < 20) : Nat.testBit 15855 k = decide (k % 5 ≠ 4 ∧ k < 14) := by
  interval_cases k <;> decide

theorem bm2 (k : ℕ) (hk : k < 20) : Nat.testBit 16912 k = decide (k % 5 = 4 ∧ k < 15) := by
  interval_cases k <;> decide

theorem bm3 (k : ℕ) (hk : k < 20) : Nat.testBit 32768 k = decide (k = 15) := by
  interval_cases k <;> decide

theorem rot_bit (v i : ℕ) : (rot v).testBit i = (decide (i < 16) && v.testBit (src i)) := by
  simp only [rot, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  rcases Nat.lt_or_ge i 16 with h | h
  · interval_cases i <;> simp [src, bm1, bm2, bm3]
  · have e1 : (15855 : ℕ).testBit (i - 1) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 15 ≤ i - 1 by omega)))
    have e2 : (16912 : ℕ).testBit (4 + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 16 ≤ 4 + i by omega)))
    have e3 : (32768 : ℕ).testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 16 ≤ i by omega)))
    have h' : ¬ i < 16 := by omega
    simp [e1, e2, e3, h']

theorem rot_and (a b : ℕ) : rot (a &&& b) = rot a &&& rot b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, rot_bit, rot_bit, rot_bit, Nat.testBit_and]
  cases decide (i < 16) <;> simp

theorem rot_or (a b : ℕ) : rot (a ||| b) = rot a ||| rot b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, rot_bit, rot_bit, rot_bit, Nat.testBit_or]
  cases decide (i < 16) <;> simp

theorem rot_zero : rot 0 = 0 := by decide
theorem rot_T : rot T = T := by decide
theorem rot_allv : rot ALLV = ALLV := by decide

/-! ## Iterated rotation -/

def rotN (j : ℕ) (L : List ℕ) : List ℕ := L.map (Nat.iterate rot j)

theorem itr_and (j : ℕ) : ∀ a b : ℕ, rot^[j] (a &&& b) = rot^[j] a &&& rot^[j] b := by
  induction j with
  | zero => intro a b; rfl
  | succ j ih => intro a b; rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, rot_and, ih]

theorem itr_or (j : ℕ) : ∀ a b : ℕ, rot^[j] (a ||| b) = rot^[j] a ||| rot^[j] b := by
  induction j with
  | zero => intro a b; rfl
  | succ j ih => intro a b; rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, rot_or, ih]

theorem itr_fix {c : ℕ} (hc : rot c = c) (j : ℕ) : rot^[j] c = c :=
  Function.iterate_fixed hc j

theorem itr_opv (j : ℕ) (o : Bool) (a b : ℕ) : rot^[j] (opv o a b) = opv o (rot^[j] a) (rot^[j] b) := by
  cases o
  · exact itr_or j a b
  · exact itr_and j a b

theorem map_kept (f : ℕ → ℕ) (k : Bool) (x : ℕ) (xs : List ℕ) :
    (kept k x xs).map f = kept k (f x) (xs.map f) := by
  cases k <;> simp [kept]

theorem Run.rotAll {s : ℕ} {L : List ℕ} (h : Run s L) (j : ℕ) : Run s (rotN j L) := by
  induction h with
  | done s =>
    have : rotN j [T] = [T] := by
      show [rot^[j] T] = [T]
      rw [itr_fix rot_T]
    rw [this]
    exact Run.done s
  | perm p _ ih => exact Run.perm (p.map _) ih
  | mono _ ih => exact Run.mono ih
  | @two s a b r o ka kb _ ih =>
    simp only [rotN, List.map_cons, map_kept, itr_opv] at ih ⊢
    exact Run.two o ka kb ih
  | @one s a w r ka hw _ ih =>
    simp only [rotN, List.map_cons, map_kept] at ih ⊢
    refine Run.one ka ?_ ih
    rcases hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (itr_fix rot_zero j)
  | @const s w r hw _ ih =>
    simp only [rotN, List.map_cons] at ih ⊢
    refine Run.const ?_ ih
    rcases hw with rfl | rfl
    · exact Or.inl (itr_fix rot_zero j)
    · exact Or.inr (itr_fix rot_allv j)

theorem rotN_perm (j : ℕ) {L₁ L₂ : List ℕ} (p : L₁.Perm L₂) : (rotN j L₁).Perm (rotN j L₂) :=
  p.map _

theorem rotN_add (i j : ℕ) (L : List ℕ) : rotN i (rotN j L) = rotN (i + j) L := by
  simp only [rotN, List.map_map]
  congr 1
  funext x
  simp [Function.iterate_add_apply]

theorem rotN_succ (j : ℕ) (L : List ℕ) : rotN j (L.map rot) = rotN (j + 1) L := by
  have := rotN_add j 1 L
  simpa [rotN] using this

/-! ## Sorting -/

theorem srt_perm {L₁ L₂ : List ℕ} (p : L₁.Perm L₂) : srt L₁ = srt L₂ := by
  apply List.Perm.eq_of_sortedLE
  · exact List.sortedLE_iff_pairwise.2 (List.pairwise_insertionSort _ _)
  · exact List.sortedLE_iff_pairwise.2 (List.pairwise_insertionSort _ _)
  · exact ((List.perm_insertionSort _ L₁).trans p).trans (List.perm_insertionSort _ L₂).symm

theorem srt_perm_self (L : List ℕ) : (srt L).Perm L := List.perm_insertionSort _ L

/-! ## Trees -/

inductive Mem : Tr → List ℕ → ℕ → Prop
  | here (l : Tr) (k : List ℕ) (v : ℕ) (r : Tr) : Mem (Tr.N l k v r) k v
  | left {l : Tr} {k k' : List ℕ} {v v' : ℕ} (r : Tr) : Mem l k' v' → Mem (Tr.N l k v r) k' v'
  | right (l : Tr) {r : Tr} {k k' : List ℕ} {v v' : ℕ} : Mem r k' v' → Mem (Tr.N l k v r) k' v'

theorem cmpL_eq : ∀ {a b : List ℕ}, cmpL a b = Ordering.eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cmpL] at h
  | _ :: _, [], h => by simp [cmpL] at h
  | x :: xs, y :: ys, h => by
    unfold cmpL at h
    by_cases h1 : Nat.blt x y = true
    · rw [if_pos h1] at h; cases h
    · rw [if_neg h1] at h
      by_cases h2 : Nat.blt y x = true
      · rw [if_pos h2] at h; cases h
      · rw [if_neg h2] at h
        rw [Nat.blt_eq] at h1 h2
        rw [cmpL_eq h, show x = y by omega]

theorem look_sound : ∀ {t : Tr} {x : List ℕ} {s : ℕ}, look t x s = true → ∃ v, Mem t x v ∧ s ≤ v
  | Tr.E, _, _, h => by simp [look] at h
  | Tr.N l k v r, x, s, h => by
    unfold look at h
    split at h
    · obtain ⟨w, hw, hs⟩ := look_sound h
      exact ⟨w, Mem.left r hw, hs⟩
    · obtain ⟨w, hw, hs⟩ := look_sound h
      exact ⟨w, Mem.right l hw, hs⟩
    · rename_i hc
      rw [cmpL_eq hc]
      exact ⟨v, Mem.here l k v r, Nat.le_of_ble_eq_true h⟩

theorem lookR_sound (t : Tr) (s : ℕ) : ∀ (k : ℕ) (L : List ℕ), lookR t s k L = true →
    ∃ j, ∃ v, Mem t (srt (rotN j L)) v ∧ s ≤ v
  | 0, _, h => by simp [lookR] at h
  | k + 1, L, h => by
    unfold lookR at h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨v, hv, hs⟩ := look_sound h
      exact ⟨0, v, by simpa [rotN] using hv, hs⟩
    · obtain ⟨j, v, hv, hs⟩ := lookR_sound t s k _ h
      rw [rotN_succ] at hv
      exact ⟨j + 1, v, hv, hs⟩

theorem allE_sound (t : Tr) : ∀ {t' : Tr} {K : List ℕ} {v : ℕ}, allE t t' = true → Mem t' K v →
    chkE t K v = true
  | Tr.E, _, _, _, hm => by cases hm
  | Tr.N l k w r, K, v, h, hm => by
    unfold allE at h
    simp only [Bool.and_eq_true] at h
    cases hm with
    | here => exact h.1.1
    | left _ hm => exact allE_sound t h.1.2 hm
    | right _ hm => exact allE_sound t h.2 hm

/-! ## Children -/

theorem picks_sound : ∀ {L : List ℕ} {x : ℕ} {r : List ℕ}, (x, r) ∈ picks L → L.Perm (x :: r)
  | [], _, _, h => by simp [picks] at h
  | y :: ys, x, r, h => by
    simp only [picks, List.mem_cons, Prod.mk.injEq, List.mem_map] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨⟨a, b⟩, hq, he⟩
    · exact List.Perm.refl _
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ((picks_sound hq).cons y).trans (List.Perm.swap _ _ _)

theorem picks_complete : ∀ {L : List ℕ} {x : ℕ}, x ∈ L → ∃ r, (x, r) ∈ picks L
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨ys, by simp [picks]⟩
    · obtain ⟨r, hr⟩ := picks_complete h
      exact ⟨y :: r, by simp only [picks, List.mem_cons, List.mem_map]; exact Or.inr ⟨(x, r), hr, rfl⟩⟩

theorem pick_perm {L r : List ℕ} {x : ℕ} (hL : L.Perm (x :: r)) :
    ∃ r', (x, r') ∈ picks L ∧ r'.Perm r := by
  obtain ⟨r', hr'⟩ := picks_complete (hL.symm.subset (List.mem_cons_self ..))
  exact ⟨r', hr', ((picks_sound hr').symm.trans hL).cons_inv⟩

theorem pairs_complete : ∀ {K : List ℕ} {a b : ℕ} {r : List ℕ}, K.Perm (a :: b :: r) →
    ∃ q ∈ pairsOf K, ((q.1 = a ∧ q.2.1 = b) ∨ (q.1 = b ∧ q.2.1 = a)) ∧ q.2.2.Perm r
  | [], _, _, _, h => by have := h.length_eq; simp at this
  | x :: xs, a, b, r, h => by
    by_cases hxa : x = a
    · subst hxa
      have h1 : xs.Perm (b :: r) := h.cons_inv
      obtain ⟨r', hr', hp⟩ := pick_perm h1
      exact ⟨(x, b, r'), by simp only [pairsOf, List.mem_append, List.mem_map]; exact Or.inl ⟨(b, r'), hr', rfl⟩,
        Or.inl ⟨rfl, rfl⟩, hp⟩
    · by_cases hxb : x = b
      · subst hxb
        have h1 : xs.Perm (a :: r) := (h.trans (List.Perm.swap _ _ _)).cons_inv
        obtain ⟨r', hr', hp⟩ := pick_perm h1
        exact ⟨(x, a, r'), by simp only [pairsOf, List.mem_append, List.mem_map]; exact Or.inl ⟨(a, r'), hr', rfl⟩,
          Or.inr ⟨rfl, rfl⟩, hp⟩
      · have hxr : x ∈ r := by
          have := h.subset (List.mem_cons_self ..)
          simp only [List.mem_cons] at this
          rcases this with h' | h' | h'
          · exact absurd h' hxa
          · exact absurd h' hxb
          · exact h'
        have hr := List.perm_cons_erase hxr
        have h2 : xs.Perm (a :: b :: r.erase x) := by
          apply List.Perm.cons_inv (a := x)
          refine h.trans ?_
          refine ((hr.cons b).cons a).trans ?_
          exact ((List.Perm.swap _ _ _).cons a).trans (List.Perm.swap _ _ _)
        obtain ⟨q, hq, hab, hp⟩ := pairs_complete h2
        refine ⟨(q.1, q.2.1, x :: q.2.2), ?_, hab, ?_⟩
        · simp only [pairsOf, List.mem_append, List.mem_map]
          exact Or.inr ⟨q, hq, rfl⟩
        · exact (hp.cons x).trans hr.symm

theorem kept_swap (ka kb : Bool) (a b : ℕ) (r : List ℕ) :
    (kept ka a (kept kb b r)).Perm (kept kb b (kept ka a r)) := by
  cases ka <;> cases kb <;> simp [kept] <;> exact List.Perm.swap _ _ _

theorem kept_perm (k : Bool) (x : ℕ) {l₁ l₂ : List ℕ} (p : l₁.Perm l₂) :
    (kept k x l₁).Perm (kept k x l₂) := by
  cases k
  · exact p
  · exact p.cons x

theorem opv_comm (o : Bool) (a b : ℕ) : opv o a b = opv o b a := by
  cases o
  · exact Nat.lor_comm a b
  · exact Nat.land_comm a b

def Child (P c : List ℕ) : Prop :=
  (∃ a b r o ka kb, P = a :: b :: r ∧ c = opv o a b :: kept ka a (kept kb b r)) ∨
  (∃ a r w ka, P = a :: r ∧ (w = 0 ∨ (w = a ∧ ka = true)) ∧ c = w :: kept ka a r) ∨
  (∃ w, (w = 0 ∨ w = ALLV) ∧ c = w :: P)

theorem child_rot {P c : List ℕ} (h : Child P c) (j : ℕ) : Child (rotN j P) (rotN j c) := by
  rcases h with ⟨a, b, r, o, ka, kb, rfl, rfl⟩ | ⟨a, r, w, ka, rfl, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · left
    refine ⟨rot^[j] a, rot^[j] b, rotN j r, o, ka, kb, rfl, ?_⟩
    simp [rotN, map_kept, itr_opv]
  · right; left
    refine ⟨rot^[j] a, rotN j r, rot^[j] w, ka, rfl, ?_, ?_⟩
    · rcases hw with rfl | ⟨rfl, rfl⟩
      · exact Or.inl (itr_fix rot_zero j)
      · exact Or.inr ⟨rfl, rfl⟩
    · simp [rotN, map_kept]
  · right; right
    refine ⟨rot^[j] w, ?_, ?_⟩
    · rcases hw with rfl | rfl
      · exact Or.inl (itr_fix rot_zero j)
      · exact Or.inr (itr_fix rot_allv j)
    · simp [rotN]

theorem child_perm {P c K : List ℕ} (h : Child P c) (hK : K.Perm P) :
    ∃ c' ∈ children K, c'.Perm c := by
  rcases h with ⟨a, b, r, o, ka, kb, rfl, rfl⟩ | ⟨a, r, w, ka, rfl, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · obtain ⟨q, hq, hab, hp⟩ := pairs_complete hK
    have hmem : ∀ o' ka' kb', opv o' q.1 q.2.1 :: kept ka' q.1 (kept kb' q.2.1 q.2.2) ∈ children K := by
      intro o' ka' kb'
      unfold children
      simp only [List.mem_append]
      left; left
      rw [List.mem_flatMap]
      refine ⟨q, hq, ?_⟩
      unfold twoCh
      cases o' <;> cases ka' <;> cases kb' <;> simp
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨_, hmem o ka kb, ?_⟩
      rw [h1, h2]
      exact (kept_perm ka a (kept_perm kb b hp)).cons _
    · refine ⟨_, hmem o kb ka, ?_⟩
      rw [h1, h2, opv_comm]
      exact ((kept_perm kb b (kept_perm ka a hp)).trans (kept_swap kb ka b a r)).cons _
  · obtain ⟨r', hr', hp⟩ := pick_perm hK
    have hmem : ∀ ch ∈ [a :: a :: r', 0 :: r', 0 :: a :: r'], ch ∈ children K := by
      intro ch hch
      unfold children
      simp only [List.mem_append]
      left; right
      rw [List.mem_flatMap]
      exact ⟨(a, r'), hr', hch⟩
    rcases hw with rfl | ⟨rfl, rfl⟩
    · cases ka
      · exact ⟨_, hmem (0 :: r') (by simp), hp.cons 0⟩
      · exact ⟨_, hmem (0 :: a :: r') (by simp), (hp.cons a).cons 0⟩
    · exact ⟨_, hmem (w :: w :: r') (by simp), (hp.cons w).cons w⟩
  · refine ⟨w :: K, ?_, hK.cons w⟩
    unfold children
    simp only [List.mem_append]
    right
    rcases hw with rfl | rfl <;> simp

/-! ## The certificate argument -/

theorem cert (t : Tr) (ht : allE t t = true) {s : ℕ} {L : List ℕ} (h : Run s L) :
    ∀ j v, Mem t (srt (rotN j L)) v → s ≤ v → False := by
  -- generic step: parent P at level s+1, child c with Run s c
  have step : ∀ {s : ℕ} {P c : List ℕ}, Child P c → Run s c →
      (∀ j v, Mem t (srt (rotN j c)) v → s ≤ v → False) →
      ∀ j v, Mem t (srt (rotN j P)) v → s + 1 ≤ v → False := by
    intro s P c hch hc ih j v hm hv
    have hK := allE_sound t ht hm
    unfold chkE at hK
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hK
    obtain ⟨c', hc'm, hc'p⟩ := child_perm (child_rot hch j) (srt_perm_self (rotN j P))
    have hrun : Run s c' := Run.perm hc'p.symm (hc.rotAll j)
    rcases hK.2 c' hc'm with hf | hl
    · rw [hrun.passOk (show s ≤ v - 1 by omega)] at hf
      cases hf
    · obtain ⟨i, w, hw, hs⟩ := lookR_sound t (v - 1) 5 c' hl
      have e : srt (rotN i c') = srt (rotN (i + j) c) := by
        rw [← rotN_add]
        exact srt_perm (rotN_perm i hc'p)
      rw [e] at hw
      exact ih (i + j) w hw (by omega)
  induction h with
  | done s =>
    intro j v hm _
    have e : srt (rotN j [T]) = [T] := by
      show srt [rot^[j] T] = [T]
      rw [itr_fix rot_T]
      rfl
    rw [e] at hm
    have hK := allE_sound t ht hm
    unfold chkE at hK
    simp only [Bool.and_eq_true] at hK
    have : cmpL [T] [T] = Ordering.eq := by decide
    rw [this] at hK
    simp at hK
  | perm p _ ih =>
    intro j v hm hv
    rw [← srt_perm (rotN_perm j p)] at hm
    exact ih j v hm hv
  | mono _ ih =>
    intro j v hm hv
    exact ih j v hm (by omega)
  | @two s a b r o ka kb hc ih =>
    exact step (Or.inl ⟨a, b, r, o, ka, kb, rfl, rfl⟩) hc ih
  | @one s a w r ka hw hc ih =>
    by_cases htriv : w = a ∧ ka = false
    · obtain ⟨rfl, rfl⟩ := htriv
      intro j v hm hv
      exact ih j v hm (by omega)
    · refine step (Or.inr (Or.inl ⟨a, r, w, ka, rfl, ?_, rfl⟩)) hc ih
      rcases hw with rfl | rfl
      · cases ka
        · exact absurd ⟨rfl, rfl⟩ htriv
        · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl rfl
  | @const s w r hw hc ih =>
    exact step (Or.inr (Or.inr ⟨w, hw, rfl⟩)) hc ih

/-! ## Points and encoding -/

open PEqualNP.CircuitLowerBounds

def ptE (a b : ℕ) : Fin 6 → Bool := fun i => decide (i.val = a ∨ i.val = b)

def pts : List (Fin 6 → Bool) :=
  [ptE 0 1, ptE 1 2, ptE 2 3, ptE 3 4, ptE 4 0, ptE 0 5, ptE 1 5, ptE 2 5, ptE 3 5, ptE 4 5,
   ptE 0 2, ptE 1 3, ptE 2 4, ptE 3 0, ptE 4 1, ptE 5 5]

def encL (g : (Fin 6 → Bool) → Bool) : List (Fin 6 → Bool) → ℕ
  | [] => 0
  | p :: ps => Nat.bit (g p) (encL g ps)

theorem encL_and (g h : (Fin 6 → Bool) → Bool) : ∀ l : List (Fin 6 → Bool),
    encL (fun x => g x && h x) l = encL g l &&& encL h l
  | [] => by simp [encL]
  | p :: ps => by simp only [encL, Nat.land_bit, encL_and g h ps]

theorem encL_or (g h : (Fin 6 → Bool) → Bool) : ∀ l : List (Fin 6 → Bool),
    encL (fun x => g x || h x) l = encL g l ||| encL h l
  | [] => by simp [encL]
  | p :: ps => by simp only [encL, Nat.lor_bit, encL_or g h ps]

theorem encL_false : ∀ l : List (Fin 6 → Bool), encL (fun _ => false) l = 0
  | [] => rfl
  | p :: ps => by simp only [encL, encL_false ps]; rfl

theorem encL_true : encL (fun _ => true) pts = ALLV := by decide

def Xv (i : ℕ) : ℕ := encL (fun x => if h : i < 6 then x ⟨i, h⟩ else false) pts

def XL : List ℕ := (List.range 6).map Xv

/-! ## Wires -/

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem foldl_pre : ∀ (gs : List Gate) (x : List Bool), ∃ ys,
    gs.foldl stp x = x ++ ys ∧ ys.length = gs.length
  | [], x => ⟨[], by simp⟩
  | g :: gs, x => by
    obtain ⟨ys, h1, h2⟩ := foldl_pre gs (stp x g)
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: ys, ?_, by simp [h2]⟩
    rw [List.foldl_cons, h1]
    simp [stp]

theorem foldl_gate (gs : List Gate) (x : List Bool) (j : ℕ) (g : Gate) (hg : gs[j]? = some g) :
    (gs.foldl stp x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < x.length + j then (gs.foldl stp x).getD i false
        else false) := by
  have hj : j < gs.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  have hsplit : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
    rw [List.getElem?_eq_getElem hj] at hg
    cases hg
    rfl
  obtain ⟨ys, h1, h2⟩ := foldl_pre (gs.take j) x
  have hlen : (x ++ ys).length = x.length + j := by
    simp [h2, List.length_take]
    omega
  generalize hw : x ++ ys = w at h1 hlen
  obtain ⟨zs, h3, _⟩ := foldl_pre (gs.drop (j + 1)) (stp w g)
  generalize hv : g.op.eval (g.inputs.map fun i => w.getD i false) = v
  have hfin : gs.foldl stp x = w ++ ([v] ++ zs) := by
    rw [hsplit, List.foldl_append, h1, List.foldl_cons, h3, ← hv]
    simp [stp]
  rw [hfin, ← hlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  show v = _
  rw [← hv]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w.length
  · rw [if_pos hi, List.getD_append _ _ _ _ hi]
  · rw [if_neg hi]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]
    rfl

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length := by
  obtain ⟨ys, h1, h2⟩ := foldl_pre C.gates x
  rw [wires_eq, h1]
  simp [h2]

def W (C : Circuit) (i : ℕ) (x : Fin 6 → Bool) : Bool := (C.wires (List.ofFn x)).getD i false

theorem W_input (C : Circuit) (i : ℕ) (hi : i < 6) (x : Fin 6 → Bool) : W C i x = x ⟨i, hi⟩ := by
  obtain ⟨ys, h1, _⟩ := foldl_pre C.gates (List.ofFn x)
  rw [W, wires_eq, h1, List.getD_append _ _ _ _ (by simp [hi])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

theorem W_gate (C : Circuit) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (x : Fin 6 → Bool) :
    W C (6 + j) x = g.op.eval (g.inputs.map fun i => if i < 6 + j then W C i x else false) := by
  have := foldl_gate C.gates (List.ofFn x) j g hg
  simp only [List.length_ofFn] at this
  simp only [W, wires_eq]
  exact this

def val (C : Circuit) (i : ℕ) : ℕ := encL (W C i) pts

theorem val_input (C : Circuit) (i : ℕ) (hi : i < 6) : val C i = Xv i := by
  unfold val Xv
  congr 1
  funext x
  rw [W_input C i hi, dif_pos hi]

theorem enc_rd (C : Circuit) (t i : ℕ) :
    encL (fun x => if i < 6 + t then W C i x else false) pts = if i < 6 + t then val C i else 0 := by
  by_cases h : i < 6 + t
  · simp only [h, if_true]; rfl
  · simp only [h, if_false]; exact encL_false _

theorem val_gate (C : Circuit) (t : ℕ) (g : Gate) (hg : C.gates[t]? = some g) :
    val C (6 + t) = encL (fun x => g.op.eval (g.inputs.map fun i => if i < 6 + t then W C i x else false)) pts := by
  unfold val
  congr 1
  funext x
  exact W_gate C t g hg x

/-! ## Needed wires -/

def gIn (C : Circuit) (t : ℕ) : Finset ℕ :=
  match C.gates[t]? with
  | some g => (g.inputs.filter (fun i => decide (i < 6 + t))).toFinset
  | none => ∅

theorem mem_gIn {C : Circuit} {t : ℕ} {g : Gate} (hg : C.gates[t]? = some g) (w : ℕ) :
    w ∈ gIn C t ↔ w ∈ g.inputs ∧ w < 6 + t := by
  unfold gIn
  rw [hg]
  simp

def need (C : Circuit) : ℕ → Finset ℕ
  | 0 => {C.output}
  | d + 1 =>
    if 6 + (C.gates.length - (d + 1)) ∈ need C d then
      (need C d).erase (6 + (C.gates.length - (d + 1))) ∪ gIn C (C.gates.length - (d + 1))
    else need C d

noncomputable def St (C : Circuit) (d : ℕ) : List ℕ := (need C d).toList.map (val C)

theorem need_bound (C : Circuit) (ho : C.output < 6 + C.gates.length) :
    ∀ d, d ≤ C.gates.length → ∀ w ∈ need C d, w < 6 + (C.gates.length - d)
  | 0, _, w, hw => by
    simp only [need, Finset.mem_singleton] at hw
    omega
  | d + 1, hd, w, hw => by
    have ih := need_bound C ho d (by omega)
    unfold need at hw
    split at hw
    · rw [Finset.mem_union, Finset.mem_erase] at hw
      rcases hw with ⟨h1, h2⟩ | h
      · have := ih w h2
        omega
      · unfold gIn at h
        split at h
        · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at h
          omega
        · simp at h
    · rename_i hn
      have := ih w hw
      have : w ≠ 6 + (C.gates.length - (d + 1)) := fun e => hn (e ▸ hw)
      omega

theorem mem_kept_iff {k : Bool} {x v : ℕ} {xs : List ℕ} :
    v ∈ kept k x xs ↔ (k = true ∧ v = x) ∨ v ∈ xs := by
  cases k <;> simp [kept]

theorem toL_perm {A : Finset ℕ} {L : List ℕ} (hL : L.Nodup) (h : ∀ w, w ∈ A ↔ w ∈ L) :
    A.toList.Perm L :=
  (List.perm_ext_iff_of_nodup (Finset.nodup_toList A) hL).2 (fun w => by rw [Finset.mem_toList]; exact h w)

theorem H0 {d : ℕ} {A I : Finset ℕ} {f : ℕ → ℕ} {w : ℕ} (hI : ∀ x, x ∉ I) (hw : w = 0 ∨ w = ALLV)
    (h : Run d (w :: A.toList.map f)) : Run (d + 1) ((A ∪ I).toList.map f) := by
  have e : A ∪ I = A := by
    ext x
    simp [hI x]
  rw [e]
  exact Run.const hw h

theorem H1 {d : ℕ} {A I : Finset ℕ} {f : ℕ → ℕ} {a w : ℕ} (hI : ∀ x, x ∈ I ↔ x = a)
    (hw : w = f a ∨ w = 0) (h : Run d (w :: A.toList.map f)) :
    Run (d + 1) ((A ∪ I).toList.map f) := by
  have hw' : w = f a ∨ w = 0 := hw
  by_cases ha : a ∈ A
  · have p1 : A.toList.Perm (a :: (A.erase a).toList) := by
      apply toL_perm (List.nodup_cons.2 ⟨by simp, Finset.nodup_toList _⟩)
      intro x
      simp only [List.mem_cons, Finset.mem_toList, Finset.mem_erase]
      constructor
      · intro hx
        by_cases e : x = a
        · exact Or.inl e
        · exact Or.inr ⟨e, hx⟩
      · rintro (rfl | ⟨_, hx⟩)
        · exact ha
        · exact hx
    have p2 : (A ∪ I).toList.Perm (a :: (A.erase a).toList) := by
      refine List.Perm.trans ?_ p1
      have e : A ∪ I = A := by
        ext x
        rw [Finset.mem_union, hI]
        constructor
        · rintro (h | rfl)
          · exact h
          · exact ha
        · exact Or.inl
      rw [e]
    have q : Run d (w :: kept true (f a) ((A.erase a).toList.map f)) := by
      refine Run.perm ?_ h
      have := (p1.map f).cons w
      simpa [kept] using this
    have r := Run.one (r := (A.erase a).toList.map f) true (hw'.imp id id) q
    exact Run.perm ((p2.map f).symm) (by simpa using r)
  · have p2 : (A ∪ I).toList.Perm (a :: A.toList) := by
      apply toL_perm (List.nodup_cons.2 ⟨by simp [ha], Finset.nodup_toList _⟩)
      intro x
      rw [Finset.mem_union, hI, List.mem_cons, Finset.mem_toList]
      tauto
    have r := Run.one (r := A.toList.map f) false hw' (by simpa [kept] using h)
    exact Run.perm ((p2.map f).symm) (by simpa using r)

theorem H2 {d : ℕ} {A I : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ} (o : Bool) (hab : a ≠ b)
    (hI : ∀ x, x ∈ I ↔ x = a ∨ x = b)
    (h : Run d (opv o (f a) (f b) :: A.toList.map f)) : Run (d + 1) ((A ∪ I).toList.map f) := by
  let R := (A.erase a).erase b
  have hR : ∀ x, x ∈ R ↔ x ∈ A ∧ x ≠ a ∧ x ≠ b := by
    intro x
    simp only [R, Finset.mem_erase]
    tauto
  have nR : R.toList.Nodup := Finset.nodup_toList _
  have p1 : A.toList.Perm (kept (decide (a ∈ A)) a (kept (decide (b ∈ A)) b R.toList)) := by
    have n1 : (kept (decide (b ∈ A)) b R.toList).Nodup := by
      cases hb : decide (b ∈ A)
      · exact nR
      · exact List.nodup_cons.2 ⟨by rw [Finset.mem_toList, hR]; tauto, nR⟩
    have n2 : (kept (decide (a ∈ A)) a (kept (decide (b ∈ A)) b R.toList)).Nodup := by
      cases ha : decide (a ∈ A)
      · exact n1
      · refine List.nodup_cons.2 ⟨?_, n1⟩
        intro hm
        rcases mem_kept hm with e | hm
        · exact hab e
        · rw [Finset.mem_toList, hR] at hm
          exact hm.2.1 rfl
    apply toL_perm n2
    intro x
    simp only [mem_kept_iff, decide_eq_true_eq, Finset.mem_toList, hR]
    constructor
    · intro hx
      by_cases e1 : x = a
      · exact Or.inl ⟨e1 ▸ hx, e1⟩
      by_cases e2 : x = b
      · exact Or.inr (Or.inl ⟨e2 ▸ hx, e2⟩)
      exact Or.inr (Or.inr ⟨hx, e1, e2⟩)
    · rintro (⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, _⟩) <;> exact h1
  have p2 : (A ∪ I).toList.Perm (a :: b :: R.toList) := by
    have hn : (a :: b :: R.toList).Nodup := by
      refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, nR⟩⟩
      · simp only [List.mem_cons, Finset.mem_toList, hR]
        tauto
      · simp only [Finset.mem_toList, hR]
        tauto
    apply toL_perm hn
    intro x
    simp only [Finset.mem_union, hI, List.mem_cons, Finset.mem_toList, hR]
    tauto
  have q : Run d (opv o (f a) (f b) :: kept (decide (a ∈ A)) (f a)
      (kept (decide (b ∈ A)) (f b) (R.toList.map f))) := by
    refine Run.perm ?_ h
    have := (p1.map f).cons (opv o (f a) (f b))
    simpa [map_kept] using this
  have r := Run.two o _ _ q
  exact Run.perm ((p2.map f).symm) (by simpa using r)

theorem eval_and2 (b1 b2 : Bool) : GateOp.eval GateOp.and [b1, b2] = (b1 && b2) := by
  cases b1 <;> cases b2 <;> rfl
theorem eval_or2 (b1 b2 : Bool) : GateOp.eval GateOp.or [b1, b2] = (b1 || b2) := by
  cases b1 <;> cases b2 <;> rfl
theorem eval_1 (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (b : Bool) :
    GateOp.eval op [b] = b := by
  rcases hop with rfl | rfl <;> cases b <;> rfl

theorem rd_enc (C : Circuit) (t i : ℕ) (hi : i < 6 + t) :
    encL (fun x => if i < 6 + t then W C i x else false) pts = val C i := by
  rw [enc_rd, if_pos hi]

theorem rd_enc0 (C : Circuit) (t i : ℕ) (hi : ¬ i < 6 + t) :
    encL (fun x => if i < 6 + t then W C i x else false) pts = 0 := by
  rw [enc_rd, if_neg hi]

theorem gate_step (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C) {t d : ℕ} {g : Gate}
    (hg : C.gates[t]? = some g) {A : Finset ℕ}
    (h : Run d (val C (6 + t) :: A.toList.map (val C))) :
    Run (d + 1) ((A ∪ gIn C t).toList.map (val C)) := by
  have hmem : g ∈ C.gates := List.mem_of_getElem? hg
  obtain ⟨hop, hlen⟩ := hM g hmem
  have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hop
  have hv := val_gate C t g hg
  have hI := mem_gIn hg
  rcases hin : g.inputs with _ | ⟨i, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
  · rw [hin] at hv hI
    refine H0 (fun x hx => by simp [hI] at hx) ?_ h
    rw [hv]
    rcases hop' with e | e <;> rw [e]
    · right; exact encL_true
    · left; exact encL_false _
  · rw [hin] at hv hI
    simp only [List.map_cons, List.map_nil] at hv
    rw [show (fun x => g.op.eval [if i < 6 + t then W C i x else false]) =
        (fun x => if i < 6 + t then W C i x else false) from funext fun x => eval_1 _ hop' _] at hv
    by_cases hi : i < 6 + t
    · refine H1 (a := i) (fun x => by rw [hI]; simp only [List.mem_singleton]; constructor <;> intro h' <;> [exact h'.1; exact ⟨h', h' ▸ hi⟩]) (Or.inl ?_) h
      rw [hv, rd_enc C t i hi]
    · refine H0 (fun x hx => by rw [hI] at hx; simp only [List.mem_singleton] at hx; exact hi (hx.1 ▸ hx.2)) (Or.inl ?_) h
      rw [hv, rd_enc0 C t i hi]
  · rw [hin] at hv hI
    simp only [List.map_cons, List.map_nil] at hv
    have hv2 : ∃ o, val C (6 + t) = opv o
        (encL (fun x => if i < 6 + t then W C i x else false) pts)
        (encL (fun x => if i2 < 6 + t then W C i2 x else false) pts) := by
      rcases hop' with e | e <;> rw [e] at hv
      · refine ⟨true, ?_⟩
        rw [hv, show (fun x => GateOp.eval GateOp.and [if i < 6 + t then W C i x else false,
            if i2 < 6 + t then W C i2 x else false]) = (fun x => (if i < 6 + t then W C i x else false)
            && (if i2 < 6 + t then W C i2 x else false)) from funext fun x => eval_and2 _ _, encL_and]
        rfl
      · refine ⟨false, ?_⟩
        rw [hv, show (fun x => GateOp.eval GateOp.or [if i < 6 + t then W C i x else false,
            if i2 < 6 + t then W C i2 x else false]) = (fun x => (if i < 6 + t then W C i x else false)
            || (if i2 < 6 + t then W C i2 x else false)) from funext fun x => eval_or2 _ _, encL_or]
        rfl
    obtain ⟨o, ho⟩ := hv2
    by_cases h1 : i < 6 + t <;> by_cases h2 : i2 < 6 + t
    · rw [rd_enc C t i h1, rd_enc C t i2 h2] at ho
      by_cases h12 : i = i2
      · subst h12
        refine H1 (a := i) (fun x => by rw [hI]; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, or_self]; constructor <;> intro h' <;> [exact h'.1; exact ⟨h', h' ▸ h1⟩]) (Or.inl ?_) h
        rw [ho]
        cases o <;> simp [opv]
      · refine H2 o h12 (fun x => ?_) (by rw [← ho]; exact h)
        rw [hI]
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        constructor
        · exact fun h' => h'.1
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, h1⟩
          · exact ⟨Or.inr rfl, h2⟩
    · rw [rd_enc C t i h1, rd_enc0 C t i2 h2] at ho
      refine H1 (a := i) (fun x => ?_) ?_ h
      · rw [hI]
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        constructor
        · rintro ⟨rfl | rfl, hx⟩
          · rfl
          · exact absurd hx h2
        · rintro rfl
          exact ⟨Or.inl rfl, h1⟩
      · rw [ho]
        cases o <;> simp [opv]
    · rw [rd_enc0 C t i h1, rd_enc C t i2 h2] at ho
      refine H1 (a := i2) (fun x => ?_) ?_ h
      · rw [hI]
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        constructor
        · rintro ⟨rfl | rfl, hx⟩
          · exact absurd hx h1
          · rfl
        · rintro rfl
          exact ⟨Or.inr rfl, h2⟩
      · rw [ho]
        cases o <;> simp [opv]
    · rw [rd_enc0 C t i h1, rd_enc0 C t i2 h2] at ho
      refine H0 (fun x hx => ?_) (Or.inl ?_) h
      · rw [hI] at hx
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with ⟨rfl | rfl, hx⟩
        · exact h1 hx
        · exact h2 hx
      · rw [ho]
        cases o <;> simp [opv]
  · rw [hin] at hlen
    simp at hlen

theorem Run.mono_le {s s' : ℕ} {L : List ℕ} (hs : s ≤ s') (h : Run s L) : Run s' L := by
  induction hs with
  | refl => exact h
  | step _ ih => exact Run.mono ih

theorem run_need (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (hT : val C C.output = T) : ∀ d, d ≤ C.gates.length → Run d (St C d)
  | 0, _ => by
    have : St C 0 = [T] := by
      simp [St, need, hT]
    rw [this]
    exact Run.done 0
  | d + 1, hd => by
    have ih := run_need C hM hT d (by omega)
    have ht : C.gates.length - (d + 1) < C.gates.length := by omega
    have hg := List.getElem?_eq_getElem ht
    unfold St need
    split
    · rename_i hin
      set t := C.gates.length - (d + 1)
      have p : (need C d).toList.Perm ((6 + t) :: ((need C d).erase (6 + t)).toList) := by
        conv_lhs => rw [← Finset.insert_erase hin]
        exact Finset.toList_insert (Finset.notMem_erase _ _)
      have h1 : Run d (val C (6 + t) :: ((need C d).erase (6 + t)).toList.map (val C)) := by
        have := Run.perm (p.map (val C)) ih
        simpa using this
      exact gate_step C hM hg h1
    · exact Run.mono ih

def t0 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0, 0, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [0, 1, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [0, 32, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N Tr.E [0, 1024, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [0, 5254, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E)) [0, 5254, 9265, 10508, 11581, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [0, 5254, 9265, 10508, 15758, 18499, 21016, 33760] 7 Tr.E) [0, 5254, 9265, 10508, 18499, 21016, 33760] 8 Tr.E) [0, 5254, 9265, 10508, 18499, 21016, 33760, 33760] 7 (Tr.N Tr.E [0, 5254, 9265, 10508, 18499, 21016, 33760, 38886] 7 Tr.E))) [0, 5254, 9265, 10508, 18499, 21016, 33760, 65535] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [0, 5254, 9265, 10508, 18499, 21016, 33761] 6 Tr.E) [0, 5254, 9265, 10508, 18499, 21017, 33760] 6 Tr.E) [0, 5254, 9265, 10508, 18499, 21018, 33760] 6 (Tr.N Tr.E [0, 5254, 9265, 10508, 18499, 21020, 33760] 6 Tr.E)) [0, 5254, 9265, 10508, 18499, 21048, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [0, 5254, 9265, 10508, 18499, 21080, 33760] 6 Tr.E) [0, 5254, 9265, 10508, 18499, 21144, 33760] 6 Tr.E) [0, 5254, 9265, 10508, 18499, 21272, 33760] 6 (Tr.N Tr.E [1, 1, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E)))) [1, 2, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 4, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1, 4, 5254, 11581, 18499, 21016, 33760] 6 Tr.E) [1, 32, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N Tr.E [1, 48, 5254, 10508, 18499, 21016, 33760] 6 Tr.E)) [1, 64, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [1, 66, 5254, 9265, 10508, 21016, 33760] 6 Tr.E) [1, 128, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1, 256, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N Tr.E [1, 512, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E))) [1, 1024, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 2048, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1, 4096, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1, 5254, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N Tr.E [1, 5254, 5255, 9265, 10508, 18499, 21016, 33760] 7 Tr.E)) [1, 5254, 8192, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 10508, 18499, 21016, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 10509, 18499, 21016, 33760] 7 (Tr.N Tr.E [1, 5254, 9265, 10508, 11581, 18499, 21016, 33760] 7 Tr.E))))) [1, 5254, 9265, 10508, 13495, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 15758, 18499, 21016, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 16384, 18499, 21016, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 18499, 18499, 21016, 33760] 7 (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21016, 21016, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 18499, 21016, 21017, 33760] 7 Tr.E)) [1, 5254, 9265, 10508, 18499, 21016, 22174, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21016, 23131, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 18499, 21016, 23751, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 18499, 21016, 26959, 33760] 7 (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21016, 27763, 33760] 7 Tr.E))) [1, 5254, 9265, 10508, 18499, 21016, 30265, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21016, 31516, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 18499, 21016, 33760] 8 Tr.E) [1, 5254, 9265, 10508, 18499, 21016, 33760, 33760] 7 (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21016, 33760, 33761] 7 Tr.E)) [1, 5254, 9265, 10508, 18499, 21016, 33760, 38886] 7 (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21016, 33760, 42993] 7 Tr.E) [1, 5254, 9265, 10508, 18499, 21016, 33760, 44012] 7 Tr.E) [1, 5254, 9265, 10508, 18499, 21016, 33760, 52195] 7 (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21016, 33760, 54264] 7 Tr.E)))) [1, 5254, 9265, 10508, 18499, 21016, 33760, 65535] 7 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21016, 33761] 7 Tr.E) [1, 5254, 9265, 10508, 18499, 21016, 33762] 6 Tr.E) [1, 5254, 9265, 10508, 18499, 21016, 33764] 6 (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21016, 33768] 6 Tr.E)) [1, 5254, 9265, 10508, 18499, 21016, 33776] 6 (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21017, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 18499, 21017, 33761] 6 Tr.E) [1, 5254, 9265, 10508, 18499, 21018, 33760] 6 (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21020, 33760] 6 Tr.E))) [1, 5254, 9265, 10508, 18499, 21048, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 18499, 21080, 33760] 6 Tr.E) [1, 5254, 9265, 10508, 18499, 21144, 33760] 6 Tr.E) [1, 5254, 9265, 10508, 18499, 21272, 33760] 6 (Tr.N Tr.E [1, 5254, 9265, 10508, 18503, 21016, 33760] 6 Tr.E)) [1, 5254, 9265, 10508, 18507, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 18515, 21016, 33760] 6 Tr.E) [1, 5254, 9265, 10508, 18531, 21016, 33760] 6 Tr.E) [1, 5254, 9265, 10508, 18627, 21016, 33760] 6 (Tr.N Tr.E [1, 5254, 9265, 10508, 18755, 21016, 33760] 6 Tr.E))))))
def t1 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 21016, 26691, 33760] 6 Tr.E) [1, 5254, 9265, 10508, 21016, 26959, 33760] 7 Tr.E) [1, 5254, 9265, 10508, 21016, 26959, 33761] 6 (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10508, 21017, 26959, 33760] 6 Tr.E) [1, 5254, 9265, 10509, 18499, 21016, 33760] 7 Tr.E)) [1, 5254, 9265, 10509, 18499, 21016, 33761] 6 (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10509, 18499, 21017, 33760] 6 Tr.E) [1, 5254, 9265, 10509, 21016, 26959, 33760] 6 Tr.E) [1, 5254, 9265, 10510, 18499, 21016, 33760] 6 (Tr.N Tr.E [1, 5254, 9265, 10524, 18499, 21016, 33760] 6 Tr.E))) [1, 5254, 9265, 10540, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 10572, 18499, 21016, 33760] 6 Tr.E) [1, 5254, 9265, 10574, 21016, 33760] 5 Tr.E) [1, 5254, 9265, 10636, 18499, 21016, 33760] 6 (Tr.N Tr.E [1, 5254, 9265, 11020, 18499, 21016, 33760] 6 Tr.E)) [1, 5254, 9265, 11581, 21016, 26959, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9265, 15758, 21016, 26959, 33760] 6 Tr.E) [1, 5254, 9265, 21016, 26959, 33760, 44012] 6 Tr.E) [1, 5254, 9265, 21016, 26959, 33768] 5 (Tr.N Tr.E [1, 5254, 9267, 10508, 18499, 21016, 33760] 6 Tr.E)))) [1, 5254, 9269, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9273, 10508, 18499, 21016, 33760] 6 Tr.E) [1, 5254, 9273, 21016, 26959, 33760] 5 Tr.E) [1, 5254, 9329, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [1, 5254, 9393, 10508, 18499, 21016, 33760] 6 Tr.E)) [1, 5254, 9521, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 9777, 10508, 18499, 21016, 33760] 6 Tr.E) [1, 5254, 10508, 11313, 18499, 21016, 33760] 6 Tr.E) [1, 5254, 10508, 11581, 18499, 21016, 33760] 7 (Tr.N Tr.E [1, 5254, 10508, 11581, 18499, 21016, 33761] 6 Tr.E))) [1, 5254, 10508, 11581, 18499, 21017, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 10508, 11581, 21016, 26959, 33760] 6 Tr.E) [1, 5254, 10509, 11581, 18499, 21016, 33760] 6 Tr.E) [1, 5254, 10556, 18499, 21016, 33760] 5 (Tr.N Tr.E [1, 5254, 11581, 18499, 21016, 26959, 33760] 6 Tr.E)) [1, 5254, 11581, 18499, 21016, 31516, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 11581, 18499, 21016, 33760, 44012] 6 Tr.E) [1, 5254, 11581, 18499, 21016, 33764] 5 Tr.E) [1, 5254, 11581, 18499, 21020, 33760] 5 (Tr.N Tr.E [1, 5254, 11581, 18503, 21016, 33760] 5 Tr.E))))) [1, 5254, 11581, 21016, 26959, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5254, 11581, 21016, 26959, 33761] 5 Tr.E) [1, 5254, 11581, 21017, 26959, 33760] 5 Tr.E) [1, 5255, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N Tr.E [1, 5255, 9265, 10508, 18499, 21016, 33761] 6 Tr.E) [1, 5255, 9265, 10508, 18499, 21017, 33760] 6 Tr.E)) [1, 5255, 9265, 10508, 21016, 26959, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1, 5255, 9265, 10509, 18499, 21016, 33760] 6 Tr.E) [1, 5255, 10508, 11581, 18499, 21016, 33760] 6 Tr.E) [1, 5255, 11581, 21016, 26959, 33760] 5 (Tr.N Tr.E [1, 5262, 9265, 10508, 18499, 21016, 33760] 6 Tr.E))) [1, 5262, 9265, 21016, 26959, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1, 5270, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1, 5286, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1, 5318, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [1, 5510, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [1, 5766, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [3, 64, 5254, 9265, 10508, 21016, 33760] 6 Tr.E) [3, 5254, 9265, 10508, 13495, 18499, 21016, 33760] 7 Tr.E) [3, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N Tr.E [3, 5254, 9265, 10508, 18499, 21016, 33763] 6 Tr.E)))) [3, 5254, 9265, 10508, 18499, 21019, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [3, 5254, 9265, 10508, 21016, 23131, 33760] 6 Tr.E) [3, 5254, 9265, 10508, 21016, 23751, 33760] 6 Tr.E) [3, 5254, 9265, 10508, 21016, 26959, 33760] 6 (Tr.N Tr.E [3, 5254, 9265, 10508, 21016, 27763, 33760] 6 Tr.E)) [3, 5254, 9265, 10508, 21016, 31991, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [3, 5254, 9265, 10508, 21080, 33760] 5 Tr.E) [3, 5254, 9265, 10511, 18499, 21016, 33760] 6 Tr.E) [3, 5254, 9265, 10572, 21016, 33760] 5 (Tr.N Tr.E [3, 5254, 9267, 10508, 18499, 21016, 33760] 6 Tr.E))) [3, 5254, 9329, 10508, 21016, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [3, 5254, 10508, 11581, 18499, 21016, 33760] 6 Tr.E) [3, 5254, 10508, 13495, 21016, 27763, 33760] 6 Tr.E) [3, 5254, 11581, 21016, 26959, 33760] 5 (Tr.N Tr.E [3, 5255, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [3, 5318, 9265, 10508, 21016, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [3, 9265, 10508, 13495, 21016, 23751, 33760] 6 Tr.E) [3, 9265, 10508, 18499, 21016, 22174, 33760] 6 Tr.E) [3, 9265, 10508, 22174, 23131, 33760] 5 (Tr.N Tr.E [5, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E))))))
def u2 : Tr := Tr.N t0 [1, 5254, 9265, 10508, 19011, 21016, 33760] 6 t1
def t3 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [32, 32, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [32, 64, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [32, 128, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N Tr.E [32, 1024, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [32, 2048, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E)) [32, 4096, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [32, 5254, 5286, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [32, 5254, 8192, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N Tr.E [32, 5254, 9265, 9265, 10508, 18499, 21016, 33760] 7 Tr.E))) [32, 5254, 9265, 10508, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 10540, 18499, 21016, 33760] 7 Tr.E) [32, 5254, 9265, 10508, 11581, 18499, 21016, 33760] 7 Tr.E) [32, 5254, 9265, 10508, 13495, 18499, 21016, 33760] 7 (Tr.N Tr.E [32, 5254, 9265, 10508, 15758, 18499, 21016, 33760] 7 Tr.E)) [32, 5254, 9265, 10508, 16384, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 18499, 21016, 33760] 7 Tr.E) [32, 5254, 9265, 10508, 18499, 18531, 21016, 33760] 7 Tr.E) [32, 5254, 9265, 10508, 18499, 21016, 21016, 33760] 7 (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21016, 21048, 33760] 7 Tr.E)))) [32, 5254, 9265, 10508, 18499, 21016, 22174, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21016, 23131, 33760] 7 Tr.E) [32, 5254, 9265, 10508, 18499, 21016, 23751, 33760] 7 Tr.E) [32, 5254, 9265, 10508, 18499, 21016, 26959, 33760] 7 (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21016, 27763, 33760] 7 Tr.E)) [32, 5254, 9265, 10508, 18499, 21016, 30265, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21016, 31516, 33760] 7 Tr.E) [32, 5254, 9265, 10508, 18499, 21016, 33760] 8 Tr.E) [32, 5254, 9265, 10508, 18499, 21016, 33760, 33760] 7 (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21016, 33760, 38886] 7 Tr.E))) [32, 5254, 9265, 10508, 18499, 21016, 33760, 42993] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21016, 33760, 44012] 7 Tr.E) [32, 5254, 9265, 10508, 18499, 21016, 33760, 52195] 7 Tr.E) [32, 5254, 9265, 10508, 18499, 21016, 33760, 54264] 7 (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21016, 33760, 65535] 7 Tr.E)) [32, 5254, 9265, 10508, 18499, 21016, 33761] 6 (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21016, 33762] 6 Tr.E) [32, 5254, 9265, 10508, 18499, 21016, 33764] 6 Tr.E) [32, 5254, 9265, 10508, 18499, 21016, 33768] 6 (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21016, 33776] 6 Tr.E))))) [32, 5254, 9265, 10508, 18499, 21017, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21018, 33760] 6 Tr.E) [32, 5254, 9265, 10508, 18499, 21020, 33760] 6 Tr.E) [32, 5254, 9265, 10508, 18499, 21048, 33760] 7 (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 18499, 21080, 33760] 6 Tr.E) [32, 5254, 9265, 10508, 18499, 21144, 33760] 6 Tr.E)) [32, 5254, 9265, 10508, 18499, 21272, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 18503, 21016, 33760] 6 Tr.E) [32, 5254, 9265, 10508, 18507, 21016, 33760] 6 Tr.E) [32, 5254, 9265, 10508, 18515, 21016, 33760] 6 (Tr.N Tr.E [32, 5254, 9265, 10508, 18531, 21016, 33760] 7 Tr.E))) [32, 5254, 9265, 10508, 18531, 21048, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10508, 18627, 21016, 33760] 6 Tr.E) [32, 5254, 9265, 10508, 18755, 21016, 33760] 6 Tr.E) [32, 5254, 9265, 10508, 19011, 21016, 33760] 6 (Tr.N Tr.E [32, 5254, 9265, 10509, 18499, 21016, 33760] 6 Tr.E)) [32, 5254, 9265, 10510, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10524, 18499, 21016, 33760] 6 Tr.E) [32, 5254, 9265, 10540, 18499, 21016, 33760] 7 Tr.E) [32, 5254, 9265, 10540, 18499, 21048, 33760] 6 (Tr.N Tr.E [32, 5254, 9265, 10540, 18531, 21016, 33760] 6 Tr.E)))) [32, 5254, 9265, 10572, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9265, 10636, 18499, 21016, 33760] 6 Tr.E) [32, 5254, 9265, 11020, 18499, 21016, 33760] 6 Tr.E) [32, 5254, 9267, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [32, 5254, 9269, 10508, 18499, 21016, 33760] 6 Tr.E)) [32, 5254, 9273, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 9329, 10508, 18499, 21016, 33760] 6 Tr.E) [32, 5254, 9393, 10508, 18499, 21016, 33760] 6 Tr.E) [32, 5254, 9521, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [32, 5254, 9777, 10508, 18499, 21016, 33760] 6 Tr.E))) [32, 5254, 10508, 18499, 21016, 33760, 42993] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 10508, 18499, 21016, 33777] 5 Tr.E) [32, 5254, 10508, 18499, 21016, 42993, 52195] 6 Tr.E) [32, 5254, 10508, 18499, 21016, 42993, 54264] 6 (Tr.N Tr.E [32, 5254, 10508, 18499, 21048, 33760, 42993] 6 Tr.E)) [32, 5254, 10508, 18531, 21016, 33760, 42993] 6 (Tr.N (Tr.N (Tr.N Tr.E [32, 5254, 10540, 18499, 21016, 33760, 42993] 6 Tr.E) [32, 5255, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [32, 5262, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [32, 5270, 9265, 10508, 18499, 21016, 33760] 6 Tr.E))))))
def t4 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [32, 5286, 9265, 10508, 18499, 21048, 33760] 6 Tr.E) [32, 5286, 9265, 10508, 18531, 21016, 33760] 6 Tr.E) [32, 5286, 9265, 10540, 18499, 21016, 33760] 6 (Tr.N (Tr.N Tr.E [32, 5286, 10508, 18499, 21016, 33760, 42993] 6 Tr.E) [32, 5318, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [32, 5510, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [32, 5766, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [33, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [33, 5254, 9265, 10508, 18499, 21016, 33760, 52195] 7 (Tr.N Tr.E [33, 5254, 9265, 10508, 18499, 21016, 33761] 6 Tr.E))) [33, 5254, 9265, 10508, 18499, 21049, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [33, 5254, 9265, 10508, 18531, 21016, 33760] 6 Tr.E) [33, 5254, 9265, 10508, 21016, 26959, 33760] 6 Tr.E) [33, 5254, 9265, 10541, 18499, 21016, 33760] 6 (Tr.N Tr.E [33, 5254, 10508, 11581, 18499, 21016, 33760] 6 Tr.E)) [33, 5254, 10508, 18499, 21016, 33760, 42993] 6 (Tr.N (Tr.N (Tr.N Tr.E [33, 5254, 10508, 18499, 21016, 33776] 5 Tr.E) [33, 5254, 10508, 18499, 21016, 42993, 52195] 6 Tr.E) [33, 5254, 10524, 18499, 21016, 33760] 5 (Tr.N Tr.E [33, 5254, 11581, 21016, 26959, 33760] 5 Tr.E)))) [33, 5287, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [34, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [36, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [40, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [48, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E)) [48, 5254, 9265, 10508, 18499, 21016, 33760, 54264] 7 (Tr.N (Tr.N (Tr.N Tr.E [48, 5254, 9265, 10508, 18499, 21016, 33776] 6 Tr.E) [48, 5254, 9265, 10508, 18499, 21048, 33760] 6 Tr.E) [48, 5254, 9265, 10508, 18499, 22174, 33760] 6 (Tr.N Tr.E [48, 5254, 9265, 10508, 18547, 21016, 33760] 6 Tr.E))) [48, 5254, 9265, 10556, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [48, 5254, 10508, 13495, 18499, 21016, 33760] 6 Tr.E) [48, 5254, 10508, 18499, 21016, 33760, 42993] 6 Tr.E) [48, 5254, 10508, 18499, 21016, 33761] 5 (Tr.N Tr.E [48, 5254, 10508, 18499, 21016, 42993, 54264] 6 Tr.E)) [48, 5255, 10508, 18499, 21016, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [48, 5302, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [48, 10508, 13495, 18499, 22174, 33760] 5 Tr.E) [49, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [49, 5254, 10508, 18499, 21016, 23131, 33760] 6 Tr.E))))) [49, 5254, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [49, 5254, 10508, 18499, 21016, 33760, 52195] 6 Tr.E) [49, 5254, 10508, 18499, 21016, 33760, 54264] 6 Tr.E) [49, 5254, 10508, 18499, 21016, 33760, 56315] 6 (Tr.N Tr.E [49, 5254, 10508, 18499, 21016, 33761] 5 Tr.E)) [49, 5254, 10508, 18499, 21016, 33776] 5 (Tr.N (Tr.N (Tr.N Tr.E [49, 5254, 10508, 18499, 21016, 33777] 5 Tr.E) [49, 5254, 10508, 18499, 21017, 33760] 5 Tr.E) [49, 5254, 10508, 18499, 21048, 33760] 5 (Tr.N Tr.E [49, 5254, 10508, 18499, 21049, 33760] 5 Tr.E))) [49, 5254, 10508, 18499, 22174, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [49, 5254, 10508, 18515, 21016, 33760] 5 Tr.E) [49, 5254, 10508, 18531, 21016, 33760] 5 Tr.E) [49, 5254, 10508, 18547, 21016, 33760] 5 (Tr.N Tr.E [49, 5254, 10508, 21016, 26959, 33760] 5 Tr.E)) [49, 5254, 10557, 18499, 21016, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [49, 5303, 10508, 18499, 21016, 33760] 5 Tr.E) [96, 5254, 9265, 10508, 18499, 21016, 27763, 33760] 7 Tr.E) [96, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N Tr.E [96, 5254, 9265, 10508, 18499, 21112, 33760] 6 Tr.E)))) [96, 5254, 9265, 10508, 18531, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [96, 5254, 9265, 10508, 21016, 33760, 52195] 6 Tr.E) [96, 5254, 9265, 10604, 18499, 21016, 33760] 6 Tr.E) [96, 5254, 9329, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [96, 5254, 10508, 18499, 21016, 33760, 42993] 6 Tr.E)) [96, 5350, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [160, 5254, 9265, 10508, 13495, 18499, 21016, 33760] 7 Tr.E) [160, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [160, 5254, 9265, 10508, 18499, 21176, 33760] 6 (Tr.N Tr.E [160, 5254, 9265, 10508, 18659, 21016, 33760] 6 Tr.E))) [160, 5254, 9265, 10668, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [160, 5254, 9393, 10508, 18499, 21016, 33760] 6 Tr.E) [160, 5254, 10508, 18499, 21016, 33760, 42993] 6 Tr.E) [160, 5286, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [160, 9265, 10508, 18499, 21016, 33760, 38886] 6 Tr.E)) [160, 10508, 18499, 21016, 38886, 42993] 5 (Tr.N (Tr.N (Tr.N Tr.E [163, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [224, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [352, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [352, 5254, 9265, 18499, 21016, 44012] 5 Tr.E))))))
def u5 : Tr := Tr.N t3 [32, 5286, 9265, 10508, 18499, 21016, 33760] 7 t4
def u6 : Tr := Tr.N u2 [5, 5254, 11581, 18499, 21016, 33760] 5 u5
def t7 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1024, 2048, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1024, 4096, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1024, 5254, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1024, 5254, 9265, 10508, 10508, 18499, 21016, 33760] 7 Tr.E)) [1024, 5254, 9265, 10508, 11532, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 11581, 18499, 21016, 33760] 7 Tr.E) [1024, 5254, 9265, 10508, 13495, 18499, 21016, 33760] 7 Tr.E) [1024, 5254, 9265, 10508, 15758, 18499, 21016, 33760] 7 (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 18499, 21016, 33760] 7 Tr.E))) [1024, 5254, 9265, 10508, 18499, 19523, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21016, 21016, 33760] 7 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 22040, 33760] 7 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 22174, 33760] 7 (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21016, 23131, 33760] 7 Tr.E)) [1024, 5254, 9265, 10508, 18499, 21016, 23751, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21016, 26959, 33760] 7 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 27763, 33760] 7 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 30265, 33760] 7 (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21016, 31516, 33760] 7 Tr.E)))) [1024, 5254, 9265, 10508, 18499, 21016, 33760] 8 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21016, 33760, 33760] 7 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 33760, 34784] 7 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 33760, 38886] 7 (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21016, 33760, 42993] 7 Tr.E)) [1024, 5254, 9265, 10508, 18499, 21016, 33760, 44012] 7 (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21016, 33760, 52195] 7 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 33760, 54264] 7 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 33760, 65535] 7 (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21016, 33761] 6 Tr.E))) [1024, 5254, 9265, 10508, 18499, 21016, 33762] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21016, 33764] 6 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 33768] 6 Tr.E) [1024, 5254, 9265, 10508, 18499, 21016, 33776] 6 (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21017, 33760] 6 Tr.E)) [1024, 5254, 9265, 10508, 18499, 21018, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21020, 33760] 6 Tr.E) [1024, 5254, 9265, 10508, 18499, 21048, 33760] 6 Tr.E) [1024, 5254, 9265, 10508, 18499, 21080, 33760] 6 (Tr.N Tr.E [1024, 5254, 9265, 10508, 18499, 21144, 33760] 6 Tr.E))))) [1024, 5254, 9265, 10508, 18499, 21272, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 18503, 21016, 33760] 6 Tr.E) [1024, 5254, 9265, 10508, 18507, 21016, 33760] 6 Tr.E) [1024, 5254, 9265, 10508, 18515, 21016, 33760] 6 (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 18531, 21016, 33760] 6 Tr.E) [1024, 5254, 9265, 10508, 18627, 21016, 33760] 6 Tr.E)) [1024, 5254, 9265, 10508, 18755, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10508, 19011, 21016, 33760] 6 Tr.E) [1024, 5254, 9265, 10509, 18499, 21016, 33760] 6 Tr.E) [1024, 5254, 9265, 10510, 18499, 21016, 33760] 6 (Tr.N Tr.E [1024, 5254, 9265, 10524, 18499, 21016, 33760] 6 Tr.E))) [1024, 5254, 9265, 10540, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9265, 10572, 18499, 21016, 33760] 6 Tr.E) [1024, 5254, 9265, 10636, 18499, 21016, 33760] 6 Tr.E) [1024, 5254, 9265, 11020, 18499, 21016, 33760] 6 (Tr.N Tr.E [1024, 5254, 9267, 10508, 18499, 21016, 33760] 6 Tr.E)) [1024, 5254, 9269, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1024, 5254, 9273, 10508, 18499, 21016, 33760] 6 Tr.E) [1024, 5254, 9329, 10508, 18499, 21016, 33760] 6 Tr.E) [1024, 5254, 9393, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [1024, 5254, 9521, 10508, 18499, 21016, 33760] 6 Tr.E)))) [1024, 5254, 9777, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1024, 5255, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1024, 5262, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1024, 5270, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [1024, 5286, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [1024, 5318, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1024, 5510, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1024, 5766, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1025, 5254, 9265, 10508, 18499, 21016, 23751, 33760] 7 (Tr.N Tr.E [1025, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E))) [1025, 5254, 9265, 10508, 21016, 26959, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1025, 5254, 10508, 11581, 18499, 21016, 33760] 6 Tr.E) [1025, 5254, 11581, 21016, 26959, 33760] 5 Tr.E) [1025, 5255, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [1026, 5254, 9265, 10508, 18499, 21016, 27763, 33760] 7 Tr.E)) [1026, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [1026, 5254, 9265, 10508, 21016, 23131, 33760] 6 Tr.E) [1026, 5254, 9267, 10508, 18499, 21016, 33760] 6 Tr.E) [1026, 9265, 10508, 18499, 21016, 22174, 33760] 6 (Tr.N Tr.E [1026, 9265, 10508, 22174, 23131, 33760] 5 Tr.E))))))
def t8 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1028, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1028, 5254, 9269, 10508, 18499, 21016, 33760] 6 Tr.E) [1028, 9265, 10508, 13495, 18499, 21016, 33760] 6 (Tr.N (Tr.N Tr.E [1028, 10508, 11581, 13495, 18499, 21016, 33760] 6 Tr.E) [1030, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [1032, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1040, 5254, 9265, 10508, 18499, 21016, 22174, 33760] 7 Tr.E) [1040, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1040, 5254, 10508, 13495, 18499, 21016, 33760] 6 (Tr.N Tr.E [1040, 5270, 9265, 10508, 18499, 21016, 33760] 6 Tr.E))) [1040, 10508, 13495, 18499, 21016, 22174, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1041, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1052, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1052, 5254, 9265, 18499, 31516, 33760] 5 (Tr.N Tr.E [1052, 10508, 13495, 18499, 21016, 33760] 5 Tr.E)) [1052, 13495, 18499, 31516, 33760] 4 (Tr.N (Tr.N (Tr.N Tr.E [1056, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [1056, 5254, 9265, 10508, 18499, 21016, 33760, 38886] 7 Tr.E) [1056, 5254, 10508, 18499, 21016, 33760, 42993] 6 (Tr.N Tr.E [1056, 5286, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)))) [1057, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1072, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1073, 5254, 10508, 18499, 21016, 33760] 5 Tr.E) [1088, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [1122, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [1152, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [1152, 5254, 9265, 10508, 18499, 21016, 33760, 42993] 7 Tr.E) [1152, 5254, 9393, 10508, 18499, 21016, 33760] 6 Tr.E) [1152, 9265, 10508, 18499, 21016, 33760, 38886] 6 (Tr.N Tr.E [1154, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E))) [1156, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [1158, 9265, 10508, 18499, 21016, 33760] 5 Tr.E) [1217, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [1280, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [1316, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [1536, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [1680, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [3072, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [3077, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [5120, 5254, 9265, 10508, 18499, 21016, 30265, 33760] 7 Tr.E))))) [5120, 5254, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5122, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5124, 5254, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5248, 5254, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N Tr.E [5254, 5254, 5254, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [5254, 5254, 9265, 9265, 10508, 18499, 21016, 33760] 7 Tr.E)) [5254, 5254, 9265, 10508, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10508, 11581, 18499, 21016, 33760] 7 Tr.E) [5254, 5254, 9265, 10508, 13495, 18499, 21016, 33760] 7 Tr.E) [5254, 5254, 9265, 10508, 15758, 18499, 21016, 33760] 7 (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21016, 22174, 33760] 7 Tr.E))) [5254, 5254, 9265, 10508, 18499, 21016, 23131, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21016, 23751, 33760] 7 Tr.E) [5254, 5254, 9265, 10508, 18499, 21016, 26959, 33760] 7 Tr.E) [5254, 5254, 9265, 10508, 18499, 21016, 27763, 33760] 7 (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21016, 30265, 33760] 7 Tr.E)) [5254, 5254, 9265, 10508, 18499, 21016, 31516, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21016, 33760] 8 Tr.E) [5254, 5254, 9265, 10508, 18499, 21016, 33760, 33760] 7 Tr.E) [5254, 5254, 9265, 10508, 18499, 21016, 33760, 38886] 7 (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21016, 33760, 42993] 7 Tr.E)))) [5254, 5254, 9265, 10508, 18499, 21016, 33760, 44012] 7 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21016, 33760, 52195] 7 Tr.E) [5254, 5254, 9265, 10508, 18499, 21016, 33760, 54264] 7 Tr.E) [5254, 5254, 9265, 10508, 18499, 21016, 33760, 65535] 7 (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21016, 33761] 6 Tr.E)) [5254, 5254, 9265, 10508, 18499, 21016, 33762] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21016, 33764] 6 Tr.E) [5254, 5254, 9265, 10508, 18499, 21016, 33768] 6 Tr.E) [5254, 5254, 9265, 10508, 18499, 21016, 33776] 6 (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21017, 33760] 6 Tr.E))) [5254, 5254, 9265, 10508, 18499, 21018, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21020, 33760] 6 Tr.E) [5254, 5254, 9265, 10508, 18499, 21048, 33760] 6 Tr.E) [5254, 5254, 9265, 10508, 18499, 21080, 33760] 6 (Tr.N Tr.E [5254, 5254, 9265, 10508, 18499, 21144, 33760] 6 Tr.E)) [5254, 5254, 9265, 10508, 18499, 21272, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10508, 18503, 21016, 33760] 6 Tr.E) [5254, 5254, 9265, 10508, 18507, 21016, 33760] 6 Tr.E) [5254, 5254, 9265, 10508, 18515, 21016, 33760] 6 (Tr.N Tr.E [5254, 5254, 9265, 10508, 18531, 21016, 33760] 6 Tr.E))))))
def u9 : Tr := Tr.N t7 [1028, 5254, 9265, 10508, 11581, 18499, 21016, 33760] 7 t8
def t10 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10508, 18755, 21016, 33760] 6 Tr.E) [5254, 5254, 9265, 10508, 19011, 21016, 33760] 6 Tr.E) [5254, 5254, 9265, 10509, 18499, 21016, 33760] 6 (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10510, 18499, 21016, 33760] 6 Tr.E) [5254, 5254, 9265, 10524, 18499, 21016, 33760] 6 Tr.E)) [5254, 5254, 9265, 10540, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9265, 10572, 18499, 21016, 33760] 6 Tr.E) [5254, 5254, 9265, 10636, 18499, 21016, 33760] 6 Tr.E) [5254, 5254, 9265, 11020, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 5254, 9267, 10508, 18499, 21016, 33760] 6 Tr.E))) [5254, 5254, 9269, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5254, 9273, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 5254, 9329, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 5254, 9393, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 5254, 9521, 10508, 18499, 21016, 33760] 6 Tr.E)) [5254, 5254, 9777, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5255, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [5254, 5255, 9265, 10508, 18499, 21016, 33761] 6 Tr.E) [5254, 5255, 9265, 10508, 18499, 21017, 33760] 6 (Tr.N Tr.E [5254, 5255, 9265, 10508, 21016, 26959, 33760] 6 Tr.E)))) [5254, 5255, 9265, 10509, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5255, 10508, 11581, 18499, 21016, 33760] 6 Tr.E) [5254, 5255, 11581, 21016, 26959, 33760] 5 Tr.E) [5254, 5262, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N Tr.E [5254, 5262, 9265, 10508, 18499, 21016, 33768] 6 Tr.E)) [5254, 5262, 9265, 10508, 18499, 23131, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5262, 9265, 10508, 18507, 21016, 33760] 6 Tr.E) [5254, 5262, 9265, 18499, 21016, 26959, 33760] 6 Tr.E) [5254, 5262, 9265, 23131, 26959, 33760] 5 (Tr.N Tr.E [5254, 5262, 9273, 10508, 18499, 21016, 33760] 6 Tr.E))) [5254, 5270, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5270, 9265, 10508, 18499, 21016, 33776] 6 Tr.E) [5254, 5270, 9265, 10508, 18515, 21016, 33760] 6 Tr.E) [5254, 5270, 9265, 10524, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 5271, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [5254, 5278, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5286, 9265, 10508, 18499, 21016, 33760] 7 Tr.E) [5254, 5286, 9265, 10508, 18499, 21048, 33760] 6 Tr.E) [5254, 5286, 9265, 10508, 18531, 21016, 33760] 6 (Tr.N Tr.E [5254, 5286, 9265, 10540, 18499, 21016, 33760] 6 Tr.E))))) [5254, 5286, 10508, 18499, 21016, 33760, 42993] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5287, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 5302, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 5318, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N (Tr.N Tr.E [5254, 5318, 9265, 10508, 18499, 21080, 33760] 6 Tr.E) [5254, 5318, 9265, 10508, 21016, 33760, 52195] 6 Tr.E)) [5254, 5318, 9265, 10572, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5318, 9329, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 5319, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 5350, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 5510, 9265, 10508, 18499, 21016, 33760] 7 Tr.E))) [5254, 5510, 9265, 10508, 18499, 21272, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5510, 9265, 10508, 18755, 21016, 33760] 6 Tr.E) [5254, 5510, 9265, 18499, 21016, 33760, 44012] 6 Tr.E) [5254, 5510, 9521, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 5518, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [5254, 5542, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5574, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 5664, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 5766, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N Tr.E [5254, 5766, 9265, 10508, 18499, 33760, 54264] 6 Tr.E)))) [5254, 5766, 9265, 10508, 19011, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 5766, 9265, 11020, 18499, 21016, 33760] 6 Tr.E) [5254, 5766, 9777, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 5774, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 5782, 9265, 10508, 18499, 21016, 33760] 6 Tr.E)) [5254, 5798, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 5830, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 6022, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 7302, 9265, 10508, 18499, 21016, 33760] 7 (Tr.N Tr.E [5254, 7303, 9265, 10508, 18499, 21016, 33760] 6 Tr.E))) [5254, 7310, 9265, 10508, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 7366, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 7558, 9265, 10508, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11266, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 11313, 18499, 21016, 33760] 7 Tr.E)) [5254, 9265, 10508, 11315, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11317, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11321, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11377, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 11532, 18499, 21016, 33760] 7 Tr.E))))))
def t11 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11534, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11548, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11564, 18499, 21016, 33760] 6 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11569, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11581, 11581, 18499, 21016, 33760] 7 Tr.E)) [5254, 9265, 10508, 11581, 13495, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11581, 15758, 18499, 21016, 33760] 7 Tr.E) [5254, 9265, 10508, 11581, 15807, 18499, 21016, 33760] 7 Tr.E) [5254, 9265, 10508, 11581, 18499, 21016, 22174, 33760] 7 (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21016, 23751, 33760] 7 Tr.E))) [5254, 9265, 10508, 11581, 18499, 21016, 27763, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21016, 28031, 33760] 7 Tr.E) [5254, 9265, 10508, 11581, 18499, 21016, 30265, 33760] 7 Tr.E) [5254, 9265, 10508, 11581, 18499, 21016, 31516, 33760] 7 (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21016, 32573, 33760] 7 Tr.E)) [5254, 9265, 10508, 11581, 18499, 21016, 33760] 8 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21016, 33760, 33760] 7 Tr.E) [5254, 9265, 10508, 11581, 18499, 21016, 33760, 38886] 7 Tr.E) [5254, 9265, 10508, 11581, 18499, 21016, 33760, 42993] 7 (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21016, 33760, 44012] 7 Tr.E)))) [5254, 9265, 10508, 11581, 18499, 21016, 33760, 45053] 7 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21016, 33760, 52195] 7 Tr.E) [5254, 9265, 10508, 11581, 18499, 21016, 33760, 54264] 7 Tr.E) [5254, 9265, 10508, 11581, 18499, 21016, 33760, 65535] 7 (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21016, 33761] 6 Tr.E)) [5254, 9265, 10508, 11581, 18499, 21016, 33762] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21016, 33764] 6 Tr.E) [5254, 9265, 10508, 11581, 18499, 21016, 33768] 6 Tr.E) [5254, 9265, 10508, 11581, 18499, 21016, 33776] 6 (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21016, 33784] 6 Tr.E))) [5254, 9265, 10508, 11581, 18499, 21017, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21018, 33760] 6 Tr.E) [5254, 9265, 10508, 11581, 18499, 21020, 33760] 6 Tr.E) [5254, 9265, 10508, 11581, 18499, 21048, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21080, 33760] 6 Tr.E)) [5254, 9265, 10508, 11581, 18499, 21144, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11581, 18499, 21272, 33760] 6 Tr.E) [5254, 9265, 10508, 11581, 18499, 21304, 33760] 6 Tr.E) [5254, 9265, 10508, 11581, 18503, 21016, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 11581, 18507, 21016, 33760] 6 Tr.E))))) [5254, 9265, 10508, 11581, 18515, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11581, 18523, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11581, 18531, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11581, 18627, 21016, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 11581, 18755, 21016, 33760] 6 Tr.E)) [5254, 9265, 10508, 11581, 18787, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 11581, 19011, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11583, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 11645, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 11660, 18499, 21016, 33760] 6 Tr.E))) [5254, 9265, 10508, 11709, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 12093, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 13495, 18499, 21017, 33760] 6 Tr.E) [5254, 9265, 10508, 13495, 18499, 21018, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 13495, 18499, 21019, 33760] 6 Tr.E)) [5254, 9265, 10508, 13495, 18499, 21020, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 13495, 18499, 21048, 33760] 6 Tr.E) [5254, 9265, 10508, 13495, 18499, 21080, 33760] 6 Tr.E) [5254, 9265, 10508, 13495, 18499, 21144, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 13495, 18499, 21176, 33760] 6 Tr.E)))) [5254, 9265, 10508, 13495, 18499, 21272, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15494, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 15543, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 15628, 18499, 21016, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 15677, 18499, 21016, 33760] 6 Tr.E)) [5254, 9265, 10508, 15758, 15758, 18499, 21016, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15758, 15807, 18499, 21016, 33760] 7 Tr.E) [5254, 9265, 10508, 15758, 18499, 21016, 23751, 33760] 7 Tr.E) [5254, 9265, 10508, 15758, 18499, 21016, 27763, 33760] 7 (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21016, 32207, 33760] 7 Tr.E))) [5254, 9265, 10508, 15758, 18499, 21016, 32670, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21016, 33760] 8 Tr.E) [5254, 9265, 10508, 15758, 18499, 21016, 33760, 33760] 7 Tr.E) [5254, 9265, 10508, 15758, 18499, 21016, 33760, 38886] 7 (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21016, 33760, 42993] 7 Tr.E)) [5254, 9265, 10508, 15758, 18499, 21016, 33760, 44012] 7 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21016, 33760, 49134] 7 Tr.E) [5254, 9265, 10508, 15758, 18499, 21016, 33760, 52195] 7 Tr.E) [5254, 9265, 10508, 15758, 18499, 21016, 33760, 54264] 7 (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21016, 33760, 65535] 7 Tr.E))))))
def u12 : Tr := Tr.N t10 [5254, 9265, 10508, 11533, 18499, 21016, 33760] 6 t11
def u13 : Tr := Tr.N u9 [5254, 5254, 9265, 10508, 18627, 21016, 33760] 6 u12
def u14 : Tr := Tr.N u6 [1024, 1024, 5254, 9265, 10508, 18499, 21016, 33760] 7 u13
def t15 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21016, 33762] 6 Tr.E) [5254, 9265, 10508, 15758, 18499, 21016, 33764] 6 Tr.E) [5254, 9265, 10508, 15758, 18499, 21016, 33768] 6 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21016, 33776] 6 Tr.E) [5254, 9265, 10508, 15758, 18499, 21017, 33760] 6 Tr.E)) [5254, 9265, 10508, 15758, 18499, 21018, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21020, 33760] 6 Tr.E) [5254, 9265, 10508, 15758, 18499, 21048, 33760] 6 Tr.E) [5254, 9265, 10508, 15758, 18499, 21080, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21144, 33760] 6 Tr.E))) [5254, 9265, 10508, 15758, 18499, 21272, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15758, 18499, 21400, 33760] 6 Tr.E) [5254, 9265, 10508, 15758, 18503, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 15758, 18507, 21016, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 15758, 18515, 21016, 33760] 6 Tr.E)) [5254, 9265, 10508, 15758, 18531, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15758, 18627, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 15758, 18755, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 15758, 18883, 21016, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 15758, 19011, 21016, 33760] 6 Tr.E)))) [5254, 9265, 10508, 15759, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 15774, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 15790, 18499, 21016, 33760] 6 Tr.E) [5254, 9265, 10508, 15807, 18499, 21016, 33760] 7 (Tr.N Tr.E [5254, 9265, 10508, 15822, 18499, 21016, 33760] 6 Tr.E)) [5254, 9265, 10508, 16270, 18499, 21016, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 31859, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 31991, 33760] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 32255, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760] 9 Tr.E))) [5254, 9265, 10508, 18499, 21016, 33760, 33760] 8 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 33760, 33760] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 33760, 38886] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 33760, 65535] 7 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 33761] 7 Tr.E)) [5254, 9265, 10508, 18499, 21016, 33760, 33763] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 34784] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 34785] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 34786] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 34788] 6 Tr.E))))) [5254, 9265, 10508, 18499, 21016, 33760, 34800] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 38880] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 38886] 8 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 38886, 38886] 7 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 38886, 42993] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 38886, 44012] 7 Tr.E)) [5254, 9265, 10508, 18499, 21016, 33760, 38886, 47095] 7 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 38886, 49134] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 38886, 55294] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 38886, 57319] 7 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 38886, 65535] 7 Tr.E))) [5254, 9265, 10508, 18499, 21016, 33760, 38887] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 38894] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 38902] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 40934] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 45036] 6 Tr.E)) [5254, 9265, 10508, 18499, 21016, 33760, 45041] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 45053] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 49134] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33760, 49151] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 65519] 6 Tr.E)))) [5254, 9265, 10508, 18499, 21016, 33760, 65535] 8 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33760, 65535, 65535] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33761] 7 Tr.E) [5254, 9265, 10508, 18499, 21016, 33761, 33761] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33761, 38886] 6 Tr.E)) [5254, 9265, 10508, 18499, 21016, 33761, 38887] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33761, 42993] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 33761, 44012] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 33761, 44013] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33761, 52195] 6 Tr.E))) [5254, 9265, 10508, 18499, 21016, 33761, 54264] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33761, 54265] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 33761, 65535] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 33763] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 33765] 5 Tr.E)) [5254, 9265, 10508, 18499, 21016, 34784, 44012] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 34784, 52195] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 34784, 54264] 6 Tr.E) [5254, 9265, 10508, 18499, 21016, 38886, 44012] 7 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21016, 38886, 60399] 6 Tr.E))))))
def t16 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21017, 22174, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21017, 22175, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21017, 23131, 33760] 6 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21017, 23751, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21017, 30265, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 21017, 31516, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21017, 31517, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21017, 33760] 7 Tr.E) [5254, 9265, 10508, 18499, 21017, 33760, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21017, 33760, 33761] 6 Tr.E))) [5254, 9265, 10508, 18499, 21017, 33760, 38886] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21017, 33760, 42993] 6 Tr.E) [5254, 9265, 10508, 18499, 21017, 33760, 44012] 6 Tr.E) [5254, 9265, 10508, 18499, 21017, 33760, 52195] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21017, 33760, 54264] 6 Tr.E)) [5254, 9265, 10508, 18499, 21017, 33760, 54265] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21017, 33760, 65535] 6 Tr.E) [5254, 9265, 10508, 18499, 21017, 33761] 6 Tr.E) [5254, 9265, 10508, 18499, 21017, 33762] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21017, 33764] 5 Tr.E)))) [5254, 9265, 10508, 18499, 21017, 33768] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21017, 33776] 5 Tr.E) [5254, 9265, 10508, 18499, 21017, 33777] 5 Tr.E) [5254, 9265, 10508, 18499, 21018, 21018, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21018, 22174, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 21018, 23131, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21018, 23751, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21018, 30265, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21018, 30267, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21018, 31516, 33760] 6 Tr.E))) [5254, 9265, 10508, 18499, 21018, 31518, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21018, 33760] 7 Tr.E) [5254, 9265, 10508, 18499, 21018, 33760, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21018, 33760, 33762] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21018, 33760, 38886] 6 Tr.E)) [5254, 9265, 10508, 18499, 21018, 33760, 42993] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21018, 33760, 44012] 6 Tr.E) [5254, 9265, 10508, 18499, 21018, 33760, 52195] 6 Tr.E) [5254, 9265, 10508, 18499, 21018, 33760, 54264] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21018, 33760, 54266] 6 Tr.E))))) [5254, 9265, 10508, 18499, 21018, 33760, 65535] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21018, 33761] 5 Tr.E) [5254, 9265, 10508, 18499, 21018, 33762] 6 Tr.E) [5254, 9265, 10508, 18499, 21018, 33764] 5 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21018, 33768] 5 Tr.E) [5254, 9265, 10508, 18499, 21018, 33776] 5 Tr.E)) [5254, 9265, 10508, 18499, 21019, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21019, 33763] 5 Tr.E) [5254, 9265, 10508, 18499, 21020, 21020, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21020, 22174, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21020, 23131, 33760] 6 Tr.E))) [5254, 9265, 10508, 18499, 21020, 23135, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21020, 23751, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21020, 30265, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21020, 30269, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21020, 31516, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 21020, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21020, 33760, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21020, 33760, 33764] 6 Tr.E) [5254, 9265, 10508, 18499, 21020, 33760, 38886] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21020, 33760, 42993] 6 Tr.E)))) [5254, 9265, 10508, 18499, 21020, 33760, 44012] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21020, 33760, 52195] 6 Tr.E) [5254, 9265, 10508, 18499, 21020, 33760, 54264] 6 Tr.E) [5254, 9265, 10508, 18499, 21020, 33760, 54268] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21020, 33760, 65535] 6 Tr.E)) [5254, 9265, 10508, 18499, 21020, 33761] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21020, 33762] 5 Tr.E) [5254, 9265, 10508, 18499, 21020, 33764] 6 Tr.E) [5254, 9265, 10508, 18499, 21020, 33768] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21020, 33772] 5 Tr.E))) [5254, 9265, 10508, 18499, 21020, 33776] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21021, 33760] 5 Tr.E) [5254, 9265, 10508, 18499, 21022, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21022, 33766] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21048, 21048, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 21048, 22174, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21048, 22206, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21048, 23131, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21048, 23163, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21048, 23751, 33760] 6 Tr.E))))))
def u17 : Tr := Tr.N t15 [5254, 9265, 10508, 18499, 21017, 21017, 33760] 6 t16
def t18 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21048, 31516, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21048, 31548, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21048, 33760] 7 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21048, 33760, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21048, 33760, 38886] 6 Tr.E)) [5254, 9265, 10508, 18499, 21048, 33760, 42993] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21048, 33760, 44012] 6 Tr.E) [5254, 9265, 10508, 18499, 21048, 33760, 52195] 6 Tr.E) [5254, 9265, 10508, 18499, 21048, 33760, 54264] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21048, 33760, 65535] 6 Tr.E))) [5254, 9265, 10508, 18499, 21048, 33761] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21048, 33762] 5 Tr.E) [5254, 9265, 10508, 18499, 21048, 33764] 5 Tr.E) [5254, 9265, 10508, 18499, 21048, 33768] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21048, 33776] 5 Tr.E)) [5254, 9265, 10508, 18499, 21049, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21049, 33760, 52195] 6 Tr.E) [5254, 9265, 10508, 18499, 21049, 33761] 5 Tr.E) [5254, 9265, 10508, 18499, 21050, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21052, 33760] 5 Tr.E)))) [5254, 9265, 10508, 18499, 21080, 21080, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21080, 22174, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21080, 22238, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21080, 23131, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21080, 23751, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 21080, 30265, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21080, 30329, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21080, 31516, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21080, 31580, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21080, 33760] 7 Tr.E))) [5254, 9265, 10508, 18499, 21080, 33760, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21080, 33760, 38886] 6 Tr.E) [5254, 9265, 10508, 18499, 21080, 33760, 42993] 6 Tr.E) [5254, 9265, 10508, 18499, 21080, 33760, 44012] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21080, 33760, 52195] 6 Tr.E)) [5254, 9265, 10508, 18499, 21080, 33760, 54264] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21080, 33760, 65535] 6 Tr.E) [5254, 9265, 10508, 18499, 21080, 33761] 5 Tr.E) [5254, 9265, 10508, 18499, 21080, 33762] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21080, 33764] 5 Tr.E))))) [5254, 9265, 10508, 18499, 21080, 33768] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21080, 33776] 5 Tr.E) [5254, 9265, 10508, 18499, 21081, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21081, 33760, 42993] 6 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21081, 33761] 5 Tr.E) [5254, 9265, 10508, 18499, 21082, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 21082, 33760, 38886] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21082, 33762] 5 Tr.E) [5254, 9265, 10508, 18499, 21083, 33760] 5 Tr.E) [5254, 9265, 10508, 18499, 21084, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21112, 33760] 6 Tr.E))) [5254, 9265, 10508, 18499, 21144, 21144, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21144, 22174, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21144, 23131, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21144, 23259, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21144, 23751, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 21144, 30265, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21144, 30393, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21144, 31516, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21144, 31644, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21144, 33760] 7 Tr.E)))) [5254, 9265, 10508, 18499, 21144, 33760, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21144, 33760, 38886] 6 Tr.E) [5254, 9265, 10508, 18499, 21144, 33760, 42993] 6 Tr.E) [5254, 9265, 10508, 18499, 21144, 33760, 44012] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21144, 33760, 52195] 6 Tr.E)) [5254, 9265, 10508, 18499, 21144, 33760, 54264] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21144, 33760, 65535] 6 Tr.E) [5254, 9265, 10508, 18499, 21144, 33761] 5 Tr.E) [5254, 9265, 10508, 18499, 21144, 33762] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21144, 33764] 5 Tr.E))) [5254, 9265, 10508, 18499, 21144, 33768] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21144, 33776] 5 Tr.E) [5254, 9265, 10508, 18499, 21145, 33760] 5 Tr.E) [5254, 9265, 10508, 18499, 21146, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21146, 33760, 52195] 6 Tr.E)) [5254, 9265, 10508, 18499, 21146, 33762] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21148, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21148, 33760, 44012] 6 Tr.E) [5254, 9265, 10508, 18499, 21148, 33764] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21150, 33760] 5 Tr.E))))))
def t19 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21179, 33760] 5 Tr.E) [5254, 9265, 10508, 18499, 21208, 23751, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21208, 33760] 6 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21240, 33760] 5 Tr.E) [5254, 9265, 10508, 18499, 21272, 21272, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 21272, 22174, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21272, 22430, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21272, 23131, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21272, 23387, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21272, 23751, 33760] 6 Tr.E))) [5254, 9265, 10508, 18499, 21272, 30265, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21272, 30521, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21272, 31516, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21272, 33760] 7 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21272, 33760, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 21272, 33760, 38886] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21272, 33760, 42993] 6 Tr.E) [5254, 9265, 10508, 18499, 21272, 33760, 44012] 6 Tr.E) [5254, 9265, 10508, 18499, 21272, 33760, 52195] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21272, 33760, 54264] 6 Tr.E)))) [5254, 9265, 10508, 18499, 21272, 33760, 65535] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21272, 33761] 5 Tr.E) [5254, 9265, 10508, 18499, 21272, 33762] 5 Tr.E) [5254, 9265, 10508, 18499, 21272, 33764] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21272, 33768] 5 Tr.E)) [5254, 9265, 10508, 18499, 21272, 33776] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21273, 33760] 5 Tr.E) [5254, 9265, 10508, 18499, 21274, 33760] 5 Tr.E) [5254, 9265, 10508, 18499, 21276, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21276, 33760, 38886] 6 Tr.E))) [5254, 9265, 10508, 18499, 21276, 33764] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21304, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21336, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 21342, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 21368, 33760] 5 Tr.E)) [5254, 9265, 10508, 18499, 21400, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 21432, 33760] 5 Tr.E) [5254, 9265, 10508, 18499, 21464, 33760] 5 Tr.E) [5254, 9265, 10508, 18499, 22040, 23131, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 22040, 31516, 33760] 6 Tr.E))))) [5254, 9265, 10508, 18499, 22040, 33760, 54264] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 22040, 33776] 5 Tr.E) [5254, 9265, 10508, 18499, 22174, 23064, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 22174, 23131, 33760] 7 (Tr.N Tr.E [5254, 9265, 10508, 18499, 22174, 29208, 33760] 6 Tr.E)) [5254, 9265, 10508, 18499, 22174, 31516, 33760] 7 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 22174, 31583, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 22174, 33760, 33776] 6 Tr.E) [5254, 9265, 10508, 18499, 22174, 33760, 54264] 7 (Tr.N Tr.E [5254, 9265, 10508, 18499, 22174, 33760, 56315] 6 Tr.E))) [5254, 9265, 10508, 18499, 22174, 33760, 64508] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 22174, 33776] 6 Tr.E) [5254, 9265, 10508, 18499, 22174, 33777] 5 Tr.E) [5254, 9265, 10508, 18499, 22174, 33784] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 22174, 42993, 54264] 6 Tr.E)) [5254, 9265, 10508, 18499, 22174, 44012, 54264] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 23064, 30265, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 23064, 33760, 54264] 6 Tr.E) [5254, 9265, 10508, 18499, 23064, 33768] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 23131, 29208, 33760] 6 Tr.E)))) [5254, 9265, 10508, 18499, 23131, 30265, 33760] 7 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 23131, 30399, 33760] 6 Tr.E) [5254, 9265, 10508, 18499, 23131, 33760, 33768] 6 Tr.E) [5254, 9265, 10508, 18499, 23131, 33760, 54264] 7 (Tr.N Tr.E [5254, 9265, 10508, 18499, 23131, 33760, 55294] 6 Tr.E)) [5254, 9265, 10508, 18499, 23131, 33760, 63481] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 23131, 33768] 6 Tr.E) [5254, 9265, 10508, 18499, 23131, 33772] 5 Tr.E) [5254, 9265, 10508, 18499, 23131, 33784] 5 (Tr.N Tr.E [5254, 9265, 10508, 18499, 23131, 42993, 54264] 6 Tr.E))) [5254, 9265, 10508, 18499, 23131, 44012, 54264] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 24287, 33760, 54264] 6 Tr.E) [5254, 9265, 10508, 18499, 29208, 33760, 54264] 6 Tr.E) [5254, 9265, 10508, 18499, 30265, 33760, 54264] 7 (Tr.N Tr.E [5254, 9265, 10508, 18499, 30265, 33760, 56315] 6 Tr.E)) [5254, 9265, 10508, 18499, 30265, 33784] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 30265, 42993, 54264] 6 Tr.E) [5254, 9265, 10508, 18499, 30265, 44012, 54264] 6 Tr.E) [5254, 9265, 10508, 18499, 30399, 33760, 54264] 6 (Tr.N Tr.E [5254, 9265, 10508, 18499, 31516, 33760, 54264] 7 Tr.E))))))
def u20 : Tr := Tr.N t18 [5254, 9265, 10508, 18499, 21176, 33760] 6 t19
def u21 : Tr := Tr.N u17 [5254, 9265, 10508, 18499, 21048, 30265, 33760] 6 u20
def t22 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 31516, 33784] 5 Tr.E) [5254, 9265, 10508, 18499, 31516, 42993, 54264] 6 Tr.E) [5254, 9265, 10508, 18499, 31516, 44012, 54264] 6 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 31583, 33760, 54264] 6 Tr.E) [5254, 9265, 10508, 18499, 32379, 33760, 54264] 6 Tr.E)) [5254, 9265, 10508, 18499, 32573, 33760, 54264] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18499, 32573, 33784] 5 Tr.E) [5254, 9265, 10508, 18499, 32670, 33760, 54264] 6 Tr.E) [5254, 9265, 10508, 18503, 21017, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18503, 21018, 33760] 5 Tr.E))) [5254, 9265, 10508, 18503, 21020, 33760] 6 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18503, 21020, 33764] 5 Tr.E) [5254, 9265, 10508, 18503, 21022, 33760] 5 Tr.E) [5254, 9265, 10508, 18503, 21048, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18503, 21080, 33760] 5 Tr.E)) [5254, 9265, 10508, 18503, 21144, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18503, 21272, 33760] 5 Tr.E) [5254, 9265, 10508, 18507, 21017, 33760] 5 Tr.E) [5254, 9265, 10508, 18507, 21018, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18507, 21020, 33760] 5 Tr.E)))) [5254, 9265, 10508, 18507, 21048, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18507, 21080, 33760] 5 Tr.E) [5254, 9265, 10508, 18507, 21144, 33760] 5 Tr.E) [5254, 9265, 10508, 18507, 21272, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18507, 23131, 33768] 5 Tr.E)) [5254, 9265, 10508, 18511, 21020, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18515, 21017, 33760] 5 Tr.E) [5254, 9265, 10508, 18515, 21018, 33760] 5 Tr.E) [5254, 9265, 10508, 18515, 21020, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18515, 21048, 33760] 5 Tr.E))) [5254, 9265, 10508, 18515, 21080, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18515, 21144, 33760] 5 Tr.E) [5254, 9265, 10508, 18515, 21272, 33760] 5 Tr.E) [5254, 9265, 10508, 18515, 22040, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18515, 22174, 33760] 6 Tr.E)) [5254, 9265, 10508, 18515, 22174, 33776] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18523, 22174, 33760] 5 Tr.E) [5254, 9265, 10508, 18523, 30265, 33760] 5 Tr.E) [5254, 9265, 10508, 18531, 21017, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18531, 21018, 33760] 5 Tr.E))))) [5254, 9265, 10508, 18531, 21020, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18531, 21048, 33760] 6 Tr.E) [5254, 9265, 10508, 18531, 21049, 33760] 5 Tr.E) [5254, 9265, 10508, 18531, 21080, 33760] 5 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18531, 21112, 33760] 5 Tr.E) [5254, 9265, 10508, 18531, 21144, 33760] 5 Tr.E)) [5254, 9265, 10508, 18531, 21272, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18547, 21048, 33760] 5 Tr.E) [5254, 9265, 10508, 18547, 22174, 33760] 5 Tr.E) [5254, 9265, 10508, 18627, 21017, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18627, 21018, 33760] 5 Tr.E))) [5254, 9265, 10508, 18627, 21020, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18627, 21048, 33760] 5 Tr.E) [5254, 9265, 10508, 18627, 21080, 33760] 5 Tr.E) [5254, 9265, 10508, 18627, 21144, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 18627, 21146, 33760] 5 Tr.E)) [5254, 9265, 10508, 18627, 21208, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18627, 21272, 33760] 5 Tr.E) [5254, 9265, 10508, 18631, 21148, 33760] 5 Tr.E) [5254, 9265, 10508, 18659, 21176, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18755, 21017, 33760] 5 Tr.E)))) [5254, 9265, 10508, 18755, 21018, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18755, 21020, 33760] 5 Tr.E) [5254, 9265, 10508, 18755, 21048, 33760] 5 Tr.E) [5254, 9265, 10508, 18755, 21080, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18755, 21144, 33760] 5 Tr.E)) [5254, 9265, 10508, 18755, 21272, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 18755, 21336, 33760] 5 Tr.E) [5254, 9265, 10508, 18759, 21276, 33760] 5 Tr.E) [5254, 9265, 10508, 18763, 21272, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 18787, 21304, 33760] 5 Tr.E))) [5254, 9265, 10508, 18883, 21400, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 19011, 21017, 33760] 5 Tr.E) [5254, 9265, 10508, 19011, 21018, 33760] 5 Tr.E) [5254, 9265, 10508, 19011, 21020, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 19011, 21048, 33760] 5 Tr.E)) [5254, 9265, 10508, 19011, 21080, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 19011, 21144, 33760] 5 Tr.E) [5254, 9265, 10508, 19011, 21272, 33760] 5 Tr.E) [5254, 9265, 10508, 19011, 33760, 54264] 6 (Tr.N Tr.E [5254, 9265, 10508, 19011, 33784] 4 Tr.E))))))
def t23 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 19011, 44012, 54264] 5 Tr.E) [5254, 9265, 10508, 19019, 33760, 54264] 5 Tr.E) [5254, 9265, 10508, 19019, 44012, 54264] 5 (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 19027, 22174, 33760] 5 Tr.E) [5254, 9265, 10508, 19027, 33760, 54264] 5 Tr.E)) [5254, 9265, 10508, 19027, 33768] 4 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 19027, 42993, 54264] 5 Tr.E) [5254, 9265, 10508, 19035, 33768] 4 Tr.E) [5254, 9265, 10508, 19035, 33784] 4 (Tr.N Tr.E [5254, 9265, 10508, 19043, 21048, 33760] 5 Tr.E))) [5254, 9265, 10508, 19043, 33760, 54264] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 19139, 21144, 33760] 5 Tr.E) [5254, 9265, 10508, 19139, 33760, 54264] 5 Tr.E) [5254, 9265, 10508, 19267, 21272, 33760] 5 (Tr.N Tr.E [5254, 9265, 10508, 19267, 33760, 54264] 5 Tr.E)) [5254, 9265, 10508, 21017, 26691, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 21017, 26959, 33760] 6 Tr.E) [5254, 9265, 10508, 21017, 26959, 33761] 5 Tr.E) [5254, 9265, 10508, 21018, 23131, 33762] 5 (Tr.N Tr.E [5254, 9265, 10508, 21019, 26959, 33760] 5 Tr.E)))) [5254, 9265, 10508, 21019, 27763, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 21049, 26959, 33760] 5 Tr.E) [5254, 9265, 10508, 21080, 33760, 52195] 6 Tr.E) [5254, 9265, 10508, 21080, 33763] 4 (Tr.N Tr.E [5254, 9265, 10508, 21080, 38886, 52195] 5 Tr.E)) [5254, 9265, 10508, 21080, 42993, 52195] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 21081, 26959, 33760] 5 Tr.E) [5254, 9265, 10508, 21081, 33760, 52195] 5 Tr.E) [5254, 9265, 10508, 21081, 33762] 4 (Tr.N Tr.E [5254, 9265, 10508, 21081, 42993, 52195] 5 Tr.E))) [5254, 9265, 10508, 21082, 33760, 52195] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 21082, 38886, 52195] 5 Tr.E) [5254, 9265, 10508, 21083, 33762] 4 Tr.E) [5254, 9265, 10508, 21083, 33763] 4 (Tr.N Tr.E [5254, 9265, 10508, 21112, 33760, 52195] 5 Tr.E)) [5254, 9265, 10508, 21208, 33760, 52195] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 21336, 33760, 52195] 5 Tr.E) [5254, 9265, 10508, 22174, 23131, 26959, 33760] 6 Tr.E) [5254, 9265, 10508, 22174, 23131, 27763, 33760] 6 (Tr.N Tr.E [5254, 9265, 10508, 22174, 23131, 33760, 52195] 6 Tr.E))))) [5254, 9265, 10508, 22174, 23131, 33762] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 23131, 26959, 30265, 33760] 6 Tr.E) [5254, 9265, 10508, 23131, 26959, 33760, 54264] 6 Tr.E) [5254, 9265, 10508, 23131, 26959, 33768] 5 (Tr.N Tr.E [5254, 9265, 10508, 23131, 27763, 30265, 33760] 6 Tr.E)) [5254, 9265, 10508, 23131, 27763, 33760, 54264] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 23131, 27763, 33768] 5 Tr.E) [5254, 9265, 10508, 23131, 30265, 33760, 52195] 6 Tr.E) [5254, 9265, 10508, 23131, 30265, 33762] 5 (Tr.N Tr.E [5254, 9265, 10508, 23131, 33760, 52195, 54264] 6 Tr.E))) [5254, 9265, 10508, 23131, 33762, 54264] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10508, 23131, 33762, 54266] 5 Tr.E) [5254, 9265, 10508, 23131, 33768, 52195] 5 Tr.E) [5254, 9265, 10508, 23131, 33768, 52203] 5 (Tr.N Tr.E [5254, 9265, 10508, 23131, 33770] 4 Tr.E)) [5254, 9265, 10509, 18499, 21017, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10509, 18499, 21017, 33761] 5 Tr.E) [5254, 9265, 10509, 18499, 21018, 33760] 5 Tr.E) [5254, 9265, 10509, 18499, 21020, 33760] 5 (Tr.N Tr.E [5254, 9265, 10509, 18499, 21048, 33760] 5 Tr.E)))) [5254, 9265, 10509, 18499, 21080, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10509, 18499, 21144, 33760] 5 Tr.E) [5254, 9265, 10509, 18499, 21272, 33760] 5 Tr.E) [5254, 9265, 10509, 21017, 26959, 33760] 5 (Tr.N Tr.E [5254, 9265, 10510, 18499, 21017, 33760] 5 Tr.E)) [5254, 9265, 10510, 18499, 21018, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10510, 18499, 21018, 33762] 5 Tr.E) [5254, 9265, 10510, 18499, 21020, 33760] 5 Tr.E) [5254, 9265, 10510, 18499, 21022, 33760] 5 (Tr.N Tr.E [5254, 9265, 10510, 18499, 21048, 33760] 5 Tr.E))) [5254, 9265, 10510, 18499, 21080, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10510, 18499, 21144, 33760] 5 Tr.E) [5254, 9265, 10510, 18499, 21272, 33760] 5 Tr.E) [5254, 9265, 10510, 21018, 23131, 33760] 5 (Tr.N Tr.E [5254, 9265, 10510, 21081, 33760] 4 Tr.E)) [5254, 9265, 10510, 22174, 23131, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10510, 23131, 30265, 33760] 5 Tr.E) [5254, 9265, 10510, 23131, 33760, 54264] 5 Tr.E) [5254, 9265, 10510, 23131, 33768] 4 (Tr.N Tr.E [5254, 9265, 10511, 18499, 21019, 33760] 5 Tr.E))))))
def u24 : Tr := Tr.N t22 [5254, 9265, 10508, 19011, 42993, 54264] 5 t23
def t25 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10524, 18499, 21018, 33760] 5 Tr.E) [5254, 9265, 10524, 18499, 21020, 33760] 5 Tr.E) [5254, 9265, 10524, 18499, 21048, 33760] 5 (Tr.N (Tr.N Tr.E [5254, 9265, 10524, 18499, 21080, 33760] 5 Tr.E) [5254, 9265, 10524, 18499, 21144, 33760] 5 Tr.E)) [5254, 9265, 10524, 18499, 21272, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10524, 18499, 22040, 33760] 5 Tr.E) [5254, 9265, 10524, 18499, 22174, 33760] 6 Tr.E) [5254, 9265, 10524, 18499, 22174, 33776] 5 (Tr.N Tr.E [5254, 9265, 10524, 18515, 22174, 33760] 5 Tr.E))) [5254, 9265, 10525, 18499, 21017, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10525, 18499, 22174, 33760] 5 Tr.E) [5254, 9265, 10540, 18499, 21017, 33760] 5 Tr.E) [5254, 9265, 10540, 18499, 21018, 33760] 5 (Tr.N Tr.E [5254, 9265, 10540, 18499, 21020, 33760] 5 Tr.E)) [5254, 9265, 10540, 18499, 21048, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10540, 18499, 21080, 33760] 5 Tr.E) [5254, 9265, 10540, 18499, 21144, 33760] 5 Tr.E) [5254, 9265, 10540, 18499, 21272, 33760] 5 (Tr.N Tr.E [5254, 9265, 10540, 18499, 21304, 33760] 5 Tr.E)))) [5254, 9265, 10540, 18531, 21048, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10541, 18499, 21049, 33760] 5 Tr.E) [5254, 9265, 10556, 18499, 21048, 33760] 5 Tr.E) [5254, 9265, 10556, 18499, 22174, 33760] 5 (Tr.N Tr.E [5254, 9265, 10572, 18499, 21017, 33760] 5 Tr.E)) [5254, 9265, 10572, 18499, 21018, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10572, 18499, 21020, 33760] 5 Tr.E) [5254, 9265, 10572, 18499, 21048, 33760] 5 Tr.E) [5254, 9265, 10572, 18499, 21080, 33760] 6 (Tr.N Tr.E [5254, 9265, 10572, 18499, 21144, 33760] 5 Tr.E))) [5254, 9265, 10572, 18499, 21272, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10572, 18499, 21336, 33760] 5 Tr.E) [5254, 9265, 10572, 21080, 33760, 52195] 5 Tr.E) [5254, 9265, 10573, 18499, 21081, 33760] 5 (Tr.N Tr.E [5254, 9265, 10574, 18499, 21082, 33760] 5 Tr.E)) [5254, 9265, 10574, 21017, 33760] 4 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10575, 21083, 33760] 4 Tr.E) [5254, 9265, 10604, 18499, 21112, 33760] 5 Tr.E) [5254, 9265, 10636, 18499, 21017, 33760] 5 (Tr.N Tr.E [5254, 9265, 10636, 18499, 21018, 33760] 5 Tr.E))))) [5254, 9265, 10636, 18499, 21020, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10636, 18499, 21048, 33760] 5 Tr.E) [5254, 9265, 10636, 18499, 21080, 33760] 5 Tr.E) [5254, 9265, 10636, 18499, 21144, 33760] 6 (Tr.N (Tr.N Tr.E [5254, 9265, 10636, 18499, 21148, 33760] 5 Tr.E) [5254, 9265, 10636, 18499, 21272, 33760] 5 Tr.E)) [5254, 9265, 10636, 18499, 21400, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 10636, 18627, 21144, 33760] 5 Tr.E) [5254, 9265, 10638, 18499, 21146, 33760] 5 Tr.E) [5254, 9265, 10668, 18499, 21176, 33760] 5 (Tr.N Tr.E [5254, 9265, 10700, 18499, 21208, 33760] 5 Tr.E))) [5254, 9265, 11020, 18499, 21017, 33760] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 11020, 18499, 21018, 33760] 5 Tr.E) [5254, 9265, 11020, 18499, 21020, 33760] 5 Tr.E) [5254, 9265, 11020, 18499, 21048, 33760] 5 (Tr.N Tr.E [5254, 9265, 11020, 18499, 21080, 33760] 5 Tr.E)) [5254, 9265, 11020, 18499, 21144, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 11020, 18499, 21272, 33760] 5 Tr.E) [5254, 9265, 11020, 18499, 33760, 54264] 6 Tr.E) [5254, 9265, 11020, 18499, 33784] 4 (Tr.N Tr.E [5254, 9265, 11020, 18499, 42993, 54264] 5 Tr.E)))) [5254, 9265, 11020, 18499, 44012, 54264] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 11020, 19011, 33760, 54264] 5 Tr.E) [5254, 9265, 11036, 18499, 22174, 33760] 5 Tr.E) [5254, 9265, 11036, 18499, 33760, 54264] 5 (Tr.N Tr.E [5254, 9265, 11036, 18499, 33784] 4 Tr.E)) [5254, 9265, 11036, 18499, 42993, 54264] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 11052, 18499, 21048, 33760] 5 Tr.E) [5254, 9265, 11052, 18499, 33760, 54264] 5 Tr.E) [5254, 9265, 11084, 18499, 21080, 33760] 5 (Tr.N Tr.E [5254, 9265, 11084, 18499, 33760, 54264] 5 Tr.E))) [5254, 9265, 11084, 52195, 54264] 4 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 11148, 18499, 21144, 33760] 5 Tr.E) [5254, 9265, 11148, 18499, 33760, 54264] 5 Tr.E) [5254, 9265, 11212, 18499, 54264] 4 (Tr.N Tr.E [5254, 9265, 11532, 18499, 21020, 33760] 5 Tr.E)) [5254, 9265, 11581, 18499, 21020, 33760] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 11581, 18499, 21020, 33764] 5 Tr.E) [5254, 9265, 11581, 18499, 21022, 33760] 5 Tr.E) [5254, 9265, 11581, 18499, 21148, 33760] 5 (Tr.N Tr.E [5254, 9265, 11581, 18499, 21276, 33760] 5 Tr.E))))))
def t26 : Tr := (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 11581, 18499, 31516, 33760, 54264] 6 Tr.E) [5254, 9265, 11581, 18499, 31516, 33784] 5 Tr.E) [5254, 9265, 11581, 18503, 21020, 33760] 5 (Tr.N (Tr.N Tr.E [5254, 9265, 11581, 21017, 26959, 33760] 5 Tr.E) [5254, 9265, 15758, 21017, 26959, 33760] 5 Tr.E)) [5254, 9265, 18499, 21272, 33760, 44012] 6 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 18499, 21272, 33772] 4 Tr.E) [5254, 9265, 18499, 21272, 38886, 44012] 5 Tr.E) [5254, 9265, 18499, 21272, 44012, 54264] 5 (Tr.N Tr.E [5254, 9265, 18499, 21276, 33760, 44012] 5 Tr.E))) [5254, 9265, 18499, 21276, 33772] 4 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 18499, 21276, 38886, 44012] 5 Tr.E) [5254, 9265, 18499, 21304, 33760, 44012] 5 Tr.E) [5254, 9265, 18499, 21336, 33760, 44012] 5 (Tr.N Tr.E [5254, 9265, 18499, 21368, 44012] 4 Tr.E)) [5254, 9265, 18499, 21400, 33760, 44012] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 18499, 22174, 31516, 33760, 44012] 6 Tr.E) [5254, 9265, 18499, 22174, 31516, 33772] 5 Tr.E) [5254, 9265, 18499, 23131, 26959, 33768] 5 (Tr.N Tr.E [5254, 9265, 18499, 31516, 33760, 44012, 54264] 6 Tr.E)))) [5254, 9265, 18499, 31516, 44012, 54264] 6 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 18499, 31516, 44012, 55294] 5 Tr.E) [5254, 9265, 18499, 31516, 45053, 54264] 5 Tr.E) [5254, 9265, 18499, 31583, 44012, 54264] 5 (Tr.N Tr.E [5254, 9265, 18499, 32573, 44012, 54264] 5 Tr.E)) [5254, 9265, 18499, 32670, 44012, 54264] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 18755, 21272, 33760, 44012] 5 Tr.E) [5254, 9265, 21017, 26959, 33760, 44012] 5 Tr.E) [5254, 9265, 21017, 26959, 33768] 4 (Tr.N Tr.E [5254, 9265, 21336, 44012, 52195] 4 Tr.E))) [5254, 9265, 23131, 26959, 33760, 33768] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9265, 23131, 26959, 33768] 5 Tr.E) [5254, 9265, 23131, 26959, 33772] 4 Tr.E) [5254, 9265, 23131, 26959, 33784] 4 (Tr.N Tr.E [5254, 9265, 23131, 26959, 44012, 54264] 5 Tr.E)) [5254, 9267, 10508, 21018, 23131, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9267, 10508, 21083, 33760] 4 Tr.E) [5254, 9267, 10508, 22174, 23131, 33760] 5 Tr.E) [5254, 9267, 10508, 23131, 30265, 33760] 5 (Tr.N Tr.E [5254, 9267, 10508, 23131, 30267, 33760] 5 Tr.E))))) [5254, 9267, 10508, 23131, 33760, 54264] 5 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9267, 10508, 23131, 33768] 4 Tr.E) [5254, 9267, 10510, 18499, 21018, 33760] 5 Tr.E) [5254, 9269, 11581, 18499, 21020, 33760] 5 (Tr.N Tr.E [5254, 9273, 10508, 19035, 33760] 4 Tr.E)) [5254, 9273, 10508, 23131, 26959, 33760] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9273, 10508, 23131, 27763, 33760] 5 Tr.E) [5254, 9273, 10508, 23131, 27771, 33760] 5 Tr.E) [5254, 9273, 10508, 23131, 33760, 52195] 5 (Tr.N Tr.E [5254, 9273, 10508, 23131, 33762] 4 Tr.E))) [5254, 9273, 10510, 23131, 33760] 4 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9273, 18499, 23131, 26959, 33760] 5 Tr.E) [5254, 9273, 21017, 26959, 33760] 4 Tr.E) [5254, 9273, 23131, 26959, 33760] 5 (Tr.N Tr.E [5254, 9273, 23131, 26959, 33768] 4 Tr.E)) [5254, 9275, 10508, 23131, 33760] 4 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9277, 18499, 22174, 31516, 33760] 5 Tr.E) [5254, 9277, 23131, 26959, 33760] 4 Tr.E) [5254, 9329, 10508, 21080, 33760, 52195] 5 (Tr.N Tr.E [5254, 9329, 10572, 18499, 21080, 33760] 5 Tr.E)))) [5254, 9331, 10508, 21083, 33760] 4 (Tr.N (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 9393, 10636, 18499, 21144, 33760] 5 Tr.E) [5254, 9521, 18499, 21272, 33760, 44012] 5 Tr.E) [5254, 9529, 23131, 26959, 33760] 4 (Tr.N Tr.E [5254, 9533, 18499, 21276, 33760] 4 Tr.E)) [5254, 9777, 11020, 18499, 33760, 54264] 5 (Tr.N (Tr.N (Tr.N Tr.E [5254, 9785, 23131, 26959, 33760] 4 Tr.E) [5254, 9841, 10508, 52195, 54264] 4 Tr.E) [5254, 10508, 11581, 21017, 26959, 33760] 5 (Tr.N Tr.E [5254, 10508, 13495, 21019, 27763, 33760] 5 Tr.E))) [5254, 10508, 23131, 27763, 42993, 54264] 5 (Tr.N (Tr.N (Tr.N (Tr.N Tr.E [5254, 10508, 23131, 30265, 42993, 52195] 5 Tr.E) [5254, 11581, 18503, 21017, 33760] 4 Tr.E) [5254, 11581, 21017, 26959, 33760] 5 (Tr.N Tr.E [5254, 11581, 21017, 26959, 33761] 4 Tr.E)) [5254, 11581, 21019, 26959, 33760] 4 (Tr.N (Tr.N (Tr.N Tr.E [5254, 11581, 21049, 26959, 33760] 4 Tr.E) [5254, 11581, 21081, 26959, 33760] 4 Tr.E) [5254, 11581, 23131, 26959, 30265, 33760] 5 (Tr.N Tr.E [5255, 11581, 21017, 26959, 33760] 4 Tr.E))))))
def u27 : Tr := Tr.N t25 [5254, 9265, 11581, 18499, 22174, 31516, 33760] 6 t26
def u28 : Tr := Tr.N u24 [5254, 9265, 10524, 18499, 21017, 33760] 5 u27
def u29 : Tr := Tr.N u21 [5254, 9265, 10508, 18499, 31516, 33760, 55294] 6 u28
def tree : Tr := Tr.N u14 [5254, 9265, 10508, 15758, 18499, 21016, 33761] 6 u29

theorem allE_N (t l r : Tr) (k : List ℕ) (v : ℕ) :
    allE t (Tr.N l k v r) = (chkE t k v && allE t l && allE t r) := rfl

theorem allE_E (t : Tr) : allE t Tr.E = true := rfl

set_option maxHeartbeats 400000000 in
theorem ok_t0 : allE tree t0 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t1 : allE tree t1 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u2 : allE tree u2 = true := by
  unfold u2
  rw [allE_N, ok_t0, ok_t1, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t3 : allE tree t3 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t4 : allE tree t4 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u5 : allE tree u5 = true := by
  unfold u5
  rw [allE_N, ok_t3, ok_t4, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u6 : allE tree u6 = true := by
  unfold u6
  rw [allE_N, ok_u2, ok_u5, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t7 : allE tree t7 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t8 : allE tree t8 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u9 : allE tree u9 = true := by
  unfold u9
  rw [allE_N, ok_t7, ok_t8, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t10 : allE tree t10 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t11 : allE tree t11 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u12 : allE tree u12 = true := by
  unfold u12
  rw [allE_N, ok_t10, ok_t11, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u13 : allE tree u13 = true := by
  unfold u13
  rw [allE_N, ok_u9, ok_u12, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u14 : allE tree u14 = true := by
  unfold u14
  rw [allE_N, ok_u6, ok_u13, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t15 : allE tree t15 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t16 : allE tree t16 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u17 : allE tree u17 = true := by
  unfold u17
  rw [allE_N, ok_t15, ok_t16, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t18 : allE tree t18 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t19 : allE tree t19 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u20 : allE tree u20 = true := by
  unfold u20
  rw [allE_N, ok_t18, ok_t19, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u21 : allE tree u21 = true := by
  unfold u21
  rw [allE_N, ok_u17, ok_u20, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t22 : allE tree t22 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t23 : allE tree t23 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u24 : allE tree u24 = true := by
  unfold u24
  rw [allE_N, ok_t22, ok_t23, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t25 : allE tree t25 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_t26 : allE tree t26 = true := by decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u27 : allE tree u27 = true := by
  unfold u27
  rw [allE_N, ok_t25, ok_t26, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u28 : allE tree u28 = true := by
  unfold u28
  rw [allE_N, ok_u24, ok_u27, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_u29 : allE tree u29 = true := by
  unfold u29
  rw [allE_N, ok_u21, ok_u28, Bool.and_true, Bool.and_true]
  decide +kernel

set_option maxHeartbeats 400000000 in
theorem ok_tree : allE tree tree = true := by
  have h : allE tree (Tr.N u14 [5254, 9265, 10508, 15758, 18499, 21016, 33761] 6 u29) = true := by
    rw [allE_N, ok_u14, ok_u29, Bool.and_true, Bool.and_true]
    decide +kernel
  exact h


set_option maxHeartbeats 400000000 in
theorem top_ok : ∀ L ∈ XL.sublists, passes 9 L = true → lookR tree 9 5 L = true := by
  decide +kernel

theorem main : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C, hM, hsize, hf⟩
  have hsz : C.gates.length ≤ 9 := hsize
  have hev : ∀ x, C.eval (List.ofFn x) = W C C.output x := fun x => rfl
  have ho : C.output < 6 + C.gates.length := by
    by_contra hc
    have h1 := (hf (ptE 0 1)).2 ⟨0, 1, by decide, by decide, by decide⟩
    rw [hev, W, List.getD_eq_default _ _ (by rw [wires_len, List.length_ofFn]; omega)] at h1
    cases h1
  have hfun : W C C.output = fun x => decide (∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
    funext x
    rw [← hev]
    exact Bool.eq_iff_iff.2 ((hf x).trans decide_eq_true_iff.symm)
  have hT : val C C.output = T := by
    rw [val, hfun]
    decide +kernel
  have hrun := run_need C hM hT C.gates.length le_rfl
  have hb := need_bound C ho C.gates.length le_rfl
  let S := (List.range 6).filter (fun i => decide (i ∈ need C C.gates.length))
  have p : (need C C.gates.length).toList.Perm S := by
    apply toL_perm (List.Nodup.filter _ List.nodup_range)
    intro w
    constructor
    · intro hw
      have := hb w hw
      exact List.mem_filter.2 ⟨List.mem_range.2 (by omega), decide_eq_true hw⟩
    · intro hw
      exact of_decide_eq_true (List.mem_filter.1 hw).2
  have hmap : S.map (val C) = S.map Xv :=
    List.map_congr_left (fun i hi => val_input C i (List.mem_range.1 (List.mem_filter.1 hi).1))
  have hsub : (S.map Xv).Sublist XL := (List.filter_sublist).map Xv
  have hr : Run C.gates.length (S.map Xv) := by
    rw [← hmap]
    exact Run.perm (p.map (val C)) hrun
  have hr9 : Run 9 (S.map Xv) := Run.mono_le hsz hr
  have hp := hr9.passOk (le_refl 9)
  have hl := top_ok _ (List.mem_sublists.2 hsub) hp
  obtain ⟨j, v, hm, hv⟩ := lookR_sound tree 9 5 _ hl
  exact cert tree ok_tree hr9 j v hm hv

end PEqualNP.Outside.L_meta_743

theorem PEqualNP.Outside.L_meta_743 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) :=
  PEqualNP.Outside.L_meta_743.main
