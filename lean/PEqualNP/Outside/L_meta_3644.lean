import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3644

open PEqualNP.Defs.LratEncoding PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Model : Type := (ℕ → ℕ) × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × (ℕ → ℕ → Bool)

def mOp : Model → ℕ → ℕ
  | (op, _, _, _, _) => op

def mS1 : Model → ℕ → ℕ
  | (_, s1, _, _, _) => s1

def mS2 : Model → ℕ → ℕ
  | (_, _, s2, _, _) => s2

def mSo : Model → ℕ
  | (_, _, _, so, _) => so

def mW : Model → ℕ → ℕ → Bool
  | (_, _, _, _, w) => w

lemma mOp_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) :
    mOp ((a, b, c, d, e) : Model) = a := rfl

lemma mS1_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) :
    mS1 ((a, b, c, d, e) : Model) = b := rfl

lemma mS2_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) :
    mS2 ((a, b, c, d, e) : Model) = c := rfl

lemma mSo_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) :
    mSo ((a, b, c, d, e) : Model) = d := rfl

lemma mW_mk (a b c : ℕ → ℕ) (d : ℕ) (e : ℕ → ℕ → Bool) :
    mW ((a, b, c, d, e) : Model) = e := rfl

def msv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then mW M (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

def Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop :=
  (∀ j < s, mOp M j < 3) ∧
  (∀ j < s, mS1 M j ≤ n + j) ∧
  (∀ j < s, mS2 M j ≤ n + j) ∧
  mSo M ≤ n + s ∧
  (∀ j < s, ∀ r, R r →
    mW M j r = gfun (mOp M j) (msv n M j (mS1 M j) r) (msv n M j (mS2 M j) r)) ∧
  (∀ r, R r → msv n M s (mSo M) r = g r)

def mpad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  mOp M j = 2 ∧ mS1 M j = n + j ∧ mS2 M j = n + j

def mpadB (n : ℕ) (M : Model) (j : ℕ) : Bool :=
  (mOp M j == 2) && (mS1 M j == n + j) && (mS2 M j == n + j)

lemma mpadB_eq_true {n : ℕ} {M : Model} {j : ℕ} : mpadB n M j = true ↔ mpad n M j := by
  simp [mpadB, mpad, and_assoc]

lemma mpadB_eq_false {n : ℕ} {M : Model} {j : ℕ} : mpadB n M j = false ↔ ¬ mpad n M j := by
  rw [← Bool.not_eq_true, mpadB_eq_true]

def NF (n s : ℕ) (M : Model) : Prop :=
  (∀ j, j + 1 < s → mpad n M (j + 1) → mpad n M j) ∧
  (∀ j < s, mOp M j = 2 → mpad n M j) ∧
  (∀ j < s, ¬ mpad n M j → mS1 M j ≠ n + j ∧ mS2 M j ≠ n + j) ∧
  (∀ j < s, ∀ i < j, mpad n M i → mS1 M j ≠ n + i ∧ mS2 M j ≠ n + i) ∧
  (∀ j < s, ¬ mpad n M j → mS1 M j < mS2 M j) ∧
  (∀ j, j + 1 < s → ¬ mpad n M j → ∃ i, j < i ∧ i < s ∧ (mS1 M i = n + j ∨ mS2 M i = n + j)) ∧
  (0 < s → mSo M = n + s - 1 ∨ mpad n M (s - 1))

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then mOp M j == a else if kd = 1 then mS1 M j == a else if kd = 2 then mS2 M j == a
  else if kd = 3 then mW M j a else if kd = 4 then msv n M j (mS1 M j) a
  else if kd = 5 then msv n M j (mS2 M j) a else if kd = 6 then mSo M == a
  else if kd = 7 then mpadB n M j else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

lemma val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

lemma litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

lemma litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

lemma litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

lemma cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

lemma cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by
  simp [ClauseSat]

lemma cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

lemma wd_lt1 {n s a : ℕ} (h : a ≤ n + s + 1) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n)
  unfold wd
  omega

lemma wd_lt2 {n s a : ℕ} (h : a < 2 ^ n) : a < wd n s := by
  unfold wd
  omega

lemma v_op {n s : ℕ} (M : Model) {j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 0 j a + 1) = (mOp M j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]

lemma v_s1 {n s : ℕ} (M : Model) {j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 1 j a + 1) = (mS1 M j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]

lemma v_s2 {n s : ℕ} (M : Model) {j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 2 j a + 1) = (mS2 M j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]

lemma v_w {n s : ℕ} (M : Model) {j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 3 j a + 1) = mW M j a := by
  rw [val_ix n s M hj ha]; simp [meaning]

lemma v_u1 {n s : ℕ} (M : Model) {j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = msv n M j (mS1 M j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]

lemma v_u2 {n s : ℕ} (M : Model) {j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = msv n M j (mS2 M j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]

lemma v_so {n s : ℕ} (M : Model) {a : ℕ} (ha : a < wd n s) :
    val n s M (ix n s 6 0 a + 1) = (mSo M == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]

lemma v_pad {n s : ℕ} (M : Model) {j : ℕ} (hj : j ≤ s) :
    val n s M (ix n s 7 j 0 + 1) = mpadB n M j := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

def msrc (M : Model) (e j : ℕ) : ℕ := if e = 1 then mS1 M j else mS2 M j

lemma v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (msrc M e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

lemma v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = msv n M j (msrc M e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha

lemma src_le {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hv : Valid n s g (· ∈ rows) M) {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) :
    msrc M e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [msrc] using hv.2.1 j hj
  · simpa [msrc] using hv.2.2.1 j hj

lemma s_fOp {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hv : Valid n s g (· ∈ rows) M) : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.1 j hj
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
    [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

lemma s_fSrcAlo {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hv : Valid n s g (· ∈ rows) M) : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨msrc M e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

lemma s_fSrcEq {n s : ℕ} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) :
    ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
      [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he, or_false]
    by_cases hs : msrc M e j = k
    · right; rw [hs]; simp [msv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
        [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w, or_false]
      by_cases hs : msrc M e j = k
      · rw [hs]
        have : msv n M j k r = mW M (k - n) r := by simp [msv, h1, h2]
        rw [this]
        cases mW M (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
      [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : msrc M e j = k
    · right; rw [hs]; simp [msv, h1, h2]
    · left; simp [hs]

lemma gate_fact (t : ℕ) (ht : t < 3) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

lemma s_fGate {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) :
    ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.1 j hj) _ _ _ (hv.2.2.2.2.1 j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
      [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2, or_false] <;>
    assumption

lemma s_fOutAlo {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hv : Valid n s g (· ∈ rows) M) : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.2.2.2.1
  apply cs_of_mem (List.mem_map.2 ⟨mSo M, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

lemma s_fOutEq {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) :
    ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.2.2.2.2.2 r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
        [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : mSo M = k
      · rw [e] at ho
        simp only [msv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
        [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : mSo M = k
      · rw [e] at ho
        simp only [msv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
          [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : mSo M = k
        · rw [e] at ho
          simp only [msv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

lemma s_fOut {n s : ℕ} {M : Model} (hn : NF n s M) :
    ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
      [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq, mpadB_eq_true]
    exact hn.2.2.2.2.2.2 (by omega)

lemma s_fPad {n s : ℕ} {M : Model} (hn : NF n s M) :
    ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.2.1 j hj
  have h2 := hn.2.2.1 j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
      [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad, or_false, beq_iff_eq,
       mpadB_eq_true, Bool.not_eq_true', mpadB_eq_false, beq_eq_false_iff_ne, ne_eq]
    unfold mpad at *
    tauto

lemma s_fPre {n s : ℕ} {M : Model} (hn : NF n s M) :
    ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
    [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false, mpadB_eq_true,
     Bool.not_eq_true', mpadB_eq_false]
  by_cases h : mpad n M (j + 1)
  · exact Or.inr (hn.1 j (by omega) h)
  · exact Or.inl h

lemma s_fPadRd {n s : ℕ} {M : Model} (hn : NF n s M) :
    ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.2.2.2.1 j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
      [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
       Bool.not_eq_true', mpadB_eq_false, beq_eq_false_iff_ne, ne_eq]
    tauto

lemma s_fOrd {n s : ℕ} {M : Model} (hn : NF n s M) :
    ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only
    [cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2, v_pad, or_false,
     Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, mpadB_eq_true]
  by_cases hp : mpad n M j
  · exact Or.inr (Or.inr hp)
  · have := hn.2.2.2.2.1 j hj hp
    omega

lemma s_fUsed {n s : ℕ} {M : Model} (hn : NF n s M) :
    ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : mpad n M j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega), mpadB_eq_true]
    exact hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.2.2.2.2.2.1 j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

lemma enc_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M) :
    ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hn c h
  · exact s_fPad hn c h
  · exact s_fPre hn c h
  · exact s_fPadRd hn c h
  · exact s_fOrd hn c h
  · exact s_fUsed hn c h

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model :=
  (fun j => (code n (gateAt C j) j).1,
   fun j => (code n (gateAt C j) j).2.1,
   fun j => (code n (gateAt C j) j).2.2,
   if C.output < n + C.gates.length then C.output else n + s,
   fun j r => if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true)

lemma xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

lemma xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

lemma code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

lemma code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

lemma wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl]; simp
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

lemma ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : msv n (ofCirc n s C) j k r = (C.wires (xr n r)).getD k false := by
  unfold msv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, mW_mk, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

lemma valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) := by
  refine ⟨fun j _ => (code_le n _ j).1, fun j _ => (code_le n _ j).2.1,
    fun j _ => (code_le n _ j).2.2, ?_, ?_, ?_⟩
  · simp only [ofCirc, mSo_mk]; split_ifs <;> omega
  · intro j hj r _
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          msv n (ofCirc n s C) j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [msv]
      simp only [hS] at h1
      have hw : mW (ofCirc n s C) j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => msv n (ofCirc n s C) j k r)
        (by simp [msv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, mOp_mk, mW_mk, hjl, hga, code, gfun]
  · intro r hr
    rw [← hev r hr, Circuit.eval]
    have hso : mSo (ofCirc n s C) =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [msv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [msv]

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else msv n M d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model :=
  (fun j => if j = 0 then 2 else if j ≤ d then mOp M (j - 1) else mOp M j,
   fun j => if j = 0 then n else if j ≤ d then phi n d (mS1 M (j - 1)) else rd n d t j (mS1 M j),
   fun j => if j = 0 then n else if j ≤ d then phi n d (mS2 M (j - 1)) else rd n d t j (mS2 M j),
   rd n d t s (mSo M),
   fun j r => if j = 0 then true else if j ≤ d then mW M (j - 1) r else mW M j r)

def mRead (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (mS1 M j = n + d ∨ mS2 M j = n + d)) ∨ mSo M = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

lemma sv_shift {n s : ℕ} {M : Model} {d t : ℕ} (hd : d < s) {i k r : ℕ} (hi : i < d)
    (hk : k ≤ n + i) : msv n (mv n s M d t) (i + 1) (phi n d k) r = msv n M i k r := by
  unfold msv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv, mW_mk,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      rw [show k + 1 - n - 1 = k - n by omega]
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

lemma sv_later {n s : ℕ} {M : Model} {d t j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    msv n (mv n s M d t) j (phi n d k) r = msv n M j k r := by
  unfold msv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv, mW_mk,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      rw [show k + 1 - n - 1 = k - n by omega]
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, mW_mk, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

lemma sv_rd {n s : ℕ} {M : Model} {d t : ℕ} (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → mW M d r = tval n M d t r) :
    msv n (mv n s M d t) j (rd n d t j k) r = msv n M j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : msv n M j k r = mW M d r := by
      unfold msv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      rw [show k - n = d by omega]
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [msv]
    · simp [msv, mv, mW_mk, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold msv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

lemma valid_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : mRead n s M d → ∀ r, R r → mW M d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [mv, mOp_mk]; split_ifs
    · omega
    · exact hv.1 _ (by omega)
    · exact hv.1 _ hj
  · intro j hj
    simp only [mv, mS1_mk]; split_ifs with h0 h1
    · omega
    · have := hv.2.1 (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.2.1 j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj
    simp only [mv, mS2_mk]; split_ifs with h0 h1
    · omega
    · have := hv.2.2.1 (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.2.2.1 j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · have := hv.2.2.2.1
    simp only [mv, mSo_mk]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  · intro j hj r hr
    by_cases h0 : j = 0
    · subst h0; simp [mv, mOp_mk, mW_mk, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.2.1 i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.2.2.1 i (by omega))
        simp only [mv, mOp_mk, mS1_mk, mS2_mk, mW_mk, if_neg h0, if_pos h1,
          Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.2.2.2.2.1 i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := mS1 M j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := mS2 M j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, mOp_mk, mS1_mk, mS2_mk, mW_mk, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.2.2.2.2.1 j hj r hr
  · intro r hr
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := mSo M) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv, mSo_mk] at e ⊢
    rw [e]
    exact hv.2.2.2.2.2 r hr

lemma pad_mv0 {n s : ℕ} {M : Model} {d t : ℕ} : mpad n (mv n s M d t) 0 := by
  simp [mpad, mv, mOp_mk, mS1_mk, mS2_mk]

lemma pad_mv_shift {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    mpad n (mv n s M d t) (i + 1) ↔ mpad n M i := by
  have h1 := hv.2.1 i (by omega)
  have h2 := hv.2.2.1 i (by omega)
  simp only [mpad, mv, mOp_mk, mS1_mk, mS2_mk, if_neg (show ¬ i + 1 = 0 by omega),
    if_pos (show i + 1 ≤ d by omega), Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

lemma pad_mv_later {n s : ℕ} {M : Model} {d t j : ℕ} (hj : d < j) (h : mpad n M j) :
    mpad n (mv n s M d t) j := by
  obtain ⟨a, b, c⟩ := h
  simp only [mpad, mv, mOp_mk, mS1_mk, mS2_mk, if_neg (show ¬ j = 0 by omega),
    if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if mpadB n M j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, mS1 M j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

lemma muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

lemma ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.2.1 j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

lemma meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ mpad n M d ∨ ∃ i < d, ¬ mpad n M i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, mpadB_eq_true, pad_mv0]
    · intro i hi
      simp only [ind]
      by_cases h : mpad n M i
      · have h' : mpad n (mv n s M d t) (i + 1) := (pad_mv_shift hv hi hd).2 h
        simp [mpadB_eq_true.2 h, mpadB_eq_true.2 h']
      · have h' : ¬ mpad n (mv n s M d t) (i + 1) := fun hp => h ((pad_mv_shift hv hi hd).1 hp)
        simp [mpadB_eq_false.2 h, mpadB_eq_false.2 h']
    · intro j hj _
      unfold ind
      by_cases h1 : mpad n (mv n s M d t) j
      · simp [mpadB_eq_true.2 h1]
      · have h2 : ¬ mpad n M j := fun h => h1 (pad_mv_later hj h)
        simp [mpadB_eq_false.2 h1, mpadB_eq_false.2 h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, mpadB_eq_false.2 h]
      · right; exact ⟨i, hi, by simp [ind, mpadB_eq_false.2 h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  (mOp M,
   fun i => if i = j then mS2 M j else mS1 M i,
   fun i => if i = j then mS1 M j else mS2 M i,
   mSo M,
   mW M)

lemma valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) := by
  refine ⟨hv.1, ?_, ?_, hv.2.2.2.1, ?_, hv.2.2.2.2.2⟩
  · intro i hi
    simp only [sw, mS1_mk]; split_ifs with h
    · subst h; exact hv.2.2.1 i hi
    · exact hv.2.1 i hi
  · intro i hi
    simp only [sw, mS2_mk]; split_ifs with h
    · subst h; exact hv.2.1 i hi
    · exact hv.2.2.1 i hi
  · intro i hi r hr
    have := hv.2.2.2.2.1 i hi r hr
    have hsv : ∀ k, msv n (sw M j) i k r = msv n M i k r := fun k => rfl
    simp only [hsv]
    simp only [sw, mOp_mk, mS1_mk, mS2_mk, mW_mk]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this

lemma pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : mpad n (sw M j) i ↔ mpad n M i := by
  simp only [mpad, sw, mOp_mk, mS1_mk, mS2_mk]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

lemma meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : mS2 M j < mS1 M j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by
    funext i
    simp only [ind]
    by_cases h : mpad n M i
    · simp [mpadB_eq_true.2 h, mpadB_eq_true.2 ((pad_sw i).2 h)]
    · simp [mpadB_eq_false.2 h, mpadB_eq_false.2 (fun hp => h ((pad_sw i).1 hp))]
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw, mS1_mk]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, mS1_mk, hlt]⟩
  omega

lemma copy_tgt {n : ℕ} {R : ℕ → Prop} {M : Model} {j k : ℕ}
    (hk : k ≤ n + j) (hw : ∀ r, R r → mW M j r = msv n M j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → mW M j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, msv, show ¬ k < n by omega, hk']

lemma const_tgt {n : ℕ} {R : ℕ → Prop} {M : Model} {j : ℕ} (c : Bool)
    (hw : ∀ r, R r → mW M j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → mW M j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

lemma op2_triv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {j : ℕ} (hj : j < s) (h2 : mOp M j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → mW M j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.2.2.2.2.1 j hj r hr, h2]; simp [gfun]

lemma false_src {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {j : ℕ} (hj : j < s)
    (h : (∀ r, R r → msv n M j (mS1 M j) r = false) ∨ (∀ r, R r → msv n M j (mS2 M j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → mW M j r = tval n M j t r := by
  have hop := hv.1 j hj
  have hw := hv.2.2.2.2.1 j hj
  by_cases h0 : mOp M j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : mOp M j = 1
    · rcases h with h | h
      · exact copy_tgt (hv.2.2.1 j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt (hv.2.1 j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

lemma true_src {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {j : ℕ} (hj : j < s)
    (h : (∀ r, R r → msv n M j (mS1 M j) r = true) ∨ (∀ r, R r → msv n M j (mS2 M j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → mW M j r = tval n M j t r := by
  have hop := hv.1 j hj
  have hw := hv.2.2.2.2.1 j hj
  by_cases h0 : mOp M j = 0
  · rcases h with h | h
    · exact copy_tgt (hv.2.2.1 j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt (hv.2.1 j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : mOp M j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

lemma same_src {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {j : ℕ} (hj : j < s) (he : mS1 M j = mS2 M j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → mW M j r = tval n M j t r := by
  have := hv.1 j hj
  by_cases h2 : mOp M j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt (hv.2.1 j hj) fun r hr => ?_
  rw [hv.2.2.2.2.1 j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases msv n M j (mS1 M j) r <;> rfl

lemma pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : mpad n M i) {r : ℕ} (hr : R r) : mW M i r = true := by
  rw [hv.2.2.2.2.1 i hi r hr, hp.1]
  simp [gfun]

lemma exists_nf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas n s M' < meas n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (mRead n s M d → ∀ r, R r → mW M d r = tval n M d t r) →
      (¬ mpad n M d ∨ ∃ i < d, ¬ mpad n M i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ mpad n M d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → mW M d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, mOp M j = 2 → mpad n M j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ mpad n M j → mS1 M j ≠ n + j ∧ mS2 M j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : mS1 M j = n + j ∨ mS2 M j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [msv]
    · exact Or.inr fun r _ => by rw [h]; simp [msv]
  have padRd : ∀ j < s, ∀ i < j, mpad n M i → mS1 M j ≠ n + i ∧ mS2 M j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : mS1 M j = n + i ∨ mS2 M j = n + i := by tauto
    have hnp : ¬ mpad n M j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → msv n M j (n + i) r = true := by
      intro r hr
      unfold msv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ mpad n M j → mS1 M j < mS2 M j := by
    intro j hj hnp
    by_contra hc
    by_cases he : mS1 M j = mS2 M j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas_sw hj (by omega))
  have pre : ∀ j, j + 1 < s → mpad n M (j + 1) → mpad n M j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have hread : ∀ j < s, ¬ mpad n M j → mRead n s M j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine ⟨M, hv, pre, padOp, noF, padRd, ord, ?_, ?_⟩
  · intro j hj hnp
    rcases hread j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : mpad n M (s - 1)
      · have hall : ∀ m, m < s → mpad n M (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by
          have := hall (s - 1 - j) (by omega)
          rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases hread (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : mpad n M (s - 1)
    · exact Or.inr h6
    · rcases hread (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

lemma main_link (n s : ℕ) (rows : List ℕ) (g : ℕ → Bool) (C : Circuit)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ r ∈ rows, C.eval (xr n r) = g r) :
    FormulaSat (enc n s g rows) := by
  have hv := valid_ofCirc n s g (· ∈ rows) C hC hsz hev
  obtain ⟨M, hM, hnf⟩ := exists_nf ⟨_, hv⟩
  exact ⟨val n s M, enc_sat hrows hM hnf⟩

end PEqualNP.Outside.L_meta_3644

theorem PEqualNP.Outside.L_meta_3644 : ∀ (x1 : List ℕ) (x2 : ℕ → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x4 ∈ x1, x4 < (1024 : ℕ)) → PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (14 : ℕ) → (∀ x7 ∈ x1, x3.eval (List.ofFn fun (x9 : Fin (10 : ℕ)) => x7.testBit ↑x9) = x2 x7) → PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc (10 : ℕ) (14 : ℕ) x2 x1) := by
  intro x1 x2 x3 hrows hC hsz hev
  exact PEqualNP.Outside.L_meta_3644.main_link 10 14 x1 x2 x3 hrows hC hsz hev
