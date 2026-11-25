import PEqualNP.Defs
import PEqualNP.Library.LRAT.LinkN2

-- Adapted from PEqualNP.Library.LRAT.Link and Link2.
namespace PEqualNP.Outside.V_meta_9689__k6_aux

open PEqualNP.Library.LRAT

structure Model where
  op : ℕ → ℕ
  s1 : ℕ → ℕ
  s2 : ℕ → ℕ
  so : ℕ
  w : ℕ → ℕ → Bool

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

structure Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop where
  op_lt : ∀ j < s, M.op j < 3
  s1_le : ∀ j < s, M.s1 j ≤ n + j
  s2_le : ∀ j < s, M.s2 j ≤ n + j
  so_le : M.so ≤ n + s
  w_eq : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)
  out_eq : ∀ r, R r → M.sv n s M.so r = g r

def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

local instance (n : ℕ) (M : Model) (j : ℕ) : Decidable (M.pad n j) := by
  unfold Model.pad; infer_instance

structure NF (n s : ℕ) (M : Model) : Prop where
  pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j
  padOp : ∀ j < s, M.op j = 2 → M.pad n j
  noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j
  noPadRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i
  ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j
  used : ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)
  out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1)

section formula
variable (n s : ℕ)

def wd : ℕ := 2 ^ n + n + s + 1

def ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd n s + a

def P (v : ℕ) : ℕ := 2 * v + 2

def Q (v : ℕ) : ℕ := 2 * v + 3

def L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v

def pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun b => (List.range b).map fun a => (a, b)

def fOp : List (List ℕ) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)]

def fSrcAlo : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)

def srcEq (e j k r : ℕ) : List (List ℕ) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

def gateCl (j r : ℕ) : List (List ℕ) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)]]

def fGate (rows : List ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r

def fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]

def outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

def fOut : List (List ℕ) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

def fPad : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

def fPre : List (List ℕ) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

def fPadRd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

def fOrd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l => [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)]

def fUsed : List (List ℕ) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s

end formula

def rowFun (n : ℕ) (f : (Fin n → Bool) → Bool) (r : ℕ) : Bool := f fun i => r.testBit i

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then decide (M.pad n j) else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

theorem val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
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

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

theorem cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

theorem wd_lt1 (h : a ≤ n + s + 1) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
theorem wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

theorem v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
theorem v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = decide (M.pad n j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

theorem v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

theorem v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha


section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

theorem src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

theorem s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

theorem s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
theorem gate_fact (t : ℕ) (ht : t < 3) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
theorem s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

theorem s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

include hn

theorem s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

theorem s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    tauto

theorem s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

theorem s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    tauto

theorem s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2, v_pad, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases hp : M.pad n j
  · exact Or.inr (Or.inr hp)
  · have := hn.ord j hj hp
    omega

theorem s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
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

include hrows in

theorem enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows hv c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hv hn c h
  · exact s_fPad hv hn c h
  · exact s_fPre hv hn c h
  · exact s_fPadRd hv hn c h
  · exact s_fOrd hv hn c h
  · exact s_fUsed hv hn c h

end sound

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

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

def ofCirc (n s : ℕ) (C : Circuit) : Model where
  op j := (code n (gateAt C j) j).1
  s1 j := (code n (gateAt C j) j).2.1
  s2 j := (code n (gateAt C j) j).2.2
  so := if C.output < n + C.gates.length then C.output else n + s
  w j r := if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
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
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) where
  op_lt j _ := (code_le n _ j).1
  s1_le j _ := (code_le n _ j).2.1
  s2_le j _ := (code_le n _ j).2.2
  so_le := by simp only [ofCirc]; split_ifs <;> omega
  w_eq j hj r _ := by
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, hjl, hga, code, gfun]
  out_eq r hr := by
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model where
  op j := if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j
  s1 j := if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j)
  s2 j := if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j)
  so := rd n d t s M.so
  w j r := if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) where
  op_lt j hj := by
    simp only [mv]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  s1_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  s2_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  so_le := by
    have := hv.so_le
    simp only [mv]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  w_eq j hj r hr := by
    by_cases h0 : j = 0
    · subst h0; simp [mv, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, if_neg h0, if_pos h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  out_eq r hr := by
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, M.s1 j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
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

theorem ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.s1_le j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  { M with s1 := fun i => if i = j then M.s2 j else M.s1 i,
           s2 := fun i => if i = j then M.s1 j else M.s2 i }

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) where
  op_lt := hv.op_lt
  s1_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  so_le := hv.so_le
  w_eq i hi r hr := by
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  out_eq r hr := hv.out_eq r hr

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

theorem meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, hlt]⟩
  omega

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem same_src (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

theorem exists_nf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
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
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas_sw hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine ⟨M, hv, {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }⟩
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by have := hall (s - 1 - j) (by omega); rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem link (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf⟩ := exists_nf ⟨_, hv⟩
  exact ⟨val n s M, enc_sat hrows hM hnf⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem lower_of_unsat (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc n s (rowFun n f) rows)) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link n s f rows hrows C hC (by omega) hev)

theorem sat_of_check (a : ℕ → Bool) (F : List (List ℕ))
    (h : F.all (fun c => c.any fun l => litVal a l) = true) : FormulaSat F := by
  refine ⟨a, fun c hc => ?_⟩
  have := List.all_eq_true.1 h c hc
  obtain ⟨l, hl, hv⟩ := List.any_eq_true.1 this
  exact ⟨l, hl, hv⟩


def lexWord (B : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => lexWord B a m * B + a m

theorem lexWord_lt {B : ℕ} {a : ℕ → ℕ} : ∀ m, (∀ i < m, a i < B) → lexWord B a m < B ^ m
  | 0, _ => by simp [lexWord]
  | m + 1, h => by
    have ih := lexWord_lt m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    have h2 : (lexWord B a m + 1) * B ≤ B ^ m * B := Nat.mul_le_mul_right _ ih
    rw [Nat.add_mul, Nat.one_mul] at h2
    simp only [lexWord, pow_succ]
    omega

theorem lexWord_congr {B : ℕ} {a b : ℕ → ℕ} :
    ∀ m, (∀ i < m, a i = b i) → lexWord B a m = lexWord B b m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [lexWord, lexWord_congr m (fun i hi => h i (by omega)), h m (by omega)]

theorem lexWord_lt_of {B : ℕ} {a b : ℕ → ℕ} {j : ℕ} (hab : ∀ i < j, a i = b i) (hj : b j < a j) :
    ∀ m, j < m → (∀ i < m, b i < B) → lexWord B b m < lexWord B a m
  | 0, h, _ => by omega
  | m + 1, hjm, hb => by
    by_cases h : m = j
    · subst h
      simp only [lexWord, lexWord_congr m hab]
      omega
    · have ih := lexWord_lt_of hab hj m (by omega) (fun i hi => hb i (by omega))
      have hm := hb m (by omega)
      have h2 : (lexWord B b m + 1) * B ≤ lexWord B a m * B := Nat.mul_le_mul_right _ ih
      rw [Nat.add_mul, Nat.one_mul] at h2
      simp only [lexWord]
      omega

def lexKey (n s : ℕ) (M : Model) (j : ℕ) : ℕ := M.s1 j * (3 * (n + s + 1)) + M.s2 j * 3 + M.op j

def lexB (n s : ℕ) : ℕ := 3 * (n + s + 1) * (n + s + 1)

theorem lex3 (K x1 y1 z1 x2 y2 z2 : ℕ) (hy : y1 * 3 + z1 < K) (hz : z1 < 3)
    (h : x1 < x2 ∨ (x1 = x2 ∧ (y1 < y2 ∨ (y1 = y2 ∧ z1 < z2)))) :
    x1 * K + y1 * 3 + z1 < x2 * K + y2 * 3 + z2 := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have : (x1 + 1) * K ≤ x2 * K := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega
  · omega

section keys
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}

theorem lexKey_lt (hv : Valid n s g R M) {j : ℕ} (hj : j < s) : lexKey n s M j < lexB n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  have : M.s1 j * (3 * (n + s + 1)) ≤ (n + s) * (3 * (n + s + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (n + s) * (3 * (n + s + 1)) + 3 * (n + s + 1) = 3 * (n + s + 1) * (n + s + 1) := by
    ring
  unfold lexKey lexB
  omega

def meas2 (n s : ℕ) (M : Model) : ℕ :=
  lexB n s ^ s * muf s (ind n M) + lexWord (lexB n s) (lexKey n s M) s

theorem lexWord_lt_pow (hv : Valid n s g R M) :
    lexWord (lexB n s) (lexKey n s M) s < lexB n s ^ s :=
  lexWord_lt s fun _ hi => lexKey_lt hv hi

end keys

theorem meas2_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas2 n s (mv n s M d t) < meas2 n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := lexWord_lt_pow hv'
  have : lexB n s ^ s * muf s (ind n (mv n s M d t)) + lexB n s ^ s ≤
      lexB n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  unfold meas2
  omega

theorem meas2_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}
    (hv : Valid n s g R M) (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas2 n s (sw M j) < meas2 n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas2
  rw [hind]
  have hk : lexKey n s (sw M j) j < lexKey n s M j := by
    have h1 := hv.s1_le j hj
    have : (M.s2 j + 1) * (3 * (n + s + 1)) ≤ M.s1 j * (3 * (n + s + 1)) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [lexKey, sw, if_pos rfl, ↓reduceIte]
    omega
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (sw M j)) (j := j)
    (fun i hi => by simp [lexKey, sw, show i ≠ j by omega]) hk s hj
    (fun i hi => lexKey_lt (valid_sw hv j) hi)
  omega

def tsw (n j k : ℕ) : ℕ := if k = n + j then n + j + 1 else if k = n + j + 1 then n + j else k

def xsw (n : ℕ) (M : Model) (j : ℕ) : Model where
  op i := if i = j then M.op (j + 1) else if i = j + 1 then M.op j else M.op i
  s1 i := if i = j then M.s1 (j + 1) else if i = j + 1 then M.s1 j
    else if j + 1 < i then tsw n j (M.s1 i) else M.s1 i
  s2 i := if i = j then M.s2 (j + 1) else if i = j + 1 then M.s2 j
    else if j + 1 < i then tsw n j (M.s2 i) else M.s2 i
  so := tsw n j M.so
  w i r := if i = j then M.w (j + 1) r else if i = j + 1 then M.w j r else M.w i r

section xsw
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}

theorem sv_xsw_low {i i' k r : ℕ} (hk : k < n + j) (hi : j ≤ i) (hi' : j ≤ i') :
    (xsw n M j).sv n i k r = M.sv n i' k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · simp only [if_neg h6, if_pos (show k < n + i by omega), if_pos (show k < n + i' by omega),
      xsw, if_neg (show k - n ≠ j by omega), if_neg (show k - n ≠ j + 1 by omega)]

theorem sv_xsw_early {i k r : ℕ} (hi : i < j) : (xsw n M j).sv n i k r = M.sv n i k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
        if_neg (show k - n ≠ j + 1 by omega)]
    · simp only [if_neg h6, if_neg h7]

theorem sv_xsw_late {i k r : ℕ} (hi : j + 1 < i) :
    (xsw n M j).sv n i (tsw n j k) r = M.sv n i k r := by
  unfold tsw
  by_cases h1 : k = n + j
  · subst h1
    simp only [if_pos rfl, ↓reduceIte]
    unfold Model.sv
    simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
      if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
      show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega,
      if_neg (show j + 1 ≠ j by omega), if_pos rfl, ↓reduceIte]
  · by_cases h2 : k = n + j + 1
    · subst h2
      simp only [if_neg h1, if_pos rfl, ↓reduceIte]
      unfold Model.sv
      simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
        if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
        show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega, if_pos rfl, ↓reduceIte]
    · simp only [if_neg h1, if_neg h2]
      unfold Model.sv
      by_cases h6 : k < n
      · simp [h6]
      · by_cases h7 : k < n + i
        · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
            if_neg (show k - n ≠ j + 1 by omega)]
        · simp only [if_neg h6, if_neg h7]

theorem tsw_le {i k : ℕ} (hi : j + 1 ≤ i) (hk : k ≤ n + i) : tsw n j k ≤ n + i := by
  unfold tsw; split_ifs <;> omega

theorem tsw_eq_iff {i k : ℕ} (hi : j + 1 < i) : tsw n j k = n + i ↔ k = n + i := by
  unfold tsw; split_ifs <;> omega

variable (hv : Valid n s g R M) (hj : j + 1 < s) (h1 : M.s1 j < n + j) (h2 : M.s2 j < n + j)
  (h3 : M.s1 (j + 1) < n + j) (h4 : M.s2 (j + 1) < n + j)
include hv hj h1 h2 h3 h4

theorem valid_xsw : Valid n s g R (xsw n M j) where
  op_lt i hi := by
    simp only [xsw]; split_ifs
    · exact hv.op_lt _ hj
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hi
  s1_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s1_le i hi)
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s2_le i hi)
    · exact hv.s2_le i hi
  so_le := tsw_le (by omega) hv.so_le
  w_eq i hi r hr := by
    by_cases a : i = j
    · subst a
      have e1 : (xsw n M i).s1 i = M.s1 (i + 1) := by simp [xsw]
      have e2 : (xsw n M i).s2 i = M.s2 (i + 1) := by simp [xsw]
      have e3 : (xsw n M i).op i = M.op (i + 1) := by simp [xsw]
      have e4 : (xsw n M i).w i r = M.w (i + 1) r := by simp [xsw]
      rw [e1, e2, e3, e4, sv_xsw_low h3 le_rfl (Nat.le_succ i),
        sv_xsw_low h4 le_rfl (Nat.le_succ i)]
      exact hv.w_eq (i + 1) hj r hr
    · by_cases b : i = j + 1
      · subst b
        have e1 : (xsw n M j).s1 (j + 1) = M.s1 j := by simp [xsw]
        have e2 : (xsw n M j).s2 (j + 1) = M.s2 j := by simp [xsw]
        have e3 : (xsw n M j).op (j + 1) = M.op j := by simp [xsw]
        have e4 : (xsw n M j).w (j + 1) r = M.w j r := by simp [xsw]
        rw [e1, e2, e3, e4, sv_xsw_low h1 (Nat.le_succ j) le_rfl,
          sv_xsw_low h2 (Nat.le_succ j) le_rfl]
        exact hv.w_eq j (by omega) r hr
      · by_cases c : j + 1 < i
        · have e1 : (xsw n M j).s1 i = tsw n j (M.s1 i) := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = tsw n j (M.s2 i) := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_late c, sv_xsw_late c]
          exact hv.w_eq i hi r hr
        · have e1 : (xsw n M j).s1 i = M.s1 i := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = M.s2 i := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_early (by omega), sv_xsw_early (by omega)]
          exact hv.w_eq i hi r hr
  out_eq r hr := by
    have e : (xsw n M j).so = tsw n j M.so := rfl
    rw [e, sv_xsw_late hj]
    exact hv.out_eq r hr

omit hv hj in
theorem ind_xsw : ind n (xsw n M j) = ind n M := by
  funext i
  unfold ind
  have hp : (xsw n M j).pad n i ↔ M.pad n i := by
    by_cases a : i = j
    · subst a
      simp only [Model.pad, xsw, if_pos rfl, ↓reduceIte]
      omega
    · by_cases b : i = j + 1
      · subst b
        simp only [Model.pad, xsw, if_neg a, if_pos rfl, ↓reduceIte]
        omega
      · by_cases c : j + 1 < i
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_pos c, tsw_eq_iff c]
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_neg c]
  by_cases h : M.pad n i
  · simp [h, hp.2 h]
  · have h' : ¬ (xsw n M j).pad n i := fun h' => h (hp.1 h')
    simp [h, h']

theorem meas2_xsw (hlt : lexKey n s M (j + 1) < lexKey n s M j) :
    meas2 n s (xsw n M j) < meas2 n s M := by
  unfold meas2
  rw [ind_xsw h1 h2 h3 h4]
  have hk : lexKey n s (xsw n M j) j = lexKey n s M (j + 1) := by simp [lexKey, xsw]
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (xsw n M j))
    (j := j)
    (fun i hi => by
      simp [lexKey, xsw, show i ≠ j by omega, show i ≠ j + 1 by omega,
        show ¬ j + 1 < i by omega])
    (by rw [hk]; exact hlt) s (by omega)
    (fun i hi => lexKey_lt (valid_xsw hv hj h1 h2 h3 h4) hi)
  omega

end xsw

def LexNF (n s : ℕ) (M : Model) : Prop :=
  ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j →
    M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ (M.s2 j < M.s2 (j + 1) ∨
      (M.s2 j = M.s2 (j + 1) ∧ M.op j = 0 ∧ M.op (j + 1) = 1)))

theorem nf_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas2_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas2_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
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
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

theorem lex_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : LexNF n s M := by
  have hnf := nf_of_min2 hv hmin
  intro j hj hnp ha hb
  have hnp1 : ¬ M.pad n (j + 1) := fun h => hnp (hnf.pre j hj h)
  have f0 := hnf.noF j (by omega) hnp
  have f1 := hnf.noF (j + 1) hj hnp1
  have l1 := hv.s1_le j (by omega)
  have l2 := hv.s2_le j (by omega)
  have l3 := hv.s1_le (j + 1) hj
  have l4 := hv.s2_le (j + 1) hj
  have h1 : M.s1 j < n + j := by omega
  have h2 : M.s2 j < n + j := by omega
  have h3 : M.s1 (j + 1) < n + j := by omega
  have h4 : M.s2 (j + 1) < n + j := by omega
  have o0 := hv.op_lt j (by omega)
  have o1 := hv.op_lt (j + 1) hj
  have o0' : M.op j ≠ 2 := fun h => hnp (hnf.padOp j (by omega) h)
  have o1' : M.op (j + 1) ≠ 2 := fun h => hnp1 (hnf.padOp (j + 1) hj h)
  -- a strictly smaller key at `j + 1` contradicts minimality through `xsw`
  have hx : lexKey n s M (j + 1) < lexKey n s M j → False := fun hlt =>
    hmin _ (valid_xsw hv hj h1 h2 h3 h4) (meas2_xsw hv hj h1 h2 h3 h4 hlt)
  have hK : ∀ y z : ℕ, y < n + j → z < 3 → y * 3 + z < 3 * (n + s + 1) := by
    intro y z hy hz; omega
  by_contra hc
  rcases lt_trichotomy (M.s1 j) (M.s1 (j + 1)) with e1 | e1 | e1
  · exact hc (Or.inl e1)
  · rcases lt_trichotomy (M.s2 j) (M.s2 (j + 1)) with e2 | e2 | e2
    · exact hc (Or.inr ⟨e1, Or.inl e2⟩)
    · by_cases e3 : M.op j = M.op (j + 1)
      · -- gate `j + 1` is a copy of wire `n + j`
        have hw : ∀ r, R r → M.w (j + 1) r = M.sv n (j + 1) (n + j) r := by
          intro r hr
          have hs : ∀ k, k < n + j → M.sv n (j + 1) k r = M.sv n j k r := by
            intro k hk
            unfold Model.sv
            by_cases h6 : k < n
            · simp [h6]
            · simp only [if_neg h6, if_pos hk, if_pos (show k < n + (j + 1) by omega)]
          rw [hv.w_eq (j + 1) hj r hr, hs _ h3, hs _ h4, ← e1, ← e2, ← e3,
            ← hv.w_eq j (by omega) r hr]
          unfold Model.sv
          simp only [if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
            show n + j - n = j by omega]
        obtain ⟨t, ht, htw⟩ := copy_tgt hv hj (k := n + j) (by omega) hw
        have hv' := valid_mv hv hj ht (fun _ => htw)
        exact hmin _ hv' (meas2_mv hv hv' hj (Or.inl hnp1))
      · have : M.op j = 0 ∧ M.op (j + 1) = 1 ∨ M.op (j + 1) < M.op j := by omega
        rcases this with h | h
        · exact hc (Or.inr ⟨e1, Or.inr ⟨e2, h⟩⟩)
        · apply hx
          unfold lexKey
          exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inr ⟨e2.symm, h⟩⟩)
    · apply hx
      unfold lexKey
      exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inl e2⟩)
  · apply hx
    unfold lexKey
    exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inl e1)

theorem exists_nf2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M ∧ LexNF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas2 n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  exact ⟨M, hv, nf_of_min2 hv hmin, lex_of_min2 hv hmin⟩

section formula
variable (n s : ℕ)

def lexBase (j : ℕ) : List ℕ :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

def fLex : List (List ℕ) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

def enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc n s g rows ++ fLex n s

end formula

theorem s_fLex {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hn : NF n s M) (hl : LexNF n s M) : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have hj1 : j + 1 < s := Nat.add_lt_of_lt_sub hj
  have hj0 : j < s := Nat.lt_of_succ_lt hj1
  have hb1 : ClauseSat (val n s M) (lexBase n s j) ↔
      M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j := by
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [lexBase, cs_cons, cs_nil, litVal_P, v_pad, v_s1, v_s2, or_false,
      beq_iff_eq, decide_eq_true_eq]
  have happ : ∀ c', ClauseSat (val n s M) (lexBase n s j) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_right _ hl', hv'⟩
  have hfront : ∀ c', (∃ l ∈ c', litVal (val n s M) l = true) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_left _ hl', hv'⟩
  by_cases hesc : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j
  · rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
      exact happ _ (hb1.2 hesc)
  have hnp : ¬ M.pad n j := fun h => hesc (Or.inl h)
  have L := hl j hj1 hnp (fun h => hesc (Or.inr (Or.inl h)))
    (fun h => hesc (Or.inr (Or.inr h)))
  have hop0 := hn.padOp j hj0
  rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;> apply hfront <;>
    simp (disch := first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption)) only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litVal_Q, v_s1, v_s2, v_op, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] <;> omega

theorem enc2_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
    (hl : LexNF n s M) : ∀ c ∈ enc2 n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact enc_sat hrows hv hn c h
  · exact s_fLex hv hn hl c h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem link2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc2 n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact ⟨val n s M, enc2_sat hrows hM hnf hlx⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem lower_of_unsat2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc2 n s (rowFun n f) rows)) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link2 n s f rows hrows C hC (by omega) hev)


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def target (x : Fin 4 → Bool) : Bool := (429 : ℕ).testBit (tableIndex x)

def g (r : ℕ) : Bool := (429 : ℕ).testBit (r % 16)


def rows : List ℕ := [75,105,165,225,90,60,135,120,15,240,45,150,195,180,210,30]

def F : List (List ℕ) := enc2 8 5 g rows

set_option maxRecDepth 6000 in
def c_Kw_0 : List Nat := [
11235582637031225554290608446582155387050310764075436689304785376286474913826327064907940915686548666968416760505835601733282906348708674584977863141202497374433693014530503175008295545704980076814230574378680215123356744792198358895972202953852068582611475140577553613827328431621789651799764595551718408193,
11235582971861378755793069157936328343741381748123376025482969122910855472314818598521909761462464398862151415546713698816636970294877178387239692481824633881129628450853210367433244383456984965132245766193121954585051688265629070729501901394677901411378949992287466390364116231725267504638854942561318993920,
11235582092889474423343846928315236168097958994956555047270937587082619621496304777952400346247904365379355133753975612498748502939130656081821275328453008682545985329901005152895546305189339456712987063483495164733641648851617536312821768168873703998340861213082275895071950009719586761718924883494594150485,
11289757568118947607630823390441512302407472837625686287783586767591727105770129709862616737522252161729717511239767391801409853022563358732325702864151780087797889684278448840658021561299724957666943730954148407351428306792218406017249089846428451601558282597136025322783198350485453782251016489076965507193,
11298674434641799772705320945404821459308959999349556249319144795645502947796146608990613383519529547267864977292680017694425578554399150946840428780935759702128518240337982986883564510558848606056210657384319461706078474894766185866908901325589738693427382146105843091724218082722532742100227621352267317248,
11235582092962604234248616794358167183475961303985856666104195023252762716985318644980332523169147614916959545011016587460694871578871476121063275082712394702895265058613509974973104709335621688889237464005567110524955185165395036432540482562779790798834293015514964590110105593312253490373865368447488950457,
11235582092889474423308159811275480957087171395867181124835634348393453299560489766666102998520923269985684188891633624572875435959207993167060541663264467295658537937617890844436247042177072404812395671184087053345298667592204055485221229406025970696378658036813512461698151702477015099625988288420347314176,
11333989443373461214149118166102004342586366954836417375975549755657945751209085109170398459137892683262978093871956669204192215387646576974892925994503101424878915385847562134077178633689166855103875382977926189257092490252188978859148427064211055092821012771323427877859547306999012253354642100110953021440,
11235582092994857997957451676144819744614621662687524801829028015213122782061147262024127315212399477221406129863953828112453169522851191642216380163341054334250154404730213508762458736974643875108840530379548925692015996419225091938851905022653216236889138685961268210720790797318927803616791132755680297248,
11360052320650580858637363594158125006962837842762553197384551233392076819702257139513013908483050107722452555834434859805797663321185365080532980540908834720766180686557463693177951861593456040908740920867637079833144226219318371426798732452880013575108666667170577151998727879292703851705420657972398260555,
11371367796978676602538457112486120575193033351883340499012727704606442024277545483371644906105720779556040327336310930094670258921417291042330010020040159802554101075142222435919611831782793661023924836635500178418800432186744683373054442778869420507066755029543150839332866082175601960468140362490816397676,
11235582093023275557783679672269090503313667011307232755262342212896321212002453569199636604130636272398808312071745368542505393416793642073977044938340552198431955557342586748144963231142927153661160422578267064693142774034682317185359485714881979121733707078723354275016500404775911579463770615635696320512,
11390222215222297025487468090456394161237241385997316875038217611500771278790778089867795772498028806819500669008981629862643074142737843238516021952053117384613341973328927969710634952215553657631845607936241763957693278292994986967018118552731089353158939623879855883397238601036063151924822337575542849536,
11235582092889479110804201282325815339943638101292166703923407435291557070759927121014567406143978505359911643368469259686984337629443260165610124242646777404925971218082481405570404269275742787142190977813498856938004601974673647508351868033132193691495400671025549660021885436662202954749958142090526326784,
11235582093048822313769516356416094881696511997677720518025312915880612350957746632483897472513855613829090194954803016170508316369254402805409663114842455551793731308938855456453078118661480912999906293879199814416000868618481587904879286814983778864227705383141254651861493815974023757723455092376922488832,
11416286808611375557097995014841193636602655169170118764688966124367866563505636400720664257734309003684081013128104210729493741739451557743332151718543401817661430954786928486185287672315750845248869179720464085981211938261856981861390026230551806583376347563762371080751709734617200724325269320547585490944,
11427945177864248682664230143938143157173438597412734866687995281615980300728081538498034602768933457324872611919102768791513048058987810478787697033792556904390021413899030085336203249784413269519988650506203452218556814898420333774336367895352107177000192185781734030391512805137735390769670000606116872720,
11235588266620707234984498991764665662349902001961071252140000496597217269889746547497703074517795302743070043671692260326848875757361973279978518984548402856696821198738621785781157442569813967802432322022344746472573805061634298994616054085917459839909239763495473771364443221946842939954942725511062323762,
11235582093090341912116930803649595197364589500039035387838730884154176187180969790093602401410665142880885112430045797696116922338730262495308359260822216007765766736456684172634357467325171510091525415352013996010009306446564923976210035685330269015529977601549836114787994397581558752769369150718986420815,
11235588894457781758012831431457594907556887587612853050692683436208813767235605380739124851941091735838274722239337670315759110628880306822969674318290299421048147617137046648041239590057688156411349783397916746469569010556013305498294788726041270852143184063608365759434163719012891756626563354063705997312,
11235582093109502564011627147239575607609458210817432908025731427411081347538081725396523592001106998237191056775154509334316162586752688799465282202031560444894264896074901036500614730293542490603900530138991631542705973088742518162997986448434066620288157017238561992036911007482504122973520856392679817216,
11484514972510988047310902130151991000520837792492169087180519187938447693119432178026108834442487287471542551435496604834283408938840837168108938072046455290328275336376988162217115867889377354198408163810980547716410603648791991224856020647734676831667736930486371585601857469182090760416036728940181585920,
11235589993172669521585735671646620113129158491032242485954640779553709821901988793658446403791218432349674255876530750450975453392030994949359201499810333193053212774313296100683829526325764496634846771037811141698688364607097982107408327208615034170875821039482709425294984907714700049060348484855068098560,
11506116586031870875808663925071407148779494574271581858398737304524971429526044134204319651975368229268251356335242206315819902831692409690032658989214446882815387634613305565677743840375221677892993102709797865073370894804174411481842373878272618102398251639417404014728832440683578104793772356863113428992,
11519497667401003286258904180523935586765061603031051484800444235642330926559440318417569754642419644562793323876004705976741759449999179810999057854235627239048486027410616973329509334524954254272901393307617595729629922821982620166138829432594626938045254600054989748560356073138631128353141118863091139350,
11529098677520960343407168394274598012845788161323287773550418213491299732795358576329131198056597020342105617417541587482667633278400690592949515699757991434556232538882396556331681303289369235489989327438294582509366522239566980537803049488738488753417564008822276041381285723356439084628982486369803633469,
11235591290702624744625257046264309254759907714078551368304903725093722669957557175156911000548924587930847169782942773913461177938525878740285923161724989721809929437937843160762823325266111301540858644473358996869067677307247966250562310421337420710014794290204386653891890125650666772250544893412757209945,
11235582092889474423308157442431404585343484975761269624868528728445769967086724978328738454536761330123687247477866640237386150921495000056625458448075349203170732217879178482169329461612714818537837169023304755732158202550811879809377451127384595068785724759748354793245827009067871560743855513301688517488,
11235582092889474423308157442431404585112356118389416079589380072548753206131112327475660465715915368880625728344420774618005545330381192198032897535235553531875388924045436966307237154560761895262724294733159404698822774012457021549212862336010980537852851341328319776088254159856441944267806921621002847105,
11553777289175531401647191387465135923574294787392615710603663250437371042995483226174795859273357798076091618228566730123089505415034179503252622684512178553700953254946443708600814224433697942347055493833588808721249226503682498899893003688309530479475021805619468278675413401791645929863472418429811557267,
11235592013017670832972391386497759351793383052387836000361680149411357413433047702360564575561955445834826970567390858829465910510440582687572095083053529781534350279063958076671782711012285741404210083030857091139557313269976394683807296211168679211750050870765525465144442939929328074744840687822128054272,
11575389262027944547936227396052030293332561921406010155324066351099743595774792289016177239664432930446227361862762682216748761175027317537745648390401888850953929985801040787600796938671441187793512079547666788557581094771355203285534758756819031968412280389824295969257249561812860297063057843172350263296,
11235592849831351254500376736522728107564899874131058839522899287339896548817018976789960838562135154059884969271681146480168555631171511952048082826676005259697823264537565211709364935895125842730260876720500291751766293016111410547127765343817214344081352569726920254969003175333052979071052881167319565280,
11235593247461498452223832450702008162719098879854790600285068868754296106730840467997811429262735844717678820380685160276997577992086001094417051197568267171181010365685919906686000931680307441509772637573422829897480320098790490102221318358149916728561525071494863764556701596116064757245117600975739356165,
11616879341474937754639346511511272818106744002798388685984160559842041300222275253409202591766792159209507167971121587363063676773740610325150137186977357178752412832144227118578433815397967938356226290910406204479674472560693494618580915173028849804074551705214133337215109592516573327769441057091780345856,
11235594095407506337704855698565996394003620907325521067631456605185163184704183500282388864648827144730762492882842065811686134239628355919421090108454860775091152492911180400663454966834734501461668668502985735281286250729695399969247531468410911727992160538888521564847086818424605545451652764751166963712,
11640526625717320069062168967554588539680434818479113245234601095647642521789969052839504841520514643576050429413268758162435345069362727013013329247184012542711937631559182576873997749142463316202185198819138017671933435214752687196089671052307868349452009725976604339839704415878826652145510057531144142848,
11235594786049376188472658957843262168224428100625245634066609550002262287314601505425968267261540214371630703634798566321366811771211123417169351489498108924357636228081688172808357898532118567127178960046290488467975103931000162797559189412677917325409516959407268082984136501730792932721167754207722210462,
11661455459493075895605142164179713596734318092914467684758493135137491150382229341149750924726004874398329828000738017858487128923121789880012859957725984113213495798497989007549155753314940908850736465080250006918587409366229338282294318174733855346552326646361112542629058870182686440791467530224270245888,
11668985894324175829285376406275194117448243079219153725674239185691222961338073885338477725461586191741565750244603917679550180069567019525992777737297837002671212765857767640394327205478832051349607608289100254471389343057373907412450649336601763965257021651281316611007392490704763547264421001444645143771,
11235595392571503073169143042511847507595766504576101931033250377081659670004096421081712210291885689232591655065917337410815815394626554219870605280808084018081220007395068928798166297762990615201856252990425047072234963954434283276593627568550750743103439240568161443613507742041515263314871093573623742464,
11685444266949217125024513857607385265602471716364410655980524022127618228742348183120041409270191158690085003840618495496871719721515656701510018839326518715816234931234771836713971796916260479283103962724098661191506183583633881046755048932249417820669045255064710049246461985561849464693829142039609999360,
11704317112210336661733111206630829297100002694875082048386809994756949154411064307715538402774520053209544519003692574427442146613024776560137176218973713364889981764597811070728809229419788514070547277504645158924983599309179685854836884446875290987687524104628080396410123118977651979069177953483922374656,
11724204918887407785624583515101577960875646380743992419571727260426579604247635888859535945030422044042893454806678672431271886057650725436503894577508026829234278894545610968057010505482265616089615233258603191004588214015582533870242245685265263352363739451131786675770773210321757525397974587229239805272,
11743064045908768334142358980030736176524963669067959150867769495113298134265074456954530463625220954686913364821689063798165890622408452837061501882841271626045970086518252582104107824280109903642279871960225905257928027066286151258595511033277926201337624382687769757373110233404202635785981731676327871890,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773615216688660640442805262344721570182697662686040745174996110653914125871184594488306643201585403274652238698163325005191100852641702460653509462525385,
11235582092889474423308157442431404585112356118389416079589390567386266428567984155219314225119008499239994391319494446735066182378383068996906055514078177306294658773089684598481834563159611000115661172539390849051120515882364038991478068895378322088322626475469309779646659585601848713565997250837156462592,
11235582092889474423308157442431404585112368320302463814701270002825102413631320236395702559585012738445806048383549862850730403403007530471381937576874352697418100862922091871310134945772618137405016195787875585002364774535685544462891362567206138971365314368976394754078892379868138382073097495774442391042,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650478973956624278220104216809561311868275940491214026122936386243541087494414661763912926541256413497264650411591494038900956166842051500688831788307903819027049749997903049936085480436010646435565218528193457160192,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964585768507649902583686236604348703367416126378239666465712094297393320568933821263386666252948909330540331035338443705230499998143853652503310818704745533104193536,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077881002364891339036521172436799075748619051525920159560308653534641117276770780984189382120253671656761362399396089561088,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569411370413277306627723576403934801391656437237929963789139923649429504,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871155041357103714705292132352000,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832915076877711496498400212839922076352942745332347019902415727472031738832039100245160927604765317451529621751371742237516879916783915206042012082875204912079112014192308040161801825835899111706119434385522210369437696,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650479092107813582520918593638826127266597496124727803688577689415682513120489042516390648718153052411543783993859924987624385740222441946131520488495346578650322135352452042269386450662978060110963732178906703200256,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650479112655854049479677787760777520751373070629864015423371093606122196133504197776682394375613238922755324732460686863235674125101095258581052780476994217502457299915369724367043990529123704521326756228559651471360,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832916936572295713164079998184828420780318058063794586014658490802313118066394491953388421632189684862288520006723755099007482686989620039721403043402638998506963866065336843074308424085188503169881643170738123925618688,
11235582092889474423308157442431404585112356118389416079589380072358292237843810196081660257727372501272353493858035732100055905452596457726483042117096106028198936751286079952429985158459671512797493108394613068412838026477901130099091070779691984251311827627453739186637227600841610159775630533871689269248,
11235582092889474423308157442431404585112356118389416079589380072358302387299466208690033851143371341288794338970944948447205146234675368316760446796531708863268026039510197386022371273403921135702133716470273223841279737445548291143987836243280021319944038907170203365069138041242999152664141746766186807296,
11235582092889474423308157442431404585112356118389427839769331154376847773940100676003652202213829246521475741302264253476234470470883405580115010321203464926877368732659206621341620814429093479122031565094898665992740022383176902793921343288406183426563148478440951920534700112730284742246833470881092599808,
11235582092889474423308157442431418202847513003646137710465634995123012727070443088743131497095866211268698437216182147213677823296532105141190244091267251540453674881218617698412329838430929083212959525689853560577814638844327038630871388275282388052481602884127609318034123526014777490225759105636353703936,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431418312736129014288661860814515729306512852089218046768095895676253495065866905922781406524222122622302574559049017894176873971144707282708173468860735778008024376498299117869160778118080804024422591243664977110424476943212302726776082071009159882659786789097368744719556804608,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702873166634832890952717312590872576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646404024349754868758579208413723229023452364627015537002790742432389445503138037497856,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092974484479062193480397462712228400666743671904788017643554266482689672401601841874573088203599941119089022201187632648807215053292961792,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491969369832117866177370056182110322733514605130992913541909681745437338214861796346125001031271815094389365815111291388220309443313806156103377829931818688536638359367056559126998358155264692060160,
11235582092889474423308157442431404585112356118389428096015252986438159692111667953669891473744017444608658613407301802679934064799215028649642549353047792071043524929357795040502744996512144101174133848493359808097403495659760015191704752256159989240351776555243109101344024545740327483780702326321215176704,
11798955640011665781639347073119044228077777947218092629099391263590395638699614987559601991220643108606851508082036026795805176316646979861686292704532591845045987796807558607663884029881578732927901153548485851331954478820499410962903473072831293128453336276861136619235185337438334686647212630929339056128,
11235599337481121327297853956147037894516494840998104465520874870216105073181039237735001207561880066425223858468729351724631078406520480516482103577646667054129318421249105437515630887119823404719374144337824763111555094348590657312011109940848990540482535055805974916775503949659242584994640287157649311340,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384520595453725392489214153211699967645977664592981252197550162551612369887714430891826611825,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905808957150915411680673533742866592768678959263744570377687805180543876801192650525032308098013224481448235550320507144999795179831133212897773985670625390883446431154176,
11235582092889474423308157442431404585112356118389416079589391516513733818591580545597535544587373729794378406988371046168087019957931967445272998586978928984884405864121150361016565219559091899877822722919080534577375326115338699367320192818380954502414283575094231603146409392287224421595811999824843112448,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
37778931862957161709568]

noncomputable def c_Kw : List Nat := c_Kw_0

noncomputable def c_K : List Nat := unpack 15 c_Kw

set_option maxRecDepth 6000 in
def c_B1w_0 : List Nat := [
13646121398508742835291881315619140134997465276582662092668921313658914100878006242560033910874462068583772501062441931463801171021110388712474785031033213162858231041018641702077325542362403123928641819815459506445085212631895930805679859633615222706223411986078823002579514462396893966224272364438324051969,
11250668938275382065389968697138257098730567700238468916571771506798825833765798095144135328018147723770577560351672773468212339750355197679946776381692336437777301450204759312351622019759260733281901899252269150443465472200879456608270659528277712084511092311109704784641532700781614559859840905240198847352,
11261641186451289537727808052672209743112436131437648788509614501668527453765853451393047611609675995455538936962806628353762871869536347377735697741953351679983137828436786101062865520642104716663465303864387234898394338113000407619178058164959206803411821711997979759867839077228090591681678368533922909363,
11271584786469683902212156163343442574302764575166522012074580578398458216887450576641049064894014648467494211451094384231718528271650917574003288445928155808353485657013240662494004573205340960543743590090060212404643723903349554198578339616130864651514264021334252541529669654746161548860475952029600517295,
11279128207035535104210247962006309630051394752982535487168164400469256826010567779586438208336268867714088509980368879012907958575487349031573949633442841414350041336022333788697652902332871032368675234233290576224080117874892571549503152271056029786047102835242276078473787586035899965237326537882415435471,
11285300096651248196399214839959830772899357614350127758968523669954933917362158490903498520929719490008207282755633514815355472053158127021837508637786471139172258615277265698039302817150992612901056049988816556571205621913254307769484854210873494889021655829706785770503337236046580917849268251751941344973,
11293872165556957817361968132786143223887533772993156782372919006552018782325365192299705363290071143015201060902599109870971733095481231247723068721030139706560984423495220739462003656929707460599824158605691988406039637990552942296638007813662462401015875258309681047533804884598895418107077962705176825555,
11235685408012124009085545707681079109742036336440292452078822793992297190001861393321742629276915813495010238890340093938824121151538215375383475806100859379039904950931352786702996955884290030417879897841853633235917029945873288992347153817361561884819902416163408646909186904742397792666198611540318523089,
11307587475920547951776275343966365164201218089299198427006472928076251062143684560385689173075293797306479625961112928007759813157249390283932290037336136148521835468734168943598150532930191464413696110878703558599121121891759313325492127522404054970500260958714562056699961449923228017474235118274581987517,
12719923963889250901396171000894100669180096350547449816365149285917023076231722191178395814733152639887908106991678930938850544584933882254344568232001430235262308611639514277824796423322888910045708583055418752309301446757499792600070111897447761691549012085323368631881408202506090397502130619335513641195,
12717866834786674310467588696799384450372184155204616136639535635260822172757770874151525532011341862207285870141986889006023956440504786958262159506860004771105001271114259793389201762442182727475195690972904294836075308477983538647706140203480011612009445080955187782949028407739802615752768013325310113769,
11235732168263144043154117021099673111616023260307733691247359258045980959481075961498447724771979218002326580260926869795976311178560992174170325540474812942102259498279799993020777608515463446212362048424051693389350411811778390463629604533477662345767847386317709511779057599138966351377446611006754141944,
11333989446497647563481191657435580280756423197280294335202973640363667448244007831328079938304149160198643791389166797072652650665256517629552261989764385454967487787410994279496453554626751899165796413181041285034128831177301553580277637469141479127418996735035062588701058731558649420351821054699600707850,
11235738143349828280481306470176316231032064379291628133581722151179670636293802110826104224070990889540527252266290290955694059731361863678076722148564014608222154801367351171301231224584708590211451122675552403584271116415115219609808808925477879310905824541312612289923580734598591803928262436657517957887,
16297268365584061130379059495984626275682545119235309008372202691209684703022905817737049663974874712676539584364463440202988756928573949234012201657851940800752731641266031374915940155756003037613182413135597432389988943702293026284382063435745411713295821333898041941004324684911488583717623329372334555447,
11235692303967077875414619234546315072882975129554664305514560618163447678790482197146558189790851627635576597908570852453554742077620194303240364159975001234480686784420040054049957650252482530420984383030451190260759742395101469218412484708767893435567931933653493351094477803972061009988148071622449833647,
16400476095567640921666448442430564366480798485980549480834009685535994102692754522207780938896858124427927698634594834433949345966542402143634414420796213512382819415136729605242978033970953119727636843024487135061926277566081405569085282856577571454665122544480493455279749311611470627708036113002152296796,
11368963487541276851059958583192452544899132938599217747440501374684251491597662467893758590511602036088005736720861641662234930385531034271813109278907991242067369392808519628979063943927536664697782679510591207844019221667972335270009458335239970720101330098874128140594154746537443041987733827574338431478,
13092296497641996510982469588071559908898984147550005858313197194188923566673225003696592328422427722830912127335858634470021951545942956315501790943557198989391206271400474355440588207900765618051116300842129372168080438973078288579562663655851199694439870866793814039428805045112564382830654428911761265425,
11381993032357947075366876363091915810558181232971101927358988704807060816242593730661092989615529626675347586921751532581685086010589670281722199146721006543145556863152145003051044623231692881027566551656396058973052532864300707334878779895335443102388901917981132151119832888657579655571235273134072413096,
13095039978234395395543981008483875769578516221702560628668162688279892066509262252059677142967553245552527235224103331364532117256343226944193452980854909270414477147666150967604070861016782584145741673629177949295732206466701946403669951549612819427042730103171847720414421839683338513544811682342531634477,
14579876147093224895036553793577399970161939656649802447392443605788588583869411490383402356716305864860304384370645696086394797116876390579640953563727859037470264839385618691969354922853216437492513490751146721891951693945998341192588382575160490869037914343837474345796566348678906186069835130461941513098,
13094354714995463687061012268230550823168829535917435910989150871718843823699444547088437047692706857742855583555489099202959181204616871610856954903466330024640778209584716418523944991486471057092501590609511882123468944993773996230359718679320926835360450448822715606533953074002268090125678642230740287488,
16945333701946653470044776313525680777769872347514021197376038455090878824405002457912654495576839745881826626402197549978654232882252304268613960175268011680017772304970031489302101883153076570687744706201273652270036234664939452083692000214222843194080265508808444483443550620723108538018541846229218737274,
16893901184172738254895066572401210084209763112413701666911438158808529529222575227940880569503221781030228831848659295179862559687173619432542584430261854341276288635016453307462972417479335778154986374045846140964866509491507727876725509019793159037645039721651223558148166244250850274057569610866040045568,
11438911571641206086360010954932727277618591341776464402570242367475961140972530744192926021733010079660047245204340646935663579321973714523020452002949778267302568885460118729324340734156467824693826127188318949528940760150424995775215119803350969361790043606120762454672424859327430172788087834348539707392,
11446797874970936966368126353664284983617760146107049701735219613909788926037749181045188735489840821323556453852527263720748559625991241773499765357918385778659860610793807770153809403856707689870558150284866786234680756108183301705217572015597098997501579229498572933755908838552284502653747555564460219259,
14733852175134093414530609266821192590324300276133877014115146962678457245590361411373608780482286670615318173319776289211329452640960623533275809297247457569691462530475510712961459945205040607304278069255765697393668708857172841972606802029089815990002799774760240284481344440053454810253482711149971151739,
13830868545463201390566736255183472481891802068806555831561295396354023709344366050815803968503883057779755846436510339700504307936152508222832100730961484382053038616410940658404397032299185322397687740258234545779448970420213669816307372176878218289222191471858060409332955252337895838501087719547218034688,
17274512489045321342543520032735362218536670146877168861764863029638266287279405438126996729672144702148090140707730358475871495653825767503385799546421987739692367954843630675968957401042485499751102696358111332132826054898388160812501823470954893449976360734064214846228486205374729979893699223185413653528,
17202507089721207719934264765364728348623377023620919247454806404805062498258194193707366565349982084955652651410933363969828652845630742724177085676448413816047739610549088698020671560160345383473058552162708350021346687364672072554192726832340657743884298096838029058761256298642503353022460158251947272545,
11481086150563444017946290031005545699796728910425873364450768029962579777749451391616936017401051113824924986713733757153178818220477776400118248048556748915791173967145402286952308756560860623881000179170739701713322426569293731592930518193096614574564464591324109851332019410243054972320490696354482366067,
11487600920605923350982927426807757385369335356270514981920520321123130610255273263489807052847078812133517495520970959135714735167474448939559236276488361180604156218649004057523032223368999009955616882358587470052831351188253800044930110484499735655305794974677711997775039462872835923808238185890750995863,
13830869550002529106374285423641093170914245393060881689888458083081716263901982019207609672814635972401921144078632486916403576512982132073870329448569351697639826628019850993613225335964951140565162160076469236796289944794118838497494042406194765729552130147769513801805022605662344583023231775026359770509,
14991022089168389009486373465312595599174877519231919715712934635059228927845813067212191265560310855428967473747332693523699303249760928503891495160108005825909344766336903794325703676189673918794900635895709393382787497903997950777115271730374369763020408564892685394943387135249916513792394476546728936743,
11235773292798614677716347370504672469782401335294251426418790881441227460862081160681762728457720942119324698764077837361003870289466420850904008973943840951941010866005948505967900268778589018419133936515480620157462153269699224133704264377391611880576423112860538076862260027156315593194386398287497428992,
11513317129601732670258673901819800040389404829621591867430331263662511234703517228348710191729646365982165816877429350713652036403486255885985502918981239431054273605719567920851392310503101384414571071551897415986460339916772200055036719719975200822964540382382604377990348640080202815887649059640180441882,
17356810021589254708889888720008699560989824700977864738307657379827925390973571822481585790718899396999444566717941149580546492678704906856728435295161810614537197101310195673211894182653470206904418392653705871387439220795417767449784301585159923524153141091598109799520796142030637850729481856107812691895,
14020827767847054939897056797014936788319487370153002282170237989186610658701148302352020725525705145736495575051818276506912675158573619694255938421999584445997923590029936710658727792394184070904903650905912299636681310170721411436004512952917406816274975246107108720271652066818111400822777903755296778833,
14205984884190841687833241650489416614559487451850158526708391137379572804868612073149020413518227974532296834118485926992495031904432703151419858067575293992724102273209993401418348857606350198892850927596188029080664212699223421172070070052858043356128721214902209105403074564308868046180461710746846086918,
16863454584010241547235999375233457514931379154729859269281301007657737583232251394839339090381542558280943803130346009254756280645920414243415924948662900537390607837311736681455581283644047010662068105879306743453192450831468896804800061605133660174540629717511337880621279912023917270003828451567823014088,
11568178367702981520466444519757932992346980424106456105927768786469248570151848479741570654905883826410359396358021676056256686651361368803544040191507754079433770804762211932841789689159374025504244493626342573544403668427311542593553383692104394356672994403408885495291413791874113281669681986247952334848,
11237306886900733823066656545572874813475513106963989642464663673713914791146829843739092273824893623456560603877454620222543706997856952173039830182689185149568871793332889985963205432377470105087884000461219762754942513367763664729661428238384028159059413158836129239674172621841487939001773097103252553731,
15937642881271419170260181168921197638823597181581040916579632128547358608904413095582230994540511347173584041042365053710752421290746727535631100801769943449326045147240887122292536313288401634729113361130680957836884623894282366932092522972842547557143495639872149223859217999037943862771803320512700720934,
14795396551210639908266855298539079163641827742091844366553082769335524806845681224968830486986395003145966264185985151488682246429754310773933798664659725235568983091742724039391142921467490372213501616870252080906864300188741287962451996805838197553538258546561973051533714389905047896911717093874801016832,
11593894575454215619796548539811431727153776427178561595934933313858004198532006064371954184183074301250118212839525242193346945386275154809504803051958387866976959836115582976046914255437746001803200007538521942119343987299186924553025723547146434620870627689750845612014430980441289548361499196433778098655,
11600752230664432641933243253359779426631450469355223871804861078081386547177169947232531826497515050438301617050023879812952227369216123562816741589960868411975880196750011448264683213579621546581443817158103788961007966284795543438948937654774192112570462996977843834243150433634632281291473208065211892257,
11235732484351886195719173548870005176584843611807705725823097468428414644069607047684998986442711721507981743971380851948585273200624327459991082968971808774016295379052109484672399971903857998010531001394822008535005243141486920380512663893802121157192401843440226620708664775510513053280381698136665326111,
16091944829656103311718255370425929887347502611202992750060625177208626606098750562604884915741397518522911964850540597025354532526405754881582009716168998463259025517785444040907357100288927330946629223014736710411209567482141411110759273106259236203274037817552687499562141390387385981329845138846818075704,
14949699420276458049880350250368693281955864582021446317516611231372844495257631884419699947904915100497371173910238529608848658638607541926132872072872383069883857723377296496827292597279271051865268512128519519706811134533363846010010424801364313670563299711865795842052191747247489613056377386527791006715,
11607621653249865969725287865303491348395909121882221940722496470979688171680349704771880106901210740891677342311073570355356939295408109596186330263952686329658140654951878010635711384729428479777495057567217369539499512081927353476784488996758686053767103053701968193632642913318321416742858985341191239417,
11627497086793433613572966316155721627571903063340277387454743617671513021054629197677702236821616283819384681732146761582629477471807896180835302612253030358903860158328205633960370175506258541343751148984019074950739628080681214186296299281188724989657627585487928171184529072859049790064691381789116115896,
11235770479083072474433356831695405754207558132656047867168624069693801237674945547929723855408089119424943937371761251320177741390517829558433839076943541090974388990714368761739402121638450841211527915507043355922918754637650307023592383421192603461811586089675027021359954569284858481826930539942353307223,
17357186901972786690861844320476127973276358084121632693847172180354242841870142019439204741846937594063378155463088021295007361761953164291023779346004723930318568845151108459630529500979024826404057409492496881383289097306385880369302094757584989491884276700701211269081351016641675795930439391333053072517,
16369345464322021630296629127625821819989149812090421291690794088073004354983226096142304635666879472913466989134284301365227469067240042566411438609662511308171003054692875870108515777554287971123420688221519466801418340604067145820914956418861997476085949374005542345590361798360320395189269755590108348416,
11423039081485501352867921243658086066563143465324582222204309430484625497107317577330719064762912603711144990566166949387022449859993994096610737345903447043963446787365927461999456009437217190983239717255684837877143275435195449643125856339767134099127294150072738311223736159194238703526023688868383967012,
14021067361356863291768458762224456998745164591118182855938168079996182076553642593418892243357034533523827342895262073238681432762383770257302086066492863453008562158599378200819939593940262460066145224670613052308251464926748565456813615375306008415449203515456162228196618149523204130459739329829462376448,
11235825089012410911853216261211827352298020979138046079347348115514006910584609264139586918712295578823634029166225762402136492811624814419683646876298010803619673536737544886246009231225628575876144836511815965724970949714247008364190186785960244250230082156688843658560849386293590020424002388581812240384,
13832964339321852130286389186781393429187630601634909453808023297114760415744029621071214355860959863752531130331623906944559884372480241700009505180677235759240189810037750955871304340188830964505399622831136765410920068290971234171438995050218762856103261825649020232379581971007044596486307736526040827243,
13461959402719978586130060606927458811224789616380261031794401426540124463631642704495664805936768390542931035853484502483927216233682878093100769514520458774437605047112369290096236127392567616019499312577239565312222732058207059633461572648697702551986808849547820180316044543681925451534945728535904410834,
11770822074598671550677525162941102328036726131279073163556560564555486421266216634133145762139816672005705061239425028328196796394367025109568333027495178991512134917762300652739249642797437987954860744679935629786612537820382902583757788922562714738623223418128639832381593618276682342130140582395874450295,
13649179037273674767654399741545423550887301517552923104790247767303942141780738115517985229568512659381434258089162976008999556076531060985809464860436819335584389864939911017707724112953012672054601544370910510898001526030792792882541289235666885952581656054967761682232260642913109921628598142093016534197,
13834678791444501704704735936542735426640286043582495406277108059108345942078570087912362794152324200189946838029433713688278593869811832047329100386683870535905460843873954192161080403555814281035199135071732334402954114744948259096837905557627805093640047406582866881849603243753695268878945477337731145115,
19198050712891730955081955524665725830060037747962172310131435321307364340390756921085664412872776576126013861117823423368389035800685058647519536840103130480167400492612574220652925918700640485816062348967922667186529197228554721821327808721162709293715303419362055129576949384140945933001930677681221238784,
13834678791444501763178404615829552894636159717947790860305297088421574574368330835729532126878943993906677626142713145032459221378747412878034584655833968116164179384391631788997220982536409050961943440032515746436562073836096754967944965104563285231663020251182316125077378761869880603740722618384543256820,
13646121482222907524316242620732737351485862024628478559784331143896293945273999122950104778243278023592265037953776017168224121383632949599393586525942770805171863190131784893399911692950991636711629543396654139141958524930113256698016825785772697968174502399219264975483902354372646278516409023523346055168,
15145182227870928795622795653737578681440490648052647545174449728072690228740254463989599603579030455692788179168828017763195548797172555484485842243783209954745801990625221409047086724852466145047546435385687634556020625887487195107675544736000933738986376517411618384411490197614105390847908578708334254974,
19198151408525984988126720881135839153516839718572675846522664651531956387599010821826818448959604575030171002985666267609761210206214192445337976467992303302456846107754882881109430852455353778001680885852550057292643573446005284361289798610605426715864592927516395000021738992303365333436425448958854180249,
12537271469080861190735958442855878526883919147841466575331745209176054339404576145077557726050189094777725297549274309747276616015474270438616059056601492397817499976319821826838203660850921618190332277910690551196980538787177177654735445786129233634799038517509977031770027886584436963117962390848079101952,
11847970699656637408151069483053451906650831214966032715998051193086879268715982921756663466662620657898799837756338612010089591491097486824094627178887874390181208997582296764838213525397474739906690773228668869181254374723565257503725023086727401735784507337772501705324066525693732705890979445103433092818,
11235830740786732825455712697375384857372509975593134015632155452470490541743338586632963800373718769625040833382722138422042513365657797106864570517040592968315463612240101991795947885358034193928585115279616149165289359088072261029414355576599030576765956582806771446482681077177736331101670431256232598929,
14651762718310769273711027679230724517922622871553261995266964217580231735033112836539633697714366668401707123398065970234224328301550844474754610145680604478263328645321476977681379763495416287689084922504449718318748322186003863423219842094226218142240350199291994831871003348290686502709459303529552840454,
12533775923039596554625786158972121667800788961656033281629701394373433915239998886398180612735905581572922286510702657714329580996929226328494451182709356469444724899248493720500127716322458252333636481124105898086800385052321018110925690934583380886544880194539724688374587183497284512393699096809733695300,
15207316428412263691535689456901021855840247760770974719887616328349824821414434928692404015130126390419613765918212780269382848296285948224959984323922896813837462609882853942484286077614151698120262129074772181114273989407490166463335442692377348151440502845954082105048703273273676819260132522855520997064,
13462330673139402392803939056654058588740986337405910643282281896915327786884744933860395590522387191354823446454571333073379649297533464044453275913878778958124542847185803013159551276081527198173449818937355129460665383823549148330260404517957268853667634886727196393024198593872267980718463429267462422528,
12723738619623830970594891178930237068696033012855329180915735910212955455630862229830230549108403208877925952951989375225162301058495027943836878562574915560058776392527639092153387237646841506429710386998158641581290065878501586253450387801852765479142585380204436579969815149144926247541917096127423650140,
14018503412946152668745737075374257186404158455477898292713416679126188850635093730430133477530453314484128398366576542611860769116308387727003326557026385679667748454685071786144879879270801543523898670655790900301734635035562742095886871829255507484636662669638210033337732369698259411040691259508246027660,
17573103702373648195421686788293953953029432109283658068040522853422662268279826633365829471099726426973765631055759141497948205549175930745669071224409194111646532413971996162610301739067637617522352241626615077543210223235260340682676516171031728253722648200879356408641494033696353426031947658345421471744,
11235604731274225796269639285553921282286150478665993444738033573761323836408461576842610570635057032979681727813535663221460693163887927432303392253295048359298576768765148945454931455840285263275727400404956751801824012668579623343935132602404044648998157381841170208802542315129167066632557526310345882507,
16441593606484753223005829430848223827827857649405644018887473443466215825847100673505584691561556785925523702564098089881385153337146150489160491617041522253740481911209296383970879140028497914686653807069146938830471707575626509651194822448544065184102006430438181359152639162619219114574881056451114731367,
14019498250220199145057523374998545832715105534438272834726996415221851259007792701843181763168555838335438178389432211083998450896961521542322700808433060636642141495345272146044489347990130609184829141136633942607793549504538458819542214137783970038878124608873054095146424481876832241111516480098333851648,
13835021490449005873247272962866066372617633493412964110794907111133135622742210657693852789029061161997173437784195714339135855059698903936996066342658338760532077086223326304465003637867195603556531453347128437902914012606435494600564261391148513413843205224488168627603380327117804714437668069158535135232,
12718570776178563029990856776781471064418000699820669860432620223344844748899707979848535280565391278393578379432167456103617282417424013541947691537967810871952922716816715092131617365460692337763586409437544807138688858120091849341190105117017772747865078432384894184806114638652699407613406324136873909458,
19383207463338278558898294695768601623774892141860151797687283434147617147225674717425698485630681455780849081898760667031329791877669354524376600357483119442791162537381728114128890390438220953608562716908953553657268772999372419000621317415536376166731967638501739533461515246109316180180744741776002028289,
11235667088689529856948219696834723285839698188815987968942508802640395638997333109553096478830215059977623590360614630220739868681583959588867907410961990524350632102274352715616828106795663066734977276950335378074585872013652922736067002071702202620946780167318096254723449606541226815973252319732064853946,
14019155190506474132424803257975753264220850738208283218434542633313110356284660588106378620252629034947075244213146653918346145849476187955986694989053957396551820317241306063085873897727671615585126078210474406388194851846772205721779227491639462396972883441698762520187024190957662018741692985510700746725,
16585638433961496506965834394003714546947786544377463265232999633815298563307683279986115436855374134870088719536995316381803545997887315456299451503714996230337998398067564757769816489501540382560610387072097277424142525020043751421496394101488626484264902262653420662658417354670677770316214800502721883394,
14651489997427054808851516298422481781416308963537179565735821065103870319597785827535935723230396230369351656998643434097893013944221678268026241938990433867234110344072166322154246259068099238620428509211429002586568440459202648240520924013129345299598845947608164775506308627007159875379104364080495770657,
14020242847183270268142533668122675840072998326750760737467915008089346549417614314587192139704795214060114799177536310299974053452069469712711090037719882605104399126725487254781399232180615326232873788844228292345277809587931154055159903505688315812505565194376069380552428481319977242130496210262311328438,
11235599078476346858941006626060707112296117152973547201743328346901218095698115317027928351805525347820075096364321114795568194675031643611854349263520825643358440987044924577150460937688048733189894235211212264901446467613109320183963790724783956516027682846499099358199366429723803253906981846182563579479,
11978027511542667832263671379715747441932866189464071295594318937715407233540379124704983804045818249447708950460166071834950616467139003270227434101373869247478471797556880664314673045919404003015973598694144404332529030815531533558296081385238621258813595088459202181736673955614638716783784068638607312951,
12533090052890814796233781194149506215564014550398962184170878674267795335126739391388820758938581846553356182590020264211068811112820911741817775013128606503181194592511790146848866567516397780874592008802247618181761957748724159861033823187666251484004911733224827328879922178767970833330789019151742697472,
11978044460068858080203781806168189012097424677700149134630710573277676275760695788876509111127646403323558215973580473079840564377163585548641695381407306322964555729768751684220028968677166521858979699446561876208278853129389010542872664252792640898582741928250529966361179292566759438445448845671879413446,
14019807041485219031076539064681336392691346221656249093913970811435533537091960422812815425239641641701912647437271366801439024437695590299923017247801506142011054387893364095060500457657500819517656431718776889692089260174588061407635576973036779501228839627034722610560292356763580039805719891537524826580,
13094124372731854389487598785162451636467600827731414231586952959681958276030118587119508636228271450110546736601746125516018045831284312321309322207990490881946198681874537545164834603184070449652317348401414145362018527387642448132974739857723994083771331057965720162035803982119773013591470622371220204893,
14020492807859235929932252849157873446981324050361438548304243992242735272407085850499198488904537572925937451595829854078314291489916322145422999619511331188742956845910051655904934895473366605581622723211326313292936316526474008901038380575826613751952160540036902641252163931473159095103826720508756235560,
14703260260051101486831300892047128921736486080054589345008622036297816856179786729619526902955634759550359826346793496688885735632715709778038129982300968682900531427525262964528703830361952520477968284829254846780207280243035884708497836311981878400937941522723848997264084276417970070721178781447553198883,
11792845876470969210008046344829849503190278486216793663253861986966680067770868968624101612511245776468968096440328101269865365049236189857299803854329521844070823709164615800857696770247737538400854110140654576759168270482444153535450495700774205569454766375184676284659373945413882050345748242740500309769,
12349984969531626515943035596243153839033384999264733060611375382256286202982717224362124511906660882790069742127468639593213449030356983633943023669209859770351580319002304937382237139622814899819583208648372241651803840936940347892961396573307538872411666614840574628996368527912608803163979116128807949615,
12013583069810943128442018228224934340753950737990807257716757981529740328491335205501254135601847942890293936324855599814139094835746330352034981999307378826447173199296837500413376895660339228301558495565069573670493418182901572345600741030346111329270658202466752918451937135797348499144449200669703739744,
13647493013241416515355653415543094051650739414733093205231441894555838440068024683742784916838607741292321401186155444284607368178927199263480439442499707912623167748007440506684564145763388193666699203049716798767504397904690083656144813425486107681966748407723008519692381284806003071814024840970654230340,
11977261421496085670533894815849281326163911863517051514533924805266001423668464512900804001405659566029082765203471606326240206476456789272632053917874179088291151814762670845434862360163734819221840428453429833085708289696463027876334464057444822371622676037586935173990349058783661286375900290533168978808,
11792187253239611689068563325206364238721745299951069013845304715865349517496929004994342997451033428537268951166704564557237140699363829633672700105279606677263905041357397690554198121826977760938685440457816436473706687750063651386946145762090498815560045708669304620298461728758618790577239300598463829295,
14020521238417022077304607894191557526605197974429060063869095088519573423766653694437353275218450406657506087714779148889198845653580722221478786329975740447295176589765070525804640696943617526902490130910383912894606389130384809975416358356377644601305146396669684056809807108514604858046251050324352572829,
12722367067677452814366499645599306654475514882248175811806973251267415168732565988488816751342818753253660279960331582660968454908286748178497696581889051870130975176614344826646592032456695483938487922910505287970544848987646001474604550482301449785582847382793668641331948725274834320498985840244948997423,
15227535222520809115673232790209744677477601902645703058967950667570613294797456128191413434634028374695519882757277536021834583226322178611892538159565995009508183544351449527757381285275934276208173761242171763373781385943781067332498946940975217064849627717176574953803084312580119230976090581932429480717,
11235638839243637096309885720085369026404207663182943330400136646867646500294377220971719138767125168737681883727868017637137359849193711422015222413737381734800399455514955489589994961120050396962626146895310822969623097903332503018425597941205793976265233239642284213803785480348450121674460272772818960384,
11607689074907572410693993636011568692034308883574707985728044957298422542624850654737926719015153488544346172633478846589970744834371705395989202850599806010202446343119491702081636263473244234190338108133781435590903767453307809770748205387389640696839545839472342542655503002028621356085387414496020859188,
13095057903501161321499745601175342650913896596190573724468632452252167883465837472344926707555606940044520986940242750039517087817723605989831472339705400450834632475001645399013250111063336353126917645290031509693189413904325735835477475541031364014814849893931430868611631418659140364871084621439398580466,
11792165805320192824871908389143691268271989747025848108078581221189032452686895208762958411013598939758412054070529711597353992537826424976820202792458519714199483676281726903470550166314410830406888059885812322658005088064436298721985324874869470411221158802091270660847918511371544238864423274710376808448,
15186471221761696296011722680987462641331700340703921238526294921481594503715922339834601000105831497130298394215924097773565962996621873464556269045617061492354570255006470447133791232177311859480720849665883969692011658058531991698918091551573550512634131761548055833480013657463122305542769633189277700338,
12903046804399893597592331776831574045035506328444431900861213817623779513473535690101681667011443513289113639581923163736926871745049371596006301064489166788359100287242204714005112911871642695812609090065687657436847744602020155844632414521155597854474318292212127667279736757302567215847467419037871144960,
13834678745670528190455784935266515928376754847527814576194847854904433100814363015536765486576757498387364877496053579993676132901857285013304312160035513201755215088931591646882960824876932552791591003620976960190902120359428154858853536287741914273189131844559979888546889797491478428301154429261742655869,
13095114586552510334797161863997086632530605450181241192361192367944477492813746833037512835582400686471307846816610518108214952833925434907653560909081599983343237117095302406040028414642452408519085233162614637681828981315961246677043263426311899146666813038876784125091863997541797041812880537515020260655,
12105475640722031473588374742033754641160142851151372547386276010611758230661212309612154240308436077747670572196959917854752049274985761066613749103589621064467379205897952040416443942326413491713432460694371700690824563320951388810101058219983806076897457420450133230439460480291248319449521150251867242496,
102293973158270365946105306070679797391608857623385498777454607484576908488857145888715645871536024449009504823636295293099803892417657335296586364215]

noncomputable def c_B1w : List Nat := c_B1w_0

noncomputable def c_B1 : List (List Nat) := decodeF (unpack 15 c_B1w)

set_option maxRecDepth 6000 in
def c_B2w_0 : List Nat := [
11319588372023728510783820180348318659825454302382333763950648083190095831422342058285121881346280414821780763110268364131111598052571318360228655573051697097315012843756437550492143286124399041002547398346637659456156768409003498425441740972993874802348449681001703399672898992354663678929749312854319759361,
11391250866657293468807773528362913981899886352836536185952224980428078401953570326881392323661003534224034908652878188841962265206464464331717961473870782774212610373553502482560540169341512568159254099519616412367652343398250185581922878803476476689908944618470803259700121434444753476846451221634325254385,
11235760421793704255523771330567350532206681439998544429463598227821371807967834842788197477969963663094019551706017663659182643284118297055710470591146992824523084793859918614128713162085144761988114185771428392093764620442050917555640568673267460796188888814053399285168126104294657040137917406488128689453,
14205985166717526392748190189996877559850831099473989118324977754460607037368644794916185092707161264930392661993319362758120185747936752327028726093393990194905133965448288786857491752461027169998271551532918344739896775598535146450273534307660195926919693194510616666192263310334545272365722235070830314114,
11235757921958370145967516856962433991160944317213903869147154951238529717095137657172586898359960812582198332100082934865632444462650312600677275953456454468816166042011906519447175354679556773389899008614047586282126721623664136416281887230804626066918297046537248817445533537053972716484101967125150386527,
11672757609374239557972964370234171177938009111738688934233011365003211752339870876879828815007701561214360315377503419601525763485854684974078495759511555242862410512858460682804689292467169110573960358460360927436078547613173195084160194380388888391781335815839012852392226321632960169784840809347880485952,
13831592808304015039216524074226804708082539938666518528226281581300425407114402765349006357017279760197376340185521010113315769027260058242593409708748542958356933080712987735693179617010776435014109841296461535206069514225462815599532667976952593384068471474241336586732037976857375891764679247398994925723,
11976914070634758134551253211922014970683546928438332891714941144100862055005623035076578266184162056053663580964023162263598862229105525470610958652623119719819087217041850673985986166876544329850364996944310270755007636256431399126485471367932415509300103845750713853287441797455931613022178258059272412370,
17552531051034049501159676736315817118667094478384001373965062046666368335684402899403044696471030341758984875912577562898686839807592076631358686965883815403894503771656547750924734420979643391187444858488273022510297887877011412516642140319456860980841147848191660510765687495908607603757067275211362011252,
12535833198636821578997183682334511738640189140413585004411881058241209557296528227513997477270528909525917032078087822497573647114615372472525442997923091093599985101454122656148468450817421456916013875842848125093792058166849678437022045398684999877290160642462647398288462543432688334181003866433809660751,
14662009488832984597645093315289535608357206760945651467381165629609226590614298280766044361371799317367512665770309512138742704963031519296543426829532271245729846511751268414994885071816039516849796099711170004220114611562275806714660581096631090384326086557991226573529886818351344290599923581745325543118,
12239542798169455704415603406907699177007870727634325167494520171649908197508557052261134260920946487525815335931298301122740041410912641256462098343351330036400741978094224740355128005222755449390713217273006451947253713741005858677388269350666250544791442702582006522700003883640416654614898725804204697323,
11235830740825397551450077824463103472552963844262239298372494734308423453377080662612167719408681906425035934896121959727089722433234119529889264232612132025533045316064983341301043854010311036336361385632465704719619027397552027593146790051948027084084532263616568226551837951430862198633866443550743338397,
5136890328034121302508016824218433588943976867618779252308676884048870331155031971671513743334987589796183389640247517064257364605029219723383705782838972707803761207493776390779471432841312469875218863000459]

noncomputable def c_B2w : List Nat := c_B2w_0

noncomputable def c_B2 : List (List Nat) := decodeF (unpack 15 c_B2w)

set_option maxRecDepth 6000 in
def c_S0_0 : List Nat := [
11978626580373658657518549020804860066074782223832282345420659607163653859920434832892741833671186921377594155554108925033098668155337417386211140044258225491847313125707865188263929670093115465760077326262501477301729666178924266552059970362440621870480409335329285860335578207005015799649648225808730654348,
11810596475654160675831318802905257144160468202908199996219717191901159089166385150600171136558852444065170110264175788724164009215738541306141225195542362004139626143581837296092168384342326207318796092700091666842665768400145474256729216526168792750932515257934431456649035408353289432200189435398007947264,
13093677453458320570133582636132483077911653755787843527175070600495810162152923719891715330026984070812108860479554747009157540936007810149403663615608625834141184637264412266070660750330039449227142273318062854912359715723275700581343914496422928547744097843204909178882768822009627264758152664132848503818,
16513246144776227166198621284492836171709629530177121473800239436759024857595947151090830905087487703301488359310355722378250991975798533782332677573788802527840194887720920799254860159663325922443878223472203556379926151551784644364753940015817628475802595283806325054472125926620948933274069187503356019999,
11581213580685374649237714016398223472923394284329036971563157489760907430676270044250629106509124335481250059269619286456432558537331941708392818944490834008382311535731406915463933944513282124010749478490998930986483296114791790092591847612386317649836372971755475583018147349182921995436592197457024189632,
12537522321037824564631589759803798110724952961837323893574757478109181855517974742986029212520228334262925873590339313703921072322663839832919726545980426183727936288651126648730048240231258102427741883532744449698187959959003442109119343048081236023990100609391096840272619651851629133051302366265429079381,
14620624574460997885563796301934978123572618518959976819120777108857419884351846806975676744048972621524461216090120162094701742867676055355495494062162251204109123987599806768965439765633505924118076741871542243447843886467152483173093967093454907639176798826851769661532885855303052880304837226927577859433,
11235582145754366279420847950663087914706487729147199738117595761665657322684705906795445996959234810883773090296056040923455018717423107402299813091541744751066438044372723773670489132924990928720522908921682323183193401166068750321894047151771657494138564774297678966987738126048739684216910445481345548288,
13459868235423115028213304340651182058292076776202618425739010865101494366063901240685522971800483713541691812279588216217841181244793223446851004843255152069966077264184856222761479128332303163494614954339510063162970668928764666059407904776505023004200192472027995161481463455721748637793459949260872744962,
12347551452105088169057403403771909919455374903894357466943661974567691088799785292469059332895626887199985035553654208969997651959943612573229164862246228188760580961886737589236476862226189699674233646077792374083336814607816527437484765230521588332740284135444164546873348064027137452477167822979996484129,
13646121482222907524316242611802922262575424814274796671950934636769388811161154095506619316189210423639539839192772603361235376301953403275935505791570745541273398754789101344213771129628453722900374535978155533007448345643181803841712487612504568406022437723208228004616794365678648662376654168958889787449,
11705748026124703460874722204285738631913626838319351863834064531253613241926207279292771885915284214831940524684276269963380048179274728880523271863946609948684819183305950220745117534163754421330797825033714983652934473026612354538959335824255078234527869192722013766787154487177591589628488704887424228222,
11824008568654451665436623282429815426126283819381759471922756899060779331695877642303788896979505526065109754345497652933274777621305728099080046213597694715739232188019278974001461570701071507288652941635204468084653194930889682540384203078714041128457145073970589314145080706042221899757827426941792033649,
11272416854899637027069249633249684848072934201767394250879351795516310024985531050814543257606197997511024782396830505786122804400111410421916108154128404339221400445020414663010645860742564507784438800432731644159443967077246754097786517683504525431954878061306680285689633774318939222528225342465272090321,
12535452478232560076500029091655832994327286322637579550755363746002217221363117896100018208386614878370072044897646522044611121451010707680708340783005623595302550570388428649563894870274650312038812052649486990552684294643763373640371700139230054654544158296770299586080625723173088471032219455223139569353,
11827740662924734777359367661523899592449625031363500297771272521282740662125912989041691205242323926556774152431557467034346408847507634634098121513804290728274201170084744430572571502593279953161793245183651558501608622367975551311873769328373422657529045384247909047642120226053823513102680585880498798603,
14888317782786761667956394242167874234003379927615480281313898739123313645341604629680399405692964079525679976779844597447524419712853731808791316614309654879433056278976658235961463667129608906810489201368688167596672683508388939517437013986550691010356653453042923786629854582058460277705153944706504228867,
16801608091792359206839895140395766353554034606558230034677869791485716550718949310719436276430426972690805870892393154350824235122893901800156165858411239218401180806637341120780517007525658759658030459018656504071965573256679190712055840939623494508782664756279602008185117531288176678578412338960592316709,
12532708771579433169573666582936103675771200285385909487022397760786293920349386252163093350544789132157868886696766199989550423028331179939620143777691381840700312518201482661730736998249481571821054410320506721579135539981061103832841314184117934597626145006855944016938068519603242997668633734685822124047,
14887974355370362977216003626942603018208535010099678330696406304591384911402632360727108627491569058301455309139223180580251660178120569775782322593365919808927184498819090813824467461088439520994279428007033298155719623445056635642916953013427797544651659032747812464452581775758960413454422009871793160309,
15947487748560668275042163897434320382183944963155362512740123139450359176601242172363102274598494558601370907364164711019990392670503201589137965281778121284837641827510568652239140029078919104695235057189492987925824331829127443690728713229494298703558908771333630136697380574076744093289429501603280389312,
11236628864717877486108488637828574310765879362729529032942868705136094852952245108888220891145108090929640541524221170565738595235666806604776367298053868463820977666838219580300636751947841404288813485353916598621207773949730913471926548281856883802612907348060560321411416374347850302083088676946115757069,
15711240997072084903266165353261381843202390429793392980749879189608479020058325737010720183046579976984049499332467037566915993669969709765447079425731597314920434950660136396029546165045525879688421067003441676096216423566599409617054544363199735232972439261489336496678057094492059176368937736091101669129,
11585671077419171986123437991191256141415764117015989558920028709720928332536320878531053284568227317739935012604301119501293652265343375888795330418745021343315903811958028912080556914192959216542663164040185671109737130111744224262874113248043397456149794655517195305481402007292679881657621911829191230426,
11568693295911237328882685394450906795056475723316140160580399535555358801819167643566606813447291055179263848979887741754717870337963612513644718720207264949288924150476464396285151492586200602162317102519856312149499290434107755251094498351339502595309284195666606015817533512506131729487796264885949511297,
11289488236614640464801547039089285106251992172329400282780184781644862648220382083764848712219687815236582101199244992656787059136403565517441509575157195122658099069735349513010939627187164573714463909630552966674449101069036816533751182986407727814288686176465954958345227409843488364092579463559035859858,
11675574155529813493376222048936251376512676463135425474525566348038229043623873262293825942445062360382259217030807373460641952227126764191779472301737610750503498803889003429541517876148550263264216588457910412200158186828368529830579550315451210106790855352092988747616930632905400106825472865567371988683,
19198116261234073521522903896515536647987655992634624275843423121817633514059713369188645683799137178198250399567103925869486559260311965051487063358383413810178005160673363140727747389920412789571796770118119780154837987909375650055786763764232065320585720687976388380797661989594307888987874973351128636289,
11276081947701287983014308710748721360969689765340822365614677870882886956512783795238881441120630832065657907161741035215697304061179898544384820004445529877779033656445566904139055068953627202232569845008047536298797549134014758289663519430603287235937488696074201200067705922154397735656774708032749961216,
11399986191156594499833929888127906523810129133420883607116694758929440462293143838705849952915553376304931112485431258298960155793572265678165304833831360724352853059003025911907759175024354201762267493727502713767888157498504018692997655999363962669008235296979205464314023578446574065525971687576056860371,
11583068326832700983459386297562275565680874431915649105738564342787354207488599354162016274954234253126991233821269214696907449574946567854393049835967015030138659369195157890858976523286959975561153946055567842830404076423715087533786156488149756406359561458268829638000433966461479369669488075585183820278,
11569004786814234472534285797873345293958017021045646474221462939162484504016496739545422434421034346454725428748373427443078234725308863752045009628245899844576692491091483778104191906453673648268032779341032488491222393260652822313538789323067317235245114316546319669198390050436888407036860295107818763665,
11290205331211203327147584143143647415752988088140164523426481534871509629388023635918669209048551072079017466493933864575730123002591808754173492209820701221217786103279777564826500222982726643336426813156100066191295054130531096174086477185085362050383543679182232416351645067302222991814219413553555750970,
11427664356987807553388608150908603747367473676006825259257671664098885430178195245070064783299979093695296773209648976494699346750382593006358308265504496061584980145900556387521580982050854629537444284046618071312032222625013217915108551413393178571486033704350501189721569835513554912120796558168651992777,
13094440174604250283465785251590569417502471069106845688869510403531535387036010807852345418937289137054296990515572114934867183612690178615386978711021074013804756987342841342194516131487572278821252416593748096651915226454657234718162412689683193566704205989093017188909479283112505383129716895569957689685,
11832957507188244893765210903742007368339993899116714965185611609757162686862005432028660538980477808514607202092089181589867530652235648752780947642196255316207453698407365363056306134016151742293828411776832252605589417510063193399958833593220811374406276535772080871237345776063858775856697881924358209536,
11834598381999603021944276052699526199103565527021848153729189675843292734950171981037849798063300233261446580762536044473680549028048890160291361723588056231838002050291222423828489870116254626085853858195829365904692640212471011539951825248041542928702927138998771646552115821077143615349067792547686941217,
13648796622749153551648921470827350559971172765541749194544659213190499894560527264299152391850919746594335965368764531774074229759998343417238379469603087378959210181443171110894486787071076357708984237082359845409995681123819116965829806777397177150977705805078458207506033286164245568821570827009643777737,
11563035126493963066794543103511406816707965495699568885181748773373397846949527285086544203504098266487752420627442427414023468635695822614494670648542348452495883075696068387162147476436167374630606700968719260719203351266838321189012959498546608429939164313973827797385163366579712971816955919090876885405,
11283387543608819707562521434207047248223393429220376079350040979949636353198988030666755867100860201416613045001688125754026001835920894694849393756227908874099215545064186672850386227632823966248811530623660966094534862155164935348161176084480909051304872520834217179238704347906252077019868014961021531237,
12352042370696303075474737493374347933024335760393332503832920921841448008183235547317829071379240498971621334277425771679401656713368698089662885891516044312897680610703458846312436001478501869114721651559690793827166790208315890676292738537616834714381351616979045393623364288244485372713254007355836577199,
13649173542665289290076952346400243718654479995862392046696493700635406020245765727077438126616223562481052965379169661308331381691855905673334039886510773204635557621033971336288481648280744573658690101279017165414571494835458891675953703404966784231355476734351738103531498914300061889947072596143087553718,
13460562351161619773627397345620296299295903338850220971204741108934633572760507578754191072149122464063783190079783092322936799618332529056090235440350512763835159989257873220073787003303882627344134405008228234381563230822337920662375873579608370038243904272754062596795785070453785751973772783578776643997,
12349283665056376309490830826273968388401224853118861086256131699891280022275881252534972166274593744877415333496566515008322426786049617895864741080331929927905258818348086477979989534482989199514254858896164686685832356457314300113732421147380178826999086241426147443445746329114769374716780155541794948417,
11837380996083946491088079504957810195860164154600681965246344687849732769804227137770533249858130284364181371954581945628055748539133724921857284654229501801698347946581689426093200930167331486817272889353360104445890777306476002544213799162125720313465366203790415245431233132415056038999025453239033561116,
16904468102588028163339260174702410046644104685271109358098025417496991788308170757890357995636287231643551897485058237954307605546662674154239438986800605968898987086958950649079833325748539534736692289634315339087277460283849193735286225346010171948441001647836060693622804192104390202933893948106435694285,
12908215066575720481341913769299075146917523712821073779717740523522267813034975203364275970884338028408656360771856612112604074610856284602594905676194943648367579082211001659910161800083332537858106202309200812136428183262572413268001222779523077193770392383542884174023485467278626616073751365182539989561,
11542656191421662494996402818384250510054263097760613233918413909512252184299030021870132440786977049022744919043573981466269774801715678585259650556015767400036226155062911591024826727404470623962521635092689992588629274670351298442530834937444973214700223438873858588393652970189976147142921398950948246290,
11737990117586706177746792963870917855442914372560879414476771738860775131732362797403919070897559955753135207342744257007928865772951556680110715330514221409502147793788716015131231485888866417152234238939331558555403014033849511047628678309696211398642964560154144372031729243385283494148783631500937634251,
14015074690046501108743345709428085723144160836022799384805741281665723909042481631846746185612708233209208195027353885013679054837850320662872929989903918807143085606094397612807552921901207377857590016670869631720914125028080709803801224002212963760946973540485451076383285179799459565194646787775419719597,
11240124462978720687466052202642019329113255284054508244316525320488794737026983365883042918477585677551142593380545478542752994739475947212209928912357969527562144770975871003083339967536390077808141074276406343936790657281112817001885124072009190321652625050109270120518756608805036680716185768553349652392,
17644759118861461794532848268793601685993207175663066630202975393280821742996515745069556465064270189842668751140946891200485339607839458031544735645321099646847243136094681986094379798279589483748354282435158874730161644097753702777486575961144186996159794936610178295498810810447836190237871526815786960623,
16297220741333109274106637170503888393766082179610877567029426927083420068476923474221831682552007883462975785866815052305613377089573554592610111217655293946363942686124844340714925483817816687829957120758837806064287799136699988996316400620246107614958976296648908409687403617067617894948008942510479540653,
19383241418693364305644499129471639646391124467328807862647756122891094281376599886509540849598802545487878877190753119110044903096646457547663320101786951832034802611831694822744530763122019020112334965958060139110044515506050139330914524567303648447122416567281625061745814418757053264971706950401493336372,
15053010400118045742819797959291163974201749811090892952223894535594572012074467429701677435385961508883784448582598164335374841563484595849972697988139195833453982589225974758363831136989831988994357401415654943170148292036888729976658520167202124392767822417388458612004741762564830905711198963081062612992,
11606935663148712690013349150759730594190254124197507786772158946068953085233902413715211542799066653310197310528520655480947965021813250304529593368031310049770807925280325260009056660021065029097918815069539398252107158542687841985069266149004872302453889172388965789936456077712305950667038128312990827582,
12910582136360261336917014051333190039411277010158083620871103481984598006096991648299018353403496589861012407211895381704386537017860617069745911971366313477867624831203845026796644459688993589600729528960310485390107787978286887586272052328260267325527535539227971814130777379242401047653102050447621784672,
11476469450030701062792530579229703946638016789079430333073671913442877272110379497475224332375523302746064865614312329834129669510403878972978043225384070945954699882426836451198770702564633010408351831952388954283376848706909027857872039423515913443212914641354440316040458922815092820348090742433471104751,
11726978441482301943748568347363032842207130828185932650138036484823486321509866505838344510376301324674672197866835169583445071974537116274193678487861216015298443529897470199995470530445580080411118051576664295633149978828084102206620563742960069934291044431498546290257614039621213482751875279004737969553,
11813466074983917724396097567938625160659324780242004209383575131512910938192007311476426027463501837303468408890528846913913901614485689775177456899191005165790252964891643836628848340561302845206847973893666245337543520520725816970161525917137159472190396641920057470257376877153390452765348218502365024499,
11649807093993604277186946648793699144254004082921018465628355906717216164104532763110336641868473230302380225866302171411654779434992377363906945857879833597819135681808674990723674644121687547449164595076655351037886134065982562345912323232029271839102222943992231926338501124999483346786860423963878305567,
11236627724511212208226330881971094076078174220901400844920871880384023557286865690036520522601171213452308578610014983853504629969419096529256238869553958221062251555540709727284982543727971765674931747099676745742871198785035094227090709237528575578575873947306556697634029499179738033422339933387958126709,
14203248354425127883797687515534672989847389233044077170458416370860838216443686329369007265066819079080189424416646579774329623122192654375629880164948480101195009283332310258461908833036174863150695623286965547638374877422452875318774221433047484377317668540907708329939749865732183447138179976996307339019,
11236620902684311611794764375958596286087212288334788320621723402730850755465104166922438714387690161974821998683500513127451748341128470060034255224518496105831634499274111477789333783595061572986685618734441651465676633940101268720308769338588726806166308086657704213731910470473624114493907051850704127484,
11680386045363329235517395979957443312674553809551853301506405173731080635652512625270341611663542788480753785009758316550209582441657274307419824237357630417486963736207680572423899264406099102047095752534069523038951236796458251591434610037148909267571381982036021442480031024563719925482330426626494824474,
16318136865669634174095666318409587219964437338999551888881664786863746471923627436300211986246054869137328090851727581361284442221194235272721132703637341623001467108784324311697412729916679240297714757751232210142167502864378611675245838436059464970950252583093861532203591240156907981146415993768602459347,
11844662754836426628990292705739995470455026460784018055007083925629887555403704595441131461131967086531677569983494282565248157413592239846710569823211468152451245710960090405440297913742583419482266194157702184840924433012148823934998460720095456855436285790962589480774328174945373943398100621248597590339,
12906157899793244595283943718698574625221037375407458341618324202014304966594064094690210306787305039804106809112655032760786943622523399072047772458798238715951840017423224115996110130739394074604451500692766705184811404821092165653225528853495946328453602857952423592238912332127475074927150690336112848071,
13088867640432365889303803524644816322256674245319398972799315009050936531339613314027295777139284621187263547266602464997451512844497514938199565912872033973678207950212972324163168572989147753280856614207200765531318579918725989233235526398257248715486393909769486303868700568229517929765249005987167343370,
11568898106536926979812700519667894393953796871299310033216181362924057801289282338638543569916807503300137244126667922325047358084988901775869348716811621979084655933461935364350342874080395895209559015272983428790712154702773481485264482598154381438008207074207511437517611565024693269714219887768477139352,
11611189421497629362195778425098751335293025205227959743401048968859344863064417392727061641645687261934177835205707603153805980320631063846143726195991096503180210766190594820825558783786450149008736982521956610426013811243770989713440407877062105741468584468083866715498505236467258027325355551457916846083,
15330648578289338126864388096651177337450377421734634317069767295732411546092110882359433294503513572488894703286175082762573377414711206822575696821090618493623384622842929004056545105276076301457514617806053337744079717422994384834906229994300980218299066132377239377942915890070340080020665973747719190355,
11791737953486081144837191904651517755422616060440293094081061693196561870424503916359178277934725535036276986254500976664741631543811362597422719456117088758893745609881920201911044648735966639910829022351500618819382930328578018951000235692334075783743393154891138787182331294885270773433307782235972798095,
13462611025392224583903754281574774348105455405128285293828008728575579041366976607815251485577019126692213136648426179671022712833941962758849951786682991927701447464006945310433197789653760248945606289902510090923749090122081602587291412513490114922671612533512809936746406250219284373011842459481960513947,
12537890516087359905194148384109208561972718071952415550770259169350617255296386236374869095686466157096485728437270560291944000928209625565567767376288463954727054916016812276195850614832033716831484871607977093046323157773019099854740074520882417964489247061345052899491909595135784288312418198665367715850,
12907138859656617532013848143739900575640554468801210830899288367942677809664163964916300830306714085460550291347523877926781531603352100761767900240004970813506677800225270826376792198620318461444096846583883288653553759185407896034187474752839628334357502743722380849700940943780613746855956411078727932798,
14723385504227283505832663088350134735224027884928324834594168583100025259076028025036044576430582540154188747236880503637545573833870697795278636824263787929955400880315018071651790251127512534232199008482982015554734907075963983630951847710660503741585182663001504823932792897626244902916729937592211374400,
11818265177872719905096612273391572319046692988740203661209081972554602273985967623276339508338821420788182567454535434027091642732370190467636243333731921410545755590415303225270092115684674336899612842733831336062538609345279149061774590993879126101867917989680093114821306546316664037915562902452432820378,
12906228079454293407119045189578888723713433840324715126837761562007131064091724736508276208973498079334839864183105982198202329942184696808582058438803392310611139841493850815392643643471124681606409526751198109660419013750812564812124609349116374946432734734401899840613514180795387264399543252427801167451,
11416794048792330448749332347138534061308126745055401651823798658141886382176253236999842673450503243874622817785537996874065376900572931654830363394255280145273117252083906082180209276662271494671832592385165022895842584392811508828174857377269789601728280786489294611369427499293745217761502551451476562690,
16184077789911225564233160491244236286608714158325028961677971219148302036908159176570153632443817518208748880674716509942393427773934114044877805921437359305086012051272857169735571649706034124089737688955142250657176356339479261565839184292043559784385035704591105567797593354606309349538290887485382007137,
11285477791414193522271135233441066584373281582410296309352579920215885386241796211125650987800598115239267236869978992880269822796379292660162754278179133972005706632025258406687120225637509919322682039561280620348284823867377086434788497122669243556311021623393551580338244427474734370807605331115165974765,
11403308380338678916391569986206466071481461931916984917629435379735053514392209368371622947167920147673708610978292191777426102975578255964760904757900409953825645398657128030055208791030920068087993585830700157250915996311248189017970100662793553310318315192479322061006172320378084023039480458449821634261,
11598014835646055321042263247983336467914055624370148824091188415058573173415676941454751277507274526430495537297016935035994414658852232375573540811083128826494140826896244093740555345981903922419513128117630458613117658703835889137883656603293219559001520587508766800762461980424370121469997833112826156321,
15207314557535217882435584696020013867691784699911419010257396099141125225111085680578521157612143265684497910950629577292957071567562136630899874204766582478298739109661946824092078466634837820377133177852327797982480281808278067700999422433532116300470553215432566878905885796552587466348550185125059511020,
11235740648551945857768321256010550415128021408483644799024198431307276431803619398532724139322148802071400555051452713564344790194803920281893393614717537478403190922868490332889719516334973170004420649174933427619856907462981080622073883727629359755966788211007824318455030175156179844717284005615505516806,
11396556432089683280686177764654556897989607689743944456771662946914091351215216235958694429119441914074596653493386853067062635056334104988702551605916776144288809487954607990680060609982870189148358216477967252177046118403927730549526011403404641088986765164860085629403946080701046270286045350370365245068,
13645367775434565091865384429443722771500845163589101656675895675251787111344731774001508364275163865112705023113397954940133558005302375023696359728666809584075143605331285770512043878677827542199245900481380998307057941175503441100654536383209266662900960804420787822057569007809530343797127152199132560387,
11869247695141184180326992609759685796109249431474105131085636355678151038381345236095501465422244775581965317754255687147946430777617449632051349036354334749203895726113231628855308859087612462641698081801239164403624901748261461638209866234839662021874945977115823004808521064942898723654578582033489733954,
11391018814894618704961961508161112495589603802539802041392444395033024654497482468734983576699748951199450323373606637456456463025057067112113219670376533864569873350062084507569471149379520591134691432416875065760406908684865053281344098837766234489209324351856484309550628064347790385277057774314361331095,
12723052895973687881926490511358575781217820451666418040451019839133683671975849689520914385904052781444312345697609375499225320145287202693472731716957518970819992076200021836633658680002631500288826999101487431039404383647616536425911114923060338072003140763536514965993538928634199824754276821350470461732,
11240124504840561474256787999953415705857475005409304415043996802014232187679392358555420081986140444342133307222505535523584676658089245846241889897232937829316032753842506591774267348319060221597305344661160568680300405279155386738646571435088161604368972605477526928762396611197611867185809915744648270060,
12723738619623830970594593833849383956454724360741179262720789805876261980435047722890634185021052210329105563571559621514290495021362522523512802880782590125170335542903822379801088309314107145467345892279582743737048048554192936289119222696522677313520557419181022610122794291949289582960552896305311260600,
11476126891665372446126174508045146375630008148089676843067200705311746548379749412637956713071450915583020938353364169499775399829561238039211635194239756230763214162869886618498409437212195941962539799362972050875110523973427833552956532859842382781182343181784844468575700151408292833809146265544997838220,
13092006061941984097455565546044551363458162817254992432866864452208707974544353671333287043074193233856433263398403074039153834745194311393941778366425847491316546377915936751851141408347932626003453612597972730831805613605295866600135888160967862625071373643958564620501926958403524581014958096988784074141,
11977942802992040434560833181383641348359193738853398582555367740185399675993952279854650092800618253748979223464557445960285273801173616334761748275329895636216144199575983334903541320839663301532586962492120658116223294273875124521715890169380949486896723105547218167801888581767521598782024158807384724784,
11235776126628733194889017750415327230921223214039275764487615783773703238622554998935532997309345451809901715906528164745566093871633824040702991577625271564580134899043453168891599590590985183305020083025272750257180705706562469581805311718094692221218116425224757568724862161853229309192847550089816721549,
15392024503659010501259019167386286254576691695367919097061358591249964071029991552646596621469929928014485277163367274876628114490127584649153300298707309202217925422665796142349893322614478385427109242762925400579839056162562339433885875979845460066320162292829951740271557582590693481081469402044131411605,
11885700638133108375281364825041996325609622545688010292313374511396521529220306967916488189871532457774839131751340791237490878849629647454988599743729848457574411508547074689609514030390426373803359841097782431627446393102021380279117109837178926140814595111998937275171529842007143628562879825299928745154,
11977400121778069381186695970960456110280452790303384679499658486084604685805494838877597277503144582660757190142298591444359590757095385482444646203121691474718303443409588122116721304490882371377796313578348796235039256287744102720392274188011356333824188869357663494945320494297608751922025391132727950399,
19568679438422075902017421937363012014860527114858174575424253371336060075332320306278776210597240175941705574527961063463233900118852218552494838278294635908581729081820838524914025385003382043235300758196452423573596887664229515402651928919303123012619337139923521536540121807479693227321623258327434625024,
11235666925698329273113039793814649292800002046009188754502159743296453285262563922176182077785589835090532991830930861081280038853248102187537220706071449053649793271307994769618653465664127313656661374786890096758105569181902374326043875195846832354006827694810312342477261556639712398725054088978685068716,
12907155757852370060270006351607210979368476162730909055624357306938508201270280852898566217687809846761601026300723342287813616849974868555415925394004556183545159371792232297392138927480632207345318830950759304164531664098784641071890530566702634759963511929463471166520562047666751713305066314046323000994,
11744331523465054964422803143137108272773921283319492797843230846893960332500467714021486776872950349135812362020916991137663520487441087492286264994295900835640449635460887342002407052642038870251081564946728427095410991259724720422875524351844437283604840805668227965880371731431947917805255614999096729523,
11817797012278457915681850324861142816561272734109170463610703164646881679010698855919258208082106740972701156010289081675290674148182130337538566785498594016271760767916127342771923888051758806512797214701663875724525166690805202705446595176332909355367066670105278829118734335740368987941399751567916631960,
14205346353584909554529801063614876923254615452238644711835276605103132698208330261723524646959834659294797458505246388470140406441524659401247440703327571907659546606757139824244212704987680906913679762414246884433216136209801176405405659187785116070796449091645378726885055514693871643663339991511742471919,
11844198984365140231059020313618695256739136032532734296469078341464598015910059971054743602238686613042055318518726311529781238139069386176990407661777371146345524160146066528922696197281104859351480078105620916507619441670314127389362389892334767891830405891210051873314352039845625594046916914754764537856,
11790417485386969788438189722013466721484179964172604981562065698304399587534640151200676530306821057260764778433105704817676896256061345401455293027275722806749066873185505877716425415365784821743917685288511997800555483649395184163046290003546931137822958161612068782389808077414700753932277946932103877395,
12903751949779752645181119894559677089047544472069081807014003238532984527863747723702313801533075545242407751596514536479351081259747366745857116502327961174618288293880152301568376629825828908747862141014097722368721884024876198512002201123037382178888006502266633304171884063640907120023611918697700558778,
12720855948764161512044465600902259131882516761580469423126652720614809177833435347345001906191257716366745244781404137312610618971030440836510130814348629700212169426462115535505369099744397605803733863056524709238066147174795485984554636798932745717866644684788343780299129001775180618037457935945277676957,
12909897155647982091607157816487874961407989401745884749507198543951446198363429372013655855231625548995136857233634516641486826568680024496153861756271898286625454737961404046466844515405772137054156894596983287541828030405128433602925280306012583306296539709866524881017682807907657688908664001122914500608,
11923422123237554976820013202919823779752857912542092238425462998574537055105979336588732381504773504479842054250755355614613577705720617932148860218649027724089891673407844149578333084744040585436599929190624407578148200284363804865425903461771028226959108754401927771885349987114598902194254759162840319591,
11925822375765310909992680317988466302410211218417930460595991153004578872998902243056701231052017875714109292352377967896816658447868196363250083728767249512014738704246784723252949761117033688594387342884816712266601246085648905875520277098599594531823925418246586247459130420429262004905920647684677803421,
19383207505196638388362692788535841943263883499092047090390294024180111604604880715216456720177109850918659364752810608943556724828038991474536378612202451670777748346347810699864028179024485124386222035550253173059720194023016850958408389567603497899479253708514077859912011558923137806856412378676913803505,
12903752117216704318413490155255247304133963500260069232236203448965074744340728856677007161828589858595240955443201312753481544200755558457417039886257281649761441752970002036627240084512151678916536625252558994398258358862268440945830983324548994772698922285110660446763821116623002093033148311708043845562,
12909897155647982091607128410000244392461168469437902980830444205641875701881889216462790074120515063590201613404765091416697013297957537010485898496581484463392122202304258492387970028138687436041847528645129761167894363422754483010328726432023604312019691308458422910942957893077134515111091230827633007826,
14019874860252379784410780551070582423886768753371744806676703727332721033229184264609623936539790330373610717374501005297106600242634806461881483191803791143900183377110282092591935664737689198622254861888143694826426796622230913849609402019105334297326396002310980436268202263565018236573777636076690179723,
14016725480995350477410703840269255234590655405266758058593652153178816219251278308129556617677439703776814570911443296617645324903582815138956140236657730510031766047524891098467811526118904410471245354569404907613084192909435425681491275286106946601353885225800228708937112085009994477069299942680223776768,
11235599081717586181157838198380571546218752656211815947760767030365263118474483038343778468692217153600332370856112156175239846710626994657525699382760313347021330280690131724604985655342803518623736949968861122580588688595408814251932440183676514217496561697103597949983727026707477214673897369931408944477,
11863068887225828920135584906433409527202450933387146019966048845057085396358782239580891530829766717785203246545973044342230489413778715401817428485074869836978821811149304698754501943678650593210089805532386808154916083737070152132727418452427771382352983123303031867327332484199561627558738704935432519990,
11938194281109679817686794914355725627722642216379861979845130060003995097046856186056618502701346898358099450480947328991170013094832097003885281369982398596597828198851986951688876540666867858653710232767025826323139078247801704241718048938672773258867912452920486794029350779160762267101859616956560245819,
11381415910815719254389887334527357034107757890323592424701948283754458065687788900113892151726043859038374842812102273825750701978162665486143656512162083313795902033387706279468628392681295929611681376102351857542745550489053301798700426913814846368132698840348465497887479252792250355028171126370591741231,
13088867640432365889303809587499961944627792935980773591321935675735892713445281702094987453054374319910709429483010395880968754215094214348344499493123475785868075704175318121181330315493521787404477851876970128181114816843928108681401686003872900861269930670910279525420189892399085865302594551634538899808,
16554399274538541269432082378861212513440526880651864693648415978152255775189999918424119704527041091377332200469083648130423282777911055405950146476541842102977479567987549206338898370881253053799635580321474789396000353056558515058959406402720933821684922498985112615843311041912460752248107433608099168664,
11934776796495939651168850593524439989566950551880367151490235277628693586920868078689690949425299077724906924608091200179300177301352904278596897453606607604463451239175212054474169636851045107413900945827250384601886175157464523623781251869767760841467713590796885100953175609597549387852100455421406021491,
11844703878490498339804342384615806199648450957389907018628133001630699661158299620901803511088807124139534341451575829503232244852159629258755145753304052547410276487863031317033982624030667094681481364717594619461784417378934931711243063774276456184170296940483854468899981629010982690754825694192519516943,
14015354096535183720517521627730693012654829617179402687581716800767540548027680614146851688190419244050984822283171461110458673119268369441188200922770137139328970502893588737055706856312722279965530173633931682687145495310853108429864947375376291328918540038828954658605813571438191931686918636974369516743,
13458496442806496877994285349728138947504886717491542914779544638356931633671890410951773645167238981660188217155743765344983162848927185693788806301274569328936141900420597304507848042671512537046172442733234809997032509292405620377411157870710156678026051611618768530962395243902948426131182716097246201431,
11283625284591294726422786203962082671552792389760624187769294011163934002765094678488513077810256161705702978126601725304462060889257483324687064402522619732190451828849126299592689950431548808437652304750628989970153190764401558687150113563572261306589200031029504019180818135273604829157183303742945002000,
11613438889514232187670382958733882559696880858995877660744473229383576594895541039729373097470607893121542517296826899898654975395415479023310766244421991234350008459411924661274503498634125995000429502553250955468187625653121706139643769464358375069174483707587346452039044525199650013282795905140593823435,
17470231618872923017754887836544138987603758865449744684487969181922833732603452802782453564806453086151444851327871765868128864879050244749955430003452380393468765668259439741175887147362414043874247091325537095396332063795567179101858693447253319526411063609131254927269703257346200666334372709118041077706,
17645098703775771613956146716447806414154789741204330076617276137375965409424139453235030505260717907052828454508963228034129966011488895995023847867724877662645474934382888474477856170140525645952220977798500813642778623171299529644161731985160090255644211700002305600240092104665458590598960742280423637854,
11588928097668933235712474665724084156701171024091839660062594666280696096979196768931938917340165697202430963989620430130244557294849231694853786009894569020110677920469295961166860474452220995160371573084956629799921655611481591379483040167522422192523592563073321225473209030864474967671783406779707623197,
11819511430877384335204883561713916879550836565476092361274523702235930898376739923508501403763912347254145992530146428565413422127414986832335050078370545231902246722344692998877034675689821141550923514811363463105270783226542505039408364466612802035093292410820302379740238712973915992905666263976979153375,
12532708519457859726186552321783923225351458315005344808889040774585939506458536083952349442289803471679421995404570204781672100063884706582401749526896307274333768689872499163990017565056497733754980176794287057552513021013853897810198767320936624574352706544746256549576151414022932623899543659799619115889,
14206339695849528482439634408302254797242249208840181606939529859605928636591603352255007189606355516118261067856860262859667370176983840512966337242636021468029189445241412840129050427189057330709201120931735796556875718441363029774313869259997592629967588093403353322363023140311074712806587485298561941597,
13091610789349377988807415651241139027868801970395146078564510521824813078088134207211690793784707457443620409442085201235382615502166812444855248096006389386293639094701598477268862858592293437870266752033854305188692221158668816524237437637303337659438325338524333773287147200432842981955621145231062763520,
15063187493671784210167496151435670524444425076323424550497599889934139609400885652338906504550627323493689300166536679827769186353626906674207556055914615346853887855961011684092488963885674411347331451752312521117709343036519549235602608545677148113119320699991290590661209614236297776180573654956159305544,
11515828765434974402124054292999245403268416731924584342899854720737111795729917766550131345441327771461941743211222888976572238652747890951582574631045026131620945788402365285616804630389825371521006977374432600403878282305152527316188357981480626073145507803828632969965899896663742561589986559053165298133,
11899487895228482887046853047717597738826809618959709524003825484039782356423290088039224863068657760446591270609635684666175538155618189965772279195491220756633972184695889832748131909955485453358867589978782552567779920593154781583082028281104327497705987192075613449152597403882495221864081981044081207588,
11430750259918880335441110790252492748534583373601892209008129837143917015030302608129169845950626176303896367623225622212418960237926006945760562484937403259547358090195261108861555178045124396164858622770033144634465092202809551222623022474020591604754157418614639315646947302256595016704192412429584998313,
11682701207089868330555176068927824005322309736057736989528656859246835612161909745564626110081257054448297118274676430513318206692832733988723812137338679046444674383535146534298505222121106957045198518493734958704023668265515396113743322340297512241681819751171543414510659726363666888690707176469340952923,
14019811567009383551177406446591680992520574503667197926137854037601885051643877436374656377594609505609289673544448679271646601831982881397210397333333860722875782354931794271622536997580315151318703882964884925858478078314066612275691568076768285077834124771481924173321520022139074957001696105260544219831,
11877824136276787229678797497646784282882947240114704697732597181885672752864141339274989287643332168033952218620070148094940437604436825864320088924309092029253175617991429011266998858680870863689818965742608279915525167911824956957030223374591269120048678965873252619148776755329453992541251276717194971161,
11713291415476544048752255502695295481341677016693127066041711445081721539947081848413075833896143515187700520913206688196552300096322643102666204795593755119205210649585216816839804114715472459779480884567202268461585914004089865593380250476635771896874965925260103194157949779964867669152177327555814407381,
14846831815998494933258239074305500214371964600338158546499708676510945341085080538730231244316196467386304911218128211470029094090421845165935680332868395913299993065290567104661963257092159863120948077549337288433135191267807259247021810569453631028698752711146018927454123472225001341917952430395785055959,
12532708771933573389246679479694721712659059070060315924732101707817100448301386271405568238147091647823794748235865801395428220946098227034601887776262767138815765133434314567438729803617684458732037471222811607652207177681986027579909197526809012555520059868149183428262809918733422401026708195544517182620,
12907139124442045264840572405426808050285881450510119688550648252829508094441589188012502376133726243987577736156597466404814487236824187989087498520915795007912366661934064408921424638195128212525083512326458770533083736411916207731632465546054326086558142442085689908150766374720794097435455161561755713653,
12723371554681045151764544992158295084485307507575252391809716390905516420056449923667669610740358546771214264852685898602246025516843649869275629660725302413602563887540199779709971531805245053300581956763180871840887500552429083261310782598951367708830079311472964249412483024542203604509131584759335748492,
11548413300617891532918031112993951971196467253469510282361899285519955468290378822203942006829259865236882058776971359298477222106928480340083407009327000542986032573708150553012992118514454255278041831520292296743859275164797797932701681449752353894986447587233651722386306671756894570618890366183615301653,
11262018041444208704740037911013969651694445622111428397033290747744528738389234608407261857420524272808665732798717450967186937568499718238429276196287067768561010583993854543813836633582143673229636112097307483662776015021113259757613142659575046255929246454227098957421383209110591009907562110261542956350,
11489425851595492645677394345912062902975441088344045342008921302937265241932173537095364189044146131884133988911284981575213080518975895082220571324649158954291157490584860662749946200343319894028895802764953677070287435745509469730416219529079417916126324351735181824418732738209060432205198540068288662707,
11402379150285694952451474287082636675658441337737495810558365243397840393561314794936439130591505308086367637718061929197641344916451781008311395023572768993083521373673061019283838229154644612247943721085975281998977011500014173751248824569322425651028916719871482162193049921643245776052145325853993354414,
12904396456849872232685592342216504325296273119742385275485547239017280656177036947830852915902457292268003530632062774127884806553692673033002289783772937563478574038874972777654466995390173963778351173848918339805051168675201824057394436702780033338120082293990521453931416476888973725625496245694354724141,
17181862807438358586163601769763007885814496772116550241460487660270515489440473457471338495653616170034355165206776662834306244518864337777056843621788151064393382122562985358468533677273087718656578739625025165854487458968634970052499071798673518237191413549371260181629365440471836794010153892529769022369,
12904396456849872232685592342216504325296273118027068337982486502795607787171616749690017365279808559642846220950594521833748282986754163590385573907228179403852621681511087598988465954497410583273686391953831484764356652126841091192211760561754702697141556117239892252622853545210729695339631104818255037287,
12536137605438216925359134859467437135680483432006490736536571436544783702972193861940722991713854192674667618497788297948020598393220234341005662164392562472584974238945494322259702807759346117721845442734149548919128911912169503468765593073354351321475691421959694070501757550287774502392914756116543571101,
11676574739393736766194483502408033398406437572251617222722305906329019197073345179496175865215798635637156019434562062871207969735650460987112869824387600892105490770258246497322767340718680992414440960600590113557888325384050996727557111755927335756531895593238024478287192423678273658696760469390164066422,
11276081947701287983014346820959968520695833817944378783402350182256819531866515446312077311844719290938803148909410868341133854281455873546036991094995020898035304147248909629636378456177444237920185125980407046252018990440584067150025865942872801229293672230019150352290958501810677546327976064458177024247,
13090925083455397051477806554964533988742182343029517696126326435493965200272860798940192381364280662008716739136937203678658764559251041920398708549213937998871140790155338561967947922625888794319381413165271042524200993096965169180684413252027976633524905039993089534522190516424937231355400113590057537235,
12909213342441882448942223425194611437838292357782020706903115280935704943354384771201602066604587183162560322266231573060958043939684202958682094164924963149648137476122563781747238216575497731838827873116977979012667666137486716861191277039395979830914836306084599335160261610187807641978297355922708857254,
16143265404089839091683222302654519576101556369876677134572467610165684416986751848972151708437215414128537133030984567201547630515408262991076068711740081473676579582946206801166702872026086248224894530924957085423148500801621870408475807644911034645645285127722825440987634861262190296680516852130447590680,
11602926018574918893924742472352174498521464780427051503586989349059790501535894414131097946541348458269799114308678920883423520403277358360996591231442947980264610504788479411719719318360667006330671590152352530401535720690764078150847611629993192437749611131898730537278261780762989817955129737356770575433,
13463990487052387644394778992845106438097313101007516517271545810382383357391196083391822326807334178596772736007645460499356541265919206007164019686332188137763825929986340109336937229617112702021801320767021118025084081669740621981043689895347829844550038251726152262064193294930053539234216720251433911357,
11454684180302575544566528659234722395295995157430357049298546354364766294553053542537920644915441510150808182916478632085652512544969374181821235136404344980849715074584565097229464974260925962171819339694282855435759456602821475649154009262796517594627088156936196073326114550210652805946009207430860080381,
12349626150348800867911957873297664874083514119328296248052036675332785665462414667877798104587314563635835808714598944329875065202910593365627933192556676716107266230283729455733284483373285108103973248750024808978682012225036742821672583969610261135181567889268350111286447331564871044736202380463547816829,
15196575624060638665214402118849258120021939377135202537237667182454245627950865515695190941964202658291483659305219473160085142449739327722626096795675926659175131165985660369962477731149347168852779390809126341399476892329912167189563143490161150118700018082265751394018876069481277335638898651018237183759,
11606581255354523806918902803627939375140543113470266313840617049776694545336040731208024717980395215039776658420198362851483678384838002512287808062945489305383931350437322885733880182149858373528593452458118361530988233631625239473257377218636843645714573995305119598677040571524610712577833281787249689743,
16513253155614305429563792887888093246144966557489218372395478695071097119325523882909312072941272475843639148155640906698522344199382649682764639877992769232554223713903907154773845244527481653633814021795212317899763383771022475385018507814384637383927219976125239609022121980590399908038255610560998115305,
11281568061937135360966757494501434595802398829298311689580121052682977223465087366400050392358922336083383502993389849145852264831909822713591212789858854284074492720002252123045059242092595465115006813151262805152263145898700334157750528005418087887334858855360553170608519363794936135479202795832533156246,
11391708357885687123338841720165047028297299396625816499036319478550565139298361095844597312181855746311663727592508676048585807917683355422243938569951828387175305563958098461296830381158575686523393083900446738866145284440256026756180003775178202062194891629658041294282649744063043988574011062983672444365,
11390278877509384111903220260307989477263382100963575404818901025212291389689338532583314961164239703517150615808749127857833869162301166334837542086316860698756790299276441985322252733459759611054490971060380753858881761842995902513857515628038258549332467594705935408241865850452065730714185825434673359680,
11379411353066624621339054210594283826164524382333585919869991277373197452420233470181158357286342249618457666258200609633198114092754353835664728512195671734775485050932886585783127835355638214484819843408173287361328219350979565069567919609774033530666102040036212616726727054548373381269348587207221646629,
11876429962062029657445888736571137236314015717931768357256976624823475322013324769138448643818015542994881233450439371179713939643206633739297650502534939249299682681886546660899682418116577185439830169440769917003688420068781711545124599442794772065151254300586643018211367112636807305009768957545362363677,
11873023767328951957323581111081136321110234588999695070874088568028068075252684055863984643055118627216206620551844169509846162652129378090245285110464826466302460780327037559020685941515720195022476804133649968054159846719050406459615754021153927571452604875978461970289646471171954928984186069997985872988,
11378038880284455335944907838616605615146365800240783679349616515877308821311171582833193120578769391883800966192904159520007692975890248936216420748375401728527052299101895225333250553509811521964078411547917709205190330902104587315228457583175063564085426714295172834405317910047101498057808710242561951860,
11274024630245352582974337646111145631174319310569073842823586015388398916336916865295899551596185521420875086189831103054776612116461023058446212127791869381107523993948085481402343656697690132025525618081647183312637536806196547096766962007512921744109648700781938607811733375123159197856720559576640132389,
11571400267779747629969308577737766138534006622801097217894789269842051044581893258645046630353738454096311405082319524474645643674296035080963185326794541067823923104808571385841921331292164610202514561658850287264294812694701644037985232452720818408808709002874993908039669279395673898276856280274173103827,
15032334314774155371820240463185749819678506775008660970201102179074438629525719193645512797763189199298566092331350134097540555306613982256780350646709072441771229453877047085430783323156618897985387119309045267192015277529421834012505137677465670148143475228285316695255923951992490927080370944412750430057,
12536138149564959333009783238904087044194143229405489516142137433413246130221422423482949327541521780985163013057853747700438329673682962306294628738812773925102254122107694824167846318528427155586496364082766768296609605053997974137878368650974638990692747596747945885747141573215433741128057313666612495155,
16184411702230974683166064909222634441529085740385961098724659635233280890678403551570140233529715303921866979516826567035244064184647391518318639633731969471309691373047624539823813858901827534876894652195239850950083525371681250063474863984255279820119691505935854500373820069897280857915812970146643837574,
11958058075725291110293775680148757620490480130545982740577745598619275271794768109476283104261223999419771281929199693417794634132756056546904820200152246647106861236658256955598352756394694785945418887723218192669240061605702589182230611718630678940304221501549067753018713705649886535571813446842241025121,
14016712277485034426072831689080478622166120736348815564021259060905994786864030840051330831581321037810152029668458815504091983381348927408623771384220216052708321937636839238959725553523838625871833695807178745258096368517742737608968497909949189465797900214261898349477778421625193784812622763752207953305,
11876207654318242801902031757947688677500940193669989663038116302538159662614055379234796211558706898551361762075088270633644967335977676256994618814890822451691646170968092727941153303429685965555909429427670210879482280445345490052356536083602719259795983423185892368991375052458777750249117535031577379597,
11878266206526812681146386299079340109556827204755377841994495679035453247678916201403460683923535249520419983120356597813983060838705530525165681188634385436586738337083590190069796300775344873971413300388958548139049505206960520314243257755682467090068202494605875884934894425403505161380558329078464759949,
11673477451781294707148406833810502223743570788970748642324624353995802502231426963270657332733011185960983769454547509447147623735768157524823730717917751535630177006361304035221769631978414163865460104174412130463337582981618868023331632444989533201502650227564901823590132415682020827338894262505173895549,
13461925322665416846716869550176682277959939525183162777132620759266656459931426317105783762357017687361002527384411842818323907625476136257040462688951616215241050369834851354614585594417839051556071461002375084041804613360205981329971118398016736488156889377498469014335987649284227116006230571630237551803,
11235667083688789186391796798216190002335193052104111018433859084525671383280838755736413452100874761982516118237596558555204442928021916338442090881414405436058330360924074870090101645723117176792294565743135719700523917275051140632574249912398918159718050591498213837304909309929727181960118422137773982223,
14019177793507181448653456682614802697548494781694541092438101418325793099412855515041812179424453635271759753750516589972465997934649142465177210320708502937832563551024533638866524073243421873457877877761370360195563955334792179420411832815007070390525108926837696260269629669672861928526752815676973680545,
12717521430566516599247513957854855836634948351105019268285299596728221637429984255410829622356828435380090683149616299887657410567053304719130613107331607192250343870470006101889374250623319276529600610260558555956202986364006653435582361633015381073175998073324692050011274861002872736523857735738344411918,
11464364070940068486502714905909819827511902336683254770748617893910194941761448935321059272961259252636209218615512788561525123774225991433604702377954457175191801475557114114115802208247331869506303342181149597988643038887957490512413197727495893356834941340049314120827468197872552318840230465128934211586,
14018782894625246749149988708334019645388851026703548742966290999783544881760295923887146389635438028894360443168723242277451941943557579224320504854684079628518227166174046495644892892588009551547239721244348174084251531245486636965279356664782788732458164762977535956098136807116353419494033668950838189451,
17665339397013409774569921401023211879732407660555782617985959510424764787566664344456120733777548520576286922620289195202195195710225707555054774754741337273013946127637236470767582813936481727317941932160638926245660136430257799239462211616070041466999153225626252475279329429332441272503282940733621438198,
17603963038922888204836747947040124129372571813175175149758030206632900393246056869087082259503921009418803184664989544563403008423393288506546258668422800879224843580842201584054048865084435498687983566046587915687575636182652462364158539105685607342469185092981760741090412324914927424573529395056018850699,
11607621100045245343567464410719847884549555011991950454529976201077518328896541679910134605551503645021353972243324428168077513154888306675615763584607803625698423635230005863238656988888302544796373146336197721632844114812175202605615475687800637235125175919992079218145296020938132582542014708168069776243,
11964230120273785487864710339769583141217101772495020174015856864898076158234058745260491176752533717044941599163377228280975172349583822730522787155547808100335518655565272130528524661817437393863245404892700988247581812251609046238199758907603855356380590494576989897733907435433423611130968250629257756674,
16369569603194511687969373736801143824096263598312168394123315630974364517540380032351824363039868405222631860841886295823360646339596685119257102003665703175622394822853023967812483075612330942579094915342325764699354591341124792840097464586840406573600349340148726321949865833954525517594778786377525501329,
14991181227222130116779405069916729182629142354337130348698176699917708781894493884406154623033358824393949468568005655057281168151329252037341773803224787486085836994695135509852750883739391396665534883715841408383375831111174869971965783826893864383074421509960446039268739066281345366119846189804739723663,
14908893361886783292309405703611810222517292579346376849260797873948537322684234756990737192245560698192509136014996498095752058352256953733328239775886164693078768507356919329356433268061567833203081168565604301313943617843668268301123489492689277062038657825241509060038626654632298977398454195394201945883,
11235627528751146995131396037634237134574832109130316231976293832881854970925340455387997709765743473220094529165745006976646745402686311601692329519434498712134115246007336325822997143361044388655278040343921340030638001614083507476668480293412867642899523857952651056753724005795344432939018416425072558890,
11391709613778347578323704078518101977527302848576633836065373871366608209612001608398312798131334652652050581141842226016977859076617934588683415285337368591327112858655135780814409224171153738205831654628019149807404810951461967897426083352145588329200325991527022254476188882398603013438705211560550040855,
11304164367939860982033997322633485642264267861974091837066602762380675055911778770383158268837169281085390225601159031666714692624937626006685051635547931881627552728442544502027606476688131824484236894763985672692683986170554496005629590895345118886462318975357171659216563065920661401793973731706916420641,
11878266206526812681146418954330707198423353826051180810881750149314864424350630111671774819420869746511873128035011269243893674754191006630394198415128629886924209628829743305421154951245761256179031770798748450134112681230651042935231776442269168350420485831788335838068166279478128600895960646014287427621,
11438642255664818941643737023179531945223704210863565754346894527166216977825100557695786375378552238548653468909041425099032196127687269269958748098577388582066019193113437238222835145194341285946255726274826086879368091084480514972687717765634355572343611414167672444323316946013678192891235893884707883389,
11389695952178851686773068388447599196179669074050502523051878548672088489010262221001413850823183242717621944843649476291943820055176125602429524963547812190159695307423200645951142984285776608238304944982059004920525721839063405497654918624853115576484918884394109396862491596235036396207503093401207217019,
11382078028322118885936717274518960559022302362292975540365245595383707741564348681815759938269765626325757269123502682491822232766296696983175615138644722100504585336463966767048752313497292706957419173546816781190065184968422814623243619197118865186946140220379974443455287202759641245263654836824192821931,
11413949046798579290880685923300452260122958573421169145682396911605564719666215068106646574555342623892764150938161420856239083319209557465493000167277630518943349978831110669501664517731718201185683771397626062871910622376147375117974544448220766701357861084747186189758868186630835899130279039955231161437,
19383518562471678435825445040375841297215785896422136206118385658442513687454664835385296763630408205850840508832302143623112021746763847092510190713848740325050865683631359268697883147478529593658430736562404159631066135642971303057939599756953519056238542169613317216444424038450582727578217565649772321119,
11707119452531380462477731407039079618980224007508984658919127049588284486897289263733742353321348394948160064425441698628119238072095255937289706076527234489515791187111702978660730837685547332097717405265605423900825990537605765700165387577725768112588839297954254745369025047489565733791533682498557609383,
13088181864460454114782906807639666310182241262797050246579047179839833625672376389711563244523114791600355673786466748122543470007081236611306104233294722354888620659788690123069398896929577683764360310734322440063068617201558367697479798751790329236002135131436252653414099512903237255194127563203424557945,
11283282422765217075872715735649451681676324942606015451387252904180169672283167943478271956276846127430031877410849859843671939609243676170678735559005812851973274167925232691154403326680918433781533608046477826787120883367549429431118357101332295020852239105520994006174533984281990091313773991244202608472,
11880018918663510649148052925259763774260596332726731554522154903788753148189931042625796657348480014777799943134778476746066785450407924578743273302951668364721954841630777307932396609357544614113672315661919497053516493091350284249981276746906856468728166572270757541749229736748186883385398836492568432329,
11275447152715467441933552912064201321094265335252543425643879770280201444018264641762231434247250636670545329373460096489506151443180700154020535664956004755890751525232614460532968222196247121488542200119927797169324450818783056732031451187260113448507079433532431855253013181593109238234182399985682660235,
19198096033473401676964540036566579950372361663170980646272471592544845841171327839733264923650895454262845231645362356933945241536363286814064418030386722797582366198968681729761771116587902503148865351847654617420508112512845668341450739324170714934525597274678678685283172235534797912382269839516007347840,
13644339910810040160247496623429819531523001023697292059565922398509073695416231676072516878533924931242390947092189888623734545856325393236755080523118898557637341633884395388113644380562808529759591666642681588291420609862866636802016799154743707649008277496731703630045128489464199981568424195959791583232,
12536552814502048187845054111728492456405596161902825364724774041196656231466154748401033937582015682553331161410763753198552689601173384037616677601298641466207508988704677956622964339138384106135639335940295269641100100357247336140985376942995357027029131132420418308917706195829540632861547875227243544721,
14980553217963157964408224849241500779148635615969868990650179898752296971609655508539016769231934422293552919862996318911390405331735810519970251288469668072104291786371652254964210969919726510805287675315520636030767086728924249076430628560155849526263288425209149555883756504034886348922610100063623778004,
11945703619967851041985442632448971627339314322208014043166350008363598057157345898090529415798784762774664762467097012204941421959155683577823276711423858359805111048654226683452436766862684286705344294943833573687088243676856517975177515689649944918056473447813317603702519368628536934017709921025196370632,
11235655750886890113872922064483252754667435944620039907574249089924720991158647843368773565041416122361976700488098482048652703785849380579262427379122624228687602945516018051477757452027971591391854341185331929132089906388788449709719386897990083189996718100660566540152923425451267329023730940861365063919,
12350294126968806379612207510064738334882456369861670709906465648354060930068059466424390065199108109298605789658624733076034524694126620223484880747446633382913121164123830755627776572173936076828747554648021227398426762230216541713099774699996924399195025948334346334313933441344188256704240445501979067669,
15176352069982876015331507133720049373251920525959446666118354656426892812611932198912519249577774286381754279125272908475461503796341003508520677465509575034498299406553151364524719033305746211554563336951815071227955464322218581261555165226008842438715900120684159754300523257068414903350904392413187113466,
14826362389152722884377440176001577285123078417622301637220126726303674372323752702930920957906097653875375737931032432562865012205147090120302763040522717775983988355004135091757903150396984987371347609730019696971684732793657630151287169394052813474567364124561652726352792834411544586895365267818993518587,
12903710338745274169257655602884302215049129278412889242788112115625583973222754142144942757282137835336553588303047244827850425027390856315256519178367696795588240109043600079998788327404263648919205344233923603633933252390126093143684875024273173552559259858824659800860295224861499607484985434629808040289,
11555344737063995596737436570677481361961508541462281264742049523318678284784712267454711442650966317376263992132776011456709222898265293324512077796597150328001676785015822850359899445851603771865851085326248418811974881945149914908743753230595205550291378124173010372109153388603603716370218483588432496719,
11502772631846551390220528003353801910857096470656404410130338821208433345608478059559198893734990078112121060710867126990637950087063518680275975103627602183152679974559057682950975820749462031321623985652684980925533784269192098789583738492863163650427291973681572590493180389754890812581687343124880567735,
13833612436564783844188449060391561728750359706638033050351886916650979723800852982048335212027546489341377136077464877639400420333279002655183099064475086544510082674868017402207433316208505050608686761811489449602153588648191556244112909381268919525265099454944307402731717872048190869140409832635329912749,
14620870439540775723593177542905063584694422899972015943712315442926060041382606016868007314765549140852475166522433436785781110811500549287085724639831635615784401069304993770194352718840395954999834378475290346011764060344200057673481908995409587960057601342452495571340298000176970267786460919296111903455,
12532709001853101326544086508250429389197425660758255556035773644375807980926415763713692927444849915165894249638355042394050815495902974390123326053645084159026395636765546613196364507896934369776887745390025558134643773219702256345740411360186405741639246897079368450735810552725228604113045776760069915362,
14020928599174078920647923547705346726843669605840815306111196829839269280203661324364048222361666574810629610025628865019956082012613697998347598513167182769406931926596538465471057098805337012764847934445588620744474827443273427051491212284016889753841358322783795128975622500350200267210482303767211704459,
11334383233342249787918889275870439475519998891776514545973602417371987707374519309803393968363015904940872591527609817364872062757533915721957070918453228427707352439915954962549009762683187917194206839712877800088758832691831170208415730262178767984561493245564092053465910310298684971164308333764774632861,
13644351265278402210502386245961161150075538650248561608637364211463439727925215616378428292935694026920128834829432432989641940229234773459340184945155621368289394698775333415410457221810074826535253236062338259952981358119160325689215264618130744496268834323243175443052773149598136198740320204844231103237,
16276999351316878560761034125669227694753699300703387020625994780015508756320416113139639468628453544093370713993985191397024002491621918534718459361606929800999342932618963638771911956326914406396428894772505177846856314694821755075618216247205695960279799278499532958704122629201812531633367387423851775831,
17274783132190698059215148476934948983051785292428366959234468594921582145757467234326379827032502144130683105224084058628746904001239530598114241119995162905358796008474888656508484550087012754216276809075095578770653705360144651444292348141594496594580031304272758062601664215826355552917720472218658702455,
16318136811791553174879997232845438292997607673164026992696711023402099061556106858816422272808860377778023779731006852137117880085010685441524728911706987109841020119172605835257232972329154209488702957688398947146488140495136423796756434397548801745051843960833144945638204765734035501500736454141556851181,
17315586294749266242313150466112146731159848790285553474185977570716041373206918024513171895397105479082188991267394131590102418933652315279796157066803531577616756101384845546085977346414348873800752891302161347650873184792968874795740406343817591360911801618355220023484612490138109976384067088328292008299,
14980895117805055496285711369147979697614570504549210536986388204689304752964908503940128736137095007530245083623381925193858574301880929503005222494998592473419580633981760821604884891988374166121791834939468487860052521890616328243467097042492581827815186495990128248416721510684680611901464253102218150322,
11237992408517850057773986748337305080401690248136464400828230865161108090856422271550813670403080966055765203268975414773039655026602216195332469925182745189798603150548659666162745021158462984663094197731097050465862556654439205138032442309667514635918291789646998424064872520462274738042705570946324398557,
11639616973881028721964070429263855969762059584270850629986681604532940440070079301974727651164102932211353487304901102410526673569306201404547595091776611687238160598569649108966837146265600253766260595040503384460572863735951344293146291444759868805975883774787296960053577598406711289900057592533542339838,
11309004395625311399720620810056068458369716887178345634104990453059672231535263293099207267081122193504227720651460058210772833362332603397852578814002209013335826446096194463460330128021024437711108350456034652821161890942532400799041524286222670988299940568230278136833913032202712248687408647062303550842,
11675400788657706759182918370330238965199340783458850893986062287698878891168583497250276138497482031928323104847647759438991944242655340066246038852074404282326918298508634932840275684632672405584078616995964837921835484842427778148482852354035957859573807060575917131127775460768614902740317896026258475141,
11508944563283329355339777819532795606495723914800675634130067881194195041108841195879100851560258647436787573079344107152863269697854465973511023214987530601201873324869256765384405333638280899054048018594645660986111223988659633946898006730432326214446071497639504823281111786294009728362271202108023803609,
11792165771959612262833640580379890791866817316382912420475849486693348343043310446621884780020602555196629992241459525734892209238019862465904925679867512107621092186879926248266152651054692649446850076582351548361547216610103352372114716353913988845972454726898814543689165611879300380563368101566477082555,
17655395829948427701890903161477029506869705574715696751076885458799079627781497961298746847887002061463293777757445700257352736997601894670495175082523032929052725981599555370783800997291780479950772095418365603659797825171960821421506556544973067793604235760599655849115315429929341606989839314901371199418,
15073490416221674334230001506180882602246162983953232757225861752333961843864677694886885826201024226957844542417968016414468949095808855178460701832492991571082107731083521093143886584969440184391188471396832102824707679337789318833271228246322870989723713500024463981974758785755732553117270275872599902046,
11945129285452138259059501534658768414616263763388830881043541932282218895040842679874007910264951946690269404093842965772171661133193582915018168905756445405840130335502115402879044927324044791332297538415847429502163601913166325739894146886289257393267985166150332706834012594051289594913329593040949183555,
11543684839897876792469004609502602582450832913097670422846307702821889092791972148154992478439429634861922930603102404584101787297377759522381092911468312722616042837641066887038358149787529894057643185378984847755222909370829033672783596685515989190980714706404857470099021368003857768176961780464527354809,
12717521431606278863933483525680938937457660380315148478213774852353949848209489478626377082074468896392545137354621454689263420823190270158293234760075480602281958188361139928875142488823594893786227713195815166194450469050025844514957753392918002649604527011453818376848867676354388575889324987067518037251,
17500820738865714665256968918349528899861083711430978661861144783237776295042243138678251182268433689384203475006568958138482664360855706363638090761952064549121159387845442270744406200107463523015009786936458318824001353605048606177452023224545615141859450968855792912846482816240556505937818176805715969538,
11977946166299626915721944919794365998689581974177468473069556749635412930132534745456489478914698969833954766032040779605122515985818176273048817609966009751720991440961295303485995215921528189982196646214846778224983854696123018518807317791912067161152586202338430462648067608215590337614244385547442197807,
11937463092672596814229080573807873202702150661829456781209303621947965743264850523315317609250607316247206698834755037554138583464787373106476207131159519965740674709376027534064975483743638331356052046272176933263273265053989892585191747945571918119987338821421005526883057035403462191662377935622965593209]

set_option maxRecDepth 6000 in
def c_S0_1 : List Nat := [
11874384007073601501421702574327217959256806237072542735196997721577769141250105325285700962671484408119823361179264646343737500684890741647745508712701606868224680704073953400196881455753150212961176715760450983092026899024055559026725584465703820637462610448997495491461269848830706607690461509210486940120,
11636598835389722204511844709686971704562566934155981353161845120966578683270624484837929732111042932343106339049617387103798462655158216497188962690987801427851378386727540543987254839337284609797378872330845553777051492369301746353341124976683891931412827055838075610965015742740022502912699386488005412945,
11616330151453254571256317295541137391569825976202162497142770584734871016843220798752599327893714507058084207574122331635002626600874638808169369619222961631895007155613540398038821956978674024810672387708880102221232075467850055037458168169780742143672826529395280936586301569034357631218631898016587548820,
13834649468962608411896737934283791323614891624349652627816491044714712367030686399326335720120976747560232583932119205940368781795129692389598190139181231328021293884480967376785302518255883945855602689902645091771883183768527106114634986787793072295922257007651292277235714654324735155585435511092883273465,
17562817372142073647681775980696890105893040609007937254480984171289382084174345717543683535894617899298713227204967460820914794360274721313808135539601358290491655716343544903914680214401585155837230356526794761260515645292082173977967734150989456231620602828009408144139219820596193813724201897251084861876,
19383518712017278285757989560612748344284589692177590638390514231044157503139703549284175408638301312458657666755511243643639859621425442780842925627380263797935134122872779587042340900295511290724911701025767309470370993014026282704052055949775524715431364702355868506641800107273737048443060105454984266608,
12718551890126976539051464067739635624944480227001665382387400469316034177962476504603882695726883063072006217577372757646367428616483535627302739907155712698610528977650939987402352503215907336974364302074105174323722108455640648563015798432938719625956755157651834710912063418299412288726150188501795833094,
13458512525898917166231741696810065881318934468228210154159758158092666157179691724302637826871920842716022492929275373051121769575615140938685927185867625114003217404208913471240494699213304613210805416071366534375165116097734681462033890999643781773313215362150141810671467627409589229935273536592685596854,
11955070363501484772499335071377462269030417908300808107268530132488682271502406066636693177004634225236262020591835507322054405616956618682582565224790004134019183543217161123651107643921148387850985719639536434604281878449345639035905175377932682382991116724652313391894304127558485225322839487807694931753,
12724735359042315887310102597030105639918284190406394669284487120321291910090759940609722781042406780437197111036148029935732307160504656077037194034694905404226136256520888096424363539731594076417275437556448073350560465495274379429863461082036862830703519499492970902178762269013934854071491740157963928635,
13834649467554329085816787724477065854477316109792064148511998355095506854346840720514165426389659956097536816547921667574579310645251378429834156749632972790356007874738764401057148967384766702522452191941514122270654840543762785212488291197752467269605509935704686318636727778882995812188082132288593167621,
13459868454128249552519814607277859545566581573949815973890616162531679080895845700554363456280891417140913303904270972275785130486599808826624367472323967468778850338608033186665128695723420686606274422506493111641211017104515557276433660227622145325852294065675881842941721553837699621344352610835229934017,
13829912205520725298698200748100639274254710309872784913463266076101857413071566880543275194542909988754707432172487780604056229147096537967495231078807168494462851088204120190662637520121665591120121772404033059549808484350622354419992527652598883441158061208081710812788447883153222267765603562804898791509,
11429721611651732902859338861166659935899983357237776375940162559249193072061441374061472316990674370582534044715032076804527843778081452995794565736965063090917411942875308454022390146612776362862189439137240714056238100717940977084537471204291793553003810767823689433615058019859694279409582420740203496772,
14970608994421580945764971818960144257620661561752722455709970475327558247359141210417624247487617311807584873178707912994389630936541598137441510546911885811145486667610291279144783269785585094825546324192643042390688082684621412353607847011211550945446241591571535131473665731092419854740933817458208446817,
16472108962133419062035174320852145285740266890121564206641435757173822753079460008818439794085950681805835473061205749719086115408247061673706978052405830864293618791664233063223745356064181587606812876737132243118469651488373905114893566543159969964840828348832992639058441812842903200279560120892984558684,
17480175186330699485195483028452562667754130776510389511404078890904297297579062463817062315324731076572278846147891369377236307556814928919020962417338765300974408154718960659787544102941422291963860656013473739498560015126459132460292679432775392082517964786102608423965902995145531882158796072096880953159,
14723385501721687396911215869742348574684085235108908359709034498436557822870895630870746528440005590294772788979620039666984255416441367424401152287452300625089031386618297215336267868968586183547417707613478473159178278714692678590544053137411242866352937086706753371288365971863975803656551287654069731671,
13834472584653990602916689049648163946772628280742552459847491823784755557443863563938386740539196742549045183067787920293099783740029421395098497148652479828067680276400770846956450183070498545386448936882833676856079198271629391258260253172476820010603598190988744677569793577301876931372637245855745025861,
11642360663754416096206332051905760515582915490421902181800434953771531488965580512873582206334440214596929864420903176531339294655167353595186634682103420611131544251267756534091998869099895656819094233298545051628527342238937230889064959561358788157754945301384482330146193256122963662546534376288599590003,
11618730016821553023973036306853690942542528530125294255963745661795416827515716459330074458313998016404700519856730682493171144232198881435473545110797037890765655821372172823802361151229789527448985310409978267027591330005995182731592411115521573381225810824726797453746985221907930399121881574072827620790,
11239776013860924628089444442786836882927972416806743031567036708455316190501829678814538565029231075113136887341056012165059172704749805196574575921922308459140602762033430318679251695750236860171513754549743727223085139195217695955362142747005202178742789856420215577912032832041528391248018155189063435229,
11244907932882858483473901424939750872920767405292433785893834855961149156231064814764540289059153449500636336296225314283104589875221277504450284781590181572190077157173880575032852725989788593491814361673971887991505139240907052068461195513724250097739913089497755692838744728048356230924981503534449499546,
14703165812475001323190424883784382517904721967504914126123691168865125109838716894729163920694541949043185524211584931749860382553580435398774728783982243363185502043362396107243444358898406846081351404699078439647213754148572862255101483263360272655712093350514427854250229772152913990829872448512922006509,
17387939484676905623600768525501278957668340620087209187260480486254778844756072567503446069884497879275029542565786619195872644016180465481675476929506657030762855082267292292536179730838062179650106830214448411094749955063549701351367471811544156736402894142964649234000890575480202649294015031579014595220,
11237398551425920658969607361572868062190328387998883647328947013213084177740840521233896550513716090374062161420752499258724016120128712427844772893601875124533960385658084101992275006795211358852973091824640013136319895683322820322155760710611122613458076215958520330385853591750505675358033089436259353715,
11386952879223892135732012890867965684961972313450032336573234010116094576566032931481749872281188466648820857103638054066671055225779746957054415303052439379850677167638635767841470356343378739846943555385340576324620968999178471217742492234798479028149822254636474233615818272049294532437130841789483355310,
11959475571675833230162589689074355617812279113486595457801220131197932613225970978433154170953476399159159509095000355718029107605943774999642286568274105529039155077803718885057768195068485480184619072056332874292880095485404650206296967850224995600018723826528147312064600371816875348398535764929327086534,
11925273152903943112844464682384208330190790979434133495036912127333865883920713024365220804023505918959659643134156605165604344391094229910146685308998498668570686742869895541152713619346044478509014179592931073526206183271345386066246011083706104474864311847689633884944845640110610238783263692237906611379,
11512716231729861903140789209895964489725345387879090430024907023803736244702888943398696011998794877464617381898930653063428373805769400088834235519269467158500507818719068886755859551285438694187656452327217795443607540588793897438236515650860292238379839770487572555204109709127580734045749500187900481777,
11506544258434440919937206096572418629519005048351697729625428626189024418481355708088209122239101221660409492805549862043573575490933698063070841669480953711012548002358184681788522167605353851411272548486517171678280982317673590902618671572756792607071497882835420076316712844985761690811539015469342138289,
11682479515516560208693964760468591925181357261680680583286631675045905289455768414778379768026784254741792151194196008938675271460086609473204944459583275846918840209887190368469306502913239229825180399198306374437640887000255883644190286387824879398937085302902040001322800394396408719968679118345836666801,
11608309100578848999339800433441294069424904196560710956702068515588752134781977100636777354596885181705687181296019617275500705172508671702026898343399152150288010650598838432829671149455347866164906675983901142458312512941016302891826102767772332996282663172558401072655013553082980686128453047506775726235,
12717866721064237365938856198594683155351675447794056725420974648345537046040339543611138358651774538591090040871735826197063878498357324503196950053049378382539097602293782393574774604083702395480692264291896247211874398954151489834744861582871091939615079653525832923027788130257257142712400449786022299817,
16184411705078462575879945246395375517856248442643698402327457373232558265346107859649619625815665652661173004556830430844324071768826949588070608099505618200963126721460312659143817778817044934888039490613793167367102143815899576597166176450289890698118008539492694373496129531998441162235876394392320902567,
11607660936306354298269124503479378963946866869866468678966097624252925014764003224744504279539499660954706073648310960578626016113007603234363397602232865963439849537817573739812368394189503589713810378234894210250679735025555116433769289005258561832530179806612446321244490414389123683151470696284159476813,
14671953088911152464743177481885248508334315299388517555119555339147787449463605268295409092560770149751059805932815374821321233798499342160444926577120541871208374438773131600298430499775785001247383434309516895394267834639677756459314838798355125275942230899083729209594966505949868915607992045122061642681,
12903729718203322397983086356784558896569303651417546044641775263036571559519301606305958546248279026724516894912171651030773161064626815311735807115198775701506352534632237469759304449803115365430917096950608353399930973348318707939203808738858530018963883442043807057406174994430942705756105593382194980677,
13461925489056542984008266028588137538893802042713358911594903430573594347592172562967396260287667158203084651930000556133663764425614157398632004581297123179065054625390345101660177855108005573541717858359134774672693454897909828911780538149758641515507684643161612109422837356086992481346517574182995069097,
16544455696502177737589451290919193682889783225381986094706717528493750137838334721228446194414246775618880575589302932066289263506846089779345705003887499822292968609792536040305535063548247319350007995947799782181385511708569023056450192809239565660365920494285439012543931454399727834800198099532244289718,
14017398335984907357383441682000906842159510603794775647706417305451379102151478994538128758314482537552841249323758328667987422612677368626834937736435094942065689228686667785895847582715587415619673398127075599673567873392490080084629467473760837318066557248862409514079871141196440649619495778215018596214,
14888331164264559204990442776817768225653343475272715284314409629215187599596713518382566975519404992591174538033546582723886744941969438564834686063074160458752879572052502824920324889712744478250787016808220963587612853379044273508536228343689296710777244473964467573556569255170275307251038836748617941312,
11819276560354318019694673490348014857360809873800028770642416906816092030694787599053258913858181695802637200237982671417269491646840294390094637772848863503228426463478792334968093833218544960198074110253878073115155411366150425859168692876433948709720625060642568946085151018302764225530756541278092820975,
13832240982023400615511711432744284585401400911279952760035389310281744058430767712895301819502677858535320407834473483582181816366946668790110182558435737240754944814277005052692207852064373602629488778014522955669499148700510947560364974000377093466306723830213474815610394355428771982588317754892066036597,
17367366877310461837082519641844522699637957967328742936536210513295965626382303404993916403408967787502823996977830507638878487889339399911311691363798286146837318077405161622817367807243793683561438965255879895937854930640789827839723843268925840724409642502210978110225710974805036370244949333618033394405,
11792845720370325210346029903941078487300699153573251238329136031226281461308850990246500478204020269070776393055382443674097958717501490172301066695464888108977093612210876490007125551127066028419066118159383370100327124518074430528943191770758003858294031144839290719492267846174487456356556415834072187650,
14857212429861298125639898574962670755444477670411102416931628321505789993769811455054147036667102607373726431415914158055676020044847832654219436890899537975774564602292104332692564588374535652579996987465982717471180397218020504551987852673485249314146158348465379711031359298977780997184632813640610193338,
15021698378364485525787431339453580305957694684935377053281819596895202692899854275490151571720422118060281644128609675457861022627396286009850817842671465904117724226041573576402437340367403974857198333723822170161281394857096610274396947983594254480266094350411731905142507171746421212408472339363853674968,
16523525030614926283002239427267244115848192314052990049315040770889324085333552176997116759719429973109044644841859275914445008154254727943689829377573106253067054053552946485847569895762428788338406870293131460103164569990934562940219598345655849545319536339990043352318640534085420983418517545805683099482,
14970608994421580945764971818960144257620661570942168854703198976599845631407128699399044067444947935451072576943970339471063838880830688229883813321258172354970506807212619840387194964579317872834175546965258977187662502413956829546269932778323990033931703233337549407741714139980843862425522658081645593074,
11422110321865819797626079322692102275085332316014902510364390555971525836502960003176041122622454704846083993648543331568749839107291866581769594451420537391524221412394455251756608371222413692396111825270911095810490287307642851232739150339319577540693512272786156233170461075508295696297626257501937632349,
15176002639944043492011748081604034490161647558193315145974255860538878190801323891137213643499263390177977413051475146304976219051189370901211920965674318214680491345224183233358129035398280659656635205009639661433314502649022046023823984003333235689493939013276901328030074743035746941389275966373193876477,
12351493693091333109829723116019176039344707887069438120411755619842297783799913788684846246510031731633418898363286285444480852585085044448832053165246513478398594271983411019277882221462742413935223395741431202985714257221892859972530774545412921438910613789646025099936095208013293298179636671948855444336,
12721993640652961858704578438971657776294589695892667452056090241252441951239418799555570210338518723669520857527010512694757584472870833059681207927458406383228443821735326917875094213518889344473396897192046044526744261456442879521655505189498761397877221009405970236418184125344682810574631418376185085955,
13828827856613542712079809447207643642802611486950710768990521144418613175730750945873187481756123920053917897288418431328862928600983992594736661369324815105086976357401726460033293167100195671209925501348464273789561848905540164081385822955200914264954998308208961636736706569182699196069989129904877405943,
17110199083230283702069762864454234343284609541673240338348283261926738760582275502294687101875009934671236704232930442899018098981517406729789048863220493129890007360493122786646486639134466609002068294832358533366062310259809564859559811669728700658937233888675432846265685637420639743718457597234741116940,
11881618647340913504831144209808816922371685449677629201977493696119140975090390053244988953661362530906935982715097540805140972828826484120821134028311446223777197719408903326355430960766170738324405506258076323207787330086059157473523095228632818584835069648238397643327287688837493494017265399926486990849,
11317233434540325705388413783589777069648167979572104103062699076188393025764045351443618152360835549454682029027923722039334914936671605317716140529489518317976147438839055523914929501872936998024589822741629576420200534629488923704790406913630784682296282945719501665787965674780695222911941200032253787138,
11379021695976697426993161295720794588717786517140716453666740853841396010204305669182581730283925626062501174946390222115702590517365613494905910191237495947316868326986764822372595022767029383110277717855147638675197541748620680284206995744937562748977526867678533344187266186315584817743079678977805224137,
13095052274935078692050472445663058699332828516990709210372765817203012320544666635692779172366774589464600980310310173377096578709064155850973853972018209467627182634370227666777705194778531143006654870942664843893064229724457619843446531689496290407099260127489599648460104248768339519605152747600433785605,
11336200905656741961107184950547223753093718036933402710644600427037535661228313558745197423444298122804187144587560981252733743369552852150487713309579482332622206953414801108249528478160028560726928398989564343413808232955735398065590946097130269722144264420921836862562604668660518314932693370606693875712,
14206339695849502179837682926568376119912713236057928203773507207236964232493095174824266288381333756708313026911026418498624948630759482424340463801213886349365517356724841986390487985115217187673660272798885455575324799583768302754666490239939033603142612401360272070457962194438077869302848637001199396497,
16554399253610638765825748651395833225116633773084611737046878941172140785355492767072909199018327327211389736396162124638801639942657340766402157849809500262476772079271858876855274364408117251255620051606028747903091658781462053197126445268986524648149751613369205159565784806827886541860950758597417862425,
15844955683023235332497681493871727425008011847698104753868627587215304200979053359578822753024891781776312694725402488087396528673270179283830460904308979383466060370431014440282089214105658887085736547861866824000748576179490898067582297964265240235594654908876679171838180559606228967664676081773287278452,
11977945372159883235778868855462521303433727417774345887990184096556443136154609896321195701832729593502252231334327688429784891774198112866589330386587804020412124908028284018286357366527295828474539394100928931893380956042491717326369578261740501695578991225727412938924118588485396319044550162791424884815,
13461644908667716614831743499018305045465943398883930024639764814022758044428301316997811304365735627644354062018863784419758085654244268851310327631650054111489256434962231780873742404373685945105889450219006720890890225830649725390354593242567049168101192182774063684121429033533818414986477551172187653955,
17480175188361668863457591464898320684237581520366103334375599674065255166369848988312459809685576967172903672431664815440973681333764181900955837418431179861030091457605072808204484292745954984253706883244429341135939564764413563767598519758304993994717052784139957024203003696557869227746105189058038475134,
16832467391107058416331448145680192294910400567777558804833504595224173818604071148325881124869233349823371880640843570305842824828890364295276887267917236342944748413267249281746505830450440480559394847595984069389263146087881555209995133848052947944443109751663365381068945442501703427263856309228402083865,
17439029046564461970138604066983902369745884247429034993840150919196231086050881709086529475112121567253471138485010511471437338057906637038961391618668498709594621623076164885212075857049116182121723176898838114575605656015641754891096191097386119566700679303854854160969081645496270365463219160076130254858,
11261092316596562183233496748839567660445257900688632633459716026028266114732431410969022166900009129372316499253649986612335915720659327827462660551935385011585410629856459747218579368143325564278706906185491851876211487935195602576296863958029933723429839407651988177403635480364176776893103099711072437396,
15258637821146916969139765534254364689997995114873112391415755433427717785661033396075086330894054005598670774901915908294721223177028260440310571516727212922545472711381102253585831865370721110491882060591984471137469133238846414891561186362680442695897947635779215227129681518525793047623534603057696486350,
11591329218581730217660474512955883772346331654032355377882221258521752460128253848149245331688574936102355618901323136967500433763592897172370349050651404816482629439053859190415882210623176183947912639224248793590315065416258266392436790641255084324174087556140756759967612566405890913585489991246355793638,
11368416805946158755072639166140315606505699616168881871969983347613045378852175136600582702195169926768608178072406650487783100889443761589455403563771706785604398418824648832457371581048592824098855126556211848203736900784307369787209779327842734808625690052009694445770898056589728432644573100479856280095,
19198090391157004163334194510283006780381535912240013250373977044463325444964052841398712839087829407161079244386510620337853426808536192688688997770764324685212291451198329214125258746164725387319622293982868042411155878666867439984428949256338032681647410506629216268331024275897390620347076162419964459645,
11505277890125942573354352769100395871810461249436990253215094540330736865233031822399264330579475284395495779411232113466403854658633691498120588158889310333139657118111440021337046254731203503912483373094128349098943871911291875955510697456208334205664116087588738687424477155646796709039851276043567464448,
12723374055567325551752625127163205875348309107784861635000771794248685290424507503285350896951847157242222842319710992798085090867798723029779698958753999403862492161662900281432411162294845887381199185252138594020317202501644313765616280415753955372521906378885122125064652000639431345879105482366729658299,
12724057414367770467869561237472398791563271474434806095720573880515994683351095380739227816929750388964773717621149453376775084915859550357332456497578804361619854570319025823600619513189826368819201296951820290674723879959471564717675710803076186207776562641342023683163772527664847400035104570159690319980,
17285074323406465862878310092910892456619455269592892964578403358456191353659188958880446509877184577960082123672537370724096902600403271794105013445812330457797821877562928301305294835217934547608977678531159384591635830060857933080856969101143494373672835382183352998633232237793849205224945360348579989720,
13088181864464924950069473138024693795423881582321099622033566558945890923325316278723924932214393213426508432301646020559309533702077804950765290214462926700253267790578628993873806495386683798644644932836327471515828088104048332378710793500200999128709319020260104719476278755239563493178956364067046720176,
16544455691995731338365954242506498822266040982319435873708608156966156596178354574986222398709348529428222768393330040823231745899891171388106846800578487383249093870276886258892724466380512192272051564454057848215109419969783740448848730481637220388206132966523467162160281808131629992476662904658530042271,
17130775985016948880904291070347964767086104273820042280140155625953931931095747096086276670744654974346996831292768188877914492259007456514025333169780653924101613731935880298983100285627972501121169324049603898528143277245499944682113361661655740512427622562984958385635001058083750366332605081827318530546,
15073131061915119667271042553839038423370953360209267878239675994590225880705359624394636158562257377566112790209686518648979707302191615067314480441267475228401872388792090272516814180989768156986735124415232773132935335024808743701183364229119355210555505561222973187731184365766963462214977235315494977652,
11639189154873250107010161809525124029051428243384065929584685560800698828923965052901798379388892506132390686544371375166300061908971871491744733679611253236228214708158615907805529332863306174491923444416951161065031194751388889645350721203570708522589956998795642995609095396719111341069993101311278483170,
14020252878883992577542117142214072950056915762382920289543180221611318604306085697114186037624724424996140692081083498520905906944172224169169279816700510231097286553995565500844235848172945898676065531333962839712861544289635402036839880660833298993341407940605744489699122473508061812150980592111797389003,
12533757769114934830716567883354802567753855803566400904702756503918195301075739705566808403138846221793271870317856852295230147414395731129856625543943395196915405997348222859511078185333944814954238285992756377265778215662764685400874948276134632675250674705753380483899362804885225762547820297498832933647,
11467899275144652140223132650120674942963641602891279822971535934875499950233870467374105908893663641937693671382443483579461364788696931792968608805769573599895902519556466230571182976925704883065150422187315886704636837113122927008079979873800211404605107307526075523718202611445210824564118594652644410698,
11904631283043017844881716500324784805806818218659900567664051447990499902321873566201623554245701249165184624369801589877699864355332497052136460520204237493124025218706990837803902815531670411588534699391664601489659441605862267174775596476016422418050231210863943260569637405693625831150439319388163254624,
15238064481141337578943035888131583460297477493898613315300632169201830752088888475039681332061362163909480818249671561341060949711792337239679861956565857666499080694428827837441607706732538871102066109622308036622979911585851133850296756935604791276694257171053932512823980140122456450363206024557082484663,
12018403317880625165795649348349350695593997892745399011007733046819699427737657608162606582306044727200305640889648161258740639057759030404337141795163459288654106472818409832370710524922688415756943847079597082774964908835901700960376143858220215200967114306471189278793528932473806988364202314615203202103,
11235661423352440340882586617795539443715634112529378108445719516343849086085025607783414439592500429562194017780804339425904096374946960835504826403281553414189301883980995062098690099795252933312577528134510049172707733000888949934745624266638170198537997571334158251628049331006490340062383397310989969820,
11937463093361740570477022583796201443251413543223450794060075972755316564713489688781947191973607250544756564931482383029335381127651567252605257935221515307698740688122551556176311395275380048111052924827154627156010362980541566498938437882991183714589686587408703859981717562853740143737488711120988964864,
11319355691498932160432362305925464043643719132419729262718345908605991914670316938483856734659176010088392810893887994582532264173244701713126063406073036035079972269261960100940160692299992334565864014281080412789526356633672772540445726566202615040386506977806919258897363342123982818943733683958301073880,
14918852571282220910894472266710183328257864440371868813487157954094514389896534227445526763662599920621227252998075554952652319838694310388858570234547327461166854738953262098665086659090118328792379678984134467695173670913919577971842537024077958713301793440263184946442953804247666183655373724699712786673,
12020210239221758244428602916048507664309099165725253480699781091008172741726348143447289757854599085628435781019578815722919898806157761105442734192909416788088763478057783124157141980118668526112528393807442525899804257100223139133474296019683859332365671708411102818756635355537049996164049524257089884945,
11606980852030963049488418034368702008458427488508741680028080780021316403657344870175326974546910231795641746725124877084327728407341800448373349430510418263304846460029328141278459418918580072622278015880572714985323036547454857698044080730553492683530393830096702289703552729710295453528029467791520082332,
11873023788318528246169240645394382180993024402801810351572922862401297203818273150702939319856911324913557188984783567435082132311656224576691463184510452567542120837135005680511232039388763986138458067067508130694624641564484202029936945427658624017782482960613328426163285570137502915092897866338879645629,
12906899087468267965070942350543499508719372042792215716033126718753623055785210959841961810064057962468348659651838041581870592529327585466196666710748343571340149523522946672911674668657872053168926948138863369687536147055903894823759251210870022666611234638460190206279009940254533029230065088081932650610,
16369235042535461116846659819426823005127284358531037409540035307478787237837771854956871382057127951114129823036012245075636004683779154951715627528481453573978117409060143140503245008211269843430376066532024409903143114842270359803274586345575900067955001431423507522945899150192896560376205067964597277438,
11385924869717781985709195217072199854952545819362605909301329715868456620755970811380448322767107051778781050528366637853740462485727273288737856226784552037264216254317336754605085965140956856335902158037603782033205504204289239623182447345775695133538913480236202411744723252017324730571663500556680724831,
11979135253794613896617496813478624562382258428368806367225047288202239821339389476606311159943957899847253635459786808015437284338603780273462765008189706713702846664582883908899897510242734772686817593090815557454177049558425166703060140045088109611951723634396774678384634109912833563282410968992919033123,
13094716401472313717060481650203014924675377507592107584546956852857052011896396764072178538902259689612824424909150831805939416423798134515645534766614854842696888976977263037325001248072243866728203902163278792455014957386633856892218615560193774384341698445984811969227978352082805163127576522265406810405,
11548485815834133844651460462533152965532083496798170093325298138889163047843742901574268439581578362146063418310746882323116133023123868993013720109636433170177189578574958256265762059092618960396292692465006726324782421990744948278420788880433278517799683797548560530289730431137091336735012703101856416829,
11235661420622167780741562050810524605761793934985501346016401168120503360714880186084708144725000930359856129068097106109326835791231552328427873609172779029156935858115919280860359780767972896166061193980833013101844186768919044573624392846297981602649604324602574505853689217361708547974417178665817582910,
17686254943879565455515869643778065564839951332536810318058699803602156029778351558544289709030044625228119449022861373824401978265597236783991642575233583010250874169928891134413303396536292308874446239031180856291162026568426528892627415867760232037768890689000123133451671950675681837060692545340768520191,
11732121703933610678268412701291774161581423140031232956409454740943813652424548975916904086806344696268110498415858559589392063110752114872613492767940676953042827897443508293078097566360394117639031950921511264200696398812119721705830034008169424917837147234943262837116517923819981253562496695522369733757,
12903042023931573983671163430689704263148913805409798551567911237789644139671121681855426132069534318928961010483805967979484594044640856429683213331082020322995254084060248420493676047947798214884487507239324675564380247982634412293959130927692581111961386379003214290788692955727909112396396133033487569141,
11936554705433485238529645287564578638416558899725721697086570632139577794144676846478065981431984931329793859375523315114447617694264131183509902242933299510249659345509503673863849361335556268331845996728641580115452147840499434293637667723343484883364855527505457431000888292183579582634484313630756079585,
11542316134146513572958184327731523326427353764917580768976235045006025278268598487182511645954583266893687754530005794571708857549172871869921208811250164052523499495634806269141865793265652471277859835500790561255733061763622734361167869339942612849797934042018963295811834205187980589245694456012205268905,
11936862157341517816533284184147530532394095632245667718684039051958421654001313629406719463054691828600863181345281471225371133245110505121498592575083645008878647324350622096341194329951560455868187413554002170312902134218685525304122628017367993285876615634280520268964585137528821421250618326584256638481,
11640373381527400789640779981068525017423451056581425548122595701970987096179180252644865498202235611201908028655092513011881521008929227000456175569001248143518082365594276086026990363118640062023578415616976820593464925407914930676394994872111325631515379215191956581806124607866162626834157908067957874599,
11839123746084043470311465356182386515493395850566931145003959912972581597206130807736740917169354279692150943284716644176153532596013683502550919141839583273315039207240989485947846271202581997916681832754054987698237336229785177852791539503517828543781467394228028073307252442517480045441722919501571010005,
12904415386141519033514052064149030882549815900355247426323805831206195194132282440104882394687603602183395311219504926585347029928392791959364683557251524446268141269011047794544516836991645116328826912231657829396991711098524492918481488102003194540072756736196171817678981192608574501755383261810024844473,
17243585258991478294232156202986632962476820713587488908698814980668391088084989577809732354249846263386558272502381121017181249268609792818041819866640449255545835337830824887408639490886432988748080351016078415553763125778971662265859695634031696274386668050553508533340687888585229886630119272882653529938,
16502966705392644938711335133620289188854319944182514955751276320011688253108410409466577623608828839470909094181430566546616578376073914269762262776787728236327697257868170967396499807040496023326943959688067360013163484228419713106344733749648523118909192318317648013666767778402704645810949358082783904463,
11548412369494421057306346007276904134124303363352974307732902820865405726950137880386854193978909562937757801380350241585649368163223510224907649632425896660164622717015828620914980015492558430148407908303381811362872747010399976067224369546624684488218816467603226515484101664040198262852452023600585703893,
14020555153773848525015154265177852826133153341502991059416553296117860130329854160804083024396192689436166594341159179674028130134678585996825161196488869872042288936633165819300688426526389636092986900870409123203985939875904761564427073834381482019529622384703067608274603827831034822042299911033592957099,
11338258201911003902649401165934157049798547506559591954520080911449865452894966933258798732900895206949357158055361313593990382368727740643120532129306324587179070434399501568703773709864383799429242642956207526808736208218766843600526705771428840308439636761901563513768426980361799741597274733795259943029,
11874738191488090779789439854759484942372598273223937887979974418861165609655757018008055031157283545035920602522432443367797914178837863856172151843594545418534654742748084785053420796440328098432468405778872327713827242748138784735507044115140506418732298963190656621021591960594587983410458947842574596552,
11620103420879917535718682235723926584363263982905008533423752301371326287766492033633881133161537216061770626413769875537988270508186571884739489973917919597905998628008980744126419054894025153166225868002596010490403436512241017671595234516861423701648872871362571511656588714384881598156127999103504628649,
12908215149251691911139711540109015687030219065101139749323081316515892599262128327423010300130233037580227266457349262154212479657581443588774921369440653642453514916278657280749921177498977680515936035013960228297378960682545051139593533104074184264186920826266659428992655305925598733226716382551975737440,
17398225745277771438122990158494756580193051685047343994657395035863406611233486215712655914033345551756775923822254314689709339738508247383151275729881385661373204116012872290953611727103886694043006648872270581035935697764086595607594818484440449146848612502422568694775292627562070373514540497952892063988,
13461247938783686376691031062534118291232483849352875712037347195419642188407313595831672683432346053056018116409414526695627856670860204079206685141278411118654349390142993376900200750091736593716193280067510383935474961680783173237836374793625202828788962545420932694098710956742564515995562206794318644342,
12723371537121164502351017902630692010713987689334162940012444884543162983983788850299044108446706992885564665680619831552560992492008638893277169115983368143780121971235442754945589790287297486729937376994112093323053270484892123437278955158320993464178376769013588175663328863223644790276322915944548401162,
13835027297944148970322638400772162523560156815614858823723687445136704336931777229647123760991795686388173925562947655049178005651462007797702545038416481573139064544982328101911797740662191858888891914518329105381122067634251948848533719113534423996412033137662268225385727186078260276680635556464836314265,
11552943929944881807835006949866060864939473455755815305914668931659582667495262976648748597264077779001111011252159935728667694297046383749959292525088695512457107613142956128417225996313593006016334303390098766390613351561365321520399302986704855346864296545174495950392344884393612785054560881707740274618,
11303926595382950550433490758531429637225091892757595569321731080022815993920957985717271850157909516221176088600149879942608561897476401684940606384237316380280326059781698833865886372589071539897444479069224237576548390968237160596781219241688772986571287506051776366882712897577391567892870892946851671419,
16358940322555243152110392240913502132503289507983806081023087354218019686458088334916827075388055669127623911661273359983130768746787238681449073769620712851908630827022067877650546429399259801397725107418423919027973187906660116591426523131039401165196898093373092786744145284429960255781888238036666978537,
15258292282867377402321651854953282409959015617908962865354042521472135185604736496998539121430521449182857381427916768762745521564521951115236197841834827772205803648461829389305561706619335576322956159978726953061364598256261760184770164263122715333692679504286551076540168204133966778455188903131635319161,
15093723121180621497998293039281951964612835562828440987497437229745956550499634748091606747098916101757727557450424967615129664246749486797712319513970625563649697295696231887849129305258461774570673768370321086273466294048725573412451259846297012724476126528821912112341728214637615405182528556698745046173,
11356044470602084623613098599375362313834421179912896038328708607640923202819028205597338376724109141551592060446208327364074629031363639173297785452044334851927316058616774741639341943683824922018805286462412132984760031769890309053199013325373874333979139090628623096839618813105714342583786426241387923033,
11607039345170735316693813039463742075296541231847505716608674959504304330900862716776791036357302455510053821388591493841973874457005174822369857758861592477350971920120351679126843437697229545646624799588330166778216426074423129347795877287541679407398588946703887929655484363977468210904828550277069978087,
11386913953550749719386206791173402398673796846481134063756934159160573365612951737451090025920286240470434695194101184243924768897059213939216541026040228624243856163482887765131601522335653963119133159159958192469468223374234231047885123464247272319013583769167358781332382875217686897641991366174411310284,
11608309094377373740665841730000821403467580365000001860382142077094612137468236252266323399331056375526248190549960134069904233911440034879537602144729364636151557922065962057720769468632890315759807733302532516442185708622098033332523391554515416201743979800722354521217791127959103354883276803025833900998,
11900516648132424265658072581138756258329325891549259815780627035066638693959236560124946345395887973931060526596238775513581328771139556079696138891530624322014554137480176768075835693737658970227496540473611040123128877069451863255390188925584646401912624146030668772438848468263014257918971230479570175102,
11389659851232586586054777135888655718329444181886481920203358158302182589727157660073833366577364321998167094337009012294512669065612190843440634278466916834227916343005172214617527425841230713321416384884395982492641363030838491034634888480214843130823076287786665052568443443273604717115486916802492571567,
11526452480662020957463781616243023535878759373590992008019178324872976520345917437101525335693734071291135216703670173450988454049205406344426823407502824599578823165382095787178299790807945133795737950108770898166257815108512780734750171199951934260951065024499635266792524772625140557348049769715453700779,
11791757362731000912034835179406217140571344209293889381054868349606958369027937980234078377212105134842658401361712756578357085866680025044997687606330879443485135679580294775344804881675645208573043972517882283269829780505586614181620715760440859453465258883922290207353768376264980883877969305004530935591,
11235638841490768357767329425055795069057952102099152433495086924775673432254328816278787943738658675541454084219749881755756376415195064326048397934922773395307910028475290566170210419401024554645850560867243447985466493593059525103124124998037701478258904337449237511638179575946251194031434723657291596895,
12717866389464798576778948878449105815247293678272330904849394828909462765947700934417669519961723832620105370012527058247507703701065134614139381066620028876742222142544122792552370119030285153582833249633577579658532472868639466792089374806303629416144103055930302202583138754480445305111958897928480491519,
12034863490748507089174691291508643086439162395773187489443251889765789757483813800602402286245562214460064519505602370973132295540027620656054831654151891172893875598613632565115157888048527184517060807362188096501519959745777892642177758072063550192848741774150372162584432933410287348932076915433707897043,
15103990353120315904252626581072951696172287694696006395875069587550637088915528673678182287944246410661888399855081254530083721687700164723545590813640675066622441090194524025883756454613940339847906554564322358956421410559518264691688518159019212747354600793326118423580955786450672157034729754687630644527,
14816313961366813274171818093877793756101115818669106437870462019744568738172868489996971981517152148370889982273322951341533531814434845946649317140076627991999750700738058856857893309884978147498519178936818274837000520544925648433614037050170753889962652211623178369833131643450520683386895415534098743732,
14019602902924423174410104220831595520215433041602589888441603102034027536966516755688051737992941327693443353098202246079994073861297454731608671763722141455470827600325303553821510097572129980066367815430120175665743192368846629837760407795633188319021521495985929633553176908376210290079779155983369339099,
16894186556871766615648304666375664463334775415468439990149724245929986910585803149270771032836984047420033566372587312640587105599630784906622021973869841335845049305363146116182593927414562909660570144789427074090799987201352800564243918017879834314297725305874056151399849393553716623211065523115104451136,
12908527467844813661277718815322753485464414958335599074520514835728594090907553628805623386567764033378838281673674907935316132411384561963864463850827250479914593180612246352393851551510979509132675048583754963009991799911300064187115094095645722588490501795395952416471331886314432380068690518317975700446,
14723408473117181073459319746505254092296198017385456487681548141107906122853184373541394751847445845698065612741539686270929774936876842563249402843931181489771347633435682924241783457475922998852053187222164226410181002575601397049002706007168105840324073586660502001252580828879809831453076434161605443895,
17387939485510043375625211606673023265662786683641882385351595313412472857074730321422147060161615726232730730956203238807776331978699248513072561958122811405526708808715499132809731169258470092274852755498845744550907911469788160422223560290527576520314268497771651728384579086765256179802673015776406767854,
11505515756686051017057406573351549327989940369096209590153445051500627906311377921688761061807912790979682368866466370912261917709185592058279632187139470199556272853738833847974812072028412082987660636580910369875862267703585145336761276507936133962871034124062811207520550155985138369576445880440118051926,
11983443482442023109329124963214162412316135810026789708614458556523075350377861798560566091588830818519873315482033859353585918606672976760228000125615867608878080657784014646953210250363502894630023606430878235959142054832544549963973215296520077943476234309524470087445476078080913951460882393550279090087,
11602924134534340138733235206572583133437210641343495647820345783568275162298369290275131748853636284670463580810924241666541741380917714603528938331273789921264402485319598878311147241490109751014397862421430674869318518040865369196248206734872552952481203430136389916713824439943902600291808288331979784195,
12030964554332153710720073006208632095131786103296136132539746282880473047527670878577381027795475063135109500755867573570912988488522879082888897118468356592458243264307738283422103826258522415034983362910450865800190890936633995513145506081623080254277649838623766064882594201472464227319810821279733987185,
16338710064319248663020970321953181855753803730327969992033723329933388281855000945227424798686161708167821709919644844114902666322437300569788311663193599575316736847090450114009019249435050514938879211291571686186912907046961016054480772210706658406879928845679954859966331464949955334042483560338878015090,
12721295088194655563076573928751703917708926172121954570398293786502314698977195651498296370491938666479102995663460342332906393970295382567907544222096882616232157002303862192841630828135847989996971798856929875997283277077626133366726029272459719821612338768768149700726733655603561663296731337021386426249,
11235638842145670516238243512254690323905338183626297543627086486830345659070378729279608358542849196113567896872490668301661849379507197323237056827876772986563712699297558306301905996335054525114150771752805467592735658979722503044923488219649737893901981754337149812375751354598751558383242286253713687216,
17613906816665268810384286185312140919141875805202068961699637964264594020048737829600419148533381728903393094340315944676724325891479930849819497182262756578259737111551203183816024855455294198230039689649896375771958134692786316906267464026801975653789485984860303935397430107715752149526165018420886374399,
12903024563807367345295347602169835604983177809097717670480658691116380608055469004661843851046217999421845856738621966170042045493179864914047640571939344796111105984370032517246937311153781845381415433551388545519528557063530689526162075990419362384437379616173532234393962755622362449937242965936355345296,
11880938469283770386241707561111634423497989157485796429266963537109960078827435540952648838729549480254770232443741616428357942190581060905325312163438759638934677257721676020178275485254252368187607577346101225147543580372026818941934499281659583823196241630837093482938343404341622650458639650052106125660,
11889961251961609735430358114104694836516562245312597166619955086511147045119534476787776856560447283874280992266612035625207729889989465909345420034739882635642589477827499495794969848496342396910639728055857764738255275803680457457524518915193167511773797678205335348511455850738712285959173759202710898888,
11356434116621052867018522928294438573926654016896984906718778532874661344702043828866153852221615218761413140393270662708992411741219346028455402649771019399730128931207024339494284478985482344015848289845902873368293720966157124188595040786134549396041796421458869726493298674150784447398849252573414967287,
11423152371228816358254620420468948578222985652233673488138586467978264753767882731619768267658226528408430906158857949055222413248455519513037910546240361710851917910432547763949078541444483223543246733093531490917623756564032968794419202416062241442816596990924162313487756371388614864877472742010882107114,
15166056560256941496767870640956777025980746930731939799905752268911245413500918965025406808136536009147705316606500650805506299761994875414964577296485024040343394273056743024748722470734586214897057800933783125319872199695860764268093016150505915468777987517634952977069320224887486543438615793275800977633,
19013205265681529400647446632872600253829811185156864943597507061791384909975940721506610162147552415349579017511680495817846081203736754759902333486796925666305630852627705113169447966425577866742708323836664192563943328891093175256168671614722939654557065419849916432960280809210401984080618846709983118227,
15762330379013093718707059019742806986702474242869287560674373942099102297327002823753095212383920124309316722777556187429688046220806126935016284839511081673874557174155741698350456929598873826362154643763180628674011576004044548344345461380287609949419986634235325583549064331352693530198888066202822346653,
16101776049903437597036538653027067279816611407118292726544632313167328587318009123324480931522246340644563490998509148222297024742750135225992946860195639121639667781405457338325155948859425002728668680604990599609793574536464847884849383707770366903763276955444012243447974169641775303598369848425948021553,
16287285636194173797590651044623825753194149004132049275995399277744570591274061495071890674150619386255917816872426997359790457530393597014622842931111622214009996466912095296996264076450151298629793284474660109996896172810961223010732391918134160821864830579433257868744909721665625797140142952794906034367,
13829508798238684394711117169571573341919902857040888948260588171377298766621609545727744217663734354302103051871080057537644095215646947119724609468565687201471867023108545637216147024714764804461922313561369401884304869875258589911130078495225314008992515451024127029484750923755214846742399105808078242935,
14672299908502239262213852827809645599160828762530551804138020014552035833255718008123198914234556721732506619117552292082997435902742950748782782654490620624645723457956864062524525448084527600144795016235447787152352523159411187105418419490074812184002473878860056503721477544123850415915088411889255547563,
13645025687748912769482684759493889749350632824402443052105137049535408578636652955377440718336374048636047313507371211246864531910742781715687489678544796366712027969454030643146455731899236990372500985575130422111254501365396171249452297889872226219383724107452065801265928894264286865300366514572650545655,
13832926109250453130341930358680447402025889961710946288384166638634287309088800375600416775502728404714332538455913182389849667548849042810614108666125997169378105182722578218449104891579829678477822753453633600438479953605061350656050171406117799406111026535452456735346664913780033380843610678795421254256,
17295017914033879372211518957259639953300289419194386328881167838160815458643217041288030307770067465500120713390053667104679992879197899018378566159091947373555068193846799170689998102657258113583725539521932303839769213525608677589766583081526403777082167110399206325745176239054216919965714705379228484889,
11236267858572127705933038424607446241042026908205085409533115930427611954926959039411012104076833985656217573758817205143199614215144720750772314301132909495561170130341644495918286033613439490015602449092326099039713698975954771452378673076710737839967453749751591587934188844522182518258775798945795605608,
11239775908965619943682212860093687210778122253412847554531055351013282274900424218704370893303492345819894576571589266722905590142377419707552034157645279712262734828650893201932997151944762456518830985786191980815922438505127740129982129671311564555706242554274478651292016721119427037867250605284293543054,
11235638839243637096309885720085369026403949757305197539890638404288193620501079211883025841657007641352445900798355891104364460690838238497597212176681552940266034741878950776855073254378665883224449850907047849349147783016432336258966730535146230648927108616460388828832281564384882328838793698410060286255,
12721295266079910899416896349887861305738938983135159198145292419092403298526922526187551226268803749435990411196531413059892460238905238460288240406823191016720082114699988150415441197976145488546715777690059585721824040939542381362364097308240489802776748865608717366013086599280487097876669252353124993023,
15083767094549868017159752128585155420522565875656395613838923027563498387690509077194635269785012144956174611485399421724673048817616215220057815170509098684028173581747431570768461258720324623279607639758630301838586992280857654980118830905764127933062061508634577676857993091783011971086554606509703528659,
11389657957261637956937810759399470824754694863301607866968866236059454138215480558176297542324337249872484670541536233911050381340519491909584380162682868846075420621630462034211233176492725384878928640790211107916937968344313240209933625566386077375119116598503977923638817382427359970140925502128106602997,
11628681768123526265521909485851023824134075459589186314755945147631924939720749943047288607504924992534127173553616111534851772568711024350876671636591475608980919469476173610230272081971140174867229263667263563262630019342271124413230796284741600644001847691010680280153379662327493710488798180859823471498,
11349185873620861699363978046532195386331641634561678063882007886513839621872853630033010785357364287454517229016818232817303058202280712180790017360537980174773252902014153124951074833482730944318070028586150400845080794050792939040135674380609198064484564290132073357009051157124944752114111406680783996648,
11687984170976848327878201808240578852365438076069088279830287104262336973306608941862852531837766067632937936836160271926143363313358360184963981938761883344361915986251066486179475973665794181499560230246667839159743856786430957433086892035241986895080736560229548078865167105072022831920681161735010920651,
11608309094377373734889682548747490643866742674268135466042756288018875314762175099960452868387399418382205619685562386020158260467425104390877680075390362914865484482022814207264970196924531300531329728208710613707186651775286803123512030940052128154752781713727417583960154908519042042186851020361789938007,
12036804862220947340394551149373396947883643273397661093530332253624134227935598802610650283577607944319766273649908067709995190702539679557174169696739829346599637970326765029183636179298130079390655343806443813428972364661547162869104582630713362298189758048636939981171709984500780214431822126498362032564,
11980825181850683823090650546019070786688198186215638217252693475683970145036545847735117029572950919035643756672976285664252928900767942225211932952468319189915988994060284553681375952973776580349161521307803044037713514554160150119968569073543504381389263529651305100985830987718337139752959557380595683573,
11399932824764161348694302278803511763919958788981693715429152675515303547686995002163872649524948369298748217397508877810413373633146034512439806136921735099961200208783733093001344340700707298592011146640278160762596273562664425264146888191980150201971261761819703028641933246474980299293020774407935240125,
13088867766001696934116586401336263328619534182800948672950610740099284043495199561124642155605069202320999320461128813363070744540336170574398262195300151616163925665792723337881288841041246145597481692572200835579925825845522078665755893452622222993557384211775004179822255307179100176363708862249165040118,
17572750612685543991949511839186926395986229575986443115902785335476707001845915887431172772872877835403155275651095739138473002968400241147250172841341822129235294670362537796863752242644044801184636931099889125508014611114144807330678304840105110859429495414965453532366739170659020062313916482136628431161,
17397879036209223842539548914337004675957282664806470388146451622515860036389271576394172618832547328461482564660758644345068995202077587266696029712015394461005762216580138219942675351757607708674966489934260485300770423834466580861839178721341948762593639119311297523267350553680943275198442758314907895668,
13461644909703592752552937356074712131660435047658953134854572776927880722169301953754132539610365090874920100265108596312850695832518086137796418247460506468718424178814853524548867638772256538707263469152597644737362761580608961778885955644572391351407575513791365057191874333836829504961322703869912319815,
11276081989557840076032569744301410799460625462174065871138654571780145684927063430422605523396339054511550439490700692718890626328032921351467189872884381142675060537698348367214803560383707720300520566080293698676246355578455480377901947731899467503676021892063493376931018488605978751328882649823869996214,
11676231877515449784751573822015928730656855187745880748117966508738379633583771813197735619547969631607438093535119477424702343258105044153510462886534014624372861811866373309868594929830072580735743654234836044381900374776619102703138868776080272482983747633492949620197271463954410058849375698680123395795,
11683095130998757366379906107054940200827901043106569366390969389035039954293736178793619717247804247131664963600546984492959805840289998580472361882597785635243021303259645248947905680645071711160644450104255963517801800487616274062266096286688058348537101376570182395611805879162868449782242193398115435583,
12041778671573817473371496578861219563510120905049148999609179479096845898057622015694145254724084366798674892300954847883253642979981243077539633153624385258538163418823007342771382843020900980425591572084144816178797752113104038518787530015275975385454467036407225164087663896464720769640104088817899755675,
15053011350678338292461829178820523813455464115588445284383397449291117069610471699132699090298789108890001296163275388846733428748435943570936759374044135266666362380953966364663533355317450660917215406917009373119211148017401332798720520753103127721173359591801206640868854762290604065092308052362742078863,
11235638841317688900642935876194459063107305382139078140541118694217477230173218710260944558044338514835795095125801780700325296786143136861661943633570923017379185816851951374862406769214100509888866308366839022197151629382026378919339734620220851954237527725208946285421544952033672144592516766618736208884,
15052920629879707017002001008370513226797759054402407965852926840116455938164933206065459573395537357176381039018313629480818264438206812558221443990020762887195313437779224245297513014046506127806644737729073395457085091639018935572035246900266748775771960124258480848040534799113845527986860706778946569504,
11236079141792973801063496096003680087494387390151376713025301400213974759264475339581815383724156118695377632499866691528025970570552252528066732970476706504344354306522770898432581215153653123763935637216915703204602808881136501090875225094766093298832213142298347371621894189252267116883962902214041206796,
16369235042535461116846659820631674056234992400450036871988754667328164127838047041865229425738262978813450087878256781629878692739653348240344049382557165616122445696017524733839514632055401465800390761359884105241384391629246041627944819108265840024141959645994252167669199290873975757982501759648858833440,
16955562479979687461511170974807298375114576486554080000645894573827732079484922698567858548299880660977235015730485251014963922752992718867914990502567487101315295248315511989059337968056868147197369349950187609514460043132815031923080771486484320919119324988805328070872476250614459764094563966805488992561,
12907840459333245978047561477107043906444795342309748172568827688590180566878998424720887225954347305437561411757955810804030831325812755293102728321170777653675115963998964579479958490247908242306019029543874433085175120289156736849502315419906154621091267211571072197480533463362091381012829257232332358628,
17583390022427376299987710890788796958109039931683832841143019280291191107747164609804482077361599479214337694215921929033041347580551497731834085200196983495006356263416010841558610312457112589470755353880115212598290618367662444117754091580702977655844163749552792734723254711190073920038809257111341238123,
12903024217443491911077924425497491397287082069160914058248660947161196771691369578057147118453352578984316184107781064887574089107178515327905842874231178512817327384324816806155261081661314823014809457205953243987851153586112188315884306798009677184315498359157596819333839362763200140723125026308559963987,
11239775929895438453978532885786399182145713194703352843875605092371224846796364810799798241707752574970501707425408318264311774438300779458957900187973914331990767844256178207835215185337463964397224065896718444163792425930451630438652016889064298207893085745498057129996594704862708166262060290318497251646,
15042285154658562758702490769151023049549234182150745279458006277221249108073959927250379167078146371583343618177810781399989738620297350055766188311005237437671847157855080615703755671549924297024184991499323177261085756158621830785078489710236236680137675736987264766877041654533653870329815312162829601101,
11237314654333977894795455004442264291957614299259966820999774484015927163008629778790809410728829007614407444723371959751131344023353264797201201599263742145165809997364235036284792307174091740500730063103139303128763935065448105701372802285259511278260048583229509322481036750613145695758921849832571077095,
11248302794043477872317240126460165189169250658580388605844215134074619662653423247305170129306571025645263196321159161306208962434014286639857800497094271078681245269155486258234427562127455899230971240218314530178937678018657141898086327840673878349974819639770640844636021199121527257559739150846149034296,
17624193267931143243790827712579086604308034217325196957801284935032947472260715138873135282567076545447096713119758861124911213785501074291009833609842830775248849127432387124573114841991824678632786397312400237777005029200641077946819096855043486662608682276867261831642730073281659875011894867928496835767,
12538210493257124596141260366243943538798474382790466979445411949399322415385397001793631762517195935230849240632999986173783486292633060773057599193742482482959257226110271839174624749737428220105282185800919400842802846762420586465843975327869882527140829612498303097220745636526607480235001826195714999179,
15166056560276101270344709247224017313837877495764457896914869872473920187501331897165086047708427904634487843816473353168312317232007646222525099224255184344776688488699485908589470771153089416126823653682530866016645922698705688693381485466627241900172518500051747325302736061748367370244269069222542084430,
17408165854537278617727289452845245968232279284365306760028110187359653111684525026030199424778095016524661664162359003145065950839048793661738750832189931307092238067062265119200937656143218617794530410665775158329229305688445422796670627535481735001429654639375253547236219990426030069141407265327058977209,
17613906816684747880482810018942770575613339263689755915575243628930006749659455146817432699773436927222671054615950365402418577996786418618166453242324765806868224196805552938771999589311108325600235915831592580554591645275574275762539884915449914644263273230138134291956272994603632285835988601150130391364,
12908869398378895612707159325990826564987169388991382267202298840320542854117156905944887582692454265938868064803187277832476477716768872563568261397801480361220579568879672326392014369921917472496412731021268164527425451325757025503770300673504048401132868378647981536532107565405082619333713406140794995600,
16400094384748267114324380967912433704244065207323861146506380135900245081790094747641565674617655145437040128509709357189432277006584182064778297552913535005568311860955763672669452484205550645233043380007725774323585567230244611794423846705434569267335966207852487456932038394321272521317756710299138983681,
11236629200774239611246663599371302510120432896507974100144518489714621793221877069843925949170740935777819079924478252078105317580520507377661429565265177097627909982851068445729239984877906374597271803662518430246074923152542943348792202620148821193743150544231745324377218206795020608389488383543274964828,
12347551190503760571648433499038358959622446369805746172384910665821230497243866654070833395469392595118280411082790518862768886567232240597291892249456394863481206113520450882236307401352322293985195083433515055449151662791433035185436285225076403934037116495824991297201847994481766834937795714763949473792,
15947842221154219098746989664660284406154717014057992827308243855476189575604703810134305522089526812723870268546390684416206696911552886195259068633877651498567661964981554349390145751846881823413087859064758117695720858588524775482281629907693164191463921871414645053602516521107844703919294347874181742628,
17315696834240355825933379897917788500374303611317637740390608485525143904916394155421363635910931491570952431884955408471053057687952939046766678268487406258289174673730203226993799745080596153283643631533707480064472267686702551531646109529941825018128531968540759412192452177280320735671111797964700484865,
11779776693307011734150956761936852294051570243055986211536198714343499780267207306033389975446882286199049822673575734820932403159985123581801721837921885308711052975141842432555576471449637818214511421329941808819825958570409679053191105655215375337652394026204839181043950762624895377033084666860963107047,
12037258966492108501431169871665620965285182543314590783249313624185528053334934102305743363762818036041527424955199563730905388931225509275630838813071732678725238114539550498981427046553122170673981529382888640978862781624283014111903388222871849119955452548128481892153731199751244327384417876105068547793,
12908866032229125739061833220479498233298079767615792679206616327807579740138831476178937031452088633477915694998464241651994786280843057901157244250064504540598131083931896223181502131842530803624456679244743034885204868725970802749603734417673622468471987474988896954177041970408625238213155983815646322619,
11882420353624462665439190751073200240832740796305354206322701446159294010974406530497962445251627844064378085379987150279132574628849506192906421620062099470250898006302478264711846168042023607803213200982301607280941599554444325481082865842266316985743583730035942093413760525758034150996490304987169849667,
11783891328217924686805694506354097422374301710821358108884085347699321571251874793638379131920185591992071395949311042313229453008364808943749443002610515565877455619912033226405090519010343047329940492265702463203180055813474131447152402142520803513926878184777647021415359659952950691976635262501879990442,
11676435087456940497106697159828134552564391306269059803879888718075461514471336203182725826467820270798893962577027848028256263226289790223701700285147932335034577702969033431256288734258241481510447187556933050332733741476212320166566152735922909317888202619395109020814065789928174275084421899684113747669,
15279207775124790249230021665576740093820899470390397717705213774387749548899478338218304434682195865386520656737118478159332609140580765342426842124037334266896114959211826717751315991661010962760974162520822393896751684172886140819709653582823797310142043591933913752481167677688076145916690106044071576639,
12535467159156166330597836757751257808975183888046398510457422606241824499869017465500932450710365538683710389710144569601159705861051445203840355885412496405765401759888246015213913235854087682636632822869020797765387219256902132564727603694648273753255864135221975545216401104489667479121728918643996131595,
14908964357833334084985334725291877354694843847205880572093617230272677380968239157601007637480531890226254161203573273509619419398991769974720334606853742563824550653713955194209410934501291518336035390928117499518843355967132343017260279067194321842699257389247334034377381624975068536455536771067057571379,
19198030476817743362445917690412252275399125921081961939285213873033942051807166046552644974670085772388912052308882426255003908738981747934181900995417575775887071919639644177398391336256105075063225714947394813701776150878806353796059416667903442041617651825065214968614531532633402730666276648026034410799,
15011418256409586672080627507930700528821647680728862467922078447796747674873144566527535918016493535787702780175610671137334712186487510005342857004000428237732872041297482032554424107462639692666011681133727731822596998902513402838404627604348867034104053367946738440651369135518981036626628224283260814591,
11556713128897075644117646998445611726489803211080861456518855258601014530077326526368459570869673065920732867015187346656939105584659065370074820266935095697935139228382273694362112348149492782487978505542919695827095924304690101347147035556051066089161997829199989385535228833595662354969162406160277636165,
11605063678182767163982679369123954553885676181882073235721864800236601246311165235773467636611262224632428259896954879192467198035364352711300192737142091950811850108250376692977856027637877219699100101240875732130978725583854220416497300344217785223799038079129284334824729925820710044475198576064934587531,
11351904314532328241193452243026556999156067918284961671025665699135072648951056340097837912863080963938007023231580195110676917509607251791217832906792761130555404633496205730525686998282252500447571512491798876173309251755331563374054797570459529524764997939734700447194741457016793536861925924652999420676,
12538892864183683957794106750683807170478067725742124847310857529612843424445256727390629904858654272541067886864793159051152959731323901700016766948656587645869391125792921326237097507417711484203174706983884783528908980803544013745657096446895757665677833132468265972319314848601622143954080780145485063795,
15094053125686891479544202182091397921852394348086283454273692747929023383482430973073233140687015387628211562802385130957180677693464150776656576867307618390588794789804283606336350696487849226505432717729052769563360588049675854988122047101695392993292774785842868510614899944139234891721662355763609830688,
17212725498077235453297677434306868460309868382951394752801120014829040803058172846259022970377373716506091630766639485700411877166397374782252455637752303273108304199423006724828905083871131229770935909942785748759351839513364671722015972393520780806336077934701598449397489023749306608374401483627863080960,
12904072807877088871156421932482418160230095108115388344501706984628202075109611938473150611981043430230142525445020495907606313093580521062392146705304143769497427749313115750217948645197684934037197724165630964989646664455566154751476886272331511745473034557566136210486696322060575692475007139369572631547,
11481137115425195382658842184228870191266012459003059999993745925382096381075825551822840528855138201733303532061995642487585172766399248346514150726859135049602337667514518123527259815992718924712637416631689407159368255699856131300418815294288994826941952763943929843447288291967325439729942053257680554132,
15001474793610791930610303472855431048309913659012927662202715129133376465464232294492428866036674172833926209217562672693710657357500225402061622363057897851883940352710156057248826528656738454658500797296830556048365950732795941489600532219420311407387406668091091868980096351305446382160546117388403219865,
15176352068948229299841000936492731401959103730000774488545520772436884569041162286652717518183317048588083091723451369783398626274989262643832979997024549868551542484494409972215972144599521264897169619175768318099272939820034785776379836832832046757513858593312233800088853863386508833899366817659569604685,
11607039662348397635590642484876797779515907274145623788294800315922570486925687231185886522772003497848089772676094458313104600214743145106134065681505719149356341828868833743165100348574965525211309195932149538390535376083892658685319313687617083074223480493374265761818887399195423805161561711231129716731,
11674134859746793666871022425104576300815474468015603329428522843208491802352981698767824376538478444903651292640551851447182761049203285054979692059074640954223686783460954785823707427766570152669295833294382551910425476355923213786888490423832013062011440506591973587859170765789182697186440800241880273136,
11339583900848038147983261649982664629701159450942083168114948921919053822829704989214156066000824133317739560546341447966790631532908752821952444242154558892335017282903052035782053994469711485175368318916828703520630069051174860653644873022433363338037884620698115211237190690063587580846471419151366249143,
17613906828288718963442368427386255323339754829302700787292408391378497813793279500145351410371965791719727699959614680938624638659387433740112361396290358383009537845441415692222086593518560166005161810620268213229586881283375316197128620979677831310314891340749255256072657918188384994628038741295842437353,
12060576220846571280470300664151286333765942895117136370896884757593749306868334029770816251149922825435682966389082888333476089222430815415886218176252208467425649511676570957460041440479083449929694649525181936406313639440122345913306310167910819870626586043163829839732387905594915706879313523704275600272,
17542244362776975122222617978924747574256322772837174818996363677052032211955901876497421505359725545223424428224814243495972586348237989048747172870791704973551204828464625022462778560580658156020095136703157573812781085160691393193067713613178637385543302533327040593063500684009438970968786900955558708825,
14631153464975169868817096576967956710282295578929963360505527602637135323457030141580269147800433172506230090931116895779610934042706703227099210099826883190309157414422095872681412379692536349143275686859013565482278435205131752909465649258271126802381024190623556762638906749823499127929280693333598307219,
11674134859746782859757541087757592859993652314657414787151168524319128298435853361860309010739279977124799507078469375832689722058267741251543043773291154322630271561779480723786560156595431833973124708837677624368780007071069333777412183603232527366157445223050323654722789789220272530832417861702467487959,
11297003467196857216570930148987737186033277662277440583041017326891930897887960951108321305439317219185953162359274859065714210901453042085516564008197109176574458272884698606179999606996119152100021506388606668527840709436135302279577368299498981527429836655293763668667548345004634489433207049744516471479,
11235638839243009237506579664516863740356045212154980704313047929400162935349679763677201366133920865218167280833924910978436718677126675586502077015361044431284408928767448035291544883363344643833966784368072228652375842574930932497933084214882565284540543476561372103281694344759374481223228753869188862179,
12908532249867961256658563772269000336955401989993107687451569748087606849656552101482231302969875352396366901978312505536393290508672423611383759409784276401346289452407758723821420144393738210580237396801058481054387514432637643248516680434763768359744333078205362939425976845421783606680151439867070121983,
14661673966823657665400473450026914046906401090373862428264677711403768805667361663300505365747295314627840916286934645985704404155474751564133167553626566589121967540184418821711705787604331964503278080868062391426783448656886938148333177812748092964601485529852479513897277310143530510291467343944202127537,
11890572964579369470861884367271873355663070555904738855616439313135689945213635405411714251426238513831579319157554593760334090839510618011430377575438188230462526492995514123488207347491212114310618363993674725435658700150624182625150709461018054537377577406350720279452550830713648258358423982802004707552,
11512373328047340479041776528297152686134023238336783408759723166595924278022050249970045733065771740989159977501596181560494934987254835171639921906819418698357971896486720130088002097544994470051479470677540267390780435082833635777705483302771978008570656042689222476992755110096623663531958130666045196279]

set_option maxRecDepth 6000 in
def c_S0_2 : List Nat := [
11576202813303514299322810978875107145327810850993912035443350340333012934221777715044714360438206954520291557217275145653800221053063032421054295834087943364457115232046959593797700357299577419632447698798868521379614659526480616827034888883588880597630252485443391788480910132160530062966656179440056541103,
12058888968187105227213435664377369331599932744466664077531450890783945034278800939799221272861911345080778100515092478500040313933230861308981162124274956600928865696863845805987547543753276833812705996362181086665637169929324216347199956073095157667748713292508354399454461774686736392562128107731472692264,
11777719375852353730295197739826249123977671325579329503977133552057696800729509404556725392225939014584718598349144331253904472765435662558197666792504148737298010561705893250243671108934157562660329535017397058009108772101994225933849097932091484464192691289946585042515856458805550889184921255539185353789,
11516796858649119338076382964442414066710288865155892498194894382322644889245814213501869283101176256644703972385074589275851633703151968282005548678804342558729570717368150433280711603165141941438091886399410995096114290275851459145024855478620597189703856763788578160931416188409693265515780387640251616975,
11440013849476327406053960980396484013622155183100174669841381337384754633740442466474270560859435108131637239321755691033745423690018157177267006172404222750593565513274736705158920622938117171428237959903855895871731917538644923163099040042632030210284213103711880943601121295126483888975063941314038669223,
16297220759204648018264176191600079972035126747499022425730349824574239352765929216695549170843462449824708333625799130964203981624312528498635870877274081433529277959876046042208461340671070506876939021819406101965415232444763761079315864120534602233304756291119547193473072533996691645672522644906549353337,
15052574891633883288080093677578339067567628465514489306065108708608567833345586678256317955969484672014557555903122189240499257385214418301816804160698031177148688773113962853925552156053085098814549059198218621156593239701946264716815302963093782780017267816666666718374318506813333530618163327426926512126,
11998547296461430192729053499139422032873237519083599220847271843176553751539484571757723625299396812406659713457316935157332651380226411205545730257585863591791931792286020946369927103736002816237012702402591046335406176065971349515728749354383915708083479265215220672852094486202791941232185618399747409944,
11676574739677116464718588453536461629364443948082508291773904868083372521280396600462568158362984708886783065570876935468530033449252827390911549959050429888782264893500847438961973586678138951030483443074428763279343253660759186109148606999342560356769926641201809348124920939949126682098436657853396357898,
12722686283177413274903074206355902129660175211937951177289855243028924700675567050171578440495028908321754760799406715393064095787386207732426992352770559807287991235077382347863976873269047921458029627436492415082921280481012862598289917675419162360194430504470740750373794535477316573832987642494426714359,
11883061542254024173071682103901198850293575535355231530349998716377458257792089027997101714727572617702194139894304707630619462684534660894161127306334731003559259160640650836859048004790614136588692912722694290426453277051682782186281230760836435270769083825780984800064272987874457140202224534703145060366,
11851135943913080327030114778133186417771215994074812542490333133273552266596183955563473195874390929020780475409602816756275775964762745691026522590266527142315070366714753717388785591204903005017786736484859871613591490477959834252701695435698938442211296403564698837811640770399763246838541596790929406769,
11685495152836303466021071113989634114391846076866130667641863249246283179161813378544078563773888749648123880398393097025195254017513012594829731412804247054123042649992728869907216306884958957958727070751518605199709055942733997878769694230035739054747532432333362388642459638642458406443640313067723065717,
11406452002413588396130692444691903591200872400051696032372775921224370566418570467840921568857956104699710428578406426819734524909559027711989848406910748092790280486443164069404168001535628459281384043176224356311684855074853111378931727897926783023357812522946615139766517078635692454769273521444427062483,
11236717184038826395480899345736579016382574352536226185984260326228522478778930136051435137357975998726814006505356833313765695013019112478742299992188322866084593030444461569170735076053513002922834294952210624354758268362367406067975865946567127700102778379492175219591999850726725304292221539941069073307,
13095114586725150900892474002104367533516467861019988385570570885319156967093364124844765583574972636434268632301094741899616634583327730368373499927248676225250117967666575316884391815023457559159727169456036368309692280529016242107392912969290222764787813351595462766565623556637844606146206564091852511386,
19198361860036757262054466717442388420053671053796879454699053647336383608225649915740809596638642219123276721101982616227241714577871232327874866769252709076449595113684139190617545484751838527675951483008231849382335620586413113752132833838418530956000357515503124203485187700497435960089082552376671764480,
14908888424262177292280105499283437367359674755470156050130070325520144050840768326977845517467470355838961707088994700042927021425075040029927065426265160522765609327425103417714964030018594635104823691984773145590724134234693336890695495689266406614883947776194233250450184321967992315424645383980726387970,
12722686279940966267295459656631002973897074272980508286716541606657174693114059318259187482600564451537155079507289224545055757193910280719568840817886197336534975528511580556690851677238792628696359452649092414667211609907716835461311452355615437775758159997715832253575729214741662433862895586945751482662,
15237718887361459691482923756612972775997811594083832462696724597923226210298996003294467681667424725466306732903705054873112660334799382345961698549767954960953410616806713060695731700504772316817151225355721740143459845331077879927139190083213734912573475389619170509903039612701398762809728295207939508332,
16317802449108670606633236940036384834709045512646584579298431677433296891485204395841305128761547672455837889736484195559824121956355382249420503303543113369425989947005584334570997800459548035578456057349658780897638502093210493558663907670110108608468713801745737607688306005003280812108394930658638529657,
16101776031370867493262148110982306756690902536365161825574318163128938477657137000187787517218554237765171367101514708759621204793133944583747249888826856573205362131524491548382651623050345015636089227094453595950523512434595622795110889719599027964287444740672000533244174380318730574429975082225470211212,
16544455694097575240937960375342956159692674087507400703595012604827892565571533134710886967500338705429939610714079163682643318476905179486106468127561264499203080503226666755165014002753492759236746746752149933075836075704883217577232817755441376458348144885259606135928851388605931162991908720260707188997,
12718552071223148299286624863368951356079714381866583699696570491205828784452265571622750103233079752589033437284455032954235863415202801237560506858419797389288444651071208479909679115389672554766427926994430533396961891460613727452768073387845207199335405499675379957135743297510065986972994338092143706610,
12724735353875484250193770138383692968834044637893919520312936601446709381133958935618985576054894491679067049353276412806081114823811736037192259546091327013006361416971752981960896665906896798883566567788841104969381939581823847211129280557698762247857478957313608890060717182911829883293262559572917288967,
16533825996023042481608714695966029874690163351600213210901548908464358321787083114119367565520099014731976285468939736861407501061455391849521133576462101773359966641228059698712048332408423469983632968506081366287094749932522914421431404011701273011585272543222702685954681747053383071965252767713280886021,
16163504320241820096699991130438457899879296155935849398013592381618132880504735239006365228559285979994662585967308911771197833575601803135318938939878357654486040278954206744421821839862775181175025750379646752024467666731698505850376317314810565779121659869756803992470346752321299060001492293435706867980,
11327862894183161077719264152179166722632581350748429966294614964617769788251515390508565427265949870616227767907006991640155270481222940606503052048935041468606033634053078991161662246096790167674930890011700140033954941790372559400809666390167610203149444622227391277525430959617896629557701820274214863045,
11826834096824323442813396307763157349303974389621994493218766951702819162495407124478784532123502266743763821811086247862974727524830364606725385350730002217695942779010987856655899305321267996898012307245623528226799500901537783435110633035744275664779597878718620938466602428826808823741359214057904017643,
17665672098563492388378131573226709210139363535906629955962625552246524272393766569305652278985947405299347070635945297213447220884054068783282238027491699230612642400648374475977092732129301510124117319855813530625420960714366199166518333346588800342298230382647471055239844825447865491420710229231225574151,
11998547212680812244865726064994807842548809048312042977152007510772635395720363010222522244436850308758118341453045776271595691537644551381389187687426195035879900236319725551481963874315213091718794001807006408033389687810206086424096481616816189793950431281139240234257027852942255187654774875681633961836,
16101776078087585135887489433965283702450700075717303309798876874173729630753088998239022566807085488465661751670820558266566726204416979972925552223920139949915315905943812761137841980800624984654522402486259557044331509760030074986788863705227579536308691389194058606281195955667541878349633563643197491592,
11421424559547045663950745430750462129168405252241768137693493153736393321805263562956648490146277148342469858616536518100815091905376741436600317362446583600335199350561036276709266322710600648816137684175761234228692527883373891699055822630129760913816280756774184997805025926180470431202695304880042934466,
12719947089774204867045335418401661904151094120554895719573762622631304096058196954726898273146031422147424867520845244057567066505182535157785497893476990476684605951665030866503378819682639887901036539028910721537322479566764067996571210905293249012290712890416524702611261623207714155975275573860525967043,
11237995625555695140942555875835502087657229864886823010550435850359660639844918096007938826267637481174623944457472514730996306383321077699978567455082634030483692677138923242732001595620027084395276327623428128737641587819356432163015487190017568673008325583264745063413001912852280050277424109978442508370,
14836540483473090717545314826327440038286552547596035440700252045495077268362549581040440528666765794682291246352007001994042043105285305690034432656947481351127602857164100021593293183656584676933158751713601963541270006594554321491504604672403501554387640255070075209378660463980442812453884746739407227266,
17634822777416990233476455351142910764539953878543359871389021061889864915263996246427496459548973523180697516535173750563795751963622347892734506912653865495893178537295180893711921476660074873623576435853287316698996387686798079441075711983567144225697944205804280153681223600564274372396559259585240629561,
11685547253501350990088746747068003419030022952076903038730523251289003161686686874792164319143403621011406093196185174229456025043466567334122009025848726145078073338082118846252754828279411803833733368602134051504728867748745496822483844238481955109105663717490498595771908943550810845249322254078901191813,
11874738191488090779789439854759484942372598273223937887979974418861165609655777627777092899828411669336062433099975019885051642660396667798512876171903405338535200163589021499625383283751669424311607908729633704969467685619564187763937937756136506604369406069526829636203024675133008119064205252435297459411,
11328205756009140407544578801315185062351796142259325308050862440565707901973413489299224440645879077233271462577191981056546099151094510515032401547457342603633259505680293359078485867152371952150282569176332614978441241371911097217597213787521747401424457563498464395312102793470598323861479247402179836841,
11320425776848382511511992725979185042468338577566873381047375923146649384257004696137730995113777547709561922328877449399064500294136207642415836512319330086265681272924638182790052842362054631522676758361338259109151988642092975273295267428108248172111560951738057046008834870570585001085737769194117828845,
11685489544818182678631934561184365853569454870126646245728569820101215502503432893919476825704013287922380134486808549017062220290290335392035036983281225014232733573559823469993587010277185332064531533270098593020241024059546038248521134935251415475741347842855510821217741836048495213442733250011823453944,
12063655266518914953913058391576085911723645955911253811389470352270450888418481093297330649217434489554255747327271935550791772994288812704871999092940756359299245623214923719072675816189614926095817216781714095360695177317830579759517574267044133689767440717746232180422942903155150632088852134074595859667,
11608309094376107151949094086123383276771519425000487519157956443343555792002322348938884323533841549732968964762115090026582377118336178912120240312484777301993718890580660696906119097072219834256857659804809473906557289017970374940202548343500511934012166720236711988759573117523959689838013394154233208763,
17428742583854929105114005370339649425966715847497041718248387247565151958091277922546943872618205805044135942510096582520467844874619320834096107829309133962640081892817484624173054459197897868732827183875048467931116572575192995765721651229951568522801916243948499657375534538818059342757044380922233980156,
16523882667435430214786265555959843610997326235050843917083445510570417789581083530706040226253727951547912928261928683775558557716777724606313067223333670499693493707970749420510548807816773687196087189355578463013487338860409840758868962056431929579842962262938988246885504438636763636688466908771883057975,
16462163579828999140796351122651064613173904721963215354281503659864201283499243150256266922165078355716835713220743860961878151738797542910437297818340547527265891024693373412475454954422886186621496983068293768532470095635467934800136554977051592991121752690019660391236242014708102846944739809032016135910,
15258637802518539392378381067080262733760813119260678186904610163663437440679631929622845860197424008225487453286446405833135855828675100927868492743700458790420849636420908712318218346396399402341942074092447578401578487116384452838843197559298751910175850199821640402254145528797213931745840396749401063873,
15279224093164404678172525146506346172211283195301028079482130359493577239461400088222380959596969311150436105807126905258182700954428066013679787400565207084330172391517205922370688279738027595907318188754485650198433820712522635659575130555281740288992791457925510002237314651792458833014375875639264544591,
11550096238909451478248756890929896287387495312531409730280787460116349186928607776227539778643870878007281134560628916466572203209765907271391586615808353167624237366731166991452467095195324915923838358748223586958992859274702902838235972463107488730844194787881780841349235124018081108361025632646268471676,
17686261227431908127915554499781713051010645110084182460965119835271750374800786461133377026132417675626487714417439603931881154147609214047691873065206406175549985112380889297024784850326653489035614557948555807385991193582918281329852532319279885007805085922730484267065946117224263613386320227633221372320,
15721174797545213428115828603769256982228450115469013059491125726438435676740780867971317159929127013493231117581979835108243469295876598540456352096028455530707931176212509606811519276353734884431445372001239770000958500538996178735021946391563733758960500755519717411714791988269334917094472988906377483565,
13645384633846381661959822035883905730027020090165398454364267217145183328302742709156616553629709072491475880191781694573007620741836646242786521496827392363394461985838965606776942534764572872261532008312575471170155372454848649384621896683017523079201435269015695473522502442896137872323686906730311648198,
11820300499654623238515845923405666951030557495130886725104240022531959935148633242535340939984729867119617963998283971654853395143691384286460560255369610173080039501088650631434954591581206471507571021232005878094212979625062462087037783460554224501176800601485481798691006578758720654639619325457791680650,
11632303143193535434793643892468642134536229075833247082557358545489003129909538797368631492576774379217575342794372043972850034619614194205975858905933921650236267064033435067143945590099712916796641488261400281748659583095703153207733651155291720184942489544759949535516397147497605053368025168911644626091,
11713291404898297386449662109606350326458594422657992571668366413981827970792592387999391079422883829258845432712972294905369157339553835722856886658462149414850688049793225541168033630660968541443791387711998723441949836008780175426078720937379872147082369069070774575747476055619108515088752784030956570135,
11634697620626039864755109720235583971601151766288968804824514492036671415732195649501562249540791070016200508047494357847539608720845845333505500845288622975565989967361817083088414304382535984972704868400653647324646623109633946431578048497727561021160108061156907606142323770834931568637543468469137775487,
11964322871493603299294405538407624612620203664583953462602399226647195201768796702402900883099375609636016914945208241420944424463935007423273462956479961858798503316390679333888280150209469243765084031830775803242593419370562308727022912117332450772734274061219258532622886425033755462294286855220102710926,
11283728543139752056036612920434825639053824539790893205336066882882236232291477594897889734660009301996832445055301921053397061728377318236997397402401860592232429189916923238218025238064791635316549291897642964067284889264430437524536260458377585814028217958086126613882036390222905176877596413731203849617,
16575314824923427800032534746195687065717842763136039626158924435332225554054375106464624445700652589763339032197306363779483458870508296596506717738600862956096097723089829710648556425606243356361253674125054399422025680639534894799812897231925160914380329683241570120215587238846008336659648717014077837003,
14672303664744913338513098711635450027452053999233352889960813625549621584307548562608808534631305323215732518733774916674766625307814309274612931823756121968740747470412503819233911452612819217673272639901940135225597579261031415481875434356764925265496405464074570003726805313839403051725117140657296277940,
17315586272820572660321035720648525604415458369321514818575733700925947415019610602143957823051074728631512748484114815121779524583849384769156877328425111291831620798261308373211542010458861765360862098018775756189607656759531519648954869124588722450162121324548928812005999200626335171098473231928400873629,
11608649872491240863344458844553445926956632458075877280548683119525971955243403995699096638006253081785369495921918768512043510795605948549312722869757498648568569513551350519772844631192442270147870365665070517536374692786235283055337099276808195129916530917341293248864630316489278250112057089082086294590,
11676574739677116464718372843335613420174507486776927777069404642472786007207754341715575938252118874566985149414195151518567605476226307615045398237932360802101044549846485795322686039063877402161600505844502407039358625826037906472918931241738014689312709511675911846066176669558745467375153074913887372613,
11821021100108079752522795067933845313406416362353308683677129906753565926901545742933426186824584477028983450026580939546115347421937061857488435106105326741081266697363212832263033956975407361348022621032381904673952544543766738346756899401214509401284865489800380877325286607684844066558811719242041233655,
11606581254316048779178740570398102164759390387391933892675353124753043040403011216585874899795678379884794450586017691221059145069321987789060955710792465527090003375610299559920735695847995759358969511708052412720476250447619407186183851659717799348463444903330566376202295280728956629174666322956083072174,
11306022189814072300897434184319631373119613087483933846049593726773546862575794851961429623838095399061807594689634637550084136144295105296877121023994226564521827264203428493306190021020359223213277203861289170346929072764416325979497858880449753586488958931935140179710978487333966372351600332836578363759,
11875904011689418356316687658527034054971856542393869234234205507506457737021579400132213694748813754390626237769747370371734959224664295439114687666909718087745168820560961503446521245492235383569859277110541550017295776392748761305774893686630101327878510041057681857924132230940473661449619601386991499420,
11591295305046964197491618865651303094420166034284710298888071219539131156653974154488883571467970969036528247500019796778189479998901713716352721066712278791819723058311013061050459005403070204922456000207755207686639336212496288807182613257909892059834555263761658789251491283481799058689967455261138926565,
15022047880585029200972781884934203040558976564646740834739535646675476230747518347693852650052115594580247338050670697137675241413216019943555303334560678744910862929392580082826344849713162283109879090255944098153730854518057993286666308940272309559586856631676527470157837953728722050034270370167932076630,
11724269178012112606398259777716269787201426554615818869866933722783078704610686193451971873108846455692733345644528175922026462510964059799947372591830054908986819100548141401370905761768627901905059792358733815584547923603664598243044320736183745101145253731171044539703384468485872500086043946934437807939,
15094046294278690767354494554165440120963136496475521277084092833581155881060366959520007033667386034483869392045073807854220272458118853361965973465860092390422032610463242974526856942472973645359150349452424785655657143423729766663564198812733674865464083939450331069145151610771714457108511553881377414545,
11563035124977364256268984110424834999629980556271665836526472089954871533102715551221273900988430821323781910118789967705570412580475213124765644022192150104197252230327890103552850673247211183268063783897728043435625366987774696794122209021817412534387441052808104920811297581429097597641355055174017124376,
12036601652284271904572711547747467885484260360619005100460146861547364422717465089673484804034312539173220124091003446231549763984077103638779249099532784282832213832755221920108742499712350191668165725298292941201568350052799372023278291592334538922913008205484710224248576447854588425197496080314208859237,
11235582125079452264100356555373130922614099627101585157251053243446770383756324651809002483235724603500531100376676806404216650664230267251946241085221849650557215474563689958178120139092627203166964086992210821445600095088806157772146636734649302604658071208390139015294622454748493245849997324701336834293,
11462067443056318419403824351157361248058183903552220730907429902460810359793566212240970754443266240626042128107043842581033004617475929935725939907410883402616876636853590656211404798620376575183448438903294893645594698803671523931600715372929477165279021038225859301959333493668249587502283138531708239876,
11946152910780965518933113147931575615870676817171183542422225843314334851993455925849500582786359454376898554556106938111114967880410748696708011865912284920834616682099418770328249969258121514906713710550588685241254403038896311025769169706954170432475300593386188722176588637104127254543073951871956461201,
11940633888182974331965608029835657480581955377729539716842865097075539367500213595464098799041238780491286074400165404235535050114076608864873566835217185420199719457644760477715814790601004821743852086750035792888163999078670056974822461571988290821825369063032211966016870247783370526995791922701018730737,
11878387379200589802842402172563390109282408948944939203183867346077234634700752700555030964009209057878852631504257308433010412083339444308443591150484763624305538127837327261182035409878838980474330477131252734209231619253479743817540835176426913435280896208438419101388137632257276920926347105090902138795,
11237491471601852821308052376652255205620350697039034652759633835390088025327376854759031008582150169306984094954042669517092870011534976255216714408715571342944751302303779312688915046488479707568816941211150003764389434171726003654981080840917379995411319856571440942215730470704442365731299229458397612413,
12036601652284271904572711547747467885484260360619073276612531164033531603887031487821485637163480362733156944157263383002022093788261825059039714852127173342600271449326495425814732405505382895052160439014231982380185371508268427257595087822089505611145249483815156979678127164712331885636509455882853911730,
11235582146008312751555716833156568574360874330559953504559765731467005165613545946510397252169137478994149772341337932588272978734889563517142454661565061933051944603373634086062825414164538396716195967339496725390285658370113060357858945578348158057249380233821531790386464290148947917771651593877855113461,
11873395027748086989912933149772976372381746454927166418077268990066710105023923156192366176540018566033453098704413366756861559019861179060186107786720482404352007556645493878772530824552428310947206002346127089072365994720954398425281331381771798421511380960072020628284136481293354872915473681988393566210,
11438642234736597084105936731987831567209261092947351919243351119423806474389081491246514262867668351589345334159094706453450054332240607713764429493303460800941585312872502863122834868977555007227406336919356487820395330163843537400988819419980671353443967387825722818835026882805271076335336790762029617932,
12717866724243858903740360336801919872902920765316270369868633765788338907462000407284796142166143763945070695227404489992615758271727792550631571392540094806074698726263994877920554208558150488170288084304948224984219203105880473013851634322403662171966457972332218980146531914240071472481408212502146620283,
17614255716143967058537332068963498256849876979167657414482510239759622833842551804568263681657737515351162031953419457508291070451358977824225585573711645304969578683460876332656873614090483391289700483682930266114889486237339312425540875888800489386486906060290653916597826583626368437507240144261579178222,
11237995627352573302544766056468802764677039712857015700258695540217860881845897335869630272224975659593854163307826860010503467212227495912017413155942312578333658611212916482994677315490455136520813702850976025167696571130434127089640559281458273565184105745849360082451003857721115445964737048357457463133,
11473885608859524865066557558985605150815706700567644483573460891127071125197381840170334432435024771889127117644635295367947487967216201893482815432459339295248648554656541765360123179625919404093413929610408425925921863181953093192201738168255130874856305128648507589905448064494551713145652410288965552585,
11879973713935900335789347696237514801412601568816737880372930256523978974147212173917713438875953562204574588444178787747301887070317244193108830887091305459171031664652786912508808865361719666439867073693704957664172135604039077421894948762754288351471593122899479788699170689116521419980326584213163744655,
11343061061640700350162928857549563584071333895214142712008559634339478359792034242597025654240357789396189830244229806906485953724413403966345192686618061822487493844186499207242550766544927739168239227740350334441761281336781429084525727684169324931685160255683555607019254407191770211063615237396239530891,
12016443875412384655187389587200289291402662436388190762525003876907079151382935484290875138321451433529349561246248026669971493698627616602492773717918766389067756344767055748784915884963749178749427345130751026937672278232069858544734676690020694353212709506908476564704138475883792731026948141276739938656,
14806023297228848763085580050569363664894637975459609410784323410808576812533738947504578960662765491057228391701920351226101848648245043946770416042080280209741425765122179712230217661332358762844253374818606763487185749054138766127105371855628561933433024397333387079531856130285101266974298382675008200634,
17686254959491198359550915896685834027869819068257285488445977532012607010289273746549625809194309565610134968839947163325605038694636213611869786603118211389176063081518299101633833723051310794491205004828405948137790436904249428465162433923812482625600371623941733238700508609662260193826587351298650703527,
16348661730932462779813929503850131947520486814715857941167566014160220062932408597656379276583300160227539697305825437670892450187610172618292411070997912424875533561706261101730188202500604530911288956446231480820820075734807558875954529972546037875232257782848574421305520878210345814469029449698520893846,
11629937034222115629838532589930973251050828091945856024183042901583373945547792251333641790175430108659928366709781843040389135031370814507479193227795495262410776429919408487530661597197574211831886625023479307686682095439011619523258309957615190913707895151502807089615164428029027819618781685301081998484,
11878307330157922132039292647866467140340165492788829736915810204968777915802992139316135458958392861291827584531250853685611643399941640623515043312076625171473968615590089258494446021387414544166706812939818775958427635274335680116882908278045974223010354931269397232820324598863243698132167939781933775545,
13834644703630424485326049433778995124169068891685465702484635683753715585076251595848714154293914226495231117977937284246665131401540469231910635360872280749027770678234631816048258281200300400595199304227342979069948415410126992927417762458064098136801677342805658189063048190805719954220992404996378741117,
17686254960528062478937178172150634095494746144640687584797847475505628747595135656799569109091098887930768008841045014518003543595474921781505218823632364322817577926598738905448516752441662151169404820035844557651984374733928594488925562704086312500909627410281814219048626062257635407854911673397296502063,
12723375369763337449866288310233144628940616356174279594922274547777557393239274447282550154991568141340223728247338146144529958376179297493081183508957673261178763623181830671776658461933859728573282129787779735210193421416048971962651632816331186274082370047982359114188610318363941249118290624518166186390,
11878307330157922132039292647866448738661994683622309316358953035517200203764396901341702339068518413580624235989619800071371552232302099952284588215994780003791857500622953292570927094453913201225828793811344655079012568343704312573801715516186745255746485722807885979779275522736233061143817094137445517600,
11852507349042638000774423733921459249354780702984137602923187967711386280363423813621659090812382871401236190424317065184655932853549776978252142717327162567077891350237626318642711142912333724822801510998850462692745185053778548986414582010218642889345828960655249224460780063962374456565990035548527020413,
12050007940856606808303238232517019119132148358864975613210836512142355175797560038202601523215384765166699371071063406719227316275392430096226106283919279959662885617031710145849692645402398575523070115488959020482073111267512145350466474467133714852811537919101213800679027703877889307856018179988573625752,
11345012682447046864113436885237410659984507007325167525972610497356491374325228431902969120080658551978544941628275575900846278712232667405338836557739878006559058551128708679192189491763889737341187343487452750395705284236127510364507688242594982965847351307066161030579537208259554548336667123937169017303,
11878646131982337444005414903151683023834894795305754346378133705327517359438165187168373224313813937604443113735868817938547736067458147573841599978223223598787288991171669222793678255511839250836870160917449602195031465572535434868442323362839533993960981404531671937399680812203874917362146872058731107083,
11682541671449069060386740494715472273153419618244355982618945310355856065702252641264706979089979429807912558870676709483960253055683065503141792640038849515154585309698488702062338426068908255473139203201946086128236429517951118821079290895366957872896867081603313315149592956572025769492606505153282653127,
12351683892396303454951316534623062892744945222885655118828398815901237816819645945136372651653011155878139059426778472459843278462972076092828884372449319542728594597975847238248805183258926135392073442018451924977949330175789313971538740561675428532662956292564172031955741554084284103010139230467698350235,
16533825973159986264111001103970568394719049929792177378383540534568124274437436743440568714965188741277334103739625383943547696737926768143988506705432432467771532263197646788266237724218018166809935237238608888176096361154158608801254664266502169912472358224816780543494643955234202449820952980172861769439,
11421424560409565161657731574026640099409398964349938757517238864884219043982439129110894953557836104415593893661526063790357193517957361675922315768467013239110846386312777043131753170147786759372197507299441835354718093446080206827557364134556243940905495919068056437679266193232315360811524306890198320400,
11988603529156815735215303866972761221325517697389173283095099128998287982916203960477964918863295382130767714642080367800382702107432203148812087476354865863322227066939490356222112398881792931484114739183501336398965162531332542897420377524354081871921732366073784628846743860615521374810471991446109193161,
11623910290062719105433301531818183015473582498685773542556794436106328015970464859618777309952946648570568652261399332491645357054086977450124059623293987085875285646079789920256834095400416904533148163207255758209293791392664516130096636986151084803644976312110573663688193735931198951219290228826810880771,
15094087101135781519407292183511894925155547171702874507813165594266734960445424114031268582277207446124562021651830211747438883752443635434890282831541709655461709923295024234875139275752494796897436246342094785298213370743007289621691065789718240273884018930458271991454260884806223820938385528437104952614,
11673680724342926355624323192870590127773530315251367054337445947712300671131929271407884202613789758851499318821202055692292182180351398532898476583978904444627678608705786382021198679651197432355028742130067788119540584725583799340562918716506379894425888876928308708768443147814143863999792456156411567516,
11672414795420433650307387106837472520552595164294091840822485235380309902061915505696585584877692014876740254342832655464094529738051617677397529920236405082637474010516246216596866738175715044775073560976248857558303016303105506641160769826496374978515551747071494410141940216326550118400783057931753393339,
14836890502124797487187146279216846018780435123631424920773237231855454256271127017578169661592779668122485065441192173048373311452853499184865205638796493029850942587833300058808017291056688470726569442657290753270140066836377528176457984995556442694366935490507470186256803250917465139632652845251730364571,
17501090709979981192433631905381901692067515854399219584371377861299565115303159379265134796407783523638246622666020565173576853231901148022360479655214691352106236305897036514064096609652749600826088012373551321402978512162652952343906052135989166974266379830027725111085475338584349032472319176688773071875,
16194698271332840221282338439325828355757984272262362396695925415180841266144709094335096201967221674016101018731797841880186630726402026174605823281146831617025852940923803496419599945841588404202410057901334573462836957757863146280126243306382393361165797468982723936400773785031261066882609814465299710749,
16246140005952886572434100792497694780982322787040012399899489357511738764095287104695649900893475594643973605354369087331909874833504829735583135121431206599491180590260068658621705486691860867950339508499633707756448914789837787589335272631140561100351391542246275792349970279908390321080752377385428747811,
16502966681118116304855240171755274759405784738522694845738003075949621154470458183642143198994171191474609888624518760402959089056885720140927124059574851597523804261233567132178144292589912760851546229566970960930424958575404483294477657059363837607560075407275098297229808400533215037986852860932664035805,
11676574739677074186157319164853510519931298580843982825821262736343409069083020432844382866585304442763717320769469281811128625813134388103704503461474076602188849154559782053317933081470738971786653776142472647969266551359255799709409011772415673644759999014984237265696976975291521485523218966415508832725,
12905102595502950164972443849664129618636941556801853298607996992518953790552758434588809554006998216625620485283386009274335379097319822755830320753217962896328994694350509468283445138614309472348767838585367139599523470154382453758382384229193418157430232222645095193846005498213719910054629431511099805943,
11237320073898470541702792070275793415776086913102452199517905504236506074616043549175225003459659374267120262394926327860452336930611542958212010020601796363308687399505777719780008075594558327279165727713843725372667742962364994464822032263458235569212311886434710886172788319966997096268729701147548287290,
14610580594381357639476737201574148533290748008614699937136716300806649038962509414096198284286053129035620650372994992665258680787788811783430491875989554742340220326410824679294481356992458346706477473419364015353859392089203054418683041893190354767294869063428791604202745662909774457501660883102134731064,
11423152368201533960475260461250689337439395840159582881518420360325717533080927962049841498784950196462284539756732580568304367444217730359305860289914926575755104766902653530834011189291219852152243773531958422574459787329046658005373158947682257589254200557452148126585642280423768713655555732446477386921,
11793003915667304163891162505932232207012564907991099063618318825283136175482843717881896797887016143804889209794317566851081286390484068814514628767218466066145140476251257657663800253556750183814471617217581109062777380411785521421999624736306935923552745764495798747435805296788630494072417279661899024096,
15978680384150559845427904779272930456057762743362082446731579559981245164241092489027808932419301468594812093920487859195664903152839875957305076375391222713805025467844178280803872026142229685657859261006893412464903406577729354386147522188903281216215176024152071234387642115399882039182286575262404968448,
11792443128411745793197548604908824928726361382960825087481964566426732811893784995426662754684687566320641040740573327690527360127584180943353953663645863694014723413817939026520065492455227232383358588681296997222666752812423637234401808855466774540728520011574050556319968483082837868615820273433221726335,
11606950412052547576882890526178847913906237050080918230597307928533988857216424865743597990787551325720428505808871002113118786832084757434675812852042261626692199506452156081106779741408704021932741952054640852301034913372829751261445414684209176019178691261973298401726948451523471977580242941967069741492,
17573103697840533165765171345490362187726031211742903525476493061072314621890358075995312792365651708105544377581211922271697999682831278421546148777627914629215536863034471451860940239999925711339517401964356686806568190020346870657922308584758671553814057093467838684215133069497772442539325141855628034050,
11421424559345886264006076061386853587271359070537579355848108625812855377427332749015754573699780387478483087829536334244174898620017931165164652190905794597237237449876695044840299382955440108562865446373169392007356269157776909949874628156452931235316648724387098015989732533364990597312159666266675349836,
11872675234171259506430082993940177905907484279369505514354886977447254537845334408285553400057991124518017044869503384953471379823024811750760484144621394331354821752618453238877275824164797825512137698281701145638683651668262272609222386461933486971230128140098442640897667464925517961663749039230655595454,
11673511375757333973838900399235484369233694899908872119982352827264151753791808456905315765479973442228898544914858252263982023219454896753107094917208782426075242089613736115749945887117172080330488313131843665563300595483577350191796173009049269790697909632430363265561281002120020443420645890042411746904,
11874483195138215568492121175411407447120384976562305361315949925063837530738181535041534455864759433392680851641703369739996688301871958919145786864157626001959842870180750534803141802334426835461009159899404612153538761253170726393937123855538970677892553455219228730583516069906615392619573201473586760891,
11821636704454736416378010560119410476216023927171254083475379433681612477695190864457212416965615178150640438968224162905679140009840453076814780624950248897959936488336048543110825432806592539362698377812766048247054338769914045436592402857402086839777199204098388739540309178917438816367634002532347758673,
2072731234764731199343077073254813926015930404253215476747622123705778507863681533340355761]

noncomputable def c_S0 : List Nat := c_S0_0 ++ c_S0_1 ++ c_S0_2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem seg0 : ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a c_B1 :=
  checkFirst_sound F c_K 15 c_S0 c_B1 (by decide +kernel)

set_option maxRecDepth 6000 in
def c_S1_0 : List Nat := [
13461925448236663882658047853004831893384098483622134109284671892624372321744102596903090443985844978735900944906296338655111546057028009758087612551125018752018406365363047603470462011920789283686633202010793060798260743703919394835914567740430159354962257228444948053018908046903261827137020948024697391596,
12903729714804010074021163311162124572881647230419549433128371804549421074702395903233308990825273403621167542515635599421277819727406995846352973090372349061918034913936257551596556210143346862710706364695958346479922625571704049298586385605881782438427116212632643338782575008079875786255451014013746872330,
12099354679127261700452507353383458583974617530416440297117008337715746638968963261332283592891914087390859429460434317191605811186132035465233668264064780238004798136436310567706243588872960162170345726103209430109750163446792610566331091660656106861617431358814524122328901841678637884124667041942861253099,
11624456382392738952788244782002004775562785098161754033276596743628413545762066953527907760742059351480176169253938123671547414638637017267928042792311136270620336528267984499356054941965755703206493124248724391192973887737078389669963352574198071223406911652000598198383456944326349958222029597408055175101,
12077137262752525941594051020559076639002536757933121602801042004191510675547433283022973860379565883766658063571292797191759693417898394455020930541432448775457536252251273564308735683746030919792473925813990283069957606765090492602018983502903858312911193246891376461098377694123268854550333707286016210711,
15022062980159370619342943794731041273175592626572599922941392836785321192641385086443389463945111212625022050523429604486463308725955147039328192551210514188390846856189915773704066470010839650079063811954167486699950975994461605121260025468098786329020493834980128860161812632376923232512948523744715615761,
11235638841317662756569809730232249491967528199133737528504054798863753316562216712876160695621472996481561800393555996199981106499137305458183894779195268255558019065737100441359789019172575661281678653646017445760967801200761737664035567255970007128078798077321650037275054337822414207234656973660485459354,
11792107033023022539036106609039677996510434935091597553135655599025669488901858393025627684708764268165517805774105967150851728477969169778191154802243224366017410345489641095306752478930158066815387962899134760908434408268112185296546670099148605726488247711774465452232902711518373043151042093980326659360,
14016038712944233501632865688732863332598370923082981019213385187151579625945860216966769314993670435000422291978063825463730397480921194886584881665886104777059765374759866345000016781218445285506533235216911334168398824958677878586596335981368620660088054252243470906046273461850309532219904202533111596866,
12534781354865030812612409047749030614842632844903975097471197513853596713725406916435851082104891004011774679617668716359691416193758752735314993417854755152682869015824885952224440202511052305865938418140688427402137251043663941836454110817236722920492865891617199645205278245829987787751857259728417884056,
12108373809843734306401556490755061220216275066438240643248507272640058631812803991452573987436118444938961542918800621946857319050714142913692022878689462832374795200262818118815003545178888944857880709279366202985684815401988118643013756199235082374778865858516510752280107357503386454820469545193781560876,
11608318302071391788904148078125633316909450297058401854818421871347755403404367007603028487106668191600030872116798346612931184527734571467262639290750012471548199928096244262750358960690584058738485206245295853956610303188165129585047623099569199142100792044844163765538288372306693149112878237548941060899,
11978067055092204572928649545475389366392449081542965177577653858221591013920715415919946175734937972495561349026124288599339132347521904483198471478773764767718149856696172265642770111313665933011981376654305205894873113180922786534332771658846740057989881866279651709197995990758628821766947157461008922781,
13095114588626896395644300037820615345906273640018682629384758278931587376501608279777375093660952220449657172251098788852155515464281177593663742577109958874407867587840811157706308169290727720759635439706607669360635424235376828668944546452203414114469041825397858886646587570061311474222858507218681568668,
11336395294115456291959525684091571372681505578190605011144294180133706830209557664399641192674477267894463128241561488861769218118423339461259045980917068206527746323189175480585440371834433906606901600755507370328564499634155420239250575290654189524723409373014496332743646763935302269319256457267798310912,
11945814413061531622128639321229567900100211817109098029078053801796214154211547989467303823219476665209719274548165850950119160983429945124671904234604150648551112859870550480687423867202241922317453688076753926810658494533746916125688729265725179193436758064147908673258486319380517600298469512533433886893,
14702839219421611920328130195263881921258475488939628367687963409636906887282396999500088651443224307771447124957524753062137697961689891853405913312399515616129191202103267317050472860073212704778251462525152965159038580586737974797589163483204631236421209783824221749526801430396815284620893090676088089469,
14775165008100581436468347423470436751175279424279561356147982882934429788591331352845935712580967627116091929669438343240471789643087274670782842145567754105908194523518982783039909025157305658429202089236989598344187352434792844869179712102157708674677607537183191067949668340017803429041686358702415519675,
11873023767461475704768518341500907878300106434255165827824518052071649275588426049123957028130004343022763567840772866687450987333788340224519046250764416431302056773069504284578509325782611675925869087243442086807041791424831634126478524709190491356987685737124557658187874098308803105914692173650944100027,
11872675234171264835885144396350884243048541957508767845004246080696839042865415110262676074453910572947227101344432172243729606010841623823371206843009232086500285049617240494305134504336983840966293453014430531520868789577752560582602802999851860916995535917288476289165238780865367275928722683468421236852,
12079262679082373053496242088441381297662529217589433321110303950716313900154038936814207166539991453508015383960665420735168663793006341197352608101576097425411239258460745448120269715267941220287777979729530343742595402859491949287411666497158719233210178870899550137877235683333758405635249691690951673432,
11792107026470604670871152558000880314630025846994201511183409960799448883634438526509165789672737678879417299244383514309822666893222227544703812278219038049856128123165483270199498927612297702392282708398574614993273498570104100150835362023723093744038813350712525927826671942952844969922605643382935989566,
12718576283762412335204635098272948126453697957686392318302970470614005024606168678805825268923184154083930355582259552205017284377849894850365259677926507796327714804701713273301788608933523967953441384167551319247317284332103359911535859643106411516193851224214787029135131692161867091336790755837026764610,
16276999351316878563669347352617890456561993467858933364933152318776409960220191953513377532921835844902991823305017163172701420356862200600167054920286950099912246116664000561571397127199003143895196549828367983323981827380219597145164323422590556871511126458123170668698168720292769384979264265795247638989,
15206875898234856875893756128924074648031219773996103178095595746712773652486676039044450725331091901834401625355536643151176344796675882708641052380793669685182769154667048715394154820244497516343854142629852309529412810060866137958060824965074444131933909545556746636312086480027647481461808983049062089854,
12102552013177109795199612775516473486034912016052758435480267600416893204808864897106630409077313691913623299670402273850114433939439620960567207538709757673345972672070516927096382505346011915661125957478183097292939997976962848274836982016191129758603180861788613429040481638538820229798044089741599573115,
17613906812918849081399179358219474164929378906303661483779038770738028993961272524720013055265821757985565227924870219557446733447427585821534040385228866526936337027183841068193564103264880360367955647430213865430359913790087629980138211384002496562748714344407090444828893905377809367494694571037228775461,
11607689190772219776174657299783706995119751151648554447202865143380035558628153334414842081071134432942696084992793226887272862319558952845173350937195462398749125462995994717691593273790977018535630294285909677756668902423246085058189398490963149499202162198862788987994238095713379291458187310841510955420,
16184411715533152826492767661330913141082900555352162390965125168632645108764292768021325597913790275840954753840947226862576651860982981934568723828338716799581290567296384231865002234753163610795501905118112386468880564904411231684408063974520691140915530476126482066606183870000823716105474884713903559983,
16276999351336038671593909092763536149836016696174002663449217387397206812882302932136788738842682008741322247192257646912083690428555050965536254992540928966694993487764980648314005909654707198795660907058099905580797962609933423195838144443639653027111043165828176603459599721857240351504299449859272835352,
11886761679041369158806351463486501038533446436440071098449021458758421107184955283549488835467341771901389841186464838368576020159432056137335498934033492459618372543757555908374741763932316488578771982058212096933952969058948686604506161478156442052967725313689390980865641831176795074508046789431816224773,
12113036055192321326419266903734914612327317168715739640674584790906739601051620209489010333269139191203238545292436003561963627016301559091231361219544328844294211559898750689364899931056599892990284724214805045176113788454667878128857741521068915506765790877862771769709663105181815115499091551376318643352,
16533825971180412441947962747447642211227691049170752925910116848795158999754207277067236552836563868921878807504479629415783709478505730221698469053176648547236872400235135254120902611535220126983535552336528755430541753885472122888810191720043808123408621534042847838002620773613885851000638058685148467439,
11471328092095833259366423056438479482683994487800170267052152279839995542921553941894708249424332110550506064650848707952421161197970459397255741544184244803384445105562149693541315814419442860719515747412297856241482269009661338970481612728826846774499959680559217319333396756006281659231358384856229839269,
11673134589800880093191191639199128999931177821600614590968103356278752749425529824381006033273233898660590335514076263506381073622576108765067217266786641603676427260621075701786051739080664593476724716948847706564521322313293998151529269996005521433061534822433849426522250769130956936250378510950656387544,
11977949595099002868968543105384118225075256418598833250066277200820122913131928560139163031661358815411991943663231369392367251115382307477116669451623263921399211436804695907492686458956870319405378473622143690625781398918977533299008060091029709829539132941939848552712666709693922403465901991634623758343,
14019455569730829522480055640757452215752668989197763686026640109280594114352227533838402797056437867451989557312848256021003326080420315773114530744955111517721391547085619316557963248100595566710537292473316961598312510541597190001332776506511279163735737463231673361403904546882569816178438457320300676931,
12350998101136906088301779061345915519458190814997419265622321257320313163671027059654633952526128833411959046366259021732175806342846882303093371288774466385309225746958970736574151884782679378939246434601590389305461250471601372753934853378490635285933175321999101452392744063267314075237091822225768350499,
14020141418949761380923444236019520730776534044353416118636477885807142699191541770031358639772324050067345915595201543543934290318073143086582743037287127617084095915789541174562953081628397600009543850181976286497949951577719462874321611300708523270373797502674259122676136859314764979040012825956496148193,
11611563057687785980900840555427389641521402661811543024021957533577626685004026011587760123679325600947770344099910759206263630275530623790072168244194397857524787191466530731611784816231748286178772808163398501158600416535422503099907436783811191619482128005710533048862414899262517271144651881592974772376,
12112676180119626697240531870659392303591415151257286154972254153677053983074965032932010572135889952157253083595387551856473403487450934721837230994874541206765540159290499522132666534463356189693110195208922711151066173537633207261064368844551547348930258339661414654066223140102308382994871675211197885098,
11492168599550653617567909470695915897336236072788588928394661674572938421168490032292803664232367524601467584915115033052848693403429285711090851308676104217233450493878129849406906832796404998258366296311767016995631518670770170758774961072245745456011452212444734222586114277117894479219862428400040811932,
11339972929612348589610316721811307967081538429393025351700335938321911590391003857344304103509182087869120421007914625220129512056661645396649623334084651774669177486030234076199370883236135533429304734659133469483288787814448996555136328551114736747563879595395255466166239031045362905942026249546685957384,
16132645177913210221283475498892570333470944657807504017185067004850569260521394944490149742496733680365859141947237968908848606426571958012970121590141935437273184160699581091238029056440524680643083623266488999644299264572952845138198300738154799481114050679293928182628456957132674071560964555068050192960,
11608309100578848852837709634535091304410891943764443273212692624687101827254354138232447271613553129922659118883399387134465358680795529551543986340583877990468411162787776924551398825738711993397069575010844160814863689574856103973534552992240559499035809053487164631758467633770528725348951322704763977915,
12119888868583684738927188080452182721132762326125966619365489936841404446357113094163053285782146656907439057715791425499254025242265509789686217073000896426042361325698470579072248339471535709412055486876456165596387254276775048067320930597559577319905997604527717290348839244256307382778711582188151996763,
12023977564636694408107089095607862198272457027859748394837497156544423659472327212833884026623887567997944424185765220170415560039872522851139375396427057013333683002479344811309896421911163858301474161448517443947327290691699294693663503730237883429410910349728853766761385519218541730744826839210944595005,
13648454566644704201243675850687479687307349145156114615836303851909658070592725332375912075073035164992571827565541959448647280230079952393857657570521284558339008241416552252932151418171223025932878366925996953106097966364127738110479379238539845964124198769712317087393329053065146156201275240569470856120,
11375980955920625137150882554220497150383935340114247057885885320125746880894235534495811447049910615116443405132849112812286680925684409983860993442334916143019214134221698999452650195719586200806007135999250946464798028393921163667059649687117445453553701679569265694569049926015642519660156833766436341848,
12079194872785271182487191362748283097806137593153301903430566937254516162109174556642437936271976366491695368903706939779092654795954270129915666186223669049051735560605990162584366625404019624923139857754099378722137231214518271826583640862146425578768222857375459954699406512947947444203008762281361937703,
11447900152825250775694695952878965543335357729118574859174044188149370154231357475786756288819852959546351812170750512169477211116786782101435624312024346338922320619213570069936007955967495450456165112618903734607281485789715332883242137201188717991069213264190847073170874916806986956137504157534583179435,
11865531264337736249127394879052956980821341811865744430793340930758523819675798873123478367787769841203187478895706608019078397867523056473033440334987008158173344237266438048382773498371674954873983422879163477401729534187066605183830147396941035836655693197629974261240152658148482466581939874403632618355,
14857463629611386429264983090954033304056244217688141041921855517004789704956245208578055297303242631550906401495547424649367508693690585105638422011459230201678307743619339940412407576738940562771883467346784067796963951674774975583930862087049965834737836134969235780679097851193741288170856705126296332701,
11387638655653064461260142544893881058221533994770200310365592335405687561770871186840725883958270697573696106793450453339061112368173691673507507805368832652388878604955668034755481190290412022193026605194012194394073604398731422542451476952962812926454817835450184124024993673105565796485495541215723685998,
11680492233786359431467988392127211494009249981159534901355475535771846731680773503810991306098643978521554015235148510245576140182570062324134615607991836205008149361166944634517614769173461566247852294134834079436293327366471104641236763584897063594705923678552244265141556092712273250405331100824567551263,
17398059644831761581291609082119194725358337634884275317874547933500213554705508801635647535403859734681151960093987866948639602562362051523693861005175605459710961354729202427167380346765336827777900230080349183116950171526819305024198696606713102954846133401919063789343087890039857960274152767732327668947,
11675169158626955933012522657467405280451978047900154646063286209279723323933255513477851272472176393669488738934157483668633454067864276565630797876286575287436636048727698770595920592177158010674553465967745555432668939731776576785370853258257342913041371705115806513631807927117792592205173834480142534826,
11442859730424671651813046256917648162383947392537685631339434086661232752095040583020760813937908695423054677904534209156235707634921895697476517897680786021487623007281643210694741989164244288074463378630271162166212004823784245734607125592737384409415001817693107567496883740917572617768434299792637005529,
11882281612082682101729677883462167222490930560374733206562730205079836670805526090508136786772748930709491870607849148129760532817328975937146277792556524846906173945738900980195010098548128190510636348032761279988998615933281756413197479162826782570427906934175237245828459113403538051575517472858028713647,
11537090331946049398061084409615030875852039985975109817993894447674322461416190062724619343248510356859205923258438247400998744900449828610267733448519246922867145367347422861295233684327416167065101627212597353542077250526257040955383267488435218836547080468973469714321222103551024352958056784523088772098,
11375534793501976935319721376844577741567916423247347992294718471123358113925049575547877165600061498598300438293247560414400503031023213790684060807471100133844793999374709387071804070902843703045017103080465754728736135639156648293887073684686402138733869313479699320575778557572419674459668748051892218569,
11295389371606318763195009353842411994720998539926049353335290917109178031602642747600292303410769671498522283486070993675692555300935809958282283065517563651377407783262279148783055434515349088809001323079479073792827869747770203988147943828992354692398681969865598059029846844803308976507387699016572966177,
11321005155378435156909196509867015361522958383513303916472472549826449162714113377721782369586479492611572283790476554574726270307300522227123039303064268058973754610408772255721020137195748069850241189212760691994356705181448305047284969910084063508154782414811779609235836149539640827271376590562913160913,
12718938135494981292716596188182219793683102418963492016611622607196435406905027359596743514472921625496260263521875258141788186275696756123215083455586589296231884711025469650243467101676467781250629893466273527067351935283176895912628543374541960473159274760200399620281281922880137096850035005244320223463,
12350998098716964694539374075339909479683247942128224607134893985820878134235052679643314299504855243637012648657684675703546986602625582825987655812172176407788887117276770280369968454994882222633292271195209021260985836429123208514638865616425876428116717084253687003275751322659718924376314350357599591836,
12722685611284653308462407776788654258514873342930109462907504145453075340559574441377415419059543140338836528048693971983469407661554330958609470783882627740685949765933600391893552209810534046099224753500469325864973086468105183353399102291540469441300610630409876429722904507486336573101358813310076290785,
16585258629284913104220056439384217774026367573677078923907284218068655689071752239660663277003698671460946160896731234215743331888249351109290490041371305872265624090611167968620485285716497627686884315973144248789877745400200755682995803754926445533891155609995850402865536512971953134977020764778925293575,
17439029036033465523046831850727556337049213671492994795074507224500178439164716921091333153684565923118164436738849276658975849337576751374648856895893016231676885127230734114974801711639482605572590901668674617828881678063802416127101832205333016186213443259695420250718208524676700169286521388418331641694,
11285339719291014592183418482884743911402703702086724236601363388992253798701621202464144586233171554326960859388843018469428361582319203881431529913520500317193494172373714873462419582463973268228549553948979807580210794962638628109137896504975122473653409068766643570470348674377151217597116522244182313501,
11838712878630383106264657645763075540957085793382701888907341490538586313264046571742706806956648188741998113561517368507494314727435468540546183411091837388469589100985262989426016711817685963955545487246970671461789293023123029599368002473815334131615464844003445849790005060559792800952920515873756155605,
12121647687786236405928909361308785750491342312461831269800715007939846867431441109516025577078092543743844138311128677639605216840353824475567657704436886784445318439064996815141420412948690062630063928655623299857139509672701526593010088206881034374289596708711900280129851731531428552583556564618591636661,
11482160070824278255528844463544463144671669521487582149627292541953512071074842638399308851694045498293328838066658373298083213719675712184952064582881516776535958520839449694710182609354109643232730579294726559086536421229548538844368740565263858668998350167351488925571401575789258420471187378674957227307,
15268924366665312583761712806885757193506999905665936286049169474521815400169985483686458704756207511218233817478380292639190858406930372627862734962366418311163852527240477232217060589463858288692963149089844096013059635059135890103786150213987523962064163214376768030479239236114812959868928559602788444422,
12718938135499512298505451932208371729585799427597791646917184692495043872870478287422415526149944235029850630399719888309157835625178060269050162353224496997472517511081518911521056498183362431696710051480103323652852361137165153695092021396550373722952819176072544556698273779319512186051110890798327368092,
12903048134529729084828136366015521176003942857760471332948097376204266956617241048213450290408981969816628583315644964705590399916518591869077126687821951945220840070553462001973359856457542733927030803448321293279103662276589730255414311417736522900637431492188635923373367133688199970612025937178318672098,
13834644706140183364463498080649587309145994285550707604106519129146530398702598472565293824602382443912074400455775811884236800474628991029879070600017148236275133005793224480571985069950364328182533893170988854129689533035211738786838752738321998572342711293461154221967695775953680433669194804775336314114,
13832926336212300027493143861787827207043616763902986364204271736313078249331086957696715457199569858246027365472969885519447748364249652460574206436844315348317387337016669769326256726378943569683089469606672427076154382060810648276623209376812651758954465633854329084480351791471468092008376877210948852406,
11877998350605965821578852013281089423136816812135348356519832000273772338298008761300633676442944602979714462685183441137411514610317410258741700195415683848283867514060469704150053531635432771420297189134593117849764260387760531632969088266628647734982465097247600401910707296397676368745867775639878664378,
11470904218365437358435137587118009135725131254484486363849510693266657244118452025311347257367817054384697704593270208244550751285023091872642457150434349595016917652368648696869097694011640153514903695221845983460332673398409305837766867995380837150618352049244699648378867189371965244882569441547374607573,
13091610789349377988805036221698010419574270376793013596286309105975082412892704727834632750658330831589584157498826598577080996157073777424929032139797976562012113938576112795689056292589169867345273195696466068879173716882052424597833019275300953222214421734366210278455085425658750505156723181589051549629,
14014654963238413763847866871851428682120728082555799774404258493671176729843355412314313060574215486416302675286612630748125432157717918141496672453589767078440451848340055417241029500120544065133438704049099380091226879678739566002028865054873645925750151567856109503915291419304320961878816854280844378542,
15166065691128626635133712154325867485750781827767659305725173398714504489363851827789964961270407014961659918154317515617876861312759255050132328686794409060630686602443502436857890275384535464390171951453278701356927492028808508553908085701983604717099618338027766087409629280271222210508397420233698904071,
17027911013285537949433008352354536844552509456554091151149157724165653249965314625311693535878242788796796541704062072160628332178396699260959818831709230402857271643831844251483051584552464132194228533506685999659965738239917961777797965494640533747604126979008573246728256021671961415374239927061554824934,
12075701566147891985106853702440963258786755437493735197587800353310887824956339011992769410149025418073159566917893631514724397435718527708442294719488752814361121788215026670295146964616671890608288534587507918178526822125424357802813449922725801898053432998263631243761980267762524223382608058751815287796,
12535130094356827266786878899756238768860318111386251057039953092539618043087101647418383257154050996376869088272105060688774220273229540315578056191543474407187644651610229309326411737359705419469325574816346218888193637805820501277285800712385849101752924005800177052953708601105633892360920462546442360106,
11881391391670028065094252702588684640096718566063259530456118040880941363127883747016026503922234138138650332243802590421599379646040399419991487987555702969383003972328726323145731185491936473957092893418695345436238068361904097604295417541969638564827866636972062287179657829320823463855452659317575780893,
11763020747011248275824040347852562484930521032255097241054474750377698065240976809412967029074645728113362438864531846079254301984996074879132576314177738510492659897236301704036674084400157015464207916465033986356036886223374376089328522894156826882880178794623695567116772301032895271654779283481547360456,
11792131679540100764807374962368114950390410529650711045196435428372116636721581466139279377818922436354612659761765318142905325363391816952116985640903266040850165704965180968902233691089919324621759471342015678459420891012669017087668147466215294668188068179440877939920783338934165166800306322644217858612,
17686254964740411279531832397383781325213943008097824553343444378696814541865472723013351976379667520008737237734367884928007310018655903527355981241875716621975058049893005995835524039325715358167943051941318570914745470687055141688522660193622266122697174360862431243373048259618670189877378416678252053023,
11422521031952540141863570258726972140862461924530162722541233449172298262496281365667675895247125219479577047836043050278242641827571985773187529975447660117681170852153735447660303848637831160060893473312328596820106453654811132441322767237134829035486196664274136928710247500848625867129555728056992696726,
16317802450392077858763808773738062543591667575351979097432031900112579997211046589720894010524657602485243863424141619514793919319275709090433598163674406362068668155378943910423147456022382693923957430802186979130396438747320397930384938274180000915229679028386612246620137963481208632207665227385443260757,
12532708770678909789112259672304894644308035224329433979500421241115729514368458494332133089591952961703872869611076218512813582372817818517113950018708450758056640149515973799145992661091515793704203156483649647550998352793932996274961135068905700628425724420015733004537634762912744897112766751833173033314,
17274444456807002633296892808659321582483618165877939314677398932627503846482404076406746765004177535908402243121759835964779637074291346101019679469606971527058378553961876047841965392454188353089297518775707047862787486251265781193431599756869403095897947317235196825774341736771430329030901798513767252087,
12094846275337700343127103369673107881035889826854564296902037307231185516978262447101034040231091388464373816266016743162114856968070836927645844500114895480828544183300662580547166048547690743032772346899709632953859727222710805935897759500225978950112691414641972093271435794297161883294291024866570633418,
11882984486379865122008113214718851426951890609992509715597256324388694313580609496492487370424196289116350633245332958508590388610961008062733354676158084506307095447445171287584941675686350052996882877202856508052709836972655897636800345005610503766812603573965691338325705117610437574395589538012581598511,
11613543444125197333272936101854661748938079161761124624169272862924148322816436827009630196523318058253058311662619940384374633567867512808035703978727987400608579864779417193635123242366619445318722599719622745229058184030317752924916119914452505552546984862836536032080420579476802406521660577643936398129,
16462163578442761352611761572244551477443698346055703293302194674840808603521041940587827844928218082484742149119733325676123951688377205982868998275860611299773515063877156394274396174519414879731604445710201813950265125903739881849575833348899819168652799495375471176679161215604455956440924270258356205514,
11398952844792263877281888541860227824044082551497128911158308514122669801767790653662331156654463252658143244035399278448352508642779473903023625725511983362359865070040461254153694616322152801450535904265262358230180229817324863108187511529043263037219750630720690889006705104246176222509757955558467404219,
11877961308215237224441747105059795473849619092154116397343919796245655899094139371760916332548350886354008291941782831393954103752398169151841490329263923292931346924048685763484760421014961862259779933061651317382355246621888530753406809511262145075661179877208162841018988479977068875058785871655986571317,
11824694386773433088674002023217778529187083053143911327240006510909438122807453328530833658179123894246658484789092667109942504354189354900733672063314815274369957523319443409096485137323547797555815717410230776505475186644430282972254479735437811252196868635222947153969800647948153047144311991477998435541,
14620869642441112179236371806379889242073874468095324789948991488104133007647935674566759923061058268238295099317628139894635240105990569745359428645091419109814810893448963136021461122538403517904170114966266118173204158933548061155707395414881978294986006254004497541306184419782557934993364985073393404484,
12352369647440951688234578324831327715398155749692952078076570335257216880042375859061942522439694317493387900730775916090044404358753767770516402350665288113082916673964697676426313044356526250395332608700182959522019660881111906370632035091719066058562608705421415984870260027031983421318212272757345256012,
12349951097719828171164243314625667126337634168600093631836254246496761586448453325447007528891499472854618134102616670725266619616838364692056962429259962241226237524165843587817687626632912836330505210257885156268136987373252141467031457256819988450555519516224845559940540518486868606552043581125667423486,
14672408032395558841844808141464739413351057143818623710948005941601654978103146041308512400622295067803539256257260698586306468215846062015445418770013571387649934650948559931358177192839271152517771893799140990174585810914010259991001586608616733199218002324886951976638304050339192109858502021120101515274,
12118162302630073519870343272625052950068845350910808402823704559315517594803125345527253914799706631760720468237186001692924017747278617433835149512701112958050357149608708259844527441605755827721886877691960090492916327368636495218288039990662006640121274558529383559043303987386689597352514016166070442678,
11634475930408945160581369980720684166847422747481027820262255565545479770077961294165711265257129437509825602336154382118402523461259175389354641413371199730560114887427376726160027207147473461154914272347331907696016038413472432817262532604038036123105241149156331348942420972708997159854415953097600405207,
11585425813052311872584206508615394856921056729355508752136147236702947542802406043279315884842560551020722811382315049517795912849497642037216355987539675721865898150562743648952069713762178124887289898926993865217128706468668226775459880264006842475113466292960184791419044652926158646469580650266353547750,
11722211986261445541763622270257927902720393940178305753877663645898109515034872299452415908485208001134578769437568507901427933514442643156554382515244523108800327255584757087617839782621232125944714153207040255158400309725366151029928883830141410678953608796377820278944469727658522746353712500475641283369,
14806024517430041370898707765776191117758548238521732665615224874433499137904303522372941233621463268231894601791412388857292524680946992690103779952315015053791924876417221666415131076027530855042136523231553558173316465265838426907897870739785657800615905496305015917151936333578440901739925456086200884627,
16513253130975091975169558203891889364404948341624396230459354365131902245990444566891986406633934319065166485564502029098540696323553557907425934709927144423721010264479067769290366402249323753789161871065497095117342944001657468737338463829836900933701290839355590966447436371766876282676784889091922887073,
13645722785822069717701738221732505326581889028098197785970407541206262106768410036345739726724395564916039490241465718782652638575145776143693404700113313851241601508965685823320173504941490262721922375395724999980618614492578749016364826775772327646045451036401211297404427470405992331483398378768421881690,
12903709887291634068499486739380285549981360006820996954978971047680874745643515927547008013801150492229933173852761392663544014824244025594972269450203642521868988697529806409411973458020154224575458897162420894176260491496933425575831458458287811199650621139932027724814507168712946330403361538861957089129,
15217162372622456013035966225127875883637420657296437133800376777844522440924954370174496569320907489947888524566099377434872313076812063552256729411125468806417156687320766562447948336649618345153649409475932310150496948239732544464357850481660994647976257372476106757662734441880670245502632266776970560266,
12903048134707300977847811997649928425715190223790537318956651196642651611742629745270437374202535110942508906377382521612394479078620249070956383712357369391511780954797101477970144066679159489165615017698390226362728811564415937662069795185705051214415527154961941501041981722908936571794362100350293771401,
14019455359415878932453850694711770172394834180488938966316705209631219170065650075206382331947963814957068965254774290879994939975291976381471864317568008313401426205833578069907451157592947484473133874971152125963478567235541612378021842091260954301892237937606019152534739973592277404008618049599300077856,
14908889586029001289540965925495091524550551641088301433426903563925287642557729130920419108807443582871459980757744340564291076372523948714791772156447871831570452152484436711892167198739787449389360232229623042819628540444837424310637372023209478792094255123717077129168338341559235794113610755626153378645,
14019455715190221486531646330347951948581921472737395612653169075327992741134447890949099647804582281860536800830592669643859396717768620368500729160509110511893155270556713260726175532168829701343288216921408823215067324931552352211865133844228270160694320496851407000337528504609338890556672413648157901792,
11633790478818564169006720021760187458483143792888592687544015120597902069909669187008482706684877696097621598173183818018316376365413546844139009176666906499628263749814928027774622880022904722480122938682759477236678366701554154398356071894262798607992520437743883828683574411118945570680785467081858843477,
11442787215101988359421977010747172989664107089266319890765146146684601532378275391106936728991610477270204324146342516665998959602679895155332456973549783330703426005002306389860411504110602507637144993069061103557873601702023035325847583249364474994002760665691840710604243998791628485900256831501078415020,
13834743276560775324549342339108629566840294879798624231977680891132063758356688045424010583783990426579451821166161053032452458493106680513497156005984718089806152889015138072116431662610603300180959463017880081392596476920130623228712990793711943276443078260321647445218321862262451820535470141238913607343,
14867761493824703973847552325970579317802810664303353638733599835260464581205689971940445836090915548400780973519490167569066816051947546401779675763144087348196926753609630339869026834829291347525046114576143664224672121179929539302168601249856124794052914185018884035188122661327934025237422924132824898230,
16523882664293164872699964919067269517010395938070894074811941749195274599283718402889818814845147399146561495477739916242827897323731908811794317011747028517404090961554921944209113223473346877698146587930751503647723784296646136539621767655341000147118797359720802918017920921574852494465028358016358089867,
14661673025077625826515903057932902239445572669599740040863237271221183234164762684796225237320082485129605699151490525864238636800819580084286996466905694815555532903526917174681111591184426514555199954538746310938465326512204673837237576018889770095184134559695167832387738775398048001143798499469939935690,
11235587775333504977816265541456123754409144032704068065281109999294405265750713951715841593217315269507512047677758278380780060516351403594477280611478256355754812777827529212876745691991068335968537432917806764262253363518984541465528971955635281611414650617802996771933887441856201700094712938979579692896,
11606951688654599113173444250216221085051022113934817633417629647923755127304522264906512043260613501428715356246266286308674675328111011095853638922660743898223002698598268499042588897294929650846034054329781096242140402590682862491391865019554588814738288197693662467182976223557285302622282744657786538572,
17377660013996629394836457145551570507799071406083450482451920539943646938253634599134425088762124804533127157827980579705313903637064080079352854237620786669483709079105884657714427777807206354421284732457668067774180909429688035271157451315019744506733575270167059075913443444422391565747442235067393245186,
14702831753197548688786331729750809381771512966243544759756475845681251915977151332247004507314200521877133386393752774718048223140152791795193847824488864894562150815918978211344243724057566590255721526838420720400393286741676366151119109458376247429563299833626769928462148829783494346621056454235203863670,
11288088599648296310411216332244273918865090168863953139661545969184620152463959433307579642974632851404281883251522343617067241149901547857697589549688767081823820072867601508669424949248579730351673509456791103856970565757400472566829119924525416780010690610779138464871375351738893826398672704471543218862,
11468444844354962683615427583052055669939856938968346845493528995043758660897198634802068256362433417402171119350732362162597660526066291988433922576872514246400072545791070525027861073832004250111038745998225943441179532879966914320466308036977163687659097909660006161820917598098359320519197592897566488223,
11634475930408945160581369980720641201707665485805852330004330047609641235221295343046463652983449760019147745084845902951575875171548424713565356568195987397600823115914515101483960057807996554354149833963553224814185178689476316497646719924609308906139742049269832514016478586770875878260317327869519142283,
12143575254103498731276426099636507068303413586363789555854208288959690537220847876854698660920095939282741533586387992463051960855789143616405195981543029783951965458996147282290030496956777221223974504165246822164667569541659052209698396744737304414770284822043044421346570057982973870173277772433335597542,
11357013516073724993223740357008510382852926662166526662586209408513979868587060202121405451152596715887624476666686158819095974275164899968201808108356263379809562304804880258140240620008824485405024990506322879360111004110653681077522882274419071513665465579391397705408072688718637940418829539012350447857,
11971211918340634064000726987460835376872883446738455479688519196048700106550482466108088354065781905726031623924426689747303919458258199698678419312273433397956481118543355162975040396077654246705066586504575708586223775247018355623893587796104380271096276348919074399577894325930624907547882464297268810513,
12054774417669576115905782354530750642014740989508823222762821166128226000704533196031427036429574774048277058505122656396788964011823619127156058485445476753693748501960261031176668988601426269318983573018067983487739510342529716708618754221139535836984618763715228437399508662879627585507502770435463617401,
12141832555427127482408008497700772803830746020976098537625629860161311672279709055991211609835819197680203503408375967751349428472745109358897052075725305883133592607510828257832153606998944103273405066421556887589803897568964469314031710021307988190436906289879986825197324553955228611794211632446078456051,
11404734763821675218814172595827512046478736625490813351875772079631146448336878943261936327933664943059509556394060278417217810315169188576564484577753350914188298611652346642814020957374718453403605101043321864057256571696932927328735341731066596443912609499547211922497461409468258840885672464404887644423,
11470193161479242399452232769752366041270763586765421253891738145701370248414848142567102934939985791200728586576353171491895436996328030550118187530665406628652251783998962111593150474204410772358602514202769196442989303226981930548738010145885351755390571397762177116767174539606345846908781612960513965209,
17357080122570840809337719089439464897242417897654232130140468123675727074871151682903663984134406473895774290076892653451050642991481929210516414129741726520865272146274906175171762466514348393191683716192751319421752730057064644309056684823032506616615380443857791827914044654982482390008912137828877933977,
12143952144053332099134819213480600037145696298090095264098704477023289958854932132852730316571702531508692375712085014332905320096920757469451325467741934278156852102427673932419143862686232540712393441616909115919569418408585054362959680456428144580476078683901043062731846125709048759803573516259125920580,
11235582125116804444707450246164184245251840887133203371014755691739504792534083773367537527057911154918544638190686557111929736164968196913900552352522173140497671314054354823686540309491999412546953456194569728687493336090461030736453069997724690759653419272469037543806731501401919619448941230009334733695,
11237330546392556313427069306216030803272676837472458602629455060274227816648737240896019606104432942344661326281506519636251274187027275874153491290752507948953906804202010248095972634234829991054291318489079894447893326951802190255178844496025344970399937955859476910371539612427515761626661339253433499652,
13834738241409508185235916589902052940927336092854296081567171127514251966998582027797256675062503092247261628075237977598164151051669475237398557983831046393756254453853992895686557989529091794447974285143771395956567231041937464164535494242720412336174725269651736476688068198986815122993284024315199326815,
17428742584786751059176527670740435791204784116351562074819242423066258943214620503760834286390563404406908190802194368293290446891473631293732691573206268236894264426670304755893374186397557554472546120797794508008527045662962049811424911294515802833698627836859612965432694716411855674079963252376378006198,
16389799028161735270700691756974236038926448534044246530559055861764511872930118877397807765911616155845415892624174088293375688363760330662564654363029589822934893656774939005423795024830940559880996220973310563473666252156952133024136590825716466785967069211438457862037409286894475126971146905447567229754,
13647459077249095935731910420852790016339586994682840201613664954366861691342916844910033318472272541247944224150303880262725909254142170473676752856247496077801134245778127166032316190822203927989729386137624515786013258631606963316236061641731704598522886608725800742500640745562968001773981191355010942077,
11448928738303484146880449489897774198648795292689811704876349964409834643227913050478128776170799168601266893098769014539419698340668668676481246079451897331958597143396303018865487363249725315488075194198578858426712938901716813392698104959782073629738956894483737735891825957197236032365134883636201790326,
11676435087452113643144502647975011049199167335640490767518761756766458664542601466392736919215900374746373235857429474548801886862356597746292134865156196794785163171396419489631542982871600080217408717954837408006772276419921011907675040595247392425380315857284500113154466229443543559279052609110190562169,
12076870651560071943321435405194177006931136118550859970085105423114962552680863379746917347962636406556906824776170332536127818870956593708750575548599718957986649814519725071915212277744858314151646509500227734770719341605297133213957919863011525256890078710399030767477449737880519296767816394700914787391,
12534461650902772984058067494630533233326314649379612768506335456143673393339072398902680120477719237576415487907153098118670721544218796069585036751163140664286697419970382204440248106402566128459025197288674158550405200776709462326521134946226099227265722232821091818207059434414751849366901942914797907352,
15947830648024145385688492017642454921859129188980030589720216565272052562610512186667214044824893934263502359021058330938396725906411626371748446767216071026409831335102788563574920019928325251474589254392020946231052909631380007037094876300642662509068495106772285211940681046573482645172329016490550238079,
11331055466629903248159653644285169254481851412853754947090523983356890059087474846535066943895077658378935796368350214762367189009631984869093666173644176780277364646164576985334795149734116944897427216938466067183134232826724036239427786536436977895838148032010547167912632609732878052142656111248089088625,
11631113977556139503639717539013984342510296406098274708573203921672813120063939241159853694027869878777273080980937472370190648289089394581164496406882971917835734450699516012671066939580639331136578484705005724258464117800626066289626380019222738616323185675359722208639644924770735824111335466541560674431,
17501100071450423570080359281340277480744691880841933062085888276975396263905410672099357392044081946659457942534585412576944100669959898361631600136247049709077641760893070028359069935675734193397616257402030456750191289086226749471627550483625162134222893978571285001722094012652565914974279188938873783891,
12534080758864877820090477455070770634799225068373537695095119487685357249995310801812324561678319627976867899685550423342698516524663322354911473190902101548883274848211613673758862942550633160358851560567606761261219694787069767171817862562562084903375290758694985328923861724670860295608635860629736555293,
12536823562487779224492766735002912715753137783421869897671377928485377439169823720994534177854251039391986216513953486175772130320210817942294972479382330902743886108326809633252544782295399413336659371279569455163526445081517539546379206076909219077255545138059730445336990233863444496531181617999230828703,
12135416343895685906774504836413778999018017704377713846969356385411629510184226958516953494321638104312067242900896638462069093787985782531878477745471728343138604410114214925122436473975899815638028547319574692010018570931254827290759079813111633473147749834180127843795511728979910846643483895175235960838,
11633447596064227736148720816278584556746518538206510116848374042145786217882382202330810540273003990581961947896736255854990538240598556749875829661916940575284243301017372054789592516538385634723831884863797431120132932517859525668041845439634230421726877091064128475495103900724527981498131365429318456620,
13833340991206639126076673054847942009841559929428743460758367096662756985459277358478669343484048157250370918679769514840029060977533504146269971037311439176193898466786646910098722628869308515561105968500858519885020532414000536789532110343443737355966108522554101225453390408601254535256782773212980152941,
11519678652013827528553774872835274643130870461359380739773597056119139272976446382040339669179207262162121075741601217899818921988344038423518300482101194280351451484604682621620898833467826223995566174625517993775584736732926126553240263767343218384034242726116989371718235985335619368237471947876817903004,
13648951990461232095780428423184829758721561932759179129908919823794914915557319304738480808838741626477145223181218018725832676940293858789709507109815110333439953520012259231003234744247207149693517195089274796379183762665599098401318535918567690641065902232542394773632544248416126491452587705450106563362,
16472449904803522930496334749017330567322495845459244429252995421637881803183285479929500945973854197595140465595316083701329734507463749794697672127152974247643183323325257469572974507719798757979362812658043079747342630426761321555515378706779251432153507091601630979047528160257788894495213394577873081645,
15258308376424387681928535986750283801742316991359352254628482645478866266131339971415581271958342877137762469729517253489115845970523303702673287857108001581851963113769957434669894199586778200843928787084047986100434058981490900249782530621834224009422352004909612309275456260710109984501923509693366044497,
13463990493255774189777341206620866613428246810238118618132914581480277374667865422786770836735035345437736995043585933237527310801507079921143195586564911925733309452829507561288482282180819687904852437928073019839068110616819869234333657535775415856677304485997045723995276820652434984377580023090928288925,
11979025413671438129992600699987943435552631353472779819449862274514848709300433574403495375350287737112953327456666403763013793595761195214179321935145595317197373287877439886688718681472993647210706729346491006912403366933722430368404105591102033469735449483023983674740789479789896856515939751492285859068,
11886496962710953357294505509652132460229764984402539634841160404636119224989033668650248494890863723382825437328651395030422907437288726743832368920664426977361024296693782944815385686808111809269769564462648164035152436112982026286302660181664723819131662235968194806142474155816583820075867121251948538149,
12142315111361574813489525352643240163889205745495927470752629847909546449281531001736037117618141918250440089480003840932537307064493894515950821711328238072430186536026289593302872729534050451386962778129988903457525213210163482159404332302512665705967405557258206308486843195114484423490522378859409852647,
14816311305065594975514555351158836168693182414336203791484778283208559183254258071450287275056535332374744020443682831454253824384933216068217593305636327037682040337628994261344573581543474330502480471608886665222796153009672206174056686802750203866124495216509111685283858262052774531310568524455388484364,
12153505816089075314465120992002889212536080496824686663064573065605161658452124065718331527738736684830334672008064803025859807113307933356103110992810679562615070216335580795266137015199073439345056554047761167298531278266383369849354601528683417914034817045897186375934856275405249838913073168727870375767,
17079339573591069481161298034901470603750198082765926029520374216808073909919921262504448567133255710008524013838786630127459183306553805713064031373071795190273505467087357038476197056699147151000496749885709074865673010939132806571190841117933516117591563315464581044416172531752864766581957156160257236923,
17079339573591069479007218664593727319262853359678938100114156154459053052431236035658447293492086273481685991960881333682114710126989148049803774840460389751465073285558290668186890222219536456382033728512895241630662330920955795275915391954895835085413466650212993848050000061311848310482629777363478020731,
16534153747750883881460363883065763362297936231140588813146809497828566976039230792155472064710739683873935265794828705821756529290127149540706435087365964683654221639468931873525923956462448117550096804522195348448011191483834502669333635553641933795712209957466482943019430076856828468995860671159250485883,
11859045937073123353713689244850213192441312652266408055985528775772664563024585756785550006795095414995383648584949741603725224132002115473714418559943287957703024592157307467635649517463864177940928502854554356647060986550721797149588392941378622279565917705805311964541860715261176708645506277634102690391,
11478104442261255556879585481245366447778867881633434077303697076559037594099443983114912895308671167060612957995997252841284375258159638550336424684961645566292305252857074233361169139278783924894058723707282372182619065783572906716844055024535923297088752198738364222242037315540197921942479988082467900024,
11494964096493949853426605453528406697349287764407083888590103114463178001034217440928647229310095395888317394990055480959510730110242209787478278137146251153426740822431746084954441945818585490502279507920655114886318957864155937643394235879394315283273413122055091008774422215678925239252278191765030356113,
12902757372199934492716132752327093657086646036885997884810743885324855681007551799198104062961233655094519073313380881955401027531102787252108540684777024173194675601473160439119573817167427871543558736695397340085988791452887795111937117046522812996628409856429557505577293330517558270428636888353975616807,
12903414728947899266471679443969432028994452022458755252585834285530102683487098877363722700234565545002803973441967290146597710325590769161426103714216031404883200606817208197070222416128166343338333357670859315810038187595302988206231713064443260204182927304565089349120315582445892346905267829300281413876,
15073134882789814706346104692624888519153736065883530324329583913403749478688439983972945891947922618016122482317679326137946801765095278396887137362524965218055286055396842797290036729114224444993118167520105001605872347219795171170001161207603252792283842059317271146159447767191810302224193637328949223355,
11675169158626955933012522657467518377964164555360461685237279473476599476042024463485625350526193331146681373416972185064245822207650199124929699689399222517495721190771803915481113294503900886101726346328784257634080849586792413111371745098370471034766734515818450156604962591378497211376428607266833465727,
11281363512279539137470784826039812202136678243510554170085105487770429361283673584809774489469776847399835550228788663375745421106102442876009751698551529142680684358648450559687745926403499668454750008992591652519137753614123170815038724728235631747977964008572780595414648781493285191211199802571969269465,
12023334795619611748644131144017281499225156574361340459715350539028858408232270251252809081168494888178853553903193655749531726156494765349267159027684240086672454746667541443508009123475700921512781538492802519820804084701867660478430487493907818471143016816567459333056542414116213992575641391455946378959,
11589270666510603218547469288125406170814887875071614963452034741338367776682334393400594785804801325142843228412510726588353843294015371228448686751631324101452362515179206925416452351347838661880756066307704228065308233500882109192903139831234632187104533832402174796309983065196588743249888666617869964042,
11877858112272823977685355923814569055520755020459688119980248021438946887281478270522467878412851904612543376658909257771279459937830396854123944368111780937786186852316817623907439656254243533208231975187267982375860386588006940627429207669098376644785617676825703754973113372367172110673496686986555336997,
11516454143317432589772886345952399075300223082885272665775704154820137670615885635998807421223183181276709904862894249075121176092313886133612015907806992833034268677103497999265132229953246580592361270726311910065038555928294839250706156434317285996093541194000225458041716172014603063835486642349947698389,
11375534919070445834439071257305120002708369698165193846014602003290266410529279029744550400710023553422644648539731311375802190207814244649883273479668152310613925842943974689993047000241703339114659555301123446442438102734943974041962704997444405504161851470061634727457027417698300407142838507882514980795,
11391710869460448411409105310237042602386523933254689968357332358954842898897425615698130125354942659572969245323888957055350168233995350638387496821115834549519577211372225368892736590729630382670399464473175431402425091195823247386752296512604626324157790149115658577711625954840078063538526447794656089377,
11519574002335188144572254003440994885986648345925615944510697436002036547131462399288838813721147001996184719688860056701336695363986196618358466348564200335258956153142600052015978408728131882807934035218331356130374755190780305348362173962428574278399781189879020090009413558179944937394288857412946869281,
13094377589539898812261834693470518679622220150215609902332828584956569082170795686096642250920393593303844174364831664378727201583748521664973660265340195557909256838017898583291729518383963432290138982776820661354052136559442801454355819858850398020070024955046142581339464908311144477504728760889864555137,
13461925493278472913531510511147424961797619977195669211297281367901689544180720911949710570698226551263012824982255634591536023844400925916909079460947006443924437399446183405769865692879692571552643635167334213711524229820230376483540329159905302030003193145100902726627348548981475481907021995604344801917,
16462163581863779720925784288903691510176778598788210998124294470202065277423643232750813416059511907690034362104016968809418664274297459285281493179773393448604165394409837675056964820225806171964319799844408073562261740370703456306605184437323305306594076333215483316272479379306719276898444493346167752917,
15916636364155306633448675548509819542030946894886288897094723640645592298182583603478201196812363972083807020420322745917055323924622015223805239649484007138645431419541880323225095679847741752454765856054764690596563766996120816491285786548983516389640238686992947529203574996338397706125484492684807078336,
11676231877515418190755701285002438640254708189914672962412466115752613289230762375005726846581645698393695603170713892146603931368495269957127564196231061903223489968103708704180027368575802757154670706034013057914933082014425412671277053123113411028936674882294752344926911560990006100691373163149700237878,
11615274820135392536173620969270435251079076354547823128302804028949519576411851509029408615997350631016733656644158475896720626881384759840456706887216060013192886559767349095118770660570315048805779346670186479867973352233424011610985982748124253102369413587244788954819213323402124727988562228269935559743,
14014667077286246380955827262928645740698687795016954382306513447660643382486566122728258264290359683940440307894896391760757639888578932359823144877209793673610918069532450497984495853787171014598467286045853604824627439955838232504149564153634533558794621933064097026010586665243621936788394998972575233994,
11235667062762802689492728233857707265983719629638352970689864289088480216417731762154324203040715789243545313598107717327012713623182595210685500568157335625560017956524660197952676484768623859245254948324829050616303977595757741555351450151133853912952580681087561656389152094316403913188863856451335719178,
11590848400231934168321529323896874522703165760610398112545008318535455464148903003082743790359554722118591419209352192247360853092343940922269824560031546613029576556612229214197488726779283430047045847215891075711041520040863886237133630772842653137928897404829787928799067804683120457877042922930390206360,
12719263982416426023147660109982600470865952571498307583038113746436265077537852019003740915215932640741914900275388214999331760194882902198460149233520195299873982495479047283014269097776750147108781776162515656747862451843248746024422177486208629955958330488435286804869217543016263156078419207148423001518,
16369235042535461115927695196421479334333452000344797157323352683451832878000878568023176927284901297637734667852786602860800805709649637159660503089342980743800589108503669709865840527977320719487148504906058109104769071049739613622956440178261863556678481486669871625434994505069810221984312791297997213932,
11878195281680903619067699874909423716193151239014159742228638910062434461226372041043122260482504575388614278357829560720389851803050223172568936690707769359211559212370163172284582521321598474690151738348032842646100524495997275250872914336539806013425883428675658874543155443645523671412146133156652810604,
13094377664169628467606509591175438244105427548766197203483018055667637682602340908828369334361001076446361539316009667053503553901051390664772155069402337836301512380065158462208317524942571983212566469122076031025007732834023845314516897272670228406104884949117017369953414265440550548372669432112234580349,
12724735352840212187821565199587396126247974811949093987917483326245122900563576132129676184779545975181422606158734663374057462232983147276897333483824769922210882977493504307085743622549676927658464789548995706919341858939879356606002248889275163534914601924345916565775497692743839527158374738781460171154,
12905449339623847792113022162546995256821880366280780581533390222349773597978025816685285629497189434257005161927310168182570354997137701802882597201126057075569893254375542378286938780878167269475543199826351342233898992306309680087753617880870344943914841574195696235063071846469754960939283176442948061438,
14836907863378284035173029852714083424471819876764710898916273820669340676650898848307372165155846009815218327568625575832364455667020861737637491664017891928942083687939619527752037194322899043869405072944091941608340857634785285591753518255014887028180566640077809169512667322625385027226421274736579641671,
12724060576812198540544003057819302851871034985424899481361479239533229120058848938399061984030411639370733449231233599671302791454819971821293583800692520181156663152360282220661604409873060995466000406683132491313803881804277058796391261807901937925060230590125052988195782066884827418050955398910186193615,
11634474998895655994317736464863934969807480173048115004343527107294390669572613418721769430283402839000639576460965002253231097225774704997698552202920097832162588846577864009109801109882843995066317036687221935063737557405140788477073912069083379490014156244176457993957665076372851002556411057094510216453,
13092296492055109651363806712325137645444041908193505828794543329104749755012001194194082289624696194187326411474286131042947996902482131757828313331008600780884637178854470233233031042212043133038438985787765969136740984521783467606228558851818903825827138576798421951929316481562728099880083988453140085222,
11879224055985177160103410151821013722183811301537612792902243611197537826419912566268323976395178009566260191245542524947241059741194070934901416073910392967188988859529107400695308540087206687473118302488029881545262112291521774819532279992236326963253756570784348721853258396995198629463785588460094521752,
13091610789349377988807415651241139027868801970395146078564510521824813080646676303846306947647630009991191731120469553365302974169348683221409230979045342495214214464485533777570879326281183627124367903884371184689281942355408545506146948779200993006715630912656881360441080185408146458462053905174910224495,
17243924120062421208201810525815683557915081819854894600474071057708620010038776187812613089145944730037023522437909468815961249740279006355745837455420266874107002240285150032406465391911443124937072711711494642036732727727644563975559325006073236126553537109019544681443901806324472601117074048419819194184,
11792329449079825865274740761689468687931717626374205757982820265876522946371076977152200981584194095744065668675420633140117936014139507984111536476007704487224450636229441265023984428191320052424063115939371840303314070853852873201770710900318266108435922337467789620852053166593082941021729266430195894103,
11684907947527152727256263932916045484315956772774513843330739707307615591204888205910139819909160697369018338055690213135572745351613196505585184586579447264959203727283490407261820809255767019968782775399524857323319663981061109571093283156931032646908416732422095246180185114628357419168189737943005069312,
11338155017656866523106645749314031425757580759745522738245032182433483146567441157615605387224581939311411661536489529927370540233228151704343845264667394569590567870180873029118846036670152834658618341556149393251397526351341177278956192920389903905072911876417374805477193164810814799463081553067450226843,
14020532572844914161248453001660889187584648927507547773085093372610745377509882493841823717319579824359104659063325666960561826884103399811215001483889158421968902435409307972244993835218587704190835411997496117645519080941578948143507934747254891730962863498402115599296804306562763925198029805655530420680,
12165501628562506014474996619745079575561247940250871202926498541916501711205197967519578910374320089227337624639982837841994778742602818961398066317693328361755641269335723282690214468730888625044691423239665786121280213775948768500374961557506455530286965764223452543259769444044066471267227444927085555007,
11634405811395248910997456174254056185481096180794118893116216605333231087624870927593357241667396860453334430132599139124293368363664671973562270892336879281955974266703947634729677128926845727644625211362542673591651344891012249886397727223863143596946911052703469332901179694978907352292178989507642107627,
13090925264502077399169105731943983014814767387128507979853252294922340417549207174504859400613231551147752996674075377039132560529005657697956870539457831566500938880890128430691755453000205579896646228735960669943224384812117788136126611954264576779505166347396294761684012700273937919554211728219511372262,
17645098685597338019486183207941244763191249378927011009628802826892951055879636948088133128601876111287660046969000213939576441218286806510944109409137390694991036910243852243500900628758347725144291036498486329031251045545652503793113778083839932931025114097254945635504367938569835024767272367189050165073,
12081253111061221802134511785963177474095144452683261150722133819632962499770259739618956899181106030969029829557793813526758904031797762995441933492115126373351920411492136896993598491643782163984187541008735090575429969404906881866687859099647860824784807103607232950797518625454569897283345505896339605357,
14661671308472308617199754178275848175956469026571622728976313648704833240420337934710153014591656853336705081069547579667186019352288037676535432676672998751052512232520021949307082463536410666972687927886947660884653257116999129221655774803471839620199635448764940519298507262722960220201157557378978859329,
11285443888211818360512316825571818757243608401817559971059827960440433863490113840509789603725369571646424316549272999759486521731197128775930380128755853886777946862388399973992305639716492321558309974115517964368670660342023678992970356015079019326662752596482697136886341594354469110132452108273783145418,
11634366110865313203201953396068717636737078850285515355226098762278636313515961633018593399006083983202637600450486286002671412522622745825961826755558225605990560452637846665321768644889795369981230563466154816853252869012150279956645690447250385942160019004435252624633122784909764437343838970196842155733,
11613554755810471353920749877206742507663978374120377866592719988062888424000920479013839641436001925324738229755419257478839897183362329681835761891611902463825249228294439626996068736969645780793854705682161080138224253710371651944756783497016859997055397756540436383404180200132646234333525415234068822502,
17655395830609438352910270329881899946087971150106642209924322608908059309361753692262400889083707001656352984088980563299218912772993033261383020395437073316091496563630278871134425069235278405330226382887567660335843163044310827629252561141820270958839948078951901166356936973199030601625020473518443444170,
12908535243594273048275252003114288687663581223041660951789232302487323610320139784337463731201586072577257236045904024201684223057108088287505511630425467254353260469855218974538157896629933145122074552159347231397033368194901634974639191782630464448842756109799874453801594490751242148811276280751955085732,
17058427881911117863515079602337736244316553133298092362604152837246481163192505100853513278647582229163134992594374914427046185698978308592736806581646548492178759583528654329857966887725290432496507542137568657505734903799697958551183725350670074468729728543231389738558343519967114092245677604451322824881,
12903727799904124439570450197102569100947947741187848348579242806878513037946851412256963697411156119041231774579371435742730641955793632075918041077991405182366858024966390051855778615491053369069130559429110456163638429479038084005955692967828071520443756555792707203570453173858120669908754023298854256778,
14651489984507982287474198878957767087797433765873399898742613879929905171446015415205809895433618062133575230996071853355493807018892332757265947186039882915980198433421445957150017359665641946915060191255163084048655639319670468038724009932417786564221536601879228782777127695113029799592059163265634437093,
19383212978708535755170833834820704219496404717137265100662214985080242764244873553352790333442393812756253191582829480958381124464226774017006662604904184264194813290552047272404380946924383270689800532367930537037494853241380207392209734421562766489000613926424101926358973710981680850780787134970830692282,
14641438539061424489316661612547334913485833380639217682209392917290030820766912243332188876239758960524699333377724051917933508010971589455152392281203204283667986877957499628285153522140374340724253426955904601791659266090837415581400040227662633325187260686136307521479617898630864413524356849115087242839,
15258308376424387681928535986750283802651337858285542399175147424797161483476829042582017372495527193949445636279710000678172736549514424154135815628275601273569204203388395806078501558037832125475242341531878383813666445303175588590058798236317727743922064363531651513357371727618018786191769310018493972703,
11527907838117062919211901119429997756785863172656529830806917692078408293130265372078183503899133661384053603274655609544657228788541581770328733756146563832719604814459575183077427415667339156623075314124998491959804282616847705411359426298247606205002291020465602253774925773984807637792283178879437112476,
14826597545462144839645706554592966071652329301471339285089916339810377958547726240192395346929353557210507325442624351912330212965669421396636766279312302553316668298918320822324633083742390516077647923627516135876353524504150166913415433282434925773041507150162251343468543548090321390289723951665542761130,
16513581075598499677921210329185428936143310400613461028326036377156634355247798662338677812037038958501644808993675538209277903118290065221687653337623605768802782250442732472792366216349152469230086704058947479382109884667831281601972959324761224818453568296612963924144063796771623717412896481228082546342,
12535833198804796622682167941356135612524710689379674412731964248345055677020501505088719566587362683649439867533272351442760289474758823718105442155912186030463729706021110853828459478888755860179367148873248011492169051798780789701968999646479822741174151488921381075602469487075638137094826246061554927451,
11327862852322566092764363740890370730198528626541607632527310275386120202253668863105976561546564171513820397781863226129341164949523950758407347371610811355041670336271301290455065604536122391325840470963728593834472858798681476290537595496201806201102914440196561511245366496627916599066569845080685153998,
14020504423882956867232381383228770156120896342115949203222632798126414483036963335560369216481138577785349403815337479951313308551807243056398953195230953688484162591663311223219304261978566287346577035856401897437150114213177308157132440577939854742990037704983512487205334994873291412656900102149646815467,
12534766328908550355439502445854786028516388295702722023559106439979220584360115913110040855346686060758935149859760397208229322103371991354524096214049053031716428580110483069738064808912516377172428236384030304436150049199359210253855483127503074688302990826184235358720624282143830616388056518723870720839,
11503115493672597602249492609390773229514310616807226330957873677372432725832617681097893076874827116828451536560479074850066297752561217075436061170568603556170669662632357443382992687912964489869898341430349170577746240524132996376284484267597949796525290419546525640443147188180566782185671795246633549966,
11583718922891356284508944060474231482218298485302748718850265697994211620899544943236398010438322471828937130265915259833022526132409459064708236281651458056382983423400294486272291510090293977384779861727754968012362888789860257757605830047289308801498055929547660898139021215390884480015454297096488132527,
16348661709956653460458510526542390815795487055884064531790459317012470353668949140970706587925757432600348435787821431251510161235138861491644877448493847475670696045554178433284457908759328695130282980909324372904051374074688228652442031390277621250221267129816901612283843054867744770776553475526616331784,
16513253131486657734778811515908348626542152941331670852814565563525769315410439648261130389487711577870459371881593089010357391697848610266515892649210042954704108822955347742783353452582777238202228194300064432444430804518643270925786131579765366702022145866797890657467516443497222553302815123403268194609,
17686254943017358881737440863917976893135206065131579709023452995489815042663104657401646309856681955905360193463514790626413330671454585703770006058277028514671946053120194494640102359745054523635134609124363892366405668464084550193498398725249390386766201552844379494932029670201245465147808709004544344515,
12172178254928987001500098298267716814096818715438566891349591739598548752932314000471470236044724545297707606690722028541388198805571460933262266337323043260295083204689370701937097726330778504491345722953444740940991200615140861392908008121941691034954453017188939183547682893100002034052476973409280493974,
11317233466006168106434105825516227759341986296625113474272594764142611182929919480651990322395124619806528654073587378295974592043035191409905139472892731616284224212234132928767698531182190340586759998706245135994616695594038347655005448326086579981519851802840760007291490880495467285904765352569070520437,
11607073887160802237875428103407536555536770611767823411249225506552074881784954290138364772707266258652031760358869721449595833637730262845270388113431879054527900463440401585348543324426151497255131185049114237136873553523757697747309392555276843702919960334535515092283066138082675304492526231068358381797,
11249336977727009003548255467567709221485075726654407936800210896999279244325088749606830372078769010190187037471552608362207625313279252057642142050816255539670592954383819555007712614315010107614790441245182662129180810783432991941551123087853441102099211114152369242837205316962092808466025904964133602508,
11503458397355150542833620865461468941238644501559462439949538984483139616207360354899088638308746099701219886512126486697427734245752415377737717472789072487901925181438050333380519971693184632569283546356162548514982266415066165138714393686757955233557693930035400844187735724405337767927519016477980462253,
11680380342820111234033183988317982277163304389544834190529892130541673627455482832971202469322295262283064627588090686887039492164718908192096674137903647839297043462501911390137853760659339270492899732147332249383606536137654830682032266417273618319671427811280551617075701596523796132331656802772240375731,
11281225147164870318276925150733171282466547200211369993089017816448759613936463197004401521382115710066284168638638523966391814020736724409175704646764775821369678118202672278167847373038819325525820521957604264964555859727883703597271785707107211253627872396329433752725030509205877480289274274654287060179,
11421784418882663492951242165797307582849112366341880655804401620590881556177344525192434097736188352695853349278998245518807049950762368763318871561465831801601033837994027100965224234748050912910190550685746503504707078288484859150507991717649328750702955997409820199747811840795810798555892299764525633231,
11519606126266653982829839365652120407639769046090403746835410841432407933412608509085019692449059645773512404504807332915303505976434579292649161488590692022923270493213183301724060855306238608627553709302688175126140982415096199538487661381574633425867465185650711033797789089276766859970310031249559191552]

set_option maxRecDepth 6000 in
def c_S1_1 : List Nat := [
11873355348696633602590693355917000419861991189563851226537951874783695735822477723814859102013993049240535636377235922280491872105284166099294576695297803492579819520331397727258798828463138894027910472538221789357683507146212529583429393888156389469312020528849900473798445209767660855752802521768258317090,
11235587782230929531283853991902635433448991089444066805911742410784421465425964694507383994182077854168599211992243998176615051243781763092310995424966094107710972655275700647328534515398592661853266034815000428475780238659810289131515317752866176780676384033635224879398218647459515632390733672283695911694,
12904415436902597987445326425482454523503028387444481112335833053129369724842994737008010180027682443157492897303767370280098411007482454794374498597167612145270191912703210726259881612910090355262743883958348924396935764141870389817817565849701315822562788212733950668218627170007188560438030663384453678335,
11873023788444952918337364437918900843907001120087573267026950288741215726888251128574057442020422935575250107241380513661756317839852326728345658322035739116298998460976690567342033371512948190864555683190776638136575838074113776799069889240435996836299746398023297344030700989969927295039722688548219947160,
11414362164102382813567674092807889695389712490033955487215073775179713328386929603249865762085460648454424579878434097266526861460510026574051011721034413869645923148881437326888019893137187139854851439671526533908173178850519604419502164262056798999327640231420509702785672152084681423704051227127975676606,
11236462509110002549608933448506719720372859620232183525996856226070981346218405559275963388891736800331219423744463569158598850738767866860755133644905419936177161487658494630796851489434753193565940376284070764599224052815841923425326459347740673265378000175772297794136886203953513414047917537597749401939,
11591672090872459437498733995359621153903405107828941925514113342662650743695672665264214886442413031902204673825692031629722631142721449087767424219238660427412399239346352955567446468530729588448646251803019573131341113698067350905547786127673034885058195870659037617078234961303946735817048490431344411708,
11912860343586457539045231024666573123732822445976128848474836627718550142712073992951905814074801247216663998552813078069708349339859830829686262173147447332142988723471061890485814395461648050230517313153704447489557432630350017557638706942630704730083684471744845905599293246040148354531219163524048008623,
11958825132391664170132208257256227909151396750117221609286774294379995502409964569694051878595087179314542575425370943124151673583618093993053291060716046078176950956490114261946214396124220635829108428251120156639927398253228733949528398075589263220365033971366184209750998085876315570413703614407137632171,
15206875898033656835750197302318198870816099682470088359824158983155134933259219931121182321409481214404399580529820637772678424594121151442030268298234926602045990766039524696079300936005284643217880472629754839375842159475243009135263835007109200696701453568506050323202967813380553506416354380417909335786,
17552194042025008323963832284636551872009656228023784351171551441612320946115458378784921889490614758618500614998041018292122360729808548811864624817526316586402524004046699349255678841898062478914297534536350097105185002120890901416283636838354888736797328016646761638767046440638619317517182837330330616911,
11608341071571452744689275595673894982350001893189309693217681070317795997156600544542632064079533935514086071971596750580611115735030676539043300835204762865931516993313734435623186795049902238208751417084587492597588436391539384208982724709143648402919444274887162308952820072427197435185823550641740906999,
11421852419107096407285489584108078221436572840170604828577771379033425789482646467364528304657858000520165193963609713890509861588332487360785574572279058925510511564628792290716603953184185361328460154470579323974779771865690715764083295052504006472082963692988055794193217547793965897176080471064827672733,
11292679898853559697470273352018306623159230534929671510320051603615777945378697243195019670532005769924542074025966452474426391371731586696731257884380163188215477366481869644364298557472044128679367268529886011823886070215600176906699736749408041387168942621296996657847201549273891540558212394951639498752,
15052557385587152718789997351815154399799679755773217738285666587504683248021249030624866799953040668137796276465326387849116538536431422839631729263109353867492349824962391943070951932507521251517274248862421337571561563766742899439756591129581819146710567715760580119745508547667446447933518382901084294859,
17274783131846154410033481997031723766718059821860266774348475638712782907997948397223211851180284998950555381167905063238950634862634100499524096735935935925257498790035812062506508430848688558725897626448792846940467744018693964868418027413335041061790998403742815982928016451603175571095032330299239301575,
15206875894853719838552527194988018068071712810400280328609443029404827386618803763222349093386429168365893770221902737542741084705825409533621045883405528542009713423417321794744111251797090038921441725869836312049349502183548273126823103547138812756837182738832087491712812279421895409360745845293126550287,
14733676957213538099021290172878084514221430720979012545047611914318604024587310607252047124980472385226014876135489483057518438303595185468884076363465718535521190424583008747079327168873107544309581580340727205825719328771189149692995434985140478084575986299778988587670494929326952439011281063391038604371,
12181938612103179633756927125355733096867835531253075968848222355627258545787481831612440239369465353369486250567209057870368143141325377371536434813168352537768996666248626767283312223691864203582265845490552651874625915543851214526779955629682155605649046709615228243906863702313719331921687190865065279980,
11512373390818913241759214875276402208499127966121285309714820813038374345495464251777374890115148490398878027157053586594904262456278990027655526904565016864953652166125049792028199184324765520585160316791118460987231514088926225723285263435984616427205808457615432651666567987522715852783333646374793319725,
11881734263728299211091578926566194992273920361112583113954347688612575655180234157148585347204235217393355974991872195923474612657743422240018860900836264706063160529163196325377664562030819417617690669435086683292740878190560477320186441395653564095230761155824685941463024939024494282863619015481751936943,
11607109359365415782158942454983258224391828123225208627799397108866693730439071183116393895958575656110996211691356683239307739982931537242048593741178878170320274121929771747754118875912490195002294131734721847263077628501902617719550294163098586412511769847123737158255900086110912656382211747915720899586,
11335069040706973321158299625139876405999843029696601550111288364768437144744010173404753604748194796941121988984243310532316511978329517219546850456172982610389519107974305100651059545072084450447738475659582711538702750446023866827752392633320582188445933703710863297796209479873642127542460708845369309220,
19198377023243508975231090815489410793144980913349419246644654561107567846187588011597492895915506319211687960019119793538110573568509563749992923480530406810960284791719006228102983687297901954319669371306676706816671670928197904707089090914085388362576615769211764398196753273141148817938698506293147996939,
15094046290685867299034804086212161984313744876821619978425700184454516127289564939194590386974896413278019804215263132997743057492847688188857279215215279650051726584201530434335088326868861531761037340322476174645470907233428825219035100361447167863014792698236034135699418285770261613494249168520377828610,
11589238333409295382921586628355871607323406775162915439277254255027741364619753503817338297728088404236886375911205400885026833453864595987620928083322454151208008466564076092874232847248881743759825134963600768405731046043535405534575854601335486727965389418742496484344029241363746561595086688694609772749,
12077213230853369019233980317100974354027919785662904634978321880241512260013234721065283486519462327679369664426368319667096189222738392608134488612842579442300633658120743451089808912751052354547533852593189539884082291286537151007732646878884482412799302492466197144877911808675554786162336438844295063845,
12908613490430907671613530923295836932934163770727844118013322984792791454169288591525257833236966442166602341051141103917701365387054295729099390597090638256689801766393966976078820330712510480967330366710047276650004309492414945238635079024558580712823838721255016058415880285490673179652184728457692818961,
15947487746481817855313318613112531591286678747707768849459485783062401017456606796228232521363297613415697479298904981957914668032998045860814431287980373726048892529469033765904246943479170832159012659531958285194105359281045049301281242607471656843959908029154557072540409561344741594156543205787794113597,
11237325463604852398966529270080236029636364546601772560598140436323129809260604152954091788599467207256994024414367412830013738430102789860674493315125149433629592780714364936367044640211604430108408107802189550151519596476929178216940634557345637882278412787419720840690642008814788185390537263917394463291,
16533825971180412438982540670755821383398910573528963128111979538165190032804001897855755881731779386257046545096404749066236634257585555587435842542199724637762906347903966511612307097144490565698223980899360232724697548401373692999432657631757747236672515959372173598823520765657462378982432386615393452032,
16390150575412852165008860953351926332285499771842098856719201633671256674265983892545331529033743052876278562726537518944213336199478444639134123242507127007745841199259387228673634893370074715593871690938905556232132081269086369780713120710093950936502957075243665261304130776212155136172302699536644800934,
14016026784038529095618191354678304394606730598517331038216524142870460030595732629506973995736167955699149920281522608701761404456339025013619429343876323454796376969333318415787229953002030531012474641163546894061702599263182017670261609869135084277568574697742260831036205135681987652739878366580470482047,
11380335235778571229010800633649012796303820918811032386078968239310367693001649341152521568332658324244041762791055317982122200445522838887857365939447678415434069472886237016671589828483972232461618495831118881419153922845358360263209491084670480312583103797296262571412611958403933100161365699104193216845,
11470193161479242399452111168846981618909930498077055551326053456514899361312487511534342178208070913271879703380556990529418133109651230432463853626413773051539874989701837207092694817790274966823355674873560491861780391526629976766344855842099411320943072668560051199515772397225969723540397990657078170919,
11352316081196353222460380430314896290294590412402682777208289017966048289746175411154838248855861076016051097585704764446664551988263698731084661979991788352191171565313624052628112196007955357888696643673056183755481125961209972562845956035482411194583399425382239398330800319165670458984963994519306968473,
16318136869706971636102855649358386912859650893088542977594072459631602445720268873964684233001766821424140097374556874931770000070581953520702190085944664595272371824676217183746972470622395031568900505427793152606396219894380153123631507575920670963079066153399674561716008532380097728084201240065029122191,
12906453272034550932608578722746351916357356171991709787299706536211391895694287486088563392483973304264762672994866046042881603271518355815655753796308423720587192251050083461857355220930182057250597782132907592159664847954648700126454796047621940746323878584920498562265756491986742157282056975036628173907,
11792443128411748119488857745763722540391575402985794186662410695761701297737829476778398988172692717467366739620076296178370373504594741765605592929154858399505523442489861192296156717615398445179889641741076131964780444875843307774695306159436695937710188170807265865445030761014914940449513059171963404608,
12724060574477841912633333598600621230351640574085527712693249863471482635188633057553420599996074623102419681723379736249035977849546028603637783857553937909304652634159798924132019902278442765175649452090825256085781462322954574621661536606616644017921457519367122866567146020921896311417391527855445574081,
16554399253533998439476653416467626526442787866134427439999986348333910894750580855594888163075452848307033828012531901334983835291650262294332416920113960939298621422010940608256100578434215212748925315485318365623272938790864736805244663280594230683280540221625222776898426240638856417918496006773644428550,
14723757045918641022860824719745841220157399747081408989245642904110211705572947412461899056548936411844555499372887943909162049158644072691900082988422863108185346672101641026817889203371886995850755244726640672791830180171569275178697069900874067838234588797084589677920277740603877571001913114458496403746,
15022047895953942983803346980420736375731566390242601014745327499096539629971677007576787634283064176681227972723153097223975843674222224322432634325236139077173608225163115230921294222344164616731015503898657593576734058612605355141160468255403558557158426755072722407515572336925922028896849145635775514731,
11348887881489154937359980158621900321373454693307287725122454739492760586087791170791360763863320817716195487034992647506311685235432454292010875964580209676708106767995580642796491604727865661026790582177660987115471416537930167426254104523690417142050133345054492574487688860139109364420948896170757292860,
11354032681930182356518332737564356834270416221761350291497849118577909344858312565037264857351982395533985592852979884307965436190802340463828620873049017040715257018255342720160085835980285532025359580882851841346350494249257853963570849984530408339118493461542114105239920123569995121457345294589640550063,
12186858802156917842574600858396302161153954261338943863163495591495822152807591785805073858786610518844729298131468873144641248666156178016598708874900061963780931617418402727729002020265430337905556108745297886603189095429796363489637915500618178271713584246919976999098133346601459247811399179182918444808,
11591261401743881643217394338045495068036624193574165122327130085976872511669022086197864335394380251931729587093549175174473386564399534811472037138966436163581819593042845852458303974853684566216033401317384538449144168680465068437974243316270595040054270179354784448055666661849480518985355776932505883406,
11374849048921599405710267338375098324369290651448063461353313711462159229270765950072597332944607058660084668460991824388064502354751307387536373427929944582263296580768351025073196452262418815795522277121900202475584403721115451917504286628916680442962787558873775889554578683238682598163227423992475468374,
11933742456079262135578253153904012060986545895610118087896985333023197671821905903427729776444330424321589381147031516087556161574387950935096893035830225747319425140254954759469625141904765990555995485106423388419880182759587100751785234688940785199479826317647061293674282199218677574981317127938648347931,
11635504578671838724170604944184946767403033406368690138956693389699443832703639224676183471681193774630507903115899698296328703780274931711872963017430166955195208566017182180758510511829245405646968720593257189577570844643298011105613114198454278769368245691281998868306360460049096516520924160990414410510,
11383142568050065071251073564448423208764790656120260125407445728893801155174638599872621103329191740381768539590688447787417370244150429937794219974051325843729630963689067122965370801426328034344753105030282994262872200548790009132780911486871131805019721763663332579666001269460299087203218950949563402980,
12075718496875953308724892636792078586235843884816490019417624278432397874093364198931649247664514500427775480713265940248208498382860815029078284633215028256398052892833425461919036259095480804009719816118273562633428205790583647393145508330843331153650409894695355199900058775082016057425130615026454566185,
14631154605565016518264116937587896269815498698858414117314472738895571243188700508940093916786420637760806475986756599944980913462361843388626050176030433766794538094036053137161661410830298411826023027730115854337476840080273496752467589327118519116245294943933447533050278792311317898166666961973529908522,
14682243968541699051639042092974077695039083652192390733346167548859329135109796359096852182052287474662323977818546815675706827947917841518545572963434428694532272377472413771211175402443645625638094783948291969358711103391833795678230361225830647457069130983559342450182248460030963271161543309152822199980,
14610581724009070314436099488221370170587443457075624080913301509234295466372453664348189676075778632577172708686404876451954021810509988945055674808692787623367388278187676429543564269659333430602456634937859894419843930876687687959485965080866311001491300189409119759491128214636015453502660647950677246430,
16431304219154184324740171650664803096800409230921328404129943933280845801151899101459304412110173402647625688055123098185429807315884402251596068837163564388468373225206755368063526999545671704250431388682803845661052561832647570606898125399815820504177428558363421046339042269727966676312022257092114219493,
12192607634027747129170176404559881210223045085720250717021882610922362935983660099433853318601887880750782723850362757318099733365162070924787858018017319374456666494351392641855637827368977138190495363178837180135790878807186323190787313742221960895368995944499673654035230016986730074003156167032263640936,
11879711184509551487531375120044390793781935419487653168827229784808643411810928477013494967403818375862504782257882266724709673699964899135749873829501762327932957742605399434833011383756448151822109265450859203443909323315642510695216746135393346982792536748716067949333555825433132943164471719090828224774,
16502966683439368981537920633262567286772641491955701243223426051342036651537608068483414862774143340514447241873108435758018922779221325415770640431293819242635682445900240314845036073068438005228526153140587426317228318892598781586513721545697400160954365039891073220852321793134838546674563436624875600779,
14980898910098352397624325909085857034720902755915157075034779142405532409574422047391133169178339451419946190364842184770161383746120260187064728638841703306072484077165151928809391937871485277120422791007364752802296824936426679172081146134574115607575573300613404446734223632740193680043009940184577769891,
11879369881623164536106256696096823735955300239444121620718173505872108770188986567627055103839286919303721893256387938867323821799232501115414366669158669626006605806502940941909242187199333209842033531523339579727761791526090634012663689234921763496061642878563479736372483196901085300384847895801201525831,
11610161714977250202662838971249187966658843990303682956513959525695727014260314298529695441071859706191305570205328785824367411705094081709100647084319671193151016027316004341139987900532039179180999973847460839651052687650297408846600023863743607430856671069720604849812235070051379836532006127903953995887,
15186289268081601752656476692551395505856026017561971201163536209482355721513556061250271898928533243980832848121483762353319372626233573236667761183553150725319217120062032372753934659955624481454899646674435843698750372856845652108617661732115556398707875670758840820380049498072547879224209040444000024463,
12087691182674944841999896503841451956983055583192806916925679824141136629376444937755037254576242514356340971991611964395032147056277727079413006326037649886251385924487890537328046918143541277221663916951346620133786864894647267437791329249563073893910036298220935148737903595252418780227762144321107854470,
13088867766001696934116586401336263328619534182800948672950610740099284043495199561124642155605069203286198878346091465905663198985508503211284991312674160918996991370361870673956773243527966897122349697024421913823166410001067372728137001140702585636332678902196686006381317035271738562565483029834921030426,
12721295266079910899738099117727315904749478841743450353387260223497305328152155109939253939956445890740445463915903389968932138658177775872935207619844190688098436911041491683072346697323941105979155828921599496848751670011074343212454707930339249513738657498895303659793201041697046938276475238825379759979,
12720264496776857046913805461523307162471037280339963920808508509710311115422375870752470322016709260170224017121187956322055141175845059029035585473092281192270063827906562692314415339023387025494301669070937862266803996988832636827981033594055505150985868240421414176512392185058589095649860227333805801683,
16502966684474012607728189304716911936668554433937479392920600407108228974823088548631175237044974848866837496364484420204487346229359164809107628609061202251635274446986347594794766286213817279979848221654811589856923423507526210594745912305697915347830668409871836821107530608629353146585096018504986199111,
11236953627154969675412676806647972995401189543217672603598593785373676269377723328455751449801397650341060453511674360559537201632854875592663771160806330054656245171005712595268161711536707291042080909193521964748832720502720490157233648008345505346827097971920290410701396001505625730152037673058470004573,
16431304220226834491359384774347433091594630693650694584631583961468390208612053260620787344683459325483528106990321377711188478084816153760627808321201695828305305872987344360299863423209821966828493790651470024783495498938155172002652353431894209670542510334683252179626371439344877057554138034730815883392,
12185378665223177386379234436147738462026501452816684880160447270803969755570928986674998906042301688883257780028533451055916313777066751772792741914227843236730856748819666176932602193531869522331353897938444690058821274610815206364149173201975155271237478444363061151118754828319959430041072428433985734504,
11356381075489793541026140340945779011840135984022998741421215753431720279780400607259134482773701161796314334935557838785954089151708925419614504326502445490554017474445998759790574605613822752131947002637605225824028662579978270558771750107057780469781138563057989226943066011342179972587656819940058210234,
11627994757404089421490120209380315105753397166108662988317122647901092131658230369570481471389499446438834393296086446275681731371959150274669070941486562933625075982007088529165420408358770809879835114885709877066750424375769528113565754151817828836371047960451893800495319573643069875331396848677588285927,
12538892857286384656878086642303259162467364500507723924635245247547553280127812720062460798799254292620044838436033867883741010516425904649326009930011187632552167730697606451124049172819599479628897200771501043131658343023381188911162050096059077190316552442734712608447203897014392427282147959132555036273,
17398225768490828825055044532279912964389995368095936288047682257482475116622594357679762231417307325263295805985218435869599013401694803968038130418166808920079308006113391376047277827431006956131806906319514396961349889462532618247930926910742022631543748424916442908552156249564685844532241922878604806881,
13828811783983795462759977856789429153542666205878235667958626267104838341381292844352944472234062335914688124549989517163561127197439606759118000103526848138823604445843792440762463926854441157645783109435679555755324780640108622049245965161042411274934891704756042144191455701274847708273859739327016502020,
17233294180548681347784223069858602718198266873669170615858903791316035523369118337612496557269114661203046343583224827421428286047720152606804526181430017891924164830456521594832310885150382647575105480527974738629642230835869081819422486509443119523647493005523885263646187997559229230899414310273283490503,
11611874245720900402694843756463396771852198027628525604511418583445800957127651496814160795652296713216008523419299980768499352985577946390299878176981506571911798375768455875515361351908528898831310032388818153031667016308344438169535665261425112994750455549949089274879514626408726050530872981448340210355,
11513847761673806634824442312720893128533534931241230803892407874368149646419284522124662116487594898952220184121749818544476415528425507512709156194491900948587993551967162494932218321209151228382172060891213329271393118352333019917214510621531841218290281116738753173026008636512341904015323939953362709313,
12077896171096593620934216636484332207657001711138496800065810919546287169587406188362803302106526048600652935687217717100232929557257447322462573643174819437493137413973061194951106355574700098215426150983483363851638110467626038044779734083208630415024194243997441003887082799148510585278817375952542313131,
11307693911418770818119733680247777940213252671244503852187788705576898226557861295228111939972450028470920371871633537379920714677984731864659824744405414662088030308192196999348200339378791974718857069001136044193827084828767381357804034121950379423628123647902486307981215967159039426000000430162130873603,
11509050856214974961093366394949152311060082002088594121372174706032621954148371835677799173174511083909773335603825721148054724929197211869148212814783606363029101353141537116620808657363758746377724579777867599229055211046637006363776008652552415471301543237078532656569701744803039292709339079581600528540,
12199161928868115440743523267336432859899106971325476718888694406778320545782386046925490936611180547917746063793223448778682666375980485677167042176853488318124371335373244519174509644601649284255542527932271471091032102663585857446367542765335873749455886574063463978869629707692463811856318592396431174645,
19383518562471692550039439754790322690945309247543444287798249826095561260484455405502828577706308677454410335152225260813130682307858705540782958496214704461187440896627695772051798500683891608284727745848088367471404479036575142808428109990040833465598288130757088704929609064762245333494355096693740316395,
17686254964395528835589323428375117477098330127821788033628240863951916947215458991105244744554611843191956306774797515028433663498786148666290777226314883979353798092452231526681730157494218022329880131016021092966924616952376830164488126631175684780661789282404001012246128776981832183570506147154987287813,
15227791800799350748967069316271363951313802774535587184226139738386149425443219883443392694207004755125109858469130660328087817657451604044376563425607943396801258094739168532737732612797458922787842197919902157084929181356135415405379975833398421042379467995661950365898951300848278848918330594960991619478,
16338718455383101877835369759169347331468087553165575553873270938975654998957048144083176108829585570839975231611862628113144923363476721123374340350482063673491939824724695860385578768659664553409962199760002366671398047391327063976279048256921006296789306542932785325678174408000635020725232157646804845723,
14816310162952508871232681314788765412270250921581090531151393125525971196870400256991508753268876545491785846379480135911581462049896548424053244456199106433663674904483278824005359599039385595425715071447880462213569760023608111323232452341847522205294211935877199217036549256551202635385089414887481247573,
16204993216186481966182297815552082807435803471102215276972807267719686053448452032209588685173960536675710343550508065493744098708427821811565856946637756669525911977846652910599961189361401536136395684340377895443824494809151096096939755702445511550068933443816437479616192089579135580238172453274722075005,
16307858641229103679950193212467408465539991006907337563002368015364972857921382182350000091411385629675660974831837681884277007496477622363804018275623513898143382925705545982893354406482258087148981060877755813884332212128239067304022149703270443298161031507608809549042016288723844511761282782807318858281,
12719238273009338272215264164150530842030274232834426822562569125064399139351139790339801503098207047429099190119263751814631812230926473848800921197674350666832439901593227263633167573489141321814705497710002446848780415122248875006600647307447746247322327689894742122829704665629057953683743951537603772718,
11632794488125841445434606904639596494120130545755250063687087586575952165932183839355096000062736630403399958238781266733633578317677335435853327083958628151815777753702984793321105261253074019605688172499950799219399020740891623089352551427602961003575720646182913766609190059953191057699207352127920507639,
11882453629169162022246716541660199011578475624729869882981272727706097171388778684146536888936137340008672933380511007860994439149611167170800842140740115498096882037972606997607309368187898559425413156500744876073256097629186743646966806659955034376044008600248617190673878067670671300794250335094853843311,
14205299145550314856635659360678744798713599462131820580645337296065629037181005369336971866106669297291400747993625165633008437296233268134307110584419365541664128512855241702872323988566387842572322489513151209224966932606774831568084113204209841119204155278250358245358145563643424365897028179810612526082,
14888323127806304057348255573557746427740297459706910630554385050520558648581269394289144373702196019131576046106918242356921013881368649898745131842544547319353537731418689926847086554389020256381824328031867752052959969412118172754419191642738252917876137012397596794423793939606168611369706084704072960412,
19383518557649423274840346882143693403163308672320148287160256294101105590368977927444098457084827302947278660289156744548260901437012524546901561839962902129278108330245154240888179818672436642313477977536862444453415212813237124045968258314066303846699686394314996673681182195162061194820698325352524251502,
13649140070558354182502133923426415855664019337589195665810075597398937491557698614576517034001383087893908616059234876306483545928607696032447196976021414679195086289679659197427933294174049239932498054045500441061923987666636683289803439724564296105055568155682952360905914395688696329112436322493480733429,
11676917622431416070261145081633291765444001923174387649193292014358194322732257493880311093488408556056806352888123941927879344061560509458941730062651525094415775454615367707322733727199337302697353913772272762974141306304816335850137462054524671540951534360306851646155520525038579436209069249691040515766,
12112755506498116586177603868488852102423069851057265192672060307785447202963210297887375941433416741926193268991322850466181752960377222770085770008548104398201983681423307888605203878017108394535838912137511018978420606820098763167102456146533931140491849399758079140319057357472987676332028147996211486111,
11613897314096139034878177376690444998878530360180606460785289473888385481219748847508408110726875246438814445951803384500985122830206833448110283809481121020909590277727570102803500515203697239913066873448682711486548578973602763555577315400951647013374451814078111656541584777725629894235003873363857544495,
11358145077291948469654193945183816756716078196930731965529741805646667911385458228649083351370081209099287216303859594932898737843468745206506589267589561185962887814508347191408393361948808300884810503183362281930427695930934761412076763069042154862504045166323215911613093536484247924963912860317673538674,
12036804862221120983091386254180647264887687598100923378012688103562034466297691046714473746651504857576118145824254268521054902861120353937384847282501024229538297209777627888955536046398282850137513442245695597869838119839093880475401602097736224746529165292888046331578574058914089331295329191015306967316,
12538892857286384656878086638120607300026491381779816941953170893583689706557703699343181992286820437656244850956705684397461731711060686166489910507097297816099784196809931260880748140314044200865595824426751445926665662949141711379626725495575593965705009290792433099091185457836274014669074923550351364341,
13832926336212300027493143864550951841969214785415562159121772476556932279906197410361831206298028246124153133007184872677859033462654185280177197183984499175788073175536818693699202878768368967815477392250918380113703405016722108191242798018736471427052711702825606128575921436641564166769143295108251323142,
11390383276816835020960129600997238737325025834054621734216197753168063534431156391894720805342190987090692818105306094106715137330013327071202243961446006241885610687745170054257774978466048125944948306692502859576241177046009962426004460767575362336730404907084452955485084862922290609432466435345698949896,
11873023788486125982812680065434017356854149746370941273822854626845783051052985291136336247264261950085723458830352505229707074075173445726592139559099175145799985512648384756147570325556654499978704973227580986069001610614652701152895392394116317346777861907238986204954019785172377093321853068849298543909,
11308318577168825135736392663012935159532934553710206087182826698648563309990761151880660765875118822878744645328797453276275081344620256598434356869145624983085460918332830708763550757758126891400346909139211613742956259868495169441520796163928576715762357979995017463201577530545888606087073265000645036146,
12077895846897498088422901354133798670493614247683638237661141136891119713939797574415063435383176321809880203233373833543360022139518131587976688599276757519633555712603637089691778362380615044531996500972924824006782493533954519924091394297174389361321685872057205997402585757187568759543875528592437186801,
14682243968541699051639042089471698486031962020565809568749005280866099176133828525935719081392399993405583862082779785838604506843407414617658118771003986130869941147821437787967037565840548787335596235734253526657634947295143200392043306817519659850651965416272187525907179801744723689398654483039748311150,
14980558997870053013698398569690932682971263110236545609833525782019598681028600210577864986901976759463788374148807292299798948449582982989319148007292102612335217694007298362574198540058073822518617264870567476488318969542350827719689894904601227816846171935841781331463272505015911049543241481539097790306,
14651384958689650319708609836452694439088322083839776606909267329358567470722678680647191020145745604364543809012053842919946390500611363208325629856287225053849797315466590665368373353265491970500814769106701188898952316249788626537814202426570767166918491847318377118397914955904754641522523839967846204502,
16462163583300798967479275062347754640460048410416013094769147976846412530808398141393406283024461565549196001473368817320084357135828325460492549852588079891100976469186375114035766809128333215983485439827143545567057433476629993680611379907714818551526555517855067303722572546210337568266944249234875910926,
12127819640157236418316292974656934752744950993044634824787203864712160852577356949928396673860189795198260420328755002324492649850725666421599803793090738202680401461205134044530080852675080325366839309780510294914831037307435664326371968988328713142630102649158865902539379748522558539137949995619542796113,
11879915471579678006075734297800911804707659295380208981139191601002688375581232837059453598666454639820383698313465717199948194939092038718385997400544677449919519248771477971224577063726008883278123926313963692818913177107083962639087380063622021348688678420939831462416435241281003504420564894025497842987,
11439979925184721348436251504765939579286371759379460795041315071880597319183531577507339134021271826177072279188837041276572809694584792083603909015702795541863511396726491842843897052276390847499687807212073300159930814225908710070279893153867079606652287878040915382775416550533357009358814313639369882507,
11878195323534473285113733101331817452142977344937165020974792737876759274981998924080471421928184349904797722183795819956361807049233930123641869686190857146927465476707189931108551665189247089072867726724040137863125094339185539576878504924536210873594050958679560056735096860239580720506330955643102075769,
11888550178300872140258617287626390499152334573155273081290985305282926055410121161845875272639222183662244817845154067521129473489946891907006687043186815468842511232014219421211449719682760819878301854236150176199867742612266618617503450175673367693529443398883087131176121467966225059455340231094650489213,
19383518562471678507042013205248791851051262654217296206024292623855998921958520677107668258559018341891673098264401213715341728448511693515747412067118273645037147438286028678459064256213444006153122627795669097771288065677237223838109601448563787557663196442367989488695068018419694319588686473239492446499,
14016039710206870979606439884229914170073926312572741203925740510777232004612464208843015015569593066146833701301382050304206190228361385357779579069579264045178794501603074213444182658954590008861445583069238316628099687658583527536343074383459818321954991552473777769795112621864830316878145354304048039933,
16472449905842963805435083967532742628863260419573257440229235997394519324547540044009225905250961619317546563860057586554927927911703293876454092531726393632732850096945140751740074371391531782291202801752431880579016885529429858509955348174821655648488020896311582019625740025130774889717329084885902133243,
11997209480238899072661091843159571685393669762317350494754066838419917802960365605368811121137181034723226419722438836400350269945845715060912090994001597838331350158923200135609038316666339206790720257387467306122568924621611366137129131217999936053125798431779313082767837278874798605918641763894944498071,
11874772188404685611925464105361731363710140183652168682810619683726862893733132587223221941099326604185514484360450210467012440525815386164194333835184681991514709869755647623905974937640332514928530523445977483041749262828260445737057572141274569986447522664668274299865729133231861475287518968972691837713,
11497363961853911696571971471478772005939545353157580510458039010416071334702351819194499971127627483595564216102053203182211407839395687620448460785934025127591625450586775485851182086377564636863739611683787099839412200195969778756675611853723711324476373375652302024619909309554182374227183330615936990121,
11375534793501976759257901185896895993216444242430571481000352646882388026505884358952480926693057705681286429249901334943962382219629265810865676709085967990962889184728864397513438952358366776001404295418103713070564218125160289135423114800696681917635720480147923038771525934659083374270142149904735021139,
13088867643584211111832389396660219365618504145072550842683939314458573606339762534316219179849740769666537780083263407246435957083546433463867216876426929845768978526085269630628657648909037011570193441274263161730724604084810866295646490631978576362848098741203167813161476916026301556565940802409053132065,
16462163580173885283027816483984463763756982390744223118077176800299179995508145926909056863644892114237418164447329158691331610595744634843130551961806771688514443366674521595090434680055640853445515294118397846014970477083777510048474288479811505939230450921950845113286262272181879878682836524581436359062,
11379067528547406933207678216069570777760490623437637170963572392974917448184834150892186388934194856280598040880834826585431885157212538643354516364020457613563212624907806153248561149300306446261444964482194364933485793907384188796604781769290721295724606876213331678504790085736746005005659766075457241531,
11617048878412738979521152706891805246630025851554284268627046775391364830783831935156892536918973352533839751144402301615448532652435203446886022939779205041415428785685633630947557085695124812270796310893798072986496051556934660276072132056573794814450618791142462874878027704708585214761021229237509827333,
11877310701772955155823652187318713122467056668583545216988586437102880866374233240223702695408507431671157806976831037949417181368162095716578753758440366998141073232604424965660262013699519798561717497918441037239619374790594020253444072486077664668932455671583908609787145914297588009475518965351755164691,
11682706887325720314846772975274732832749573230043237599996117702383611936842210374169790102175316488405444186251556740991390915947374559033076097035613310013922830522380533027079066793659347620920681008945020724302687130779515493225137709475639176092135263404762340971629911916309338625333364491871964740700,
11620038628604480814643326556982524030250684216201094127867040843300890195538863169258119370977266053339306208010806321478711755563590197332883317628662385944764569757046604330828141845372590811759498945241451720951729669596098578555842223416735101002914222934196331595092561512891755036689309238077575191223,
11275880841228787698201037992513551983176311440053978427328521679837715551407269164520901529334943416028148351274204522462190945833917553192245623661581487217096685654070162303763921970606240817894570289448698828008764080045927321832706574738787181936938274611463988559870812689734460970320648340174974397369,
15278872517764509178995040202914970549186682155006592306815912459730146446331046957434222736440210627587316416214349361084959015604615639337004048969351597157309624825583804731664970289445653187544032645111086461953267436041492096846449642767580314748373370727881464073516218360241481177851153514021661642449,
11878254267772121526264220203842780470149614072637675328943342972301842023333659749665949254416892591051827808837802203365675375090736807179295817608035721296254901161893525500514469680857664952350514716644986782054573505939930263088744216715538030994989563767428761343531985235234768433479274563904000135950,
13094379249912982615264829766902461051636110848203731558937984543965593545935314671464999291041700589996138997708071656153106744376715564874228305339498906044123317483068353168141706966393567441234715235965188358338606012188686652470416169692886777911053611785511837435102427682166211970047334715341318867325,
13088867640434281912533306098237591000726551318043893406878556850405218751743026895224517414809571385058307568435692956168212595327932396068926992194993617131858203669576908946234881640489752931397287394090778649317657017403604544324639098008430437980893995441378088364254729313742251840843713010338041005329,
12904396111538203568847672971544561371667769049275126309841837385812078702339311457614267633421878418824383257068083985902402381058033515465529421031047276308990877360722956023957017222576084435613345912609083848557368749860166114812766603943963248438951715969274015124760960932830334268880523897172292108694,
12213944342447012894761747936815510649457150878280770436962856732750153384882969286176043672948434467291511248613349964236631244033096173793478293059484821513962737626830727170714566891951656247200019697417385417215909434839187323390216457830801448797545870930938046077669486257123200254272461419392171475768,
11676574739677305757373103249840365622021923864060427500190239348138481802136281623451250103681052864381169124180595451980945256306791075312571993153149009325442628438986282445873113467903473624244315056913369218220055514092305264559031098547982598510698579562251951123749922171172588469953819434093193728240,
11421835371082717414306206049731818380580999338079858883989216948307774049118897940066720308511325620261760353214047185594715672247465434431379502038909189551499800881462702097608864950270400880769878538272904509004009353949876767487204453773437346086521865889353987672083874838399755631099173288732538147063,
16575314830585565171990773439245820385329130290244646421744897381897879180189508821269681492685240719096038868140249671307214177762575801689806433856492133528518377642093378273922008906124753373561867875549949892903119227808015351274263666065051108055231315392877227275793056388231262216086676032993726437727,
11385924869717635513924496675804314713900009799804874668645777118895459603834548122452718906249016884134268105921599950335480460187524330171886258121567650654930872110625105564778415081346423780116786499084523242025385629829313376859184863849944651192139549114896016029244614892443440984335576245056806028568,
11386212502365327868263221006521100253966274433878877768375215904736268175637280468211439589493434078387364758417606211580834442364184175861402533634420947926964187590285682430249433751660216327295745669543344981347283327019825243582771358555017471995272061309661093681751625920122028370912015459333205366051,
11350947992550904939965112957639981515937473734625307417887097677170640645141899047034669421582003668135294687942186523244390406997155356560381545599150651895394471791111982188356662794898181714064882568140726605902314794752132813277185445577966018677728473090345132138445032136072588067778272026651003889327,
12908186823335696989646617994055815842184023413078201236937488222539096851163043806241095497622606523230416344949798072749033319531739004040890366730732583423158466623098326614570468898320690902150410636456673965547707103377242489581140560794275617390778658724068014379114878561949491431336408860832000293230,
15196932214581810879085551817399993265849775982962794929259612162528655977850625000239790934494811739112116966692235994069118163548244365317459190540292077911584063100291057847023589214441909413556466352652621673295607641273547208250123705873695955805624246703193893359115334286548539528661919993983227927965,
16348661709956653462144469839061815257226659513433921189380722857236325668955695458728662968231794408211585504920933424246434834803189047148113901364653249030445916980458098018276484645317846442847992232636838363530049654933797992904070890205630690522963903667823698720675855215622793963344541905606006049174,
16132645125660194742358675651762060311736397732979442048436791844650507474261639040121384321119052444571271731012212556079619692668947114561447262041927840814704199252124324930465785959961120366141274281992640401489332862902758156894243664200352645963685208202578077351082033110513032619075571427697922933049,
11675057905903380744158030864625814856880764818707329238663501417513741505925130916532559030718424287135114025668014146611955592823196437668598565986436908275036237759322877031876667617919542617888879584821996794157804579931687178754476341554528429040310335214970688696106654305409764583152197668076959630424,
11976914060861967548616212725647446775054880057763830785566430214369082136972349508916258908708514156290003310204644812980231234152812195087314527092179145975798537325002418176676826116580728942784507266223344585483046929929825776660056659768290628475011372170808766165837252397583961120003977662657019806243,
14020499108956052073658563050368741803610147333325801567559253232303912119637043568234577421815923757201897199420609138841568102778009435997139622882685861257192657007710232711074005659501269725267652255833424476016741160310892137243449719146276456226358754696270061871307399438459416088946950503720159610717,
15083417607634055348927580022507260902072773963681492828624344271247221584940935278671209586582005687100581894619044930235522489339427908447309040895087652633169298330358580170293228378825141736072694666954307353618869312595223165300636165296161415342195867183298190515380534711876620490634830607931515864900,
11613556314886525581036478609594965906585696701410765783144456050635749612902127212822196901325520700331241921834247717404022291850726726884528372325502188468786690811280827004002109314121090415395715416257972543111292288146782110348704153386754976202020920326834282188488054833640061566474914856821193738392,
12078925750652749652561825646604376031347806527665811612030259609410481664321840207051551512747411006300816847495289343036616925189386948800325715904187608238440627393363722783870739610231036160484493097841487609561677928058205405650817558132961019142821876418191190829278349545347270715355742981653366781898,
12082012009546319634803509726341413625728498415293236244602137650202444709227566628001348288298137286319790122074268082668759613992491081788186418403286316553961390007271550333472594999678775337472002719110351087549623583947413342664170502968004574550541887149755378439290869598218657686648914814498401529180,
11597132159568286400761058954059321697014279580853095513706196521639455711539501449019587553439171804575661722468224026759667042762674338838770422060110205137666118452516882047878784454411691013620953878148383300888514132846500440853642855050861095166948072960109338782257729507683039417856962170572320033058,
11235705495050197840017617201380583472075428330230346463574289600193603146543418012936137862045946037774724428821829872695633037501037096614684264933333832124118198246122992448831793260295922285897068447843491584657793361960765248472672228803522450033037596890564751201744121840117054121250549698850051768979,
12908900811157055896709026524352431678705259915120080553952665812432940328964073657490595065572141461332461381812242187406979181322421022758579822699644826439524635488620712176532072820691254030002764776941981214676051799864538786628205007712278987833037824206850712709555000161787110933550735924983624597506,
13094032259604380890213962970862580304843590998603479847210508580389209009781923968706125230013810715041930959657572931420805618002239385450116842508750589971271206158591287598749754264960338304578268409324200692663731311981045978165221656042897407583698147901255235185516802243698004400149214336397902579289,
11607267019824016484170894832286469005677625363644644963454274615401319623942927315521344441778353065671603459935167971159483358860951380157123046588112521137577815323390219305288962065279491242049797201019142177445435134639295675536040018453899653858942873055550251599457057762533993423388175462354553047467,
11680544029972169142548488946760167091410896653327958540773023974180350194889261149342614109444484689571290170888756379012709796309693311944319970616164279610994671827679197566047697153240751070355256275968675928232105588607972445457445739466802264513287905246618967113954679929691356611270025666455115893555,
12082012009546318757726437769306919642780744314185475745868136542700132886693321574990688240220788870109775162456150476900387800222489223175018902392581555301054222441925986200299245790539635934564530289342003778291577962658691543204332463564882527840910514571482392196121682373333263910383378489601544707283,
11976914060861967548937696950731739430359111972703584682009247779454823866182684326513517979605941734642280728560761907846571025106196807118885809508390866508412172115688547185600474429596611193813645341005069221347382768637715646767056734503774156681622403829839510345057451028016830910371089517419172677922,
13092982833109448135332972388256661833812832390179110019731176136618667366921201033252342731559161110403924077518338553209453980611343896158092470241932343079327484210892214928326748997759127427040181867952519293663070615581463299783028788700534190111427233801757808390214977073515990288464074093239669426012,
15186289267018225519182881171398520133076852140427820895390805925890675200044318467932246614756271451293875795428846428872834036584557859193087503035112483714517860354527546341403609097661295255233294744297433193861246423205600024039910836450811755255529989935361550329778036956315066414284975519301389746635,
11682816747595692369447577118314460697911324497316173683044139973289398052040292262001887959982098714771474805112701661586507709107327511294437693608193460300021342622165857506370780901678299903850063130906103096126344929423842987405671841424708900393148619275962280380273342749640611367336430946415158690950,
11236279191777377191341454807130585737502569191157451118547117826034276986380056254098024599859083822040142781484881918784447777922117742164724120375044345422373197524047541547023298419588873015969932842579183103333370825527749511719309687028649217544313854453760331654204243416247133675490808802393536912055,
13088867766001696934116586401336263328619534182800948672950610740099284043495199561124642155605069203286198878346091465905663198985508746868682266662540787431194010708612681459951564320360572693647812574670766462676592505635974895260675708672375874801923770471806386118149589321577606212502887311324829156412,
16482736506434402111981435428180670349210389751584807640812664115710452187916967496834901904742257406295460491242882483447172825221891048024396299659607424519623581715899391256721420929634126820715471020059362947213012003901001885415984012572905228207214197868075644562110462854365601747875528542683021444851,
12535793564949966376311954233108822196770785358637023532270654448438621487367812725587313329791714322318744102147213518632557484882176197036920885716820892846223183822804286356135771168198337526435895510377580705384278869185068669397665627918534831233480590557282949324072428567156430476696957894741721416782,
11887081949714974115001612297171638015488349126811950119198831122936774123912118370587798838462795373541215230957493520568877592774618079577559502900654719510173923100246667307083382133167553499355013029731823408981574156502053485270810944457451836634208617079395140026742535075348299919192908817642827974480,
11635503322581882885635057914323348649075763394091703493478627096376255882810836432116857021273098699634005869989116333756353513965177444548823329661130936065398934528859832950779483246792020282899803649404090791095195740538095424865962927375059388242257199799341611782081846111812771560192595166017656801600,
11391018814894521525057832087117835047011868483677959699030026799034339836288070333893613311323674479980806724218042057564360010111514565631391835693511393330941224228681228469881635101249760778836161421252852650784224725849699266869712447802392341641406753091269513285925611535267670506868748715407887058574,
11871121849675799388716119378804570707636828464447433934481415787706045040680911003228520921992706961284623205398971317136547153737023440473753298070301500909955996659603663872098231444798861830012971985847085595816987874689280275086967897784919638509632438999596635207446890678713264749899418641358179543332,
14682243968541699051639042094552859012002264203966285201535518708097800242651191689381861789766219318504766565449163874599808238900658046383607004005590588990534014147662134893326550018769041309461292273374302643678522567709540520122551671232767222426605726176577825377727653577254787035422637745962786399859,
16276647908006252162269100147363598317689236648655152919258224327258350563487218045479429827498185586139466322500791030959072278897330035707316448438078658200079438816366693339602458332029237379818089532898612931603056384170685438433239469149978221641538905819271976944433788898332831164432260063063609051953,
14775190966218403600784591384344837080070953442636743024195571271691694443843242494258758122737808985529966873291032689219094444060276211947187417492036039056476345879942229339627225516211388998844197618588794544271401701734356733959906435661152771787137921844470488314142438854410629250121373398656799147142,
11675057905903489199444844431635368651929715602655156031411835935784869146861655666536134411586249546269492887012830674062146817756872518223628619145981398818999847271006810869050958351607471558405833836743150902313554760357055323073855846979157945750433414058142868233255089619477854727584591027242913236667,
11611883976964783552812264362272952353410648582424327146013623482074691505940243926530458059910267964669352093765717432967932111854841696008986971620106157034203399096749482580806461837318820560159806610405148691539972414836818013037761090212512549031502805373973768852237809473488063937135248031955149685283,
11239550662099317927255625936502913089238730300847642989664980621624580813352720412222584989741360463187400441548772222026159726382802618443377739155560686041320850437263358818890027444268733205070718344590072147649392331169105117055248008862249679395484502406038085846679773416543479259543205110274103457768,
11379992394880493798750743980235739755908357932600883873062614937401298403913723993054106630237980047964012658145097602253312159847328852959738499323065991536267850770661991713960812571560091432794769513721166916197263423244289444373899833586534260659980961506015434276105183026852702762715560661918999812990,
11583408698236307147030823256629218017877359908572819887124812970098912520529365695523334175241368591855667853887547111895882415795874730936430651172902372860219286925781591133853523605626993390379890922685317949282509986470624694736265662672997155497653344548735162836769166482582788044842490709694062138659,
13091611166070463571681761190763196812006173686180291193953693204664919056944604077535044177244752354495560706675821147199392229051489989013192394280149848000871736158330365316743907746693809503524973012007708994035524245414768421557506167089834535846663417423963335989167979549508792644508594069290764943929,
11792110805859607653353996288432811980319875874556505335059970492935883358263278322098010176430430202451305439513356113191995850420956231637898382278837262927755709519943668777285156040480980841328944708734888572629062476505808703702394923373919273330429007905903410058977160775194471336601650864835879896909,
11235661421661601335396731836371077656714237331806773031281945632124912056766953386225336503689190069026224123425452227695784814738188165868399905871336107150108501261687438825842240326389270497526298880782929785609812480160283462669709825816322719640818284089015706848337189782370259812664098473087112841026,
15227435448228655894609628154648255887620964007096803766540086530354156455114110318189895197337771738440473415597068354345780897505777827226079414790431402867022954396746927855536049231191203564823298075202300757172249736351964439929806613696887819981703945528440744680018410188954736196651767428489689074477,
11881734263728267636273763966733576093347333654752521416907076826906007276344702122939883237654171445742089279335852727238749598889081012992262644017963708666681604486134036332251405797913169884789647465127660670112907711568223516042285180528548976282000644444436479756587149770187136283616784539973278434466,
11792137550683751142970630340893232561348970672401735338766444191665119771063495516394184314964147904594805248821329924544259042669863770389544824538289957592765641888857275612637818767509777403364084520107680744823575513660677660238680564732877197433541029309721172990077847098686959041951985755451337325570,
11408210993083525274109734510683214274471872312930559240153599394022709282292244710116926993790443703990029104888975047156456860553350495094594111355557825028203695162496059269392631215259068784110436440778608827571222436276350981830824512867566161395339447211880903024108851297642427780509464612993481214069,
11568693295911208677613707014884970243821058518622140924133885226653268600596041275671418769345080743163210941999820942893108492389578869164163984207846548887683883671080073892775124088899314412801531398383779012856034112902946990236133905077094684011202216301679100603016487572065976330082624951205569669743,
14016724489968038062474653771951300551701470713992094965732628598049010035159264040994348053897922036271026006748402832080622809884895635907021704344841318486140151405227780553960577208980654803122780098983905626590036080029180256092202041983023435287712467681532411373017410687001166619878884662373393576850,
15073490414890051061548950941218988070582814015608264287767289489193127736460493426441767312717477234489458770360100645055302709018353038502716491282353928907365882128954202141108765850734360401527251809557561542461284078588016948192798611675111517396703010108769071615048494285158233197852676289006482851741,
15052917471077300680985966137506347482462806583883948187063535067699021744181503264596207643915183918748040420242460146184913855852649738173401802643389878185151451452480274738413099365303912029146389550294626420622122007413649208949656487810593143770225532855760478071421214520205383020414601271464456914723,
13830883897465831753189935441430232460811699635683556110215193683312023688573004041959457676477110964045203142141160780477707336821258959651933626750160246867064365500631558535458555363659613657978671727992503134721025589386643077731006805961938650742350533136680326490216152529612671614831859524987577204922,
15206875898915344943929438809357305057258795631570927573542591317086813394616555741143953401080289967505845538119180853237931704909149759199260352654095539489707693850654902180441386496644257615148140262622913372957200109741885230847997806876230085537297934338123658178835080493812488516773290217146876856396,
12210176713180605898752751251952680951129113678338808107676263407825630770161973076607040939542475066499225246649163027467927854858697277767445870340838687731539066627627925737679592500027270744462146513050624714809318164905726220484431126006501579110867984972386573321969879803100579560850704900050889114643,
11945122055343206003397452325832425495667610733421251983010553656870586546817670080197259778971350118222445834857500507646174868641495603080906170614274390582001791514597839340266972769077620973742213880462955130065558731807803276916671345106872964408527650104275974016505275489989920682164412220653473043757,
11955752990195206971322056133540083289826654627825527943370767069803424166698790251439505913472539498596881316345659304546044243185872903790229940541287702011891520160368140519125593768961826764555465332800045362365155908087621911794632330378061623650147018379640138885362805778387787482596371580256192539577,
13092296492055109651363806712325137645444041908193505828794543329104749755012001194194082286675183878710854410964312722932963546272656430314556096632441910428829563807596379117552649874385667811561379442372010347406318767489573965104316740087820266889347571578520132723401091456069436676887191169487933516668,
11471182130257931879282502100478533145432584751934587617481448065341528618798567365485579501769836688300452612641699082473859640007219550682191536580441876851828026057327373027158915348711493716858832707177163215932834515002803459994126899585267962318005315653456837475575146760545032028609388693235493274008,
11336200905656741961370606201678519652837432371595653425237245127738079564435883641589791931727001688075933505954197303778902561061054392421129493599333857169591282459021269673970758765911891348118934391639301298925916029160973265615753193371216552507736502446382471806504728738010909707299714757020685288773,
12080638291381142575649138492961519269723210555989974940969521271331186346798262869933487814162627006349560794412862436337096559197966158134814827325641640577682999712037462070322199606630778252119627690180537549762266289369802739659843762556605881879716014786642158686614093783367055499917031388934345991825,
17459940950826618261684794990716127781954926324771208443145113319937493283811262141601052713156741635818498594210527279723234282264990460355842435457030398787318620497830312788347329300276151746564520514933411483487670372784362392853777868838288431456588865499614539626065137578217322802003519279190632017065,
16287285634096155624321125698262326710344160663659933616049966216660453300520658093148584677245967575723718760884949489423249949183855975447771742080144738662318422011026652297433195747397315880935079557309330232179914547210342587769197212750508077219753981808699836852431485692852479783631043166474363602767,
17439368339944305803633101192531170857959741144623619378912928812544577466133381777027021228940984613660077637861453988225044333118911974255445016567512215657947335202559502783285650479396628531495817399389508116077025943549163450994574758679910353734564466884080373285592876991863042959825399723927831871781,
15721527269310764233909826421621787132179358684780203536741011622338890283696632913744335001536507654096612231261563630616340531183418275445075801136943552713794595773657238383775681346424324955944876533742859615265420457794154945263433156624986279276064655932130355019153937863511368339462032498362653114823,
13092982477402485368135934286792264424265130929715076996529601163689509109881440208058676558348183864332036843109019633823949791842883197505431446998170431398122404488696730209894983138946144829603855571509008881753079150925936408574539123791544115597481306842080941710786997435557329403935197061899949015062,
14631153466536723718185316102560627916221023019766084275075622831149496441621967352746593067300033385474743278238946805423979713685166563876455214037275318843867033893475919373111156042158312796227837812099716447757128275003211497462258684901316065381375125581956727012403568111524079481928749503950217249177,
17315933344321556388018759548844463937666292792971111209770191556356683858383788452160295996745284229568968828102500360760945643801528270972425057179591361571349045466637204084268862868728381874956544180333785874659702662879692604059415340300122900352069433755989978816645405974476476317794509454964439811187,
11508944637138709281318372786155028138659484045303081744143398435053256955160089660940189671037898099060684702790348972463182453299629197250168291147379171520841792576842418071421432649627666924417068053300899295623992875886330183241618354527453271311926633926684277614451682302009727314336625754556651243327,
12723352604465345568768868507773296272073325926483436161976534165705795087807163432953397543634685410416989551964760714242574204680642249871680146429516695206442844552986707357206971738615053800444168544049182696873964906509618164369715552249093183167089428243241600061403821492263389685515443509044639443957,
16348661709956653461974949965943224272123940866670423321728086872719668440082975086478695955830720383936513764391995750207475793444975207013964048551934761220174815099793242643764827934815048538964867424436732419771180130058907938554040385761497301506718636139447989526331237429171429384655027266358464643282,
14020506277088699816352982111889729782901595194475188743655473224319507057859043765002794681412995287220201623656304253885706361333283285706179349075628155420154165759947976616031424320295588409598373809941868436223331794588531086138480098193320214387449837864654610291104340744665206597865073875357771366712,
15237728217999850050325167864636820693991381798512264888166432996422758472634240340583307248671826973395739925542672413405037793426143434517380395249375850475312922076276061964172000558449708322421519181116000272374431519879745301792605528691577777208704977861849025304874044130231346259729500282823429653332,
14205653106281717603190899969139793404323284208514097508770058030569389535728993052887089842760992892503650783756088757883356223754529331876076497952053604209754398868483739539764331444803799608224369868726996646483571919866681742243589982960239332786371858609111362454030511473382343053215148027842247263353,
11523452235356531385042569933222596706881447173451532399391644245477604616209637711035316265822231014513388252925437015927493370208647083094882326127329707315701266020013455068833083625195070752554993393778346570307779370897809686389651574613050008067934047520261928637773765839784091747144535832614777915699,
16317802450392077858763808761757932726645793029957988980500445509183195610750337216975488965987574917432489710950297648670493303467730094167756447265097132957888634052183905083157344448994076227681195906141643948708011094044242458782395510926138368531260179982138143805567159853977592907797326397330952694802,
16297220769850621348600117827798338047866261042618870326062224367467050693468106537783859968801396617226543367087841992157710491342516948510415025955801434859696603224589319734316794718337188759933921105309923842946325593007913014179528128850858199095339643415885012419751869471183333277689892659810122205628,
11834100871449397461267143353413808248354493462349474403561188985603614506712300897646555055678755419146264020311391067587307656712473498784600621556360315632688008741899472273279859003947448260378153841994292344642024844586200239991932907175465161696612184796801419951465896248150366499267551603155541657427,
11380440304775389009021496134021097852096716763436141998853113156464111618001775485513438892035961931347951878783366168677795393923223655972016725673764617449210261409880225152044973302282613715605858901431912439637948591360889650255420075324299135173486558126471828404353198070010305962527308831286467795825,
17613906816674863861407866563713726644303568879441665132022939690325558565327309638783320277764603864938626346287576334567681595456086745662855268817931518738877232084052965820713298997918296990933988834199177165662845992981830333824993941043715317116616431747808049655552433245634898572128497040661159253287,
16575314820121300246761480924783481966338543438726250456330402761062091224824246369176737877626015236321777030057426589054104155200153116426890591918484276101251748528125189790439154742046299471534273383090582948639518952473975638602511372885860792283075069060825901932772833303413515771973368129401380604316,
12536823381413960728545406089248431048318538147570847891550385105639623395099766089144158360898305376431024609756407928940289217267437019603341287603193123976092788723181220206353884985719485026595155132517810348196000639478095979315645791794181594412388302148371418289054237141246058451316848542111774378810,
17572766884206380553445027044521608666114496934035731153320254540865436177506754821383771813504467211453139046854837275224836184593397507536864520806629597864916129645824752169495028339922184539692360685134522828903602765853495971619043141464268655023264282233887902184965570502403657164028370153661214130295,
11903366023659521335202386813002716795444669106347309740373906536622855536500282320385698535985928383477440858327797509610028011791623776710231481593255025070824694536925775270241842159212352160284833099583237583313152931588435252663138301350298010973170055775096073491388361302697478662277802624848079456305,
11877621553725772798432823109951993508049505849644927259253714429766146823845080257474726789712175136755400428156350522233890775141824048527677699871615581904902240341835779153725456996781539005338409184489499983776952733292070995600001484466292164386293514448770375171450298708105416420663959607318940557231,
11862134068732516541237677597865707275684795994954608882550764648413891358266369127980238241060451634357245317470348467856084864383459014261039244864010568122427598461005619856185283820358669590056277316741049001704045942843229680911659283012322790741844696346818991538949698274994994225716570103028120242557,
16390150575585307992020913012242812295481174076341070836728795521813833861110517438193771937925713272484515590042183085461155655446216490554583644805584198629904304083961541981376463456324956088168768539789339514955176690073358057917860796888122807694896991264224574322743013483089236561285618262503808444289,
11680544029972169142548538364309411104143061966183980192772145167001448272808640082674863144360052243912246557814481910341074632911487995486033025702799014913747042388561569186091004401323085342630772758862579780961561641634157735224142857005170362126377086970448812005707243191004256464909191940900423500927,
11534352293109279208714134392981553119224575850787949485712846518972570823583043958699992313881230524135181226343060290462962792157778835598950714778747233293140571627766082735806197799343383002183326011865676331465498500069209620441621087546471769949323157275873808675102125991731267552090249285595868355795,
11826477098850749653782663250880958560274790518111938889324476599355608071021344668847116449825505926460187021213045014917026461620952602250702343867384918402066654495743958531152740042757280232478019097007114140796840681102961358706417722886404017646767488279384313008235592890180927778410722983095517365722,
13648847643665451830353330064032282654384461962103479085782615527568652199604001728202527706542271563104114514454835289946057800030234726817006529508019842607904013176494796691947892598028946830724737342789494868666909404329922007408427645519736927732566841915171211314183876176874778891736515013800093034968,
11640649389580941836857248648003617706898222523242916314488185140378761425855943998786258947866722986979263438723418859303566398846835834529845765926577479589170964308064103058669641277780423087863641277193128743865177829956643373574261633272925255259846963876717213220268304095430120167764584140478698662360,
11882076832565018973665832516004569964454817675243123526625933818124134667955138650441897372911770838724868104471926388351848098287708774733685576374786323217737258678197505387200200634039321673618302013147662883691630276647167825684973339092487720259972139092672787022792808838932741985621913526859671389988,
11977268178160479470725534154862295154318119484437904716068301365726887231609105172802718954313794949592067919134280841541443869116659440696076949293748851152256672788157697409586330494627970235046483333097526711039764363137970329876769622218428936971584457669157689336211198480500176888339329175647186667690,
12903709885618942681764481040805998082128015455224937475047649736224065049428088571110330561175437766492514605471323449518646379121507216090687975045613877301613991854940990136974771785281388152323686394216836996458407439204171278210955845288985002186053542970547879610078322685702766347883505569352304428867,
14723415452199038355827656929066617113386676903627834811739624291314175397350847838361797924322079044131553566472443461481804028678462174607090196883789196744959279023408721379721108884723133972988369280187918351823082414035630326423336816540734687280810989905942021050854701413120439888739773796320062701876,
16132645122455363795017596017996675922306846745582920870549412430894374880633159732196923267395179827822707575705999576426120833161902700760246241792250623955408317748490237673043655565632207914222639523578508134548733370887671983769692312830088750788692599607495055318833080478227481139110814401033585429306,
17459601842009653089033052710516509192571830166379972386531308318419829773080671905886529448747793954664352631315312303062073208253520092839376593494714200124226546643516736997359670339957474507317452259393521357267307884449507676830543771848086293845768196228342017854925771799095859043455553480864980304116,
14867399505010868891811728007177791777882085446546390089335859917419470278362084237993367194823547866805052910381257667992289675553301510800598723085124742150257178950874762210048638816465942880214866895513837971167244916295805828035750634660033120202448432309585932488667246460506743514003682990747260158737,
13462611098641160694037516469725334726165890572942381668567910158258443998340016111370522578410399447166534973445696968067550736833787175314623425394130499008240834421803814701688619071466400603387665085488463363173685458083185606737334258731148948309010221716231278466615760251053695576747306220463480571649,
13090925086662487049028335671947518612244937459129561682676286910126483994990522602119440954315175050416046170084819725154989257848403085683592671974701326657604653925063348834368679907064681971634554298225058399337987223607736345984832031362802219551350890719180951780881816805026968940349154690649774129680,
12206283177727344955722504126966597127545597200354207100236874385286748553691608460933319943572583445579741745198054727343819535778189876383539770828247371765893507493300701231266312794133035710866535883699769834068550518025459786901312077343187856567574442557846820041591306695081216493371065899145893054300,
12908537743441085236757261320808618387495907983172590155666826812299708482478888290045640129079872856075917920608633985507042077060049210070667734709217616099060545698485728444160784301929669157980862158840884402330473084614552305702713735443344307893663476124604273373152133836064050749460269648810856612383,
16574956885928587579518533768990439944017393652866848181587176585685877451962660066416082329755276216543854525518448307401870100759206803146187391113451981041400619826014512929156658649648197526771288764561444061973135620613737950067187286003261135653866549843214731534724829473633203406380820331564504613215,
17079343906795394319608146526252440559204159301671108844092550029030393888003128248179646021580845212347780468407806407842977581366867156348669968292261215757717837100459159365718491133946152522748596613240650333898025365681371889828011746913683561457589526681738464290742682473556637732015920274398448093008,
16328088901638792322634112941732567829686350887178329469318802308358485753422993738616266378215899174910523691466870642986322881676184207445477173704703698835871802703442404091531973761721341614019937781618471576647886715307506143410742391114860008144564221816551151015382353234989945987499084400480300139549,
13092296624939101820094412804670770971645222830243977409687353811241999478609790768339795569951304885386781559302853478484146772537418802336938720175051725460066696983527250780611135307351735786542444965950132962458974989514224758685685620046839328066211263542603547406220133520805290002737969795722283090263,
14857120778248621227271390227525001840326083429423963333104681533972676086718435663805570909940241338478385057238861620030442096981945678725035881258429399054641800394635189140067821701301682178135993688000332897233265963368131981084068804148956650713484079083452430008706051801587685189613096533338512264054,
16132645179034070729239697910056162548567470196825950125361766903720096612236045107610486755170967866786160987782841961880084494587512346657304968995324185726202585872183260838515772137808239714139007001434767751013138293583588486335093286069968814850039857774888514869274477576178350340021362726757970542973]

set_option maxRecDepth 6000 in
def c_S1_2 : List Nat := [
13088867768001701839353474021050932754256965773528816580596007336173209898066053962344277605547757204175631321969520632320961219270725118389742030783855730791676298823540252945946492000731492764948019452521527410276580674893636892277184601987963237583590921498972336650161315934599176509817107422911923225702,
15073134881534826887236677431260010898458321930131741291892552583065337255069791325071736054097369902929656639321594248593496177481626377443369037229688206237619537696132839393366287140007073373267477329637945407313773583438478509705466434406130220318508382072091623501004135345601873420344505174268853649828,
14020875421027427611815719872512646347393383155309650194812763557663174065559083808653963561323006312738920903420682795998061275111149351286794701205435726253764531129544759317265065577399975269309769736983845621428818001900381136240481425204666097871817649049573596903583284168260657393447398147821182583653,
14579722570789260572450931511647637522662829645731248795414103951953214553695537545090775536202952611854410599471581095036458546958069678978924676119702132759713165473411261963123261415555489469583437006609590110442130168658298952344661968387537247303002396755840721774840496658131591639775777664077263799895,
14980898907962001404421857995073800595560505972569969671162004240832119407481517871573569055611729104743232015715137779033093674829165248888788018740004264934674950041213188869054672996796011467844810916731873759473616382198143830260867996771287112462107014587824079285140029315289541792930340795884262034267,
11490185398367035856807805421472455166913431337892288408749298142212282172840169789848740242468563327758947418859061108125945973439635958527279286412204305468247413166640786737096930370215396916416946588184677856597825722751870568542165157709134793876542894654031292911868720287054260595213027288801547027520,
19383518682181557598350321902393788429717516203483430324779322082409079908666728634203122905210804886217078345498761095855392093283072663526828771261596711800625250160306642868933942541990810253724659245251233806600046373216560509126160513104436991597247500756995300539879280310507551770341125172204444435721,
19198361860824862390295681857357252796673625582285319425661366704750914235307583409150025555304578164373884107176747007855461323742520685142389711561310825163128162679001367230497159785279823594132964014091749234812540343068630429798133594659562293431344753348156149194705028043388285220290750970724766813056,
15258637812656771815139831798922678535021501284596485334524108244998617846299530943176220840674728345638394222945197344637335419247513387608348166878796618991347351445197076122673730517848235020345384129834319054301649882442527045055274017475681745943905498604491512514978235047433497899709294855943634388225,
17367366855270948588939584558480340498135010452680590406793992216534052508250926562120214454616368818171282857152757778996494888392191132998189708511557178403119705497555959480219756785841679953993357595087049816540870886724472476940477830671660949161840076061558943517904605322046882448097067646506421616906,
16091506403877710742724839494926921776362636995529788381767146479120250511856341525405901079627289714372309299486400923284232563164832624752962767014647903526836960950299386242998448580481241905667048162782419343510333025901402284503477499102855679045664420751040331060528842680124624441882177865185188348776,
16482736513867248952488571269931773673978865491464149545661049443526156775817392997692492016605932739827699729719596745107419352601140309938308495379281702333438415960693678824470895932306843885537838689879229824980014019019582168902640411280260569476319756375573781240446141392504957436878934152341378957319,
12536823384658407546613698325875434970582631653804002148937812290335644530713427154605054553205453547088112883122534024779956502397253464730538722293536013473614340423886320912140535294231253686641089874408447582932747045044743535806627761928031875103023232337107494424205731851135611095515597936035795927478,
16112062941661484961259696453119108848951208926631333862589271174956453154552055094895261573016433669260360746993083926024018827956920219784734165298118993613651988214809730578366954073539659601417332644979073889715491428317103256544228661897303973018309376139121282013103725733561757367367829329804627902911,
11375295190412025867601917971637119345339068044346210117019988046982502845577838582709228807579846715098335511798193329293929325194926260336475378228219456936565286588859750694111739091179604157166104432230609557366756453913469757301848064252688404566622341263496337747755861924011086355604151974349433898380,
11777033610343115713962817096297809711203942323932974326857642499029606228930219750164061567988479184803999964531180119113401973791065038083654157981356578510997284577845352244554266390191936022481853030796658782344415749677473757509202825270588613831116875862009534741875995558953098483489818711133549958429,
12232447139976699091302096654230181836486196047806419999537084531893682654612159866431018938043423376486594910314518786500088445087723780395975722703399175050428137086540677098399459286846842381178334262167940304100786590732255672115925652676752092954873921830702318950341087789178513245781977269266503077583,
16575314829474281220414996229143918242295109649566657509086056170569507646651421698455523904542450230505913369877412066223533771824404449983840338163678913340828146457919649376450933041175282925525447413479849451435532351571655421784800044213385445408253428983520185239304602473635856157187775606533364361029,
12724060573441292594865854201778067556062977130059855484623056017666637791720744545899186385762752054873761543163951061988067381071953778663738030728970604142690574370562141415315962045955154600632295159899571877629231320940360976287044081277869663469013919800905529620431736161012860130972812219226393904980,
16533825974367064849553592018131499806184782914512543380515275317620958074443917054849683386014606118434706093880659885285980452120543023021558704463155584911720364860600407318860488148191032599422563484002912560489367303027537726772450764059522035572749068546171235543449216468722540675790764609768546470229,
12226564202716536714135847855097941739483214273565467815854053984203722054754560537808090428752760677693967520224995762778120182807880669761413161925291461670061087824388567734141904780362888942693470107830483924932462375199415623547804621269362990364375292715700076054472463550192495731270144023758143684941,
11386212502365326698819047136507264893489969402449950640303928692868475560688746395439734443519404411430945046195222579498465931320017994774223869454534419485190098803712244112911417522949435177292228283142050242062843751194452180213037998751248922784277617246719586822439095170040805062395906319931709625087,
17233294181580455943797882980707504809474617176714946586804825361594129043422875474635689998366531433114854387326429854483255314739385169591451156766549848189248435538933792676329123533688967849378489370959529016316741674291481703233198640743431579306780720776814221424050926750320924420643396416097871537839,
15145499989845479320085962072761373201205541581515725402799659347940106794901945444447270083495793323156936193748762012584589658378715396674920705219103178359648206810324490386144550332177068142367182128547055699496433886804059934942175303406342118389774919350810560948057281357562968511310427819338538615475,
12908874264116223459831022228322489480159270161673180535725906537362398528700306128595980391998735705057393366234801575053401226771434179148074125103736843060310928487735852642944423736289086594257497703855824891450845839273232720663062211413984885203525335790357642173733389239945353124895686096887411541107,
11385821422633946419039906522699710470982157605365133042144814772619134576774280741667396393977906414725930541329438118407975253897103312081089806975992179707499441589196409481293672942876127362557861408079196914915017002229698301399117019484809197989657038248779937930039741696415285178579329633537110081859,
12249222842748171640611731137381986659213432219727730985399815978713166497391435681127669250935130660118758875404809536991500850521839515079060504136663063465090138080035222663031070166707020420084115833697882315643536174210284684638486271942041060735800065015041030146859689158863376842474884642117106111779,
11423152371228816424612463309939122234740731497517010247919964311181650066232256979725459175906751693512328794605254084068814363107910838393097797409903055019929718191200041456499497888896381284633435404447128513401542435419186514528612089249760979292274877549755850564604005191070394447451058324258535540312,
17274444496493267742860757946006397826799180246805909433603418965862025677796546560383547924104873282626288818782865414596247690462763955079609545834544561894944957847110446535812855175472266571293699766700935963024458216860338907555190283892812395426211481963808310949939172134574598999183026680896534085633,
12077213230853369019233380608998687677903964577419948786808357365861482770640839381942569679069204280741610392902121445785874923898164845410417766621547938241204249669397073236683390337795263312108941189453901309676662270089320230409412467768824512552939713028076127231476595215086702955891674803803047199395,
15022087403622859678934198678528880121921965803040493750546240230037377302966224812435114825859144567890252294175360992475863393848027089227866319622819175745723313329956391384112376436211349482215204013915349125651469401682427791719160590614589015752656478276740027047175281066028349170258577291765597810193,
11877498277834373061229526389084973085748250748161162064235817287069133831543172141829071380053782419598865877552618239555036608997735424417847066834295721364311631142804894359729658471421894210544473669875629990151013166915644077827963357232543549653540858908097797294446387252517340796604379035405974864957,
11883741960681942305239116063299563060326061340604466949085046716221467264075235271863185259164396129649936917580127461691530666244270641824278599873100841593488316160734319830166280659586318031682022150834235631888807897232695146324269266223614906166321841873165482703143184123681879097243779464569016764797,
12254660675959814515479731100029319778209006040786109777811834167843607919723790623457968354730169061926923282054696638341024590091061055390987860817697064610438980187888367781743230869997926595624832176939822989954383070833436387634586987358961902537409991589228813483120975816394381203161253907411380452594,
12243388163733632023465482592807923492688678189655803669381560094973031155888245239397054194316328616017452613407220234048755932825287848264389892721044630521736129527899454923927291206722875899915486573694686008612579595824819412500001242924783036401113565769982892613422488241504030607600713681184397262853,
11307632832588447586632771104733284337389806881070143446665668922852940411805084769318567637900054185917205151064829197698216295927771530015320519989400105045862513139638395666051610017512182383596915501525378569229414893994721630744560125313257419664526241851426792407412287817884419304494150705583396850589,
15094050072627285128448064696723186598900606518665702741304096208696502225000369230102522046417458566668433677858906586111124437194253551443903460216699950248044709283054368832135979677017017409048749428830233975640912467653546712688331634729412176495487613425149375130245701769179541089617911499899223576813,
11236953623907659822774750937877410003732532838195996303338948044444319662479906157412767969184388449988710102760765058640966052200557421029095105998335131869594412617039491068359276926638371576064897329709364720466590753212171545584444330282939638023330584777302648137998940308355301995658506988947896173631,
11597091046793575320306754291729596878427027630043494967961144496740883154372334432925456248009503039884057703103454365458844719477148330356774761193592220497624581186848967589266130266035709402412461709430818031320343236813656087120732679666864036340207274308399125087925559786623678600495384716735459559466,
14774885733102400173740963442636146640629870760007037989124423050251917430400550590088947365673803025149114219718380083024261594436861698234122423134608624042029254590122704132795730414174036326230915267064212066667330279018703507018555377987947607660366154248681871073997341223406564118298425552852956889747,
11880578656151983728357334771764095996961869562228468213990258845526936644167361659868799905055523841089099786062841876744916212563154523426474382622919917662970670937251044757642710887697576016408244036734298697371192025204748166739693741785414537366296799082091728625849141254954109621901696376871650235151,
11423152371228816424130368888558560107358581218110132360283172814603720589663783541214394628488532717693844786387151137298840818988643607218924867990181651029730034422961669939259644559737160953739682615789319950492706728483754272191178945402727020030040531392592748104438014412360776021000665453215386614816,
15094050072627285128448064696723186598900606518665702736471061186443350124268926566712371772993727770012114698436299412856341573346770785989032333976561868815471808992331916544622362852151437800740819993388683001214347745808265239512336901893814398139405103098977847774785675897814740558038041777375921831937,
17274787369918850159133534018081570111769196335749567646452881401537064156008099595949649386106265003548198943370505389802171932919136200413080403341922809774624603397131153660433124715353498635381440805211747495550914439015394247831959083401160562799063317133018051225871227947942136765368744925681945576511,
12719938206707932408845732577265395113781402994426359696674050771876438134287987486331350982668916715680513156048218801067768876194546752902694975560011104239256701449348087912114017098573961200104656705247555925658112239192514942536246930100450425910695942766393972072178204225176514163565939456453249368849,
14918833656790756609912925389510796044392115549590028526929448510377075118943955592352468696343642602702269869956567226774536934026977713109508754999370061996753719910828862740071629238193485199227035928900356411912859131886227078882106469379670765206613045331918990209373536529363038451355496677552895950855,
12721295266079910896397058761671156781567711690738774460438798415274200766827124877239245815314086627949640229785263740826971834115151257563410858454631045275024283755693573721566133425955719452635583717741899899606448221225487587702819555170805880569561384564419267511945991875682518184876063691864274175837,
15165716344593209911520282034200738784076310914697870532515398865825374799805395358619890872530577546903389190975019743580096185959056296917875997571602104321631226406612225870553290237746526400982793167729520312339254259508654786178810428118804941160046412528918896519336378975858187200268213023864358666451,
11421797051920179318636881593808533950942777139363847199819271725670094647079841108657559063771263445650666759042654513509110939837411282881091388302728320863231756574890259587435563068368873549309228747868248362968868175458809727405580170482906981788748392056283092898138873274605688091076380936486262277264,
11307975589773515390943572211834371885578383920871411635653974845521069132315537380412245289039557620363323619153887403781490081767342984234127453080133830183500611536386997898157669804290985478324665862391937236549120023919582324849437538953579371281946231939872320298417581988087456862877441955002985972669,
11888847249290544263195253469672532623593915807360706755811706377412087332879327040577363029826102063960297499452124238833057487799158970872224879452318027099462643423477271313955642530357454135499614315816104167064231535822479710421573038241055812867361500728678249005251570175821450177752145189487508001007,
11854868036975726046133260201525669185563803842207479919317631181681799717919440791424961837175995819692257721734932309462362542808517536924335635520885794958527023494636853800923947749269301301234671795017183409392297631619706508373158413002248284952014735289466073693884182201095563954167485312205860781238,
12533394982891050009661163981285292131865750599319735131726855290597242068640818999088136505881246049596461055392060029600039744535060813619144617026064229099058478709026706961293439674800863009859991024608555574273062088163586151126016973053528604118493255674310010407881929981288730860271275756588829455791,
12905767213533400647959051846559588816593803354957121858316225381656665133732090453218943463271608219614195568186918866278938188766410353262205858259075441216951181948346938008147306565955713398793472634822586773340555584365210207211002412345990514636672355268432274120974827431844323887198549607030006810461,
16338394447436869733949891678427352318178435118808455894567331602964609698509607507378225828819900972603125929408966582837549507007197897485023943226421506470656630680565830570831772970562897334819299764413847306577789604940914809043775874528030575855020280387389901385093260061248621005932280423495623576377,
11236629202763059657588981636595256797590714129203115990233495013259298085511886787426050098480658037433112236732259334328927432084691603806572164685409478306981507844066993920316989275210080473273406859836999883722775003271893970381957398971225123341933920109771047739197312813787415120726100873357735822490,
11630430398926205783184053863666798903978591083953513972554506817050684943424215563202892639609285461708839845970735116779068090276802099206188893703422321239921167217428235937474452559746838646944920735011027619614172532680520666138066633890370887201401609967977998838197288697999559851077949316464434645034,
11422110321867099515136588995717436873112898964861961625058233806919410325912907786832862930709817939859256767596910661539006349651596476859726150940964869160508366225081310555647187275612272025015548934492594594096367513719992257673733324865640335734383703233570504632902786393373571220400709649235440676368,
11319052059152841003897028583444092630768890741606720097528525642182168716894422379227231979659821055635741886512945605010999337773669449140241750082111036261490045656107008668333471941331464106058012911267708457058956838623116301659351058508623493097484764165191170236029311108475822877345894320811124886410,
14020830060836931196411916550738743769600481444383278031667278019072595278814336186696849228635090001412562783959762106263607577157048863451593488133710530709541253954879148970463901573084288175573051919626555634405901705906436879694782111637175139758422494805354486075081274633536597179806359029120052564207,
11235930699834284609732680973084198353599889849491041023249952408914812397907445441465838916993824953216027254404257233077109314192040398541483767641626690947472252174825850107289590324665833271832720978442629255749620454515669363930348642821521891023672008801893866966187952887154314785607417582625290158080,
11601613817841024138337310994296901740191235914631035650745893250154905509295102348342206196234427438710026486476658501102549602646633645186253805144055738662953365243022702156284308276673961134571486900912202838781186641476158747772112044875684424919247208995104700531133717969697211898912513942052574331424,
16554399249318783458172730095364817973624106444232284123228898907920645699996852392221817086147542726699778954187387202853582055409143402078901383635300027032909810127099283827813607878256351458015466904496002493573044634168348831549344434702706401843981658834783278605736447981188175186270782206682150581499,
12908507083464894192545875607507567028527711071256352750213791147787195104603398822582241611833566122927652450452673201192257904302202640810341778201363756538260995837558535855023810413394429075233012985961267507830744648500475433170468210622586776027190637109455772227756783726116202421539282169242573472237,
17243585257882442689529231649406323535409826546072183705266066245632554982849232824735645063175665044720019519686225054319912169068900677704705249983664990340904430405661779686913084113440214506030775926924235339869334586666458050070683583362857392462613518114781205278015356386787134615101302500971620346659,
11683066710906708817120725135248069931127413054258279477476988397536188253120401385404768589605491621229190194048804038450563320407820544143894908405401361042022693285216563337732225419372058556495581009514939918595578616391796802563709243462430005917348963319594817180604121950146458560138870765246139368140,
12722437270329560738301561348534811098546890718174756072835981879184618000571949064997252541086288718139548257208293137525451039561642351050264404464035099537908933977281940639680887571109306088284426995208572954982189672969993415404208225359915985350600315098667921083996089577444800770468074625446095706267,
15258308376424387669021251865004450823760609811866550139803305395757506858413859319973975811808310932063205786634886415279571526189453321215360703864902172668638260405302616022164032625624691057368987445489527325350930372825002887141857282852177042160977610154623485545841845495227843312986127599678707998651,
16502966681925710164308785785919751354790124258693206704566847312739926236164088205414233595538572757800149154183293897769910715339610388384476635418484710017146240565977517516973374651046971141776997678725106101022753246654798509951747447365448449854027742597550794268547719660817767008942031919502079100771,
17696198740480896581246425599853428899522821515379845256079423515558654573146863415726579027693857649512954503771423888142673932474204759607307138100918826676891978960303745527616884161180847489480879818912362587346927198328477174919194057163365684522705085152280869122593850930229307496102006432341424275923,
11479451016783869226300568088758429676981025773494773042554387509045239335289184089765750576762817999215027601448015755899967150927030731992097891339673795868148839596936242797839982521687812273926385820188446558580189021118812322641366535545747714939756953290319196781727130632529475206151696172895379589535,
16133021806977344234266657493064451651919200671861586363145850680915987332452028950636450842005762783575310734514081669940035421481096018651474575398805089813675372127071119325146093994873367901250896146590935093184956908522922356485915070913680738918323533372689550368084987643390812768090024532224724114831,
15032334314774178455142661557163000100465823811552564589842768920312316185364560707726612719499537859718465348568435314447703502374721146190268948248726637405759419585099098419358851178859731150615471135489656388319437050095616204818244544010432438411740087163880770533691373683781982215104358254166128791792,
12538892860495056436797620271968367854533260518845979086203809310574842671131016233316991973750541579779730144006564502350267689024527086810624809854161138344939796581203788034048518272628082910719052481732177205778384956069915523924153026757791418652433645912006740677622195363943722589453685480941447185203,
19383518681141804737893568394713274385021051050732049990070211470574160338920309923976993506229397598607100256365255982769021426773320942609831831536892654321236342032194794016666531377726980828993201968920122177488818956187259391224025627804031632217847177447169401514541433355549117720026658772080553265440,
16143290174333969098970455846848469149488710538958058770387886207539282542089594947331802384011834653601918996235966384247936007682492825900851244595301077633817386780502790645990886196480906746678430845435359138586159485838535902587347099973629296811262044326611949023512356099167013600541509289523199772960,
13832926103589310477601913365406124808883136945139950653212211165248992728337728888015984419655682804320505837311538015011352353496923749077142744179991951580037199488674246152752658086252982286217912465471546600660702729913918745654215644308516544850974500349281635616109620359280387951014911663965040837705,
12722372770109659463299068463052184842420049907507736034484525972646037090417978161231287181895523152781822382014351999392537627782294847899505504859167216932320909015533428402302469786912923696207765879942305355717747361595433511547205522221229465157685986058186251189014892054168376261481715482007958618972,
17501090711014612098919193337653944854563450953500790560069401533009566282136895377356823811092522568204921403565405612312792954302145359756889192377289153430840942391836739002773027483390251787441619313079119472824877373181698529072410144358031502650628097789101359333424889907757715158231155780122136551355,
16204993220467151550728482863081293214924567937250800778810598481919065532054584168097366815170352034309716058653138589425315548587151224033784331081130744609434600659207437132865682988091998527455659691778079072979294561081560391774224485728609516192417847041266680717676339178228055997976600928263652409666,
12054768766799358491198412825847678357179749647206369778460243573774402747487340290087331056126473145668520287767071055018733868016741918736897807770932154032154455360402088089766106269948564224466517131134961746704966540504788052751539973231789553044794865085747390213456844605721939625927322194428539863310,
11530654657119095596097262765639120412221771274736087998582697398071395722415670036120384841641551716753711052579047055869572905661994212611046696388334839272845273966791499263481260431961392576488785691146555329034699943762502377819699224211224763668252344979496853168811703469036098740911995208791776825587,
11779090906422196046367021530189089369918846222850937023353420133050013245937393477260955493415970283531181642228706866503509669574915692612410503723291799246434357794225439437997130445465180440805414923493310110899701168228233394859052378213058440910225258906603957032541124977963714140618993756639101332408,
11237995626246723570958928898625726546502464010246829615677339278691008589319342167673872144507813408895105280718537896013473096089334547943424039266785040088640444879572342431404676712383128402412448519889860788666522505845314829606241099580787063574588009055385061985722558831271281520948465254357932904145,
68418615696755084406618101186996579952616152485163598257537409821623218196599847512010167420762]

noncomputable def c_S1 : List Nat := c_S1_0 ++ c_S1_1 ++ c_S1_2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem seg1 : ∀ a, EntriesSat a c_B1 → EntriesSat a c_B2 :=
  checkSeg_sound c_B1 15 c_S1 c_B2 (by decide +kernel)

set_option maxRecDepth 6000 in
def c_S2_0 : List Nat := [
11724269178012110569637148303471349814204124875672981673173821887175571339868549830480976325052311798238366749755026724914932509430104200854431808245692166917301258228097533492950127162854159632061801101989184978396649484211714157212052824874181778017381667234168079990241294241478694087990546665096043400126,
11878591813227598474629759605930751499843235193718965945167629022980591232236815473169514256723885157428609632231050849495555105268204285823571133919124695873481914146371006871815957215612177169143414287572336961686825259416912307971657590110870639946270198315774213391821628738864130539599285531681147657617,
12132563399065242090131345358008846507715380553986631133027008445065558053732254908645473009987764546517525254137526434643712224767831032274163318665138827814920223372330642952859273835694082147658381129585342755229903922652841115991089182640401247702995322510109286489833605045338395048975709671110837222343,
13094038097631461100932150284632728020920091137483008970604899121264182906336176131713542903677789162168007630295225326726880474699180577827525988268009305464788642496745555146292943206524207968319599640410978925822085461151850420869760318547352340376714957480282022292529089525447064386952394777310428236735,
12268687831767933275512613330891322252084698688510425770116578877152541694550044121848142190911695418981161482958139307202440782978762534499323145574511639268046474626698662328626883697341961821249541429785428518302972952586061781945995888710901080814638749705751026519701058225684833869013385227176945614848,
12269716485797373679546838002371791353712405785529353721481189948446042946640811619288228954318396015601260175548203970040473692314778073919122868915479686010109418486281784951436741509004311485824240032314516181208052145337542671934812028082898417709785606419810564271060675480777324549082970191690669195811,
14918860429348792612863232390999283596357236052658223871153354217530453113260626709927116126225439345098632357104471635791072470736299884733710568160099136890676638425385249680218517280394307445743138120538787800993707322471637518962247773932399779538895649079492801805444428515587815351292342150820730407026,
11902916743702125649296527212392626098517346826392670337589214550862423647663158636699870387296644814796448337205279748228927062909409008367545417634299022993209942084326532099337297210567055872422576920241212264629763926995634514355542249327805005588852112575641285094064567531779457143790220120834079096832,
15968424676338753046291330098556410919559157988467451556782060609291193819342541119887619969172719066535394399544643506110250041433718487816739643127575064886312312043441075834937111227683325940018999403685167880954990441926143615753299074844037533648382966122711517300939016111196240883243610538580527390637,
12276347110026979562570078038973081872110184103425000579299199005211816169597652238415030994369572841320946937097423924990519655530826963595517490579664706079731213428920358617311586275940024861118174508108957402012138538575841535086536045974399431931153271813230696934751106725941697284744552504970660052992,
12268455156143971698079893783030323451800823338750253586443582014820580343752391455077637160753270462217143542682359986169355300997645000514106545403628471591843060980283981044014333509315655637323891925015028123476784068340099996036366667624135506557053949741624842701759606212097350191164331243986855406460,
12269491348924981119631641889010875850006981203261492610717583982425825418931351385461195755738464018788654154339447577528961576331283789227863993388764279547169112033895545924630636776987046243979239526536923191321766430447593407187624791226839758648271143556671954136491883459073254643691651135085787916550,
15021725206623336404965594627898963674701429579086619484603400924103624690039547274095404754583600018979158542782185204042389161691646363277160809479852818057350535064043206894127106588069263112673167795639305428815337528229858724150560657444416469310441401699282779307245519072314460273788165466036392254675,
37409200769995]

noncomputable def c_S2 : List Nat := c_S2_0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem seg2 : ∀ a, EntriesSat a c_B2 → False :=
  checkLast_sound c_B2 15 c_S2 (by decide +kernel)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem unsat : ¬ FormulaSat F := fun ⟨a, ha⟩ =>
  seg2 a (seg1 a (seg0 a ha))
def witness : Circuit := ⟨[⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [8, 12]⟩], 13⟩

theorem allInputs : ∀ a b c d : Bool,
    witness.eval (List.ofFn ![a,b,c,d] ++ List.ofFn (fun i => !(![a,b,c,d] i))) =
      target ![a,b,c,d] := by decide

theorem upper : HasLitSize 4 target 6 := by
  refine ⟨witness, by simp [witness, Monotone2], by decide, ?_⟩
  intro x
  have hx : x = ![x 0, x 1, x 2, x 3] := by funext i; fin_cases i <;> rfl
  rw [hx]
  exact allInputs (x 0) (x 1) (x 2) (x 3)

theorem rowCoverage : ∀ r ∈ rows, ∃ x : Fin 4 → Bool,
    (List.ofFn fun i : Fin 8 => r.testBit i) = List.ofFn x ++ List.ofFn (fun i => !x i) ∧
      g r = target x := by decide

theorem lower (t : ℕ) (h : HasLitSize 4 target t) : 6 ≤ t := by
  by_contra! ht
  obtain ⟨C, legal, size, evaluates⟩ := h
  have hv := valid_ofCirc 8 5 g (· ∈ rows) C legal
    (by simp only [Circuit.size] at size; omega) (by
      intro r hr
      obtain ⟨x, hx, hg⟩ := rowCoverage r hr
      change C.eval (List.ofFn fun i : Fin 8 => r.testBit i) = g r
      rw [hx, evaluates, hg])
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact unsat ⟨val 8 5 M, enc2_sat (by decide) hM hnf hlx⟩

end PEqualNP.Outside.V_meta_9689__k6_aux

theorem PEqualNP.Outside.V_meta_9689__k6 :
PEqualNP.Represents.HasLitSize 4 (fun x : Fin 4 → Bool => (429 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 6 ∧
  ∀ t : ℕ, PEqualNP.Represents.HasLitSize 4 (fun x : Fin 4 → Bool => (429 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 6 ≤ t :=
  ⟨PEqualNP.Outside.V_meta_9689__k6_aux.upper, PEqualNP.Outside.V_meta_9689__k6_aux.lower⟩
