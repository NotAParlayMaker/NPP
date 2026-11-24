import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5104

def stepN (d : ℕ) (L : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ :=
  L ++ [if g.1 = true then L.getD g.2.1 d ||| L.getD g.2.2 d else L.getD g.2.1 d &&& L.getD g.2.2 d]

def stepB (d : Bool) (L : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  L ++ [if g.1 = true then (L.getD g.2.1 d || L.getD g.2.2 d) else (L.getD g.2.1 d && L.getD g.2.2 d)]

def evalN (L : List ℕ) (gs : List (Bool × ℕ × ℕ)) (w : ℕ) : ℕ :=
  (gs.foldl (stepN (L.headD 0)) L).getD w (L.headD 0)

def evalB (L : List Bool) (gs : List (Bool × ℕ × ℕ)) (w : ℕ) : Bool :=
  (gs.foldl (stepB (L.headD false)) L).getD w (L.headD false)

def col (L : List ℕ) (k : ℕ) : List Bool := L.map fun v => v.testBit k

def leB : List Bool → List Bool → Bool
  | [], [] => true
  | a :: as, b :: bs => (!a || b) && leB as bs
  | _, _ => false

def X2 : List ℕ := [917681504273, 14878052356, 31886295704066, 257731462272, 42884715528480, 82789891049544, 248671168364547, 198670308868108, 158476001083504, 238332533539200, 176488259259904, 212188564320256, 280375465312256, 271282175737871, 280357743624591]

def X3 : List ℕ := [63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752, 191866593364673099, 193001360500003407]

def sig : List ℕ := [0, 0, 0, 0, 4, 15, 2, 12, 16, 1, 9, 13, 7, 10, 17, 5, 8, 14, 3, 6, 11, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 32, 33, 34, 35, 36, 37, 37, 38, 39, 39, 40, 41, 42, 44, 43, 44, 45, 45, 46, 46, 47, 47]

theorem getD_map_f (f : ℕ → Bool) (L : List ℕ) (i d : ℕ) :
    (L.map f).getD i (f d) = f (L.getD i d) := by
  induction L generalizing i with
  | nil => simp
  | cons a L ih => cases i with
    | zero => simp
    | succ i => simpa using ih i

theorem proj (d k : ℕ) (gs : List (Bool × ℕ × ℕ)) (L : List ℕ) :
    (gs.foldl (stepN d) L).map (fun v => v.testBit k) =
      gs.foldl (stepB (d.testBit k)) (L.map fun v => v.testBit k) := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    simp only [stepN, stepB, List.map_append, List.map_cons, List.map_nil]
    rw [getD_map_f (fun v => v.testBit k), getD_map_f (fun v => v.testBit k)]
    cases g.1 <;> simp [Nat.testBit_or, Nat.testBit_and]

theorem headD_col (L : List ℕ) (k : ℕ) : (col L k).headD false = (L.headD 0).testBit k := by
  cases L <;> simp [col]

theorem evalN_bit (L : List ℕ) (gs : List (Bool × ℕ × ℕ)) (w k : ℕ) :
    (evalN L gs w).testBit k = evalB (col L k) gs w := by
  unfold evalN evalB
  rw [headD_col, ← getD_map_f (fun v => v.testBit k), proj]
  rfl

theorem getD_lt {α : Type} (L : List α) (i : ℕ) (d d' : α) (h : i < L.length) :
    L.getD i d = L.getD i d' := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_ge {α : Type} (L : List α) (i : ℕ) (d : α) (h : L.length ≤ i) :
    L.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_append_one {α : Type} (A : List α) (x d : α) (i : ℕ) :
    (A ++ [x]).getD i d = if i < A.length then A.getD i d else if i = A.length then x else d := by
  induction A generalizing i with
  | nil => cases i <;> simp
  | cons a A ih => cases i with
    | zero => simp
    | succ i =>
      simp only [List.cons_append, List.getD_cons_succ, ih, List.length_cons]
      by_cases h1 : i < A.length
      · simp [h1]
      · by_cases h2 : i = A.length
        · simp [h2]
        · simp [h1, h2]

theorem mono_step (dA dB : Bool) (hd : dA = true → dB = true) (A B : List Bool)
    (hl : A.length = B.length) (h : ∀ i, A.getD i dA = true → B.getD i dB = true)
    (g : Bool × ℕ × ℕ) :
    (stepB dA A g).length = (stepB dB B g).length ∧
      ∀ i, (stepB dA A g).getD i dA = true → (stepB dB B g).getD i dB = true := by
  refine ⟨by simp [stepB, hl], ?_⟩
  intro i hi
  simp only [stepB, getD_append_one] at hi ⊢
  rw [← hl]
  by_cases h1 : i < A.length
  · rw [if_pos h1] at hi; rw [if_pos h1]; exact h i hi
  · rw [if_neg h1] at hi; rw [if_neg h1]
    by_cases h2 : i = A.length
    · rw [if_pos h2] at hi; rw [if_pos h2]
      rcases g with ⟨b, a1, a2⟩
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hi ⊢
        exact ⟨h _ hi.1, h _ hi.2⟩
      · simp only [↓reduceIte, Bool.or_eq_true] at hi ⊢
        exact hi.imp (h _) (h _)
    · rw [if_neg h2] at hi; rw [if_neg h2]; exact hd hi

theorem mono_fold (dA dB : Bool) (hd : dA = true → dB = true) (gs : List (Bool × ℕ × ℕ)) :
    ∀ (A B : List Bool), A.length = B.length → (∀ i, A.getD i dA = true → B.getD i dB = true) →
      ∀ i, (gs.foldl (stepB dA) A).getD i dA = true → (gs.foldl (stepB dB) B).getD i dB = true := by
  induction gs with
  | nil => intro A B _ h; simpa using h
  | cons g gs ih =>
    intro A B hl h
    obtain ⟨hl', h'⟩ := mono_step dA dB hd A B hl h g
    simpa [List.foldl_cons] using ih _ _ hl' h'

theorem leB_spec : ∀ (A B : List Bool), leB A B = true →
    A.length = B.length ∧ ∀ i, A.getD i false = true → B.getD i false = true
  | [], [], _ => ⟨rfl, by simp⟩
  | a :: as, b :: bs, h => by
    simp only [leB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hab, hrest⟩ := h
    obtain ⟨hl, hi⟩ := leB_spec as bs hrest
    refine ⟨by simp [hl], ?_⟩
    intro i
    cases i with
    | zero => cases a <;> cases b <;> simp_all
    | succ i => simpa using hi i
  | [], _ :: _, h => by simp [leB] at h
  | _ :: _, [], h => by simp [leB] at h

theorem evalB_mono (A B : List Bool) (gs : List (Bool × ℕ × ℕ)) (w : ℕ) (hAB : leB A B = true) :
    evalB A gs w = true → evalB B gs w = true := by
  obtain ⟨hl, h⟩ := leB_spec A B hAB
  have hd : A.headD false = true → B.headD false = true := by
    cases A <;> cases B <;> simp_all
    · simpa using h 0
  have h2 : ∀ i, A.getD i (A.headD false) = true → B.getD i (B.headD false) = true := by
    intro i hi
    by_cases hi' : i < A.length
    · rw [getD_lt A i _ false hi'] at hi
      rw [getD_lt B i _ false (hl ▸ hi')]
      exact h i hi
    · rw [getD_ge A i _ (by omega)] at hi
      rw [getD_ge B i _ (by omega)]
      exact hd hi
  exact mono_fold _ _ hd gs A B hl h2 w

def checkLo (k : ℕ) : Bool := col X3 k == col X2 (sig.getD k 0) && decide (sig.getD k 0 < 18)
def checkHi (k : ℕ) : Bool := leB (col X3 k) (col X2 (sig.getD k 0)) && decide (18 ≤ sig.getD k 0)

theorem lo_ok : (List.range' 3 18).all checkLo = true := by decide
theorem hi_ok : (List.range' 21 37).all checkHi = true := by decide

theorem X3_lt : ∀ v ∈ X3, v < 2 ^ 58 := by decide

theorem col_X3_big (k : ℕ) (hk : 58 ≤ k) : col X3 k = List.replicate 15 false := by
  have h : ∀ v ∈ X3, v.testBit k = false := fun v hv =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (X3_lt v hv) (Nat.pow_le_pow_right (by norm_num) hk))
  unfold col
  rw [List.eq_replicate_iff]
  refine ⟨by rfl, ?_⟩
  intro b hb
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hb
  exact h v hv

theorem main (gs : List (Bool × ℕ × ℕ)) (w : ℕ) (h : evalN X2 gs w = 262143) :
    evalN X3 gs w ||| 7 = 2097151 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or]
  by_cases k3 : k < 3
  · have h7 : (7 : ℕ).testBit k = true := by interval_cases k <;> decide
    have h2 : (2097151 : ℕ).testBit k = true := by interval_cases k <;> decide
    rw [h7, h2]; simp
  by_cases k21 : k < 21
  · have hk : checkLo k = true := by
      have := List.all_eq_true.mp lo_ok k (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      exact this
    simp only [checkLo, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
    rw [evalN_bit, hk.1, ← evalN_bit, h]
    have h1 : (262143 : ℕ).testBit (sig.getD k 0) = true := by
      have := hk.2
      interval_cases (sig.getD k 0) <;> decide
    have h2 : (2097151 : ℕ).testBit k = true := by interval_cases k <;> decide
    rw [h1, h2]; simp
  · have hlhs : (evalN X3 gs w).testBit k = false := by
      rw [evalN_bit]
      by_cases k58 : k < 58
      · have hk : checkHi k = true :=
          List.all_eq_true.mp hi_ok k (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
        simp only [checkHi, Bool.and_eq_true, decide_eq_true_eq] at hk
        have hz : evalB (col X2 (sig.getD k 0)) gs w = false := by
          rw [← evalN_bit, h]
          exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk.2))
        cases hv : evalB (col X3 k) gs w
        · rfl
        · have := evalB_mono _ _ gs w hk.1 hv
          rw [hz] at this; exact absurd this (by simp)
      · have hk : leB (col X3 k) (col X2 18) = true := by
          rw [col_X3_big k (by omega)]; decide
        have hz : evalB (col X2 18) gs w = false := by
          rw [← evalN_bit, h]; decide
        cases hv : evalB (col X3 k) gs w
        · rfl
        · have := evalB_mono _ _ gs w hk hv
          rw [hz] at this; exact absurd this (by simp)
    have h7 : (7 : ℕ).testBit k = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 3 ≤ k)))
    have hr : (2097151 : ℕ).testBit k = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 21 ≤ k)))
    rw [hlhs, h7, hr]; rfl

end PEqualNP.Outside.L_meta_5104

theorem PEqualNP.Outside.L_meta_5104 : have x1 : List ℕ → List (Bool × ℕ × ℕ) → ℕ → ℕ := fun (x1 : List ℕ) (x2 : List (Bool × ℕ × ℕ)) (x3 : ℕ) =>   have x4 : ℕ := x1.headD (0 : ℕ);   (List.foldl         (fun (x5 : List ℕ) (x6 : Bool × ℕ × ℕ) =>           have x7 : ℕ → ℕ := fun (x7 : ℕ) => x5.getD x7 x4;           x5 ++ [if x6.1 = Bool.true then x7 x6.2.1 ||| x7 x6.2.2 else x7 x6.2.1 &&& x7 x6.2.2])         x1 x2).getD     x3 x4; have x2 : List ℕ := [(917681504273 : ℕ), (14878052356 : ℕ), (31886295704066 : ℕ), (257731462272 : ℕ), (42884715528480 : ℕ), (82789891049544 : ℕ), (248671168364547 : ℕ), (198670308868108 : ℕ), (158476001083504 : ℕ), (238332533539200 : ℕ), (176488259259904 : ℕ), (212188564320256 : ℕ), (280375465312256 : ℕ), (271282175737871 : ℕ), (280357743624591 : ℕ)]; have x3 : List ℕ := [(63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ), (191866593364673099 : ℕ), (193001360500003407 : ℕ)]; ∀ (x4 : List (Bool × ℕ × ℕ)) (x5 : ℕ), x1 x2 x4 x5 = (262143 : ℕ) → x1 x3 x4 x5 ||| (7 : ℕ) = (2097151 : ℕ) := by
  show ∀ (gs : List (Bool × ℕ × ℕ)) (w : ℕ),
    PEqualNP.Outside.L_meta_5104.evalN PEqualNP.Outside.L_meta_5104.X2 gs w = 262143 →
    PEqualNP.Outside.L_meta_5104.evalN PEqualNP.Outside.L_meta_5104.X3 gs w ||| 7 = 2097151
  exact PEqualNP.Outside.L_meta_5104.main
