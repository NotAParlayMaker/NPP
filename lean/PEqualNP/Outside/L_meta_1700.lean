import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1700

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

def G : List (Bool × ℕ × ℕ) := [(false, 16, 17), (false, 18, 19), (false, 16, 18), (false, 17, 19), (false, 20, 21), (false, 22, 23), (false, 20, 22), (false, 21, 23), (false, 24, 25), (false, 26, 27), (false, 24, 26), (false, 25, 27), (false, 28, 29), (false, 30, 31), (false, 28, 30), (false, 29, 31), (false, 32, 36), (false, 48, 40), (false, 49, 44), (false, 33, 37), (false, 51, 41), (false, 52, 45), (false, 34, 38), (false, 54, 42), (false, 55, 46), (false, 35, 39), (false, 57, 43), (false, 58, 47), (true, 50, 56), (true, 0, 60), (true, 50, 59), (true, 1, 62), (true, 53, 56), (true, 2, 64), (true, 53, 59), (true, 3, 66), (false, 32, 36), (false, 68, 41), (false, 69, 45), (false, 33, 37), (false, 71, 40), (false, 72, 44), (false, 34, 39), (false, 74, 42), (false, 75, 47), (false, 35, 38), (false, 77, 43), (false, 78, 46), (true, 70, 76), (true, 4, 80), (true, 70, 79), (true, 5, 82), (true, 73, 76), (true, 6, 84), (true, 73, 79), (true, 7, 86), (false, 32, 37), (false, 88, 41), (false, 89, 44), (false, 33, 36), (false, 91, 40), (false, 92, 45), (false, 34, 38), (false, 94, 43), (false, 95, 47), (false, 35, 39), (false, 97, 42), (false, 98, 46), (true, 90, 96), (true, 8, 100), (true, 90, 99), (true, 9, 102), (true, 93, 96), (true, 10, 104), (true, 93, 99), (true, 11, 106), (false, 32, 37), (false, 108, 40), (false, 109, 45), (false, 33, 36), (false, 111, 41), (false, 112, 44), (false, 34, 39), (false, 114, 43), (false, 115, 46), (false, 35, 38), (false, 117, 42), (false, 118, 47), (true, 110, 116), (true, 12, 120), (true, 110, 119), (true, 13, 122), (true, 113, 116), (true, 14, 124), (true, 113, 119), (true, 15, 126), (false, 61, 63), (false, 128, 65), (false, 129, 67), (false, 130, 81), (false, 131, 83), (false, 132, 85), (false, 133, 87), (false, 134, 101), (false, 135, 103), (false, 136, 105), (false, 137, 107), (false, 138, 121), (false, 139, 123), (false, 140, 125), (false, 141, 127), (true, 0, 4), (true, 143, 8), (true, 144, 12), (true, 1, 5), (true, 146, 9), (true, 147, 13), (true, 2, 6), (true, 149, 10), (true, 150, 14), (true, 3, 7), (true, 152, 11), (true, 153, 15), (true, 145, 148), (true, 155, 151), (true, 156, 154), (true, 154, 151), (true, 158, 148), (true, 159, 145), (true, 145, 158), (true, 155, 154), (true, 0, 5), (true, 163, 10), (true, 164, 15), (true, 1, 4), (true, 166, 11), (true, 167, 14), (true, 2, 7), (true, 169, 8), (true, 170, 13), (true, 3, 6), (true, 172, 9), (true, 173, 12), (true, 165, 168), (true, 175, 171), (true, 176, 174), (true, 174, 171), (true, 178, 168), (true, 179, 165), (true, 165, 178), (true, 175, 174), (true, 0, 6), (true, 183, 11), (true, 184, 13), (true, 1, 7), (true, 186, 10), (true, 187, 12), (true, 2, 4), (true, 189, 9), (true, 190, 15), (true, 3, 5), (true, 192, 8), (true, 193, 14), (true, 185, 188), (true, 195, 191), (true, 196, 194), (true, 194, 191), (true, 198, 188), (true, 199, 185), (true, 185, 198), (true, 195, 194), (true, 0, 7), (true, 203, 9), (true, 204, 14), (true, 1, 6), (true, 206, 8), (true, 207, 15), (true, 2, 5), (true, 209, 11), (true, 210, 12), (true, 3, 4), (true, 212, 10), (true, 213, 13), (true, 205, 208), (true, 215, 211), (true, 216, 214), (true, 214, 211), (true, 218, 208), (true, 219, 205), (true, 205, 218), (true, 215, 214), (false, 159, 161), (false, 223, 162), (false, 224, 156), (false, 225, 179), (false, 226, 181), (false, 227, 182), (false, 228, 176), (false, 229, 199), (false, 230, 201), (false, 231, 202), (false, 232, 196), (false, 233, 219), (false, 234, 221), (false, 235, 222), (false, 236, 216), (false, 237, 0), (false, 238, 4), (false, 239, 8), (false, 240, 12), (true, 16, 241), (false, 237, 1), (false, 243, 5), (false, 244, 9), (false, 245, 13), (true, 17, 246), (false, 237, 2), (false, 248, 6), (false, 249, 10), (false, 250, 14), (true, 18, 251), (false, 237, 3), (false, 253, 7), (false, 254, 11), (false, 255, 15), (true, 19, 256), (false, 237, 0), (false, 258, 5), (false, 259, 10), (false, 260, 15), (true, 20, 261), (false, 237, 1), (false, 263, 4), (false, 264, 11), (false, 265, 14), (true, 21, 266), (false, 237, 2), (false, 268, 7), (false, 269, 8), (false, 270, 13), (true, 22, 271), (false, 237, 3), (false, 273, 6), (false, 274, 9), (false, 275, 12), (true, 23, 276), (false, 237, 0), (false, 278, 6), (false, 279, 11), (false, 280, 13), (true, 24, 281), (false, 237, 1), (false, 283, 7), (false, 284, 10), (false, 285, 12), (true, 25, 286), (false, 237, 2), (false, 288, 4), (false, 289, 9), (false, 290, 15), (true, 26, 291), (false, 237, 3), (false, 293, 5), (false, 294, 8), (false, 295, 14), (true, 27, 296), (false, 237, 0), (false, 298, 7), (false, 299, 9), (false, 300, 14), (true, 28, 301), (false, 237, 1), (false, 303, 6), (false, 304, 8), (false, 305, 15), (true, 29, 306), (false, 237, 2), (false, 308, 5), (false, 309, 11), (false, 310, 12), (true, 30, 311), (false, 237, 3), (false, 313, 4), (false, 314, 10), (false, 315, 13), (true, 31, 316), (false, 242, 247), (false, 318, 252), (false, 319, 257), (false, 320, 262), (false, 321, 267), (false, 322, 272), (false, 323, 277), (false, 324, 282), (false, 325, 287), (false, 326, 292), (false, 327, 297), (false, 328, 302), (false, 329, 307), (false, 330, 312), (false, 331, 317), (true, 142, 332)]

def Inc : List (ℕ × ℕ) := [(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)]

def toGate (g : Bool × ℕ × ℕ) : Gate := ⟨cond g.1 GateOp.and GateOp.or, [g.2.1, g.2.2]⟩

def C0 : Circuit := ⟨G.map toGate, 333⟩

def stpG (fa fo : ℕ → ℕ → ℕ) (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ :=
  w ++ [cond g.1 (fa (w.getD g.2.1 0) (w.getD g.2.2 0)) (fo (w.getD g.2.1 0) (w.getD g.2.2 0))]

def rd (n : ℕ) (r : List ℕ) (a : ℕ) : ℕ := if a < n then r.getD (n - 1 - a) 0 else 0

def evR (fa fo : ℕ → ℕ → ℕ) : List (Bool × ℕ × ℕ) → ℕ → List ℕ → List ℕ
  | [], _, r => r
  | g :: gs, n, r =>
    evR fa fo gs (n + 1)
      (cond g.1 (fa (rd n r g.2.1) (rd n r g.2.2)) (fo (rd n r g.2.1) (rd n r g.2.2)) :: r)

theorem rd_eq (w : List ℕ) (a : ℕ) : rd w.length w.reverse a = w.getD a 0 := by
  unfold rd
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by omega)]
    congr 2
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem evR_eq (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    evR fa fo gs w.length w.reverse = (gs.foldl (stpG fa fo) w).reverse := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ← ih, evR, rd_eq, rd_eq]
    simp [stpG]

theorem length_fold (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    (gs.foldl (stpG fa fo) w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stpG]
    omega

theorem fold_getD (fa fo : ℕ → ℕ → ℕ) (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) (a : ℕ) :
    (gs.foldl (stpG fa fo) w).getD a 0
      = rd (w.length + gs.length) (evR fa fo gs w.length w.reverse) a := by
  rw [evR_eq, ← length_fold fa fo, rd_eq]

def stpN (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ := stpG (fun a b => a &&& b) (fun a b => a ||| b) w g

theorem getD_tb (k : ℕ) (W : List ℕ) (i : ℕ) :
    (W.map fun v => v.testBit k).getD i false = (W.getD i 0).testBit k := by
  have h := List.getD_map (f := fun v : ℕ => v.testBit k) (l := W) (d := 0) (n := i)
  simpa using h

theorem bridge (k : ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (W : List ℕ),
    (gs.map toGate).foldl stp (W.map fun v => v.testBit k)
      = (gs.foldl stpN W).map fun v => v.testBit k := by
  intro gs
  induction gs with
  | nil => intro W; rfl
  | cons g gs ih =>
    intro W
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    obtain ⟨b, i, j⟩ := g
    have hi := getD_tb k W i
    have hj := getD_tb k W j
    cases b
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_lor]
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_land]

def tab : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, p => if p = n then (2 ^ 2 ^ n - 1) <<< 2 ^ n else tab n p ||| (tab n p <<< 2 ^ n)

theorem tab_bit : ∀ n p k, p < n →
    (tab n p).testBit k = (decide (k < 2 ^ n) && k.testBit p) := by
  intro n
  induction n with
  | zero => intro p k h; omega
  | succ n ih =>
    intro p k hp
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    rw [tab]
    split_ifs with hpn
    · subst hpn
      rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hk : k < 2 ^ p
      · rw [Nat.testBit_lt_two_pow hk]
        simp
        omega
      · have hb : k.testBit p = !((k - 2 ^ p).testBit p) := by
          rw [← Nat.testBit_two_pow_add_eq]
          congr 1
          omega
        by_cases hk2 : k - 2 ^ p < 2 ^ p
        · have e0 : decide (k ≥ 2 ^ p) = true := by
            simp only [decide_eq_true_eq]
            omega
          have e1 : decide (k - 2 ^ p < 2 ^ p) = true := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = true := by
            simp only [decide_eq_true_eq]
            omega
          rw [hb, Nat.testBit_lt_two_pow hk2, e0, e1, e2]
          rfl
        · have e1 : decide (k - 2 ^ p < 2 ^ p) = false := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = false := by
            simp only [decide_eq_false_iff_not]
            omega
          rw [e1, e2]
          simp
    · have hp' : p < n := by omega
      rw [Nat.testBit_lor, Nat.testBit_shiftLeft, ih p k hp', ih p (k - 2 ^ n) hp']
      by_cases hk : k < 2 ^ n
      · have e1 : decide (k < 2 ^ n) = true := by simpa using hk
        have e2 : decide (k < 2 ^ (n + 1)) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e3 : decide (k ≥ 2 ^ n) = false := by
          simp only [decide_eq_false_iff_not]
          omega
        rw [e1, e2, e3]
        simp
      · have hb : (k - 2 ^ n).testBit p = k.testBit p := by
          rw [← Nat.testBit_two_pow_add_gt hp' (k - 2 ^ n)]
          congr 1
          omega
        have e1 : decide (k < 2 ^ n) = false := by simpa using hk
        have e3 : decide (k ≥ 2 ^ n) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e4 : decide (k - 2 ^ n < 2 ^ n) = decide (k < 2 ^ (n + 1)) := by
          apply decide_eq_decide.mpr
          omega
        rw [e1, e3, e4, hb]
        simp

def orTab (L : List (ℕ × ℕ)) (l : ℕ) : ℕ :=
  L.foldr (fun q acc => cond (q.2 == l) (tab 16 q.1 ||| acc) acc) 0

theorem orTab_bit (l k : ℕ) : ∀ L : List (ℕ × ℕ), (orTab L l).testBit k = true →
    ∃ q ∈ L, q.2 = l ∧ (tab 16 q.1).testBit k = true := by
  intro L
  induction L with
  | nil => intro h; simp [orTab] at h
  | cons q L ih =>
    intro h
    by_cases hq : q.2 = l
    · have e : orTab (q :: L) l = tab 16 q.1 ||| orTab L l := by
        simp [orTab, hq]
      rw [e, Nat.testBit_lor, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨q, List.mem_cons_self, hq, h⟩
      · obtain ⟨q', hq', h1, h2⟩ := ih h
        exact ⟨q', List.mem_cons_of_mem _ hq', h1, h2⟩
    · have e : orTab (q :: L) l = orTab L l := by
        simp [orTab, hq]
      rw [e] at h
      obtain ⟨q', hq', h1, h2⟩ := ih h
      exact ⟨q', List.mem_cons_of_mem _ hq', h1, h2⟩

def wf (i : ℕ) : ℕ := if i < 16 then tab 16 i else (2 ^ 2 ^ 16 - 1) ^^^ orTab Inc (i - 16)

def W : List ℕ := (List.range 32).map wf

theorem W_getD (i : ℕ) : W.getD i 0 = if i < 32 then wf i else 0 := by
  unfold W
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem W_len : W.length = 32 := by simp [W]

theorem G_len : G.length = 302 := by decide +kernel

set_option maxRecDepth 100000 in
theorem false_side0 :
    rd 334 (evR (fun a b => a &&& b) (fun a b => a ||| b) G 32 W.reverse) 333 = 0 := by
  decide +kernel

theorem false_side : (G.foldl stpN W).getD 333 0 = 0 := by
  have h := fold_getD (fun a b => a &&& b) (fun a b => a ||| b) G W 333
  rw [W_len, G_len] at h
  exact h.trans false_side0

def rowNum (L : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  L.foldr (fun q acc => 2 * acc + (if i = q.1 ∨ i = 16 + q.2 then 1 else 0)) 0

theorem rowNum_bit (i : ℕ) : ∀ (L : List (ℕ × ℕ)) (j : ℕ) (hj : j < L.length),
    (rowNum L i).testBit j = decide (i = (L[j]).1 ∨ i = 16 + (L[j]).2) := by
  intro L
  induction L with
  | nil => intro j hj; simp at hj
  | cons q L ih =>
    intro j hj
    have e : rowNum (q :: L) i = 2 * rowNum L i + (if i = q.1 ∨ i = 16 + q.2 then 1 else 0) := rfl
    rw [e]
    cases j with
    | zero =>
      rw [Nat.testBit_zero]
      by_cases hc : i = q.1 ∨ i = 16 + q.2
      · simp only [List.getElem_cons_zero, if_pos hc, decide_eq_true hc, decide_eq_true_eq]
        omega
      · simp only [List.getElem_cons_zero, if_neg hc, decide_eq_false hc, decide_eq_false_iff_not]
        omega
    | succ j =>
      rw [Nat.testBit_succ, List.getElem_cons_succ, ← ih j (by simpa using hj)]
      congr 1
      split_ifs <;> omega

def TW : List ℕ := (List.range 32).map (rowNum Inc)

theorem TW_len : TW.length = 32 := by simp [TW]

set_option maxRecDepth 100000 in
theorem true_side0 :
    rd 334 (evR (fun a b => a &&& b) (fun a b => a ||| b) G 32 TW.reverse) 333 = 2 ^ 64 - 1 := by
  decide +kernel

theorem true_side : (G.foldl stpN TW).getD 333 0 = 2 ^ 64 - 1 := by
  have h := fold_getD (fun a b => a &&& b) (fun a b => a ||| b) G TW 333
  rw [TW_len, G_len] at h
  exact h.trans true_side0

theorem Inc_len : Inc.length = 64 := by decide +kernel

theorem Inc_lt : ∀ q ∈ Inc, q.1 < 16 ∧ q.2 < 16 := by decide +kernel

theorem monoC0 : ∀ g ∈ C0.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  simp only [C0, List.mem_map] at hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := hg
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem len : C0.gates.length = 302 := by
  show (G.map toGate).length = 302
  rw [List.length_map, G_len]

set_option maxRecDepth 100000 in
theorem readsG : ∀ j < 302, (G.getD j (false, 0, 0)).2.1 < 32 + j ∧ (G.getD j (false, 0, 0)).2.2 < 32 + j := by
  decide +kernel

theorem readsBack : PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C0 := by
  intro j hj i hi
  rw [len] at hj
  have h := readsG j hj
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt C0 j = toGate (G.getD j (false, 0, 0)) := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    show (G.map toGate).getD j _ = _
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [G_len]; exact hj)]
    rfl
  rw [e] at hi
  simp only [toGate, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h.1
  · exact h.2

theorem deg_bridge : ∀ (gs : List (Bool × ℕ × ℕ)) (d : List ℕ),
    (gs.map toGate).foldl (fun d g => d ++ [g.lineDegree d]) d
      = gs.foldl (stpG (fun a b => a + b) (fun a b => max a b)) d := by
  intro gs
  induction gs with
  | nil => intro d; rfl
  | cons g gs ih =>
    intro d
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 2
    obtain ⟨b, i, j⟩ := g
    cases b <;> simp [Gate.lineDegree, toGate, stpG]

def D0 : List ℕ := List.replicate 16 0 ++ List.replicate 16 1

theorem D0_eq : ((List.range (16 + 16)).map fun i => if i ∈ Finset.Ico 16 (16 + 16) then 1 else 0) = D0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem deg0 : rd 334 (evR (fun a b => a + b) (fun a b => max a b) G 32 D0.reverse) 333 ≤ 3 := by
  decide +kernel

theorem lineDeg : HasLineDegree (16 + 16) (Finset.Ico 16 (16 + 16)) C0 3 := by
  unfold HasLineDegree Circuit.lineDeg Circuit.lineDegrees
  rw [D0_eq]
  show ((G.map toGate).foldl (fun d g => d ++ [g.lineDegree d]) D0).getD 333 0 ≤ 3
  rw [deg_bridge, fold_getD, G_len]
  exact deg0

theorem inp_getD (x y : Fin 16 → Bool) (i : ℕ) :
    (List.ofFn x ++ List.ofFn y).getD i false =
      if h : i < 16 then x ⟨i, h⟩ else if h2 : i - 16 < 16 then y ⟨i - 16, h2⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < 16
  · rw [List.getElem?_append_left (by simpa using h), dif_pos h, ← List.getD_eq_getElem?_getD,
      ofFn_getD, dif_pos h]
  · rw [List.getElem?_append_right (by simpa using h), dif_neg h, ← List.getD_eq_getElem?_getD,
      ofFn_getD]
    simp

theorem eval_tb (k : ℕ) (V : List ℕ) :
    (C0.gates.foldl stp (V.map fun v => v.testBit k)).getD 333 false
      = ((G.foldl stpN V).getD 333 0).testBit k := by
  show ((G.map toGate).foldl stp (V.map fun v => v.testBit k)).getD 333 false = _
  rw [bridge, getD_tb]

theorem main (x y : Fin 16 → Bool) :
    C0.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16,
      ((p : ℕ), (l : ℕ)) ∈ Inc ∧ x p = true ∧ y l = true) := by
  rw [eval_eq]
  by_cases h : ∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ Inc ∧ x p = true ∧ y l = true
  · rw [decide_eq_true h]
    obtain ⟨p, l, hm, hx, hy⟩ := h
    obtain ⟨j, hj, hjq⟩ := List.mem_iff_getElem.mp hm
    have hj64 : j < 64 := by rw [← Inc_len]; exact hj
    have h2 := eval_tb j TW
    rw [true_side, Nat.testBit_two_pow_sub_one, decide_eq_true hj64] at h2
    refine mono C0.gates _ _ (by simp [TW]) monoC0 ?_ _ h2
    intro i hi
    rw [getD_tb, List.getD_eq_getElem?_getD] at hi
    rw [inp_getD]
    by_cases hi32 : i < 32
    · rw [show TW = (List.range 32).map (rowNum Inc) from rfl, List.getElem?_map,
        List.getElem?_range hi32] at hi
      simp only [Option.map_some, Option.getD_some] at hi
      rw [rowNum_bit i Inc j hj, hjq] at hi
      by_cases hc : i = p.1 ∨ i = 16 + l.1
      · rcases hc with hc | hc
        · have hp := p.2
          rw [dif_pos (by omega)]
          have hg : ∀ (m : ℕ) (hm : m < 16), m = p.1 → x ⟨m, hm⟩ = true := by
            intro m hm e
            subst e
            exact hx
          exact hg _ _ hc
        · have hl := l.2
          rw [dif_neg (by omega), dif_pos (by omega)]
          have hg : ∀ (m : ℕ) (hm : m < 16), m = l.1 → y ⟨m, hm⟩ = true := by
            intro m hm e
            subst e
            exact hy
          exact hg _ _ (by omega)
      · simp [hc] at hi
    · rw [List.getElem?_eq_none (by simpa [TW] using hi32)] at hi
      simp at hi
  · rw [decide_eq_false h]
    by_contra hcon
    have hcon' : (C0.gates.foldl stp (List.ofFn x ++ List.ofFn y)).getD C0.output false = true := by
      simpa using hcon
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, k < 2 ^ 16 ∧ ∀ (i : ℕ) (hi : i < 16), k.testBit i = x ⟨i, hi⟩ :=
      ⟨Nat.ofBits x, Nat.ofBits_lt_two_pow x, fun i hi => Nat.testBit_ofBits_lt x i hi⟩
    have h3 := mono C0.gates _ (W.map fun v => v.testBit k) (by simp [W]) monoC0 ?_ _ hcon'
    · have h4 := eval_tb k W
      rw [false_side] at h4
      rw [show C0.output = 333 from rfl, h4] at h3
      simp at h3
    · intro i hi
      rw [inp_getD] at hi
      rw [getD_tb, W_getD]
      by_cases h16 : i < 16
      · rw [dif_pos h16] at hi
        rw [if_pos (by omega), wf, if_pos h16, tab_bit 16 i k h16, hk2 i h16, hi]
        simpa using hk1
      · rw [dif_neg h16] at hi
        by_cases h32 : i - 16 < 16
        · rw [dif_pos h32] at hi
          rw [if_pos (by omega), wf, if_neg h16, Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
          have e1 : decide (k < 2 ^ 16) = true := by simpa using hk1
          have e2 : (orTab Inc (i - 16)).testBit k = false := by
            by_contra hne
            have hne' : (orTab Inc (i - 16)).testBit k = true := by simpa using hne
            obtain ⟨q, hq, hq2, hq3⟩ := orTab_bit (i - 16) k Inc hne'
            have hlt := Inc_lt q hq
            rw [tab_bit 16 q.1 k hlt.1, hk2 q.1 hlt.1] at hq3
            apply h
            refine ⟨⟨q.1, hlt.1⟩, ⟨i - 16, h32⟩, ?_, ?_, hi⟩
            · have : ((q.1, i - 16) : ℕ × ℕ) = q := by rw [← hq2]
              rw [this]
              exact hq
            · have hq4 : k < 65536 ∧ x ⟨q.1, hlt.1⟩ = true := by simpa using hq3
              exact hq4.2
          rw [e1, e2]
          rfl
        · rw [dif_neg h32] at hi
          simp at hi

set_option maxRecDepth 100000 in
theorem full : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 62] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 80] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 86] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [94, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 104] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 106] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [109, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [111, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [112, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [114, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [115, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [117, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 120] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 122] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 124] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 126] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [61, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [128, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [129, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [130, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [131, 83] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [132, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [133, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [134, 101] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [135, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [136, 105] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [137, 107] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [138, 121] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [139, 123] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [140, 125] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [141, 127] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [143, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [153, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [158, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 145] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 158] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [163, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [173, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [178, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 165] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [183, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [184, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [186, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [187, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [189, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [190, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [192, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [193, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [196, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [194, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [198, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [199, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [203, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [204, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [206, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [207, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [209, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [210, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [212, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [213, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [216, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [214, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [218, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [219, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [159, 161] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [223, 162] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 156] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [225, 179] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [226, 181] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 182] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 176] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [229, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [230, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [231, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 196] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [233, 219] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [234, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 216] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [238, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [239, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [245, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [249, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [253, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [255, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 256] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [259, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 261] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [263, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [264, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [265, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 266] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [268, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [269, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [270, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 271] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [273, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [274, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [275, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 276] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [278, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [279, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [280, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 281] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [283, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [284, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [285, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 286] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [288, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [289, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [290, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 291] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [293, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [294, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [295, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 296] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [298, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [299, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [300, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 301] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [303, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [304, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [305, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 306] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [308, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [309, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [310, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 311] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [313, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [314, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [315, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 316] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [242, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [318, 252] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [319, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [320, 262] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [321, 267] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [322, 272] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [323, 277] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [324, 282] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [325, 287] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [326, 292] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [327, 297] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [328, 302] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [329, 307] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [330, 312] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [331, 317] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 332] }], output := 333 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 302 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (16 + 16) (Finset.Ico 16 (16 + 16)) C 3 ∧
  ∀ (x y : Fin 16 → Bool), C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) := by
  intro C hC
  have hC' : C = C0 := hC
  clear hC
  subst hC'
  exact ⟨len, readsBack, lineDeg, main⟩

end PEqualNP.Outside.L_meta_1700

theorem PEqualNP.Outside.L_meta_1700 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 26] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 29] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [28, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [58, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 62] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 56] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [53, 59] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 80] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [70, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [73, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 86] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [88, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [94, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [90, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 104] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [93, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 106] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [109, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [111, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [112, 44] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [114, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [115, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 38] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [117, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 120] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 122] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 116] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 124] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [113, 119] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 126] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [61, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [128, 65] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [129, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [130, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [131, 83] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [132, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [133, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [134, 101] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [135, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [136, 105] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [137, 107] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [138, 121] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [139, 123] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [140, 125] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [141, 127] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [143, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [153, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 151] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [158, 148] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 145] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 158] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 154] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [163, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [173, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 171] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [178, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 165] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 174] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [183, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [184, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [186, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [187, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [189, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [190, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [192, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [193, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [196, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [194, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [198, 188] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [199, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [185, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [195, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [203, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [204, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [206, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [207, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [209, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [210, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [212, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [213, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [216, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [214, 211] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [218, 208] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [219, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [205, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [215, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [159, 161] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [223, 162] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 156] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [225, 179] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [226, 181] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 182] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 176] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [229, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [230, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [231, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 196] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [233, 219] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [234, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 216] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [238, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [239, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [245, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [249, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [253, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [255, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 256] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [259, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 261] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [263, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [264, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [265, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 266] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [268, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [269, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [270, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 271] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [273, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [274, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [275, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 276] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [278, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [279, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [280, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 281] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [283, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [284, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [285, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 286] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [288, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [289, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [290, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 291] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [293, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [294, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [295, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 296] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [298, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [299, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [300, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 301] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [303, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [304, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [305, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 306] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [308, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [309, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [310, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 311] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [237, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [313, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [314, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [315, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 316] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [242, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [318, 252] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [319, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [320, 262] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [321, 267] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [322, 272] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [323, 277] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [324, 282] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [325, 287] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [326, 292] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [327, 297] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [328, 302] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [329, 307] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [330, 312] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [331, 317] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 332] }], output := 333 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 302 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (16 + 16) (Finset.Ico 16 (16 + 16)) C 3 ∧
  ∀ (x y : Fin 16 → Bool), C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) := by
  exact PEqualNP.Outside.L_meta_1700.full
