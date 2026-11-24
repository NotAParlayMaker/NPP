import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1748_aux

open PEqualNP.CircuitLowerBounds

def pat (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if i = n then (2 ^ (2 ^ n) - 1) <<< (2 ^ n) else pat i n ||| (pat i n <<< (2 ^ n))

theorem pat_spec (i : ℕ) : ∀ n j, (pat i n).testBit j = (decide (j < 2 ^ n) && j.testBit i)
  | 0, j => by
    cases j <;> simp [pat]
  | n + 1, j => by
    have ih := pat_spec i n
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    rcases Nat.lt_or_ge j (2 ^ n) with hj | hj
    · have hj2 : j < 2 ^ (n + 1) := by omega
      by_cases hi : i = n
      · subst hi
        simp [pat, Nat.testBit_lt_two_pow hj]
        intro h; omega
      · simp [pat, hi, ih, hj, hj2]
    · obtain ⟨t, rfl⟩ : ∃ t, j = 2 ^ n + t := ⟨j - 2 ^ n, by omega⟩
      have e : 2 ^ n + t - 2 ^ n = t := by omega
      by_cases hi : i = n
      · subst hi
        simp only [pat, ite_true, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, e,
          Nat.testBit_two_pow_add_eq]
        rcases Nat.lt_or_ge t (2 ^ i) with ht | ht
        · simp [Nat.testBit_lt_two_pow ht, ht, hp]
        · have : ¬ (2 ^ i + t < 2 ^ (i + 1)) := by omega
          simp [this]
          omega
      · simp only [pat, hi, ite_false, Nat.testBit_or, Nat.testBit_shiftLeft, ih, e]
        rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
        · rw [Nat.testBit_two_pow_add_gt hlt]
          have : ¬ (2 ^ n + t < 2 ^ n) := by omega
          simp only [this, decide_false, Bool.false_and, Bool.false_or, ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and]
          congr 1
          simp only [decide_eq_decide]
          omega
        · rcases Nat.lt_or_ge t (2 ^ n) with ht | ht
          · have h1 : 2 ^ n + t < 2 ^ i := by
              have : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hgt
              omega
            have h2 : t < 2 ^ i := by omega
            simp [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
          · have : ¬ (2 ^ n + t < 2 ^ n) := by omega
            have h3 : ¬ (t < 2 ^ n) := by omega
            have h4 : ¬ (2 ^ n + t < 2 ^ (n + 1)) := by omega
            simp [this, h3, h4]


def gm (W : List ℕ) (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [a, b] => W.getD a 0 &&& W.getD b 0
  | GateOp.or, [a, b] => W.getD a 0 ||| W.getD b 0
  | _, _ => 0

def sim : List ℕ → List Gate → List ℕ
  | W, [] => W
  | W, g :: gs => sim (W ++ [gm W g]) gs

def Ag (j : ℕ) (W : List ℕ) (w : List Bool) : Prop :=
  W.length = w.length ∧ ∀ i, (W.getD i 0).testBit j = w.getD i false

theorem gm_spec (j : ℕ) (W : List ℕ) (w : List Bool) (h : Ag j W w) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    (gm W g).testBit j = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hl
  rcases hop with rfl | rfl <;> simp only [gm, GateOp.eval, List.map, Nat.testBit_and, Nat.testBit_or, h.2] <;> simp

theorem step (j : ℕ) (W : List ℕ) (w : List Bool) (h : Ag j W w) (m : ℕ) (b : Bool)
    (hb : m.testBit j = b) : Ag j (W ++ [m]) (w ++ [b]) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp [h1], fun i => ?_⟩
  rcases lt_trichotomy i W.length with hi | rfl | hi
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega), h2]
  · rw [List.getD_append_right _ _ _ _ le_rfl, h1, List.getD_append_right _ _ _ _ le_rfl]
    simp [hb]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem sim_spec (j : ℕ) : ∀ (gs : List Gate) (W : List ℕ) (w : List Bool), Ag j W w →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    Ag j (sim W gs) (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
  | [], W, w, h, _ => by simpa [sim] using h
  | g :: gs, W, w, h, hs => by
    simp only [sim, List.foldl_cons]
    exact sim_spec j gs _ _ (step j W w h _ _ (gm_spec j W w h g (hs g (by simp))))
      (fun g' hg' => hs g' (by simp [hg']))

def mk : ℕ → ℕ → List Bool → ℕ
  | _, m, [] => m
  | k, m, b :: bs => mk (k + 1) (if b then m ||| 2 ^ k else m) bs

def Inv (w : List Bool) (m : ℕ) : Prop :=
  (∀ i, w.getD i false = m.testBit i) ∧ (∀ i, w.length ≤ i → m.testBit i = false)

theorem step_inv (w : List Bool) (m : ℕ) (b : Bool) (h : Inv w m) :
    Inv (w ++ [b]) (if b then m ||| 2 ^ w.length else m) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro i
    rcases lt_trichotomy i w.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ hi, h1]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow] <;> omega
    · rw [List.getD_append_right _ _ _ _ le_rfl]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow, h2]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      cases b <;> simp [Nat.testBit_or, h2 i hi.le, Nat.testBit_two_pow] <;> omega
  · intro i hi
    simp at hi
    cases b <;> simp [Nat.testBit_or, h2 i (by omega), Nat.testBit_two_pow] <;> omega

theorem mk_spec : ∀ (bs w : List Bool) (m : ℕ), Inv w m → Inv (w ++ bs) (mk w.length m bs)
  | [], w, m, h => by simpa [mk] using h
  | b :: bs, w, m, h => by
    have := mk_spec bs (w ++ [b]) _ (step_inv w m b h)
    simpa [mk] using this

def chk (n : ℕ) : List Gate → Bool
  | [] => true
  | g :: gs => g.inputs.all (fun i => decide (i < n)) && chk (n + 1) gs

theorem chk_spec : ∀ (gs : List Gate) (n : ℕ), chk n gs = true →
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | g :: gs, n, h, 0, _, i, hi => by
    simp only [chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    simpa using h.1 i (by simpa using hi)
  | g :: gs, n, h, j + 1, hj, i, hi => by
    simp only [chk, Bool.and_eq_true] at h
    have := chk_spec gs (n + 1) h.2 j (by simpa using hj) i (by simpa using hi)
    omega

def S : Finset (Fin 7) := {0, 1, 3}

def ps : List (ℕ × ℕ) :=
  (List.finRange 7).flatMap fun p =>
    ((List.finRange 7).filter fun (l : Fin 7) => decide (p - l ∈ S)).map fun l => ((p : ℕ), 7 + (l : ℕ))

def tm : List (ℕ × ℕ) → ℕ
  | [] => 0
  | q :: r => (pat q.1 14 &&& pat q.2 14) ||| tm r

theorem tm_spec (j : ℕ) : ∀ qs : List (ℕ × ℕ),
    (tm qs).testBit j = qs.any (fun q => (pat q.1 14).testBit j && (pat q.2 14).testBit j)
  | [] => by simp [tm]
  | q :: r => by simp [tm, tm_spec j r]

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem isAO_spec (o : GateOp) (h : isAO o = true) : o = GateOp.and ∨ o = GateOp.or := by
  cases o <;> simp_all [isAO]

theorem shp_spec (gs : List Gate) (h : gs.all (fun g => isAO g.op && g.inputs.length == 2) = true) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨isAO_spec _ this.1, this.2⟩

def W0 : List ℕ := (List.range 14).map fun i => pat i 14

theorem main_eq : (sim W0 ([{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [60, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [61, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [66, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [73, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [79, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [81, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [84, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [85, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [90, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [93, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [96, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [99, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [102, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [103, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [104, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [105, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [107, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [109, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [110, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [111, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [114, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [115, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [116, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [117, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [119, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [120, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [121, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [122, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [128, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [133, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 106] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 112] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 118] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 124] }])).getD 138 0 = tm ps := by
  set_option maxRecDepth 100000 in decide +kernel

end PEqualNP.Outside.L_meta_1748_aux

theorem PEqualNP.Outside.L_meta_1748 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [60, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [61, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [66, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [73, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [79, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [81, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [84, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [85, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [90, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [93, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [96, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [99, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [102, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [103, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [104, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [105, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [107, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [109, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [110, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [111, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [114, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [115, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [116, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [117, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [119, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [120, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [121, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [122, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [128, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [133, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 106] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 112] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 118] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 124] }], output := 138 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 125 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (7 + 7) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  ∀ (x y : Fin 7 → Bool), C.eval (List.ofFn x ++ List.ofFn y)
     = decide (∃ p : Fin 7, ∃ l : Fin 7, p - l ∈ ({0, 1, 3} : Finset (Fin 7)) ∧ x p = true ∧ y l = true) := by
  intro C hC
  subst hC
  have hsh : ∀ g ∈ ([{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 30] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [37, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [43, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [51, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [54, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [55, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [60, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [61, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [63, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [66, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [67, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [69, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [72, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [73, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [75, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [78, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [79, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [81, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [84, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [85, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [87, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [90, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [91, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [93, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [96, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [97, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [99, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [102, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [103, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [104, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [105, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [107, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [109, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [110, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [111, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [114, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [115, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [116, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [117, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [119, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [120, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [121, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [122, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [128, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [133, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 106] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 112] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 118] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 124] }] : List PEqualNP.CircuitLowerBounds.Gate), (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2 := by
    exact PEqualNP.Outside.L_meta_1748_aux.shp_spec _ (by decide +kernel)
  refine ⟨rfl, ?_, hsh, ?_⟩
  · exact PEqualNP.Outside.L_meta_1748_aux.chk_spec _ _ (by decide +kernel)
  · intro x y
    have hL : (List.ofFn x ++ List.ofFn y).length = 14 := by simp
    have hI := PEqualNP.Outside.L_meta_1748_aux.mk_spec (List.ofFn x ++ List.ofFn y) [] 0 ⟨by simp, by simp⟩
    simp only [List.nil_append, List.length_nil] at hI
    have hj : PEqualNP.Outside.L_meta_1748_aux.mk 0 0 (List.ofFn x ++ List.ofFn y) < 2 ^ 14 :=
      Nat.lt_pow_two_of_testBit _ (fun i hi => hI.2 i (by omega))
    have hA : PEqualNP.Outside.L_meta_1748_aux.Ag (PEqualNP.Outside.L_meta_1748_aux.mk 0 0 (List.ofFn x ++ List.ofFn y))
        PEqualNP.Outside.L_meta_1748_aux.W0 (List.ofFn x ++ List.ofFn y) := by
      refine ⟨by simp [PEqualNP.Outside.L_meta_1748_aux.W0], fun i => ?_⟩
      rcases Nat.lt_or_ge i 14 with hi | hi
      · rw [hI.1 i]
        have hw : PEqualNP.Outside.L_meta_1748_aux.W0.getD i 0 = PEqualNP.Outside.L_meta_1748_aux.pat i 14 := by
          simp [PEqualNP.Outside.L_meta_1748_aux.W0, hi]
        rw [hw, PEqualNP.Outside.L_meta_1748_aux.pat_spec]
        simp only [hj, decide_true, Bool.true_and]
      · rw [List.getD_eq_default _ _ (by simp [PEqualNP.Outside.L_meta_1748_aux.W0]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
        simp
    have hS := (PEqualNP.Outside.L_meta_1748_aux.sim_spec _ _ _ _ hA hsh).2 138
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [← hS, PEqualNP.Outside.L_meta_1748_aux.main_eq, PEqualNP.Outside.L_meta_1748_aux.tm_spec]
    have hx : ∀ p : Fin 7, (List.ofFn x ++ List.ofFn y).getD (p : ℕ) false = x p := by
      intro p
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have hy : ∀ l : Fin 7, (List.ofFn x ++ List.ofFn y).getD (7 + (l : ℕ)) false = y l := by
      intro l
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have hb : ∀ p : Fin 7, (PEqualNP.Outside.L_meta_1748_aux.mk 0 0 (List.ofFn x ++ List.ofFn y)).testBit (p : ℕ) = x p := by
      intro p
      rw [← hI.1, hx]
    have hc : ∀ l : Fin 7, (PEqualNP.Outside.L_meta_1748_aux.mk 0 0 (List.ofFn x ++ List.ofFn y)).testBit (7 + (l : ℕ)) = y l := by
      intro l
      rw [← hI.1, hy]
    simp only [PEqualNP.Outside.L_meta_1748_aux.ps, PEqualNP.Outside.L_meta_1748_aux.pat_spec, hj,
      decide_true, Bool.true_and, List.any_flatMap, List.any_map, Function.comp_def, hb, hc]
    generalize PEqualNP.Outside.L_meta_1748_aux.mk 0 0 (List.ofFn x ++ List.ofFn y) = m at hb hc ⊢
    rw [Bool.eq_iff_iff]
    simp [List.any_eq_true, PEqualNP.Outside.L_meta_1748_aux.S]
    simp only [hc]
