import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18183_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- One evaluation step: the gate adds one wire. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (L : List Bool) (a : Bool) (w : ℕ) :
    (L ++ [a]).getD w false = if w = L.length then a else L.getD w false := by
  rcases lt_trichotomy w L.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ w = L.length := by omega
    have h2 : L.length ≤ w := by omega
    have h3 : (L ++ [a]).length ≤ w := by simp; omega
    simp [List.getD_eq_getElem?_getD, h1, List.getElem?_eq_none h2, List.getElem?_eq_none h3]

theorem oneEach_getD (N : ℕ) (u v : Fin N) (i : ℕ) :
    (oneEach u v).getD i false = (decide (i = u.val) || decide (i = N + v.val)) := by
  unfold oneEach
  by_cases h : i < N
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    have h1 : i ≠ N + v.val := by omega
    simp [h, h1, Fin.ext_iff]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using h)]
    have h1 : i ≠ u.val := by have := u.isLt; omega
    by_cases h2 : i - N < N
    · simp [h2, h1, Fin.ext_iff]; omega
    · have h3 : i ≠ N + v.val := by have := v.isLt; omega
      simp [h2, h1, h3]

/-- Evaluation against a specification: if `val` is right on the inputs and every gate reads
earlier wires and satisfies its equation under `val`, then `val` is the value of every wire. -/
theorem spec (g : ℕ → Gate) (val : ℕ → Bool) (X : List Bool)
    (hX : ∀ w, w < X.length → X.getD w false = val w) (m : ℕ)
    (hin : ∀ t, t < m → ∀ i ∈ (g t).inputs, i < X.length + t)
    (hval : ∀ t, t < m → (g t).op.eval ((g t).inputs.map val) = val (X.length + t)) :
    (((List.range m).map g).foldl step X).length = X.length + m ∧
      ∀ w, w < X.length + m → (((List.range m).map g).foldl step X).getD w false = val w := by
  induction m with
  | zero => exact ⟨by simp, by simpa using hX⟩
  | succ m ih =>
    obtain ⟨hl, hw⟩ := ih (fun t ht => hin t (by omega)) (fun t ht => hval t (by omega))
    rw [List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    refine ⟨by rw [List.length_append, hl, List.length_singleton, Nat.add_assoc], fun w hw' => ?_⟩
    rw [getD_snoc, hl]
    split_ifs with h
    · subst h
      rw [← hval m (by omega)]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hw i (hin m (by omega) i hi)
    · exact hw w (by omega)

theorem or_dec (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] (h : (P ∨ Q) ↔ R) :
    (decide P || decide Q) = decide R := by
  rw [Bool.eq_iff_iff]; simpa using h

theorem and_dec (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] (h : (P ∧ Q) ↔ R) :
    (decide P && decide Q) = decide R := by
  rw [Bool.eq_iff_iff]; simpa using h

/-- Threshold two of the `m` values on wires `X ..`; gate `s` gives wire `B + s`. -/
def gateT (X B m s : ℕ) : Gate :=
  if s < m - 2 then ⟨GateOp.or, [if s = 0 then X else B + s - 1, X + s + 1]⟩
  else if s < 2 * m - 3 then
    ⟨GateOp.and, [if s = m - 2 then X else B + s + 1 - m, X + s + 3 - m]⟩
  else ⟨GateOp.or, [if s = 2 * m - 3 then B + m - 2 else B + s - 1, B + s + 2 - m]⟩

/-- The value of wire `w` of the threshold block at `B` when the values at `p` and `q` are on. -/
def thv (B m p q w : ℕ) : Bool :=
  if w < B + (m - 2) then decide (p + B ≤ w + 1 ∨ q + B ≤ w + 1)
  else if w < B + (2 * m - 3) then
    decide ((p + m + B < w + 3 ∧ q + m + B = w + 3) ∨ (q + m + B < w + 3 ∧ p + m + B = w + 3))
  else decide (p ≠ q ∧ p + 2 * m + B ≤ w + 5 ∧ q + 2 * m + B ≤ w + 5)

theorem thv1 (B m p q w : ℕ) (h : w < B + (m - 2)) :
    thv B m p q w = decide (p + B ≤ w + 1 ∨ q + B ≤ w + 1) := by
  unfold thv; split_ifs; rfl

theorem thv2 (B m p q w : ℕ) (h1 : B + (m - 2) ≤ w) (h2 : w < B + (2 * m - 3)) :
    thv B m p q w = decide ((p + m + B < w + 3 ∧ q + m + B = w + 3)
      ∨ (q + m + B < w + 3 ∧ p + m + B = w + 3)) := by
  unfold thv; split_ifs <;> first | omega | rfl

theorem thv3 (B m p q w : ℕ) (h1 : B + (2 * m - 3) ≤ w) (h2 : 3 ≤ m) :
    thv B m p q w = decide (p ≠ q ∧ p + 2 * m + B ≤ w + 5 ∧ q + 2 * m + B ≤ w + 5) := by
  unfold thv; split_ifs <;> first | omega | rfl

theorem thv_last (B m p q w : ℕ) (hm : 2 ≤ m) (hp : p < m) (hq : q < m) (hw : w + 6 = B + 3 * m) :
    thv B m p q w = decide (p ≠ q) := by
  unfold thv; split_ifs <;> first | omega | (rw [decide_eq_decide]; omega)

theorem thr_in (X B m s i : ℕ) (hm : 2 ≤ m) (hXB : X + m ≤ B) (hs : s < 3 * m - 5)
    (hi : i ∈ (gateT X B m s).inputs) : i < B + s := by
  unfold gateT at hi
  split_ifs at hi <;>
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi <;> omega

theorem thr_val (val : ℕ → Bool) (X B m p q : ℕ) (hm : 2 ≤ m)
    (hX : ∀ w, X ≤ w → w < X + m → val w = decide (p + X = w ∨ q + X = w))
    (hB : ∀ w, B ≤ w → w < B + (3 * m - 5) → val w = thv B m p q w) (s : ℕ)
    (hs : s < 3 * m - 5) :
    (gateT X B m s).op.eval ((gateT X B m s).inputs.map val) = val (B + s) := by
  rw [hB (B + s) (by omega) (by omega)]
  unfold gateT
  split_ifs <;>
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.or_false, Bool.and_true] <;>
    simp (disch := omega) only [hX, hB] <;>
    simp (disch := omega) only [thv1, thv2, thv3] <;>
    first
      | exact or_dec _ _ _ (by omega)
      | exact and_dec _ _ _ (by omega)

/-- Row chain, gate `t` gives wire `3 * N + t`: the OR of the cells `0 .. t / r + 1` of row
`t % r`. -/
def gateR (N r c t : ℕ) : Gate :=
  if t < r then ⟨GateOp.or, [2 * N + t * c, 2 * N + t * c + 1]⟩
  else ⟨GateOp.or, [3 * N + (t - r), 2 * N + (t % r * c + t / r + 1)]⟩

/-- Column chain, gate `t` gives wire `4 * N - r + t`: the OR of the cells `≤ t + c` in the
column of cell `t + c`. -/
def gateC (N r c t : ℕ) : Gate :=
  ⟨GateOp.or, [if t < c then 2 * N + t else 4 * N - r + (t - c), 2 * N + (t + c)]⟩

/-- Gate number `t` (it produces wire `2 * N + t`), `N = r * c`. -/
def gate (N r c t : ℕ) : Gate :=
  if t < N then ⟨GateOp.or, [t, N + t]⟩
  else if t < 2 * N - r then gateR N r c (t - N)
  else if t < 3 * N - r - c then gateC N r c (t - (2 * N - r))
  else if t < 3 * N + 2 * r - c - 5 then
    gateT (4 * N - 2 * r) (5 * N - r - c) r (t - (3 * N - r - c))
  else if t < 3 * N + 2 * r + 2 * c - 10 then
    gateT (5 * N - r - 2 * c) (5 * N + 2 * r - c - 5) c (t - (3 * N + 2 * r - c - 5))
  else ⟨GateOp.or, [5 * N + 2 * r - c - 6, 5 * N + 2 * r + 2 * c - 11]⟩

/-- The value of wire `w` on the input with left vertex `u` and right vertex `v`. -/
def val (N r c u v w : ℕ) : Bool :=
  if w < N then decide (w = u)
  else if w < 2 * N then decide (w = N + v)
  else if w < 3 * N then decide (u + 2 * N = w ∨ v + 2 * N = w)
  else if w < 4 * N - r then
    decide (((w - 3 * N) % r * c ≤ u ∧ u ≤ (w - 3 * N) % r * c + (w - 3 * N) / r + 1)
      ∨ ((w - 3 * N) % r * c ≤ v ∧ v ≤ (w - 3 * N) % r * c + (w - 3 * N) / r + 1))
  else if w < 5 * N - r - c then
    decide ((u + 4 * N ≤ w + r + c ∧ u % c = (w + r + c - 4 * N) % c)
      ∨ (v + 4 * N ≤ w + r + c ∧ v % c = (w + r + c - 4 * N) % c))
  else if w < 5 * N + 2 * r - c - 5 then thv (5 * N - r - c) r (u / c) (v / c) w
  else if w < 5 * N + 2 * r + 2 * c - 10 then thv (5 * N + 2 * r - c - 5) c (u % c) (v % c) w
  else decide (u / c ≠ v / c ∨ u % c ≠ v % c)

/-- The circuit: `3 * r * c + 2 * (r + c) - 9` gates, output the last wire. -/
def circ (r c : ℕ) : Circuit :=
  ⟨(List.range (3 * (r * c) + 2 * r + 2 * c - 9)).map (gate (r * c) r c),
    5 * (r * c) + 2 * r + 2 * c - 10⟩

theorem val1 (N r c u v w : ℕ) (h : w < N) : val N r c u v w = decide (w = u) := by
  unfold val; split_ifs; rfl

theorem val2 (N r c u v w : ℕ) (h1 : N ≤ w) (h2 : w < 2 * N) :
    val N r c u v w = decide (w = N + v) := by
  unfold val; split_ifs <;> first | omega | rfl

theorem val3 (N r c u v w : ℕ) (h1 : 2 * N ≤ w) (h2 : w < 3 * N) :
    val N r c u v w = decide (u + 2 * N = w ∨ v + 2 * N = w) := by
  unfold val; split_ifs <;> first | omega | rfl

theorem valR (N r c u v t : ℕ) (h1 : 2 * r ≤ N) (ht : t < N - r) :
    val N r c u v (3 * N + t) = decide ((t % r * c ≤ u ∧ u ≤ t % r * c + t / r + 1)
      ∨ (t % r * c ≤ v ∧ v ≤ t % r * c + t / r + 1)) := by
  unfold val; split_ifs <;> first | omega | rw [Nat.add_sub_cancel_left]

theorem valC (N r c u v t : ℕ) (h1 : 2 * r ≤ N) (h2 : 2 * c ≤ N) (ht : t < N - c) :
    val N r c u v (4 * N - r + t) = decide ((u ≤ t + c ∧ u % c = (t + c) % c)
      ∨ (v ≤ t + c ∧ v % c = (t + c) % c)) := by
  have e : 4 * N - r + t + r + c - 4 * N = t + c := by omega
  unfold val; split_ifs <;> first | omega | (rw [e, decide_eq_decide]; omega)

theorem val6 (N r c u v w : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (h1 : 2 * r ≤ N) (h2 : 2 * c ≤ N)
    (w1 : 5 * N - r - c ≤ w) (w2 : w < 5 * N - r - c + (3 * r - 5)) :
    val N r c u v w = thv (5 * N - r - c) r (u / c) (v / c) w := by
  unfold val; split_ifs <;> first | omega | rfl

theorem val7 (N r c u v w : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (h1 : 2 * r ≤ N) (h2 : 2 * c ≤ N)
    (w1 : 5 * N + 2 * r - c - 5 ≤ w) (w2 : w < 5 * N + 2 * r - c - 5 + (3 * c - 5)) :
    val N r c u v w = thv (5 * N + 2 * r - c - 5) c (u % c) (v % c) w := by
  unfold val; split_ifs <;> first | omega | rfl

theorem val8 (N r c u v w : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (h1 : 2 * r ≤ N) (h2 : 2 * c ≤ N)
    (w1 : 5 * N + 2 * r + 2 * c - 10 ≤ w) :
    val N r c u v w = decide (u / c ≠ v / c ∨ u % c ≠ v % c) := by
  unfold val; split_ifs <;> first | omega | rfl

theorem colstep (c x k : ℕ) :
    (x ≤ k + c ∧ x % c = (k + c) % c) ↔ ((x ≤ k ∧ x % c = k % c) ∨ x = k + c) := by
  rw [Nat.add_mod_right]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h : x ≤ k
    · exact Or.inl ⟨h, h2⟩
    · have h3 := Nat.le_of_dvd (by omega)
        (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h2))
      right; omega
  · rintro (⟨h1, h2⟩ | rfl)
    · exact ⟨by omega, h2⟩
    · exact ⟨le_refl _, by rw [Nat.add_mod_right]⟩

theorem colbase (c x k : ℕ) (h : k < c) : (x ≤ k ∧ x % c = k % c) ↔ x = k := by
  constructor
  · rintro ⟨h1, h2⟩
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h] at h2
  · rintro rfl
    exact ⟨le_refl _, rfl⟩

theorem row_iff (c u i : ℕ) (hc : 0 < c) : (i * c ≤ u ∧ u < i * c + c) ↔ u / c = i := by
  constructor
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 (by rw [Nat.add_mul, Nat.one_mul]; exact h2)
  · rintro rfl
    have h1 := Nat.div_add_mod u c
    have h2 := Nat.mod_lt u hc
    rw [Nat.mul_comm] at h1
    omega

theorem col_fin (r c x j : ℕ) (hr : 1 ≤ r) (hx : x < r * c) (hj : j < c) :
    (x ≤ r * c - c + j ∧ x % c = (r * c - c + j) % c) ↔ x % c = j := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have e : (r' + 1) * c - c + j = r' * c + j := by rw [Nat.add_mul, Nat.one_mul]; omega
  rw [e, Nat.mul_add_mod', Nat.mod_eq_of_lt hj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have h1 := Nat.div_add_mod x c
    have h2 : x / c < r' + 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
    have h3 := Nat.mul_le_mul_left c (Nat.le_of_lt_succ h2)
    rw [Nat.mul_comm c r'] at h3
    omega

theorem ne_iff (c u v : ℕ) : (u / c ≠ v / c ∨ u % c ≠ v % c) ↔ u ≠ v := by
  constructor
  · rintro h rfl
    simp at h
  · intro h
    by_contra h'
    obtain ⟨a, b⟩ := not_or.mp h'
    apply h
    rw [← Nat.div_add_mod u c, ← Nat.div_add_mod v c, not_not.mp a, not_not.mp b]

/-- The row values: wire `4 * N - 2 * r + i` is the OR of row `i`. -/
theorem valRf (N r c u v w : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hN : N = r * c)
    (w1 : 4 * N - 2 * r ≤ w) (w2 : w < 4 * N - 2 * r + r) :
    val N r c u v w = decide (u / c + (4 * N - 2 * r) = w ∨ v / c + (4 * N - 2 * r) = w) := by
  have h1 : 2 * r ≤ N := by rw [hN, Nat.mul_comm 2 r]; exact Nat.mul_le_mul_left r hc
  have e0 : r * (c - 2) = N - 2 * r := by rw [Nat.mul_sub, hN]; omega
  obtain ⟨i, rfl⟩ : ∃ i, w = 3 * N + (r * (c - 2) + i) := ⟨w - (4 * N - 2 * r), by omega⟩
  have hi : i < r := by omega
  rw [valR N r c u v _ h1 (by omega), Nat.mul_add_mod, Nat.mul_add_div (by omega),
    Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi, decide_eq_decide]
  have a := row_iff c u i (by omega)
  have b := row_iff c v i (by omega)
  omega

/-- The column values: wire `5 * N - r - 2 * c + j` is the OR of column `j`. -/
theorem valCf (N r c u v w : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hN : N = r * c) (hu : u < N)
    (hv : v < N) (w1 : 5 * N - r - 2 * c ≤ w) (w2 : w < 5 * N - r - 2 * c + c) :
    val N r c u v w
      = decide (u % c + (5 * N - r - 2 * c) = w ∨ v % c + (5 * N - r - 2 * c) = w) := by
  have h1 : 2 * r ≤ N := by rw [hN, Nat.mul_comm 2 r]; exact Nat.mul_le_mul_left r hc
  have h2 : 2 * c ≤ N := by rw [hN]; exact Nat.mul_le_mul_right c hr
  obtain ⟨j, rfl⟩ : ∃ j, w = 4 * N - r + (N - 2 * c + j) :=
    ⟨w - (5 * N - r - 2 * c), by omega⟩
  have hj : j < c := by omega
  have e : N - 2 * c + j + c = r * c - c + j := by omega
  rw [valC N r c u v _ h1 h2 (by omega), e, decide_eq_decide,
    col_fin r c u j (by omega) (hN ▸ hu) hj, col_fin r c v j (by omega) (hN ▸ hv) hj]
  omega

theorem gateR_in (N r c t i : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hN : N = r * c) (ht : t < N - r)
    (hi : i ∈ (gateR N r c t).inputs) : i < 3 * N + t := by
  have h3 : t % r * c + c ≤ r * c := by
    have := Nat.mul_le_mul_right c (Nat.mod_lt t (show 0 < r by omega))
    rwa [Nat.succ_mul] at this
  have h4 : t / r < c - 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega), Nat.sub_mul, Nat.mul_comm c r]; omega
  unfold gateR at hi
  split_ifs at hi with h <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  · rw [Nat.mod_eq_of_lt h] at h3
    omega
  · omega

theorem gateR_val (N r c u v t : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hN : N = r * c)
    (ht : t < N - r) :
    (gateR N r c t).op.eval ((gateR N r c t).inputs.map (val N r c u v))
      = val N r c u v (3 * N + t) := by
  have h1 : 2 * r ≤ N := by rw [hN, Nat.mul_comm 2 r]; exact Nat.mul_le_mul_left r hc
  have h3 : t % r * c + c ≤ r * c := by
    have := Nat.mul_le_mul_right c (Nat.mod_lt t (show 0 < r by omega))
    rwa [Nat.succ_mul] at this
  have h4 : t / r < c - 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega), Nat.sub_mul, Nat.mul_comm c r]; omega
  rw [valR N r c u v t h1 ht]
  unfold gateR
  split_ifs with h <;>
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
  · rw [Nat.mod_eq_of_lt h] at h3
    rw [val3 N r c u v _ (by omega) (by omega), val3 N r c u v _ (by omega) (by omega),
      Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
    exact or_dec _ _ _ (by omega)
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + r := ⟨t - r, by omega⟩
    have h5 := Nat.zero_le ((s + r) / r)
    have h6 := Nat.zero_le (s / r)
    rw [Nat.add_sub_cancel, valR N r c u v s h1 (by omega),
      val3 N r c u v (2 * N + _) (by omega) (by omega)]
    rw [Nat.add_mod_right, Nat.add_div_right s (by omega)]
    exact or_dec _ _ _ (by omega)

theorem gateC_in (N r c t i : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (h1 : 2 * r ≤ N) (h2 : 2 * c ≤ N)
    (ht : t < N - c) (hi : i ∈ (gateC N r c t).inputs) : i < 4 * N - r + t := by
  unfold gateC at hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  split_ifs at hi <;> omega

theorem gateC_val (N r c u v t : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (h1 : 2 * r ≤ N)
    (h2 : 2 * c ≤ N) (ht : t < N - c) :
    (gateC N r c t).op.eval ((gateC N r c t).inputs.map (val N r c u v))
      = val N r c u v (4 * N - r + t) := by
  rw [valC N r c u v t h1 h2 ht]
  unfold gateC
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
    Bool.or_false]
  rw [val3 N r c u v (2 * N + (t + c)) (by omega) (by omega)]
  split_ifs with h
  · rw [val3 N r c u v _ (by omega) (by omega)]
    refine or_dec _ _ _ ?_
    rw [colstep c u t, colstep c v t, colbase c u t h, colbase c v t h]
    omega
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + c := ⟨t - c, by omega⟩
    rw [Nat.add_sub_cancel, valC N r c u v s h1 h2 (by omega)]
    refine or_dec _ _ _ ?_
    rw [colstep c u (s + c), colstep c v (s + c)]
    omega

theorem gate_in (N r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hN : N = r * c) (t : ℕ)
    (ht : t < 3 * N + 2 * r + 2 * c - 9) (i : ℕ) (hi : i ∈ (gate N r c t).inputs) :
    i < 2 * N + t := by
  have h1 : 2 * r ≤ N := by rw [hN, Nat.mul_comm 2 r]; exact Nat.mul_le_mul_left r hc
  have h2 : 2 * c ≤ N := by rw [hN]; exact Nat.mul_le_mul_right c hr
  unfold gate at hi
  split_ifs at hi
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    omega
  · have := gateR_in N r c _ i hr hc hN (by omega) hi
    omega
  · have := gateC_in N r c _ i hr hc h1 h2 (by omega) hi
    omega
  · have := thr_in _ _ _ _ i hr (by omega) (by omega) hi
    omega
  · have := thr_in _ _ _ _ i hc (by omega) (by omega) hi
    omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    omega

theorem gate_val (N r c u v : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hN : N = r * c) (hu : u < N)
    (hv : v < N) (t : ℕ) (ht : t < 3 * N + 2 * r + 2 * c - 9) :
    (gate N r c t).op.eval ((gate N r c t).inputs.map (val N r c u v))
      = val N r c u v (2 * N + t) := by
  have h1 : 2 * r ≤ N := by rw [hN, Nat.mul_comm 2 r]; exact Nat.mul_le_mul_left r hc
  have h2 : 2 * c ≤ N := by rw [hN]; exact Nat.mul_le_mul_right c hr
  have hp : u / c < r := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hN]; exact hu)
  have hq : v / c < r := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hN]; exact hv)
  have hp' : u % c < c := Nat.mod_lt u (by omega)
  have hq' : v % c < c := Nat.mod_lt v (by omega)
  unfold gate
  split_ifs
  · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [val1 N r c u v t (by omega), val2 N r c u v _ (by omega) (by omega),
      val3 N r c u v _ (by omega) (by omega)]
    exact or_dec _ _ _ (by omega)
  · have := gateR_val N r c u v (t - N) hr hc hN (by omega)
    rwa [show 3 * N + (t - N) = 2 * N + t by omega] at this
  · have := gateC_val N r c u v (t - (2 * N - r)) hr hc h1 h2 (by omega)
    rwa [show 4 * N - r + (t - (2 * N - r)) = 2 * N + t by omega] at this
  · have := thr_val (val N r c u v) (4 * N - 2 * r) (5 * N - r - c) r (u / c) (v / c) hr
      (fun w w1 w2 => valRf N r c u v w hr hc hN w1 w2)
      (fun w w1 w2 => val6 N r c u v w hr hc h1 h2 w1 w2) (t - (3 * N - r - c)) (by omega)
    rwa [show 5 * N - r - c + (t - (3 * N - r - c)) = 2 * N + t by omega] at this
  · have := thr_val (val N r c u v) (5 * N - r - 2 * c) (5 * N + 2 * r - c - 5) c (u % c)
      (v % c) hc (fun w w1 w2 => valCf N r c u v w hr hc hN hu hv w1 w2)
      (fun w w1 w2 => val7 N r c u v w hr hc h1 h2 w1 w2) (t - (3 * N + 2 * r - c - 5))
      (by omega)
    rwa [show 5 * N + 2 * r - c - 5 + (t - (3 * N + 2 * r - c - 5)) = 2 * N + t by omega]
      at this
  · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [val6 N r c u v _ hr hc h1 h2 (by omega) (by omega),
      thv_last _ r _ _ _ hr hp hq (by omega),
      val7 N r c u v _ hr hc h1 h2 (by omega) (by omega),
      thv_last _ c _ _ _ hc hp' hq' (by omega), val8 N r c u v _ hr hc h1 h2 (by omega)]
    exact or_dec _ _ _ Iff.rfl

theorem main_thm : ∀ r c : ℕ, 2 ≤ r → 2 ≤ c → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (r * c) => decide (u ≠ v)) (3 * r * c + 2 * (r + c) - 9) := by
  intro r c hr hc
  have h1 : 2 * r ≤ r * c := by rw [Nat.mul_comm 2 r]; exact Nat.mul_le_mul_left r hc
  have h2 : 2 * c ≤ r * c := Nat.mul_le_mul_right c hr
  refine ⟨circ r c, ?_, ?_, ?_⟩
  · intro g hg
    simp only [circ, List.mem_map, List.mem_range] at hg
    obtain ⟨t, _, rfl⟩ := hg
    unfold gate gateR gateC gateT
    split_ifs <;> simp
  · show ((List.range _).map _).length ≤ _
    rw [List.length_map, List.length_range, Nat.mul_assoc]
    omega
  · intro u v
    have hu := u.isLt
    have hv := v.isLt
    have hlen : (oneEach u v).length = 2 * (r * c) := by simp [oneEach]; omega
    have hX : ∀ w, w < (oneEach u v).length →
        (oneEach u v).getD w false = val (r * c) r c u.val v.val w := by
      intro w hw
      rw [hlen] at hw
      rw [oneEach_getD]
      by_cases h : w < r * c
      · rw [val1 _ r c _ _ w h]; exact or_dec _ _ _ (by omega)
      · rw [val2 _ r c _ _ w (by omega) hw]; exact or_dec _ _ _ (by omega)
    have key := spec (gate (r * c) r c) (val (r * c) r c u.val v.val) (oneEach u v) hX
      (3 * (r * c) + 2 * r + 2 * c - 9)
      (by intro t ht i hi; rw [hlen]; exact gate_in (r * c) r c hr hc rfl t ht i hi)
      (by intro t ht; rw [hlen]; exact gate_val (r * c) r c u.val v.val hr hc rfl hu hv t ht)
    unfold Circuit.eval
    rw [wires_eq]
    simp only [circ]
    rw [key.2 (5 * (r * c) + 2 * r + 2 * c - 10) (by rw [hlen]; omega),
      val8 _ r c _ _ _ hr hc h1 h2 (le_refl _), decide_eq_decide, ne_iff]
    exact not_congr Fin.ext_iff.symm

end PEqualNP.Outside.L_meta_18183_aux

theorem PEqualNP.Outside.L_meta_18183 : ∀ r c : ℕ, 2 ≤ r → 2 ≤ c → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (r * c) => decide (u ≠ v)) (3 * r * c + 2 * (r + c) - 9) := by
  exact PEqualNP.Outside.L_meta_18183_aux.main_thm
