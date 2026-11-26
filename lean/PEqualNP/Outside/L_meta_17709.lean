import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17709_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepWire_len (gs : List Gate) :
    ∀ xs : List Bool, (gs.foldl stepWire xs).length = xs.length + gs.length := by
  induction gs with
  | nil => intro xs; simp
  | cons g gs ih =>
      intro xs
      simp only [List.foldl_cons, List.length_cons, ih, stepWire, List.length_append, List.length_nil]
      omega

theorem foldl_stepWire_getD_lt (gs : List Gate) :
    ∀ (xs : List Bool) (i : ℕ), i < xs.length →
      (gs.foldl stepWire xs).getD i false = xs.getD i false := by
  induction gs with
  | nil => intro xs i _; rfl
  | cons g gs ih =>
      intro xs i hi
      simp only [List.foldl_cons]
      rw [ih (stepWire xs g) i (by simp [stepWire]; omega)]
      exact List.getD_append _ _ _ _ hi

theorem getD_append_add (p w : List Bool) (i : ℕ) :
    (p ++ w).getD (i + p.length) false = w.getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
    rw [List.getD_eq_getElem _ _ hi]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def shiftGate (off : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (· + off)⟩

theorem foldl_shift (gs : List Gate) (p : List Bool) :
    ∀ w : List Bool, (gs.map (shiftGate p.length)).foldl stepWire (p ++ w) = p ++ gs.foldl stepWire w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
      intro w
      simp only [List.map_cons, List.foldl_cons, stepWire, shiftGate, List.map_map]
      have hmap : (g.inputs.map ((fun i => (p ++ w).getD i false) ∘ (· + p.length))) =
          g.inputs.map (fun i => w.getD i false) := by
        apply List.map_congr_left
        intro i _
        exact getD_append_add p w i
      rw [hmap, List.append_assoc]
      exact ih _

theorem getD_snoc_self (l : List Bool) (x : Bool) (n : ℕ) (h : l.length = n) :
    (l ++ [x]).getD n false = x := by
  subst h; simp

-- Stage 1: swap-fold 4n inputs into 2n virtual inputs (a, b) using 2n OR gates
def foldGate (n : ℕ) (k : Fin (2 * n)) : Gate :=
  if k.1 < n then ⟨.or, [k.1, 3 * n + k.1]⟩ else ⟨.or, [k.1, 2 * n + (k.1 - n)]⟩

def foldGates (n : ℕ) : List Gate :=
  List.ofFn (foldGate n)

def virtInput (n : ℕ) (u v : Fin (2 * n)) (k : Fin (2 * n)) : Bool :=
  if k.1 < n then decide (k.1 = u.1) || decide (n + k.1 = v.1)
  else decide (k.1 = u.1) || decide (k.1 - n = v.1)

theorem oneEach_len (n : ℕ) (u v : Fin (2 * n)) : (oneEach u v).length = 4 * n := by
  simp [oneEach]; omega

theorem oneEach_getD_left (n : ℕ) (u v : Fin (2 * n)) (i : ℕ) (hi : i < 2 * n) :
    (oneEach u v).getD i false = decide (i = u.1) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  by_cases h : i = u.1
  · have hfin : (⟨i, hi⟩ : Fin (2 * n)) = u := Fin.ext h
    rw [decide_eq_true hfin, decide_eq_true h]
  · have hfin : (⟨i, hi⟩ : Fin (2 * n)) ≠ u := fun he => h (congrArg Fin.val he)
    rw [decide_eq_false hfin, decide_eq_false h]

theorem oneEach_getD_right (n : ℕ) (u v : Fin (2 * n)) (i : ℕ) (hi1 : 2 * n ≤ i) (hi2 : i < 4 * n) :
    (oneEach u v).getD i false = decide (i - 2 * n = v.1) := by
  unfold oneEach
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp only [List.length_ofFn, List.getElem_ofFn]
  have hj : i - 2 * n < 2 * n := by omega
  by_cases h : i - 2 * n = v.1
  · have hfin : (⟨i - 2 * n, hj⟩ : Fin (2 * n)) = v := Fin.ext h
    rw [decide_eq_true hfin, decide_eq_true h]
  · have hfin : (⟨i - 2 * n, hj⟩ : Fin (2 * n)) ≠ v := fun he => h (congrArg Fin.val he)
    rw [decide_eq_false hfin, decide_eq_false h]

theorem foldl_foldGates_take (n : ℕ) (u v : Fin (2 * n)) :
    ∀ k, k ≤ 2 * n →
      ((foldGates n).take k).foldl stepWire (oneEach u v) =
        oneEach u v ++ (List.ofFn (virtInput n u v)).take k
  | 0, _ => by simp
  | k + 1, hk => by
      have ih := foldl_foldGates_take n u v k (by omega)
      have hlen_fg : (foldGates n).length = 2 * n := by simp [foldGates]
      have hlen_vi : (List.ofFn (virtInput n u v)).length = 2 * n := by simp
      rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      rw [List.take_succ_eq_append_getElem (by omega), ← List.append_assoc]
      simp only [stepWire, foldGates, List.getElem_ofFn, foldGate, virtInput]
      have hlen_oe : (oneEach u v).length = 4 * n := oneEach_len n u v
      by_cases hkn : k < n
      · simp only [hkn, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        rw [oneEach_getD_left n u v k (by omega), oneEach_getD_right n u v (3 * n + k) (by omega) (by omega)]
        have hsub : 3 * n + k - 2 * n = n + k := by omega
        rw [hsub]
      · simp only [hkn, ↓reduceIte, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        rw [oneEach_getD_left n u v k (by omega), oneEach_getD_right n u v (2 * n + (k - n)) (by omega) (by omega)]
        have hsub : 2 * n + (k - n) - 2 * n = k - n := by omega
        rw [hsub]

-- Stage 2: (5n - 7)-gate monotone2 circuit for single n x n crown on 2n inputs (a_0..a_{n-1}, b_0..b_{n-1})
def prefWire (n k : ℕ) : ℕ :=
  if k = 0 then n else 2 * n + (k - 1)

def sufWire (n m : ℕ) : ℕ :=
  if m = 0 then 2 * n - 1 else (3 * n - 2) + (m - 1)

def bnotWire (n i : ℕ) : ℕ :=
  if i = 0 then sufWire n (n - 2)
  else if i = n - 1 then prefWire n (n - 2)
  else (4 * n - 4) + (i - 1)

def orWire (n k : ℕ) : ℕ :=
  if k = 0 then 5 * n - 6 else (6 * n - 6) + (k - 1)

def pGates (n : ℕ) : List Gate :=
  List.ofFn (fun p : Fin (n - 2) => ⟨.or, [prefWire n p.1, n + p.1 + 1]⟩)

def sGates (n : ℕ) : List Gate :=
  List.ofFn (fun q : Fin (n - 2) => ⟨.or, [n + (n - 2 - q.1), sufWire n q.1]⟩)

def bGates (n : ℕ) : List Gate :=
  List.ofFn (fun r : Fin (n - 2) => ⟨.or, [prefWire n r.1, sufWire n (n - 3 - r.1)]⟩)

def tGates (n : ℕ) : List Gate :=
  List.ofFn (fun i : Fin n => ⟨.and, [i.1, bnotWire n i.1]⟩)

def oGates (n : ℕ) : List Gate :=
  List.ofFn (fun t : Fin (n - 1) => ⟨.or, [orWire n t.1, (5 * n - 6) + t.1 + 1]⟩)

def crownGates (n : ℕ) : List Gate :=
  pGates n ++ sGates n ++ bGates n ++ tGates n ++ oGates n

def crownCircuit (n : ℕ) : Circuit :=
  ⟨crownGates n, orWire n (n - 1)⟩

theorem crownCircuit_mono (n : ℕ) : Monotone2 (crownCircuit n) := by
  intro g hg
  simp only [crownCircuit, crownGates, List.mem_append, pGates, sGates, bGates, tGates, oGates, List.mem_ofFn] at hg
  rcases hg with ((((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem crownCircuit_size (n : ℕ) (hn : 2 ≤ n) : (crownCircuit n).size = 5 * n - 7 := by
  simp only [crownCircuit, Circuit.size, crownGates, List.length_append,
    pGates, sGates, bGates, tGates, oGates, List.length_ofFn]
  omega

theorem prefWire_lt (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n - 2) : prefWire n k < 2 * n + k := by
  unfold prefWire; split_ifs <;> omega

theorem sufWire_lt (n m : ℕ) (hn : 2 ≤ n) (hm : m ≤ n - 2) : sufWire n m < (3 * n - 2) + m := by
  unfold sufWire; split_ifs <;> omega

theorem bnotWire_lt (n i : ℕ) (hn : 2 ≤ n) (hi : i < n) : bnotWire n i < 5 * n - 6 := by
  unfold bnotWire
  split_ifs
  · have := sufWire_lt n (n - 2) hn le_rfl; omega
  · have := prefWire_lt n (n - 2) hn le_rfl; omega
  · omega

theorem orWire_lt (n k : ℕ) (hn : 2 ≤ n) (hk : k < n) : orWire n k < (6 * n - 6) + k := by
  unfold orWire; split_ifs <;> omega

theorem pGates_eval (n : ℕ) (hn : 2 ≤ n) (xs : List Bool) (hl : xs.length = 2 * n)
    (b : Fin n → Bool) (hb : ∀ j : Fin n, xs.getD (n + j.1) false = b j) :
    ∀ k, k ≤ n - 2 →
      (((pGates n).take k).foldl stepWire xs).getD (prefWire n k) false =
        decide (∃ j : Fin n, j.1 ≤ k ∧ b j = true)
  | 0, _ => by
      simp only [List.take_zero, List.foldl_nil, prefWire, ↓reduceIte]
      have h0 := hb ⟨0, by omega⟩
      simp only [Nat.add_zero] at h0
      rw [h0]
      cases hbv : b ⟨0, by omega⟩
      · symm; apply decide_eq_false
        rintro ⟨j, hj, hbj⟩
        have hj0 : j = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hj0, hbv] at hbj; exact Bool.noConfusion hbj
      · symm; exact decide_eq_true ⟨⟨0, by omega⟩, by dsimp; omega, hbv⟩
  | k + 1, hk => by
      have ih := pGates_eval n hn xs hl b hb k (by omega)
      have hlen_p : (pGates n).length = n - 2 := by simp [pGates]
      rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil]
      let w := ((pGates n).take k).foldl stepWire xs
      have hw_len : w.length = 2 * n + k := by
        dsimp only [w]; rw [foldl_stepWire_len, hl, List.length_take, hlen_p]; omega
      have hp_eq : prefWire n (k + 1) = 2 * n + k := by simp [prefWire]
      rw [hp_eq]
      change (stepWire w ((pGates n)[k]'(by omega))).getD (2 * n + k) false = _
      unfold stepWire
      rw [getD_snoc_self w _ (2 * n + k) hw_len]
      simp only [pGates, List.getElem_ofFn, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have h1 : w.getD (prefWire n k) false = decide (∃ j : Fin n, j.1 ≤ k ∧ b j = true) := ih
      have h2 : w.getD (n + k + 1) false = b ⟨k + 1, by omega⟩ := by
        dsimp only [w]
        rw [foldl_stepWire_getD_lt _ xs (n + k + 1) (by omega)]
        have := hb ⟨k + 1, by omega⟩
        rwa [show n + (k + 1) = n + k + 1 from by omega] at this
      rw [h1, h2]
      by_cases hex : ∃ j : Fin n, j.1 ≤ k ∧ b j = true
      · rw [decide_eq_true hex, Bool.true_or]
        obtain ⟨j, hj, hbj⟩ := hex
        exact (decide_eq_true ⟨j, by omega, hbj⟩).symm
      · rw [decide_eq_false hex, Bool.false_or]
        cases hbv : b ⟨k + 1, by omega⟩
        · symm; apply decide_eq_false
          rintro ⟨j, hj, hbj⟩
          by_cases hle : j.1 ≤ k
          · exact hex ⟨j, hle, hbj⟩
          · have hjeq : j = ⟨k + 1, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [hjeq, hbv] at hbj; exact Bool.noConfusion hbj
        · symm; exact decide_eq_true ⟨⟨k + 1, by omega⟩, by dsimp; omega, hbv⟩

theorem sGates_eval (n : ℕ) (hn : 2 ≤ n) (xs : List Bool) (hl : xs.length = 3 * n - 2)
    (b : Fin n → Bool) (hb : ∀ j : Fin n, xs.getD (n + j.1) false = b j) :
    ∀ m, m ≤ n - 2 →
      (((sGates n).take m).foldl stepWire xs).getD (sufWire n m) false =
        decide (∃ j : Fin n, n - 1 - m ≤ j.1 ∧ b j = true)
  | 0, _ => by
      simp only [List.take_zero, List.foldl_nil, sufWire, ↓reduceIte]
      have h0 := hb ⟨n - 1, by omega⟩
      have heq : n + (n - 1) = 2 * n - 1 := by omega
      rw [heq] at h0
      rw [h0]
      cases hbv : b ⟨n - 1, by omega⟩
      · symm; apply decide_eq_false
        rintro ⟨j, hj, hbj⟩
        have hj0 : j = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hj0, hbv] at hbj; exact Bool.noConfusion hbj
      · symm; exact decide_eq_true ⟨⟨n - 1, by omega⟩, by dsimp; omega, hbv⟩
  | m + 1, hm => by
      have ih := sGates_eval n hn xs hl b hb m (by omega)
      have hlen_s : (sGates n).length = n - 2 := by simp [sGates]
      rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil]
      let w := ((sGates n).take m).foldl stepWire xs
      have hw_len : w.length = (3 * n - 2) + m := by
        dsimp only [w]; rw [foldl_stepWire_len, hl, List.length_take, hlen_s]; omega
      have hs_eq : sufWire n (m + 1) = (3 * n - 2) + m := by simp [sufWire]
      rw [hs_eq]
      change (stepWire w ((sGates n)[m]'(by omega))).getD ((3 * n - 2) + m) false = _
      unfold stepWire
      rw [getD_snoc_self w _ ((3 * n - 2) + m) hw_len]
      simp only [sGates, List.getElem_ofFn, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have h1 : w.getD (sufWire n m) false = decide (∃ j : Fin n, n - 1 - m ≤ j.1 ∧ b j = true) := ih
      have h2 : w.getD (n + (n - 2 - m)) false = b ⟨n - 2 - m, by omega⟩ := by
        dsimp only [w]
        rw [foldl_stepWire_getD_lt _ xs (n + (n - 2 - m)) (by omega)]
        exact hb ⟨n - 2 - m, by omega⟩
      rw [h1, h2]
      by_cases hex : ∃ j : Fin n, n - 1 - m ≤ j.1 ∧ b j = true
      · rw [decide_eq_true hex, Bool.or_true]
        obtain ⟨j, hj, hbj⟩ := hex
        exact (decide_eq_true ⟨j, by omega, hbj⟩).symm
      · rw [decide_eq_false hex, Bool.or_false]
        cases hbv : b ⟨n - 2 - m, by omega⟩
        · symm; apply decide_eq_false
          rintro ⟨j, hj, hbj⟩
          by_cases hge : n - 1 - m ≤ j.1
          · exact hex ⟨j, hge, hbj⟩
          · have hjeq : j = ⟨n - 2 - m, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [hjeq, hbv] at hbj; exact Bool.noConfusion hbj
        · symm; exact decide_eq_true ⟨⟨n - 2 - m, by omega⟩, by dsimp; omega, hbv⟩

theorem bGates_eval (n : ℕ) (hn : 2 ≤ n) (xs : List Bool) (hl : xs.length = 4 * n - 4)
    (b : Fin n → Bool)
    (hp : ∀ k ≤ n - 2, xs.getD (prefWire n k) false = decide (∃ j : Fin n, j.1 ≤ k ∧ b j = true))
    (hs : ∀ m ≤ n - 2, xs.getD (sufWire n m) false = decide (∃ j : Fin n, n - 1 - m ≤ j.1 ∧ b j = true)) :
    ∀ r, r < n - 2 →
      (((bGates n).take (r + 1)).foldl stepWire xs).getD ((4 * n - 4) + r) false =
        decide (∃ j : Fin n, j.1 ≠ r + 1 ∧ b j = true) := by
  intro r hr
  have hlen_b : (bGates n).length = n - 2 := by simp [bGates]
  rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil]
  let w := ((bGates n).take r).foldl stepWire xs
  have hw_len : w.length = (4 * n - 4) + r := by
    dsimp only [w]; rw [foldl_stepWire_len, hl, List.length_take, hlen_b]; omega
  change (stepWire w ((bGates n)[r]'(by omega))).getD ((4 * n - 4) + r) false = _
  unfold stepWire
  rw [getD_snoc_self w _ ((4 * n - 4) + r) hw_len]
  simp only [bGates, List.getElem_ofFn, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  have h1 : w.getD (prefWire n r) false = decide (∃ j : Fin n, j.1 ≤ r ∧ b j = true) := by
    dsimp only [w]
    rw [foldl_stepWire_getD_lt _ xs (prefWire n r) (by have := prefWire_lt n r hn (by omega); omega)]
    exact hp r (by omega)
  have h2 : w.getD (sufWire n (n - 3 - r)) false = decide (∃ j : Fin n, n - 1 - (n - 3 - r) ≤ j.1 ∧ b j = true) := by
    dsimp only [w]
    rw [foldl_stepWire_getD_lt _ xs (sufWire n (n - 3 - r)) (by have := sufWire_lt n (n - 3 - r) hn (by omega); omega)]
    exact hs (n - 3 - r) (by omega)
  rw [h1, h2]
  by_cases hL : ∃ j : Fin n, j.1 ≤ r ∧ b j = true
  · rw [decide_eq_true hL, Bool.true_or]
    obtain ⟨j, hj, hbj⟩ := hL
    exact (decide_eq_true ⟨j, by omega, hbj⟩).symm
  · rw [decide_eq_false hL, Bool.false_or]
    by_cases hR : ∃ j : Fin n, n - 1 - (n - 3 - r) ≤ j.1 ∧ b j = true
    · rw [decide_eq_true hR]
      obtain ⟨j, hj, hbj⟩ := hR
      exact (decide_eq_true ⟨j, by omega, hbj⟩).symm
    · rw [decide_eq_false hR]
      symm; apply decide_eq_false
      rintro ⟨j, hne, hbj⟩
      by_cases hle : j.1 ≤ r
      · exact hL ⟨j, hle, hbj⟩
      · exact hR ⟨j, by omega, hbj⟩

theorem tGates_eval (n : ℕ) (hn : 2 ≤ n) (xs : List Bool) (hl : xs.length = 5 * n - 6)
    (a b : Fin n → Bool)
    (ha : ∀ i : Fin n, xs.getD i.1 false = a i)
    (hbn : ∀ i : Fin n, xs.getD (bnotWire n i.1) false = decide (∃ j : Fin n, j ≠ i ∧ b j = true)) :
    ∀ i : Fin n,
      ((tGates n).foldl stepWire xs).getD ((5 * n - 6) + i.1) false =
        (a i && decide (∃ j : Fin n, j ≠ i ∧ b j = true)) := by
  intro i
  have hlen_t : (tGates n).length = n := by simp [tGates]
  have hsplit : tGates n = (tGates n).take (i.1 + 1) ++ (tGates n).drop (i.1 + 1) :=
    (List.take_append_drop (i.1 + 1) (tGates n)).symm
  rw [hsplit, List.foldl_append]
  have htake_len : (((tGates n).take (i.1 + 1)).foldl stepWire xs).length = (5 * n - 6) + (i.1 + 1) := by
    rw [foldl_stepWire_len, hl, List.length_take, hlen_t]; omega
  rw [foldl_stepWire_getD_lt _ _ ((5 * n - 6) + i.1) (by omega)]
  rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil]
  let w := ((tGates n).take i.1).foldl stepWire xs
  have hw_len : w.length = (5 * n - 6) + i.1 := by
    dsimp only [w]; rw [foldl_stepWire_len, hl, List.length_take, hlen_t]; omega
  change (stepWire w ((tGates n)[i.1]'(by omega))).getD ((5 * n - 6) + i.1) false = _
  unfold stepWire
  rw [getD_snoc_self w _ ((5 * n - 6) + i.1) hw_len]
  simp only [tGates, List.getElem_ofFn, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  dsimp only [w]
  rw [foldl_stepWire_getD_lt _ xs i.1 (by omega)]
  rw [foldl_stepWire_getD_lt _ xs (bnotWire n i.1) (by have := bnotWire_lt n i.1 hn i.2; omega)]
  rw [ha i, hbn i]

theorem oGates_eval (n : ℕ) (hn : 2 ≤ n) (xs : List Bool) (hl : xs.length = 6 * n - 6)
    (a b : Fin n → Bool)
    (ht : ∀ i : Fin n, xs.getD ((5 * n - 6) + i.1) false = (a i && decide (∃ j : Fin n, j ≠ i ∧ b j = true))) :
    ∀ k, k < n →
      (((oGates n).take k).foldl stepWire xs).getD (orWire n k) false =
        decide (∃ i j : Fin n, i.1 ≤ k ∧ i ≠ j ∧ a i = true ∧ b j = true)
  | 0, hk => by
      simp only [List.take_zero, List.foldl_nil, orWire, ↓reduceIte]
      have h0 := ht ⟨0, hk⟩
      simp only [Nat.add_zero] at h0
      rw [h0]
      cases hav : a ⟨0, hk⟩
      · simp only [Bool.false_and]; symm; apply decide_eq_false
        rintro ⟨i, _, hi, _, hai, _⟩
        have hi0 : i = ⟨0, hk⟩ := Fin.ext (by dsimp; omega)
        rw [hi0, hav] at hai; exact Bool.noConfusion hai
      · simp only [Bool.true_and]
        by_cases hex : ∃ j : Fin n, j ≠ ⟨0, hk⟩ ∧ b j = true
        · rw [decide_eq_true hex]
          obtain ⟨j, hjne, hbj⟩ := hex
          exact (decide_eq_true ⟨⟨0, hk⟩, j, by dsimp; omega, fun e => hjne e.symm, hav, hbj⟩).symm
        · rw [decide_eq_false hex]; symm; apply decide_eq_false
          rintro ⟨i, j, hi, hij, _, hbj⟩
          have hi0 : i = ⟨0, hk⟩ := Fin.ext (by dsimp; omega)
          subst hi0; exact hex ⟨j, fun e => hij e.symm, hbj⟩
  | k + 1, hk => by
      have ih := oGates_eval n hn xs hl a b ht k (by omega)
      have hlen_o : (oGates n).length = n - 1 := by simp [oGates]
      rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil]
      let w := ((oGates n).take k).foldl stepWire xs
      have hw_len : w.length = (6 * n - 6) + k := by
        dsimp only [w]; rw [foldl_stepWire_len, hl, List.length_take, hlen_o]; omega
      have ho_eq : orWire n (k + 1) = (6 * n - 6) + k := by simp [orWire]
      rw [ho_eq]
      change (stepWire w ((oGates n)[k]'(by omega))).getD ((6 * n - 6) + k) false = _
      unfold stepWire
      rw [getD_snoc_self w _ ((6 * n - 6) + k) hw_len]
      simp only [oGates, List.getElem_ofFn, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have h1 : w.getD (orWire n k) false = decide (∃ i j : Fin n, i.1 ≤ k ∧ i ≠ j ∧ a i = true ∧ b j = true) := ih
      have h2 : w.getD ((5 * n - 6) + k + 1) false =
          (a ⟨k + 1, hk⟩ && decide (∃ j : Fin n, j ≠ ⟨k + 1, hk⟩ ∧ b j = true)) := by
        dsimp only [w]
        rw [foldl_stepWire_getD_lt _ xs ((5 * n - 6) + k + 1) (by omega)]
        have := ht ⟨k + 1, hk⟩
        rwa [show (5 * n - 6) + (k + 1) = (5 * n - 6) + k + 1 from by omega] at this
      rw [h1, h2]
      by_cases hL : ∃ i j : Fin n, i.1 ≤ k ∧ i ≠ j ∧ a i = true ∧ b j = true
      · rw [decide_eq_true hL, Bool.true_or]
        obtain ⟨i, j, hi, hij, hai, hbj⟩ := hL
        exact (decide_eq_true ⟨i, j, by omega, hij, hai, hbj⟩).symm
      · rw [decide_eq_false hL, Bool.false_or]
        cases hav : a ⟨k + 1, hk⟩
        · simp only [Bool.false_and]; symm; apply decide_eq_false
          rintro ⟨i, j, hi, hij, hai, hbj⟩
          by_cases hle : i.1 ≤ k
          · exact hL ⟨i, j, hle, hij, hai, hbj⟩
          · have hieq : i = ⟨k + 1, hk⟩ := Fin.ext (by dsimp; omega)
            rw [hieq, hav] at hai; exact Bool.noConfusion hai
        · simp only [Bool.true_and]
          by_cases hR : ∃ j : Fin n, j ≠ ⟨k + 1, hk⟩ ∧ b j = true
          · rw [decide_eq_true hR]
            obtain ⟨j, hjne, hbj⟩ := hR
            exact (decide_eq_true ⟨⟨k + 1, hk⟩, j, le_rfl, fun e => hjne e.symm, hav, hbj⟩).symm
          · rw [decide_eq_false hR]; symm; apply decide_eq_false
            rintro ⟨i, j, hi, hij, hai, hbj⟩
            by_cases hle : i.1 ≤ k
            · exact hL ⟨i, j, hle, hij, hai, hbj⟩
            · have hieq : i = ⟨k + 1, hk⟩ := Fin.ext (by dsimp; omega)
              subst hieq; exact hR ⟨j, fun e => hij e.symm, hbj⟩

theorem crownCircuit_eval (n : ℕ) (hn : 2 ≤ n) (xs : List Bool) (hl : xs.length = 2 * n)
    (a b : Fin n → Bool)
    (ha : ∀ i : Fin n, xs.getD i.1 false = a i)
    (hb : ∀ j : Fin n, xs.getD (n + j.1) false = b j) :
    (crownCircuit n).eval xs = decide (∃ i j : Fin n, i ≠ j ∧ a i = true ∧ b j = true) := by
  unfold Circuit.eval Circuit.wires crownCircuit crownGates
  change ((((pGates n ++ sGates n ++ bGates n ++ tGates n ++ oGates n).foldl stepWire xs)).getD (orWire n (n - 1)) false) = _
  rw [List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append]
  let wP := (pGates n).foldl stepWire xs
  let wS := (sGates n).foldl stepWire wP
  let wB := (bGates n).foldl stepWire wS
  let wT := (tGates n).foldl stepWire wB
  have hlenP : wP.length = 3 * n - 2 := by
    dsimp only [wP]; rw [foldl_stepWire_len, hl]; simp [pGates]; omega
  have hlenS : wS.length = 4 * n - 4 := by
    dsimp only [wS]; rw [foldl_stepWire_len, hlenP]; simp [sGates]; omega
  have hlenB : wB.length = 5 * n - 6 := by
    dsimp only [wB]; rw [foldl_stepWire_len, hlenS]; simp [bGates]; omega
  have hlenT : wT.length = 6 * n - 6 := by
    dsimp only [wT]; rw [foldl_stepWire_len, hlenB]; simp [tGates]; omega
  have hP_ok : ∀ k ≤ n - 2, wP.getD (prefWire n k) false = decide (∃ j : Fin n, j.1 ≤ k ∧ b j = true) := by
    intro k hk
    have hsplit : pGates n = (pGates n).take k ++ (pGates n).drop k := (List.take_append_drop k (pGates n)).symm
    dsimp only [wP]; rw [hsplit, List.foldl_append]
    have htl : (((pGates n).take k).foldl stepWire xs).length = 2 * n + k := by
      rw [foldl_stepWire_len, hl, List.length_take]; simp [pGates]; omega
    rw [foldl_stepWire_getD_lt _ _ (prefWire n k) (by have := prefWire_lt n k hn hk; omega)]
    exact pGates_eval n hn xs hl b hb k hk
  have hb_wP : ∀ j : Fin n, wP.getD (n + j.1) false = b j := fun j => by
    dsimp only [wP]; rw [foldl_stepWire_getD_lt _ xs (n + j.1) (by omega)]; exact hb j
  have hS_ok : ∀ m ≤ n - 2, wS.getD (sufWire n m) false = decide (∃ j : Fin n, n - 1 - m ≤ j.1 ∧ b j = true) := by
    intro m hm
    have hsplit : sGates n = (sGates n).take m ++ (sGates n).drop m := (List.take_append_drop m (sGates n)).symm
    dsimp only [wS]; rw [hsplit, List.foldl_append]
    have htl : (((sGates n).take m).foldl stepWire wP).length = (3 * n - 2) + m := by
      rw [foldl_stepWire_len, hlenP, List.length_take]; simp [sGates]; omega
    rw [foldl_stepWire_getD_lt _ _ (sufWire n m) (by have := sufWire_lt n m hn hm; omega)]
    exact sGates_eval n hn wP hlenP b hb_wP m hm
  have hP_wS : ∀ k ≤ n - 2, wS.getD (prefWire n k) false = decide (∃ j : Fin n, j.1 ≤ k ∧ b j = true) := fun k hk => by
    dsimp only [wS]
    rw [foldl_stepWire_getD_lt _ wP (prefWire n k) (by have := prefWire_lt n k hn hk; omega)]
    exact hP_ok k hk
  have hbn_wB : ∀ i : Fin n, wB.getD (bnotWire n i.1) false = decide (∃ j : Fin n, j ≠ i ∧ b j = true) := by
    intro i
    unfold bnotWire
    split_ifs with h0 hlast
    · dsimp only [wB]
      rw [foldl_stepWire_getD_lt _ wS (sufWire n (n - 2)) (by have := sufWire_lt n (n - 2) hn le_rfl; omega)]
      rw [hS_ok (n - 2) le_rfl]
      congr 1; apply propext; constructor
      · rintro ⟨j, hj, hbj⟩; exact ⟨j, fun e => by have := congrArg Fin.val e; omega, hbj⟩
      · rintro ⟨j, hne, hbj⟩; exact ⟨j, by have : j.1 ≠ 0 := fun e => hne (Fin.ext (by omega)); omega, hbj⟩
    · dsimp only [wB]
      rw [foldl_stepWire_getD_lt _ wS (prefWire n (n - 2)) (by have := prefWire_lt n (n - 2) hn le_rfl; omega)]
      rw [hP_wS (n - 2) le_rfl]
      congr 1; apply propext; constructor
      · rintro ⟨j, hj, hbj⟩; exact ⟨j, fun e => by have := congrArg Fin.val e; omega, hbj⟩
      · rintro ⟨j, hne, hbj⟩; exact ⟨j, by have : j.1 ≠ n - 1 := fun e => hne (Fin.ext (by omega)); omega, hbj⟩
    · let r := i.1 - 1
      have hr : r < n - 2 := by omega
      have hsplit : bGates n = (bGates n).take (r + 1) ++ (bGates n).drop (r + 1) :=
        (List.take_append_drop (r + 1) (bGates n)).symm
      dsimp only [wB]; rw [hsplit, List.foldl_append]
      have htl : (((bGates n).take (r + 1)).foldl stepWire wS).length = (4 * n - 4) + (r + 1) := by
        rw [foldl_stepWire_len, hlenS, List.length_take]; simp [bGates]; omega
      rw [foldl_stepWire_getD_lt _ _ ((4 * n - 4) + r) (by omega)]
      rw [bGates_eval n hn wS hlenS b hP_wS hS_ok r hr]
      congr 1; apply propext; constructor
      · rintro ⟨j, hne, hbj⟩; exact ⟨j, fun e => hne (by have := congrArg Fin.val e; omega), hbj⟩
      · rintro ⟨j, hne, hbj⟩; exact ⟨j, fun e => hne (Fin.ext (by omega)), hbj⟩
  have ha_wB : ∀ i : Fin n, wB.getD i.1 false = a i := fun i => by
    have hi := i.2
    have h1 : wB.getD i.1 false = wS.getD i.1 false := foldl_stepWire_getD_lt (bGates n) wS i.1 (by omega)
    have h2 : wS.getD i.1 false = wP.getD i.1 false := foldl_stepWire_getD_lt (sGates n) wP i.1 (by omega)
    have h3 : wP.getD i.1 false = xs.getD i.1 false := foldl_stepWire_getD_lt (pGates n) xs i.1 (by omega)
    rw [h1, h2, h3]; exact ha i
  have ht_wT : ∀ i : Fin n, wT.getD ((5 * n - 6) + i.1) false =
      (a i && decide (∃ j : Fin n, j ≠ i ∧ b j = true)) :=
    tGates_eval n hn wB hlenB a b ha_wB hbn_wB
  have ho_full : ((oGates n).foldl stepWire wT).getD (orWire n (n - 1)) false =
      decide (∃ i j : Fin n, i.1 ≤ n - 1 ∧ i ≠ j ∧ a i = true ∧ b j = true) := by
    have hlen_o : (oGates n).length = n - 1 := by simp [oGates]
    have htake : (oGates n).take (n - 1) = oGates n := List.take_of_length_le (by omega)
    rw [← htake]
    exact oGates_eval n hn wT hlenT a b ht_wT (n - 1) (by omega)
  change ((oGates n).foldl stepWire wT).getD (orWire n (n - 1)) false = _
  rw [ho_full]
  congr 1; apply propext; constructor
  · rintro ⟨i, j, _, hij, hai, hbj⟩; exact ⟨i, j, hij, hai, hbj⟩
  · rintro ⟨i, j, hij, hai, hbj⟩; exact ⟨i, j, by omega, hij, hai, hbj⟩

def doubleCrownCircuit (n : ℕ) : Circuit :=
  ⟨foldGates n ++ (crownGates n).map (shiftGate (4 * n)), orWire n (n - 1) + 4 * n⟩

theorem doubleCrownCircuit_mono (n : ℕ) : Monotone2 (doubleCrownCircuit n) := by
  intro g hg
  simp only [doubleCrownCircuit, List.mem_append, List.mem_map] at hg
  rcases hg with hfg | ⟨g0, hg0, rfl⟩
  · simp only [foldGates, List.mem_ofFn] at hfg
    rcases hfg with ⟨k, rfl⟩
    unfold foldGate; split_ifs <;> simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  · have h0 := crownCircuit_mono n g0 hg0
    exact ⟨h0.1, by simp [shiftGate, h0.2]⟩

theorem doubleCrownCircuit_size (n : ℕ) (hn : 2 ≤ n) : (doubleCrownCircuit n).size = 7 * n - 7 := by
  have hs := crownCircuit_size n hn
  simp only [doubleCrownCircuit, Circuit.size, List.length_append, List.length_map, foldGates, List.length_ofFn]
  simp only [crownCircuit, Circuit.size] at hs
  omega

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      RepSizeAtMost
        (fun u v : Fin (2 * n) => decide (u.val / n = v.val / n ∧ u.val % n ≠ v.val % n))
        (7 * n - 7) := by
  intro n hn
  refine ⟨doubleCrownCircuit n, doubleCrownCircuit_mono n, by rw [doubleCrownCircuit_size n hn], ?_⟩
  intro u v
  dsimp only
  -- Reduce doubleCrownCircuit.eval (oneEach u v) to (crownCircuit n).eval (List.ofFn (virtInput n u v))
  have heval : (doubleCrownCircuit n).eval (oneEach u v) =
      (crownCircuit n).eval (List.ofFn (virtInput n u v)) := by
    unfold Circuit.eval Circuit.wires doubleCrownCircuit crownCircuit
    rw [List.foldl_append]
    have h1 : (foldGates n).foldl stepWire (oneEach u v) = oneEach u v ++ List.ofFn (virtInput n u v) := by
      have h := foldl_foldGates_take n u v (2 * n) le_rfl
      have hlen1 : (foldGates n).length = 2 * n := by simp [foldGates]
      have hlen2 : (List.ofFn (virtInput n u v)).length = 2 * n := by simp
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at h
      exact h
    change (((crownGates n).map (shiftGate (4 * n))).foldl stepWire ((foldGates n).foldl stepWire (oneEach u v))).getD
      (orWire n (n - 1) + 4 * n) false = _
    rw [h1]
    have hlen : (oneEach u v).length = 4 * n := oneEach_len n u v
    rw [← hlen, foldl_shift (crownGates n) (oneEach u v) (List.ofFn (virtInput n u v)), getD_append_add]
    rfl
  rw [heval]
  let a : Fin n → Bool := fun i => decide (i.1 = u.1) || decide (n + i.1 = v.1)
  let b : Fin n → Bool := fun j => decide (n + j.1 = u.1) || decide (j.1 = v.1)
  have hce := crownCircuit_eval n hn (List.ofFn (virtInput n u v)) (by simp) a b
    (fun i => by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      simp [virtInput, a, i.2])
    (fun j => by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      have hnotlt : ¬ n + j.1 < n := by omega
      simp [virtInput, b, hnotlt])
  rw [hce]
  congr 1; apply propext
  by_cases hu : u.1 < n
  · by_cases hv : v.1 < n
    · have hud : u.1 / n = 0 := Nat.div_eq_of_lt hu
      have hvd : v.1 / n = 0 := Nat.div_eq_of_lt hv
      have hum : u.1 % n = u.1 := Nat.mod_eq_of_lt hu
      have hvm : v.1 % n = v.1 := Nat.mod_eq_of_lt hv
      constructor
      · rintro ⟨i, j, hij, hai, hbj⟩
        simp only [a, b, Bool.or_eq_true, decide_eq_true_eq] at hai hbj
        have hi : i.1 = u.1 := hai.resolve_right (by omega)
        have hj : j.1 = v.1 := hbj.resolve_left (by omega)
        refine ⟨by omega, ?_⟩
        rw [hum, hvm]; intro heq; exact hij (Fin.ext (by omega))
      · rintro ⟨_, hne⟩
        rw [hum, hvm] at hne
        refine ⟨⟨u.1, hu⟩, ⟨v.1, hv⟩, fun e => hne (Fin.mk.inj e), ?_, ?_⟩
        · simp [a]
        · simp [b]
    · have hud : u.1 / n = 0 := Nat.div_eq_of_lt hu
      have hvd : v.1 / n = 1 := by
        have h1 : v.1 = n + (v.1 - n) := by omega
        have h2 : v.1 - n < n := by omega
        rw [h1, Nat.add_div_left _ (by omega), Nat.div_eq_of_lt h2]
      constructor
      · rintro ⟨_, j, _, _, hbj⟩
        simp only [b, Bool.or_eq_true, decide_eq_true_eq] at hbj
        omega
      · rintro ⟨hdiv, _⟩; omega
  · by_cases hv : v.1 < n
    · have hud : u.1 / n = 1 := by
        have h1 : u.1 = n + (u.1 - n) := by omega
        have h2 : u.1 - n < n := by omega
        rw [h1, Nat.add_div_left _ (by omega), Nat.div_eq_of_lt h2]
      have hvd : v.1 / n = 0 := Nat.div_eq_of_lt hv
      constructor
      · rintro ⟨i, _, _, hai, _⟩
        simp only [a, Bool.or_eq_true, decide_eq_true_eq] at hai
        omega
      · rintro ⟨hdiv, _⟩; omega
    · have hu2 : u.1 - n < n := by omega
      have hv2 : v.1 - n < n := by omega
      have hud : u.1 / n = 1 := by
        have h1 : u.1 = n + (u.1 - n) := by omega
        rw [h1, Nat.add_div_left _ (by omega), Nat.div_eq_of_lt hu2]
      have hvd : v.1 / n = 1 := by
        have h1 : v.1 = n + (v.1 - n) := by omega
        rw [h1, Nat.add_div_left _ (by omega), Nat.div_eq_of_lt hv2]
      have hum : u.1 % n = u.1 - n := by
        have h1 : u.1 = n + (u.1 - n) := by omega
        conv_lhs => rw [h1]
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hu2]
      have hvm : v.1 % n = v.1 - n := by
        have h1 : v.1 = n + (v.1 - n) := by omega
        conv_lhs => rw [h1]
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hv2]
      constructor
      · rintro ⟨i, j, hij, hai, hbj⟩
        simp only [a, b, Bool.or_eq_true, decide_eq_true_eq] at hai hbj
        have hi : n + i.1 = v.1 := hai.resolve_left (by omega)
        have hj : n + j.1 = u.1 := hbj.resolve_right (by omega)
        refine ⟨by omega, ?_⟩
        rw [hum, hvm]; intro heq; exact hij (Fin.ext (by omega))
      · rintro ⟨_, hne⟩
        rw [hum, hvm] at hne
        refine ⟨⟨v.1 - n, hv2⟩, ⟨u.1 - n, hu2⟩, fun e => hne (by have := congrArg Fin.val e; dsimp at this; omega), ?_, ?_⟩
        · simp only [a, Bool.or_eq_true, decide_eq_true_eq]; right; omega
        · simp only [b, Bool.or_eq_true, decide_eq_true_eq]; left; omega

end PEqualNP.Outside.L_meta_17709_aux

theorem PEqualNP.Outside.L_meta_17709 :
    ∀ n : ℕ, 2 ≤ n →
      PEqualNP.Represents.RepSizeAtMost
        (fun u v : Fin (2 * n) => decide (u.val / n = v.val / n ∧ u.val % n ≠ v.val % n))
        (7 * n - 7) :=
  PEqualNP.Outside.L_meta_17709_aux.main
