import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3313_aux

open PEqualNP.CircuitLowerBounds

def C0 : PEqualNP.CircuitLowerBounds.Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 41] }], output := 43 }

def spec (x : Fin 14 → Bool) : Bool := decide (∃ e ∈ ([(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8), (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12), (6, 12), (2, 13), (4, 13), (5, 13)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)

def edgeL : List (Fin 14 × Fin 14) := ([(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8), (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12), (6, 12), (2, 13), (4, 13), (5, 13)] : List (Fin 14 × Fin 14))


def Tn : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, i =>
    if i < n then Tn n i ||| (Tn n i <<< 2 ^ n)
    else if i = n then (2 ^ (2 ^ n) - 1) <<< 2 ^ n else 0

theorem Tn_high : ∀ (n i k : ℕ), 2 ^ n ≤ k → (Tn n i).testBit k = false := by
  intro n
  induction n with
  | zero => intro i k _; simp [Tn]
  | succ n ih =>
    intro i k hk
    have hk' : 2 ^ n ≤ k := le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)) hk
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    simp only [Tn]
    split_ifs with h1 h2'
    · rw [Nat.testBit_lor, Nat.testBit_shiftLeft, ih i k hk', ih i (k - 2 ^ n) (by omega)]
      simp
    · rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
      right
      omega
    · simp

theorem Tn_spec : ∀ (n i m : ℕ), m < 2 ^ n → (Tn n i).testBit m = m.testBit i := by
  intro n
  induction n with
  | zero =>
    intro i m hm
    have : m = 0 := by simpa using hm
    subst this
    simp [Tn]
  | succ n ih =>
    intro i m hm
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
    simp only [Tn]
    split_ifs with h1 h3
    · rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
      by_cases hlt : m < 2 ^ n
      · rw [ih i m hlt]
        have : ¬ (m ≥ 2 ^ n) := by omega
        simp [this]
      · rw [Tn_high n i m (by omega), ih i (m - 2 ^ n) (by omega)]
        have hge : m ≥ 2 ^ n := by omega
        have e : m = 2 ^ n + (m - 2 ^ n) := by omega
        conv_rhs => rw [e]
        rw [Nat.testBit_two_pow_add_gt h1]
        simp [hge]
    · subst h3
      rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hlt : m < 2 ^ i
      · rw [Nat.testBit_eq_false_of_lt hlt]
        have : ¬ (m ≥ 2 ^ i) := by omega
        simp [this]
      · have e : m = 2 ^ i + (m - 2 ^ i) := by omega
        conv_rhs => rw [e]
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_eq_false_of_lt (by omega : m - 2 ^ i < 2 ^ i)]
        have hge : m ≥ 2 ^ i := by omega
        simp [hge]
        omega
    · have hi : n < i := by omega
      have : m < 2 ^ i := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hi)
      rw [Nat.testBit_eq_false_of_lt this]
      simp



def stepN (p : ℕ × ℕ) (g : Gate) : ℕ × ℕ :=
  (if g.op.eval (g.inputs.map fun i => p.1.testBit i) then p.1 ||| 2 ^ p.2 else p.1, p.2 + 1)

def encL : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (encL l)

theorem encL_spec : ∀ (l : List Bool) (i : ℕ), l.getD i false = (encL l).testBit i := by
  intro l
  induction l with
  | nil => intro i; simp [encL]
  | cons b l ih =>
    intro i
    cases i with
    | zero => simp [encL]
    | succ i =>
      show l.getD i false = (Nat.bit b (encL l)).testBit (i + 1)
      rw [Nat.testBit_bit_succ]
      exact ih i

theorem inv_step (wl : List Bool) (N : ℕ) (g : Gate) (h : ∀ i, wl.getD i false = N.testBit i) :
    ∀ i, (wl ++ [g.op.eval (g.inputs.map fun i => wl.getD i false)]).getD i false =
      (stepN (N, wl.length) g).1.testBit i := by
  have hv : (g.inputs.map fun i => wl.getD i false) = g.inputs.map fun i => N.testBit i := by
    congr 1
    funext j
    exact h j
  have hout : ∀ i, wl.length ≤ i → N.testBit i = false := by
    intro i hi
    rw [← h i]
    exact List.getD_eq_default _ _ hi
  intro i
  rw [hv]
  simp only [stepN]
  rcases lt_trichotomy i wl.length with hi | hi | hi
  · rw [List.getD_append _ _ _ _ hi, h i]
    split_ifs
    · rw [Nat.testBit_lor, Nat.testBit_two_pow]
      have : wl.length ≠ i := by omega
      simp [this]
    · rfl
  · subst hi
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp only [Nat.sub_self, List.getD_cons_zero]
    split_ifs with hc
    · rw [Nat.testBit_lor, Nat.testBit_two_pow]
      simp [hc]
    · rw [hout _ (le_refl _)]
      simp [hc]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have hpos : i - wl.length = (i - wl.length - 1) + 1 := by omega
    rw [hpos, List.getD_cons_succ, List.getD_nil]
    split_ifs
    · rw [Nat.testBit_lor, Nat.testBit_two_pow, hout i (by omega)]
      have : wl.length ≠ i := by omega
      simp [this]
    · rw [hout i (by omega)]

theorem fold_spec : ∀ (gs : List Gate) (wl : List Bool) (N : ℕ),
    (∀ i, wl.getD i false = N.testBit i) →
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wl).getD i false =
      (gs.foldl stepN (N, wl.length)).1.testBit i := by
  intro gs
  induction gs with
  | nil => intro wl N h i; exact h i
  | cons g gs ih =>
    intro wl N h i
    simp only [List.foldl_cons]
    have e : stepN (N, wl.length) g =
        ((stepN (N, wl.length) g).1,
          (wl ++ [g.op.eval (g.inputs.map fun i => wl.getD i false)]).length) := by
      simp [stepN]
    rw [e]
    exact ih _ _ (inv_step wl N g h) i


theorem encL_lt : ∀ l : List Bool, encL l < 2 ^ l.length := by
  intro l
  induction l with
  | nil => simp [encL]
  | cons b l ih =>
    simp only [encL, List.length_cons, pow_succ, Nat.bit_val]
    cases b <;> simp <;> omega

def ALL : ℕ := 2 ^ 16384 - 1

def tcomb : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.foldr (fun a b => a &&& b) ALL
  | GateOp.or, l => l.foldr (fun a b => a ||| b) 0
  | _, _ => 0

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem isAO_spec (op : GateOp) (h : isAO op = true) : op = GateOp.and ∨ op = GateOp.or := by
  cases op <;> simp_all [isAO]

theorem tcomb_spec (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (m : ℕ)
    (hm : m < 16384) : (tcomb op l).testBit m = op.eval (l.map (fun a => a.testBit m)) := by
  rcases hop with rfl | rfl
  · induction l with
    | nil =>
      simp only [tcomb, List.foldr_nil, ALL, List.map_nil, GateOp.eval, List.all_nil]
      rw [Nat.testBit_two_pow_sub_one]
      simp [hm]
    | cons a l ih =>
      simp only [tcomb, List.foldr_cons, Nat.testBit_land, List.map_cons, GateOp.eval,
        List.all_cons, id] at ih ⊢
      rw [ih]
  · induction l with
    | nil => simp [tcomb, GateOp.eval]
    | cons a l ih =>
      simp only [tcomb, List.foldr_cons, Nat.testBit_lor, List.map_cons, GateOp.eval,
        List.any_cons, id] at ih ⊢
      rw [ih]

def tabStep (t : List ℕ) (g : Gate) : List ℕ :=
  t ++ [tcomb g.op (g.inputs.map fun i => t.getD i 0)]

theorem tab_fold : ∀ (gs : List Gate) (wl : List Bool) (t : List ℕ) (m : ℕ), m < 16384 →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → wl.length = t.length →
    (∀ j, wl.getD j false = (t.getD j 0).testBit m) →
    ∀ j, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wl).getD j
      false = ((gs.foldl tabStep t).getD j 0).testBit m := by
  intro gs
  induction gs with
  | nil => intro wl t m _ _ _ h j; exact h j
  | cons g gs ih =>
    intro wl t m hm hops hlen h
    simp only [List.foldl_cons]
    apply ih _ _ m hm (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
      (by simp [tabStep, hlen])
    intro j
    have hv : g.op.eval (g.inputs.map fun i => wl.getD i false) =
        (tcomb g.op (g.inputs.map fun i => t.getD i 0)).testBit m := by
      rw [tcomb_spec g.op (hops g List.mem_cons_self) _ m hm, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    simp only [tabStep]
    rcases lt_trichotomy j wl.length with hj | hj | hj
    · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (by omega), h j]
    · subst hj
      rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, hlen, List.getD_cons_zero]
      exact hv
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      have e1 : j - wl.length = (j - wl.length - 1) + 1 := by omega
      have e2 : j - t.length = (j - t.length - 1) + 1 := by omega
      rw [e1, e2, List.getD_cons_succ, List.getD_cons_succ, List.getD_nil, List.getD_nil]
      simp

def tIn : List ℕ := (List.range 14).map (Tn 14)

theorem bits_of (x : Fin 14 → Bool) (i : Fin 14) :
    (Tn 14 i).testBit (encL (List.ofFn x)) = x i := by
  have hm : encL (List.ofFn x) < 2 ^ 14 := by simpa using encL_lt (List.ofFn x)
  rw [Tn_spec 14 i _ hm, ← encL_spec, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem tIn_spec (x : Fin 14 → Bool) :
    ∀ j, (List.ofFn x).getD j false = (tIn.getD j 0).testBit (encL (List.ofFn x)) := by
  intro j
  by_cases hj : j < 14
  · have h1 : tIn.getD j 0 = Tn 14 j := by simp [tIn, hj]
    rw [h1, bits_of x ⟨j, hj⟩, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [tIn]; omega)]
    simp

def specT : ℕ := edgeL.foldr (fun e acc => (Tn 14 e.1 &&& Tn 14 e.2) ||| acc) 0

theorem specT_spec (x : Fin 14 → Bool) : specT.testBit (encL (List.ofFn x)) = spec x := by
  have key : ∀ L : List (Fin 14 × Fin 14),
      (L.foldr (fun e acc => (Tn 14 e.1 &&& Tn 14 e.2) ||| acc) 0).testBit (encL (List.ofFn x)) =
        decide (∃ e ∈ L, x e.1 = true ∧ x e.2 = true) := by
    intro L
    induction L with
    | nil => simp
    | cons e L ih =>
      rw [List.foldr_cons, Nat.testBit_lor, Nat.testBit_land, bits_of, bits_of, ih]
      simp
  exact key edgeL

theorem hops : ∀ g ∈ C0.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  have h : C0.gates.all (fun g => isAO g.op) = true := by decide +kernel
  intro g hg
  exact isAO_spec _ (List.all_eq_true.1 h g hg)

theorem tab_check : (C0.gates.foldl tabStep tIn).getD 43 0 = specT := by decide +kernel

theorem all_inputs : ∀ x : Fin 14 → Bool,
    PEqualNP.MetaComplexity.circuitFun 14 C0 x = spec x := by
  intro x
  have hm : encL (List.ofFn x) < 16384 := by simpa using encL_lt (List.ofFn x)
  have h1 := tab_fold C0.gates (List.ofFn x) tIn _ hm hops (by simp [tIn]) (tIn_spec x) 43
  show (C0.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    (List.ofFn x)).getD 43 false = spec x
  rw [h1, tab_check, specT_spec]

theorem fast (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    C.eval (List.ofFn x) =
      (C.gates.foldl stepN (encL (List.ofFn x), n)).1.testBit C.output := by
  have h := fold_spec C.gates (List.ofFn x) (encL (List.ofFn x)) (encL_spec _) C.output
  rw [List.length_ofFn] at h
  exact h

end PEqualNP.Outside.L_meta_3313_aux

theorem PEqualNP.Outside.L_meta_3313 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [33, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [36, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [34, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 41] }], output := 43 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 30 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (1, 7), (2, 7), (0, 8), (3, 8), (4, 8), (0, 9), (5, 9), (6, 9), (1, 10), (3, 10), (5, 10), (1, 11), (4, 11), (6, 11), (2, 12), (3, 12), (6, 12), (2, 13), (4, 13), (5, 13)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (([(3, [5, 8], [3, 9], [5, 9]), (4, [5, 8], [8, 9], [5, 9]), (7, [8], [4], [4, 8]), (9, [9], [6], [6, 9]), (11, [10], [5], [5, 10]), (14, [7], [2], [2, 7]), (17, [11], [6], [6, 11]), (20, [12], [6], [6, 12]), (23, [13], [5], [5, 13])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))).map (fun t => t.1) ++ ([(0, [3, 8], [5, 9], [5, 8]), (1, [5, 9], [3, 8], [3, 9]), (2, [3, 10], [5, 10], [10]), (5, [5, 9], [0, 9], [9]), (6, [3, 8], [4, 8], [8]), (8, [5, 9], [6, 9], [9]), (10, [5, 10], [1, 10], [10]), (12, [1, 7], [2, 7], [7]), (13, [2, 7], [0, 7], [7]), (15, [4, 11], [6, 11], [11]), (16, [6, 11], [1, 11], [11]), (18, [2, 12], [3, 12], [12]), (19, [3, 12], [6, 12], [12]), (21, [2, 13], [5, 13], [13]), (22, [5, 13], [4, 13], [13]), (24, [4, 8], [2, 7], []), (25, [4, 8], [6, 9], []), (26, [6, 9], [5, 13], []), (27, [6, 12], [6, 11], []), (28, [6, 9], [5, 10], []), (29, [6, 9], [6, 12], [])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))).map (fun t => t.1)).Perm (List.range 30) ∧
  (∀ t ∈ ([(3, [5, 8], [3, 9], [5, 9]), (4, [5, 8], [8, 9], [5, 9]), (7, [8], [4], [4, 8]), (9, [9], [6], [6, 9]), (11, [10], [5], [5, 10]), (14, [7], [2], [2, 7]), (17, [11], [6], [6, 11]), (20, [12], [6], [6, 12]), (23, [13], [5], [5, 13])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))), (PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 1 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 0 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.2)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.2))) ∧
  (∀ t ∈ ([(0, [3, 8], [5, 9], [5, 8]), (1, [5, 9], [3, 8], [3, 9]), (2, [3, 10], [5, 10], [10]), (5, [5, 9], [0, 9], [9]), (6, [3, 8], [4, 8], [8]), (8, [5, 9], [6, 9], [9]), (10, [5, 10], [1, 10], [10]), (12, [1, 7], [2, 7], [7]), (13, [2, 7], [0, 7], [7]), (15, [4, 11], [6, 11], [11]), (16, [6, 11], [1, 11], [11]), (18, [2, 12], [3, 12], [12]), (19, [3, 12], [6, 12], [12]), (21, [2, 13], [5, 13], [13]), (22, [5, 13], [4, 13], [13]), (24, [4, 8], [2, 7], []), (25, [4, 8], [6, 9], []), (26, [6, 9], [5, 13], []), (27, [6, 12], [6, 11], []), (28, [6, 9], [5, 10], []), (29, [6, 9], [6, 12], [])] : List (ℕ × List (Fin 14) × List (Fin 14) × List (Fin 14))), (PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 1 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(PEqualNP.MetaComplexity.NestedCover.gateAt C t.1).inputs.getD 0 0] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.1)) ∧ PEqualNP.MetaComplexity.circuitFun 14 (⟨C.gates.set t.1 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] }, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) (fun u : Fin 14 => decide (u ∈ t.2.2.2)) ≠ PEqualNP.MetaComplexity.circuitFun 14 C (fun u : Fin 14 => decide (u ∈ t.2.2.2))) := by
  intro C hC
  subst hC
  refine ⟨by decide +kernel, by decide +kernel, PEqualNP.Outside.L_meta_3313_aux.all_inputs,
    by decide +kernel, ?_, ?_⟩
  · simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.Outside.L_meta_3313_aux.fast,
      List.forall_mem_cons]
    repeat' constructor
    all_goals first | rfl | exact List.forall_mem_nil _ | decide +kernel
  · simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.Outside.L_meta_3313_aux.fast,
      List.forall_mem_cons]
    repeat' constructor
    all_goals first | rfl | exact List.forall_mem_nil _ | decide +kernel
