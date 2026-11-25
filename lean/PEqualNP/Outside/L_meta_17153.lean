import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17153_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def bm_op (K : ℕ) (op : GateOp) (l : List ℕ) : ℕ :=
  match op with
  | GateOp.and => l.foldr Nat.land (2 ^ K - 1)
  | GateOp.or => l.foldr Nat.lor 0
  | GateOp.not => Nat.xor (2 ^ K - 1) (l.headD 0)
  | _ => 0

def bm_okop (op : GateOp) : Bool :=
  match op with
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def bm_ok (C : Circuit) : Bool := C.gates.all (fun g => bm_okop g.op)

def bm_step (K : ℕ) (m : List ℕ) (g : Gate) : List ℕ :=
  m ++ [bm_op K g.op (g.inputs.map fun i => m.getD i 0)]

def bm_W (K : ℕ) (gs : List Gate) (m : List ℕ) : List ℕ := gs.foldl (bm_step K) m

theorem bm_step_len (K : ℕ) (m : List ℕ) (g : Gate) :
    (bm_step K m g).length = m.length + 1 := by
  simp [bm_step]

theorem bm_step_lt (K : ℕ) (m : List ℕ) (g : Gate) (i : ℕ) (hi : i < m.length) :
    (bm_step K m g).getD i 0 = m.getD i 0 := by
  simp [bm_step, List.getD, List.getElem?_append_left hi]

theorem bm_step_last (K : ℕ) (m : List ℕ) (g : Gate) (k : ℕ) (hk : k = m.length) :
    (bm_step K m g).getD k 0 = bm_op K g.op (g.inputs.map fun i => m.getD i 0) := by
  subst hk
  simp [bm_step, List.getD]

theorem bm_op_bit (K k : ℕ) (hk : k < K) (op : GateOp) (hop : bm_okop op = true)
    (inputs : List ℕ) (fm : ℕ → ℕ) (fw : ℕ → Bool) (h : ∀ i, fw i = Nat.testBit (fm i) k) :
    Nat.testBit (bm_op K op (inputs.map fm)) k = op.eval (inputs.map fw) := by
  cases op with
  | and =>
    show Nat.testBit (List.foldr Nat.land (2 ^ K - 1) (List.map fm inputs)) k =
      (List.map fw inputs).all id
    induction inputs with
    | nil => simp [Nat.testBit_two_pow_sub_one, hk]
    | cons a l ih =>
      show Nat.testBit (fm a &&& List.foldr Nat.land (2 ^ K - 1) (List.map fm l)) k =
        (fw a && (List.map fw l).all id)
      rw [Nat.testBit_and, ih, h a]
  | or =>
    show Nat.testBit (List.foldr Nat.lor 0 (List.map fm inputs)) k =
      (List.map fw inputs).any id
    induction inputs with
    | nil => simp
    | cons a l ih =>
      show Nat.testBit (fm a ||| List.foldr Nat.lor 0 (List.map fm l)) k =
        (fw a || (List.map fw l).any id)
      rw [Nat.testBit_or, ih, h a]
  | not =>
    cases inputs with
    | nil =>
      show Nat.testBit ((2 ^ K - 1) ^^^ 0) k = !false
      simp [Nat.testBit_two_pow_sub_one, hk]
    | cons a l =>
      show Nat.testBit ((2 ^ K - 1) ^^^ fm a) k = !(fw a)
      rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, h a]
      simp [hk]
  | mod m => simp [bm_okop] at hop
  | maj => simp [bm_okop] at hop

def bm_Rep (k : ℕ) (w : List Bool) (m : List ℕ) : Prop :=
  w.length = m.length ∧ ∀ t, w.getD t false = Nat.testBit (m.getD t 0) k

theorem bm_rep_step (K k : ℕ) (hk : k < K) (g : Gate) (hop : bm_okop g.op = true)
    (w : List Bool) (m : List ℕ) (h : bm_Rep k w m) : bm_Rep k (step w g) (bm_step K m g) := by
  have h1 := h.1
  refine ⟨by rw [step_len, bm_step_len, h1], fun t => ?_⟩
  by_cases hlt : t < w.length
  · rw [step_lt w g t hlt, bm_step_lt K m g t (by omega)]
    exact h.2 t
  · by_cases heq : t = w.length
    · rw [step_last w g t heq, bm_step_last K m g t (heq.trans h1)]
      exact (bm_op_bit K k hk g.op hop g.inputs (fun i => m.getD i 0)
        (fun i => w.getD i false) h.2).symm
    · rw [getD_ge (step w g) t (by rw [step_len]; omega),
        List.getD_eq_default (bm_step K m g) 0 (by rw [bm_step_len]; omega)]
      exact (Nat.zero_testBit k).symm

theorem bm_rep_fold (K k : ℕ) (hk : k < K) (gs : List Gate)
    (hg : ∀ g ∈ gs, bm_okop g.op = true) :
    ∀ (w : List Bool) (m : List ℕ), bm_Rep k w m → bm_Rep k (W gs w) (bm_W K gs m) := by
  induction gs with
  | nil =>
    intro w m h
    exact h
  | cons g gs ih =>
    intro w m h
    show bm_Rep k (W gs (step w g)) (bm_W K gs (bm_step K m g))
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (bm_rep_step K k hk g (hg g (List.mem_cons.mpr (Or.inl rfl))) w m h)

def bm_num : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bm_num l)

theorem bm_num_lt : ∀ l : List Bool, bm_num l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have ih := bm_num_lt l
    have h2 : bm_num (b :: l) = 2 * bm_num l + b.toNat := Nat.bit_val b (bm_num l)
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    rw [h2, List.length_cons, pow_succ]
    omega

theorem bm_num_bit : ∀ (l : List Bool) (i : ℕ), Nat.testBit (bm_num l) i = l.getD i false
  | [], i => by
    first
    | exact Nat.zero_testBit i
    | simp [bm_num]
  | b :: l, 0 => by
    rw [List.getD_cons_zero]
    exact Nat.testBit_bit_zero b (bm_num l)
  | b :: l, i + 1 => by
    rw [List.getD_cons_succ]
    exact (Nat.testBit_bit_succ i b (bm_num l)).trans (bm_num_bit l i)

theorem bm_num_append : ∀ (a b : List Bool), bm_num (a ++ b) = bm_num a + 2 ^ a.length * bm_num b
  | [], b => by simp [bm_num]
  | c :: a, b => by
    have ih := bm_num_append a b
    show Nat.bit c (bm_num (a ++ b)) = Nat.bit c (bm_num a) + 2 ^ (a.length + 1) * bm_num b
    rw [Nat.bit_val, Nat.bit_val, ih, pow_succ]
    ring

def bm_tab (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
    if m = p then 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 else (2 ^ 2 ^ m + 1) * bm_tab p m

theorem bm_bnd (A t : ℕ) (h : t < A) : A * t + t < A * A := by
  have h1 := Nat.mul_le_mul_left A (Nat.succ_le_of_lt h)
  rw [Nat.mul_succ] at h1
  omega

theorem bm_tab_spec (p : ℕ) : ∀ m : ℕ, bm_tab p m < 2 ^ 2 ^ m ∧
    ∀ k : ℕ, k < 2 ^ m → Nat.testBit (bm_tab p m) k = Nat.testBit k p := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, fun k hk => ?_⟩
    · show (0 : ℕ) < 2 ^ 2 ^ 0
      exact Nat.two_pow_pos _
    · have hk0 : k = 0 := by simpa using hk
      rw [hk0]
      show Nat.testBit 0 0 = Nat.testBit 0 p
      rw [Nat.zero_testBit, Nat.zero_testBit]
  | succ m ih =>
    obtain ⟨hb, hbits⟩ := ih
    have hA : 0 < 2 ^ 2 ^ m := Nat.two_pow_pos _
    have hpm : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := Nat.two_pow_succ m
    have hpow : 2 ^ 2 ^ (m + 1) = 2 ^ 2 ^ m * 2 ^ 2 ^ m := by
      rw [hpm, Nat.pow_add]
    by_cases hmp : m = p
    · have hdef : bm_tab p (m + 1) = 2 ^ 2 ^ m * (2 ^ 2 ^ m - 1) + 0 := by
        rw [bm_tab, if_pos hmp]
      rw [hdef, ← hmp]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bm_bnd (2 ^ 2 ^ m) (2 ^ 2 ^ m - 1) (by omega)
        rw [hpow]
        omega
      · rw [Nat.testBit_two_pow_mul_add (2 ^ 2 ^ m - 1) hA k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt, Nat.zero_testBit, Nat.testBit_lt_two_pow hlt]
        · rw [if_neg hlt, Nat.testBit_two_pow_sub_one]
          have h1 : Nat.testBit k m = true := by
            have h2 := Nat.testBit_two_pow_add_eq (k - 2 ^ m) m
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega,
              Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ m from by omega)] at h2
            exact h2
          rw [h1]
          exact decide_eq_true (by omega)
    · have hdef : bm_tab p (m + 1) = 2 ^ 2 ^ m * bm_tab p m + bm_tab p m := by
        rw [bm_tab, if_neg hmp]
        ring
      rw [hdef]
      refine ⟨?_, fun k hk => ?_⟩
      · have h1 := bm_bnd (2 ^ 2 ^ m) (bm_tab p m) hb
        rw [hpow]
        exact h1
      · rw [Nat.testBit_two_pow_mul_add (bm_tab p m) hb k]
        by_cases hlt : k < 2 ^ m
        · rw [if_pos hlt]
          exact hbits k hlt
        · rw [if_neg hlt, hbits (k - 2 ^ m) (by omega)]
          rcases Nat.lt_or_gt_of_ne hmp with hlt2 | hgt
          · have hle : 2 ^ (m + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hlt2
            rw [Nat.testBit_lt_two_pow (show k - 2 ^ m < 2 ^ p from by omega),
              Nat.testBit_lt_two_pow (show k < 2 ^ p from by omega)]
          · have h2 := Nat.testBit_two_pow_add_gt hgt (k - 2 ^ m)
            rw [show 2 ^ m + (k - 2 ^ m) = k from by omega] at h2
            exact h2.symm

def bm_init (n : ℕ) : List ℕ := (List.range n).map (fun p => bm_tab p n)

theorem bm_init_len (n : ℕ) : (bm_init n).length = n := by simp [bm_init]

theorem bm_rep_init (n : ℕ) (x : List Bool) (hx : x.length = n) :
    bm_Rep (bm_num x) x (bm_init n) := by
  have hk : bm_num x < 2 ^ n := by
    have h := bm_num_lt x
    rw [hx] at h
    exact h
  refine ⟨by rw [bm_init_len, hx], fun t => ?_⟩
  by_cases ht : t < n
  · rw [List.getD_eq_getElem (bm_init n) 0 (by rw [bm_init_len]; exact ht)]
    simp only [bm_init, List.getElem_map, List.getElem_range]
    rw [(bm_tab_spec t n).2 _ hk, bm_num_bit]
  · rw [getD_ge x t (by omega), List.getD_eq_default (bm_init n) 0 (by rw [bm_init_len]; omega)]
    exact (Nat.zero_testBit _).symm

def bm_out (n : ℕ) (C : Circuit) : ℕ := (bm_W (2 ^ n) C.gates (bm_init n)).getD C.output 0

theorem bm_eval (n : ℕ) (C : Circuit) (hC : bm_ok C = true) (x : List Bool) (hx : x.length = n) :
    C.eval x = Nat.testBit (bm_out n C) (bm_num x) := by
  have hk : bm_num x < 2 ^ n := by
    have h := bm_num_lt x
    rw [hx] at h
    exact h
  have hg : ∀ g ∈ C.gates, bm_okop g.op = true := fun g hgm => List.all_eq_true.mp hC g hgm
  have h := bm_rep_fold (2 ^ n) (bm_num x) hk C.gates hg x (bm_init n) (bm_rep_init n x hx)
  rw [eval_W]
  exact h.2 C.output

def bm_code {n : ℕ} (x : Fin n → Bool) : ℕ := bm_num (List.ofFn x)

def bm_input (n m : ℕ) : Fin n → Bool := fun i => Nat.testBit m i.val

theorem bm_code_lt {n : ℕ} (x : Fin n → Bool) : bm_code x < 2 ^ n := by
  have h := bm_num_lt (List.ofFn x)
  rw [List.length_ofFn] at h
  exact h

theorem bm_input_code {n : ℕ} (x : Fin n → Bool) : bm_input n (bm_code x) = x := by
  funext i
  show Nat.testBit (bm_num (List.ofFn x)) i.val = x i
  rw [bm_num_bit, ofFn_getD x i.val i.isLt]

def ex_okop (op : GateOp) : Bool :=
  match op with
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def ex_okopn (op : GateOp) : Bool :=
  match op with
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

theorem ex_okop_mem (op : GateOp) (h : ex_okop op = true) :
    op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
  cases op
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl
  all_goals simp [ex_okop] at h

theorem ex_okopn_mem (op : GateOp) (h : ex_okopn op = true) :
    op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
  cases op
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  all_goals simp [ex_okopn] at h

theorem ex_mono2 (C : Circuit)
    (h : C.gates.all (fun g => ex_okop g.op && decide (g.inputs.length ≤ 2)) = true) :
    Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨ex_okop_mem g.op h1.1, h1.2⟩

theorem ex_fanin2 (C : Circuit)
    (h : C.gates.all (fun g => ex_okopn g.op && decide (g.inputs.length ≤ 2)) = true) :
    FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨ex_okopn_mem g.op h1.1, h1.2⟩

def C : Circuit := ⟨[
    ⟨.not, [0]⟩,
    ⟨.not, [1]⟩,
    ⟨.not, [2]⟩,
    ⟨.not, [3]⟩,
    ⟨.not, [4]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.and, [10, 1]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.and, [2, 13]⟩,
    ⟨.and, [12, 3]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [19, 14]⟩,
    ⟨.and, [20, 14]⟩,
    ⟨.and, [21, 14]⟩,
    ⟨.and, [22, 14]⟩,
    ⟨.and, [19, 4]⟩,
    ⟨.and, [20, 4]⟩,
    ⟨.and, [21, 4]⟩,
    ⟨.and, [22, 4]⟩,
    ⟨.and, [15, 23]⟩,
    ⟨.and, [16, 23]⟩,
    ⟨.and, [17, 23]⟩,
    ⟨.and, [18, 23]⟩,
    ⟨.and, [15, 24]⟩,
    ⟨.and, [16, 24]⟩,
    ⟨.and, [17, 24]⟩,
    ⟨.and, [18, 24]⟩,
    ⟨.and, [15, 25]⟩,
    ⟨.and, [16, 25]⟩,
    ⟨.and, [17, 25]⟩,
    ⟨.and, [18, 25]⟩,
    ⟨.and, [15, 26]⟩,
    ⟨.and, [16, 26]⟩,
    ⟨.and, [17, 26]⟩,
    ⟨.and, [18, 26]⟩,
    ⟨.and, [15, 27]⟩,
    ⟨.and, [16, 27]⟩,
    ⟨.and, [17, 27]⟩,
    ⟨.and, [18, 27]⟩,
    ⟨.and, [15, 28]⟩,
    ⟨.and, [16, 28]⟩,
    ⟨.and, [17, 28]⟩,
    ⟨.and, [18, 28]⟩,
    ⟨.and, [15, 29]⟩,
    ⟨.and, [16, 29]⟩,
    ⟨.and, [17, 29]⟩,
    ⟨.and, [18, 29]⟩,
    ⟨.and, [15, 30]⟩,
    ⟨.and, [16, 30]⟩,
    ⟨.and, [17, 30]⟩,
    ⟨.and, [18, 30]⟩,
    ⟨.not, [5]⟩,
    ⟨.not, [6]⟩,
    ⟨.not, [7]⟩,
    ⟨.not, [8]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [63, 64]⟩,
    ⟨.and, [5, 64]⟩,
    ⟨.and, [63, 6]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.and, [65, 66]⟩,
    ⟨.and, [7, 66]⟩,
    ⟨.and, [65, 8]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.and, [72, 67]⟩,
    ⟨.and, [73, 67]⟩,
    ⟨.and, [74, 67]⟩,
    ⟨.and, [75, 67]⟩,
    ⟨.and, [72, 9]⟩,
    ⟨.and, [73, 9]⟩,
    ⟨.and, [74, 9]⟩,
    ⟨.and, [75, 9]⟩,
    ⟨.and, [68, 76]⟩,
    ⟨.and, [69, 76]⟩,
    ⟨.and, [70, 76]⟩,
    ⟨.and, [71, 76]⟩,
    ⟨.and, [68, 77]⟩,
    ⟨.and, [69, 77]⟩,
    ⟨.and, [70, 77]⟩,
    ⟨.and, [71, 77]⟩,
    ⟨.and, [68, 78]⟩,
    ⟨.and, [69, 78]⟩,
    ⟨.and, [70, 78]⟩,
    ⟨.and, [71, 78]⟩,
    ⟨.and, [68, 79]⟩,
    ⟨.and, [69, 79]⟩,
    ⟨.and, [70, 79]⟩,
    ⟨.and, [71, 79]⟩,
    ⟨.and, [68, 80]⟩,
    ⟨.and, [69, 80]⟩,
    ⟨.and, [70, 80]⟩,
    ⟨.and, [71, 80]⟩,
    ⟨.and, [68, 81]⟩,
    ⟨.and, [69, 81]⟩,
    ⟨.and, [70, 81]⟩,
    ⟨.and, [71, 81]⟩,
    ⟨.and, [68, 82]⟩,
    ⟨.and, [69, 82]⟩,
    ⟨.and, [70, 82]⟩,
    ⟨.and, [71, 82]⟩,
    ⟨.and, [68, 83]⟩,
    ⟨.and, [69, 83]⟩,
    ⟨.and, [70, 83]⟩,
    ⟨.and, [71, 83]⟩,
    ⟨.or, [62, 48]⟩,
    ⟨.or, [59, 33]⟩,
    ⟨.or, [49, 39]⟩,
    ⟨.or, [52, 36]⟩,
    ⟨.or, [56, 37]⟩,
    ⟨.or, [54, 50]⟩,
    ⟨.or, [47, 44]⟩,
    ⟨.or, [57, 38]⟩,
    ⟨.or, [61, 41]⟩,
    ⟨.or, [60, 34]⟩,
    ⟨.or, [116, 46]⟩,
    ⟨.or, [55, 53]⟩,
    ⟨.or, [58, 40]⟩,
    ⟨.or, [123, 32]⟩,
    ⟨.or, [125, 118]⟩,
    ⟨.or, [50, 43]⟩,
    ⟨.or, [121, 119]⟩,
    ⟨.or, [117, 35]⟩,
    ⟨.or, [119, 39]⟩,
    ⟨.or, [44, 42]⟩,
    ⟨.or, [129, 53]⟩,
    ⟨.or, [51, 45]⟩,
    ⟨.or, [59, 35]⟩,
    ⟨.or, [120, 31]⟩,
    ⟨.or, [122, 42]⟩,
    ⟨.or, [52, 49]⟩,
    ⟨.or, [140, 50]⟩,
    ⟨.or, [127, 40]⟩,
    ⟨.or, [55, 54]⟩,
    ⟨.or, [138, 57]⟩,
    ⟨.or, [116, 34]⟩,
    ⟨.or, [117, 31]⟩,
    ⟨.or, [128, 60]⟩,
    ⟨.or, [122, 58]⟩,
    ⟨.or, [131, 61]⟩,
    ⟨.or, [133, 38]⟩,
    ⟨.or, [126, 36]⟩,
    ⟨.or, [124, 123]⟩,
    ⟨.or, [137, 59]⟩,
    ⟨.or, [132, 42]⟩,
    ⟨.or, [139, 125]⟩,
    ⟨.or, [56, 52]⟩,
    ⟨.or, [147, 61]⟩,
    ⟨.or, [158, 116]⟩,
    ⟨.or, [58, 32]⟩,
    ⟨.or, [129, 45]⟩,
    ⟨.or, [159, 118]⟩,
    ⟨.or, [120, 41]⟩,
    ⟨.or, [62, 51]⟩,
    ⟨.or, [55, 41]⟩,
    ⟨.or, [165, 130]⟩,
    ⟨.or, [134, 126]⟩,
    ⟨.or, [167, 38]⟩,
    ⟨.or, [57, 43]⟩,
    ⟨.or, [136, 118]⟩,
    ⟨.or, [62, 46]⟩,
    ⟨.or, [141, 128]⟩,
    ⟨.or, [49, 48]⟩,
    ⟨.or, [173, 37]⟩,
    ⟨.or, [143, 43]⟩,
    ⟨.or, [121, 32]⟩,
    ⟨.or, [45, 34]⟩,
    ⟨.or, [150, 36]⟩,
    ⟨.or, [135, 124]⟩,
    ⟨.or, [33, 126]⟩,
    ⟨.or, [130, 157]⟩,
    ⟨.or, [160, 179]⟩,
    ⟨.or, [180, 181]⟩,
    ⟨.or, [183, 182]⟩,
    ⟨.and, [84, 184]⟩,
    ⟨.or, [32, 49]⟩,
    ⟨.or, [60, 117]⟩,
    ⟨.or, [132, 163]⟩,
    ⟨.or, [186, 187]⟩,
    ⟨.or, [189, 188]⟩,
    ⟨.and, [85, 190]⟩,
    ⟨.or, [39, 142]⟩,
    ⟨.or, [145, 157]⟩,
    ⟨.or, [192, 193]⟩,
    ⟨.and, [86, 194]⟩,
    ⟨.or, [51, 124]⟩,
    ⟨.or, [147, 175]⟩,
    ⟨.or, [196, 197]⟩,
    ⟨.or, [198, 176]⟩,
    ⟨.and, [87, 199]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.or, [127, 139]⟩,
    ⟨.or, [141, 179]⟩,
    ⟨.or, [201, 202]⟩,
    ⟨.or, [204, 203]⟩,
    ⟨.and, [88, 205]⟩,
    ⟨.or, [48, 136]⟩,
    ⟨.or, [154, 155]⟩,
    ⟨.or, [207, 208]⟩,
    ⟨.or, [209, 163]⟩,
    ⟨.and, [89, 210]⟩,
    ⟨.or, [141, 143]⟩,
    ⟨.or, [153, 154]⟩,
    ⟨.or, [212, 213]⟩,
    ⟨.or, [214, 171]⟩,
    ⟨.and, [90, 215]⟩,
    ⟨.or, [38, 120]⟩,
    ⟨.or, [124, 146]⟩,
    ⟨.or, [217, 218]⟩,
    ⟨.or, [219, 149]⟩,
    ⟨.and, [91, 220]⟩,
    ⟨.or, [31, 40]⟩,
    ⟨.or, [46, 53]⟩,
    ⟨.or, [121, 124]⟩,
    ⟨.or, [222, 223]⟩,
    ⟨.or, [224, 174]⟩,
    ⟨.or, [225, 226]⟩,
    ⟨.and, [92, 227]⟩,
    ⟨.or, [32, 127]⟩,
    ⟨.or, [146, 151]⟩,
    ⟨.or, [229, 230]⟩,
    ⟨.or, [231, 178]⟩,
    ⟨.and, [93, 232]⟩,
    ⟨.or, [36, 44]⟩,
    ⟨.or, [145, 160]⟩,
    ⟨.or, [234, 235]⟩,
    ⟨.or, [236, 174]⟩,
    ⟨.and, [94, 237]⟩,
    ⟨.or, [134, 156]⟩,
    ⟨.or, [164, 169]⟩,
    ⟨.or, [239, 240]⟩,
    ⟨.and, [95, 241]⟩,
    ⟨.or, [31, 35]⟩,
    ⟨.or, [47, 148]⟩,
    ⟨.or, [243, 244]⟩,
    ⟨.or, [245, 168]⟩,
    ⟨.and, [96, 246]⟩,
    ⟨.or, [57, 60]⟩,
    ⟨.or, [135, 144]⟩,
    ⟨.or, [248, 249]⟩,
    ⟨.or, [250, 152]⟩,
    ⟨.and, [97, 251]⟩,
    ⟨.or, [117, 136]⟩,
    ⟨.or, [150, 172]⟩,
    ⟨.or, [253, 254]⟩,
    ⟨.and, [98, 255]⟩,
    ⟨.or, [45, 133]⟩,
    ⟨.or, [140, 152]⟩,
    ⟨.or, [257, 258]⟩,
    ⟨.or, [259, 175]⟩,
    ⟨.and, [99, 260]⟩,
    ⟨.or, [46, 47]⟩,
    ⟨.or, [151, 156]⟩,
    ⟨.or, [262, 263]⟩,
    ⟨.or, [264, 172]⟩,
    ⟨.and, [100, 265]⟩,
    ⟨.or, [37, 46]⟩,
    ⟨.or, [55, 132]⟩,
    ⟨.or, [135, 161]⟩,
    ⟨.or, [267, 268]⟩,
    ⟨.or, [270, 269]⟩,
    ⟨.and, [101, 271]⟩,
    ⟨.or, [34, 53]⟩,
    ⟨.or, [117, 134]⟩,
    ⟨.or, [273, 274]⟩,
    ⟨.or, [275, 149]⟩,
    ⟨.and, [102, 276]⟩,
    ⟨.or, [43, 56]⟩,
    ⟨.or, [152, 170]⟩,
    ⟨.or, [278, 279]⟩,
    ⟨.and, [103, 280]⟩,
    ⟨.or, [43, 120]⟩,
    ⟨.or, [130, 161]⟩,
    ⟨.or, [282, 283]⟩,
    ⟨.and, [104, 284]⟩,
    ⟨.or, [37, 142]⟩,
    ⟨.or, [148, 162]⟩,
    ⟨.or, [286, 287]⟩,
    ⟨.and, [105, 288]⟩,
    ⟨.or, [51, 116]⟩,
    ⟨.or, [130, 139]⟩,
    ⟨.or, [153, 155]⟩,
    ⟨.or, [290, 291]⟩,
    ⟨.or, [293, 292]⟩,
    ⟨.and, [106, 294]⟩,
    ⟨.or, [122, 127]⟩,
    ⟨.or, [131, 137]⟩,
    ⟨.or, [296, 297]⟩,
    ⟨.or, [298, 168]⟩,
    ⟨.and, [107, 299]⟩,
    ⟨.or, [37, 40]⟩,
    ⟨.or, [51, 131]⟩,
    ⟨.or, [145, 166]⟩,
    ⟨.or, [301, 302]⟩,
    ⟨.or, [304, 303]⟩,
    ⟨.and, [108, 305]⟩,
    ⟨.or, [45, 47]⟩,
    ⟨.or, [55, 57]⟩,
    ⟨.or, [162, 176]⟩,
    ⟨.or, [307, 308]⟩,
    ⟨.or, [310, 309]⟩,
    ⟨.and, [109, 311]⟩,
    ⟨.or, [138, 142]⟩,
    ⟨.or, [313, 166]⟩,
    ⟨.and, [110, 314]⟩,
    ⟨.or, [48, 177]⟩,
    ⟨.or, [316, 178]⟩,
    ⟨.and, [111, 317]⟩,
    ⟨.or, [33, 49]⟩,
    ⟨.or, [121, 128]⟩,
    ⟨.or, [137, 146]⟩,
    ⟨.or, [319, 320]⟩,
    ⟨.or, [321, 169]⟩,
    ⟨.or, [322, 323]⟩,
    ⟨.and, [112, 324]⟩,
    ⟨.or, [39, 144]⟩,
    ⟨.or, [149, 164]⟩,
    ⟨.or, [326, 327]⟩,
    ⟨.and, [113, 328]⟩,
    ⟨.or, [41, 62]⟩,
    ⟨.or, [118, 119]⟩,
    ⟨.or, [144, 148]⟩,
    ⟨.or, [330, 331]⟩,
    ⟨.or, [332, 151]⟩,
    ⟨.or, [333, 334]⟩,
    ⟨.and, [114, 335]⟩,
    ⟨.or, [33, 40]⟩,
    ⟨.or, [54, 170]⟩,
    ⟨.or, [171, 177]⟩,
    ⟨.or, [337, 338]⟩,
    ⟨.or, [340, 339]⟩,
    ⟨.and, [115, 341]⟩,
    ⟨.or, [185, 191]⟩,
    ⟨.or, [195, 200]⟩,
    ⟨.or, [206, 211]⟩,
    ⟨.or, [216, 221]⟩,
    ⟨.or, [228, 233]⟩,
    ⟨.or, [238, 242]⟩,
    ⟨.or, [247, 252]⟩,
    ⟨.or, [256, 261]⟩,
    ⟨.or, [266, 272]⟩,
    ⟨.or, [277, 281]⟩,
    ⟨.or, [285, 289]⟩,
    ⟨.or, [295, 300]⟩,
    ⟨.or, [306, 312]⟩,
    ⟨.or, [315, 318]⟩,
    ⟨.or, [325, 329]⟩,
    ⟨.or, [336, 342]⟩,
    ⟨.or, [343, 344]⟩,
    ⟨.or, [345, 346]⟩,
    ⟨.or, [347, 348]⟩,
    ⟨.or, [349, 350]⟩,
    ⟨.or, [351, 352]⟩,
    ⟨.or, [353, 354]⟩,
    ⟨.or, [355, 356]⟩,
    ⟨.or, [357, 358]⟩,
    ⟨.or, [359, 360]⟩,
    ⟨.or, [361, 362]⟩,
    ⟨.or, [363, 364]⟩,
    ⟨.or, [365, 366]⟩,
    ⟨.or, [367, 368]⟩,
    ⟨.or, [369, 370]⟩,
    ⟨.or, [371, 372]⟩], 373⟩
def target : (Fin 10 → Bool) → Bool := (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0xf2e8bac10a6043d9457138034725c66e70255481935a6c64005908b76782a258f242212a808cc37840c7587731c008681fe2432ed77945531ae8b7a126a59084808bb1419a92806024a6a4951998ca080462a035454001fbd121d148e7fc1805c0db52e001730db248cebe22450196149d550a91d225c20b821a462b02611918 (32 * u.val + v.val)))
def resultMask : Nat := ([3928403214, 850134118, 371796240, 1373115911, 1130638425, 385502434, 3581200000, 3389203656, 1087276609, 3511292094, 470163570, 2788168041, 2820899761, 2776803360, 1550586502, 2437151284, 975536861, 94955746, 409018668, 2252771746, 637817290, 4161743685, 3871215081, 2172383648, 891033432, 3582935303, 822947096, 1074417704, 2359185932, 2307989760, 3114534836, 2227487630] : List Nat).foldr (fun lo hi => lo + 2^32*hi) 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checkMask : bm_out 10 C = resultMask := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem tableBits : ∀ j : Fin 1024, resultMask.testBit j.val = target (bm_input 10 j.val) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem finish : HasCircuitSize 10 target 364 := by
  refine ⟨C, ex_fanin2 C (by decide +kernel), by decide +kernel, ?_⟩
  intro x
  rw [bm_eval 10 C (by decide +kernel) _ (by simp), checkMask]
  rw [show bm_num (List.ofFn x) = bm_code x from rfl]
  have hh := tableBits ⟨bm_code x, bm_code_lt x⟩
  simpa only [bm_input_code] using hh

end PEqualNP.Outside.L_meta_17153_aux

theorem PEqualNP.Outside.L_meta_17153 : PEqualNP.MetaComplexity.HasCircuitSize 10 (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0xf2e8bac10a6043d9457138034725c66e70255481935a6c64005908b76782a258f242212a808cc37840c7587731c008681fe2432ed77945531ae8b7a126a59084808bb1419a92806024a6a4951998ca080462a035454001fbd121d148e7fc1805c0db52e001730db248cebe22450196149d550a91d225c20b821a462b02611918 (32 * u.val + v.val))) 365 := by
  obtain ⟨C, basis, small, computes⟩ := PEqualNP.Outside.L_meta_17153_aux.finish
  exact ⟨C, basis, by omega, computes⟩
