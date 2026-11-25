import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17145_aux

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
    ⟨.or, [56, 52]⟩,
    ⟨.or, [41, 37]⟩,
    ⟨.or, [59, 55]⟩,
    ⟨.or, [46, 40]⟩,
    ⟨.or, [44, 39]⟩,
    ⟨.or, [50, 31]⟩,
    ⟨.or, [35, 34]⟩,
    ⟨.or, [51, 36]⟩,
    ⟨.or, [117, 49]⟩,
    ⟨.or, [118, 116]⟩,
    ⟨.or, [61, 42]⟩,
    ⟨.or, [122, 57]⟩,
    ⟨.or, [121, 48]⟩,
    ⟨.or, [124, 119]⟩,
    ⟨.or, [120, 32]⟩,
    ⟨.or, [54, 33]⟩,
    ⟨.or, [128, 62]⟩,
    ⟨.or, [47, 31]⟩,
    ⟨.or, [60, 49]⟩,
    ⟨.or, [126, 58]⟩,
    ⟨.or, [134, 40]⟩,
    ⟨.or, [125, 45]⟩,
    ⟨.or, [131, 57]⟩,
    ⟨.or, [53, 38]⟩,
    ⟨.or, [135, 43]⟩,
    ⟨.or, [123, 32]⟩,
    ⟨.or, [123, 47]⟩,
    ⟨.or, [142, 58]⟩,
    ⟨.or, [138, 125]⟩,
    ⟨.or, [117, 116]⟩,
    ⟨.or, [127, 32]⟩,
    ⟨.or, [55, 45]⟩,
    ⟨.or, [140, 120]⟩,
    ⟨.or, [56, 31]⟩,
    ⟨.or, [130, 46]⟩,
    ⟨.or, [41, 35]⟩,
    ⟨.or, [116, 59]⟩,
    ⟨.or, [57, 53]⟩,
    ⟨.or, [149, 41]⟩,
    ⟨.or, [141, 40]⟩,
    ⟨.or, [129, 62]⟩,
    ⟨.or, [147, 117]⟩,
    ⟨.or, [153, 45]⟩,
    ⟨.or, [148, 124]⟩,
    ⟨.or, [144, 53]⟩,
    ⟨.or, [160, 130]⟩,
    ⟨.or, [137, 44]⟩,
    ⟨.or, [43, 39]⟩,
    ⟨.or, [158, 47]⟩,
    ⟨.or, [119, 59]⟩,
    ⟨.or, [154, 139]⟩,
    ⟨.or, [137, 37]⟩,
    ⟨.or, [58, 49]⟩,
    ⟨.or, [143, 60]⟩,
    ⟨.or, [129, 121]⟩,
    ⟨.or, [133, 39]⟩,
    ⟨.or, [145, 119]⟩,
    ⟨.or, [132, 127]⟩,
    ⟨.or, [34, 33]⟩,
    ⟨.or, [136, 33]⟩,
    ⟨.or, [133, 60]⟩,
    ⟨.or, [129, 60]⟩,
    ⟨.or, [152, 122]⟩,
    ⟨.or, [87, 108]⟩,
    ⟨.or, [179, 112]⟩,
    ⟨.and, [146, 180]⟩,
    ⟨.or, [101, 115]⟩,
    ⟨.and, [175, 182]⟩,
    ⟨.or, [35, 121]⟩,
    ⟨.or, [130, 157]⟩,
    ⟨.or, [184, 185]⟩,
    ⟨.and, [84, 186]⟩,
    ⟨.or, [42, 127]⟩,
    ⟨.or, [131, 165]⟩,
    ⟨.or, [188, 189]⟩,
    ⟨.or, [190, 166]⟩,
    ⟨.and, [85, 191]⟩,
    ⟨.or, [37, 150]⟩,
    ⟨.or, [152, 164]⟩,
    ⟨.or, [193, 194]⟩,
    ⟨.and, [86, 195]⟩,
    ⟨.or, [48, 119]⟩,
    ⟨.or, [125, 135]⟩,
    ⟨.or, [197, 198]⟩,
    ⟨.and, [87, 199]⟩,
    ⟨.or, [140, 155]⟩,
    ⟨.or, [162, 173]⟩,
    ⟨.or, [201, 202]⟩,
    ⟨.and, [88, 203]⟩,
    ⟨.or, [52, 58]⟩,
    ⟨.or, [127, 157]⟩,
    ⟨.or, [205, 206]⟩,
    ⟨.or, [207, 171]⟩,
    ⟨.and, [89, 208]⟩,
    ⟨.or, [33, 44]⟩,
    ⟨.or, [132, 168]⟩,
    ⟨.or, [210, 211]⟩,
    ⟨.and, [90, 212]⟩,
    ⟨.or, [151, 161]⟩,
    ⟨.or, [214, 169]⟩,
    ⟨.and, [91, 215]⟩,
    ⟨.or, [116, 147]⟩,
    ⟨.or, [217, 170]⟩,
    ⟨.and, [92, 218]⟩,
    ⟨.or, [50, 136]⟩,
    ⟨.or, [141, 151]⟩,
    ⟨.or, [220, 221]⟩,
    ⟨.or, [222, 162]⟩,
    ⟨.and, [93, 223]⟩,
    ⟨.or, [48, 126]⟩,
    ⟨.or, [133, 136]⟩,
    ⟨.or, [139, 167]⟩,
    ⟨.or, [225, 226]⟩,
    ⟨.or, [228, 227]⟩,
    ⟨.and, [94, 229]⟩,
    ⟨.or, [118, 126]⟩,
    ⟨.or, [130, 174]⟩,
    ⟨.or, [231, 232]⟩,
    ⟨.or, [233, 177]⟩,
    ⟨.and, [95, 234]⟩,
    ⟨.or, [132, 139]⟩,
    ⟨.or, [236, 145]⟩,
    ⟨.and, [96, 237]⟩,
    ⟨.or, [56, 118]⟩,
    ⟨.or, [141, 163]⟩,
    ⟨.or, [239, 240]⟩,
    ⟨.or, [241, 170]⟩,
    ⟨.and, [97, 242]⟩,
    ⟨.or, [121, 172]⟩,
    ⟨.or, [244, 174]⟩,
    ⟨.and, [98, 245]⟩,
    ⟨.or, [35, 144]⟩,
    ⟨.or, [247, 159]⟩,
    ⟨.and, [99, 248]⟩,
    ⟨.or, [55, 116]⟩,
    ⟨.or, [131, 150]⟩,
    ⟨.or, [151, 168]⟩,
    ⟨.or, [250, 251]⟩,
    ⟨.or, [253, 252]⟩,
    ⟨.and, [100, 254]⟩,
    ⟨.or, [44, 46]⟩,
    ⟨.or, [51, 54]⟩,
    ⟨.or, [134, 166]⟩,
    ⟨.or, [256, 257]⟩,
    ⟨.or, [259, 258]⟩,
    ⟨.and, [102, 260]⟩,
    ⟨.or, [155, 171]⟩,
    ⟨.or, [262, 178]⟩,
    ⟨.and, [103, 263]⟩,
    ⟨.or, [47, 55]⟩,
    ⟨.or, [126, 163]⟩,
    ⟨.or, [172, 173]⟩,
    ⟨.or, [265, 266]⟩,
    ⟨.or, [268, 267]⟩,
    ⟨.and, [104, 269]⟩,
    ⟨.or, [35, 120]⟩,
    ⟨.or, [132, 164]⟩,
    ⟨.or, [271, 272]⟩,
    ⟨.and, [105, 273]⟩,
    ⟨.or, [33, 148]⟩,
    ⟨.or, [156, 178]⟩,
    ⟨.or, [275, 276]⟩,
    ⟨.and, [106, 277]⟩,
    ⟨.or, [132, 167]⟩,
    ⟨.or, [279, 169]⟩,
    ⟨.and, [107, 280]⟩,
    ⟨.or, [35, 165]⟩,
    ⟨.or, [282, 176]⟩,
    ⟨.and, [109, 283]⟩,
    ⟨.or, [34, 42]⟩,
    ⟨.or, [138, 177]⟩,
    ⟨.or, [285, 286]⟩,
    ⟨.and, [110, 287]⟩,
    ⟨.or, [118, 122]⟩,
    ⟨.or, [143, 150]⟩,
    ⟨.or, [289, 290]⟩,
    ⟨.and, [111, 291]⟩,
    ⟨.or, [43, 45]⟩,
    ⟨.or, [54, 149]⟩,
    ⟨.or, [293, 294]⟩,
    ⟨.or, [295, 156]⟩,
    ⟨.and, [112, 296]⟩,
    ⟨.or, [118, 123]⟩,
    ⟨.or, [159, 176]⟩,
    ⟨.or, [298, 299]⟩,
    ⟨.and, [113, 300]⟩,
    ⟨.or, [129, 133]⟩,
    ⟨.or, [302, 161]⟩,
    ⟨.and, [114, 303]⟩,
    ⟨.or, [31, 123]⟩,
    ⟨.and, [115, 305]⟩,
    ⟨.or, [181, 183]⟩,
    ⟨.or, [187, 192]⟩,
    ⟨.or, [196, 200]⟩,
    ⟨.or, [204, 209]⟩,
    ⟨.or, [213, 216]⟩,
    ⟨.or, [219, 224]⟩,
    ⟨.or, [230, 235]⟩,
    ⟨.or, [238, 243]⟩,
    ⟨.or, [246, 249]⟩,
    ⟨.or, [255, 261]⟩,
    ⟨.or, [264, 270]⟩,
    ⟨.or, [274, 278]⟩,
    ⟨.or, [281, 284]⟩,
    ⟨.or, [288, 292]⟩,
    ⟨.or, [297, 301]⟩,
    ⟨.or, [304, 306]⟩,
    ⟨.or, [307, 308]⟩,
    ⟨.or, [309, 310]⟩,
    ⟨.or, [311, 312]⟩,
    ⟨.or, [313, 314]⟩,
    ⟨.or, [315, 316]⟩,
    ⟨.or, [317, 318]⟩,
    ⟨.or, [319, 320]⟩,
    ⟨.or, [321, 322]⟩,
    ⟨.or, [323, 324]⟩,
    ⟨.or, [325, 326]⟩,
    ⟨.or, [327, 328]⟩,
    ⟨.or, [329, 330]⟩,
    ⟨.or, [331, 332]⟩,
    ⟨.or, [333, 334]⟩,
    ⟨.or, [335, 336]⟩], 337⟩
def target : (Fin 10 → Bool) → Bool := (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val)))
def resultMask : Nat := ([17327443, 381718173, 375513410, 1596099098, 3745151547, 220284249, 2282627077, 1072768310, 53265985, 859596338, 1936149185, 1896132430, 2187986113, 320640867, 36210253, 1604599124, 195339542, 537133572, 584361089, 305201979, 3341524825, 2219532561, 3659841372, 3141222497, 67108890, 805405201, 612666956, 420585786, 2256852571, 2031435105, 400926535, 538182181] : List Nat).foldr (fun lo hi => lo + 2^32*hi) 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem checkMask : bm_out 10 C = resultMask := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem tableBits : ∀ j : Fin 1024, resultMask.testBit j.val = target (bm_input 10 j.val) := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem finish : HasCircuitSize 10 target 328 := by
  refine ⟨C, ex_fanin2 C (by decide +kernel), by decide +kernel, ?_⟩
  intro x
  rw [bm_eval 10 C (by decide +kernel) _ (by simp), checkMask]
  rw [show bm_num (List.ofFn x) = bm_code x from rfl]
  have hh := tableBits ⟨bm_code x, bm_code_lt x⟩
  simpa only [bm_input_code] using hh

end PEqualNP.Outside.L_meta_17145_aux

theorem PEqualNP.Outside.L_meta_17145 : PEqualNP.MetaComplexity.HasCircuitSize 10 (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val))) 330 := by
  obtain ⟨C, basis, small, computes⟩ := PEqualNP.Outside.L_meta_17145_aux.finish
  exact ⟨C, basis, by omega, computes⟩
