import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6214

-- The fold lemmas below (step, W and their properties) are taken from the checked file
-- L_meta_5465.lean of this repository (Apache-2.0).

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


-- Padding every gate to exactly two earlier wires; wire 26 is true and wire 27 is false.
def fixw (j a : ℕ) : ℕ := if a < 28 + j then a else 27

def cw : GateOp → ℕ
  | GateOp.and => 26
  | _ => 27

def fixin (j : ℕ) (op : GateOp) : List ℕ → List ℕ
  | [] => [cw op, cw op]
  | [a] => [fixw j a, fixw j a]
  | a :: b :: _ => [fixw j a, fixw j b]

def fix (j : ℕ) (g : Gate) : Gate := ⟨g.op, fixin j g.op g.inputs⟩

def nrm : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => fix j g :: nrm (j + 1) gs

theorem fixw_lt (j a : ℕ) : fixw j a < 28 + j := by
  unfold fixw; split <;> omega

theorem cw_lt (j : ℕ) (op : GateOp) : cw op < 28 + j := by
  cases op <;> simp [cw] <;> omega

theorem fix_len (j : ℕ) (g : Gate) : (fix j g).inputs.length = 2 := by
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, t⟩⟩ <;> simp [fix, fixin]

theorem fix_lt (j : ℕ) (g : Gate) : ∀ w ∈ (fix j g).inputs, w < 28 + j := by
  obtain ⟨op, ins⟩ := g
  have h1 := cw_lt j op
  rcases ins with _ | ⟨a, _ | ⟨b, t⟩⟩
  · intro w hw
    simp [fix, fixin] at hw
    omega
  · intro w hw
    simp [fix, fixin] at hw
    have := fixw_lt j a
    omega
  · intro w hw
    simp [fix, fixin] at hw
    have := fixw_lt j a
    have := fixw_lt j b
    rcases hw with rfl | rfl <;> omega

theorem fixw_val (j a : ℕ) (w : List Bool) (hl : w.length = 28 + j)
    (h27 : w.getD 27 false = false) : w.getD (fixw j a) false = w.getD a false := by
  unfold fixw
  split
  · rfl
  · rw [h27, getD_ge w a (by omega)]

theorem fix_step (j : ℕ) (g : Gate) (w : List Bool) (hl : w.length = 28 + j)
    (h26 : w.getD 26 false = true) (h27 : w.getD 27 false = false)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h2 : g.inputs.length ≤ 2) :
    step w (fix j g) = step w g := by
  obtain ⟨op, ins⟩ := g
  unfold step
  congr 2
  simp only at hop h2
  rcases ins with _ | ⟨a, _ | ⟨b, t⟩⟩
  · rcases hop with rfl | rfl
    · simp only [fix, fixin, cw, List.map_cons, List.map_nil, h26]; rfl
    · simp only [fix, fixin, cw, List.map_cons, List.map_nil, h27]; rfl
  · rcases hop with rfl | rfl
    · simp only [fix, fixin, List.map_cons, List.map_nil, fixw_val j a w hl h27, eval_and2,
        eval_and1, Bool.and_self]
    · simp only [fix, fixin, List.map_cons, List.map_nil, fixw_val j a w hl h27, eval_or2,
        eval_or1, Bool.or_self]
  · have ht : t = [] := by
      simp only [List.length_cons] at h2
      exact List.length_eq_zero_iff.mp (by omega)
    subst ht
    simp only [fix, fixin, List.map_cons, List.map_nil, fixw_val j a w hl h27,
      fixw_val j b w hl h27]

theorem nrm_len : ∀ (gs : List Gate) (j : ℕ), (nrm j gs).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro j; rfl
  | cons g gs ih => intro j; simp [nrm, ih]

theorem nrm_W : ∀ (gs : List Gate) (j : ℕ) (w : List Bool), w.length = 28 + j →
    w.getD 26 false = true → w.getD 27 false = false →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    W (nrm j gs) w = W gs w := by
  intro gs
  induction gs with
  | nil => intro j w _ _ _ _; rfl
  | cons g gs ih =>
    intro j w hl h26 h27 hm
    have hg := hm g List.mem_cons_self
    show W (fix j g :: nrm (j + 1) gs) w = W (g :: gs) w
    rw [W_cons, W_cons, fix_step j g w hl h26 h27 hg.1 hg.2]
    apply ih (j + 1) (step w g)
    · rw [step_len]; omega
    · rw [step_lt w g 26 (by omega)]; exact h26
    · rw [step_lt w g 27 (by omega)]; exact h27
    · intro g' hg'; exact hm g' (List.mem_cons_of_mem _ hg')

theorem nrm_idx : ∀ (gs : List Gate) (j k : ℕ) (hk : k < (nrm j gs).length),
    ((nrm j gs)[k]).inputs.length = 2 ∧ ∀ w ∈ ((nrm j gs)[k]).inputs, w < 28 + j + k := by
  intro gs
  induction gs with
  | nil => intro j k hk; simp [nrm] at hk
  | cons g gs ih =>
    intro j k hk
    cases k with
    | zero =>
      show (fix j g).inputs.length = 2 ∧ ∀ w ∈ (fix j g).inputs, w < 28 + j + 0
      exact ⟨fix_len j g, fix_lt j g⟩
    | succ k =>
      have hk' : k < (nrm (j + 1) gs).length := by
        simp only [nrm, List.length_cons] at hk; omega
      have := ih (j + 1) k hk'
      show ((nrm (j + 1) gs)[k]).inputs.length = 2 ∧ ∀ w ∈ ((nrm (j + 1) gs)[k]).inputs, w < 28 + j + (k + 1)
      refine ⟨this.1, fun w hw => ?_⟩
      have := this.2 w hw
      omega

theorem nrm_op : ∀ (gs : List Gate) (j : ℕ), ∀ g ∈ nrm j gs, ∃ g0 ∈ gs, g.op = g0.op ∧ g.inputs.length = 2 := by
  intro gs
  induction gs with
  | nil => intro j g hg; simp [nrm] at hg
  | cons g0 gs ih =>
    intro j g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨g0, List.mem_cons_self, rfl, fix_len j g0⟩
    · obtain ⟨g1, h1, h2⟩ := ih (j + 1) g hg
      exact ⟨g1, List.mem_cons_of_mem _ h1, h2⟩

theorem main (C : Circuit) (hC : Monotone2 C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
      (∀ k : Fin D.gates.length, (D.gates.get k).inputs.length = 2 ∧
        ∀ w ∈ (D.gates.get k).inputs, w < 28 + k.val) ∧
      ∀ x : Fin 26 → Bool, D.wires (List.ofFn x ++ [true, false]) =
        C.wires (List.ofFn x ++ [true, false]) := by
  have hC' : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hC g hg
    exact ⟨by simpa using this.1, this.2⟩
  refine ⟨⟨nrm 0 C.gates, C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, h0, hop, hl⟩ := nrm_op C.gates 0 g hg
    have := hC g0 h0
    exact ⟨by rw [hop]; exact this.1, by omega⟩
  · exact nrm_len C.gates 0
  · intro k
    have := nrm_idx C.gates 0 k.val k.isLt
    rw [List.get_eq_getElem]
    refine ⟨this.1, fun w hw => ?_⟩
    have := this.2 w hw
    omega
  · intro x
    show W (nrm 0 C.gates) _ = W C.gates _
    exact nrm_W C.gates 0 _ (by simp) (by simp [List.getD_eq_getElem?_getD])
      (by simp [List.getD_eq_getElem?_getD]) hC'

end PEqualNP.Outside.L_meta_6214

theorem PEqualNP.Outside.L_meta_6214 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size = x1.size ∧ (∀ (x4 : Fin x3.gates.length), (x3.gates.get x4).inputs.length = (2 : ℕ) ∧ ∀ x5 ∈ (x3.gates.get x4).inputs, x5 < (28 : ℕ) + ↑x4) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), x3.wires (List.ofFn x4 ++ [Bool.true, Bool.false]) = x1.wires (List.ofFn x4 ++ [Bool.true, Bool.false]) := by
  intro C hC
  exact PEqualNP.Outside.L_meta_6214.main C hC
