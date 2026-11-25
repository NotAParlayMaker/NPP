import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5720

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


-- Straight-line programs of functions: each entry is the AND or the OR of two sources,
-- a source being an input projection or an earlier entry (the list is newest first).

def bop {n : ℕ} (b : Bool) (u v : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => if b then (u x && v x) else (u x || v x)

def proj {n : ℕ} (k : Fin n) : (Fin n → Bool) → Bool := fun x => x k

def zero {n : ℕ} : (Fin n → Bool) → Bool := fun _ => false

def Src {n : ℕ} (L : List ((Fin n → Bool) → Bool)) (u : (Fin n → Bool) → Bool) : Prop :=
  (∃ k : Fin n, u = proj k) ∨ u ∈ L

def SLP {n : ℕ} : List ((Fin n → Bool) → Bool) → Prop
  | [] => True
  | h :: L => SLP L ∧ ∃ (u v : (Fin n → Bool) → Bool) (b : Bool), Src L u ∧ Src L v ∧ h = bop b u v

def res {n : ℕ} (i : Fin n) (h : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  fun x => h (Function.update x i false)

theorem Src_cons {n : ℕ} {L : List ((Fin n → Bool) → Bool)} {u : (Fin n → Bool) → Bool}
    (h : (Fin n → Bool) → Bool) (hu : Src L u) : Src (h :: L) u := by
  rcases hu with hk | hm
  · exact Or.inl hk
  · exact Or.inr (List.mem_cons_of_mem _ hm)

theorem res_proj_self {n : ℕ} (i : Fin n) : res i (proj i) = zero := by
  funext x; simp [res, proj, zero]

theorem res_proj_ne {n : ℕ} (i k : Fin n) (h : k ≠ i) : res i (proj k) = proj k := by
  funext x; simp [res, proj, Function.update_of_ne h]

theorem bop_zero_left {n : ℕ} (b : Bool) (v : (Fin n → Bool) → Bool) :
    bop b zero v = zero ∨ bop b zero v = v := by
  cases b
  · right; funext x; simp [bop, zero]
  · left; funext x; simp [bop, zero]

theorem bop_zero_right {n : ℕ} (b : Bool) (v : (Fin n → Bool) → Bool) :
    bop b v zero = zero ∨ bop b v zero = v := by
  cases b
  · right; funext x; simp [bop, zero]
  · left; funext x; simp [bop, zero]

theorem src_res {n : ℕ} (i : Fin n) {L L' : List ((Fin n → Bool) → Bool)}
    (hinv : ∀ h ∈ L, res i h = zero ∨ Src L' (res i h)) {u : (Fin n → Bool) → Bool}
    (hu : Src L u) : res i u = zero ∨ Src L' (res i u) := by
  rcases hu with ⟨k, rfl⟩ | hm
  · by_cases hk : k = i
    · subst hk; exact Or.inl (res_proj_self k)
    · rw [res_proj_ne i k hk]; exact Or.inr (Or.inl ⟨k, rfl⟩)
  · exact hinv u hm

theorem src_fix {n : ℕ} (i : Fin n) {L : List ((Fin n → Bool) → Bool)}
    (hfix : ∀ h ∈ L, res i h = h) {u : (Fin n → Bool) → Bool}
    (hu : Src L u) : res i u = zero ∨ res i u = u := by
  rcases hu with ⟨k, rfl⟩ | hm
  · by_cases hk : k = i
    · subst hk; exact Or.inl (res_proj_self k)
    · exact Or.inr (res_proj_ne i k hk)
  · exact Or.inr (hfix u hm)

-- Setting input i to false: entries that become constant false or repeat are dropped.
theorem norm {n : ℕ} (i : Fin n) : ∀ L : List ((Fin n → Bool) → Bool), SLP L →
    ∃ L' : List ((Fin n → Bool) → Bool), SLP L' ∧ L'.length ≤ L.length ∧
      (∀ h ∈ L, res i h = zero ∨ Src L' (res i h)) ∧
      (L'.length < L.length ∨ ∀ h ∈ L, res i h = h) := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], trivial, le_refl _, by simp, Or.inr (by simp)⟩
  | cons h L ih =>
    intro hS
    obtain ⟨hSL, u, v, b, hu, hv, rfl⟩ := hS
    obtain ⟨L', hS', hle, hinv, hstr⟩ := ih hSL
    have hres : res i (bop b u v) = bop b (res i u) (res i v) := rfl
    by_cases hz : res i (bop b u v) = zero ∨ Src L' (res i (bop b u v))
    · refine ⟨L', hS', ?_, ?_, Or.inl ?_⟩
      · simp only [List.length_cons]; omega
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hz
        · exact hinv g hg
      · simp only [List.length_cons]; omega
    · have nzu : res i u ≠ zero := by
        intro h0
        apply hz
        rw [hres, h0]
        rcases bop_zero_left b (res i v) with e | e
        · exact Or.inl e
        · rw [e]; exact src_res i hinv hv
      have nzv : res i v ≠ zero := by
        intro h0
        apply hz
        rw [hres, h0]
        rcases bop_zero_right b (res i u) with e | e
        · exact Or.inl e
        · rw [e]; exact src_res i hinv hu
      have hu' : Src L' (res i u) := (src_res i hinv hu).resolve_left nzu
      have hv' : Src L' (res i v) := (src_res i hinv hv).resolve_left nzv
      refine ⟨res i (bop b u v) :: L', ⟨hS', res i u, res i v, b, hu', hv', hres⟩, ?_, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact Or.inr (Or.inr List.mem_cons_self)
        · rcases hinv g hg with h0 | hs
          · exact Or.inl h0
          · exact Or.inr (Src_cons _ hs)
      · rcases hstr with hlt | hfix
        · left; simp only [List.length_cons]; omega
        · right
          intro g hg
          rcases List.mem_cons.mp hg with rfl | hg
          · have eu : res i u = u := (src_fix i hfix hu).resolve_left nzu
            have ev : res i v = v := (src_fix i hfix hv).resolve_left nzv
            rw [hres, eu, ev]
          · exact hfix g hg

-- A program gives a gate list with one gate per entry.
theorem build {n : ℕ} : ∀ L : List ((Fin n → Bool) → Bool), SLP L →
    ∃ gs : List Gate, gs.length = L.length ∧
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      (∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ w ∈ g.inputs, w < n + j) ∧
      ∀ h ∈ L, ∃ w, w < n + gs.length ∧
        ∀ x : Fin n → Bool, (W gs (List.ofFn x)).getD w false = h x := by
  intro L
  induction L with
  | nil => intro _; exact ⟨[], rfl, by simp, by simp, by simp⟩
  | cons h L ih =>
    intro hS
    obtain ⟨hSL, u, v, b, hu, hv, rfl⟩ := hS
    obtain ⟨gs, hlen, hops, hback, hval⟩ := ih hSL
    have hsrc : ∀ t, Src L t → ∃ w, w < n + gs.length ∧
        ∀ x : Fin n → Bool, (W gs (List.ofFn x)).getD w false = t x := by
      intro t ht
      rcases ht with ⟨k, rfl⟩ | hm
      · refine ⟨k.val, by omega, fun x => ?_⟩
        rw [W_prefix gs (List.ofFn x) k.val (by rw [List.length_ofFn]; exact k.isLt),
          ofFn_getD x k.val k.isLt]
        rfl
      · exact hval t hm
    obtain ⟨wu, hwu, hvu⟩ := hsrc u hu
    obtain ⟨wv, hwv, hvv⟩ := hsrc v hv
    refine ⟨gs ++ [⟨if b then GateOp.and else GateOp.or, [wu, wv]⟩], by simp [hlen], ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hops g hg
      · rw [List.mem_singleton] at hg
        subst hg
        refine ⟨?_, rfl⟩
        cases b <;> simp
    · intro j g hj w hw
      by_cases hjl : j < gs.length
      · rw [List.getElem?_append_left hjl] at hj
        exact hback j g hj w hw
      · obtain ⟨hjlt, hje⟩ := List.getElem?_eq_some_iff.mp hj
        simp only [List.length_append, List.length_cons, List.length_nil] at hjlt
        have hjeq : j = gs.length := by omega
        subst hjeq
        simp only [List.getElem_concat_length] at hje
        subst hje
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> omega
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | hm
      · refine ⟨n + gs.length, by simp, fun x => ?_⟩
        rw [W_snoc_getD, if_pos (by rw [List.length_ofFn])]
        simp only [List.map_cons, List.map_nil, hvu x, hvv x]
        cases b
        · simp [bop, eval_or2]
        · simp [bop, eval_and2]
      · obtain ⟨w, hw, hv⟩ := hval t hm
        refine ⟨w, by simp only [List.length_append, List.length_cons, List.length_nil]; omega,
          fun x => ?_⟩
        rw [W_snoc_getD, if_neg (by rw [List.length_ofFn]; omega)]
        exact hv x

def wf (n : ℕ) (C : Circuit) (w : ℕ) : (Fin n → Bool) → Bool :=
  fun x => (W C.gates (List.ofFn x)).getD w false

-- The gate functions of a circuit of the model form a program.
theorem toSLP {n : ℕ} (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∀ k, k ≤ C.gates.length → ∃ L : List ((Fin n → Bool) → Bool), SLP L ∧ L.length = k ∧
      ∀ j < k, wf n C (n + j) ∈ L := by
  obtain ⟨hao, hrb, h2⟩ := hC
  intro k
  induction k with
  | zero => intro _; exact ⟨[], trivial, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro hk
    obtain ⟨L, hS, hlen, hmem⟩ := ih (by omega)
    have hk' : k < C.gates.length := by omega
    have hgm : C.gates[k] ∈ C.gates := List.getElem_mem hk'
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ hgm)
    have hrk := hrb k hk'
    rw [gateAt_eq hk', hab] at hrk
    have ha : a < n + k := hrk a (by simp)
    have hb : b < n + k := hrk b (by simp)
    have hsrc : ∀ w, w < n + k → Src L (wf n C w) := by
      intro w hw
      by_cases hwn : w < n
      · left
        refine ⟨⟨w, hwn⟩, ?_⟩
        funext x
        show (W C.gates (List.ofFn x)).getD w false = x ⟨w, hwn⟩
        rw [W_prefix C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hwn),
          ofFn_getD x w hwn]
      · right
        have := hmem (w - n) (by omega)
        rwa [show n + (w - n) = w by omega] at this
    have hval : ∃ bb : Bool, wf n C (n + k) = bop bb (wf n C a) (wf n C b) := by
      rcases hao _ hgm with e | e
      · refine ⟨true, ?_⟩
        funext x
        have h := W_gate C.gates (List.ofFn x) k hk'
        rw [List.length_ofFn] at h
        show (W C.gates (List.ofFn x)).getD (n + k) false = _
        rw [h, hab, e]
        simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb]
        rw [eval_and2]
        simp [bop, wf]
      · refine ⟨false, ?_⟩
        funext x
        have h := W_gate C.gates (List.ofFn x) k hk'
        rw [List.length_ofFn] at h
        show (W C.gates (List.ofFn x)).getD (n + k) false = _
        rw [h, hab, e]
        simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb]
        rw [eval_or2]
        simp [bop, wf]
    obtain ⟨bb, hbb⟩ := hval
    refine ⟨wf n C (n + k) :: L, ⟨hS, _, _, bb, hsrc a ha, hsrc b hb, hbb⟩, by simp [hlen], ?_⟩
    intro j hj
    by_cases hjk : j = k
    · subst hjk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hmem j (by omega))

theorem main {n : ℕ} (C : Circuit) (i : Fin n) (hC : PEqualNP.TopForm.IsAO2 n C)
    (h1 : ∃ x : Fin n → Bool, circuitFun n C x ≠ circuitFun n C (Function.update x i false))
    (h2 : ∃ y z : Fin n → Bool, circuitFun n C (Function.update y i false) ≠
      circuitFun n C (Function.update z i false)) :
    ∃ C' : Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ C'.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n C' x = circuitFun n C (Function.update x i false) := by
  obtain ⟨L, hS, hlen, hmem⟩ := toSLP C hC C.gates.length (le_refl _)
  have hsrc : wf n C C.output = zero ∨ Src L (wf n C C.output) := by
    by_cases ho : C.output < n
    · right; left
      refine ⟨⟨C.output, ho⟩, ?_⟩
      funext x
      show (W C.gates (List.ofFn x)).getD C.output false = x ⟨C.output, ho⟩
      rw [W_prefix _ _ _ (by rw [List.length_ofFn]; exact ho), ofFn_getD x _ ho]
    · by_cases ho2 : C.output < n + C.gates.length
      · right; right
        have := hmem (C.output - n) (by omega)
        rwa [show n + (C.output - n) = C.output by omega] at this
      · left
        funext x
        exact W_ge _ _ _ (by rw [List.length_ofFn]; omega)
  obtain ⟨f, hfe⟩ : ∃ f, f = wf n C C.output := ⟨_, rfl⟩
  have hf : circuitFun n C = f := by rw [hfe]; rfl
  rw [← hfe] at hsrc
  obtain ⟨L', hS', hle, hinv, hstr⟩ := norm i L hS
  have hnz : res i f ≠ zero := by
    intro h0
    obtain ⟨y, z, hyz⟩ := h2
    apply hyz
    rw [hf]
    show res i f y = res i f z
    rw [h0]
    rfl
  have hsrc' : Src L' (res i f) := by
    rcases hsrc with h0 | hs
    · exfalso; apply hnz; rw [h0]; rfl
    · exact (src_res i hinv hs).resolve_left hnz
  have hlt : L'.length < L.length := by
    rcases hstr with h | hfix
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := h1
      apply hx
      rw [hf]
      show f x = res i f x
      have hfx : res i f = f := by
        rcases hsrc with h0 | hs
        · rw [h0]; rfl
        · exact (src_fix i hfix hs).resolve_left hnz
      rw [hfx]
  obtain ⟨gs, hglen, hops, hback, hval⟩ := build L' hS'
  obtain ⟨w, hw⟩ : ∃ w, ∀ x : Fin n → Bool, (W gs (List.ofFn x)).getD w false = res i f x := by
    rcases hsrc' with ⟨k, hk⟩ | hm
    · refine ⟨k.val, fun x => ?_⟩
      rw [W_prefix gs (List.ofFn x) k.val (by rw [List.length_ofFn]; exact k.isLt),
        ofFn_getD x k.val k.isLt, hk]
      rfl
    · obtain ⟨w, _, hw⟩ := hval _ hm
      exact ⟨w, hw⟩
  refine ⟨⟨gs, w⟩, ⟨fun g hg => (hops g hg).1, ?_, fun g hg => (hops g hg).2⟩, ?_, ?_⟩
  · intro j hj v hv
    have hj' : j < gs.length := hj
    have e : gateAt (⟨gs, w⟩ : Circuit) j = gs[j] := gateAt_eq hj
    rw [e] at hv
    exact hback j gs[j] (List.getElem?_eq_getElem hj') v hv
  · show gs.length < C.gates.length
    omega
  · intro x
    show (W gs (List.ofFn x)).getD w false = _
    rw [hw x, hf]
    rfl

end PEqualNP.Outside.L_meta_5720

theorem PEqualNP.Outside.L_meta_5720 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∃ (x5 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x5 x3 Bool.false)) → (∃ (x6 : Fin x1 → Bool) (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x6 x3 Bool.false) ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x7 x3 Bool.false)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size < x2.size ∧ ∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = PEqualNP.MetaComplexity.circuitFun x1 x2 (Function.update x8 x3 Bool.false) := by
  intro n C i hC h1 h2
  exact PEqualNP.Outside.L_meta_5720.main C i hC h1 h2
