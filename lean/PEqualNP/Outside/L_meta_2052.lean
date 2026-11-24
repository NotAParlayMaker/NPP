import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2052

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

theorem isAnd_iff (o : GateOp) : isAnd o = true ↔ o = GateOp.and := by
  cases o <;> simp [isAnd]

def off : Bool → ℕ
  | true => 0
  | false => 1

theorem off_le (s : Bool) : off s ≤ 1 := by
  cases s <;> simp [off]

def gt (gs : List Gate) (j : ℕ) : Gate := gs.getD j ⟨GateOp.or, []⟩

theorem gt_eq (gs : List Gate) (j : ℕ) (hj : j < gs.length) : gt gs j = gs[j] := by
  simp [gt, List.getD_eq_getElem?_getD, hj]

def sw (N : ℕ) (gs : List Gate) (s : Bool) (w : ℕ) : List ℕ :=
  if w < N + N then (if decide (w < N) = s then [w] else [])
  else if w - (N + N) < gs.length then
    (if isAnd (gt gs (w - (N + N))).op = true then []
      else [N + N + (5 * (w - (N + N)) + off s)])
  else []

def qw (N : ℕ) (gs : List Gate) (w : ℕ) : List ℕ :=
  if w < N + N then []
  else if w - (N + N) < gs.length then
    (if isAnd (gt gs (w - (N + N))).op = true then [N + N + (5 * (w - (N + N)) + 4)]
      else [N + N + (5 * (w - (N + N)) + 2)])
  else []

theorem sw_in (N : ℕ) (gs : List Gate) (s : Bool) (w : ℕ) (hw : w < N + N) :
    sw N gs s w = if decide (w < N) = s then [w] else [] := by
  unfold sw
  rw [if_pos hw]

theorem sw_big (N : ℕ) (gs : List Gate) (s : Bool) (w : ℕ) (hw : N + N + gs.length ≤ w) :
    sw N gs s w = [] := by
  have h1 : ¬ (w < N + N) := by omega
  have h2 : ¬ (w - (N + N) < gs.length) := by omega
  unfold sw
  rw [if_neg h1, if_neg h2]

theorem sw_and (N : ℕ) (gs : List Gate) (s : Bool) (j : ℕ) (hj : j < gs.length)
    (h : isAnd (gt gs j).op = true) : sw N gs s (N + N + j) = [] := by
  have h1 : ¬ (N + N + j < N + N) := by omega
  have h2 : N + N + j - (N + N) = j := by omega
  unfold sw
  rw [if_neg h1, h2, if_pos hj, if_pos h]

theorem sw_or (N : ℕ) (gs : List Gate) (s : Bool) (j : ℕ) (hj : j < gs.length)
    (h : isAnd (gt gs j).op = false) : sw N gs s (N + N + j) = [N + N + (5 * j + off s)] := by
  have h1 : ¬ (N + N + j < N + N) := by omega
  have h2 : N + N + j - (N + N) = j := by omega
  have h3 : ¬ (isAnd (gt gs j).op = true) := by rw [h]; exact Bool.false_ne_true
  unfold sw
  rw [if_neg h1, h2, if_pos hj, if_neg h3]

theorem qw_in (N : ℕ) (gs : List Gate) (w : ℕ) (hw : w < N + N) : qw N gs w = [] := by
  unfold qw
  rw [if_pos hw]

theorem qw_big (N : ℕ) (gs : List Gate) (w : ℕ) (hw : N + N + gs.length ≤ w) :
    qw N gs w = [] := by
  have h1 : ¬ (w < N + N) := by omega
  have h2 : ¬ (w - (N + N) < gs.length) := by omega
  unfold qw
  rw [if_neg h1, if_neg h2]

theorem qw_and (N : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (h : isAnd (gt gs j).op = true) : qw N gs (N + N + j) = [N + N + (5 * j + 4)] := by
  have h1 : ¬ (N + N + j < N + N) := by omega
  have h2 : N + N + j - (N + N) = j := by omega
  unfold qw
  rw [if_neg h1, h2, if_pos hj, if_pos h]

theorem qw_or (N : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (h : isAnd (gt gs j).op = false) : qw N gs (N + N + j) = [N + N + (5 * j + 2)] := by
  have h1 : ¬ (N + N + j < N + N) := by omega
  have h2 : N + N + j - (N + N) = j := by omega
  have h3 : ¬ (isAnd (gt gs j).op = true) := by rw [h]; exact Bool.false_ne_true
  unfold qw
  rw [if_neg h1, h2, if_pos hj, if_neg h3]

theorem sw_cases (N : ℕ) (gs : List Gate) (s : Bool) (w : ℕ) :
    sw N gs s w = [] ∨ ∃ q, sw N gs s w = [q] := by
  unfold sw
  split_ifs <;> simp

theorem qw_cases (N : ℕ) (gs : List Gate) (w : ℕ) :
    qw N gs w = [] ∨ ∃ q, qw N gs w = [q] := by
  unfold qw
  split_ifs <;> simp

theorem sw_len (N : ℕ) (gs : List Gate) (s : Bool) (w : ℕ) : (sw N gs s w).length ≤ 1 := by
  rcases sw_cases N gs s w with h | ⟨q, h⟩ <;> rw [h] <;> simp

theorem qw_len (N : ℕ) (gs : List Gate) (w : ℕ) : (qw N gs w).length ≤ 1 := by
  rcases qw_cases N gs w with h | ⟨q, h⟩ <;> rw [h] <;> simp

theorem sw_lt (N : ℕ) (gs : List Gate) (s : Bool) (w j q : ℕ) (hw : w < N + N + j)
    (hq : q ∈ sw N gs s w) : q < N + N + 5 * j := by
  have := off_le s
  unfold sw at hq
  split_ifs at hq <;> simp at hq <;> omega

theorem qw_lt (N : ℕ) (gs : List Gate) (w j q : ℕ) (hw : w < N + N + j)
    (hq : q ∈ qw N gs w) : q < N + N + 5 * j := by
  unfold qw at hq
  split_ifs at hq <;> simp at hq <;> omega

theorem flat_len (f : ℕ → List ℕ) (hf : ∀ w, (f w).length ≤ 1) :
    ∀ l : List ℕ, (l.flatMap f).length ≤ l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    have := hf a
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

def ua (gs : List Gate) (j : ℕ) : ℕ := (gt gs j).inputs.getD 0 0

def va (gs : List Gate) (j : ℕ) : ℕ := (gt gs j).inputs.getD 1 (ua gs j)

def prod (a b : List ℕ) : Gate :=
  match a, b with
  | [x], [y] => ⟨GateOp.and, [x, y]⟩
  | _, _ => ⟨GateOp.or, []⟩

theorem prod_legal (a b : List ℕ) :
    ((prod a b).op = GateOp.and ∨ (prod a b).op = GateOp.or) ∧ (prod a b).inputs.length ≤ 2 := by
  rcases a with _ | ⟨x, _ | ⟨x2, t⟩⟩ <;> rcases b with _ | ⟨y, _ | ⟨y2, t'⟩⟩ <;> simp [prod]

theorem prod_and (a b : List ℕ) (h : (prod a b).op = GateOp.and) :
    ∃ x y, a = [x] ∧ b = [y] ∧ (prod a b).inputs = [x, y] := by
  rcases a with _ | ⟨x, _ | ⟨x2, t⟩⟩ <;> rcases b with _ | ⟨y, _ | ⟨y2, t'⟩⟩ <;>
    first
      | exact ⟨_, _, rfl, rfl, rfl⟩
      | (simp [prod] at h)

theorem prod_mem (x y : List ℕ) (a : ℕ) (h : a ∈ (prod x y).inputs) : a ∈ x ∨ a ∈ y := by
  rcases x with _ | ⟨x1, _ | ⟨x2, t⟩⟩ <;> rcases y with _ | ⟨y1, _ | ⟨y2, t'⟩⟩ <;>
    simp [prod] at h ⊢ <;> exact h

def dg (N : ℕ) (gs : List Gate) (j r : ℕ) : Gate :=
  if isAnd (gt gs j).op = true then
    (if r = 0 then prod (sw N gs true (ua gs j)) (sw N gs false (va gs j))
     else if r = 1 then prod (sw N gs false (ua gs j)) (sw N gs true (va gs j))
     else if r = 2 then ⟨GateOp.or, [N + N + (5 * j + 0), N + N + (5 * j + 1)]⟩
     else if r = 3 then ⟨GateOp.or, qw N gs (ua gs j) ++ qw N gs (va gs j)⟩
     else ⟨GateOp.or, [N + N + (5 * j + 2), N + N + (5 * j + 3)]⟩)
  else
    (if r = 0 then ⟨GateOp.or, (gt gs j).inputs.flatMap (sw N gs true)⟩
     else if r = 1 then ⟨GateOp.or, (gt gs j).inputs.flatMap (sw N gs false)⟩
     else if r = 2 then ⟨GateOp.or, (gt gs j).inputs.flatMap (qw N gs)⟩
     else ⟨GateOp.or, []⟩)

theorem dg_a0 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = true) :
    dg N gs j 0 = prod (sw N gs true (ua gs j)) (sw N gs false (va gs j)) := by
  unfold dg
  rw [if_pos h]
  rfl

theorem dg_a1 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = true) :
    dg N gs j 1 = prod (sw N gs false (ua gs j)) (sw N gs true (va gs j)) := by
  unfold dg
  rw [if_pos h]
  rfl

theorem dg_a2 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = true) :
    dg N gs j 2 = ⟨GateOp.or, [N + N + (5 * j + 0), N + N + (5 * j + 1)]⟩ := by
  unfold dg
  rw [if_pos h]
  rfl

theorem dg_a3 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = true) :
    dg N gs j 3 = ⟨GateOp.or, qw N gs (ua gs j) ++ qw N gs (va gs j)⟩ := by
  unfold dg
  rw [if_pos h]
  rfl

theorem dg_a4 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = true) :
    dg N gs j 4 = ⟨GateOp.or, [N + N + (5 * j + 2), N + N + (5 * j + 3)]⟩ := by
  unfold dg
  rw [if_pos h]
  rfl

theorem nt (b : Bool) (h : b = false) : ¬ (b = true) := by
  rw [h]
  exact Bool.false_ne_true

theorem dg_o0 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = false) :
    dg N gs j 0 = ⟨GateOp.or, (gt gs j).inputs.flatMap (sw N gs true)⟩ := by
  unfold dg
  rw [if_neg (nt _ h)]
  rfl

theorem dg_o1 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = false) :
    dg N gs j 1 = ⟨GateOp.or, (gt gs j).inputs.flatMap (sw N gs false)⟩ := by
  unfold dg
  rw [if_neg (nt _ h)]
  rfl

theorem dg_o2 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = false) :
    dg N gs j 2 = ⟨GateOp.or, (gt gs j).inputs.flatMap (qw N gs)⟩ := by
  unfold dg
  rw [if_neg (nt _ h)]
  rfl

theorem dg_o3 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = false) :
    dg N gs j 3 = ⟨GateOp.or, []⟩ := by
  unfold dg
  rw [if_neg (nt _ h)]
  rfl

theorem dg_o4 (N : ℕ) (gs : List Gate) (j : ℕ) (h : isAnd (gt gs j).op = false) :
    dg N gs j 4 = ⟨GateOp.or, []⟩ := by
  unfold dg
  rw [if_neg (nt _ h)]
  rfl

theorem dg_as (N : ℕ) (gs : List Gate) (j : ℕ) (s : Bool) (h : isAnd (gt gs j).op = true) :
    dg N gs j (off s) = prod (sw N gs s (ua gs j)) (sw N gs (!s) (va gs j)) := by
  cases s
  · exact dg_a1 N gs j h
  · exact dg_a0 N gs j h

theorem dg_os (N : ℕ) (gs : List Gate) (j : ℕ) (s : Bool) (h : isAnd (gt gs j).op = false) :
    dg N gs j (off s) = ⟨GateOp.or, (gt gs j).inputs.flatMap (sw N gs s)⟩ := by
  cases s
  · exact dg_o1 N gs j h
  · exact dg_o0 N gs j h

def dgs (N : ℕ) (gs : List Gate) : List Gate :=
  (List.range (5 * gs.length)).map (fun i => dg N gs (i / 5) (i % 5))

theorem dgs_len (N : ℕ) (gs : List Gate) : (dgs N gs).length = 5 * gs.length := by
  simp [dgs]

theorem dgs_get (N : ℕ) (gs : List Gate) (j r : ℕ) (hr : r < 5)
    (h : 5 * j + r < (dgs N gs).length) : (dgs N gs)[5 * j + r] = dg N gs j r := by
  have h1 : (5 * j + r) / 5 = j := by omega
  have h2 : (5 * j + r) % 5 = r := by omega
  simp only [dgs, List.getElem_map, List.getElem_range, h1, h2]

theorem gtD (N : ℕ) (gs : List Gate) (j r : ℕ) (hj : j < gs.length) (hr : r < 5) :
    gt (dgs N gs) (5 * j + r) = dg N gs j r := by
  have h : 5 * j + r < (dgs N gs).length := by rw [dgs_len]; omega
  rw [gt_eq _ _ h, dgs_get N gs j r hr h]

theorem dval_or (N : ℕ) (gs : List Gate) (z : Fin (N + N) → Bool) (j r : ℕ)
    (hj : j < gs.length) (hr : r < 5) (ins : List ℕ)
    (hg : dg N gs j r = ⟨GateOp.or, ins⟩) (hlt : ∀ i ∈ ins, i < N + N + (5 * j + r)) :
    val (dgs N gs) (N + N + (5 * j + r)) z = true ↔ ∃ i ∈ ins, val (dgs N gs) i z = true := by
  have h : 5 * j + r < (dgs N gs).length := by rw [dgs_len]; omega
  have e : (dgs N gs)[5 * j + r] = ⟨GateOp.or, ins⟩ := by rw [dgs_get N gs j r hr h, hg]
  rw [val_or (dgs N gs) z (5 * j + r) h (congrArg Gate.op e), e]
  constructor
  · rintro ⟨i, hi, _, hv⟩
    exact ⟨i, hi, hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, hlt i hi, hv⟩

theorem dval_and (N : ℕ) (gs : List Gate) (z : Fin (N + N) → Bool) (j r : ℕ)
    (hj : j < gs.length) (hr : r < 5) (x y : ℕ)
    (hg : dg N gs j r = ⟨GateOp.and, [x, y]⟩) (hx : x < N + N + (5 * j + r))
    (hy : y < N + N + (5 * j + r)) :
    val (dgs N gs) (N + N + (5 * j + r)) z = true ↔
      val (dgs N gs) x z = true ∧ val (dgs N gs) y z = true := by
  have h : 5 * j + r < (dgs N gs).length := by rw [dgs_len]; omega
  have e : (dgs N gs)[5 * j + r] = ⟨GateOp.and, [x, y]⟩ := by rw [dgs_get N gs j r hr h, hg]
  rw [val_and (dgs N gs) z (5 * j + r) h (congrArg Gate.op e), e]
  constructor
  · intro hh
    exact ⟨(hh x (by simp)).2, (hh y (by simp)).2⟩
  · rintro ⟨h1, h2⟩ i hi
    have hi' : i = x ∨ i = y := by simpa using hi
    rcases hi' with e1 | e1
    · rw [e1]
      exact ⟨hx, h1⟩
    · rw [e1]
      exact ⟨hy, h2⟩

theorem ex2 (p : ℕ → Prop) (a b : ℕ) : (∃ i ∈ [a, b], p i) ↔ p a ∨ p b := by
  simp

theorem dv_a2 (N : ℕ) (gs : List Gate) (z : Fin (N + N) → Bool) (j : ℕ) (hj : j < gs.length)
    (hA : isAnd (gt gs j).op = true) :
    val (dgs N gs) (N + N + (5 * j + 2)) z = true ↔
      val (dgs N gs) (N + N + (5 * j + 0)) z = true ∨
      val (dgs N gs) (N + N + (5 * j + 1)) z = true :=
  (dval_or N gs z j 2 hj (by norm_num) _ (dg_a2 N gs j hA) (by
    intro i hi
    simp at hi
    omega)).trans (ex2 _ _ _)

theorem dv_a4 (N : ℕ) (gs : List Gate) (z : Fin (N + N) → Bool) (j : ℕ) (hj : j < gs.length)
    (hA : isAnd (gt gs j).op = true) :
    val (dgs N gs) (N + N + (5 * j + 4)) z = true ↔
      val (dgs N gs) (N + N + (5 * j + 2)) z = true ∨
      val (dgs N gs) (N + N + (5 * j + 3)) z = true :=
  (dval_or N gs z j 4 hj (by norm_num) _ (dg_a4 N gs j hA) (by
    intro i hi
    simp at hi
    omega)).trans (ex2 _ _ _)

theorem dv_a3 (N : ℕ) (gs : List Gate) (z : Fin (N + N) → Bool) (j : ℕ) (hj : j < gs.length)
    (hA : isAnd (gt gs j).op = true) (hu : ua gs j < N + N + j) (hv : va gs j < N + N + j) :
    val (dgs N gs) (N + N + (5 * j + 3)) z = true ↔
      ∃ q ∈ qw N gs (ua gs j) ++ qw N gs (va gs j), val (dgs N gs) q z = true :=
  dval_or N gs z j 3 hj (by norm_num) _ (dg_a3 N gs j hA) (by
    intro i hi
    rcases List.mem_append.1 hi with h | h
    · have := qw_lt N gs (ua gs j) j i hu h
      omega
    · have := qw_lt N gs (va gs j) j i hv h
      omega)

theorem prod_val (N : ℕ) (gs : List Gate) (z : Fin (N + N) → Bool) (j : ℕ)
    (hj : j < gs.length) (s : Bool) (hA : isAnd (gt gs j).op = true)
    (hu : ua gs j < N + N + j) (hv : va gs j < N + N + j) :
    val (dgs N gs) (N + N + (5 * j + off s)) z = true ↔
      (∃ q ∈ sw N gs s (ua gs j), val (dgs N gs) q z = true) ∧
      (∃ q ∈ sw N gs (!s) (va gs j), val (dgs N gs) q z = true) := by
  have e := dg_as N gs j s hA
  have ho : off s < 5 := by have := off_le s; omega
  rcases sw_cases N gs s (ua gs j) with h1 | ⟨x, h1⟩ <;>
    rcases sw_cases N gs (!s) (va gs j) with h2 | ⟨y, h2⟩
  · rw [h1, h2] at e ⊢
    rw [dval_or N gs z j (off s) hj ho [] e (by intro i hi; simp at hi)]
    simp
  · rw [h1, h2] at e ⊢
    rw [dval_or N gs z j (off s) hj ho [] e (by intro i hi; simp at hi)]
    simp
  · rw [h1, h2] at e ⊢
    rw [dval_or N gs z j (off s) hj ho [] e (by intro i hi; simp at hi)]
    simp
  · have hx : x < N + N + (5 * j + off s) := by
      have := sw_lt N gs s (ua gs j) j x hu (by rw [h1]; simp)
      omega
    have hy : y < N + N + (5 * j + off s) := by
      have := sw_lt N gs (!s) (va gs j) j y hv (by rw [h2]; simp)
      omega
    rw [h1, h2] at e ⊢
    rw [dval_and N gs z j (off s) hj ho x y e hx hy]
    simp

def Hyp (N : ℕ) (I : Fin N → Fin N → Prop) (gs : List Gate) : Prop :=
  0 < N ∧
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ j, j < gs.length → ∀ i ∈ (gt gs j).inputs, i < N + N + j) ∧
  (∀ j, j < gs.length → (gt gs j).op = GateOp.and → ∀ k : Fin (N + N),
    val gs (N + N + j) (fun k' : Fin (N + N) => decide (k' = k)) = false) ∧
  (∀ j, j < gs.length → (gt gs j).op = GateOp.and → ∀ z : Fin (N + N) → Bool,
    val gs (N + N + j) z = true →
      val gs (N + N + j) (fun k : Fin (N + N) => decide (k.val < N) && z k) = true ∨
      val gs (N + N + j) (fun k : Fin (N + N) => decide (N ≤ k.val) && z k) = true ∨
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

theorem hL {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := H.2.1

theorem hR {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) :
    ∀ j, j < gs.length → ∀ i ∈ (gt gs j).inputs, i < N + N + j := H.2.2.1

theorem hC2 {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) :
    ∀ j, j < gs.length → (gt gs j).op = GateOp.and → ∀ k : Fin (N + N),
      val gs (N + N + j) (fun k' : Fin (N + N) => decide (k' = k)) = false := H.2.2.2.1

theorem hC1 {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) :
    ∀ j, j < gs.length → (gt gs j).op = GateOp.and → ∀ z : Fin (N + N) → Bool,
    val gs (N + N + j) z = true →
      val gs (N + N + j) (fun k : Fin (N + N) => decide (k.val < N) && z k) = true ∨
      val gs (N + N + j) (fun k : Fin (N + N) => decide (N ≤ k.val) && z k) = true ∨
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true :=
  H.2.2.2.2

theorem leg {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) (j : ℕ)
    (hj : j < gs.length) :
    ((gt gs j).op = GateOp.and ∨ (gt gs j).op = GateOp.or) ∧ (gt gs j).inputs.length ≤ 2 := by
  rw [gt_eq gs j hj]
  exact hL H _ (List.getElem_mem hj)

theorem cv_and {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) (j : ℕ)
    (hj : j < gs.length) (ha : (gt gs j).op = GateOp.and) (z : Fin (N + N) → Bool) :
    val gs (N + N + j) z = true ↔ ∀ i ∈ (gt gs j).inputs, val gs i z = true := by
  have e : gt gs j = gs[j] := gt_eq gs j hj
  have hr := hR H j hj
  rw [e] at ha hr ⊢
  rw [val_and gs z j hj ha]
  constructor
  · intro h i hi
    exact (h i hi).2
  · intro h i hi
    exact ⟨hr i hi, h i hi⟩

theorem cv_or {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) (j : ℕ)
    (hj : j < gs.length) (ho : (gt gs j).op = GateOp.or) (z : Fin (N + N) → Bool) :
    val gs (N + N + j) z = true ↔ ∃ i ∈ (gt gs j).inputs, val gs i z = true := by
  have e : gt gs j = gs[j] := gt_eq gs j hj
  have hr := hR H j hj
  rw [e] at ho hr ⊢
  rw [val_or gs z j hj ho]
  constructor
  · rintro ⟨i, hi, _, h⟩
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, hr i hi, h⟩

theorem uv_mem {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) (j : ℕ)
    (hj : j < gs.length) (ha : (gt gs j).op = GateOp.and) :
    ua gs j ∈ (gt gs j).inputs ∧ va gs j ∈ (gt gs j).inputs ∧
      ∀ i ∈ (gt gs j).inputs, i = ua gs j ∨ i = va gs j := by
  have hlen := (leg H j hj).2
  obtain ⟨k0⟩ : Nonempty (Fin (N + N)) := ⟨⟨0, by have := H.1; omega⟩⟩
  have hcv := cv_and H j hj ha (fun k' : Fin (N + N) => decide (k' = k0))
  have hc2 := hC2 H j hj ha k0
  unfold va ua
  rcases hin : (gt gs j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exfalso
    rw [hin] at hcv
    have h3 := hcv.2 (by intro i hi; simp at hi)
    rw [hc2] at h3
    exact Bool.noConfusion h3
  · simp
  · simp
  · rw [hin] at hlen
    simp only [List.length_cons] at hlen
    omega

theorem dv_os {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs)
    (z : Fin (N + N) → Bool) (j : ℕ) (hj : j < gs.length) (s : Bool)
    (hna : isAnd (gt gs j).op = false) :
    val (dgs N gs) (N + N + (5 * j + off s)) z = true ↔
      ∃ i ∈ (gt gs j).inputs.flatMap (sw N gs s), val (dgs N gs) i z = true := by
  have ho : off s < 5 := by have := off_le s; omega
  apply dval_or N gs z j (off s) hj ho _ (dg_os N gs j s hna)
  intro i hi
  obtain ⟨u, hu, hiu⟩ := List.mem_flatMap.1 hi
  have := sw_lt N gs s u j i (hR H j hj u hu) hiu
  omega

theorem dv_o2 {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs)
    (z : Fin (N + N) → Bool) (j : ℕ) (hj : j < gs.length)
    (hna : isAnd (gt gs j).op = false) :
    val (dgs N gs) (N + N + (5 * j + 2)) z = true ↔
      ∃ i ∈ (gt gs j).inputs.flatMap (qw N gs), val (dgs N gs) i z = true := by
  apply dval_or N gs z j 2 hj (by norm_num) _ (dg_o2 N gs j hna)
  intro i hi
  obtain ⟨u, hu, hiu⟩ := List.mem_flatMap.1 hi
  have := qw_lt N gs u j i (hR H j hj u hu) hiu
  omega

theorem invA {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) (s : Bool)
    (z : Fin (N + N) → Bool) :
    ∀ w, (∃ q ∈ sw N gs s w, val (dgs N gs) q z = true) ↔
      ∃ k : Fin (N + N), decide (k.val < N) = s ∧ z k = true ∧
        val gs w (fun k' : Fin (N + N) => decide (k' = k)) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < N + N
    · rw [sw_in N gs s w hwn]
      constructor
      · rintro ⟨q, hq, hv⟩
        by_cases hs : decide (w < N) = s
        · rw [if_pos hs, List.mem_singleton] at hq
          rw [hq, val_input (dgs N gs) z w hwn] at hv
          refine ⟨⟨w, hwn⟩, hs, hv, ?_⟩
          rw [val_input gs _ w hwn]
          simp
        · rw [if_neg hs] at hq
          simp at hq
      · rintro ⟨k, hk, hzk, hv⟩
        rw [val_input gs _ w hwn] at hv
        have e : (⟨w, hwn⟩ : Fin (N + N)) = k := of_decide_eq_true hv
        have hs : decide (w < N) = s := by
          rw [← e] at hk
          exact hk
        rw [if_pos hs]
        refine ⟨w, List.mem_singleton_self w, ?_⟩
        rw [val_input (dgs N gs) z w hwn, e]
        exact hzk
    · by_cases hbig : N + N + gs.length ≤ w
      · rw [sw_big N gs s w hbig]
        constructor
        · rintro ⟨q, hq, _⟩
          simp at hq
        · rintro ⟨k, _, _, hv⟩
          rw [val_big gs _ w hbig] at hv
          exact Bool.noConfusion hv
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj : j < gs.length := by omega
        rcases (leg H j hj).1 with ha | ho
        · rw [sw_and N gs s j hj (by rw [ha]; rfl)]
          constructor
          · rintro ⟨q, hq, _⟩
            simp at hq
          · rintro ⟨k, _, _, hv⟩
            rw [hC2 H j hj ha k] at hv
            exact Bool.noConfusion hv
        · have hna : isAnd (gt gs j).op = false := by rw [ho]; rfl
          rw [sw_or N gs s j hj hna]
          have hD := dv_os H z j hj s hna
          constructor
          · rintro ⟨q, hq, hv⟩
            rw [List.mem_singleton] at hq
            rw [hq] at hv
            obtain ⟨i, hi, hiv⟩ := hD.1 hv
            obtain ⟨u, hu, hiu⟩ := List.mem_flatMap.1 hi
            obtain ⟨k, hk, hzk, hkv⟩ := (ih u (hR H j hj u hu)).1 ⟨i, hiu, hiv⟩
            exact ⟨k, hk, hzk, (cv_or H j hj ho _).2 ⟨u, hu, hkv⟩⟩
          · rintro ⟨k, hk, hzk, hv⟩
            obtain ⟨u, hu, huv⟩ := (cv_or H j hj ho _).1 hv
            obtain ⟨i, hiu, hiv⟩ := (ih u (hR H j hj u hu)).2 ⟨k, hk, hzk, huv⟩
            exact ⟨_, List.mem_singleton_self _,
              hD.2 ⟨i, List.mem_flatMap.2 ⟨u, hu, hiu⟩, hiv⟩⟩

theorem and_pair {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) (j : ℕ)
    (hj : j < gs.length) (ha : (gt gs j).op = GateOp.and) (a b : ℕ)
    (hall : ∀ i ∈ (gt gs j).inputs, i = a ∨ i = b) (z : Fin (N + N) → Bool)
    (k1 k2 : Fin (N + N)) (h1 : k1.val < N) (h2 : N ≤ k2.val)
    (hz1 : z k1 = true) (hz2 : z k2 = true)
    (ha1 : val gs a (fun k' : Fin (N + N) => decide (k' = k1)) = true)
    (hb2 : val gs b (fun k' : Fin (N + N) => decide (k' = k2)) = true) :
    ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  have hpair : val gs (N + N + j) (fun k' : Fin (N + N) => decide (k' = k1 ∨ k' = k2)) = true := by
    rw [cv_and H j hj ha]
    intro i hi
    rcases hall i hi with e | e
    · rw [e]
      exact val_mono gs (hL H) _ _ (by
        intro v hv
        have e2 : v = k1 := of_decide_eq_true hv
        exact decide_eq_true (Or.inl e2)) a ha1
    · rw [e]
      exact val_mono gs (hL H) _ _ (by
        intro v hv
        have e2 : v = k2 := of_decide_eq_true hv
        exact decide_eq_true (Or.inr e2)) b hb2
  rcases hC1 H j hj ha _ hpair with h | h | ⟨p, l, hI, hp, hl⟩
  · exfalso
    have h3 := val_mono gs (hL H) _ (fun k' : Fin (N + N) => decide (k' = k1)) (by
      intro v hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      rcases hv.2 with e | e
      · exact decide_eq_true e
      · exfalso
        have h4 := hv.1
        rw [e] at h4
        omega) _ h
    rw [hC2 H j hj ha k1] at h3
    exact Bool.noConfusion h3
  · exfalso
    have h3 := val_mono gs (hL H) _ (fun k' : Fin (N + N) => decide (k' = k2)) (by
      intro v hv
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      rcases hv.2 with e | e
      · exfalso
        have h4 := hv.1
        rw [e] at h4
        omega
      · exact decide_eq_true e) _ h
    rw [hC2 H j hj ha k2] at h3
    exact Bool.noConfusion h3
  · have hp' : Fin.castAdd N p = k1 ∨ Fin.castAdd N p = k2 := of_decide_eq_true hp
    have hl' : Fin.natAdd N l = k1 ∨ Fin.natAdd N l = k2 := of_decide_eq_true hl
    have hpl := p.isLt
    have e1 : Fin.castAdd N p = k1 := by
      rcases hp' with e | e
      · exact e
      · exfalso
        have h5 := congrArg Fin.val e
        simp at h5
        omega
    have e2 : Fin.natAdd N l = k2 := by
      rcases hl' with e | e
      · exfalso
        have h5 := congrArg Fin.val e
        simp at h5
        omega
      · exact e
    exact ⟨p, l, hI, by rw [e1]; exact hz1, by rw [e2]; exact hz2⟩

theorem invC {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs)
    (z : Fin (N + N) → Bool) :
    ∀ w, (∃ q ∈ qw N gs w, val (dgs N gs) q z = true) →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rintro ⟨q, hq, hv⟩
    by_cases hwn : w < N + N
    · rw [qw_in N gs w hwn] at hq
      simp at hq
    · by_cases hbig : N + N + gs.length ≤ w
      · rw [qw_big N gs w hbig] at hq
        simp at hq
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj : j < gs.length := by omega
        rcases (leg H j hj).1 with ha | ho
        · have hA : isAnd (gt gs j).op = true := by rw [ha]; rfl
          rw [qw_and N gs j hj hA, List.mem_singleton] at hq
          rw [hq] at hv
          obtain ⟨hu, hv', hall⟩ := uv_mem H j hj ha
          have hult := hR H j hj _ hu
          have hvlt := hR H j hj _ hv'
          rcases (dv_a4 N gs z j hj hA).1 hv with h | h
          · rcases (dv_a2 N gs z j hj hA).1 h with h0 | h0
            · obtain ⟨⟨q1, hq1, hq1v⟩, ⟨q2, hq2, hq2v⟩⟩ :=
                (prod_val N gs z j hj true hA hult hvlt).1 h0
              obtain ⟨k1, hk1, hzk1, hk1v⟩ := (invA H true z (ua gs j)).1 ⟨q1, hq1, hq1v⟩
              obtain ⟨k2, hk2, hzk2, hk2v⟩ := (invA H (!true) z (va gs j)).1 ⟨q2, hq2, hq2v⟩
              exact and_pair H j hj ha (ua gs j) (va gs j) hall z k1 k2 (by simpa using hk1)
                (by simpa using hk2) hzk1 hzk2 hk1v hk2v
            · obtain ⟨⟨q1, hq1, hq1v⟩, ⟨q2, hq2, hq2v⟩⟩ :=
                (prod_val N gs z j hj false hA hult hvlt).1 h0
              obtain ⟨k2, hk2, hzk2, hk2v⟩ := (invA H false z (ua gs j)).1 ⟨q1, hq1, hq1v⟩
              obtain ⟨k1, hk1, hzk1, hk1v⟩ := (invA H (!false) z (va gs j)).1 ⟨q2, hq2, hq2v⟩
              exact and_pair H j hj ha (va gs j) (ua gs j) (fun i hi => (hall i hi).symm) z k1 k2
                (by simpa using hk1) (by simpa using hk2) hzk1 hzk2 hk1v hk2v
          · obtain ⟨i3, hi3, hi3v⟩ := (dv_a3 N gs z j hj hA hult hvlt).1 h
            rcases List.mem_append.1 hi3 with h3 | h3
            · exact ih (ua gs j) hult ⟨i3, h3, hi3v⟩
            · exact ih (va gs j) hvlt ⟨i3, h3, hi3v⟩
        · have hna : isAnd (gt gs j).op = false := by rw [ho]; rfl
          rw [qw_or N gs j hj hna, List.mem_singleton] at hq
          rw [hq] at hv
          obtain ⟨i, hi, hiv⟩ := (dv_o2 H z j hj hna).1 hv
          obtain ⟨u, hu, hiu⟩ := List.mem_flatMap.1 hi
          exact ih u (hR H j hj u hu) ⟨i, hiu, hiv⟩

theorem invD {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs)
    (z : Fin (N + N) → Bool) (k1 k2 : Fin (N + N)) (h1 : k1.val < N) (h2 : N ≤ k2.val)
    (hz1 : z k1 = true) (hz2 : z k2 = true) :
    ∀ w, val gs w (fun k' : Fin (N + N) => decide (k' = k1 ∨ k' = k2)) = true →
      val gs w (fun k' : Fin (N + N) => decide (k' = k1)) = true ∨
      val gs w (fun k' : Fin (N + N) => decide (k' = k2)) = true ∨
      ∃ q ∈ qw N gs w, val (dgs N gs) q z = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hwn : w < N + N
    · rw [val_input gs _ w hwn] at hv
      rcases of_decide_eq_true hv with e | e
      · left
        rw [val_input gs _ w hwn]
        exact decide_eq_true e
      · right
        left
        rw [val_input gs _ w hwn]
        exact decide_eq_true e
    · by_cases hbig : N + N + gs.length ≤ w
      · rw [val_big gs _ w hbig] at hv
        exact Bool.noConfusion hv
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj : j < gs.length := by omega
        rcases (leg H j hj).1 with ha | ho
        · have hA : isAnd (gt gs j).op = true := by rw [ha]; rfl
          obtain ⟨hu, hv', hall⟩ := uv_mem H j hj ha
          have hall' := (cv_and H j hj ha _).1 hv
          have hult := hR H j hj _ hu
          have hvlt := hR H j hj _ hv'
          have hQ4 : (val (dgs N gs) (N + N + (5 * j + 2)) z = true ∨
              val (dgs N gs) (N + N + (5 * j + 3)) z = true) →
              ∃ q ∈ qw N gs (N + N + j), val (dgs N gs) q z = true := by
            intro h
            rw [qw_and N gs j hj hA]
            exact ⟨_, List.mem_singleton_self _, (dv_a4 N gs z j hj hA).2 h⟩
          have hP : ∀ s : Bool, val (dgs N gs) (N + N + (5 * j + off s)) z = true →
              ∃ q ∈ qw N gs (N + N + j), val (dgs N gs) q z = true := by
            intro s hs
            apply hQ4
            left
            rw [dv_a2 N gs z j hj hA]
            cases s
            · exact Or.inr hs
            · exact Or.inl hs
          have hQ3 : ∀ q, q ∈ qw N gs (ua gs j) ++ qw N gs (va gs j) →
              val (dgs N gs) q z = true →
              ∃ q ∈ qw N gs (N + N + j), val (dgs N gs) q z = true := by
            intro q hq hqv
            apply hQ4
            right
            exact (dv_a3 N gs z j hj hA hult hvlt).2 ⟨q, hq, hqv⟩
          rcases ih _ hult (hall' _ hu) with a1 | a2 | ⟨q, hq, hqv⟩
          · rcases ih _ hvlt (hall' _ hv') with b1 | b2 | ⟨q, hq, hqv⟩
            · left
              rw [cv_and H j hj ha]
              intro i hi
              rcases hall i hi with e | e
              · rw [e]
                exact a1
              · rw [e]
                exact b1
            · right
              right
              apply hP true
              rw [prod_val N gs z j hj true hA hult hvlt]
              exact ⟨(invA H true z _).2 ⟨k1, by simpa using h1, hz1, a1⟩,
                (invA H (!true) z _).2 ⟨k2, by simpa using h2, hz2, b2⟩⟩
            · right
              right
              exact hQ3 q (List.mem_append_right _ hq) hqv
          · rcases ih _ hvlt (hall' _ hv') with b1 | b2 | ⟨q, hq, hqv⟩
            · right
              right
              apply hP false
              rw [prod_val N gs z j hj false hA hult hvlt]
              exact ⟨(invA H false z _).2 ⟨k2, by simpa using h2, hz2, a2⟩,
                (invA H (!false) z _).2 ⟨k1, by simpa using h1, hz1, b1⟩⟩
            · right
              left
              rw [cv_and H j hj ha]
              intro i hi
              rcases hall i hi with e | e
              · rw [e]
                exact a2
              · rw [e]
                exact b2
            · right
              right
              exact hQ3 q (List.mem_append_right _ hq) hqv
          · right
            right
            exact hQ3 q (List.mem_append_left _ hq) hqv
        · have hna : isAnd (gt gs j).op = false := by rw [ho]; rfl
          obtain ⟨u, hu, huv⟩ := (cv_or H j hj ho _).1 hv
          rcases ih u (hR H j hj u hu) huv with a1 | a2 | ⟨q, hq, hqv⟩
          · left
            exact (cv_or H j hj ho _).2 ⟨u, hu, a1⟩
          · right
            left
            exact (cv_or H j hj ho _).2 ⟨u, hu, a2⟩
          · right
            right
            rw [qw_or N gs j hj hna]
            exact ⟨_, List.mem_singleton_self _,
              (dv_o2 H z j hj hna).2 ⟨q, List.mem_flatMap.2 ⟨u, hu, hq⟩, hqv⟩⟩

theorem dg_legal {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) (j : ℕ)
    (hj : j < gs.length) (r : ℕ) :
    ((dg N gs j r).op = GateOp.and ∨ (dg N gs j r).op = GateOp.or) ∧
      (dg N gs j r).inputs.length ≤ 2 := by
  have hl := (leg H j hj).2
  have f1 := flat_len (sw N gs true) (sw_len N gs true) (gt gs j).inputs
  have f2 := flat_len (sw N gs false) (sw_len N gs false) (gt gs j).inputs
  have f3 := flat_len (qw N gs) (qw_len N gs) (gt gs j).inputs
  have q1 := qw_len N gs (ua gs j)
  have q2 := qw_len N gs (va gs j)
  unfold dg
  split_ifs <;> first
    | exact prod_legal _ _
    | exact ⟨Or.inr rfl, le_trans f1 hl⟩
    | exact ⟨Or.inr rfl, le_trans f2 hl⟩
    | exact ⟨Or.inr rfl, le_trans f3 hl⟩
    | exact ⟨Or.inr rfl, by
        show (qw N gs (ua gs j) ++ qw N gs (va gs j)).length ≤ 2
        rw [List.length_append]
        omega⟩
    | exact ⟨Or.inr rfl, by simp⟩

theorem dgs_legal {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) :
    ∀ g ∈ dgs N gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  unfold dgs at hg
  rw [List.mem_map] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  rw [List.mem_range] at hi
  exact dg_legal H (i / 5) (by omega) (i % 5)

theorem dg_rb {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) (j : ℕ)
    (hj : j < gs.length) (r : ℕ) (hr : r < 5) :
    ∀ a ∈ (dg N gs j r).inputs, a < N + N + (5 * j + r) := by
  intro a ha
  rcases hb : isAnd (gt gs j).op with _ | _
  · interval_cases r
    · rw [dg_o0 N gs j hb] at ha
      obtain ⟨u, hu, hau⟩ := List.mem_flatMap.1 ha
      have := sw_lt N gs true u j a (hR H j hj u hu) hau
      omega
    · rw [dg_o1 N gs j hb] at ha
      obtain ⟨u, hu, hau⟩ := List.mem_flatMap.1 ha
      have := sw_lt N gs false u j a (hR H j hj u hu) hau
      omega
    · rw [dg_o2 N gs j hb] at ha
      obtain ⟨u, hu, hau⟩ := List.mem_flatMap.1 ha
      have := qw_lt N gs u j a (hR H j hj u hu) hau
      omega
    · rw [dg_o3 N gs j hb] at ha
      simp at ha
    · rw [dg_o4 N gs j hb] at ha
      simp at ha
  · have hop := (isAnd_iff _).1 hb
    obtain ⟨hu, hv, _⟩ := uv_mem H j hj hop
    have hul := hR H j hj _ hu
    have hvl := hR H j hj _ hv
    interval_cases r
    · rw [dg_a0 N gs j hb] at ha
      rcases prod_mem _ _ a ha with h | h
      · have := sw_lt N gs true (ua gs j) j a hul h
        omega
      · have := sw_lt N gs false (va gs j) j a hvl h
        omega
    · rw [dg_a1 N gs j hb] at ha
      rcases prod_mem _ _ a ha with h | h
      · have := sw_lt N gs false (ua gs j) j a hul h
        omega
      · have := sw_lt N gs true (va gs j) j a hvl h
        omega
    · rw [dg_a2 N gs j hb] at ha
      simp at ha
      omega
    · rw [dg_a3 N gs j hb] at ha
      rcases List.mem_append.1 ha with h | h
      · have := qw_lt N gs (ua gs j) j a hul h
        omega
      · have := qw_lt N gs (va gs j) j a hvl h
        omega
    · rw [dg_a4 N gs j hb] at ha
      simp at ha
      omega

theorem dgs_rb {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) :
    ∀ i, i < (dgs N gs).length → ∀ a ∈ (gt (dgs N gs) i).inputs, a < N + N + i := by
  intro i hi a ha
  rw [dgs_len] at hi
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 5 ∧ i = 5 * j + r := ⟨i / 5, i % 5, by omega, by omega⟩
  have hj : j < gs.length := by omega
  rw [gtD N gs j r hj hr] at ha
  exact dg_rb H j hj r hr a ha

def SS (N : ℕ) (gs : List Gate) (s : Bool) : Finset ℕ :=
  (Finset.range (N + N + gs.length)).biUnion (fun u => (sw N gs s u).toFinset)

theorem mem_SS (N : ℕ) (gs : List Gate) (s : Bool) (w : ℕ) :
    w ∈ SS N gs s ↔ ∃ u, u < N + N + gs.length ∧ w ∈ sw N gs s u := by
  simp [SS]

theorem S_closed {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs)
    (s : Bool) : ∀ w ∈ SS N gs s, (w < N + N ∧ decide (w < N) = s) ∨
      ∃ i < (dgs N gs).length, w = N + N + i ∧ (gt (dgs N gs) i).op = GateOp.or ∧
        ∀ u ∈ (gt (dgs N gs) i).inputs, u ∈ SS N gs s := by
  intro w hw
  obtain ⟨u, hu, hwu⟩ := (mem_SS N gs s w).1 hw
  by_cases hun : u < N + N
  · rw [sw_in N gs s u hun] at hwu
    by_cases hs : decide (u < N) = s
    · rw [if_pos hs, List.mem_singleton] at hwu
      left
      rw [hwu]
      exact ⟨hun, hs⟩
    · rw [if_neg hs] at hwu
      simp at hwu
  · obtain ⟨j, rfl⟩ : ∃ j, u = N + N + j := ⟨u - (N + N), by omega⟩
    have hj : j < gs.length := by omega
    rcases hb : isAnd (gt gs j).op with _ | _
    · rw [sw_or N gs s j hj hb, List.mem_singleton] at hwu
      have ho := off_le s
      have eg := gtD N gs j (off s) hj (by omega)
      rw [dg_os N gs j s hb] at eg
      right
      refine ⟨5 * j + off s, by rw [dgs_len]; omega, hwu, congrArg Gate.op eg, ?_⟩
      intro x hx
      rw [eg] at hx
      obtain ⟨v, hv, hxv⟩ := List.mem_flatMap.1 hx
      exact (mem_SS N gs s x).2 ⟨v, by have := hR H j hj v hv; omega, hxv⟩
    · rw [sw_and N gs s j hj hb] at hwu
      simp at hwu

theorem D_and {N : ℕ} {I : Fin N → Fin N → Prop} {gs : List Gate} (H : Hyp N I gs) :
    ∀ i, i < (dgs N gs).length → (gt (dgs N gs) i).op = GateOp.and →
      ∃ a b : ℕ, (gt (dgs N gs) i).inputs = [a, b] ∧
        ((a ∈ SS N gs true ∧ b ∈ SS N gs false) ∨ (a ∈ SS N gs false ∧ b ∈ SS N gs true)) := by
  intro i hi hop
  rw [dgs_len] at hi
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 5 ∧ i = 5 * j + r := ⟨i / 5, i % 5, by omega, by omega⟩
  have hj : j < gs.length := by omega
  rw [gtD N gs j r hj hr] at hop ⊢
  rcases hb : isAnd (gt gs j).op with _ | _
  · exfalso
    interval_cases r
    · rw [dg_o0 N gs j hb] at hop
      simp at hop
    · rw [dg_o1 N gs j hb] at hop
      simp at hop
    · rw [dg_o2 N gs j hb] at hop
      simp at hop
    · rw [dg_o3 N gs j hb] at hop
      simp at hop
    · rw [dg_o4 N gs j hb] at hop
      simp at hop
  · have hop' := (isAnd_iff _).1 hb
    obtain ⟨hu, hv, _⟩ := uv_mem H j hj hop'
    have hul : ua gs j < N + N + gs.length := by have := hR H j hj _ hu; omega
    have hvl : va gs j < N + N + gs.length := by have := hR H j hj _ hv; omega
    interval_cases r
    · rw [dg_a0 N gs j hb] at hop ⊢
      obtain ⟨x, y, hx, hy, hxy⟩ := prod_and _ _ hop
      exact ⟨x, y, hxy, Or.inl ⟨(mem_SS N gs true x).2 ⟨_, hul, by rw [hx]; simp⟩,
        (mem_SS N gs false y).2 ⟨_, hvl, by rw [hy]; simp⟩⟩⟩
    · rw [dg_a1 N gs j hb] at hop ⊢
      obtain ⟨x, y, hx, hy, hxy⟩ := prod_and _ _ hop
      exact ⟨x, y, hxy, Or.inr ⟨(mem_SS N gs false x).2 ⟨_, hul, by rw [hx]; simp⟩,
        (mem_SS N gs true y).2 ⟨_, hvl, by rw [hy]; simp⟩⟩⟩
    · exfalso
      rw [dg_a2 N gs j hb] at hop
      simp at hop
    · exfalso
      rw [dg_a3 N gs j hb] at hop
      simp at hop
    · exfalso
      rw [dg_a4 N gs j hb] at hop
      simp at hop

theorem out_val (N : ℕ) (gs : List Gate) (z : Fin (N + N) → Bool) (o : ℕ) :
    val (dgs N gs) ((qw N gs o).headD (N + N + 5 * gs.length)) z = true ↔
      ∃ q ∈ qw N gs o, val (dgs N gs) q z = true := by
  rcases qw_cases N gs o with h | ⟨q, h⟩
  · rw [h]
    have h0 : val (dgs N gs) (N + N + 5 * gs.length) z = false :=
      val_big _ z _ (le_of_eq (by rw [dgs_len]))
    simp [h0]
  · rw [h]
    simp

theorem main : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → (C.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨ (C.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (C.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ 5 * C.size ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = true ↔ ∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true) ∧ (∀ w ∈ P, w < N ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  intro N I _ C _ hmono hrb hf hc1 hc2
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    refine ⟨⟨[], 0⟩, ∅, ∅, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · intro j hj
      exact absurd hj (Nat.not_lt_zero _)
    · exact Nat.zero_le _
    · intro y
      constructor
      · intro h
        have h1 : (List.ofFn y).getD 0 false = true := h
        have h2 : (List.ofFn y).getD 0 false = false := List.getD_eq_default _ _ (by simp)
        rw [h2] at h1
        exact Bool.noConfusion h1
      · rintro ⟨p, _⟩
        exact p.elim0
    · intro w hw
      simp at hw
    · intro w hw
      simp at hw
    · intro i hi
      exact absurd hi (Nat.not_lt_zero _)
  · have H : Hyp N I C.gates := by
      refine ⟨h0, legal_of C hmono, fun j hj i hi => hrb j hj i hi, ?_,
        fun j hj ha z hz => hc1 j hj ha z hz⟩
      intro j hj ha k
      by_cases hk : k.val < N
      · obtain ⟨p, rfl⟩ : ∃ p : Fin N, k = Fin.castAdd N p := ⟨⟨k.val, hk⟩, Fin.ext (by simp)⟩
        exact (hc2 j hj ha).1 p
      · have hkl := k.isLt
        obtain ⟨l, rfl⟩ : ∃ l : Fin N, k = Fin.natAdd N l :=
          ⟨⟨k.val - N, by omega⟩, Fin.ext (by
            rw [Fin.coe_natAdd]
            show k.val = N + (k.val - N)
            omega)⟩
        exact (hc2 j hj ha).2 l
    refine ⟨⟨dgs N C.gates, (qw N C.gates C.output).headD (N + N + 5 * C.gates.length)⟩,
      SS N C.gates true, SS N C.gates false, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨h1, h2⟩ := dgs_legal H g hg
      refine ⟨?_, h2⟩
      rcases h1 with h | h
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        exact Or.inr rfl
    · exact dgs_rb H
    · exact le_of_eq (dgs_len N C.gates)
    · intro y
      show val (dgs N C.gates) ((qw N C.gates C.output).headD (N + N + 5 * C.gates.length)) y
        = true ↔ _
      rw [out_val]
      constructor
      · exact invC H y C.output
      · rintro ⟨p, l, hI, hp, hl⟩
        have hC : val C.gates C.output
            (fun k' : Fin (N + N) => decide (k' = Fin.castAdd N p ∨ k' = Fin.natAdd N l)) = true :=
          (hf (fun k' : Fin (N + N) => decide (k' = Fin.castAdd N p ∨ k' = Fin.natAdd N l))).2
            ⟨p, l, hI, by simp, by simp⟩
        rcases invD H y (Fin.castAdd N p) (Fin.natAdd N l) (by simp) (by simp) hp hl
          C.output hC with h | h | h
        · exfalso
          obtain ⟨p', l', _, _, hl'⟩ :=
            (hf (fun k' : Fin (N + N) => decide (k' = Fin.castAdd N p))).1 h
          have h5 := congrArg Fin.val (of_decide_eq_true hl')
          have h6 := p.isLt
          simp at h5
          omega
        · exfalso
          obtain ⟨p', l', _, hp', _⟩ :=
            (hf (fun k' : Fin (N + N) => decide (k' = Fin.natAdd N l))).1 h
          have h5 := congrArg Fin.val (of_decide_eq_true hp')
          have h6 := p'.isLt
          simp at h5
          omega
        · exact h
    · intro w hw
      rcases S_closed H true w hw with ⟨_, h2⟩ | h
      · left
        simpa using h2
      · right
        exact h
    · intro w hw
      rcases S_closed H false w hw with ⟨h1, h2⟩ | h
      · left
        exact ⟨by simpa using h2, h1⟩
      · right
        exact h
    · exact D_and H

end PEqualNP.Outside.L_meta_2052

theorem PEqualNP.Outside.L_meta_2052 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → (C.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨ (C.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (C.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (C.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ 5 * C.size ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = true ↔ ∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true) ∧ (∀ w ∈ P, w < N ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (N ≤ w ∧ w < N + N) ∨ ∃ i < D.gates.length, w = N + N + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  exact PEqualNP.Outside.L_meta_2052.main
