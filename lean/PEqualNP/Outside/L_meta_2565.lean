import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2565

open PEqualNP.CircuitLowerBounds

abbrev St := Bool ⊕ ℕ

def ev (w : List Bool) : St → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def wiresOf : List St → List ℕ
  | [] => []
  | Sum.inl _ :: l => wiresOf l
  | Sum.inr k :: l => k :: wiresOf l

def hasConst (b : Bool) : List St → Bool
  | [] => false
  | Sum.inl c :: l => (c == b) || hasConst b l
  | Sum.inr _ :: l => hasConst b l

def resAnd (l : List St) : Option St :=
  if hasConst false l then some (Sum.inl false) else
    match wiresOf l with
    | [] => some (Sum.inl true)
    | [k] => some (Sum.inr k)
    | _ => none

def resOr (l : List St) : Option St :=
  if hasConst true l then some (Sum.inl true) else
    match wiresOf l with
    | [] => some (Sum.inl false)
    | [k] => some (Sum.inr k)
    | _ => none

def resNot : List St → Option St
  | [] => some (Sum.inl true)
  | Sum.inl b :: _ => some (Sum.inl (!b))
  | Sum.inr _ :: _ => none

def res : GateOp → List St → Option St
  | GateOp.and, l => resAnd l
  | GateOp.or, l => resOr l
  | GateOp.not, l => resNot l
  | _, _ => none

def stOf (st : List St) (i : ℕ) : St := st.getD i (Sum.inl false)

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def step (n : ℕ) (p : List St × List Gate) (g : Gate) : List St × List Gate :=
  match res g.op (g.inputs.map (stOf p.1)) with
  | some s => (p.1 ++ [s], p.2)
  | none => (p.1 ++ [Sum.inr (n + p.2.length)],
      p.2 ++ [⟨g.op, wiresOf (g.inputs.map (stOf p.1))⟩])

def hitIdx (i : ℕ) : Bool := i == 4 || i == 9

def hit (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, l => l.any hitIdx
  | GateOp.or, l => l.any hitIdx
  | GateOp.not, i :: _ => hitIdx i
  | _, _ => false

def Good (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def Inv (st : List St) (Cw Dw : List Bool) : Prop :=
  st.length = Cw.length ∧ (∀ i, Cw.getD i false = ev Dw (stOf st i)) ∧
    (∀ k, Sum.inr k ∈ st → k < Dw.length)

def outIdx : St → ℕ → ℕ
  | Sum.inl _, m => m
  | Sum.inr k, _ => k

lemma ite_t {α : Type} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

lemma ite_f {α : Type} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) :
    (if c then a else b) = b := by simp [h]

lemma getD_snoc {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default]; simp; omega

lemma all_ev (w : List Bool) (l : List St) (h : hasConst false l = false) :
    (l.map (ev w)).all id = ((wiresOf l).map fun i => w.getD i false).all id := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rcases s with c | k
    · cases c
      · simp [hasConst] at h
      · simp only [hasConst] at h
        simp [wiresOf, ev, ih (by simpa using h)]
    · simp only [hasConst] at h
      simp [wiresOf, ev, ih h]

lemma all_ev_false (w : List Bool) (l : List St) (h : hasConst false l = true) :
    (l.map (ev w)).all id = false := by
  induction l with
  | nil => simp [hasConst] at h
  | cons s l ih =>
    rcases s with c | k
    · cases c
      · simp [ev]
      · simp only [hasConst] at h
        simp [ev, ih (by simpa using h)]
    · simp only [hasConst] at h
      simp [ev, ih h]

lemma any_ev (w : List Bool) (l : List St) (h : hasConst true l = false) :
    (l.map (ev w)).any id = ((wiresOf l).map fun i => w.getD i false).any id := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rcases s with c | k
    · cases c
      · simp only [hasConst] at h
        simp [wiresOf, ev, ih (by simpa using h)]
      · simp [hasConst] at h
    · simp only [hasConst] at h
      simp [wiresOf, ev, ih h]

lemma any_ev_true (w : List Bool) (l : List St) (h : hasConst true l = true) :
    (l.map (ev w)).any id = true := by
  induction l with
  | nil => simp [hasConst] at h
  | cons s l ih =>
    rcases s with c | k
    · cases c
      · simp only [hasConst] at h
        simp [ev, ih (by simpa using h)]
      · simp [ev]
    · simp only [hasConst] at h
      simp [ev, ih h]

lemma mem_wiresOf (l : List St) (k : ℕ) (h : k ∈ wiresOf l) : Sum.inr k ∈ l := by
  induction l with
  | nil => simp [wiresOf] at h
  | cons s l ih =>
    rcases s with c | j
    · simp only [wiresOf] at h
      exact List.mem_cons_of_mem _ (ih h)
    · simp only [wiresOf, List.mem_cons] at h
      rcases h with h | h
      · subst h; simp
      · exact List.mem_cons_of_mem _ (ih h)

lemma length_wiresOf_le (l : List St) : (wiresOf l).length ≤ l.length := by
  induction l with
  | nil => simp [wiresOf]
  | cons s l ih =>
    rcases s with c | j
    · simp only [wiresOf, List.length_cons]; omega
    · simp only [wiresOf, List.length_cons]; omega

lemma length_wiresOf_lt (l : List St) (b : Bool) (h : Sum.inl b ∈ l) :
    (wiresOf l).length < l.length := by
  induction l with
  | nil => simp at h
  | cons s l ih =>
    rcases s with c | j
    · simp only [wiresOf, List.length_cons]
      have := length_wiresOf_le l
      omega
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      simp only [wiresOf, List.length_cons]
      have := ih h
      omega

lemma hasConst_of_mem (l : List St) (b : Bool) (h : Sum.inl b ∈ l) : hasConst b l = true := by
  induction l with
  | nil => simp at h
  | cons s l ih =>
    rcases s with c | j
    · simp only [List.mem_cons, Sum.inl.injEq] at h
      rcases h with h | h
      · subst h; simp [hasConst]
      · simp [hasConst, ih h]
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      simp [hasConst, ih h]

lemma res_some_eval (w : List Bool) (op : GateOp) (l : List St) (s : St)
    (h : res op l = some s) : ev w s = op.eval (l.map (ev w)) := by
  cases op with
  | and =>
    simp only [res, resAnd] at h
    split_ifs at h with hc
    · simp at h; subst h
      simp [ev, GateOp.eval, all_ev_false w l hc]
    · have hc' : hasConst false l = false := by simpa using hc
      rcases hw : wiresOf l with _ | ⟨k, _ | ⟨k2, t⟩⟩ <;> rw [hw] at h <;> simp at h
      · subst h; simp [ev, GateOp.eval, all_ev w l hc', hw]
      · subst h; simp [ev, GateOp.eval, all_ev w l hc', hw]
  | or =>
    simp only [res, resOr] at h
    split_ifs at h with hc
    · simp at h; subst h
      simp [ev, GateOp.eval, any_ev_true w l hc]
    · have hc' : hasConst true l = false := by simpa using hc
      rcases hw : wiresOf l with _ | ⟨k, _ | ⟨k2, t⟩⟩ <;> rw [hw] at h <;> simp at h
      · subst h; simp [ev, GateOp.eval, any_ev w l hc', hw]
      · subst h; simp [ev, GateOp.eval, any_ev w l hc', hw]
  | not =>
    rcases l with _ | ⟨a, t⟩
    · simp [res, resNot] at h; subst h; simp [ev, GateOp.eval]
    · rcases a with b | k
      · simp [res, resNot] at h; subst h; simp [ev, GateOp.eval]
      · simp [res, resNot] at h
  | mod m => simp [res] at h
  | maj => simp [res] at h

lemma res_none_eval (w : List Bool) (op : GateOp) (l : List St)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (h : res op l = none) :
    op.eval ((wiresOf l).map fun i => w.getD i false) = op.eval (l.map (ev w)) := by
  rcases hop with rfl | rfl | rfl
  · simp only [res, resAnd] at h
    split_ifs at h with hc
    have hc' : hasConst false l = false := by simpa using hc
    simp [GateOp.eval, all_ev w l hc']
  · simp only [res, resOr] at h
    split_ifs at h with hc
    have hc' : hasConst true l = false := by simpa using hc
    simp [GateOp.eval, any_ev w l hc']
  · rcases l with _ | ⟨a, t⟩
    · simp [res, resNot] at h
    · rcases a with b | k
      · simp [res, resNot] at h
      · simp [GateOp.eval, wiresOf, ev]

lemma res_some_mem (op : GateOp) (l : List St) (k : ℕ) (h : res op l = some (Sum.inr k)) :
    Sum.inr k ∈ l := by
  cases op with
  | and =>
    simp only [res, resAnd] at h
    split_ifs at h with hc
    · simp at h
    · rcases hw : wiresOf l with _ | ⟨j, _ | ⟨k2, t⟩⟩ <;> rw [hw] at h <;> simp at h
      subst h
      exact mem_wiresOf l j (by simp [hw])
  | or =>
    simp only [res, resOr] at h
    split_ifs at h with hc
    · simp at h
    · rcases hw : wiresOf l with _ | ⟨j, _ | ⟨k2, t⟩⟩ <;> rw [hw] at h <;> simp at h
      subst h
      exact mem_wiresOf l j (by simp [hw])
  | not =>
    rcases l with _ | ⟨a, t⟩
    · simp [res, resNot] at h
    · rcases a with b | j
      · simp [res, resNot] at h
      · simp [res, resNot] at h
  | mod m => simp [res] at h
  | maj => simp [res] at h

lemma stOf_mem (st : List St) (i k : ℕ) (h : stOf st i = Sum.inr k) : Sum.inr k ∈ st := by
  unfold stOf at h
  rw [List.getD_eq_getElem?_getD] at h
  rcases hi : st[i]? with _ | s
  · rw [hi] at h; simp at h
  · rw [hi] at h; simp at h; subst h
    exact List.mem_of_getElem? hi

lemma ev_snoc (Dw : List Bool) (v : Bool) (s : St) (h : ∀ k, s = Sum.inr k → k < Dw.length) :
    ev (Dw ++ [v]) s = ev Dw s := by
  rcases s with b | k
  · rfl
  · have hk := h k rfl
    simp only [ev, getD_snoc, hk, ↓reduceIte]

lemma foldl_F_length (L : List Gate) : ∀ w : List Bool, (L.foldl F w).length = w.length + L.length := by
  induction L with
  | nil => intro w; simp
  | cons g L ih => intro w; simp [ih, F]; omega

lemma step_inv (n : ℕ) (y0 : List Bool) (hy : y0.length = n) (st : List St) (gs : List Gate)
    (Cw : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hI : Inv st Cw (gs.foldl F y0)) :
    Inv (step n (st, gs) g).1 (F Cw g) ((step n (st, gs) g).2.foldl F y0) := by
  obtain ⟨hl, hv, hb⟩ := hI
  have hDl : (gs.foldl F y0).length = n + gs.length := by rw [foldl_F_length, hy]
  have hmap : g.inputs.map (fun i => Cw.getD i false) =
      (g.inputs.map (stOf st)).map (ev (gs.foldl F y0)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact hv i
  have hbl : ∀ k, Sum.inr k ∈ g.inputs.map (stOf st) → k < (gs.foldl F y0).length := by
    intro k hk
    rw [List.mem_map] at hk
    obtain ⟨i, _, hi⟩ := hk
    exact hb k (stOf_mem st i k hi)
  have hfold : ∀ e : Gate, (gs ++ [e]).foldl F y0 = F (gs.foldl F y0) e := by
    intro e
    rw [List.foldl_append]
    rfl
  simp only [step]
  generalize hlg : g.inputs.map (stOf st) = l at hmap hbl ⊢
  rcases hr : res g.op l with _ | s
  · rw [hfold]
    generalize hDw : gs.foldl F y0 = Dw at hDl hv hb hmap hbl ⊢
    have hval : g.op.eval (g.inputs.map fun i => Cw.getD i false) =
        GateOp.eval g.op ((wiresOf l).map fun i => Dw.getD i false) := by
      rw [hmap, res_none_eval Dw g.op l hop hr]
    refine ⟨?_, ?_, ?_⟩
    · simp [F, hl]
    · intro i
      simp only [F, stOf, getD_snoc]
      rw [← hl]
      split_ifs with h1 h2
      · have := hv i
        simp only [stOf] at this
        rw [this, ev_snoc]
        intro k hk
        exact hb k (stOf_mem st i k hk)
      · show _ = (Dw ++ [_]).getD (n + gs.length) false
        rw [getD_snoc, ite_f (by omega), ite_t (by omega)]
        exact hval
      · rfl
    · intro k hk
      simp only [List.mem_append, List.mem_singleton, Sum.inr.injEq] at hk
      simp only [F, List.length_append, List.length_singleton]
      rcases hk with hk | hk
      · have := hb k hk; omega
      · omega
  · generalize hDw : gs.foldl F y0 = Dw at hDl hv hb hmap hbl ⊢
    have hval : g.op.eval (g.inputs.map fun i => Cw.getD i false) = ev Dw s := by
      rw [hmap, res_some_eval Dw g.op l s hr]
    refine ⟨?_, ?_, ?_⟩
    · simp [F, hl]
    · intro i
      simp only [F, stOf, getD_snoc]
      rw [← hl]
      split_ifs with h1 h2
      · exact hv i
      · exact hval
      · rfl
    · intro k hk
      simp only [List.mem_append, List.mem_singleton] at hk
      rcases hk with hk | hk
      · exact hb k hk
      · subst hk
        exact hbl k (res_some_mem g.op l k hr)

lemma run_inv (n : ℕ) (y0 : List Bool) (hy : y0.length = n) (L : List Gate) :
    ∀ (st : List St) (gs : List Gate) (Cw : List Bool),
    (∀ g ∈ L, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
    Inv st Cw (gs.foldl F y0) →
    Inv (L.foldl (step n) (st, gs)).1 (L.foldl F Cw)
      ((L.foldl (step n) (st, gs)).2.foldl F y0) := by
  induction L with
  | nil => intro st gs Cw _ h; simpa using h
  | cons g L ih =>
    intro st gs Cw hops hI
    have h1 := step_inv n y0 hy st gs Cw g (hops g (by simp)) hI
    have := ih (step n (st, gs) g).1 (step n (st, gs) g).2 (F Cw g)
      (fun g' hg' => hops g' (by simp [hg'])) h1
    simpa using this

lemma stOf_snoc (st : List St) (s : St) (i : ℕ) (h : i < st.length) :
    stOf (st ++ [s]) i = stOf st i := by
  unfold stOf
  rw [getD_snoc, ite_t h]

lemma hit_res (st : List St) (h4 : stOf st 4 = Sum.inl false) (h9 : stOf st 9 = Sum.inl false)
    (g : Gate) (hlen : g.inputs.length ≤ 2) (hh : hit g = true) :
    res g.op (g.inputs.map (stOf st)) ≠ none := by
  rcases g with ⟨op, ins⟩
  simp only at hlen ⊢
  have hmemf : (∃ i ∈ ins, hitIdx i = true) → Sum.inl false ∈ ins.map (stOf st) := by
    rintro ⟨i, hi, hx⟩
    rw [List.mem_map]
    refine ⟨i, hi, ?_⟩
    simp only [hitIdx, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with rfl | rfl
    · exact h4
    · exact h9
  cases op with
  | and =>
    simp only [hit, List.any_eq_true] at hh
    have hc := hasConst_of_mem _ _ (hmemf hh)
    simp [res, resAnd, hc]
  | or =>
    simp only [hit, List.any_eq_true] at hh
    have hm := hmemf hh
    have hlt := length_wiresOf_lt _ _ hm
    simp only [List.length_map] at hlt
    simp only [res, resOr]
    split_ifs with hc
    · simp
    · rcases hw : wiresOf (ins.map (stOf st)) with _ | ⟨j, _ | ⟨k2, t⟩⟩
      · simp
      · simp
      · rw [hw] at hlt; simp at hlt; omega
  | not =>
    rcases ins with _ | ⟨i, t⟩
    · simp [hit] at hh
    · simp only [hit] at hh
      have : stOf st i = Sum.inl false := by
        simp only [hitIdx, Bool.or_eq_true, beq_iff_eq] at hh
        rcases hh with rfl | rfl
        · exact h4
        · exact h9
      simp [res, resNot, this]
  | mod m => simp [hit] at hh
  | maj => simp [hit] at hh

lemma run_count (n : ℕ) (L : List Gate) : ∀ (st : List St) (gs : List Gate),
    stOf st 4 = Sum.inl false → stOf st 9 = Sum.inl false → 10 ≤ st.length →
    (∀ g ∈ L, g.inputs.length ≤ 2) →
    (L.foldl (step n) (st, gs)).2.length + L.countP hit ≤ gs.length + L.length := by
  induction L with
  | nil => intro st gs _ _ _ _; simp
  | cons g L ih =>
    intro st gs h4 h9 h10 hlen
    simp only [List.foldl_cons, List.countP_cons, List.length_cons]
    have hst : (step n (st, gs) g).1.length = st.length + 1 := by
      simp only [step]; split <;> simp
    have h4' : stOf (step n (st, gs) g).1 4 = Sum.inl false := by
      simp only [step]; split <;> (simp only; rw [stOf_snoc _ _ _ (by omega)]; exact h4)
    have h9' : stOf (step n (st, gs) g).1 9 = Sum.inl false := by
      simp only [step]; split <;> (simp only; rw [stOf_snoc _ _ _ (by omega)]; exact h9)
    have := ih (step n (st, gs) g).1 (step n (st, gs) g).2 h4' h9' (by omega)
      (fun g' hg' => hlen g' (by simp [hg']))
    simp only [Prod.mk.eta] at this
    by_cases hh : hit g = true
    · have hr := hit_res st h4 h9 g (hlen g (by simp)) hh
      have hgs : (step n (st, gs) g).2 = gs := by
        simp only [step]
        rcases hr' : res g.op (g.inputs.map (stOf st)) with _ | s
        · exact absurd hr' hr
        · rfl
      rw [hgs] at this
      simp only [hh, ↓reduceIte]
      omega
    · have hgs : (step n (st, gs) g).2.length ≤ gs.length + 1 := by
        simp only [step]; split <;> simp
      simp only [hh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

lemma run_good (n : ℕ) (L : List Gate) : ∀ (st : List St) (gs : List Gate),
    (∀ g ∈ L, Good g) → (∀ e ∈ gs, Good e) → ∀ e ∈ (L.foldl (step n) (st, gs)).2, Good e := by
  induction L with
  | nil => intro st gs _ h; simpa using h
  | cons g L ih =>
    intro st gs hL hgs
    simp only [List.foldl_cons]
    have hg := hL g (by simp)
    have := ih (step n (st, gs) g).1 (step n (st, gs) g).2
      (fun g' hg' => hL g' (by simp [hg']))
    simp only [Prod.mk.eta] at this
    apply this
    simp only [step]
    split
    · exact hgs
    · intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact hgs e he
      · subst he
        refine ⟨hg.1, ?_⟩
        have := length_wiresOf_le (g.inputs.map (stOf st))
        simp only [List.length_map] at this
        exact le_trans this hg.2

lemma foldl_getD_lt (L : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (L.foldl F w).getD i false = w.getD i false := by
  induction L with
  | nil => intro w i _; rfl
  | cons g L ih =>
    intro w i hi
    simp only [List.foldl_cons]
    rw [ih (F w g) i (by simp [F]; omega)]
    simp only [F]
    rw [getD_snoc, ite_t hi]

lemma val_eq (W W' : List Bool) (g : Gate) (hg : Good g)
    (hh : hit g = true → g.op = GateOp.and ∧ 9 ∈ g.inputs)
    (h9 : W.getD 9 false = false) (h9' : W'.getD 9 false = false)
    (hag : ∀ i, i ≠ 4 → W.getD i false = W'.getD i false) :
    g.op.eval (g.inputs.map fun i => W.getD i false) =
      g.op.eval (g.inputs.map fun i => W'.getD i false) := by
  by_cases hht : hit g = true
  · obtain ⟨hop, h9in⟩ := hh hht
    rw [hop]
    have e1 : (g.inputs.map fun i => W.getD i false).all id = false := by
      rw [List.all_eq_false]
      exact ⟨false, List.mem_map.2 ⟨9, h9in, h9⟩, by simp⟩
    have e2 : (g.inputs.map fun i => W'.getD i false).all id = false := by
      rw [List.all_eq_false]
      exact ⟨false, List.mem_map.2 ⟨9, h9in, h9'⟩, by simp⟩
    simp only [GateOp.eval]
    rw [e1, e2]
  · rcases g with ⟨op, ins⟩
    obtain ⟨hop, _⟩ := hg
    simp only at hop ⊢
    have hmap : (∀ i ∈ ins, i ≠ 4) → (ins.map fun i => W.getD i false) =
        ins.map fun i => W'.getD i false := by
      intro h
      apply List.map_congr_left
      intro i hi
      exact hag i (h i hi)
    rcases hop with rfl | rfl | rfl
    · rw [hmap]
      intro i hi h4
      apply hht
      simp only [hit, List.any_eq_true]
      exact ⟨i, hi, by simp [hitIdx, h4]⟩
    · rw [hmap]
      intro i hi h4
      apply hht
      simp only [hit, List.any_eq_true]
      exact ⟨i, hi, by simp [hitIdx, h4]⟩
    · rcases ins with _ | ⟨i, t⟩
      · rfl
      · have hi4 : i ≠ 4 := by
          intro h4
          apply hht
          simp [hit, hitIdx, h4]
        simp only [GateOp.eval, List.map_cons, List.headD_cons]
        rw [hag i hi4]

lemma agree (L : List Gate) : ∀ (W W' : List Bool),
    (∀ g ∈ L, Good g) → (∀ g ∈ L, hit g = true → g.op = GateOp.and ∧ 9 ∈ g.inputs) →
    W.length = W'.length → 10 ≤ W.length → W.getD 9 false = false → W'.getD 9 false = false →
    (∀ i, i ≠ 4 → W.getD i false = W'.getD i false) →
    ∀ i, i ≠ 4 → (L.foldl F W).getD i false = (L.foldl F W').getD i false := by
  induction L with
  | nil => intro W W' _ _ _ _ _ _ hag; simpa using hag
  | cons g L ih =>
    intro W W' hgood hhit hlen h10 h9 h9' hag
    simp only [List.foldl_cons]
    have hv := val_eq W W' g (hgood g (by simp)) (hhit g (by simp)) h9 h9' hag
    apply ih (F W g) (F W' g) (fun g' hg' => hgood g' (by simp [hg']))
      (fun g' hg' => hhit g' (by simp [hg']))
    · simp [F, hlen]
    · simp [F]; omega
    · simp only [F, getD_snoc]; rw [ite_t (by omega)]; exact h9
    · simp only [F, getD_snoc]; rw [ite_t (by omega)]; exact h9'
    · intro i hi
      simp only [F, getD_snoc, hlen]
      split_ifs
      · exact hag i hi
      · exact hv
      · rfl

lemma two_le_countP (l : List Gate) (a b : Gate) (ha : a ∈ l) (hb : b ∈ l) (hab : b ≠ a)
    (pa : hit a = true) (pb : hit b = true) : 2 ≤ l.countP hit := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  simp only [List.countP_append, List.countP_cons, pa, ↓reduceIte]
  simp only [List.mem_append, List.mem_cons] at hb
  rcases hb with hb | hb | hb
  · have : 0 < s.countP hit := List.countP_pos_iff.2 ⟨b, hb, pb⟩
    omega
  · exact absurd hb hab
  · have : 0 < t.countP hit := List.countP_pos_iff.2 ⟨b, hb, pb⟩
    omega


lemma good_of_fan (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C) :
    ∀ g ∈ C.gates, Good g := by
  intro g hg
  obtain ⟨h1, h2⟩ := hfan g hg
  refine ⟨?_, h2⟩
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h1

def st0 : List St := [Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl false, Sum.inr 4,
  Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl false]

def rho (y : Fin 8 → Bool) : Fin 9 → Bool := ![y 0, y 1, y 2, y 3, false, y 4, y 5, y 6, y 7]

lemma inv0 (y : Fin 8 → Bool) :
    Inv st0 (List.ofFn (rho y) ++ [rho y 4 && rho y 6]) (List.ofFn y) := by
  have e1 : List.ofFn (rho y) ++ [rho y 4 && rho y 6] =
      [y 0, y 1, y 2, y 3, false, y 4, y 5, y 6, y 7, false] := by
    simp [rho, List.ofFn_succ]
  have e2 : List.ofFn y = [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7] := by simp [List.ofFn_succ]
  rw [e1, e2]
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    rcases Nat.lt_or_ge i 10 with h | h
    · interval_cases i <;> rfl
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [stOf]
      rw [List.getD_eq_default _ _ (by simp [st0]; omega)]
      rfl
  · intro k hk
    simp [st0] at hk
    simp
    omega

lemma main : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (9 : ℕ) ∈ x3.inputs) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ))) (x1.size - (2 : ℕ)) := by
  intro C hfan hex heval
  obtain ⟨g0, hg0, hop0, h90⟩ := hex
  have hgood := good_of_fan C hfan
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hgood g hg).1
  have hhit0 : hit g0 = true := by
    rcases g0 with ⟨op, ins⟩
    simp only at hop0 h90
    subst hop0
    simp only [hit, List.any_eq_true]
    exact ⟨9, h90, rfl⟩
  have hwires : ∀ X, C.eval X = (C.gates.foldl F X).getD C.output false := fun X => rfl
  have hcount : 2 ≤ C.gates.countP hit := by
    by_contra hlt
    have hall : ∀ h ∈ C.gates, hit h = true → h.op = GateOp.and ∧ 9 ∈ h.inputs := by
      intro h hh hhit
      by_cases heq : h = g0
      · subst heq; exact ⟨hop0, h90⟩
      · exact absurd (two_le_countP C.gates g0 h hg0 hh heq hhit0 hhit) hlt
    have e1 : C.eval [true, false, false, false, false, false, false, false, false, false] =
        false := by
      simpa [List.ofFn_succ] using heval ![true, false, false, false, false, false, false, false, false]
    have e2 : C.eval [true, false, false, false, true, false, false, false, false, false] =
        true := by
      simpa [List.ofFn_succ] using heval ![true, false, false, false, true, false, false, false, false]
    have e3 : C.eval [false, false, false, false, true, false, false, false, false, false] =
        false := by
      simpa [List.ofFn_succ] using heval ![false, false, false, false, true, false, false, false, false]
    rw [hwires] at e1 e2 e3
    by_cases ho : C.output = 4
    · rw [ho, foldl_getD_lt _ _ _ (by decide)] at e3
      exact absurd e3 (by decide)
    · have hag := agree C.gates [true, false, false, false, false, false, false, false, false, false]
        [true, false, false, false, true, false, false, false, false, false] hgood hall rfl
        (by decide) rfl rfl (by
          intro i hi
          rcases Nat.lt_or_ge i 10 with h | h
          · interval_cases i <;> first | rfl | exact absurd rfl hi
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]) C.output ho
      rw [hag, e2] at e1
      exact Bool.noConfusion e1
  have hfoldlen : ∀ (L : List Gate) (w : List Bool), (L.foldl F w).length = w.length + L.length :=
    foldl_F_length
  set p := C.gates.foldl (step 8) (st0, []) with hp
  have hcorr : ∀ y : Fin 8 → Bool, C.eval (List.ofFn (rho y) ++ [rho y 4 && rho y 6]) =
      ev (p.2.foldl F (List.ofFn y)) (stOf p.1 C.output) := by
    intro y
    have hI := run_inv 8 (List.ofFn y) (by simp) C.gates st0 [] _ hops (inv0 y)
    rw [hwires]
    exact hI.2.1 C.output
  have hne : stOf p.1 C.output ≠ Sum.inl true := by
    intro hs
    have h0 := hcorr (fun _ => false)
    rw [hs, heval] at h0
    simp [rho, ev] at h0
  refine ⟨⟨p.2, outIdx (stOf p.1 C.output) (8 + p.2.length)⟩, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨h1, h2⟩ := run_good 8 C.gates st0 [] hgood (by simp) e he
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · have := run_count 8 C.gates st0 [] rfl rfl (by simp [st0]) (fun g hg => (hgood g hg).2)
    rw [← hp] at this
    show p.2.length ≤ C.gates.length - 2
    simp only [List.length_nil, zero_add] at this
    omega
  · intro y
    have hlenD : (p.2.foldl F (List.ofFn y)).length = 8 + p.2.length := by
      rw [hfoldlen]; simp
    have key : Circuit.eval ⟨p.2, outIdx (stOf p.1 C.output) (8 + p.2.length)⟩ (List.ofFn y) =
        C.eval (List.ofFn (rho y) ++ [rho y 4 && rho y 6]) := by
      rw [hcorr y]
      show (p.2.foldl F (List.ofFn y)).getD (outIdx (stOf p.1 C.output) (8 + p.2.length)) false = _
      rcases hs : stOf p.1 C.output with b | k
      · cases b
        · simp only [outIdx, ev]
          rw [List.getD_eq_default _ _ (by omega)]
        · exact absurd hs hne
      · rfl
    rw [key, heval]
    simp [rho]

end PEqualNP.Outside.L_meta_2565

theorem PEqualNP.Outside.L_meta_2565 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (9 : ℕ) ∈ x3.inputs) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ))) (x1.size - (2 : ℕ)) :=
  PEqualNP.Outside.L_meta_2565.main
