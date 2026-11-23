import Mathlib
import PEqualNP.Defs

/-!
# Gate elimination for `¬x_p ∨ g`

Fix the input `p` to `true` in a fan-in-two circuit for `¬x_p ∨ g` and propagate constants:
every gate that reads a constant becomes a constant or a copy of one of its inputs and is
dropped. What is left computes `g`. If no gate were dropped, the same circuit would also come
out of fixing `p` to `false`, where the function is constantly `true`; so `g` would be
constant. Hence at least one gate is dropped.
-/

namespace PEqualNP.Outside.L_meta_199_aux

open PEqualNP.CircuitLowerBounds

/-- What an old wire becomes: a constant, or a wire of the new circuit. -/
inductive V where
  | c (b : Bool)
  | w (k : ℕ)
  deriving DecidableEq

/-- The value of `v` given the wire values `W` of the new circuit. -/
def V.den (W : List Bool) : V → Bool
  | .c b => b
  | .w k => W.getD k false

/-- The wire index of `v`, if it is a wire. -/
def V.getW : V → Option ℕ
  | .c _ => none
  | .w k => some k

/-- `v` names an existing wire (or a constant) among `L` wires. -/
def V.ok (L : ℕ) : V → Prop
  | .c _ => True
  | .w k => k < L

/-- A gate on the inputs `vs`, simplified: `some v` when it is a constant or a copy. -/
def simpV : GateOp → List V → Option V
  | .and, vs =>
    if V.c false ∈ vs then some (V.c false) else
      match vs.filterMap V.getW with
      | [] => some (V.c true)
      | [k] => some (V.w k)
      | _ => none
  | .or, vs =>
    if V.c true ∈ vs then some (V.c true) else
      match vs.filterMap V.getW with
      | [] => some (V.c false)
      | [k] => some (V.w k)
      | _ => none
  | .not, vs =>
    match vs.headD (V.c false) with
    | .c b => some (V.c (!b))
    | .w _ => none
  | _, _ => none

/-- The wires a kept gate reads in the new circuit. -/
def emitIns : GateOp → List V → List ℕ
  | .not, vs =>
    match vs.headD (V.c false) with
    | .c _ => []
    | .w k => [k]
  | _, vs => vs.filterMap V.getW

/-- One step of the transformation: map of old wires, and gates of the new circuit. -/
def step (n : ℕ) (st : List V × List Gate) (g : Gate) : List V × List Gate :=
  match simpV g.op (g.inputs.map (fun i => st.1.getD i (V.c false))) with
  | some v => (st.1 ++ [v], st.2)
  | none => (st.1 ++ [V.w (n + st.2.length)],
      st.2 ++ [⟨g.op, emitIns g.op (g.inputs.map (fun i => st.1.getD i (V.c false)))⟩])

/-- One step of circuit evaluation. -/
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The three allowed operations. -/
def Basic (op : GateOp) : Prop := op = .and ∨ op = .or ∨ op = .not

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

lemma length_foldl_wstep (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, wstep]; omega

lemma getD_concat {α : Type} (l : List α) (a d : α) (i : ℕ) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  rcases lt_trichotomy i l.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ i < l.length := by omega
    have h2 : i ≠ l.length := by omega
    simp only [h1, h2, if_false]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · simp; omega

lemma den_concat (W : List Bool) (b : Bool) (v : V) (h : v.ok W.length) :
    v.den (W ++ [b]) = v.den W := by
  cases v with
  | c => rfl
  | w k =>
    simp only [V.ok] at h
    simp only [V.den, getD_concat, if_pos h]

lemma ok_mono {L L' : ℕ} (h : L ≤ L') (v : V) (hv : v.ok L) : v.ok L' := by
  cases v with
  | c => trivial
  | w k => simp only [V.ok] at *; omega

lemma all_den (W : List Bool) (vs : List V) :
    (vs.map (V.den W)).all id =
      (decide (V.c false ∉ vs) && ((vs.filterMap V.getW).map (fun k => W.getD k false)).all id) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    cases v with
    | c b => cases b <;> simp [V.den, V.getW, ih]
    | w k =>
      simp only [List.map_cons, List.all_cons, ih, List.filterMap_cons, V.getW, V.den,
        List.mem_cons, reduceCtorEq, false_or, id]
      cases W.getD k false <;> cases decide (V.c false ∉ vs) <;> simp

lemma any_den (W : List Bool) (vs : List V) :
    (vs.map (V.den W)).any id =
      (decide (V.c true ∈ vs) || ((vs.filterMap V.getW).map (fun k => W.getD k false)).any id) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    cases v with
    | c b => cases b <;> simp [V.den, V.getW, ih]
    | w k =>
      simp only [List.map_cons, List.any_cons, ih, List.filterMap_cons, V.getW, V.den,
        List.mem_cons, reduceCtorEq, false_or, id]
      cases W.getD k false <;> cases decide (V.c true ∈ vs) <;> simp

lemma headD_den (W : List Bool) (vs : List V) :
    (vs.map (V.den W)).headD false = (vs.headD (V.c false)).den W := by
  cases vs <;> rfl

lemma simp_some (W : List Bool) (op : GateOp) (hop : Basic op) (vs : List V) (v : V)
    (h : simpV op vs = some v) : v.den W = op.eval (vs.map (V.den W)) := by
  rcases hop with rfl | rfl | rfl
  · simp only [simpV] at h
    simp only [GateOp.eval, all_den]
    split_ifs at h with hf
    · cases h; simp [V.den, hf]
    · simp only [hf, not_false_eq_true, decide_true, Bool.true_and]
      revert h
      generalize vs.filterMap V.getW = fm
      intro h
      rcases fm with _ | ⟨k, _ | ⟨k', fm⟩⟩ <;> simp at h <;> subst h <;> simp [V.den]
  · simp only [simpV] at h
    simp only [GateOp.eval, any_den]
    split_ifs at h with hf
    · cases h; simp [V.den, hf]
    · simp only [hf, decide_false, Bool.false_or]
      revert h
      generalize vs.filterMap V.getW = fm
      intro h
      rcases fm with _ | ⟨k, _ | ⟨k', fm⟩⟩ <;> simp at h <;> subst h <;> simp [V.den]
  · simp only [simpV] at h
    simp only [GateOp.eval, headD_den]
    revert h
    cases vs.headD (V.c false) with
    | c b => intro h; cases h; rfl
    | w k => intro h; cases h

lemma simp_none (W : List Bool) (op : GateOp) (hop : Basic op) (vs : List V)
    (h : simpV op vs = none) :
    op.eval ((emitIns op vs).map (fun i => W.getD i false)) = op.eval (vs.map (V.den W)) := by
  rcases hop with rfl | rfl | rfl
  · simp only [simpV] at h
    simp only [GateOp.eval, all_den, emitIns]
    split_ifs at h with hf
    simp [hf]
  · simp only [simpV] at h
    simp only [GateOp.eval, any_den, emitIns]
    split_ifs at h with hf
    simp [hf]
  · simp only [simpV] at h
    simp only [GateOp.eval, headD_den, emitIns]
    revert h
    cases vs.headD (V.c false) with
    | c b => intro h; cases h
    | w k => intro _; rfl

lemma simp_some_mem (op : GateOp) (vs : List V) (k : ℕ) (h : simpV op vs = some (V.w k)) :
    V.w k ∈ vs := by
  cases op with
  | and =>
    simp only [simpV] at h
    split_ifs at h
    · simp at h
    split at h
    · cases h
    · rename_i k' hk'
      simp only [Option.some.injEq, V.w.injEq] at h
      subst h
      have hj : k' ∈ vs.filterMap V.getW := by rw [hk']; simp
      obtain ⟨a, ha, haj⟩ := List.mem_filterMap.mp hj
      cases a with
      | c => simp [V.getW] at haj
      | w => simp only [V.getW, Option.some.injEq] at haj; subst haj; exact ha
    · cases h
  | or =>
    simp only [simpV] at h
    split_ifs at h
    · simp at h
    split at h
    · cases h
    · rename_i k' hk'
      simp only [Option.some.injEq, V.w.injEq] at h
      subst h
      have hj : k' ∈ vs.filterMap V.getW := by rw [hk']; simp
      obtain ⟨a, ha, haj⟩ := List.mem_filterMap.mp hj
      cases a with
      | c => simp [V.getW] at haj
      | w => simp only [V.getW, Option.some.injEq] at haj; subst haj; exact ha
    · cases h
  | not =>
    simp only [simpV] at h
    revert h
    cases vs.headD (V.c false) with
    | c b => intro h; cases h
    | w k => intro h; cases h
  | mod m => simp [simpV] at h
  | maj => simp [simpV] at h

lemma getD_mem (m : List V) (i : ℕ) (P : V → Prop) (hm : ∀ u ∈ m, P u) (hd : P (V.c false)) :
    P (m.getD i (V.c false)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : m[i]? with
  | none => exact hd
  | some u => exact hm u (List.mem_of_getElem? h)

/-- The invariant of the transformation, for the new circuit run on `x`. -/
structure Inv (n : ℕ) (x : List Bool) (w : List Bool) (st : List V × List Gate) : Prop where
  len : st.1.length = w.length
  den : ∀ i, (st.1.getD i (V.c false)).den (st.2.foldl wstep x) = w.getD i false
  ok : ∀ v ∈ st.1, v.ok (st.2.foldl wstep x).length

lemma inv_step (n : ℕ) (x : List Bool) (hx : x.length = n) (w : List Bool)
    (st : List V × List Gate) (g : Gate) (hg : Basic g.op) (hI : Inv n x w st) :
    Inv n x (wstep w g) (step n st g) := by
  set W := st.2.foldl wstep x with hW
  set vs := g.inputs.map (fun i => st.1.getD i (V.c false)) with hvs
  have hval : g.op.eval (g.inputs.map fun i => w.getD i false) = g.op.eval (vs.map (V.den W)) := by
    congr 1
    rw [hvs, List.map_map]
    exact List.map_congr_left (fun i _ => (hI.den i).symm)
  have hWlen : W.length = n + st.2.length := by
    rw [hW, length_foldl_wstep, hx]
  unfold step
  rw [← hvs]
  cases hs : simpV g.op vs with
  | some v =>
    refine ⟨?_, ?_, ?_⟩
    · simp [wstep, hI.len]
    · intro i
      simp only [wstep, getD_concat, hI.len]
      split_ifs
      · exact hI.den i
      · rw [← hW, simp_some W g.op hg vs v hs, hval]
      · rfl
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hI.ok u hu
      · simp only [List.mem_singleton] at hu
        subst hu
        cases u with
        | c => trivial
        | w k =>
          have hk := simp_some_mem g.op vs k hs
          rw [hvs, List.mem_map] at hk
          obtain ⟨i, _, hi⟩ := hk
          have := getD_mem st.1 i (V.ok W.length) hI.ok trivial
          rw [hi] at this
          exact this
  | none =>
    have hfold : (st.2 ++ [(⟨g.op, emitIns g.op vs⟩ : Gate)]).foldl wstep x =
        W ++ [g.op.eval ((emitIns g.op vs).map fun i => W.getD i false)] := by
      rw [List.foldl_append]; rfl
    refine ⟨?_, ?_, ?_⟩
    · simp [wstep, hI.len]
    · intro i
      simp only [hfold]
      simp only [wstep, getD_concat, hI.len]
      split_ifs with h1 h2
      · rw [den_concat _ _ _ (getD_mem st.1 i (V.ok W.length) hI.ok trivial)]
        exact hI.den i
      · simp only [V.den, getD_concat, hWlen, lt_irrefl, if_false, if_true]
        rw [simp_none W g.op hg vs hs, hval]
      · rfl
    · intro u hu
      rw [hfold, List.length_append, List.length_singleton]
      rcases List.mem_append.mp hu with hu | hu
      · have h3 : (List.foldl wstep x st.2).length = W.length := rfl
        exact ok_mono (by omega) u (hI.ok u hu)
      · simp only [List.mem_singleton] at hu
        subst hu
        have h1 : (List.foldl wstep x st.2).length = n + st.2.length := by
          rw [length_foldl_wstep, hx]
        have h2 := hWlen
        simp only [V.ok]; omega

lemma inv_fold (n : ℕ) (x : List Bool) (hx : x.length = n) (gs : List Gate)
    (hgs : ∀ g ∈ gs, Basic g.op) :
    ∀ (w : List Bool) (st : List V × List Gate), Inv n x w st →
      Inv n x (gs.foldl wstep w) (gs.foldl (step n) st) := by
  induction gs with
  | nil => intro w st h; exact h
  | cons g gs ih =>
    intro w st h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (inv_step n x hx w st g (hgs g List.mem_cons_self) h)

lemma step_len (n : ℕ) (st : List V × List Gate) (g : Gate) :
    (step n st g).2.length ≤ st.2.length + 1 := by
  unfold step
  split <;> simp

lemma step_len_none (n : ℕ) (st : List V × List Gate) (g : Gate)
    (h : (step n st g).2.length = st.2.length + 1) :
    simpV g.op (g.inputs.map (fun i => st.1.getD i (V.c false))) = none := by
  revert h
  unfold step
  split <;> simp_all

lemma fold_len (n : ℕ) (gs : List Gate) :
    ∀ st : List V × List Gate, (gs.foldl (step n) st).2.length ≤ st.2.length + gs.length := by
  induction gs with
  | nil => intro st; simp
  | cons g gs ih =>
    intro st
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (step n st g)
    have h2 := step_len n st g
    omega

/-- Gates of fan-in at most two in the basis AND, OR, NOT. -/
def Good (g : Gate) : Prop := Basic g.op ∧ g.inputs.length ≤ 2

lemma emitIns_len (op : GateOp) (vs : List V) (h : vs.length ≤ 2) : (emitIns op vs).length ≤ 2 := by
  cases op with
  | not =>
    simp only [emitIns]
    split <;> simp
  | _ => exact le_trans (List.length_filterMap_le _ _) h

lemma good_fold (n : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, Good g) :
    ∀ st : List V × List Gate, (∀ g ∈ st.2, Good g) → ∀ g ∈ (gs.foldl (step n) st).2, Good g := by
  induction gs with
  | nil => intro st h; exact h
  | cons g gs ih =>
    intro st h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    have hg := hgs g List.mem_cons_self
    unfold step
    split
    · exact h
    · intro g' hg'
      rcases List.mem_append.mp hg' with hg' | hg'
      · exact h g' hg'
      · simp only [List.mem_singleton] at hg'
        subst hg'
        exact ⟨hg.1, emitIns_len _ _ (by simp [hg.2])⟩

/-- The two runs (input `p` fixed to `true`, resp. `false`) agree so far. -/
def Rel (p : ℕ) (a b : List V × List Gate) : Prop :=
  a.2 = b.2 ∧ a.1.length = b.1.length ∧ a.1.getD p (V.c false) = V.c true ∧
    ∀ i, i ≠ p → a.1.getD i (V.c false) = b.1.getD i (V.c false)

lemma simpV_none_wires (op : GateOp) (hop : op = .and ∨ op = .or) (vs : List V)
    (hlen : vs.length ≤ 2) (h : simpV op vs = none) : ∀ v ∈ vs, ∃ k, v = V.w k := by
  rcases hop with rfl | rfl
  · match vs, hlen with
    | [], _ => simp [simpV] at h
    | [a], _ =>
      cases a with
      | c b => cases b <;> simp [simpV, V.getW, List.filterMap_cons] at h
      | w k => simp [simpV, V.getW, List.filterMap_cons] at h
    | [a, b], _ =>
      cases a with
      | c b1 => cases b1 <;> cases b with
        | c b2 => cases b2 <;> simp [simpV, V.getW, List.filterMap_cons] at h
        | w k => simp [simpV, V.getW, List.filterMap_cons] at h
      | w k1 => cases b with
        | c b2 => cases b2 <;> simp [simpV, V.getW, List.filterMap_cons] at h
        | w k2 => intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  · match vs, hlen with
    | [], _ => simp [simpV] at h
    | [a], _ =>
      cases a with
      | c b => cases b <;> simp [simpV, V.getW, List.filterMap_cons] at h
      | w k => simp [simpV, V.getW, List.filterMap_cons] at h
    | [a, b], _ =>
      cases a with
      | c b1 => cases b1 <;> cases b with
        | c b2 => cases b2 <;> simp [simpV, V.getW, List.filterMap_cons] at h
        | w k => simp [simpV, V.getW, List.filterMap_cons] at h
      | w k1 => cases b with
        | c b2 => cases b2 <;> simp [simpV, V.getW, List.filterMap_cons] at h
        | w k2 => intro v hv; simp at hv; rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩

lemma rel_eq_of_wire (p : ℕ) (a b : List V × List Gate) (hR : Rel p a b) (i k : ℕ)
    (h : a.1.getD i (V.c false) = V.w k) : b.1.getD i (V.c false) = a.1.getD i (V.c false) := by
  have hip : i ≠ p := by
    rintro rfl
    rw [hR.2.2.1] at h
    cases h
  exact (hR.2.2.2 i hip).symm

lemma rel_step (n p : ℕ) (a b : List V × List Gate) (g : Gate) (hg : Good g) (hR : Rel p a b)
    (he : (step n a g).2.length = a.2.length + 1) : Rel p (step n a g) (step n b g) := by
  have hnone := step_len_none n a g he
  set vsa := g.inputs.map (fun i => a.1.getD i (V.c false)) with hvsa
  set vsb := g.inputs.map (fun i => b.1.getD i (V.c false)) with hvsb
  have hsame : simpV g.op vsb = simpV g.op vsa ∧ emitIns g.op vsb = emitIns g.op vsa := by
    rcases hg.1 with hop | hop | hop
    · have hw := simpV_none_wires g.op (Or.inl hop) vsa (by simp [hvsa, hg.2]) hnone
      have : vsb = vsa := by
        rw [hvsa, hvsb]
        refine List.map_congr_left (fun i hi => ?_)
        obtain ⟨k, hk⟩ := hw _ (List.mem_map_of_mem hi)
        exact rel_eq_of_wire p a b hR i k hk
      rw [this]; exact ⟨rfl, rfl⟩
    · have hw := simpV_none_wires g.op (Or.inr hop) vsa (by simp [hvsa, hg.2]) hnone
      have : vsb = vsa := by
        rw [hvsa, hvsb]
        refine List.map_congr_left (fun i hi => ?_)
        obtain ⟨k, hk⟩ := hw _ (List.mem_map_of_mem hi)
        exact rel_eq_of_wire p a b hR i k hk
      rw [this]; exact ⟨rfl, rfl⟩
    · have hhead : vsb.headD (V.c false) = vsa.headD (V.c false) := by
        rw [hvsa, hvsb]
        rw [hop] at hnone
        cases hin : g.inputs with
        | nil => simp [hvsa, hin, simpV] at hnone
        | cons i is =>
          simp only [List.map_cons, List.headD_cons]
          simp only [hvsa, hin, List.map_cons, List.headD_cons, simpV] at hnone
          revert hnone
          cases hk : a.1.getD i (V.c false) with
          | c bb => intro h; cases h
          | w k => intro _; rw [← hk]; exact rel_eq_of_wire p a b hR i k hk
      rw [hop]
      refine ⟨?_, ?_⟩ <;> simp only [simpV, emitIns, hhead]
  have hnoneb : simpV g.op vsb = none := by rw [hsame.1, hnone]
  unfold step
  rw [← hvsa, ← hvsb, hnone, hnoneb, hsame.2]
  obtain ⟨h2, hl, hp, hi⟩ := hR
  have hpl : p < a.1.length := by
    by_contra hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hp
    cases hp
  refine ⟨by simp [h2], by simp [hl], ?_, ?_⟩
  · simp only [getD_concat, if_pos hpl]; exact hp
  · intro i hip
    simp only [getD_concat, hl, h2]
    split_ifs
    · exact hi i hip
    · rfl
    · rfl

lemma rel_fold (n p : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, Good g) :
    ∀ a b : List V × List Gate, Rel p a b →
      (gs.foldl (step n) a).2.length = a.2.length + gs.length →
      Rel p (gs.foldl (step n) a) (gs.foldl (step n) b) := by
  induction gs with
  | nil => intro a b h _; exact h
  | cons g gs ih =>
    intro a b hR he
    simp only [List.foldl_cons, List.length_cons] at he ⊢
    have h1 := fold_len n gs (step n a g)
    have h2 := step_len n a g
    have hs : (step n a g).2.length = a.2.length + 1 := by omega
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (rel_step n p a b g (hgs g List.mem_cons_self) hR hs) (by omega)

/-- The starting map: input `p` is the constant `b`, other inputs stay. -/
def m0 (n : ℕ) (p : Fin n) (b : Bool) : List V :=
  List.ofFn (fun i : Fin n => if i = p then V.c b else V.w i.val)

lemma m0_getD (n : ℕ) (p : Fin n) (b : Bool) (i : ℕ) :
    (m0 n p b).getD i (V.c false) =
      if h : i < n then (if (⟨i, h⟩ : Fin n) = p then V.c b else V.w i) else V.c false := by
  rw [m0, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> simp_all

lemma inv_init (n : ℕ) (p : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (Function.update x p b)) (m0 n p b, []) := by
  refine ⟨by simp [m0], ?_, ?_⟩
  · intro i
    simp only [List.foldl_nil, m0_getD]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases h : i < n
    · simp only [h, dif_pos]
      split_ifs with hp
      · subst hp; simp [V.den]
      · simp only [V.den, Option.getD_some]
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h, Option.getD_some,
          Function.update_of_ne hp]
    · simp [h, V.den]
  · intro v hv
    simp only [m0, List.mem_ofFn, Set.mem_range] at hv
    obtain ⟨i, rfl⟩ := hv
    split_ifs
    · trivial
    · simp [V.ok, i.isLt]

end PEqualNP.Outside.L_meta_199_aux

open PEqualNP.Outside.L_meta_199_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_199 : ∀ (n : ℕ) (p : Fin n) (g : (Fin n → Bool) → Bool) (s : ℕ),
    (∃ x y : Fin n → Bool, g x ≠ g y) →
    (∀ x : Fin n → Bool, g (Function.update x p (!x p)) = g x) →
    PEqualNP.MetaComplexity.HasCircuitSize n (fun x => !x p || g x) (s + 1) →
    PEqualNP.MetaComplexity.HasCircuitSize n g s := by
  intro n p g s ⟨x0, y0, hxy⟩ hind ⟨C, hfan, hsize, hC⟩
  have hgood : ∀ gt ∈ C.gates, Good gt := by
    intro gt hgt
    obtain ⟨hop, hl⟩ := hfan gt hgt
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact hop
  have hbasic : ∀ gt ∈ C.gates, Basic gt.op := fun gt hgt => (hgood gt hgt).1
  have hupd : ∀ (x : Fin n → Bool) (b : Bool), g (Function.update x p b) = g x := by
    intro x b
    by_cases hb : b = x p
    · subst hb; rw [Function.update_eq_self]
    · have : b = !x p := by cases b <;> cases h : x p <;> simp_all
      subst this; exact hind x
  -- the runs with `p` fixed to `b`
  let R : Bool → List V × List Gate := fun b => C.gates.foldl (step n) (m0 n p b, [])
  let val : Bool → V := fun b => (R b).1.getD C.output (V.c false)
  have hden : ∀ (b : Bool) (x : Fin n → Bool),
      (val b).den ((R b).2.foldl wstep (List.ofFn x)) = (!b || g x) := by
    intro b x
    have hI := inv_fold n (List.ofFn x) (by simp) C.gates hbasic _ _ (inv_init n p b x)
    have := hI.den C.output
    rw [← wires_eq] at this
    change (val b).den _ = C.eval _ at this
    rw [this, hC]
    simp [hupd]
  have hnotconst : ¬ ∀ x : Fin n → Bool, g x = true := by
    intro h; exact hxy (by rw [h x0, h y0])
  have hvt : val true ≠ V.c true := by
    intro h
    apply hnotconst
    intro x
    have := hden true x
    rw [h] at this
    simpa [V.den] using this.symm
  have hWlen : ∀ x : Fin n → Bool,
      ((R true).2.foldl wstep (List.ofFn x)).length = n + (R true).2.length := by
    intro x; rw [length_foldl_wstep]; simp
  refine ⟨⟨(R true).2, match val true with | V.w k => k | V.c _ => n + (R true).2.length⟩,
    ?_, ?_, ?_⟩
  · -- fan-in two
    intro gt hgt
    have := good_fold n C.gates hgood (m0 n p true, []) (by simp) gt hgt
    refine ⟨?_, this.2⟩
    rcases this.1 with h | h | h <;> simp [h]
  · -- size
    have hle := fold_len n C.gates (m0 n p true, [])
    simp only [List.length_nil, zero_add] at hle
    have hne : (R true).2.length ≠ C.gates.length := by
      intro he
      have hR := rel_fold n p C.gates hgood (m0 n p true, []) (m0 n p false, [])
        ⟨rfl, by simp [m0], by rw [m0_getD, dif_pos p.isLt]; simp, by
          intro i hip
          simp only [m0_getD]
          split_ifs with h1 h2
          · exact absurd (congrArg Fin.val h2) hip
          · rfl
          · rfl⟩ (by simpa using he)
      apply hnotconst
      intro x
      have ht := hden true x
      have hf := hden false x
      by_cases hop : C.output = p
      · exact absurd (by simp only [val, hop]; exact hR.2.2.1) hvt
      · have hv : val true = val false := hR.2.2.2 _ hop
        change (val true).den ((R true).2.foldl wstep (List.ofFn x)) = _ at ht
        change (val false).den ((R false).2.foldl wstep (List.ofFn x)) = _ at hf
        rw [← hv, ← hR.1] at hf
        rw [ht] at hf
        simpa using hf
    show (R true).2.length ≤ s
    change (R true).2.length ≤ C.gates.length at hle
    have hcs : C.size = C.gates.length := rfl
    omega
  · -- correctness
    intro x
    have ht := hden true x
    simp only [Bool.not_true, Bool.false_or] at ht
    rw [← ht]
    simp only [Circuit.eval, wires_eq]
    revert hvt
    cases val true with
    | w k => intro _; rfl
    | c bb =>
      intro hbb
      cases bb
      · simp only [V.den]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hWlen x])]
        rfl
      · exact absurd rfl hbb
