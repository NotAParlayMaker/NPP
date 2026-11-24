import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2822

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def gv (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def okOp (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def readsAt (i : ℕ) (g : Gate) : Bool :=
  (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).contains i

theorem getD_append_lt {w l : List Bool} {i : ℕ} (h : i < w.length) :
    (w ++ l).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge {w : List Bool} {i : ℕ} (h : w.length ≤ i) : w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem stepW_length (w : List Bool) (g : Gate) : (stepW w g).length = w.length + 1 := by
  simp [stepW]

theorem stepW_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (stepW w g).getD i false =
      if i < w.length then w.getD i false else if i = w.length then gv g w else false := by
  split_ifs with h1 h2
  · exact getD_append_lt h1
  · subst h2
    simp [stepW, gv, List.getD_eq_getElem?_getD]
  · apply getD_ge
    rw [stepW_length]
    omega

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, stepW_length, List.length_cons]
    omega

def AgreeOff (T : ℕ → Prop) (u u' : List Bool) : Prop :=
  u.length = u'.length ∧ ∀ i, ¬ T i → u.getD i false = u'.getD i false

def Ext (w u : List Bool) : Prop :=
  w.length ≤ u.length ∧ ∀ i, i < w.length → u.getD i false = w.getD i false

theorem ext_step {w u : List Bool} (h : Ext w u) (g : Gate) : Ext w (stepW u g) := by
  refine ⟨by rw [stepW_length]; have := h.1; omega, fun i hi => ?_⟩
  rw [stepW_getD, if_pos (by have := h.1; omega)]
  exact h.2 i hi

theorem agree_run (T : ℕ → Prop) (w0 w0' : List Bool) :
    ∀ (gs : List Gate) (u u' : List Bool), AgreeOff T u u' → Ext w0 u → Ext w0' u' →
    (∀ k (hk : k < gs.length), T (u.length + k) ∨
      ∀ a a', AgreeOff T a a' → Ext w0 a → Ext w0' a' → gv gs[k] a = gv gs[k] a') →
    AgreeOff T (gs.foldl stepW u) (gs.foldl stepW u') := by
  intro gs
  induction gs with
  | nil => intro u u' h _ _ _; exact h
  | cons g gs ih =>
    intro u u' hag he he' cond
    apply ih (stepW u g) (stepW u' g) _ (ext_step he g) (ext_step he' g)
    · intro k hk
      have hlen : (stepW u g).length + k = u.length + (k + 1) := by
        rw [stepW_length]; omega
      rw [hlen]
      exact cond (k + 1) (by simp only [List.length_cons]; omega)
    · refine ⟨by rw [stepW_length, stepW_length, hag.1], fun i hi => ?_⟩
      rw [stepW_getD, stepW_getD, ← hag.1]
      split_ifs with h1 h2
      · exact hag.2 i hi
      · subst h2
        rcases cond 0 (by simp) with h | h
        · exact absurd (by simpa using h) hi
        · exact h u u' hag he he'
      · rfl

theorem gv_congr (g : Gate) (hg : okOp g) (a a' : List Bool)
    (h : ∀ i, readsAt i g = true → a.getD i false = a'.getD i false) : gv g a = gv g a' := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, _⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · have hm : ins.map (fun i => a.getD i false) = ins.map (fun i => a'.getD i false) :=
      List.map_congr_left (fun i hi => h i (by simp [readsAt, GateOp.eval, hi]))
    simp only [gv, hm]
  · have hm : ins.map (fun i => a.getD i false) = ins.map (fun i => a'.getD i false) :=
      List.map_congr_left (fun i hi => h i (by simp [readsAt, GateOp.eval, hi]))
    simp only [gv, hm]
  · cases ins with
    | nil => rfl
    | cons i rest =>
      have e := h i (by simp [readsAt, GateOp.eval])
      simp only [List.getD_eq_getElem?_getD] at e
      simp [gv, GateOp.eval, e]

def repVal (u : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr k => u.getD k false

def isC (b : Bool) : Bool ⊕ ℕ → Bool
  | .inl c => c == b
  | .inr _ => false

def rights : List (Bool ⊕ ℕ) → List ℕ
  | [] => []
  | .inl _ :: rs => rights rs
  | .inr k :: rs => k :: rights rs

def simpG (op : GateOp) (rs : List (Bool ⊕ ℕ)) : Option (Bool ⊕ ℕ) :=
  match op with
  | .not =>
    match rs with
    | [] => some (.inl true)
    | .inl b :: _ => some (.inl (!b))
    | .inr _ :: _ => none
  | .and =>
    if rs.any (isC false) then some (.inl false) else
      match rights rs with
      | [] => some (.inl true)
      | [k] => some (.inr k)
      | _ => none
  | .or =>
    if rs.any (isC true) then some (.inl true) else
      match rights rs with
      | [] => some (.inl false)
      | [k] => some (.inr k)
      | _ => none
  | _ => none

def emitG (op : GateOp) (rs : List (Bool ⊕ ℕ)) : Gate :=
  match op with
  | .not => ⟨.not, (rights rs).take 1⟩
  | _ => ⟨op, rights rs⟩

theorem simp_sem (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (u : List Bool) :
    (∀ r, simpG op rs = some r → repVal u r = op.eval (rs.map (repVal u)) ∧
      ∀ k, r = .inr k → Sum.inr k ∈ rs) ∧
    (simpG op rs = none → gv (emitG op rs) u = op.eval (rs.map (repVal u))) := by
  rcases rs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rs⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [simpG, GateOp.eval, repVal, rights]
  · rcases a with (_ | _) | a <;> rcases hop with rfl | rfl | rfl <;>
      simp [simpG, GateOp.eval, repVal, isC, rights, emitG, gv]
  · rcases a with (_ | _) | a <;> rcases b with (_ | _) | b <;> rcases hop with rfl | rfl | rfl <;>
      simp [simpG, GateOp.eval, repVal, isC, rights, emitG, gv]
  · simp at hl

theorem simp_saved_rs (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (b : Bool)
    (hm : (op = .not ∧ rs.head? = some (.inl b)) ∨ (op ≠ .not ∧ Sum.inl b ∈ rs)) :
    (simpG op rs).isSome = true := by
  rcases rs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rs⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp at hm
  · rcases x with (_ | _) | x <;> rcases hop with rfl | rfl | rfl <;> cases b <;>
      simp_all [simpG, isC, rights]
  · rcases x with (_ | _) | x <;> rcases y with (_ | _) | y <;> rcases hop with rfl | rfl | rfl <;>
      cases b <;> simp_all [simpG, isC, rights]
  · simp at hl

theorem simp_saved (g : Gate) (hg : okOp g) (look : ℕ → Bool ⊕ ℕ) (i : ℕ) (b : Bool)
    (hr : readsAt i g = true) (hc : look i = .inl b) :
    (simpG g.op (g.inputs.map look)).isSome = true := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  apply simp_saved_rs op hop _ (by simpa using hl) b
  rcases hop with rfl | rfl | rfl
  · right
    refine ⟨by simp, ?_⟩
    have hi : i ∈ ins := by simpa [readsAt, GateOp.eval] using hr
    rw [← hc]
    exact List.mem_map_of_mem hi
  · right
    refine ⟨by simp, ?_⟩
    have hi : i ∈ ins := by simpa [readsAt, GateOp.eval] using hr
    rw [← hc]
    exact List.mem_map_of_mem hi
  · left
    refine ⟨rfl, ?_⟩
    cases ins with
    | nil => simp [readsAt] at hr
    | cons a rest =>
      have e : i = a := by simpa [readsAt, GateOp.eval] using hr
      subst e
      simp [hc]

theorem simp_const_out (g : Gate) (hg : okOp g) (look : ℕ → Bool ⊕ ℕ) (i : ℕ)
    (hr : readsAt i g = true) (hc : look i = .inl false)
    (hor : g.op = GateOp.or → ∀ a ∈ g.inputs, look a = .inl false) :
    ∃ b, simpG g.op (g.inputs.map look) = some (.inl b) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hl hor
  rcases hop with rfl | rfl | rfl
  · refine ⟨false, ?_⟩
    have hi : i ∈ ins := by simpa [readsAt, GateOp.eval] using hr
    have hany : (ins.map look).any (isC false) = true :=
      List.any_eq_true.mpr ⟨look i, List.mem_map_of_mem hi, by simp [hc, isC]⟩
    simp [simpG, hany]
  · refine ⟨false, ?_⟩
    have hall := hor rfl
    rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, ins⟩⟩⟩
    · simp [readsAt] at hr
    · simp [simpG, hall a (by simp), isC, rights]
    · simp [simpG, hall a (by simp), hall c (by simp), isC, rights]
    · simp at hl
  · refine ⟨true, ?_⟩
    cases ins with
    | nil => simp [readsAt] at hr
    | cons a rest =>
      have e : i = a := by simpa [readsAt, GateOp.eval] using hr
      subst e
      simp [simpG, hc]

theorem rights_length (rs : List (Bool ⊕ ℕ)) : (rights rs).length ≤ rs.length := by
  induction rs with
  | nil => simp [rights]
  | cons r rs ih => rcases r with b | k <;> simp [rights] <;> omega

theorem emit_ok (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) : okOp (emitG op rs) := by
  have hr := rights_length rs
  rcases hop with rfl | rfl | rfl
  · refine ⟨by simp [emitG], ?_⟩
    simp only [emitG]
    omega
  · refine ⟨by simp [emitG], ?_⟩
    simp only [emitG]
    omega
  · refine ⟨by simp [emitG], ?_⟩
    simp only [emitG, List.length_take]
    omega

def lookR (reps : List (Bool ⊕ ℕ)) (i : ℕ) : Bool ⊕ ℕ := reps.getD i (.inl false)

theorem lookR_append_lt {l : List (Bool ⊕ ℕ)} {i : ℕ} (r : Bool ⊕ ℕ) (h : i < l.length) :
    lookR (l ++ [r]) i = lookR l i := by
  simp only [lookR, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem lookR_append_self (l : List (Bool ⊕ ℕ)) (r : Bool ⊕ ℕ) : lookR (l ++ [r]) l.length = r := by
  simp [lookR, List.getD_eq_getElem?_getD]

theorem lookR_ge {l : List (Bool ⊕ ℕ)} {i : ℕ} (h : l.length ≤ i) : lookR l i = .inl false := by
  simp only [lookR, List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

def sStep (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
  match simpG g.op (g.inputs.map (lookR st.1)) with
  | some r => (st.1 ++ [r], st.2)
  | none => (st.1 ++ [.inr (8 + st.2.length)], st.2 ++ [emitG g.op (g.inputs.map (lookR st.1))])

theorem sStep_fst_length (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (sStep st g).1.length = st.1.length + 1 := by
  unfold sStep
  split <;> simp

theorem sStep_look_lt (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (i : ℕ) (h : i < st.1.length) :
    lookR (sStep st g).1 i = lookR st.1 i := by
  unfold sStep
  split <;> exact lookR_append_lt _ h

theorem run_fst_length (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) :
    (gs.foldl sStep st).1.length = st.1.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, sStep_fst_length, List.length_cons]
    omega

theorem run_look_lt (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (i : ℕ)
    (h : i < st.1.length) : lookR (gs.foldl sStep st).1 i = lookR st.1 i := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by rw [sStep_fst_length]; omega), sStep_look_lt _ _ _ h]

def Sim (u0 W : List Bool) (st : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  W.length = st.1.length ∧
  (∀ i, W.getD i false = repVal (st.2.foldl stepW u0) (lookR st.1 i)) ∧
  (∀ i k, lookR st.1 i = .inr k → k < u0.length + st.2.length)

theorem repVal_step (U : List Bool) (e : Gate) (r : Bool ⊕ ℕ)
    (h : ∀ k, r = .inr k → k < U.length) : repVal (stepW U e) r = repVal U r := by
  rcases r with b | k
  · rfl
  · simp only [repVal]
    rw [stepW_getD, if_pos (h k rfl)]

theorem sim_step (u0 W : List Bool) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hg : okOp g)
    (hu : u0.length = 8) (h : Sim u0 W st) : Sim u0 (stepW W g) (sStep st g) := by
  obtain ⟨hlen, hval, hbd⟩ := h
  obtain ⟨hop, hl⟩ := hg
  have hop' : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
  have hUlen : (st.2.foldl stepW u0).length = u0.length + st.2.length := run_length _ _
  have key : gv g W =
      g.op.eval ((g.inputs.map (lookR st.1)).map (repVal (st.2.foldl stepW u0))) := by
    unfold gv
    rw [List.map_map]
    congr 1
    exact List.map_congr_left (fun i _ => hval i)
  have hrsl : (g.inputs.map (lookR st.1)).length ≤ 2 := by rw [List.length_map]; exact hl
  obtain ⟨hsome, hnone⟩ := simp_sem g.op hop' _ hrsl (st.2.foldl stepW u0)
  unfold sStep
  rcases hs : simpG g.op (g.inputs.map (lookR st.1)) with _ | r
  · have e := hnone hs
    dsimp only
    refine ⟨by rw [stepW_length, List.length_append, List.length_singleton, hlen], ?_, ?_⟩
    · intro i
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, stepW_getD]
      split_ifs with h1 h2
      · rw [lookR_append_lt _ (by omega), hval i]
        exact (repVal_step _ _ _ (fun k hk => by rw [hUlen]; exact hbd i k hk)).symm
      · subst h2
        rw [hlen, lookR_append_self]
        simp only [repVal]
        rw [stepW_getD, if_neg (by omega), if_pos (by omega), key, e]
      · rw [lookR_ge (by simp; omega)]
        rfl
    · intro i k hk
      simp only [List.length_append, List.length_singleton]
      by_cases h1 : i < st.1.length
      · rw [lookR_append_lt _ h1] at hk
        have := hbd i k hk
        omega
      · by_cases h2 : i = st.1.length
        · subst h2
          rw [lookR_append_self] at hk
          cases hk
          omega
        · rw [lookR_ge (by simp; omega)] at hk
          cases hk
  · obtain ⟨e, hin⟩ := hsome r hs
    dsimp only
    refine ⟨by rw [stepW_length, List.length_append, List.length_singleton, hlen], ?_, ?_⟩
    · intro i
      rw [stepW_getD]
      split_ifs with h1 h2
      · rw [lookR_append_lt _ (by omega), hval i]
      · subst h2
        rw [hlen, lookR_append_self, e, key]
      · rw [lookR_ge (by simp; omega)]
        rfl
    · intro i k hk
      by_cases h1 : i < st.1.length
      · rw [lookR_append_lt _ h1] at hk
        exact hbd i k hk
      · by_cases h2 : i = st.1.length
        · subst h2
          rw [lookR_append_self] at hk
          subst hk
          obtain ⟨j, _, hjk⟩ := List.mem_map.mp (hin k rfl)
          exact hbd j k hjk
        · rw [lookR_ge (by simp; omega)] at hk
          cases hk

theorem sim_run (u0 : List Bool) (hu : u0.length = 8) :
    ∀ (gs : List Gate) (W : List Bool) (st : List (Bool ⊕ ℕ) × List Gate),
    (∀ g ∈ gs, okOp g) → Sim u0 W st → Sim u0 (gs.foldl stepW W) (gs.foldl sStep st) := by
  intro gs
  induction gs with
  | nil => intro W st _ h; exact h
  | cons g gs ih =>
    intro W st hok h
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (sim_step _ _ _ _ (hok g (by simp)) hu h)

def initReps (v : ℕ) : List (Bool ⊕ ℕ) :=
  (List.range 9).map (fun i => if i < v then .inr i else if i = v then .inl false else .inr (i - 1))

theorem look_init (v i : ℕ) : lookR (initReps v) i =
    if i < 9 then (if i < v then .inr i else if i = v then .inl false else .inr (i - 1))
    else .inl false := by
  unfold lookR initReps
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < 9
  · simp [List.getElem?_range, h]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [h]

theorem sim_init (x : Fin 8 → Bool) (v : ℕ) (hv : v < 9) :
    Sim (List.ofFn x) ((List.ofFn x).insertIdx v false) (initReps v, []) := by
  have hlen8 : (List.ofFn x).length = 8 := List.length_ofFn
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_insertIdx_of_le_length (by omega)]
    simp [initReps, hlen8]
  · intro i
    simp only [List.foldl_nil]
    rw [look_init, List.getD_eq_getElem?_getD, List.getElem?_insertIdx]
    by_cases h9 : i < 9
    · by_cases h1 : i < v
      · simp only [h9, h1, if_true, repVal, List.getD_eq_getElem?_getD]
      · by_cases h2 : i = v
        · subst h2
          have h8 : i ≤ (List.ofFn x).length := by omega
          simp only [lt_irrefl, h8, h9, ite_true, ite_false, ↓reduceIte, Option.getD_some, repVal]
        · simp only [h9, h1, h2, if_true, if_false, repVal, List.getD_eq_getElem?_getD]
    · have h1 : ¬ i < v := by omega
      have h2 : ¬ i = v := by omega
      simp only [h9, h1, h2, if_false, repVal]
      rw [List.getElem?_eq_none (by omega)]
      rfl
  · intro i k hk
    rw [look_init] at hk
    simp only [List.length_nil, Nat.add_zero, hlen8]
    split_ifs at hk <;> cases hk <;> omega

theorem run_out_ok : ∀ (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate),
    (∀ g ∈ gs, okOp g) → (∀ e ∈ st.2, okOp e) → ∀ e ∈ (gs.foldl sStep st).2, okOp e := by
  intro gs
  induction gs with
  | nil => intro st _ h; exact h
  | cons g gs ih =>
    intro st hok hst
    apply ih _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    have hg := hok g (by simp)
    have hop' : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg.1
    unfold sStep
    split
    · exact hst
    · intro e he
      rcases List.mem_append.mp he with h | h
      · exact hst e h
      · rw [List.mem_singleton.mp h]
        exact emit_ok _ hop' _ (by rw [List.length_map]; exact hg.2)

def savedB (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : Bool :=
  (simpG g.op (g.inputs.map (lookR st.1))).isSome

def nsaved : List (Bool ⊕ ℕ) × List Gate → List Gate → ℕ
  | _, [] => 0
  | st, g :: gs => (if savedB st g then 1 else 0) + nsaved (sStep st g) gs

theorem sStep_snd_length (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (sStep st g).2.length + (if savedB st g then 1 else 0) = st.2.length + 1 := by
  unfold sStep savedB
  split <;> simp_all

theorem nsaved_len (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) :
    (gs.foldl sStep st).2.length + nsaved st gs = st.2.length + gs.length := by
  induction gs generalizing st with
  | nil => simp [nsaved]
  | cons g gs ih =>
    have h1 := ih (sStep st g)
    have h2 := sStep_snd_length st g
    simp only [List.foldl_cons, nsaved, List.length_cons] at h1 ⊢
    omega

theorem nsaved_append (A B : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) :
    nsaved st (A ++ B) = nsaved st A + nsaved (A.foldl sStep st) B := by
  induction A generalizing st with
  | nil => simp [nsaved]
  | cons g A ih =>
    simp only [List.cons_append, nsaved, ih, List.foldl_cons]
    omega

theorem nsaved_at (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (k : ℕ)
    (hk : k < gs.length) (h : savedB ((gs.take k).foldl sStep st) gs[k] = true) :
    1 ≤ nsaved st gs := by
  have e : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  rw [e, nsaved_append]
  simp only [nsaved, h, if_true]
  omega

theorem nsaved_two (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (p q : ℕ)
    (hpq : p < q) (hq : q < gs.length)
    (hp' : savedB ((gs.take p).foldl sStep st) (gs[p]'(by omega)) = true)
    (hq' : savedB ((gs.take q).foldl sStep st) gs[q] = true) : 2 ≤ nsaved st gs := by
  have e : gs = gs.take (p + 1) ++ gs.drop (p + 1) := (List.take_append_drop _ _).symm
  rw [e, nsaved_append]
  have h1 : 1 ≤ nsaved st (gs.take (p + 1)) := by
    apply nsaved_at _ _ p (by simp; omega)
    convert hp' using 2
    · rw [List.take_take]
      congr 2
      omega
    · simp
  have h2 : 1 ≤ nsaved ((gs.take (p + 1)).foldl sStep st) (gs.drop (p + 1)) := by
    apply nsaved_at _ _ (q - (p + 1)) (by simp; omega)
    convert hq' using 2
    · rw [← List.foldl_append, ← List.take_add]
      congr 2
      omega
    · simp only [List.getElem_drop]
      congr 1
      omega
  omega

theorem two_elems (l : List ℕ) (hl : l.length ≤ 2) {v a : ℕ} (hv : v ∈ l) (ha : a ∈ l)
    (hne : a ≠ v) : l = [v, a] ∨ l = [a, v] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
  · simp at hv
  · simp at hv ha
    omega
  · simp at hv ha
    rcases hv with rfl | rfl <;> rcases ha with rfl | rfl <;> simp_all
  · simp at hl

theorem main (C : Circuit) (v : Fin 9) (hmin : IsMinimalCircuit 9 C)
    (hcon : ∃ (x y : Fin 8 → Bool), C.eval ((List.ofFn x).insertIdx v.val false) ≠
      C.eval ((List.ofFn y).insertIdx v.val false))
    (hdep : ∀ j : Fin 9, j ≠ v → ∃ x : Fin 8 → Bool,
      C.eval ((List.ofFn x).insertIdx v.val false) ≠ C.eval ((List.ofFn x).insertIdx v.val true) ∧
      ((List.ofFn x).insertIdx v.val false).getD j.val false = true) :
    (∃ D : Circuit, FanInTwo D ∧ D.size + 2 ≤ C.size ∧
      circuitFun 8 D = fun x => C.eval ((List.ofFn x).insertIdx v.val false)) ∨
    ∃ (g : Fin C.size) (w : ℕ), 9 ≤ w ∧ w < 9 + g.val ∧ (C.gates.get g).op = GateOp.or ∧
      ((C.gates.get g).inputs = [v.val, w] ∨ (C.gates.get g).inputs = [w, v.val]) ∧
      ∀ h : Fin C.size, readsAt v.val (C.gates.get h) = true → h = g := by
  classical
  have hok : ∀ g ∈ C.gates, okOp g := hmin.1
  have hv9 : v.val < 9 := v.isLt
  have hj : ∃ j : Fin 9, j ≠ v := by
    by_cases hv0 : v = 0
    · exact ⟨1, by rw [hv0]; decide⟩
    · exact ⟨0, fun e => hv0 e.symm⟩
  obtain ⟨j0, hj0⟩ := hj
  let st0 : List (Bool ⊕ ℕ) × List Gate := (initReps v.val, [])
  let state : ℕ → List (Bool ⊕ ℕ) × List Gate := fun k => (C.gates.take k).foldl sStep st0
  let fin := C.gates.foldl sStep st0
  have hsim : ∀ x : Fin 8 → Bool,
      Sim (List.ofFn x) (C.gates.foldl stepW ((List.ofFn x).insertIdx v.val false)) fin :=
    fun x => sim_run _ (by simp) C.gates _ _ hok (sim_init x v.val hv9)
  have state_len : ∀ k, k ≤ C.gates.length → (state k).1.length = 9 + k := by
    intro k hk
    simp only [state, run_fst_length, List.length_take, st0, initReps, List.length_map,
      List.length_range]
    omega
  have state_full : state C.gates.length = fin := by
    simp only [state, fin, List.take_length]
  have state_succ : ∀ k (hk : k < C.gates.length), state (k + 1) = sStep (state k) C.gates[k] := by
    intro k hk
    simp only [state, List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
  have look_later : ∀ k m, k ≤ m → m ≤ C.gates.length → ∀ i, i < 9 + k →
      lookR (state m).1 i = lookR (state k).1 i := by
    intro k m hkm hm i hi
    have e : m = k + (m - k) := by omega
    have hk : (state k).1.length = 9 + k := state_len k (by omega)
    simp only [state] at hk ⊢
    rw [e, List.take_add, List.foldl_append]
    exact run_look_lt _ _ i (by omega)
  have hv_const : ∀ k, k ≤ C.gates.length → lookR (state k).1 v.val = .inl false := by
    intro k hk
    rw [look_later 0 k (Nat.zero_le _) hk v.val (by omega)]
    simp only [state, List.take_zero, List.foldl_nil, st0]
    rw [look_init]
    simp [hv9]
  have hout : ∃ k, lookR fin.1 C.output = .inr k := by
    rcases hb : lookR fin.1 C.output with b | k
    · exfalso
      obtain ⟨x, y, hxy⟩ := hcon
      apply hxy
      have ex := (hsim x).2.1 C.output
      have ey := (hsim y).2.1 C.output
      rw [hb] at ex ey
      exact ex.trans ey.symm
    · exact ⟨k, rfl⟩
  obtain ⟨kout, hkout⟩ := hout
  have W_len : ∀ (x : Fin 8 → Bool) (b : Bool), ((List.ofFn x).insertIdx v.val b).length = 9 := by
    intro x b
    rw [List.length_insertIdx_of_le_length (by simp; omega)]
    simp
  have ins_agree : ∀ (x : Fin 8 → Bool) (i : ℕ), i ≠ v.val →
      ((List.ofFn x).insertIdx v.val false).getD i false =
        ((List.ofFn x).insertIdx v.val true).getD i false := by
    intro x i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_insertIdx, hi]
  have contra : ∀ (T : ℕ → Prop) (x : Fin 8 → Bool), T v.val →
      (∀ i, T i → ∃ b, lookR fin.1 i = .inl b) →
      C.eval ((List.ofFn x).insertIdx v.val false) ≠ C.eval ((List.ofFn x).insertIdx v.val true) →
      (∀ k (hk : k < C.gates.length), T (9 + k) ∨ ∀ a a', AgreeOff T a a' →
        Ext ((List.ofFn x).insertIdx v.val false) a →
        Ext ((List.ofFn x).insertIdx v.val true) a' → gv C.gates[k] a = gv C.gates[k] a') →
      False := by
    intro T x hTv hT hne cond
    have hA := agree_run T _ _ C.gates ((List.ofFn x).insertIdx v.val false)
      ((List.ofFn x).insertIdx v.val true)
      ⟨by rw [W_len, W_len], fun i hi => ins_agree x i (fun e => hi (by rw [e]; exact hTv))⟩
      ⟨le_rfl, fun _ _ => rfl⟩ ⟨le_rfl, fun _ _ => rfl⟩
      (fun k hk => by rw [W_len]; exact cond k hk)
    have hno : ¬ T C.output := by
      intro ht
      obtain ⟨b, hb⟩ := hT _ ht
      rw [hkout] at hb
      cases hb
    exact hne (hA.2 _ hno)
  have hsaved : ∀ k (hk : k < C.gates.length) (i : ℕ) (b : Bool), readsAt i C.gates[k] = true →
      lookR (state k).1 i = .inl b → savedB (state k) C.gates[k] = true :=
    fun k hk i b hr hc => simp_saved _ (hok _ (by simp)) _ i b hr hc
  have hD : circuitFun 8 ⟨fin.2, kout⟩ = fun x => C.eval ((List.ofFn x).insertIdx v.val false) := by
    funext x
    have e := (hsim x).2.1 C.output
    rw [hkout] at e
    exact e.symm
  have hDfan : FanInTwo ⟨fin.2, kout⟩ :=
    fun e he => run_out_ok C.gates st0 hok (by simp [st0]) e he
  have hcount : fin.2.length + nsaved st0 C.gates = st0.2.length + C.gates.length :=
    nsaved_len C.gates st0
  suffices key : 2 ≤ nsaved st0 C.gates ∨
      ∃ (g : Fin C.size) (w : ℕ), 9 ≤ w ∧ w < 9 + g.val ∧ (C.gates.get g).op = GateOp.or ∧
        ((C.gates.get g).inputs = [v.val, w] ∨ (C.gates.get g).inputs = [w, v.val]) ∧
        ∀ h : Fin C.size, readsAt v.val (C.gates.get h) = true → h = g by
    rcases key with h | h
    · left
      refine ⟨⟨fin.2, kout⟩, hDfan, ?_, hD⟩
      have h0 : st0.2.length = 0 := rfl
      show fin.2.length + 2 ≤ C.gates.length
      omega
    · right
      exact h
  by_cases two : ∃ p q : Fin C.gates.length, p < q ∧ readsAt v.val (C.gates.get p) = true ∧
      readsAt v.val (C.gates.get q) = true
  · obtain ⟨p, q, hpq, rp, rq⟩ := two
    left
    exact nsaved_two C.gates st0 p.val q.val hpq q.isLt
      (hsaved p.val p.isLt v.val false rp (hv_const _ p.isLt.le))
      (hsaved q.val q.isLt v.val false rq (hv_const _ q.isLt.le))
  push_neg at two
  by_cases some_reader : ∃ g : Fin C.gates.length, readsAt v.val (C.gates.get g) = true
  swap
  · push_neg at some_reader
    exfalso
    obtain ⟨x, hx, _⟩ := hdep j0 hj0
    refine contra (fun i => i = v.val) x rfl
      (fun i hi => ⟨false, by rw [hi, ← state_full]; exact hv_const _ le_rfl⟩) hx ?_
    intro k hk
    right
    intro a1 a1' hag _ _
    apply gv_congr _ (hok _ (by simp))
    intro i hi
    apply hag.2 i
    intro e
    rw [e] at hi
    exact some_reader ⟨k, hk⟩ hi
  obtain ⟨g, rg⟩ := some_reader
  have uniq : ∀ h : Fin C.gates.length, readsAt v.val (C.gates.get h) = true → h = g := by
    intro h rh
    rcases lt_trichotomy h g with l | e | l
    · exact absurd rg (two h g l rh)
    · exact e
    · exact absurd rh (two g h l rg)
  have hokg : okOp C.gates[g.val] := hok _ (by simp)
  by_cases pairG : ∃ a, a < 9 + g.val ∧ a ≠ v.val ∧ (C.gates.get g).op = GateOp.or ∧
      ((C.gates.get g).inputs = [v.val, a] ∨ (C.gates.get g).inputs = [a, v.val])
  · obtain ⟨a, al, av, hop, hin⟩ := pairG
    by_cases a9 : 9 ≤ a
    · right
      exact ⟨g, a, a9, al, hop, hin, uniq⟩
    · exfalso
      obtain ⟨x, hx, hxj⟩ := hdep ⟨a, by omega⟩ (fun e => av (congrArg Fin.val e))
      refine contra (fun i => i = v.val) x rfl
        (fun i hi => ⟨false, by rw [hi, ← state_full]; exact hv_const _ le_rfl⟩) hx ?_
      intro k hk
      right
      intro a1 a1' hag he he'
      by_cases kg : k = g.val
      · subst kg
        have t1 : a1.getD a false = true := by
          rw [he.2 a (by rw [W_len]; omega)]
          exact hxj
        have t2 : a1'.getD a false = true := by
          rw [he'.2 a (by rw [W_len]; omega), ← ins_agree x a av]
          exact hxj
        have hop' : C.gates[g.val].op = GateOp.or := hop
        have hin' : C.gates[g.val].inputs = [v.val, a] ∨ C.gates[g.val].inputs = [a, v.val] := hin
        simp only [List.getD_eq_getElem?_getD] at t1 t2
        unfold gv
        rw [hop']
        rcases hin' with h' | h' <;> rw [h'] <;> simp [GateOp.eval, t1, t2]
      · apply gv_congr _ (hok _ (by simp))
        intro i hi
        apply hag.2 i
        intro e
        rw [e] at hi
        exact kg (congrArg Fin.val (uniq ⟨k, hk⟩ hi))
  push_neg at pairG
  have allF : C.gates[g.val].op = GateOp.or →
      ∀ a ∈ C.gates[g.val].inputs, lookR (state g.val).1 a = .inl false := by
    intro hop a ha
    by_cases e : a = v.val
    · rw [e]
      exact hv_const _ g.isLt.le
    · by_cases big : 9 + g.val ≤ a
      · exact lookR_ge (by rw [state_len _ g.isLt.le]; exact big)
      · exfalso
        have hv_in : v.val ∈ C.gates[g.val].inputs := by
          have r := rg
          simp only [List.get_eq_getElem] at r
          simpa [readsAt, hop, GateOp.eval] using r
        rcases two_elems _ hokg.2 hv_in ha e with h' | h'
        · exact (pairG a (by omega) e hop).1 h'
        · exact (pairG a (by omega) e hop).2 h'
  obtain ⟨b, hb⟩ := simp_const_out C.gates[g.val] hokg (lookR (state g.val).1) v.val rg
    (hv_const _ g.isLt.le) allF
  have g_saved : savedB (state g.val) C.gates[g.val] = true := by
    unfold savedB
    rw [hb]
    rfl
  have rep_g : ∀ m, g.val < m → m ≤ C.gates.length →
      lookR (state m).1 (9 + g.val) = .inl b := by
    intro m hm hml
    rw [look_later (g.val + 1) m hm hml (9 + g.val) (by omega), state_succ g.val g.isLt]
    unfold sStep
    rw [hb]
    dsimp only
    rw [← state_len g.val g.isLt.le, lookR_append_self]
  by_cases other : ∃ h : Fin C.gates.length, h ≠ g ∧ readsAt (9 + g.val) (C.gates.get h) = true
  · obtain ⟨h, hg, rh⟩ := other
    left
    rcases lt_or_gt_of_ne hg with lt | gt
    · have lt' : h.val < g.val := lt
      have hs : savedB (state h.val) C.gates[h.val] = true :=
        hsaved h.val h.isLt (9 + g.val) false rh
          (lookR_ge (by rw [state_len _ h.isLt.le]; omega))
      exact nsaved_two C.gates st0 h.val g.val lt' g.isLt hs g_saved
    · have gt' : g.val < h.val := gt
      have hs : savedB (state h.val) C.gates[h.val] = true :=
        hsaved h.val h.isLt (9 + g.val) b rh (rep_g h.val gt' h.isLt.le)
      exact nsaved_two C.gates st0 g.val h.val gt' h.isLt g_saved hs
  push_neg at other
  exfalso
  obtain ⟨x, hx, _⟩ := hdep j0 hj0
  refine contra (fun i => i = v.val ∨ i = 9 + g.val) x (Or.inl rfl) ?_ hx ?_
  · rintro i (hi | hi)
    · exact ⟨false, by rw [hi, ← state_full]; exact hv_const _ le_rfl⟩
    · exact ⟨b, by rw [hi, ← state_full]; exact rep_g _ g.isLt le_rfl⟩
  · intro k hk
    by_cases kg : k = g.val
    · exact Or.inl (Or.inr (by omega))
    · right
      intro a1 a1' hag _ _
      apply gv_congr _ (hok _ (by simp))
      intro i hi
      apply hag.2 i
      rintro (e | e)
      · rw [e] at hi
        exact kg (congrArg Fin.val (uniq ⟨k, hk⟩ hi))
      · rw [e] at hi
        exact other ⟨k, hk⟩ (fun h' => kg (congrArg Fin.val h')) hi

end PEqualNP.Outside.L_meta_2822

theorem PEqualNP.Outside.L_meta_2822 : have x1 : Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Gate) => (if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs).contains ↑x1; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x2 →     have x5 : Bool → (Fin (8 : ℕ) → Bool) → Bool := fun (x5 : Bool) (x6 : Fin (8 : ℕ) → Bool) => x2.eval ((List.ofFn x6).insertIdx (↑x3) x5);     (∃ (x6 : Fin (8 : ℕ) → Bool) (x7 : Fin (8 : ℕ) → Bool), x5 Bool.false x6 ≠ x5 Bool.false x7) → (∀ (x7 : Fin (9 : ℕ)), x7 ≠ x3 → ∃ (x9 : Fin (8 : ℕ) → Bool), x5 Bool.false x9 ≠ x5 Bool.true x9 ∧ ((List.ofFn x9).insertIdx (↑x3) Bool.false).getD (↑x7) Bool.false = Bool.true) → (∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (2 : ℕ) ≤ x2.size ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x8 = x5 Bool.false) ∨ ∃ (x8 : Fin x2.size) (x9 : ℕ), (9 : ℕ) ≤ x9 ∧ x9 < (9 : ℕ) + ↑x8 ∧ (x2.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ((x2.gates.get x8).inputs = [↑x3, x9] ∨ (x2.gates.get x8).inputs = [x9, ↑x3]) ∧ ∀ (x10 : Fin x2.size), x1 x3 (x2.gates.get x10) = Bool.true → x10 = x8 := by
  dsimp only
  exact PEqualNP.Outside.L_meta_2822.main
