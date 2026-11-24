import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3700_aux

namespace LMeta616

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < m

lemma statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hk => lt_of_lt_of_le hk h

lemma statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s → statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr k, hk => getD_append_left_lt w t k hk

def simpMono (op : GateOp) (m : ℕ) (ins : List Stat) : Stat × Option Gate :=
  match op with
  | GateOp.and =>
    match ins with
    | [] => (Sum.inl true, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl false, _ => (Sum.inl false, none)
      | _, Sum.inl false => (Sum.inl false, none)
      | Sum.inl true, s => (s, none)
      | s, Sum.inl true => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.and, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | GateOp.or =>
    match ins with
    | [] => (Sum.inl false, none)
    | [s] => (s, none)
    | [s1, s2] =>
      match s1, s2 with
      | Sum.inl true, _ => (Sum.inl true, none)
      | _, Sum.inl true => (Sum.inl true, none)
      | Sum.inl false, s => (s, none)
      | s, Sum.inl false => (s, none)
      | Sum.inr a, Sum.inr b => (Sum.inr m, some ⟨GateOp.or, [a, b]⟩)
    | _ => (Sum.inl false, none)
  | _ => (Sum.inl false, none)

lemma simpMono_ok (op : GateOp) (m : ℕ) (ins : List Stat)
    (hins : ∀ s ∈ ins, statValid m s) :
    let res := simpMono op m ins
    statValid (m + res.2.toList.length) res.1 ∧
    ∀ g, res.2 = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  cases op with
  | and =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · simp [simpMono, statValid]
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
        | inr b =>
          simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | or =>
    rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statValid]
    · refine ⟨by simpa [simpMono] using hins s1 (by simp), fun _ h => by simp [simpMono] at h⟩
    · cases s1 with
      | inl b1 =>
        cases b1
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr b => refine ⟨by simpa [simpMono] using hins (Sum.inr b) (by simp), fun _ h => by simp [simpMono] at h⟩
        · cases s2 with
          | inl b2 => cases b2 <;> simp [simpMono, statValid]
          | inr _ => simp [simpMono, statValid]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2
          · refine ⟨by simpa [simpMono] using hins (Sum.inr a) (by simp), fun _ h => by simp [simpMono] at h⟩
          · simp [simpMono, statValid]
        | inr b =>
          simp [simpMono, statValid]
    · simp [simpMono, statValid]
  | not => simp [simpMono, statValid]
  | mod _ => simp [simpMono, statValid]
  | maj => simp [simpMono, statValid]

lemma simpMono_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2) :
    let res := simpMono op w.length ins
    statVal (res.2.toList.foldl step w) res.1 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval] | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step, statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen
  · rcases ins with _ | ⟨s1, _ | ⟨s2, _ | _⟩⟩
    · simp [simpMono, statVal, GateOp.eval]
    · simp [simpMono, statVal, GateOp.eval]
    · cases s1 with
      | inl b1 =>
        cases b1 <;> cases s2 with | inl b2 => cases b2 <;> simp [simpMono, statVal, GateOp.eval] | inr _ => simp [simpMono, statVal, GateOp.eval]
      | inr a =>
        cases s2 with
        | inl b2 =>
          cases b2 <;> simp [simpMono, statVal, GateOp.eval]
        | inr b =>
          simp only [simpMono, Option.toList_some, List.foldl_cons, List.foldl_nil, step, statVal, getD_append_self, GateOp.eval, List.map_cons, List.map_nil]
    · simp at hlen

end LMeta616

namespace BypassTheory

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hk, hm⟩ => absurd hm (hno k hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

end BypassTheory

namespace WireTheory

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma ite_true_iff (c : Prop) [Decidable c] (b : Bool) :
    (if c then b else false) = true ↔ c ∧ b = true := by
  by_cases h : c <;> simp [h]

lemma W_and_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) :
    W n C x (n + k) = true ↔ ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
  constructor
  · intro h w hw
    exact (ite_true_iff _ _).mp (h _ ⟨w, hw, rfl⟩)
  · rintro h b ⟨w, hw, rfl⟩
    exact (ite_true_iff _ _).mpr (h w hw)

lemma W_or_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) :
    W n C x (n + k) = true ↔ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ W n C x w = true := by
  rw [W_gate n C x k hk, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨b, ⟨w, hw, rfl⟩, h⟩
    exact ⟨w, hw, (ite_true_iff _ _).mp h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (ite_true_iff _ _).mpr h⟩

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i hi
    obtain ⟨w, _, hn, hlt, h⟩ := (inCone_iff n C i k hk).mp hi
    rcases h with h | h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

lemma gate_mono2 (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length ≤ 2 := by
  have hg := hM (C.gates[k]) (List.getElem_mem hk)
  rw [← gateAt_eq C k hk] at hg
  have h1 := hg.1
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact ⟨h1, hg.2⟩

def Reach (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P t.val →
    (∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ a ∈ (gateAt C k).inputs, a < n + k → P a → P (n + k)) → P w

lemma reach_refl (n : ℕ) (C : Circuit) (t : Fin n) : Reach n C t t.val := fun _ h _ => h

lemma reach_step (n : ℕ) (C : Circuit) (t : Fin n) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a : ℕ) (ha : a ∈ (gateAt C k).inputs)
    (hlt : a < n + k) (h : Reach n C t a) : Reach n C t (n + k) :=
  fun P h0 hs => hs k hk hop a ha hlt (h P h0 hs)

lemma reach_inv (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (h : Reach n C t w) :
    w = t.val ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
      ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a := by
  have h2 := h (fun w => Reach n C t w ∧ (w = t.val ∨ ∃ k, k < C.gates.length ∧ w = n + k ∧
      (gateAt C k).op = GateOp.or ∧ ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a))
    ⟨reach_refl n C t, Or.inl rfl⟩
    (fun k hk hop a ha hlt ih => ⟨reach_step n C t k hk hop a ha hlt ih.1,
      Or.inr ⟨k, hk, rfl, hop, a, ha, hlt, ih.1⟩⟩)
  exact h2.2

lemma reach_val (n : ℕ) (C : Circuit) (t : Fin n) (w : ℕ) (y : Fin n → Bool)
    (hy : y t = true) (h : Reach n C t w) : W n C y w = true :=
  h (fun w => W n C y w = true) (by rw [W_input n C y t.val t.isLt]; exact hy)
    (fun k hk hop a ha hlt ih => (W_or_iff n C y k hk hop).mpr ⟨a, ha, hlt, ih⟩)

open PEqualNP.EdgeOwnership in
lemma descent (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x : Fin n → Bool) :
    ∀ k, k < C.gates.length → W n C x (n + k) = true →
      (gateAt C k).op = GateOp.and ∨
      (∃ i, InCone n C i k ∧ (gateAt C i).op = GateOp.and ∧ W n C x (n + i) = true) ∨
      (∃ u : Fin n, x u = true ∧ Reach n C u (n + k)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hx
    rcases (gate_mono2 C hM k hk).1 with hop | hop
    · exact Or.inl hop
    · obtain ⟨w, hw, hlt, hwx⟩ := (W_or_iff n C x k hk hop).mp hx
      by_cases hwn : w < n
      · right; right
        refine ⟨⟨w, hwn⟩, ?_, ?_⟩
        · rw [← W_input n C x w hwn]; exact hwx
        · exact reach_step n C ⟨w, hwn⟩ k hk hop w hw hlt (reach_refl n C ⟨w, hwn⟩)
      · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        have he : n + k' - n = k' := by omega
        rcases ih k' (by omega) (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨u, hu, hdom⟩
        · right; left
          exact ⟨k', (inCone_iff n C k' k hk).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩,
            h, hwx⟩
        · right; left
          exact ⟨i, (inCone_iff n C i k hk).mpr
            ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩, hia, hix⟩
        · right; right
          exact ⟨u, hu, reach_step n C u k hk hop (n + k') hw hlt hdom⟩

open PEqualNP.EdgeOwnership in
lemma owns_reach (n : ℕ) (C : Circuit) (hM : Monotone2 C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (p q : Fin n) (ho : Owns n C j p q) :
    ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ (Reach n C p w ∨ Reach n C q w) := by
  obtain ⟨_, _, hval, hno⟩ := ho
  intro w hw
  have hval' : W n C (pairInput p q) (n + j) = true := hval
  obtain ⟨hlt, hwx⟩ := (W_and_iff n C _ j hj hop).mp hval' w hw
  refine ⟨hlt, ?_⟩
  by_cases hwn : w < n
  · rw [W_input n C _ w hwn] at hwx
    have h' : (⟨w, hwn⟩ : Fin n) = p ∨ (⟨w, hwn⟩ : Fin n) = q := of_decide_eq_true hwx
    rcases h' with h | h
    · left
      rw [← h]; exact reach_refl n C ⟨w, hwn⟩
    · right
      rw [← h]; exact reach_refl n C ⟨w, hwn⟩
  · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
    have he : n + k' - n = k' := by omega
    have hk'j : k' < j := by omega
    have hc : InCone n C k' j :=
      (inCone_iff n C k' j hj).mpr ⟨n + k', hw, by omega, hlt, Or.inl (by omega)⟩
    rcases descent n C hM (pairInput p q) k' (by omega) hwx with h | ⟨i, hi, hia, hix⟩ | ⟨t, ht, hdom⟩
    · have hf : W n C (pairInput p q) (n + k') = false := hno k' hk'j hc h
      rw [hwx] at hf
      exact absurd hf (by simp)
    · have hc2 : InCone n C i j := (inCone_iff n C i j hj).mpr
        ⟨n + k', hw, by omega, hlt, Or.inr (by rw [he]; exact hi)⟩
      have hij := inCone_lt n C j hj i hc2
      have hf : W n C (pairInput p q) (n + i) = false := hno i hij hc2 hia
      rw [hix] at hf
      exact absurd hf (by simp)
    · have h' : t = p ∨ t = q := of_decide_eq_true ht
      rcases h' with h | h
      · left; rw [← h]; exact hdom
      · right; rw [← h]; exact hdom

noncomputable def R (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun t => Reach n C t w)

lemma mem_R (n : ℕ) (C : Circuit) (w : ℕ) (t : Fin n) : t ∈ R n C w ↔ Reach n C t w := by
  unfold R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma R_card_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) : (R n C w).card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
  have h1 : w = a.val := by
    rcases reach_inv n C a w ((mem_R n C w a).mp ha) with h | ⟨k, _, h, _⟩
    · exact h
    · omega
  have h2 : w = b.val := by
    rcases reach_inv n C b w ((mem_R n C w b).mp hb) with h | ⟨k, _, h, _⟩
    · exact h
    · omega
  exact Fin.ext (h1.symm.trans h2)

lemma R_gate (n : ℕ) (C : Circuit) (k : ℕ) (t : Fin n) (ht : t ∈ R n C (n + k)) :
    k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ a ∈ (gateAt C k).inputs, a < n + k ∧ Reach n C t a := by
  rcases reach_inv n C t (n + k) ((mem_R n C (n + k) t).mp ht) with h | ⟨k', hk', h, hop, hex⟩
  · have := t.isLt
    omega
  · have hkk : k = k' := by omega
    rw [hkk]
    exact ⟨hk', hop, hex⟩

noncomputable def cw (n : ℕ) (C : Circuit) (j : ℕ) : ℕ :=
  if (R n C ((gateAt C j).inputs.getD 0 0)).card ≤ 1 then (gateAt C j).inputs.getD 0 0
  else (gateAt C j).inputs.getD 1 0

noncomputable def lw (n : ℕ) (C : Circuit) (j : ℕ) : ℕ :=
  if (R n C ((gateAt C j).inputs.getD 0 0)).card ≤ 1 then (gateAt C j).inputs.getD 1 0
  else (gateAt C j).inputs.getD 0 0

end WireTheory

namespace Prune3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open LMeta616

structure Prefix where
  wire : ℕ → Stat
  gates : List Gate

def emitted (n g j : ℕ) (C : Circuit) (p : Prefix) : Stat × Option Gate :=
  if j = g then (.inl false, none)
  else simpMono (gateAt C j).op (n + p.gates.length) ((gateAt C j).inputs.map p.wire)

def build (n g : ℕ) (C : Circuit) : ℕ → Prefix
  | 0 => ⟨fun w => if w < n then .inr w else .inl false, []⟩
  | j+1 =>
    let p := build n g C j
    let res := emitted n g j C p
    ⟨Function.update p.wire (n+j) res.1, p.gates ++ res.2.toList⟩

lemma inputs_two {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a,b] := by
  have h : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD,hj]
  exact List.length_eq_two.mp (ao.2.2 _ (h ▸ List.getElem_mem hj))

lemma masked (n g : ℕ) (C : Circuit) (j : ℕ) (h : g < j) :
    (build n g C j).wire (n+g) = .inl false := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases e : g = j
    · subst j; simp [build,emitted]
    · have ne : n+g ≠ n+j := by omega
      simpa only [build, Function.update_of_ne ne] using ih (by omega)

lemma no_gate_with_false (op : GateOp) (m : ℕ) (a b : Stat) (h : a = .inl false ∨ b = .inl false) :
    (simpMono op m [a,b]).2 = none := by
  rcases h with rfl | rfl
  · cases b with
    | inl x => cases x <;> cases op <;> rfl
    | inr w => cases op <;> rfl
  · cases a with
    | inl x => cases x <;> cases op <;> rfl
    | inr w => cases op <;> rfl

def charged (n g : ℕ) (C : Circuit) (j : ℕ) : Prop := j = g ∨ n+g ∈ (gateAt C j).inputs
instance (n g : ℕ) (C : Circuit) (j : ℕ) : Decidable (charged n g C j) := by unfold charged; infer_instance

lemma no_emit {n g j : ℕ} {C : Circuit} (ao : IsAO2 n C) (hj : j < C.gates.length)
    (charge : charged n g C j) : (emitted n g j C (build n g C j)).2 = none := by
  by_cases e : j = g
  · simp [emitted,e]
  obtain h | mem := charge
  · contradiction
  have lt := ao.2.1 j hj (n+g) mem
  obtain ⟨a,b,inputs⟩ := inputs_two ao hj
  simp only [emitted,e,ite_false,inputs,List.map_cons,List.map_nil]
  apply no_gate_with_false
  simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with eq | eq
  · exact Or.inl (eq ▸ masked n g C j (by omega))
  · exact Or.inr (eq ▸ masked n g C j (by omega))

lemma gate_budget {n g : ℕ} {C : Circuit} (ao : IsAO2 n C) (j : ℕ) (hj : j ≤ C.gates.length) :
    (build n g C j).gates.length + ((Finset.range j).filter (charged n g C)).card ≤ j := by
  induction j with
  | zero => simp [build]
  | succ j ih =>
    have prev := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    have fresh : j ∉ (Finset.range j).filter (charged n g C) := by simp
    by_cases h : charged n g C j
    · simp only [h,ite_true,Finset.card_insert_of_notMem fresh,build,no_emit ao (by omega) h,
        Option.toList_none,List.append_nil]
      omega
    · simp only [h,ite_false,build,List.length_append]
      cases he : (emitted n g j C (build n g C j)).2 <;> simp <;> omega

lemma emitted_shape {op : GateOp} {m : ℕ} {a b : Stat} {d : Gate}
    (e : (simpMono op m [a,b]).2 = some d) :
    ∃ i j, a = .inr i ∧ b = .inr j ∧ d = ⟨op,[i,j]⟩ ∧ (op = .and ∨ op = .or) := by
  cases op <;> cases a with
  | inl x => cases x <;> cases b with
    | inl y => cases y <;> simp [simpMono] at e
    | inr j => simp [simpMono] at e
  | inr i => cases b with
    | inl y => cases y <;> simp [simpMono] at e
    | inr j => simp [simpMono] at e <;> subst d <;> simp

lemma append_ao {n : ℕ} {gs : List Gate} {d : Gate} (ok : IsAO2 n ⟨gs,0⟩)
    (op : d.op = .and ∨ d.op = .or) (len : d.inputs.length = 2)
    (reads : ∀ w ∈ d.inputs, w < n+gs.length) : IsAO2 n ⟨gs++[d],0⟩ := by
  refine ⟨?_,?_,?_⟩
  · intro v hv
    change v ∈ gs++[d] at hv
    simp only [List.mem_append,List.mem_singleton] at hv
    exact hv.elim (fun h => ok.1 v h) (fun h => h ▸ op)
  · intro k hk w hw
    by_cases old : k < gs.length
    · have eq : gateAt ⟨gs++[d],0⟩ k = gateAt ⟨gs,0⟩ k := List.getD_append _ _ _ _ old
      exact ok.2.1 k old w (eq ▸ hw)
    · change k < (gs++[d]).length at hk
      simp at hk
      have eq : k = gs.length := by omega
      subst k
      apply reads w
      simpa [gateAt] using hw
  · intro v hv
    change v ∈ gs++[d] at hv
    simp only [List.mem_append,List.mem_singleton] at hv
    exact hv.elim (fun h => ok.2.2 v h) (fun h => h ▸ len)

lemma valid_build {n g : ℕ} {C : Circuit} (ao : IsAO2 n C) (j : ℕ) (hj : j ≤ C.gates.length) :
    let p := build n g C j
    IsAO2 n ⟨p.gates,0⟩ ∧ ∀ w, statValid (n+p.gates.length) (p.wire w) := by
  induction j with
  | zero =>
    refine ⟨⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly,build],by simp [ReadsBack, build],by simp [build]⟩,?_⟩
    intro w
    by_cases h : w < n <;> simp [build,h,statValid]
  | succ j ih =>
    obtain ⟨ok,valid⟩ := ih (by omega)
    let p := build n g C j
    let res := emitted n g j C p
    have shape (d : Gate) (e : res.2 = some d) : IsAO2 n ⟨p.gates++[d],0⟩ := by
      by_cases h : j = g
      · simp [res,emitted,h] at e
      obtain ⟨a,b,habs⟩ := inputs_two ao (show j < C.gates.length by omega)
      have ed : (simpMono (gateAt C j).op (n+p.gates.length) [p.wire a,p.wire b]).2 = some d := by
        simpa [res,emitted,h,habs] using e
      obtain ⟨i,k,ea,eb,rfl,op⟩ := emitted_shape ed
      apply append_ao (d := ⟨(gateAt C j).op,[i,k]⟩) ok op rfl
      intro w hw
      have va := valid a
      have vb := valid b
      change statValid _ (p.wire a) at va
      change statValid _ (p.wire b) at vb
      rw [ea] at va
      rw [eb] at vb
      rcases List.mem_cons.mp hw with rfl | mem
      · exact va
      · exact (List.mem_singleton.mp mem) ▸ vb
    have vr : statValid (n+p.gates.length+res.2.toList.length) res.1 := by
      by_cases e : j = g
      · simp [res,emitted,e,statValid]
      · simp only [res,emitted,e,ite_false]
        exact (simpMono_ok _ _ _ (by rintro s hs; obtain ⟨t,_,rfl⟩ := List.mem_map.mp hs; exact valid t)).1
    constructor
    · change IsAO2 n ⟨p.gates ++ res.2.toList,0⟩
      cases h : res.2 with
      | none => simpa using ok
      | some d => simpa using shape d h
    · intro w
      change statValid (n+(p.gates ++ res.2.toList).length) (Function.update p.wire (n+j) res.1 w)
      rw [List.length_append, ←Nat.add_assoc]
      by_cases e : w = n+j
      · simpa [e] using vr
      · rw [Function.update_of_ne e]
        exact statValid_mono (Nat.le_add_right (n+p.gates.length) _) _ (valid w)

def cutValue (n g : ℕ) (C : Circuit) (x : Fin n → Bool) : ℕ → ℕ → Bool
  | 0 => fun w => (List.ofFn x).getD w false
  | j+1 =>
    let v := cutValue n g C x j
    Function.update v (n+j) (if j=g then false else (gateAt C j).op.eval ((gateAt C j).inputs.map v))

lemma sound_build {n g : ℕ} {C : Circuit} (ao : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j ≤ C.gates.length) (w : ℕ) :
    let p := build n g C j
    statVal (p.gates.foldl step (List.ofFn x)) (p.wire w) = cutValue n g C x j w := by
  induction j generalizing w with
  | zero =>
    by_cases h : w < n
    · simp [build,cutValue,h,statVal]
    · simp [build,cutValue,h,statVal,List.getD_eq_getElem?_getD]
  | succ j ih =>
    let p := build n g C j
    let res := emitted n g j C p
    let vals := p.gates.foldl step (List.ofFn x)
    have len : vals.length = n+p.gates.length := by simp [vals,foldl_step_len]
    have valid (t : ℕ) : statValid vals.length (p.wire t) := len ▸ (valid_build (g := g) ao j (by omega)).2 t
    change statVal ((p.gates ++ res.2.toList).foldl step (List.ofFn x)) (Function.update p.wire (n+j) res.1 w) = _
    rw [List.foldl_append]
    change statVal (res.2.toList.foldl step vals) _ = cutValue n g C x (j+1) w
    simp only [cutValue]
    by_cases e : w = n+j
    · subst w
      rw [Function.update_self,Function.update_self]
      by_cases cut : j=g
      · simp [res,emitted,cut,statVal]
      have hj' : j < C.gates.length := by omega
      have mem : gateAt C j ∈ C.gates := by
        have e : gateAt C j = C.gates[j] := by simp [gateAt,List.getD_eq_getElem?_getD,hj']
        exact e ▸ List.getElem_mem hj'
      have sound := simpMono_sound (gateAt C j).op (ao.1 _ mem) vals ((gateAt C j).inputs.map p.wire)
        (by rw [List.length_map,ao.2.2 _ mem])
      simp only [res,emitted,cut,ite_false,← len]
      rw [sound,List.map_map]
      congr 1
      apply List.map_congr_left
      intro t _
      exact ih (by omega) t
    · rw [Function.update_of_ne e,Function.update_of_ne e]
      have keep : statVal (res.2.toList.foldl step vals) (p.wire w) = statVal vals (p.wire w) := by
        cases h : res.2 with
        | none => rfl
        | some d => exact statVal_append vals _ (p.wire w) (valid w)
      exact keep.trans (ih (by omega) w)

end Prune3700

namespace Exchange3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Core PEqualNP.TopForm PEqualNP.EdgeOwnership

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma or_above_implicant {j : ℕ} {b : Fin 2}
    (fixed : IsLiftFixedPoint G C) (live : InOutputCone n C j)
    (op : (gateAt C j).op = GateOp.or) (imp : IsImpWire G C (opnd C j b)) :
    BelowF G C j := by
  by_contra h
  exact fixed ⟨j,live.1,b,live,op,h,imp⟩

lemma only_dirty_below_and {g i j : ℕ} (form : TopForm G C)
    (unique : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (ai : (gateAt C i).op = GateOp.and) (aj : (gateAt C j).op = GateOp.and)
    (below : InCone n C i j) : i = g := by
  by_contra h
  exact form i hi j hj ai (unique i hi ai h) aj below

open WireTheory

lemma gate_mem {k : ℕ} (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  rw [gateAt_eq C k hk]
  exact List.getElem_mem hk

lemma all_high (ao : IsAO2 n C) {w : ℕ} (valid : w < n + C.gates.length) :
    W n C (fun _ => true) w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases input : w < n
    · exact W_input n C _ w input
    let k := w - n
    have hk : k < C.gates.length := by dsimp [k]; omega
    have eqw : w = n + k := by dsimp [k]; omega
    rw [eqw]
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (ao.2.2 _ (gate_mem hk))
    have ha := ao.2.1 k hk a (by simp [hab])
    have hb := ao.2.1 k hk b (by simp [hab])
    rcases ao.1 _ (gate_mem hk) with op | op
    · rw [W_and n C _ k hk op a b hab ha hb, ih a (by omega) (by omega), ih b (by omega) (by omega)]; rfl
    · rw [W_or n C _ k hk op a b hab ha hb, ih a (by omega) (by omega), ih b (by omega) (by omega)]; rfl

lemma topForm_of_fixed (ao : IsAO2 n C) (fixed : IsLiftFixedPoint G C)
    (live : ∀ k < C.gates.length, InOutputCone n C k)
    (operands : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ t ∈ (gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, W n C x t = true → graphFun G ∅ x = true)) :
    TopForm G C := by
  intro i hi j hj _ below andJ path
  suffices descend : ∀ k, k < C.gates.length → InCone n C i k →
      (gateAt C k).op = GateOp.or ∧ BelowF G C k by
    have clash := (descend j hj path).1.symm.trans andJ
    contradiction
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk inside
    obtain ⟨w,member,lo,lt,pathw⟩ := (inCone_iff n C i k hk).mp inside
    have hprev : w - n < k := by omega
    have belowPrev : BelowF G C (w - n) := by
      rcases pathw with eq | sub
      · simpa [← eq] using below
      · exact (ih _ hprev (by omega) sub).2
    have bw : ∀ x : Fin n → Bool, W n C x w = true → graphFun G ∅ x = true := by
      have e : n + (w - n) = w := by omega
      simpa only [BelowF, gateVal, W, e] using belowPrev
    rcases ao.1 _ (gate_mem hk) with op | op
    · exact False.elim ((operands k hk op w member) bw)
    · refine ⟨op, ?_⟩
      have imp : IsImpWire G C w := ⟨bw, _, all_high ao (by omega)⟩
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (ao.2.2 _ (gate_mem hk))
      simp only [hab, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · apply or_above_implicant (b := 0) fixed (live k hk) op
        simpa [opnd, hab] using imp
      · apply or_above_implicant (b := 1) fixed (live k hk) op
        simpa [opnd, hab] using imp

lemma pure_operand {g w : ℕ} (ao : IsAO2 n C) (hg : g < C.gates.length)
    (pure : ∀ i, InCone n C i g → (gateAt C i).op ≠ GateOp.and)
    (hw : w ∈ (gateAt C g).inputs) (x : Fin n → Bool) :
    W n C x w = true ↔ ∃ u ∈ R n C w, x u = true := by
  constructor
  · intro on
    by_cases input : w < n
    · exact ⟨⟨w,input⟩, (mem_R ..).mpr (reach_refl n C ⟨w,input⟩), (W_input n C x w input).symm.trans on⟩
    obtain ⟨k,rfl⟩ : ∃ k, w = n + k := ⟨w-n, by omega⟩
    have lt := ao.2.1 g hg _ hw
    have mono : PEqualNP.MetaComplexity.Monotone2 C := fun d hd =>
      ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ao.1 d hd, (ao.2.2 d hd).le⟩
    rcases descent n C mono x k (by omega) on with op | ⟨i,sub,op,_⟩ | ⟨u,xu,ru⟩
    · exact False.elim (pure k ((inCone_iff n C k g hg).mpr
        ⟨_,hw,by omega,lt,Or.inl (by omega)⟩) op)
    · exact False.elim (pure i ((inCone_iff n C i g hg).mpr
        ⟨_,hw,by omega,lt,Or.inr (by simpa using sub)⟩) op)
    · exact ⟨u,(mem_R ..).mpr ru,xu⟩
  · rintro ⟨u,ru,xu⟩
    exact reach_val n C u w x xu ((mem_R ..).mp ru)

lemma dirty_rectangle_at {g : ℕ} (ao : IsAO2 n C) (hg : g < C.gates.length)
    (op : (gateAt C g).op = GateOp.and) (form : TopForm G C)
    (unique : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (off : ∀ v : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput v) = false) :
    ∃ a b, (gateAt C g).inputs = [a,b] ∧
    let A := R n C a
    let B := R n C b
    A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      ∀ x : Fin n → Bool, gateVal n C g x = true ↔
        (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true) := by
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (ao.2.2 _ (gate_mem hg))
  have pure : ∀ i, InCone n C i g → (gateAt C i).op ≠ GateOp.and := by
    intro i sub opi
    have lt := inCone_lt n C g hg i sub
    exact (Nat.ne_of_lt lt) (only_dirty_below_and form unique (by omega) hg opi op sub)
  have ma : a ∈ (gateAt C g).inputs := by simp [hab]
  have mb : b ∈ (gateAt C g).inputs := by simp [hab]
  have ha := ao.2.1 g hg a ma
  have hb := ao.2.1 g hg b mb
  have sem (x : Fin n → Bool) : gateVal n C g x = true ↔
      (∃ u ∈ R n C a, x u = true) ∧ (∃ v ∈ R n C b, x v = true) := by
    change W n C x (n + g) = true ↔ _
    rw [W_and n C x g hg op a b hab ha hb, Bool.and_eq_true,
      pure_operand ao hg pure ma x, pure_operand ao hg pure mb x]
  obtain ⟨⟨u,hu,_⟩,⟨v,hv,_⟩⟩ := (sem (fun _ => true)).mp (all_high ao (by omega))
  refine ⟨a,b,hab,⟨u,hu⟩,⟨v,hv⟩,Finset.disjoint_left.mpr ?_,sem⟩
  intro t ta tb
  have ht : PEqualNP.SplitCount.unitInput t t = true := by simp [PEqualNP.SplitCount.unitInput]
  have on := (sem _).mpr ⟨⟨t,ta,ht⟩,⟨t,tb,ht⟩⟩
  rw [off] at on
  contradiction

lemma dirty_rectangle {g : ℕ} (ao : IsAO2 n C) (hg : g < C.gates.length)
    (op : (gateAt C g).op = GateOp.and) (form : TopForm G C)
    (unique : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (off : ∀ v : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput v) = false) :
    ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      ∀ x : Fin n → Bool, gateVal n C g x = true ↔
        (∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true) := by
  obtain ⟨a,b,_,rect⟩ := dirty_rectangle_at ao hg op form unique off
  exact ⟨R n C a,R n C b,rect⟩

def OrFrom (n : ℕ) (C : Circuit) (source w : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P source → (∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
    ∀ t ∈ (gateAt C k).inputs, t < n + k → P t → P (n+k)) → P w

lemma orFrom_val {s w : ℕ} (path : OrFrom n C s w) (x : Fin n → Bool) :
    W n C x s = true → W n C x w = true := by
  intro on
  exact path _ on (fun k hk op t ht bound v => (W_or_iff n C x k hk op).mpr ⟨t,ht,bound,v⟩)

def OnlyAnd (n : ℕ) (C : Circuit) (g w : ℕ) : Prop :=
  ∀ k, w = n + k → ∀ i, (i = k ∨ InCone n C i k) → (gateAt C i).op = GateOp.and → i = g

lemma onlyAnd_operand {g k w : ℕ} (ao : IsAO2 n C) (hk : k < C.gates.length)
    (hw : w ∈ (gateAt C k).inputs)
    (h : ∀ i, InCone n C i k → (gateAt C i).op = GateOp.and → i = g) : OnlyAnd n C g w := by
  intro j eq i path op
  apply h i ((inCone_iff n C i k hk).mpr ⟨w, hw, by omega, ao.2.1 k hk _ hw, ?_⟩) op
  simpa [eq] using path

lemma operand_expansion {g w : ℕ} (ao : IsAO2 n C) (valid : w < n + C.gates.length)
    (only : OnlyAnd n C g w) (x : Fin n → Bool) :
    W n C x w = true ↔ (∃ u ∈ R n C w, x u = true) ∨
      (OrFrom n C (n+g) w ∧ gateVal n C g x = true) := by
  constructor
  · intro on
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases input : w < n
      · exact Or.inl ⟨⟨w,input⟩,(mem_R ..).mpr (reach_refl n C ⟨w,input⟩), (W_input n C x w input).symm.trans on⟩
      obtain ⟨k,eq⟩ : ∃ k, w = n + k := ⟨w-n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases ao.1 _ (gate_mem hk) with op | op
      · have kg := only k eq k (Or.inl rfl) op
        subst g
        exact Or.inr ⟨fun P hs _ => eq ▸ hs, by simpa only [eq, W, gateVal] using on⟩
      · obtain ⟨t,member,bound,onT⟩ := (W_or_iff n C x k hk op).mp (eq ▸ on)
        have onlyT := onlyAnd_operand ao hk member (fun i hi => only k eq i (Or.inr hi))
        rcases ih t (by omega) (by omega) onlyT onT with ⟨u,hu,xu⟩ | ⟨path,xg⟩
        · apply Or.inl
          exact ⟨u,(mem_R ..).mpr (eq ▸ reach_step n C u k hk op t member bound ((mem_R ..).mp hu)),xu⟩
        · exact Or.inr ⟨fun P hs next => eq ▸ next k hk op t member bound (path P hs next),xg⟩
  · rintro (⟨u,hr,xu⟩ | ⟨path,xg⟩)
    · exact reach_val n C u w x xu ((mem_R ..).mp hr)
    · exact orFrom_val path x xg

lemma clean_top_expansion {g k : ℕ} (ao : IsAO2 n C) (form : TopForm G C)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (dirty : ¬ BelowF G C g) (hk : k < C.gates.length) (op : (gateAt C k).op = GateOp.and)
    (clean : BelowF G C k) :
    ∃ p q, (gateAt C k).inputs.Perm [p,q] ∧ ¬ OrFrom n C (n+g) q ∧
      ∀ x : Fin n → Bool, gateVal n C k x = true ↔
        ((∃ u ∈ R n C p, x u = true) ∨ (OrFrom n C (n+g) p ∧ gateVal n C g x = true)) ∧
        (∃ v ∈ R n C q, x v = true) := by
  classical
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (ao.2.2 _ (gate_mem hk))
  have ma : a ∈ (gateAt C k).inputs := by simp [hab]
  have mb : b ∈ (gateAt C k).inputs := by simp [hab]
  have stack (i : ℕ) (path : InCone n C i k) (opI : (gateAt C i).op = GateOp.and) : i = g :=
    only_dirty_below_and form unique (lt_trans (inCone_lt n C k hk i path) hk) hk opI op path
  have expand (t : ℕ) (ht : t ∈ (gateAt C k).inputs) (x : Fin n → Bool) :=
    operand_expansion ao (lt_trans (ao.2.1 k hk t ht) (Nat.add_lt_add_left hk n))
      (onlyAnd_operand ao hk ht stack) x
  have sem (x : Fin n → Bool) : gateVal n C k x = true ↔ W n C x a = true ∧ W n C x b = true := by
    change W n C x (n+k) = true ↔ _
    rw [W_and n C x k hk op a b hab (ao.2.1 k hk a ma) (ao.2.1 k hk b mb),Bool.and_eq_true]
  by_cases hb : OrFrom n C (n+g) b
  · have ha : ¬ OrFrom n C (n+g) a := by
      intro both
      exact dirty (fun x hx => clean x ((sem x).mpr ⟨orFrom_val both x hx, orFrom_val hb x hx⟩))
    refine ⟨b,a,hab ▸ List.Perm.swap _ _ [],ha,?_⟩
    intro x
    rw [sem, and_comm, expand b mb, expand a ma]
    simp only [ha, false_and, or_false]
  · refine ⟨a,b,hab ▸ List.Perm.refl _,hb,?_⟩
    intro x
    rw [sem, expand a ma, expand b mb]
    simp only [hb, false_and, or_false]

def Hits (S : Finset (Fin n)) (x : Fin n → Bool) : Prop := ∃ v ∈ S, x v = true

lemma hits_pair (S : Finset (Fin n)) (u v : Fin n) : Hits S (pairInput u v) ↔ u ∈ S ∨ v ∈ S := by
  simp only [Hits,pairInput,decide_eq_true_eq]
  aesop

lemma pair_edge (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a,b,adj,ha,hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl adj).elim
    · exact adj
    · exact adj.symm
    · exact (G.irrefl adj).elim
  · intro h
    exact ⟨u,v,h,Or.inl rfl,Or.inr rfl⟩

lemma route_pairs (A B S : Finset (Fin n)) (disj : Disjoint A B) (u v : Fin n) :
    (Hits A (pairInput u v) ∧ Hits B (pairInput u v) ∧ Hits S (pairInput u v)) ↔
      (u ∈ A ∩ S ∧ v ∈ B) ∨ (v ∈ A ∩ S ∧ u ∈ B) ∨
      (u ∈ B ∩ S ∧ v ∈ A) ∨ (v ∈ B ∩ S ∧ u ∈ A) := by
  simp only [hits_pair,Finset.mem_inter]
  have hu : u ∈ A → u ∈ B → False := fun ha hb => Finset.disjoint_left.mp disj ha hb
  have hv : v ∈ A → v ∈ B → False := fun ha hb => Finset.disjoint_left.mp disj ha hb
  tauto

lemma route_complete (A B S : Finset (Fin n))
    (sound : ∀ x : Fin n → Bool, Hits A x → Hits B x → Hits S x → graphFun G ∅ x = true) :
    (∀ u ∈ A ∩ S, ∀ v ∈ B, G.Adj u v) ∧ (∀ u ∈ B ∩ S, ∀ v ∈ A, G.Adj u v) := by
  constructor <;> intro u hu v hv <;> obtain ⟨h1,h2⟩ := Finset.mem_inter.mp hu
  · exact (pair_edge u v).mp (sound _ ((hits_pair ..).mpr (.inl h1)) ((hits_pair ..).mpr (.inr hv)) ((hits_pair ..).mpr (.inl h2)))
  · exact (pair_edge u v).mp (sound _ ((hits_pair ..).mpr (.inr hv)) ((hits_pair ..).mpr (.inl h1)) ((hits_pair ..).mpr (.inl h2)))

lemma star_centres {U B : Finset (Fin n)} (c4 : NoFourCycle G) (many : 1 < B.card)
    (all_adj : ∀ u ∈ U, ∀ v ∈ B, G.Adj u v) : U.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra neq
  have sub : B ⊆ Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,all_adj u hu b hb,all_adj v hv b hb⟩
  exact (Nat.not_lt_of_ge (le_trans (Finset.card_le_card sub) (c4 u v neq))) many

lemma common_neighbour_unique (c4 : NoFourCycle G) {a b x y : Fin n} (ab : a ≠ b)
    (ax : G.Adj a x) (bx : G.Adj b x) (ay : G.Adj a y) (by' : G.Adj b y) : x = y := by
  apply Finset.card_le_one.mp (c4 a b ab)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ax,bx⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ay,by'⟩

lemma double_star {A B : Finset (Fin n)} {u v : Fin n} (c4 : NoFourCycle G)
    (hu : u ∈ A) (hv : v ∈ B) (u_all : ∀ b ∈ B, G.Adj u b) (v_all : ∀ a ∈ A, G.Adj a v)
    {a b : Fin n} (ha : a ∈ A) (hb : b ∈ B) : G.Adj a b ↔ a = u ∨ b = v := by
  constructor
  · intro ab
    by_cases au : a = u
    · exact Or.inl au
    · exact Or.inr (common_neighbour_unique c4 au ab (u_all b hb) (v_all a ha) (u_all v hv))
  · rintro (rfl | rfl)
    · exact u_all b hb
    · exact v_all a ha

lemma triple_edge {a b y : Fin n} (h : graphFun G ∅ (fun t => decide (t=a ∨ t=b ∨ t=y)) = true) :
    G.Adj a b ∨ G.Adj a y ∨ G.Adj b y := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at h
  obtain ⟨p,q,pq,hp,hq⟩ := h
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    first | exact (G.irrefl pq).elim | solve_by_elim [Or.inl, Or.inr, SimpleGraph.Adj.symm]

lemma mixed_branch_forcing {A B S : Finset (Fin n)} {u y z a b : Fin n}
    (s : Fin n → Bool) (bip : ∀ p q, G.Adj p q → s p ≠ s q) (c4 : NoFourCycle G)
    (sound : ∀ x : Fin n → Bool, Hits A x → Hits B x → Hits S x → graphFun G ∅ x = true)
    (ha : a ∈ A) (hb : b ∈ B) (hy : y ∈ S) (ab : ¬ G.Adj a b)
    (same : s a = s y) (distinct : u ≠ y) (ub : G.Adj u b) (uz : G.Adj u z) (yz : G.Adj y z) : b = z := by
  let x := fun t : Fin n => decide (t=a ∨ t=b ∨ t=y)
  have on := sound x ⟨a,ha,by simp [x]⟩ ⟨b,hb,by simp [x]⟩ ⟨y,hy,by simp [x]⟩
  rcases triple_edge on with e | e | e
  · exact (ab e).elim
  · exact (bip _ _ e same).elim
  · exact common_neighbour_unique c4 distinct ub e.symm uz yz

end Exchange3700

namespace Flat3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open Prune3700 LMeta616 Exchange3700 WireTheory

def Marked (n : ℕ) (gs : List Gate) (P : ℕ → Prop) : Prop :=
  ∀ j < gs.length, let d := gateAt ⟨gs,0⟩ j
    (d.op = GateOp.and → ¬ P (n+j)) ∧
    (d.op = GateOp.and ∨ P (n+j) → ∀ w ∈ d.inputs, P w)

lemma no_stacks {n : ℕ} {gs : List Gate} {P : ℕ → Prop} (mark : Marked n gs P) :
    ∀ j < gs.length, ∀ i, InCone n ⟨gs,0⟩ i j →
      (gateAt ⟨gs,0⟩ j).op = GateOp.and ∨ P (n+j) → (gateAt ⟨gs,0⟩ i).op ≠ GateOp.and := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj i sub needs
    obtain ⟨w,member,lo,lt,inside⟩ := (inCone_iff n ⟨gs,0⟩ i j hj).mp sub
    have pure := (mark j hj).2 needs w member
    have pw : P (n+(w-n)) := by simpa only [Nat.add_sub_of_le lo] using pure
    have lt' : w-n < j := by omega
    rcases inside with rfl | inside
    · exact fun op => (mark _ (by omega)).1 op pw
    · exact ih _ lt' (by omega) i inside (Or.inr pw)

def SourceMarks (n g : ℕ) (C : Circuit) (P : ℕ → Prop) : Prop :=
  ∀ j < C.gates.length, j ≠ g → let d := gateAt C j
    (d.op = GateOp.and → ¬ P (n+j)) ∧
    (d.op = GateOp.and ∨ P (n+j) → ∀ w ∈ d.inputs, P w)

lemma source_marks {n g : ℕ} {C : Circuit} (ao : IsAO2 n C)
    (stack : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ i,
      InCone n C i j → (gateAt C i).op = GateOp.and → i = g) : SourceMarks n g C (OnlyAnd n C g) := by
  intro j hj ne
  refine ⟨fun op pure => ne (pure j rfl j (Or.inl rfl) op), ?_⟩
  rintro (op | pure) w hw
  · exact onlyAnd_operand ao hj hw (stack j hj op)
  · exact onlyAnd_operand ao hj hw (fun i hi => pure j rfl i (Or.inr hi))

def Safe (P : ℕ → Prop) : Stat → Prop
  | .inl _ => True
  | .inr w => P w

lemma safe_simp {P : ℕ → Prop} {m : ℕ} (op : GateOp) (a b : Stat)
    (ha : Safe P a) (hb : Safe P b) (hm : P m) : Safe P (simpMono op m [a,b]).1 := by
  cases op <;> cases a with
  | inl x => cases x <;> cases b with
    | inl y => cases y <;> trivial
    | inr v => first | exact hb | trivial
  | inr u => cases b with
    | inl y => cases y <;> first | exact ha | trivial
    | inr v => first | exact hm | trivial

lemma carry {P : ℕ → Prop} {m : ℕ} {q : Prop} {v : Stat} (valid : statValid m v)
    (h : Safe P v) : Safe (Function.update P m q) v := by
  cases v with
  | inl b => trivial
  | inr w => simpa only [Safe, Function.update_of_ne (Nat.ne_of_lt valid)] using h

lemma preserve_mark {n : ℕ} {gs : List Gate} {P : ℕ → Prop} {q : Prop} (mark : Marked n gs P)
    (ao : IsAO2 n ⟨gs,0⟩) : Marked n gs (Function.update P (n+gs.length) q) := by
  intro j hj
  have ne : n+j ≠ n+gs.length := by omega
  simp only [Function.update_of_ne ne]
  refine ⟨(mark j hj).1, ?_⟩
  intro cond w mem
  have lt := ao.2.1 j hj w mem
  rw [Function.update_of_ne (show w ≠ n+gs.length by omega)]
  exact (mark j hj).2 cond w mem

lemma marked_build {n g : ℕ} {C : Circuit} {P : ℕ → Prop} (ao : IsAO2 n C)
    (source : SourceMarks n g C P) (j : ℕ) (hj : j ≤ C.gates.length) :
    let p := build n g C j
    ∃ Q : ℕ → Prop, Marked n p.gates Q ∧ ∀ w, P w → Safe Q (p.wire w) := by
  induction j with
  | zero =>
    refine ⟨P,by intro j hj; simp [build] at hj,?_⟩
    intro w hw
    by_cases lt : w < n <;> simp [build,lt,Safe,hw]
  | succ j ih =>
    obtain ⟨Q,mark,safe⟩ := ih (by omega)
    let p := build n g C j
    let m := n+p.gates.length
    let res := emitted n g j C p
    let Q' := Function.update Q m (P (n+j))
    have hj' : j < C.gates.length := by omega
    have ok := (valid_build (g := g) ao j (by omega)).1
    have prev (w : ℕ) (h : P w) : Safe Q' (p.wire w) :=
      carry ((valid_build (g := g) ao j (by omega)).2 w) (safe w h)
    obtain ⟨a,b,inputs⟩ := inputs_two ao hj'
    have ma : a ∈ (gateAt C j).inputs := by simp [inputs]
    have mb : b ∈ (gateAt C j).inputs := by simp [inputs]
    have atM : Q' m ↔ P (n+j) := by simp [Q']
    refine ⟨Q',?_,?_⟩
    · change Marked n (p.gates ++ res.2.toList) Q'
      have old := preserve_mark (q := P (n+j)) mark ok
      cases ed : res.2 with
      | none => simpa [Q',m,p] using old
      | some d =>
        have ne : j ≠ g := by intro eq; simp [res,emitted,eq] at ed
        have emit : (simpMono (gateAt C j).op m [p.wire a,p.wire b]).2 = some d := by
          simpa [res,emitted,ne,inputs,m] using ed
        obtain ⟨i,k,ea,eb,rfl,_⟩ := emitted_shape emit
        intro t ht
        by_cases earlier : t < p.gates.length
        · have eq : gateAt ⟨p.gates ++ [{op := (gateAt C j).op, inputs := [i,k]}],0⟩ t = gateAt ⟨p.gates,0⟩ t := List.getD_append _ _ _ _ earlier
          change _ ∧ _
          simpa only [Option.toList_some,eq] using (show _ from old t earlier)
        · change t < (p.gates ++ [_]).length at ht
          have eq : t = p.gates.length := by simp at ht; omega
          subst t
          have last : gateAt ⟨p.gates ++ [{op := (gateAt C j).op, inputs := [i,k]}],0⟩ p.gates.length = ⟨(gateAt C j).op,[i,k]⟩ := by simp [gateAt]
          simp only [Option.toList_some,last]
          refine ⟨fun op h => (source j hj' ne).1 op (atM.mp h),?_⟩
          intro cond w hw
          have cond' : (gateAt C j).op = GateOp.and ∨ P (n+j) := cond.imp_right atM.mp
          have ia := prev a ((source j hj' ne).2 cond' a ma)
          have ib := prev b ((source j hj' ne).2 cond' b mb)
          rw [ea] at ia
          rw [eb] at ib
          rcases List.mem_cons.mp hw with rfl | h
          · exact ia
          · exact (List.mem_singleton.mp h) ▸ ib
    · intro w hw
      change Safe Q' (Function.update p.wire (n+j) res.1 w)
      by_cases eq : w = n+j
      · subst w
        rw [Function.update_self]
        by_cases ne : j = g
        · simp [res,emitted,ne,Safe]
        have oblig := (source j hj' ne).2 (Or.inr hw)
        simpa [res,emitted,ne,inputs,m] using
          safe_simp (gateAt C j).op (p.wire a) (p.wire b) (prev a (oblig a ma)) (prev b (oblig b mb)) (atM.mpr hw)
      · rw [Function.update_of_ne eq]
        exact prev w hw

lemma simp_ne_true (op : GateOp) (m : ℕ) (a b : Stat) (ha : a ≠ .inl true) (hb : b ≠ .inl true) :
    (simpMono op m [a,b]).1 ≠ .inl true := by
  cases a with
  | inl a => cases a <;> cases b with
    | inl b => cases b <;> cases op <;> simp_all [simpMono]
    | inr t => cases op <;> simp_all [simpMono]
  | inr t => cases b with
    | inl b => cases b <;> cases op <;> simp_all [simpMono]
    | inr u => cases op <;> simp [simpMono]

lemma no_true {n g : ℕ} {C : Circuit} (ao : IsAO2 n C) (j : ℕ) (hj : j ≤ C.gates.length) (w : ℕ) :
    (build n g C j).wire w ≠ .inl true := by
  induction j generalizing w with
  | zero => by_cases lt : w < n <;> simp [build,lt]
  | succ j ih =>
    by_cases eq : w = n+j
    · subst w
      by_cases eq : j=g
      · simp [build,emitted,eq]
      obtain ⟨a,b,inputs⟩ := inputs_two ao (show j < C.gates.length by omega)
      simp only [build, Function.update_self,emitted,eq,ite_false,inputs,List.map_cons,List.map_nil]
      exact simp_ne_true _ _ _ _ (ih (by omega) a) (ih (by omega) b)
    · simpa only [build, Function.update_of_ne eq] using ih (by omega) w

def outWire (n : ℕ) (p : Prefix) (w : ℕ) : ℕ :=
  match p.wire w with
  | .inl _ => n+p.gates.length
  | .inr i => i

lemma cut_circuit {n g : ℕ} {C : Circuit} (ao : IsAO2 n C)
    (stack : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ i,
      InCone n C i j → (gateAt C i).op = GateOp.and → i = g) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + ((Finset.range C.size).filter (charged n g C)).card ≤ C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = cutValue n g C x C.size C.output) ∧
      ∀ j < D.gates.length, ∀ i, InCone n D i j → (gateAt D j).op = GateOp.and → (gateAt D i).op ≠ GateOp.and := by
  let p := build n g C C.size
  let D : Circuit := ⟨p.gates,outWire n p C.output⟩
  obtain ⟨Q,hQ,_⟩ := marked_build (g := g) ao (source_marks ao stack) C.size (le_refl _)
  refine ⟨D,(valid_build ao C.size (le_refl _)).1,gate_budget ao C.size (le_refl _),?_,?_⟩
  · intro x
    have h := sound_build (g := g) ao x C.size (le_refl _) C.output
    let vals := p.gates.foldl LMeta616.step (List.ofFn x)
    change statVal vals (p.wire C.output) = _ at h
    change vals.getD (outWire n p C.output) false = _
    rw [←h]
    cases eq : p.wire C.output with
    | inl v =>
      cases v with
      | true => exact (no_true (g := g) ao C.size (le_refl _) C.output eq).elim
      | false =>
        simp only [outWire,eq,statVal]
        apply List.getD_eq_default
        simp [vals,LMeta616.foldl_step_len]
    | inr t => simp [outWire,eq,statVal]
  · intro j hj i path op
    exact no_stacks hQ j hj i path (Or.inl op)

end Flat3700

namespace Cover3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership WireTheory
open Exchange3700 Prune3700
variable {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

abbrev cut (n g : ℕ) (C : Circuit) (x : Fin n → Bool) := cutValue n g C x C.size

lemma stable (x : Fin n → Bool) {i j w : ℕ} (ij : i ≤ j) (lo : w < n+i) :
    cutValue n g C x j w = cutValue n g C x i w := by
  induction j with
  | zero => rw [show i = 0 by omega]
  | succ j ih =>
    by_cases eq : i=j+1
    · subst i; rfl
    · simpa only [cutValue,Function.update_of_ne (show w ≠ n+j by omega)] using ih (by omega)

lemma cut_input (x : Fin n → Bool) (t : Fin n) : cut n g C x t.val = x t := by
  rw [cut,stable x (i := 0) (Nat.zero_le _) (by simp)]
  simp [cutValue,List.getD_eq_getElem?_getD]

lemma cut_oob (x : Fin n → Bool) {j w : ℕ} (hi : n+j ≤ w) : cutValue n g C x j w = false := by
  induction j with
  | zero => simp [cutValue,List.getD_eq_getElem?_getD,List.getElem?_eq_none (show (List.ofFn x).length ≤ w by simpa using hi)]
  | succ j ih => simpa only [cutValue,Function.update_of_ne (show w ≠ n+j by omega)] using ih (by omega)

lemma cut_gate (ao : IsAO2 n C) (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length) :
    cut n g C x (n+k) = if k=g then false else (gateAt C k).op.eval ((gateAt C k).inputs.map (cut n g C x)) := by
  change cutValue n g C x C.size (n+k) = _
  rw [stable x (i := k+1) (show k+1 ≤ C.size from hk) (by omega)]
  simp only [cutValue,Function.update_self]
  split
  · rfl
  · congr 1
    apply List.map_congr_left
    intro w hw
    exact (stable x (show k ≤ C.size from hk.le) (ao.2.1 k hk w hw)).symm

lemma cut_or (ao : IsAO2 n C) (ag : (gateAt C g).op = GateOp.and) (x : Fin n → Bool)
    {k : ℕ} (hk : k < C.gates.length) (op : (gateAt C k).op = GateOp.or) :
    cut n g C x (n+k) = true ↔ ∃ t ∈ (gateAt C k).inputs, cut n g C x t = true := by
  have ne : k ≠ g := by rintro rfl; rw [ag] at op; contradiction
  simp only [cut_gate ao x hk,ne,ite_false,op,GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
  aesop

lemma cut_and (ao : IsAO2 n C) (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length) (ne : k ≠ g)
    (op : (gateAt C k).op = GateOp.and) : cut n g C x (n+k) = true ↔ ∀ t ∈ (gateAt C k).inputs, cut n g C x t = true := by
  simp only [cut_gate ao x hk,ne,ite_false,op,GateOp.eval,List.all_eq_true,List.mem_map,id_eq]
  aesop

lemma survives {t : Fin n} {w : ℕ} (ao : IsAO2 n C) (ag : (gateAt C g).op = GateOp.and)
    (x : Fin n → Bool) (ht : x t = true) (path : Reach n C t w) : cut n g C x w = true :=
  path (fun v => cut n g C x v = true) ((cut_input x t).trans ht)
    (fun _ hk op z hz _ on => (cut_or ao ag x hk op).mpr ⟨z,hz,on⟩)

lemma cut_sub (ao : IsAO2 n C) (x : Fin n → Bool) (w : ℕ) : cut n g C x w = true → W n C x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro on
    by_cases input : w < n
    · exact (W_input n C x w input).trans ((cut_input (g := g) (C := C) x ⟨w,input⟩).symm.trans on)
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    by_cases hk : k < C.gates.length
    · rw [cut_gate ao x hk] at on
      split at on
      · contradiction
      · rw [W_gate n C x k hk]
        apply LMeta616.gateOp_mono _ (ao.1 _ (gate_mem hk)) _ _ _ _ on
        intro t ht v
        have bound := ao.2.1 k hk _ ht
        simp [bound,ih t bound v]
    · have off := cut_oob (g := g) (C := C) x (j := C.size) (w := n+k) (by change n+C.gates.length ≤ n+k; omega)
      exact False.elim (Bool.noConfusion (off.symm.trans on))

lemma trace_loss (ao : IsAO2 n C) (ag : (gateAt C g).op = GateOp.and) (x : Fin n → Bool) (w : ℕ)
    (on : W n C x w = true) (lost : cut n g C x w ≠ true) :
    ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ OrFrom n C (n+k) w ∧
      W n C x (n+k) = true ∧ cut n g C x (n+k) ≠ true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases input : w < n
    · exact False.elim (lost ((cut_input x ⟨w,input⟩).trans ((W_input n C x w input).symm.trans on)))
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have hk : k < C.gates.length := by
      by_contra h
      have off := LMeta616.wires_oob C x (n+k) (by omega)
      exact Bool.noConfusion (off.symm.trans on)
    rcases ao.1 _ (gate_mem hk) with op | op
    · exact ⟨k,hk,op,fun _ h _ => h,on,lost⟩
    · obtain ⟨t,ht,lt,ont⟩ := (W_or_iff n C x k hk op).mp on
      have off : cut n g C x t ≠ true := fun v => lost ((cut_or ao ag x hk op).mpr ⟨t,ht,v⟩)
      obtain ⟨j,hj,aj,path,jOn,jLost⟩ := ih t lt ont off
      exact ⟨j,hj,aj,fun P hs step => step k hk op t ht lt (path P hs step),jOn,jLost⟩

noncomputable def routes (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) : Finset (Fin n) := by
  classical exact Finset.univ.filter (fun v => ∀ x : Fin n → Bool, gateVal n C g x = true → x v = true → graphFun G ∅ x = true)

lemma route_iff {v : Fin n} : v ∈ routes G C g ↔
    ∀ x : Fin n → Bool, gateVal n C g x = true → x v = true → graphFun G ∅ x = true := by
  classical simp [routes]

lemma global_cover (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (x : Fin n → Bool) : graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨
      (gateVal n C g x = true ∧ Hits (routes G C g) x) := by
  have eq (y : Fin n → Bool) : W n C y C.output = graphFun G ∅ y := congrFun computes y
  constructor
  · intro on
    by_cases stays : cut n g C x C.output = true
    · exact Or.inl stays
    obtain ⟨k,hk,op,path,before,after⟩ := trace_loss ao ag x C.output ((eq x).trans on) stays
    have clean : BelowF G C k := fun y hy => (eq y).symm.trans (orFrom_val path y hy)
    have ne : k ≠ g := fun e => dirty (e ▸ clean)
    obtain ⟨p,q,perm,_,sem⟩ := clean_top_expansion ao form unique dirty hk op clean
    obtain ⟨left,⟨v,hv,xv⟩⟩ := (sem x).mp before
    have qOn := survives ao ag x xv ((mem_R ..).mp hv)
    rcases left with ⟨u,hu,xu⟩ | ⟨gp,gOn⟩
    · have pOn := survives ao ag x xu ((mem_R ..).mp hu)
      exfalso
      apply after ((cut_and ao x hk ne op).mpr ?_)
      intro t ht
      have mem := perm.mem_iff.mp ht
      rcases List.mem_cons.mp mem with rfl | mem
      · exact pOn
      · exact (List.mem_singleton.mp mem) ▸ qOn
    · refine Or.inr ⟨gOn,v,route_iff.mpr ?_,xv⟩
      intro y gy yv
      exact clean y ((sem y).mpr ⟨Or.inr ⟨gp,gy⟩,v,hv,yv⟩)
  · rintro (on | ⟨on,v,hv,xv⟩)
    · exact (eq x).symm.trans (cut_sub ao x C.output on)
    · exact (route_iff.mp hv) x on xv

lemma cut_mono (ao : IsAO2 n C) {x y : Fin n → Bool} (le : ∀ t, x t = true → y t = true)
    {j : ℕ} (hj : j ≤ C.gates.length) (w : ℕ) : cutValue n g C x j w = true → cutValue n g C y j w = true := by
  induction j generalizing w with
  | zero =>
    by_cases hw : w < n
    · simpa [cutValue,List.getD_eq_getElem?_getD,hw] using le ⟨w,hw⟩
    · simp [cutValue,List.getD_eq_getElem?_getD,hw]
  | succ j ih =>
    by_cases eq : w = n+j
    · subst w
      simp only [cutValue,Function.update_self]
      split
      · simp
      · exact LMeta616.gateOp_mono _ (ao.1 _ (gate_mem (show j<C.gates.length by omega))) _ _ _
          (fun t _ => ih (by omega) t)
    · simpa only [cutValue,Function.update_of_ne eq] using ih (by omega) w

lemma two_star_cover {A B S : Finset (Fin n)} (ao : IsAO2 n C) (disj : Disjoint A B)
    (cover : ∀ x : Fin n → Bool, graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨
      (Hits A x ∧ Hits B x ∧ Hits S x)) (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨
      (Hits (A ∩ S) x ∧ Hits B x) ∨ (Hits (B ∩ S) x ∧ Hits A x) := by
  constructor
  · intro on
    obtain ⟨u,v,adj,xu,xv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by simpa [graphFun] using on
    rcases (cover _).mp ((pair_edge u v).mpr adj) with stays | routed
    · refine Or.inl (cut_mono ao (fun t ht => ?_) (le_refl _) C.output stays)
      have eq : t=u ∨ t=v := by simpa [pairInput] using ht
      exact eq.elim (fun e => e ▸ xu) (fun e => e ▸ xv)
    · right
      rcases (route_pairs A B S disj u v).mp routed with ⟨hu,hv⟩ | ⟨hv,hu⟩ | ⟨hu,hv⟩ | ⟨hv,hu⟩
      · exact Or.inl ⟨⟨u,hu,xu⟩,v,hv,xv⟩
      · exact Or.inl ⟨⟨v,hv,xv⟩,u,hu,xu⟩
      · exact Or.inr ⟨⟨u,hu,xu⟩,v,hv,xv⟩
      · exact Or.inr ⟨⟨v,hv,xv⟩,u,hu,xu⟩
  · rintro (stays | ⟨⟨u,hu,xu⟩,hb⟩ | ⟨⟨v,hv,xv⟩,ha⟩)
    · exact (cover x).mpr (Or.inl stays)
    · obtain ⟨ua,us⟩ := Finset.mem_inter.mp hu
      exact (cover x).mpr (Or.inr ⟨⟨u,ua,xu⟩,hb,u,us,xu⟩)
    · obtain ⟨vb,vs⟩ := Finset.mem_inter.mp hv
      exact (cover x).mpr (Or.inr ⟨ha,⟨v,vb,xv⟩,v,vs,xv⟩)

lemma graph_decomposition (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (hg : g < C.gates.length) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (units : ∀ u : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput u) = false) :
    ∃ A B S : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      (∀ u ∈ A ∩ S, ∀ v ∈ B, G.Adj u v) ∧ (∀ v ∈ B ∩ S, ∀ u ∈ A, G.Adj v u) ∧
      ∀ x : Fin n → Bool, graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨
        (Hits (A ∩ S) x ∧ Hits B x) ∨ (Hits (B ∩ S) x ∧ Hits A x) := by
  obtain ⟨A,B,ha,hb,disj,rect⟩ := dirty_rectangle ao hg ag form unique units
  let S := routes G C g
  have cover (x : Fin n → Bool) : graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨
      (Hits A x ∧ Hits B x ∧ Hits S x) := by
    rw [global_cover ao computes form ag dirty unique, rect]
    exact or_congr_right and_assoc
  obtain ⟨left,right⟩ := route_complete A B S (fun x a b s => (cover x).mpr (.inr ⟨a,b,s⟩))
  exact ⟨A,B,S,ha,hb,disj,left,right,two_star_cover ao disj cover⟩

end Cover3700

namespace Restore3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open WireTheory Exchange3700 Prune3700 Flat3700 Cover3700

structure Network (n : ℕ) where
  gates : List Gate
  pure : ℕ → Prop
  ao : IsAO2 n ⟨gates,0⟩
  marks : Marked n gates pure

abbrev bound {n : ℕ} (D : Network n) := n+D.gates.length
abbrev bit {n : ℕ} (D : Network n) (x : Fin n → Bool) (w : ℕ) := W n ⟨D.gates,0⟩ x w

lemma marked_snoc {n : ℕ} (D : Network n) (op : GateOp) (a b : ℕ)
    (ha : a < bound D) (hb : b < bound D) (andInput : op = .and → D.pure a ∧ D.pure b) :
    Marked n (D.gates ++ [⟨op,[a,b]⟩]) (Function.update D.pure (bound D) False) := by
  intro j hj
  by_cases old : j < D.gates.length
  · have eq : gateAt ⟨D.gates ++ [⟨op,[a,b]⟩],0⟩ j = gateAt ⟨D.gates,0⟩ j := List.getD_append _ _ _ _ old
    simpa only [eq] using preserve_mark (q := False) D.marks D.ao j old
  · have e : j=D.gates.length := by simp at hj; omega
    subst j
    have last : gateAt ⟨D.gates ++ [⟨op,[a,b]⟩],0⟩ D.gates.length = ⟨op,[a,b]⟩ := by simp [gateAt]
    simp only [last,Function.update_self,not_false_eq_true,implies_true,true_and,or_false]
    intro hand w hw
    rcases List.mem_cons.mp hw with rfl | h
    · rw [Function.update_of_ne (Nat.ne_of_lt ha)]; exact (andInput hand).1
    · obtain rfl := List.mem_singleton.mp h
      rw [Function.update_of_ne (Nat.ne_of_lt hb)]; exact (andInput hand).2

def append {n : ℕ} (D : Network n) (op : GateOp) (a b : ℕ) (ha : a < bound D) (hb : b < bound D)
    (hop : op = .and ∨ op = .or) (andInput : op = .and → D.pure a ∧ D.pure b) : Network n :=
  { gates := D.gates ++ [⟨op,[a,b]⟩]
    pure := Function.update D.pure (bound D) False
    ao := append_ao (d := ⟨op,[a,b]⟩) D.ao hop rfl (by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | h
      · exact ha
      · exact (List.mem_singleton.mp h) ▸ hb)
    marks := marked_snoc D op a b ha hb andInput }

lemma old_bit {n : ℕ} (D E : Network n) {ds : List Gate} (eq : E.gates = D.gates++ds)
    (x : Fin n → Bool) {w : ℕ} (hw : w < bound D) : bit E x w = bit D x w := by
  unfold bit W Circuit.wires
  rw [eq,List.foldl_append]
  apply foldl_stepWire_getD_lt
  change w < (D.gates.foldl stepWire (List.ofFn x)).length
  rw [foldl_stepWire_length,List.length_ofFn]
  exact hw

lemma new_bit {n : ℕ} (D E : Network n) (op : GateOp) {a b : ℕ}
    (eq : E.gates = D.gates ++ [⟨op,[a,b]⟩]) (x : Fin n → Bool) :
    bit E x (bound D) = op.eval [bit D x a,bit D x b] := by
  let vals := (Circuit.mk D.gates 0).wires (List.ofFn x)
  have hl : vals.length = bound D := wires_length n _ _
  change ((E.gates.foldl stepWire (List.ofFn x)).getD (bound D) false) = _
  rw [eq,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (vals ++ [op.eval [bit D x a,bit D x b]]).getD (bound D) false = _
  rw [←hl]
  simp

abbrev readOut {n : ℕ} (D : Network n) (x : Fin n → Bool) (o : Option ℕ) := o.elim false (bit D x)

lemma add_star {n : ℕ} (D : Network n) (o : Option ℕ) (outOK : ∀ t ∈ o, t < bound D)
    (a b : ℕ) (ha : a < bound D) (hb : b < bound D) (pa : D.pure a) (pb : D.pure b) :
    ∃ E : Network n, ∃ r < bound E,
      E.gates.length ≤ D.gates.length+2 ∧ D.gates.length ≤ E.gates.length ∧
      (∀ w < bound D, D.pure w → E.pure w) ∧
      (∀ x : Fin n → Bool, ∀ w < bound D, bit E x w = bit D x w) ∧
      ∀ x : Fin n → Bool, bit E x r = (readOut D x o || (bit D x a && bit D x b)) := by
  let H := append D .and a b ha hb (.inl rfl) (fun _ => ⟨pa,pb⟩)
  have len : H.gates.length = D.gates.length+1 := by simp [H,append]
  have newOK : bound D < bound H := by unfold bound; omega
  have head (x : Fin n → Bool) : bit H x (bound D) = (bit D x a && bit D x b) := by
    simpa [GateOp.eval] using new_bit D H .and (a:=a) (b:=b) rfl x
  have prev (x : Fin n → Bool) (w : ℕ) (hw : w < bound D) : bit H x w = bit D x w := old_bit D H rfl x hw
  have pure (w : ℕ) (hw : w < bound D) (p : D.pure w) : H.pure w := by
    simpa [H,append,Function.update_of_ne (Nat.ne_of_lt hw)] using p
  cases o with
  | none => exact ⟨H,_,newOK,by omega,by omega,pure,prev,fun x => by simpa [readOut] using head x⟩
  | some t =>
    have tOK := outOK t (by simp)
    let E := append H .or t (bound D) (lt_trans tOK newOK) newOK (.inr rfl) (by intro h; contradiction)
    have lenE : E.gates.length = H.gates.length+1 := by simp [E,append]
    refine ⟨E,bound H,by unfold bound; omega,by omega,by omega,?_,?_,?_⟩
    · intro w hw p
      simpa [E,append,Function.update_of_ne (Nat.ne_of_lt (lt_trans hw newOK))] using pure w hw p
    · intro x w hw
      exact (old_bit H E rfl x (lt_trans hw newOK)).trans (prev x w hw)
    · intro x
      have eq := new_bit H E .or (a := t) (b := bound D) rfl x
      simpa [GateOp.eval,head x,prev x t tOK,readOut] using eq

def Signal {n : ℕ} (D : Network n) (S : Finset (Fin n)) :=
  ∃ w < bound D, D.pure w ∧ ∀ x : Fin n → Bool, bit D x w = true ↔ Hits S x

lemma cut_base_exact {n g : ℕ} {C : Circuit} (ao : IsAO2 n C) {hg : g < C.gates.length}
    (ag : (gateAt C g).op = GateOp.and)
    (stack : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ i,
      InCone n C i j → (gateAt C i).op = GateOp.and → i = g) :
    ∃ D : Network n, ∃ o : Option ℕ, (∀ t ∈ o, t < bound D) ∧
      D.gates.length = (build n g C C.size).gates.length ∧
      (∀ x : Fin n → Bool, readOut D x o = cut n g C x C.output) ∧
      (∀ v : Fin n, Signal D {v}) ∧ (∀ w ∈ (gateAt C g).inputs, Signal D (R n C w)) := by
  let p := build n g C C.size
  obtain ⟨Q,mk,safe⟩ := marked_build ao (source_marks ao stack) C.size (le_refl _)
  obtain ⟨legal,valid⟩ := valid_build (g := g) ao C.size (le_refl _)
  let D : Network n := ⟨p.gates,Q,legal,mk⟩
  let o : Option ℕ := match p.wire C.output with | .inl _ => none | .inr t => some t
  have wire (x : Fin n → Bool) (w : ℕ) : LMeta616.statVal ((Circuit.mk D.gates 0).wires (List.ofFn x)) (p.wire w) = cut n g C x w := sound_build ao x C.size (le_refl _) w
  have signal (w : ℕ) (S : Finset (Fin n)) (nonempty : S.Nonempty) (pure : OnlyAnd n C g w)
      (sem : ∀ x : Fin n → Bool, cut n g C x w = true ↔ Hits S x) : Signal D S := by
    cases e : p.wire w with
    | inl v =>
      cases v with
      | true => exact (no_true (g := g) ao C.size (le_refl _) w e).elim
      | false =>
        obtain ⟨v,hv⟩ := nonempty
        have on := (sem (fun _ => true)).mpr ⟨v,hv,rfl⟩
        have h := wire (fun _ => true) w
        rw [e,on] at h
        contradiction
    | inr t =>
      have boundT := valid w
      have pureT := safe w pure
      change LMeta616.statValid (bound D) (p.wire w) at boundT
      change Safe Q (p.wire w) at pureT
      rw [e] at boundT pureT
      refine ⟨t,boundT,pureT,?_⟩
      intro x
      have eq := wire x w
      rw [e] at eq
      exact (show bit D x t = cut n g C x w from eq) ▸ sem x
  refine ⟨D,o,?_,rfl,?_,?_,?_⟩
  · intro t mem
    cases e : p.wire C.output with
    | inl v => simp [o,e] at mem
    | inr w =>
      have val := valid C.output
      change LMeta616.statValid (bound D) (p.wire C.output) at val
      rw [e] at val
      simp [o,e] at mem
      exact mem ▸ val
  · intro x
    have eq := wire x C.output
    cases e : p.wire C.output with
    | inl v =>
      cases v with
      | true => exact (no_true (g := g) ao C.size (le_refl _) C.output e).elim
      | false => simpa [o,e,readOut,LMeta616.statVal] using eq
    | inr t => simpa [o,e,readOut,LMeta616.statVal,bit,W] using eq
  · intro v
    apply signal v.val _ (by simp)
    · intro k h; have := v.isLt; omega
    · intro x; rw [cut_input]; simp [Hits]
  · intro w hw
    have pure (i : ℕ) (h : InCone n C i g) : (gateAt C i).op ≠ GateOp.and :=
      fun op => (Nat.ne_of_lt (inCone_lt n C g hg i h)) (stack g hg ag i h op)
    have sem := pure_operand ao hg pure hw
    obtain ⟨v,hv,_⟩ := (sem (fun _ => true)).mp (all_high ao (by have := ao.2.1 g hg w hw; omega))
    apply signal w _ ⟨v,hv⟩ (onlyAnd_operand ao hg hw (stack g hg ag))
    intro x
    constructor
    · exact fun h => (sem x).mp (cut_sub ao x w h)
    · rintro ⟨t,ht,xt⟩
      exact survives ao ag x xt ((mem_R ..).mp ht)

lemma cut_base {n g : ℕ} {C : Circuit} (ao : IsAO2 n C) {hg : g < C.gates.length}
    (ag : (gateAt C g).op = GateOp.and)
    (stack : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ i,
      InCone n C i j → (gateAt C i).op = GateOp.and → i = g) :
    ∃ D : Network n, ∃ o : Option ℕ, (∀ t ∈ o, t < bound D) ∧
      D.gates.length + ((Finset.range C.size).filter (charged n g C)).card ≤ C.size ∧
      (∀ x : Fin n → Bool, readOut D x o = cut n g C x C.output) ∧
      (∀ v : Fin n, Signal D {v}) ∧ (∀ w ∈ (gateAt C g).inputs, Signal D (R n C w)) := by
  obtain ⟨D,o,ho,size,sem,prim,sig⟩ := cut_base_exact (hg:=hg) ao ag stack
  exact ⟨D,o,ho,size ▸ gate_budget ao C.size (le_refl _),sem,prim,sig⟩

abbrev Star (n : ℕ) := Fin n × Finset (Fin n)
def Fires {n : ℕ} (t : Star n) (x : Fin n → Bool) := x t.1 = true ∧ Hits t.2 x

lemma add_many {n : ℕ} (stars : List (Star n)) (D : Network n) (o : Option ℕ)
    (outOK : ∀ t ∈ o, t < bound D)
    (ready : ∀ t ∈ stars, Signal D {t.1} ∧ Signal D t.2) :
    ∃ E : Network n, ∃ r : Option ℕ, (∀ t ∈ r, t < bound E) ∧
      E.gates.length ≤ D.gates.length + 2*stars.length ∧ ∀ x : Fin n → Bool,
      readOut E x r = true ↔ readOut D x o = true ∨ ∃ t ∈ stars, Fires t x := by
  induction stars generalizing D o with
  | nil => exact ⟨D,o,outOK,by simp,fun x => by simp⟩
  | cons t rest ih =>
    obtain ⟨⟨a,ha,pa,va⟩,⟨b,hb,pb,vb⟩⟩ := ready t (by simp)
    obtain ⟨H,r,hr,len,grow,marks,values,sem⟩ := add_star D o outOK a b ha hb pa pb
    have keep {S} (sig : Signal D S) : Signal H S := by
      obtain ⟨w,hw,pw,vw⟩ := sig
      have boundH : bound D ≤ bound H := Nat.add_le_add_left grow n
      exact ⟨w,lt_of_lt_of_le hw boundH,marks w hw pw,fun x => (values x w hw) ▸ vw x⟩
    obtain ⟨E,s,hs,sz,done⟩ := ih H (some r) (by simpa using hr) (fun t ht =>
      (ready t (List.mem_cons_of_mem _ ht)).imp keep keep)
    refine ⟨E,s,hs,by simp [List.length_cons]; omega,?_⟩
    intro x
    rw [done]
    have first : readOut H x (some r) = true ↔ readOut D x o = true ∨ Fires t x := by
      change bit H x r = true ↔ _
      simp only [sem,Bool.or_eq_true,Bool.and_eq_true,va x,vb x,Fires,Hits,Finset.mem_singleton]
      simp
    rw [first]
    simp [or_assoc]

noncomputable def centres {n : ℕ} (U B : Finset (Fin n)) : List (Star n) := U.toList.map (fun u => (u,B))

lemma centre_fires {n : ℕ} (U B : Finset (Fin n)) (x : Fin n → Bool) :
    (∃ t ∈ centres U B, Fires t x) ↔ Hits U x ∧ Hits B x := by
  simp only [centres,List.mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨_,⟨u,hu,rfl⟩,xu,xb⟩
    exact ⟨⟨u,hu,xu⟩,xb⟩
  · rintro ⟨⟨u,hu,xu⟩,xb⟩
    exact ⟨_,⟨u,hu,rfl⟩,xu,xb⟩

lemma reify {n : ℕ} (D : Network n) (o : Option ℕ) :
    ∃ E : Circuit, IsAO2 n E ∧ E.size = D.gates.length ∧
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = readOut D x o) ∧
      ∀ i < E.gates.length, ∀ j < E.gates.length, (gateAt E i).op = GateOp.and →
        (gateAt E j).op = GateOp.and → ¬ InCone n E i j := by
  let E : Circuit := ⟨D.gates,o.getD (bound D)⟩
  refine ⟨E,D.ao,rfl,?_,fun i _ j hj ai aj path => no_stacks D.marks j hj i path (Or.inl aj) ai⟩
  intro x
  cases o with
  | none => exact LMeta616.wires_oob E x (bound D) (le_refl _)
  | some t => rfl

def Goal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  ∃ E : Circuit, IsAO2 n E ∧ E.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun n E = graphFun G ∅ ∧
    ∀ i < E.gates.length, ∀ j < E.gates.length, (gateAt E i).op = GateOp.and → (gateAt E j).op = GateOp.and → ¬ InCone n E i j

set_option maxHeartbeats 1600000 in
lemma restore_actual {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (ao : IsAO2 n C) (computes : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (form : TopForm G C)
    (hg : g < C.gates.length) (op : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (units : ∀ u : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput u) = false)
    (budget : ∀ a b, (gateAt C g).inputs = [a,b] → let S := routes G C g
      2*((R n C a ∩ S).card+(R n C b ∩ S).card) + (build n g C C.size).gates.length ≤ C.size) : Goal G C := by
  obtain ⟨a,b,inputs,_,_,disj,rect⟩ := dirty_rectangle_at ao hg op form unique units
  let A := R n C a
  let B := R n C b
  let S := routes G C g
  have stack (j : ℕ) (hj : j < C.gates.length) (aj : (gateAt C j).op = GateOp.and) (i : ℕ)
      (h : InCone n C i j) (ai : (gateAt C i).op = GateOp.and) :=
    only_dirty_below_and form unique (lt_trans (inCone_lt n C j hj i h) hj) hj ai aj h
  obtain ⟨D,o,ho,sz,sem,primary,signals⟩ := cut_base_exact (hg := hg) ao op stack
  let stars := centres (A ∩ S) B ++ centres (B ∩ S) A
  have ready (t : Star n) (ht : t ∈ stars) : Signal D {t.1} ∧ Signal D t.2 := by
    refine ⟨primary _,?_⟩
    rcases List.mem_append.mp ht with ha | hb
    · obtain ⟨z,_,rfl⟩ := List.mem_map.mp ha
      exact signals b (by simp [inputs])
    · obtain ⟨z,_,rfl⟩ := List.mem_map.mp hb
      exact signals a (by simp [inputs])
  obtain ⟨H,r,_,used,result⟩ := add_many stars D o ho ready
  obtain ⟨E,aoE,sizeE,output,flat⟩ := reify H r
  have cost := budget a b inputs
  have length : stars.length = (A ∩ S).card + (B ∩ S).card := by simp [stars,centres]
  change 2*((A ∩ S).card+(B ∩ S).card) + _ ≤ _ at cost
  rw [length] at used
  refine ⟨E,aoE,by omega,?_,flat⟩
  funext x
  apply Bool.eq_iff_iff.mpr
  change E.eval (List.ofFn x) = true ↔ _
  rw [output,result,sem]
  have cover (y : Fin n → Bool) : graphFun G ∅ y = true ↔ cut n g C y C.output = true ∨ Hits A y ∧ Hits B y ∧ Hits S y := by
    rw [global_cover ao computes form op dirty unique,rect]
    exact or_congr_right and_assoc
  rw [two_star_cover ao disj cover x]
  apply or_congr_right
  rw [← centre_fires (A ∩ S) B, ← centre_fires (B ∩ S) A]
  constructor
  · rintro ⟨t,ht,fire⟩
    exact (List.mem_append.mp ht).imp (fun h => ⟨t,h,fire⟩) (fun h => ⟨t,h,fire⟩)
  · rintro (⟨t,h,fire⟩ | ⟨t,h,fire⟩)
    · exact ⟨t,List.mem_append.mpr (.inl h),fire⟩
    · exact ⟨t,List.mem_append.mpr (.inr h),fire⟩

set_option maxHeartbeats 1600000 in
lemma restore_if_budget {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (ao : IsAO2 n C) (computes : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (form : TopForm G C)
    (hg : g < C.gates.length) (op : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (units : ∀ u : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput u) = false)
    (budget : ∀ a b, (gateAt C g).inputs = [a,b] → let S := routes G C g
      2*((R n C a ∩ S).card+(R n C b ∩ S).card) ≤ ((Finset.range C.size).filter (charged n g C)).card) : Goal G C := by
  apply restore_actual ao computes form hg op dirty unique units
  intro a b ins
  exact le_trans (Nat.add_le_add_right (budget a b ins) _) (Nat.add_comm _ _ ▸ gate_budget ao C.size (le_refl _))

lemma large_actual {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (ao : IsAO2 n C) (computes : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (form : TopForm G C)
    (hg : g < C.gates.length) (op : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (units : ∀ u : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput u) = false)
    (c4 : NoFourCycle G) (big : ∀ w ∈ (gateAt C g).inputs, 1 < (R n C w).card)
    (paid : (build n g C C.size).gates.length + 4 ≤ C.size) : Goal G C := by
  apply restore_actual ao computes form hg op dirty unique units
  obtain ⟨a,b,inputs,_,_,_,rect⟩ := dirty_rectangle_at ao hg op form unique units
  intro c d hand
  have id := inputs.symm.trans hand
  obtain ⟨rfl,rfl⟩ : a=c ∧ b=d := by simpa using id
  let A := R n C a
  let B := R n C b
  let S := routes G C g
  have sound (x : Fin n → Bool) (ha : Hits A x) (hb : Hits B x) (hs : Hits S x) : graphFun G ∅ x = true := by
    obtain ⟨v,hv,xv⟩ := hs
    exact (route_iff.mp hv) x ((rect x).mpr ⟨ha,hb⟩) xv
  obtain ⟨left,right⟩ := route_complete A B S sound
  have cardA := star_centres c4 (big b (by simp [inputs])) left
  have cardB := star_centres c4 (big a (by simp [inputs])) right
  change 2*((A ∩ S).card + (B ∩ S).card) + _ ≤ _
  omega

lemma large_sides {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (ao : IsAO2 n C) (computes : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (form : TopForm G C)
    (hg : g < C.gates.length) (op : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (units : ∀ u : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput u) = false)
    (c4 : NoFourCycle G) (big : ∀ w ∈ (gateAt C g).inputs, 1 < (R n C w).card)
    (paid : 4 ≤ ((Finset.range C.size).filter (charged n g C)).card) : Goal G C := by
  apply large_actual ao computes form hg op dirty unique units c4 big
  exact le_trans (Nat.add_le_add_left paid _) (gate_budget ao C.size (le_refl _))

lemma has_reader {n g : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length) (sub : InCone n C g k) :
    ∃ j < C.gates.length, g < j ∧ n+g ∈ (gateAt C j).inputs := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨w,hw,lo,lt,path⟩ := (inCone_iff n C g k hk).mp sub
    rcases path with eq | sub
    · exact ⟨k,hk,by omega, (show n+g = w by omega) ▸ hw⟩
    · exact ih (w-n) (by omega) (by omega) sub

lemma two_credits {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (computes : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (live : PEqualNP.Core.InOutputCone n C g) (dirty : ¬ BelowF G C g) :
    2 ≤ ((Finset.range C.size).filter (charged n g C)).card := by
  obtain ⟨hg,out | ⟨_,path⟩⟩ := live
  · exfalso
    apply dirty
    intro x hx
    rw [←computes]
    change W n C x C.output = true
    exact out ▸ hx
  · have len : (cones n C).length = C.gates.length := by simp [cones,coneFold_length]
    have bound : C.output - n < C.gates.length := by
      by_contra h
      have off := List.getD_eq_default (cones n C) ([] : List ℕ) (show (cones n C).length ≤ C.output-n by omega)
      unfold InCone at path
      rw [off] at path
      exact List.not_mem_nil path
    obtain ⟨j,hj,lt,mem⟩ := has_reader bound path
    have sub : ({g,j} : Finset ℕ) ⊆ (Finset.range C.size).filter (charged n g C) := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | h
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg,Or.inl rfl⟩
      · obtain rfl := Finset.mem_singleton.mp h
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,Or.inr mem⟩
    simpa [Finset.card_pair (Nat.ne_of_lt lt)] using Finset.card_le_card sub

end Restore3700

namespace Reader3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700
variable {n g j : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma inherit_mix {z : Fin n} {w : ℕ} (mix : Reach n C z (n+j))
    (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j) (path : OrFrom n C (n+g) w) :
    w=n+g ∨ Reach n C z w := by
  apply path (fun t => t=n+g ∨ Reach n C z t) (Or.inl rfl)
  intro k hk op t ht lt h
  rcases h with rfl | prev
  · exact Or.inr ((only k hk ht) ▸ mix)
  · exact Or.inr (reach_step n C z k hk op t ht lt prev)

lemma mixed_loss {z : Fin n} (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (mix : Reach n C z (n+j)) (opJ : (gateAt C j).op = GateOp.or)
    (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j)
    (x : Fin n → Bool) (on : graphFun G ∅ x = true) (off : cut n g C x C.output ≠ true) :
    gateVal n C g x = true ∧ x z ≠ true ∧ ∃ v ∈ routes G C g, G.Adj z v ∧ x v = true := by
  have eq (y : Fin n → Bool) : W n C y C.output = graphFun G ∅ y := congrFun computes y
  obtain ⟨k,hk,ak,out,before,after⟩ := trace_loss ao ag x C.output ((eq x).trans on) off
  have clean : BelowF G C k := fun y hy => (eq y).symm.trans (orFrom_val out y hy)
  have ne : k ≠ g := fun e => dirty (e ▸ clean)
  obtain ⟨p,q,perm,_,sem⟩ := clean_top_expansion ao form unique dirty hk ak clean
  obtain ⟨left,v,hv,xv⟩ := (sem x).mp before
  have qOn := survives ao ag x xv ((mem_R ..).mp hv)
  have pOff (hp : cut n g C x p = true) : False := by
    apply after ((cut_and ao x hk ne ak).mpr ?_)
    intro t ht
    rcases List.mem_cons.mp (perm.mem_iff.mp ht) with rfl | h
    · exact hp
    · exact (List.mem_singleton.mp h) ▸ qOn
  rcases left with ⟨u,hu,xu⟩ | ⟨gp,gOn⟩
  · exact (pOff (survives ao ag x xu ((mem_R ..).mp hu))).elim
  have zp : Reach n C z p := by
    rcases inherit_mix mix only gp with e | h
    · have mem : n+g ∈ (gateAt C k).inputs := perm.mem_iff.mpr (by simp [e])
      have bad := (only k hk mem) ▸ ak
      rw [opJ] at bad
      contradiction
    · exact h
  refine ⟨gOn,fun xz => pOff (survives ao ag x xz zp),v,route_iff.mpr ?_,?_,xv⟩
  · intro y gy yv
    exact clean y ((sem y).mpr ⟨Or.inr ⟨gp,gy⟩,v,hv,yv⟩)
  · apply (pair_edge z v).mp
    apply clean _ ((sem _).mpr ?_)
    exact ⟨Or.inl ⟨z,(mem_R ..).mpr zp,by simp [pairInput]⟩,v,hv,by simp [pairInput]⟩

lemma centre_budget {A B S : Finset (Fin n)} {z : Fin n} (c4 : NoFourCycle G)
    (bip : ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v)
    (neighbours : ∀ u ∈ S, G.Adj z u)
    (left : ∀ u ∈ A ∩ S, ∀ v ∈ B, G.Adj u v)
    (right : ∀ v ∈ B ∩ S, ∀ u ∈ A, G.Adj v u)
    (az : ∃ u ∈ A, u ≠ z) (bz : ∃ v ∈ B, v ≠ z) :
    (A ∩ S).card + (B ∩ S).card ≤ 1 := by
  obtain ⟨s,color⟩ := bip
  have side {U V : Finset (Fin n)} (adj : ∀ u ∈ U ∩ S, ∀ v ∈ V, G.Adj u v)
      (diff : ∃ v ∈ V, v ≠ z) : (U ∩ S).card ≤ 1 := by
    obtain ⟨v,hv,vz⟩ := diff
    apply Finset.card_le_one.mpr
    intro u hu t ht
    exact common_neighbour_unique c4 vz (adj u hu v hv).symm (neighbours _ (Finset.mem_inter.mp hu).2)
      (adj t ht v hv).symm (neighbours _ (Finset.mem_inter.mp ht).2)
  have hA := side left bz
  have hB := side right az
  by_contra h
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < (A ∩ S).card by omega)
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < (B ∩ S).card by omega)
  have uv := color _ _ (left u hu v (Finset.mem_inter.mp hv).1)
  have zu := color _ _ (neighbours _ (Finset.mem_inter.mp hu).2)
  have zv := color _ _ (neighbours _ (Finset.mem_inter.mp hv).2)
  revert uv zu zv
  generalize s u = i, s v = v1, s z = k
  cases i <;> cases v1 <;> cases k <;> decide

set_option maxHeartbeats 1600000 in
lemma restore_subset {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (ao : IsAO2 n C) (_computes : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (form : TopForm G C)
    (hg : g < C.gates.length) (op : (gateAt C g).op = GateOp.and) (_dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (units : ∀ u : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput u) = false)
    (S : Finset (Fin n))
    (routed : ∀ x, graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨ (gateVal n C g x = true ∧ Hits S x))
    (budget : ∀ a b, (gateAt C g).inputs = [a,b] →
      2*((R n C a ∩ S).card+(R n C b ∩ S).card) ≤ ((Finset.range C.size).filter (charged n g C)).card) : Goal G C := by
  obtain ⟨a,b,inputs,_,_,disj,rect⟩ := dirty_rectangle_at ao hg op form unique units
  let A := R n C a
  let B := R n C b
  have stack (j : ℕ) (hj : j < C.gates.length) (aj : (gateAt C j).op = GateOp.and) (i : ℕ)
      (h : InCone n C i j) (ai : (gateAt C i).op = GateOp.and) :=
    only_dirty_below_and form unique (lt_trans (inCone_lt n C j hj i h) hj) hj ai aj h
  obtain ⟨D,o,ho,sz,sem,primary,signals⟩ := cut_base (hg := hg) ao op stack
  let stars := centres (A ∩ S) B ++ centres (B ∩ S) A
  have ready (t : Star n) (ht : t ∈ stars) : Signal D {t.1} ∧ Signal D t.2 := by
    refine ⟨primary _,?_⟩
    rcases List.mem_append.mp ht with ha | hb
    · obtain ⟨z,_,rfl⟩ := List.mem_map.mp ha
      exact signals b (by simp [inputs])
    · obtain ⟨z,_,rfl⟩ := List.mem_map.mp hb
      exact signals a (by simp [inputs])
  obtain ⟨H,r,_,used,result⟩ := add_many stars D o ho ready
  obtain ⟨E,aoE,sizeE,output,flat⟩ := reify H r
  have cost := budget a b inputs
  have length : stars.length = (A ∩ S).card + (B ∩ S).card := by simp [stars,centres]
  change 2*((A ∩ S).card+(B ∩ S).card) ≤ _ at cost
  rw [length] at used
  refine ⟨E,aoE,by omega,?_,flat⟩
  funext x
  apply Bool.eq_iff_iff.mpr
  change E.eval (List.ofFn x) = true ↔ _
  rw [output,result,sem]
  have cover (y : Fin n → Bool) : graphFun G ∅ y = true ↔ cut n g C y C.output = true ∨ Hits A y ∧ Hits B y ∧ Hits S y := by
    rw [routed,rect]
    exact or_congr_right and_assoc
  rw [two_star_cover ao disj cover x]
  apply or_congr_right
  rw [← centre_fires (A ∩ S) B, ← centre_fires (B ∩ S) A]
  constructor
  · rintro ⟨t,ht,fire⟩
    exact (List.mem_append.mp ht).imp (fun h => ⟨t,h,fire⟩) (fun h => ⟨t,h,fire⟩)
  · rintro (⟨t,h,fire⟩ | ⟨t,h,fire⟩)
    · exact ⟨t,List.mem_append.mpr (.inl h),fire⟩
    · exact ⟨t,List.mem_append.mpr (.inr h),fire⟩

lemma single_mixed_reader {z : Fin n} (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (hg : g < C.gates.length) (ag : (gateAt C g).op = GateOp.and)
    (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (units : ∀ u : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput u) = false)
    (live : PEqualNP.Core.InOutputCone n C g) (c4 : NoFourCycle G)
    (bip : ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v)
    (mix : Reach n C z (n+j)) (opJ : (gateAt C j).op = GateOp.or)
    (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j) : Goal G C := by
  classical
  have fromCut (x : Fin n → Bool) (h : cut n g C x C.output = true) : graphFun G ∅ x = true :=
    (congrFun computes x).symm.trans (cut_sub ao x _ h)
  by_cases loss : ∃ x, graphFun G ∅ x = true ∧ cut n g C x C.output ≠ true
  · let S := (routes G C g).filter (G.Adj z)
    have lost := mixed_loss ao computes form ag dirty unique mix opJ only
    have cover (x : Fin n → Bool) : graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨
        (gateVal n C g x = true ∧ Hits S x) := by
      constructor
      · intro on
        by_cases kept : cut n g C x C.output = true
        · exact Or.inl kept
        · obtain ⟨gOn,_,v,hv,adj,xv⟩ := lost x on kept
          exact Or.inr ⟨gOn,v,Finset.mem_filter.mpr ⟨hv,adj⟩,xv⟩
      · rintro (h | ⟨on,v,hv,xv⟩)
        · exact fromCut x h
        · exact (route_iff.mp (Finset.mem_filter.mp hv).1) x on xv
    apply restore_subset ao computes form hg ag dirty unique units S cover
    obtain ⟨a,b,ins,_,_,_,rect⟩ := dirty_rectangle_at ao hg ag form unique units
    intro c d inputs
    obtain ⟨rfl,rfl⟩ : a=c ∧ b=d := by simpa using ins.symm.trans inputs
    obtain ⟨x,hx,off⟩ := loss
    obtain ⟨on,zOff,_⟩ := lost x hx off
    have diff {U : Finset (Fin n)} (hit : Hits U x) : ∃ u ∈ U, u ≠ z := by
      obtain ⟨t,ht,xt⟩ := hit
      exact ⟨t,ht,fun e => zOff (e ▸ xt)⟩
    obtain ⟨left,right⟩ := route_complete (R n C a) (R n C b) S
      (fun y ha hb hs => (cover y).mpr (Or.inr ⟨(rect y).mpr ⟨ha,hb⟩,hs⟩))
    have small := centre_budget c4 bip (fun u hu => (Finset.mem_filter.mp hu).2) left right
      (diff ((rect x).mp on).1) (diff ((rect x).mp on).2)
    change (R n C a ∩ S).card + (R n C b ∩ S).card ≤ 1 at small
    have paid := two_credits computes live dirty
    omega
  · apply restore_subset ao computes form hg ag dirty unique units ∅
    · intro x
      simpa [Hits] using (show graphFun G ∅ x = true ↔ cut n g C x C.output = true from
        ⟨fun h => Classical.byContradiction (fun off => loss ⟨x,h,off⟩),fromCut x⟩)
    · simp

end Reader3700

namespace Unique3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Restore3700 Reader3700
variable {n g j : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma no_alias (least : IsLeastAO G C) (hj : j < C.size) {t : ℕ} (ht : t < n+j)
    (same : ∀ x : Fin n → Bool, W n C x (n+j) = W n C x t) : False := by
  let D := BypassTheory.bypass n C j t
  have legal : IsAO2 n D := by
    refine ⟨?_,BypassTheory.bypass_readsBack ht least.1.2.1,?_⟩
    · intro d hd
      obtain ⟨d',mem,e,_⟩ := BypassTheory.bypass_mem d hd
      exact e ▸ least.1.1 d' mem
    · intro d hd
      obtain ⟨d',mem,_,e⟩ := BypassTheory.bypass_mem d hd
      exact e.trans (least.1.2.2 d' mem)
  have eq : circuitFun n D = circuitFun n C := by
    funext x
    exact BypassTheory.bypass_eval_eq (List.length_ofFn ..)
      (fun k hk => least.1.1 _ (gate_mem hk)) hj (.inl ht) (same x)
  have minimal := least.2.2 D legal (eq.trans least.2.1)
  change C.gates.length ≤ (BypassTheory.bypass n C j t).gates.length at minimal
  rw [BypassTheory.bypass_length] at minimal
  change j < C.gates.length at hj
  omega

lemma only_dirty_source (ao : IsAO2 n C) (fixed : IsLiftFixedPoint G C)
    (live : ∀ k < C.size, InOutputCone n C k)
    (unique : ∀ k < C.size, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (w : ℕ) (hw : w < n+C.size) (none : ∀ z : Fin n, ¬ Reach n C z w)
    (dirty : ¬ ∀ x : Fin n → Bool, W n C x w = true → graphFun G ∅ x = true)
    (x : Fin n → Bool) (on : W n C x w = true) : gateVal n C g x = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases primary : w < n
    · exact (none ⟨w,primary⟩ (reach_refl n C ⟨w,primary⟩)).elim
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have hk : k < C.size := by omega
    rcases ao.1 _ (gate_mem hk) with ak | ok
    · by_cases kg : k=g
      · exact kg ▸ on
      · exact (dirty (unique k hk ak kg)).elim
    · obtain ⟨t,mem,lt,active⟩ := (W_or_iff n C x k hk ok).mp on
      apply ih t lt (by omega) (fun z path => none z (reach_step n C z k hk ok t mem lt path)) _ active
      intro implicant
      have imp : IsImpWire G C t := ⟨implicant,x,active⟩
      obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 _ (gate_mem hk))
      simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with rfl | rfl
      · apply dirty (or_above_implicant (b:=0) fixed (live k hk) ok ?_)
        simpa [opnd,ins] using imp
      · apply dirty (or_above_implicant (b:=1) fixed (live k hk) ok ?_)
        simpa [opnd,ins] using imp

lemma reader_has_primary (least : IsLeastAO G C) (fixed : IsLiftFixedPoint G C)
    (live : ∀ k < C.size, InOutputCone n C k)
    (unique : ∀ k < C.size, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (dirty : ¬ BelowF G C g) (hj : j < C.size) (opJ : (gateAt C j).op = GateOp.or)
    (member : n+g ∈ (gateAt C j).inputs) : ∃ z : Fin n, Reach n C z (n+j) := by
  by_contra! none
  have lt := least.1.2.1 j hj _ member
  have upward (x : Fin n → Bool) (on : gateVal n C g x = true) : W n C x (n+j) = true :=
    (W_or_iff n C x j hj opJ).mpr ⟨_,member,lt,on⟩
  have bad : ¬ ∀ x : Fin n → Bool, W n C x (n+j) = true → graphFun G ∅ x = true :=
    fun clean => dirty (fun x hx => clean x (upward x hx))
  apply no_alias least hj lt
  intro x
  apply Bool.eq_iff_iff.mpr
  exact ⟨only_dirty_source least.1 fixed live unique _ (by omega) none bad x,upward x⟩

lemma single_or (least : IsLeastAO G C) (fixed : IsLiftFixedPoint G C)
    (live : ∀ k < C.size, InOutputCone n C k) (form : TopForm G C)
    (hg : g < C.size) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ k < C.size, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (units : ∀ u : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput u) = false)
    (c4 : NoFourCycle G) (bip : ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v)
    (hj : j < C.size) (opJ : (gateAt C j).op = GateOp.or) (member : n+g ∈ (gateAt C j).inputs)
    (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j) : Goal G C := by
  obtain ⟨z,mix⟩ := reader_has_primary least fixed live unique dirty hj opJ member
  exact single_mixed_reader least.1 least.2.1 form hg ag dirty unique units (live g hg) c4 bip mix opJ only

end Unique3700

namespace Direct3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700
variable {n g j : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma no_or_exit {w : ℕ} (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → (gateAt C k).op ≠ GateOp.or)
    (path : OrFrom n C (n+g) w) : w=n+g := by
  apply path (fun t => t=n+g) rfl
  rintro k hk op t ht _ rfl
  exact (only k hk ht op).elim

lemma direct_loss {q : ℕ} (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (form : TopForm G C) (unique : ∀ i < C.size, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (opJ : (gateAt C j).op = GateOp.and) (inputs : (gateAt C j).inputs.Perm [n+g,q])
    (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j)
    (x : Fin n → Bool) (on : graphFun G ∅ x = true) (off : cut n g C x C.output ≠ true) :
    gateVal n C g x = true ∧ Hits (R n C q) x := by
  have eq (y : Fin n → Bool) : W n C y C.output = graphFun G ∅ y := congrFun computes y
  obtain ⟨k,hk,ak,out,before,after⟩ := trace_loss ao ag x C.output ((eq x).trans on) off
  have clean : BelowF G C k := fun y hy => (eq y).symm.trans (orFrom_val out y hy)
  have ne : k ≠ g := fun e => dirty (e ▸ clean)
  obtain ⟨p,t,perm,nt,sem⟩ := clean_top_expansion ao form unique dirty hk ak clean
  obtain ⟨left,v,hv,xv⟩ := (sem x).mp before
  rcases left with ⟨u,hu,xu⟩ | ⟨gp,gOn⟩
  · exfalso
    apply after ((cut_and ao x hk ne ak).mpr ?_)
    intro i hi
    rcases List.mem_cons.mp (perm.mem_iff.mp hi) with rfl | h
    · exact survives ao ag x xu ((mem_R ..).mp hu)
    · exact (List.mem_singleton.mp h) ▸ survives ao ag x xv ((mem_R ..).mp hv)
  · have e := no_or_exit (fun k hk h e => by rw [only k hk h,opJ] at e; contradiction) gp
    subst p
    have kj := only k hk (perm.mem_iff.mpr (by simp))
    subst k
    have id : t=q := by
      have counts := ((perm.symm.trans inputs).erase (n+g))
      simpa using counts
    exact ⟨gOn,v,id ▸ hv,xv⟩

lemma singleton_bad_rectangle {a : Fin n} {B Y : Finset (Fin n)} (c4 : NoFourCycle G)
    (sound : ∀ x : Fin n → Bool, x a = true → Hits B x → Hits Y x → graphFun G ∅ x = true) :
    let bad := fun U : Finset (Fin n) => U.filter (fun t => ¬ G.Adj a t)
    (∀ b ∈ bad B, ∀ y ∈ bad Y, G.Adj b y) ∧ ((bad B).card ≤ 1 ∨ (bad Y).card ≤ 1) := by
  dsimp only
  let bad := fun U : Finset (Fin n) => U.filter (fun t => ¬ G.Adj a t)
  have rect (b : Fin n) (hb : b ∈ bad B) (y : Fin n) (hy : y ∈ bad Y) : G.Adj b y := by
    have edge := triple_edge (a:=a) (b:=b) (y:=y) (sound _ (by simp)
      ⟨b,(Finset.mem_filter.mp hb).1,by simp⟩ ⟨y,(Finset.mem_filter.mp hy).1,by simp⟩)
    exact (edge.resolve_left (Finset.mem_filter.mp hb).2).resolve_left (Finset.mem_filter.mp hy).2
  refine ⟨rect,?_⟩
  by_cases h : 1 < (bad Y).card
  · exact Or.inl (star_centres c4 h rect)
  · exact Or.inr (Nat.le_of_not_gt h)

lemma cut_network {n g : ℕ} {C : Circuit} (ao : IsAO2 n C)
    (stack : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → ∀ i,
      InCone n C i j → (gateAt C i).op = GateOp.and → i = g) :
    ∃ D : Network n, ∃ o : Option ℕ, (∀ t ∈ o, t < bound D) ∧
      D.gates.length + ((Finset.range C.size).filter (charged n g C)).card ≤ C.size ∧
      (∀ x : Fin n → Bool, readOut D x o = cut n g C x C.output) ∧
      (∀ w (S : Finset (Fin n)), S.Nonempty → OnlyAnd n C g w →
        (∀ x, cut n g C x w = true ↔ Hits S x) → Signal D S) := by
  let p := build n g C C.size
  obtain ⟨Q,mk,safe⟩ := marked_build ao (source_marks ao stack) C.size (le_refl _)
  obtain ⟨legal,valid⟩ := valid_build (g := g) ao C.size (le_refl _)
  let D : Network n := ⟨p.gates,Q,legal,mk⟩
  let o : Option ℕ := match p.wire C.output with | .inl _ => none | .inr t => some t
  have wire (x : Fin n → Bool) (w : ℕ) : LMeta616.statVal ((Circuit.mk D.gates 0).wires (List.ofFn x)) (p.wire w) = cut n g C x w := sound_build ao x C.size (le_refl _) w
  have signal (w : ℕ) (S : Finset (Fin n)) (nonempty : S.Nonempty) (pure : OnlyAnd n C g w)
      (sem : ∀ x : Fin n → Bool, cut n g C x w = true ↔ Hits S x) : Signal D S := by
    cases e : p.wire w with
    | inl v =>
      cases v with
      | true => exact (no_true (g := g) ao C.size (le_refl _) w e).elim
      | false =>
        obtain ⟨v,hv⟩ := nonempty
        have on := (sem (fun _ => true)).mpr ⟨v,hv,rfl⟩
        have h := wire (fun _ => true) w
        rw [e,on] at h
        contradiction
    | inr t =>
      have boundT := valid w
      have pureT := safe w pure
      change LMeta616.statValid (bound D) (p.wire w) at boundT
      change Safe Q (p.wire w) at pureT
      rw [e] at boundT pureT
      refine ⟨t,boundT,pureT,?_⟩
      intro x
      have eq := wire x w
      rw [e] at eq
      exact (show bit D x t = cut n g C x w from eq) ▸ sem x
  refine ⟨D,o,?_,gate_budget ao C.size (le_refl _),?_,signal⟩
  · intro t mem
    cases e : p.wire C.output with
    | inl v => simp [o,e] at mem
    | inr w =>
      have val := valid C.output
      change LMeta616.statValid (bound D) (p.wire C.output) at val
      rw [e] at val
      simp [o,e] at mem
      exact mem ▸ val
  · intro x
    have eq := wire x C.output
    cases e : p.wire C.output with
    | inl v =>
      cases v with
      | true => exact (no_true (g := g) ao C.size (le_refl _) C.output e).elim
      | false => simpa [o,e,readOut,LMeta616.statVal] using eq
    | inr t => simpa [o,e,readOut,LMeta616.statVal,bit,W] using eq

lemma residual_support (ao : IsAO2 n C) (ag : (gateAt C g).op = GateOp.and)
    {w : ℕ} (valid : w < n+C.size) (only : OnlyAnd n C g w) (noPath : ¬ OrFrom n C (n+g) w)
    (x : Fin n → Bool) : cut n g C x w = true ↔ Hits (R n C w) x := by
  constructor
  · intro h
    rcases (operand_expansion ao valid only x).mp (cut_sub ao x w h) with h | ⟨gp,_⟩
    · exact h
    · exact (noPath gp).elim
  · rintro ⟨u,hu,xu⟩
    exact survives ao ag x xu ((mem_R ..).mp hu)

lemma direct_safe_rectangle {p q : ℕ} (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (hg : g < C.size) (hj : j < C.size) (ag : (gateAt C g).op = GateOp.and)
    (dirty : ¬ BelowF G C g) (form : TopForm G C)
    (unique : ∀ i < C.size, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (opJ : (gateAt C j).op = GateOp.and) (inputs : (gateAt C j).inputs.Perm [n+g,q])
    (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j)
    (memP : p ∈ (gateAt C g).inputs) (live : InOutputCone n C g)
    (sound : ∀ u ∈ R n C p, ∀ v ∈ R n C q, G.Adj u v) : Goal G C := by
  have stack (k : ℕ) (hk : k<C.size) (ak : (gateAt C k).op = GateOp.and) (i : ℕ)
      (h : InCone n C i k) (ai : (gateAt C i).op = GateOp.and) :=
    only_dirty_below_and form unique (lt_trans (inCone_lt n C k hk i h) hk) hk ai ak h
  have ngmem : n+g ∈ (gateAt C j).inputs := inputs.mem_iff.mpr (by simp)
  have qmem : q ∈ (gateAt C j).inputs := inputs.mem_iff.mpr (by simp)
  have gj : g<j := by have := ao.2.1 j hj _ ngmem; omega
  have npq : ¬ OrFrom n C (n+g) q := by
    intro path
    apply dirty
    intro x gx
    apply unique j hj opJ (Nat.ne_of_gt gj) x
    apply (W_and_iff n C x j hj opJ).mpr
    intro t ht
    refine ⟨ao.2.1 j hj t ht,?_⟩
    rcases List.mem_cons.mp (inputs.mem_iff.mp ht) with rfl | h
    · exact gx
    · exact (List.mem_singleton.mp h) ▸ orFrom_val path x gx
  have npp : ¬ OrFrom n C (n+g) p := by
    intro path
    have bound := path (fun w => n+g ≤ w) (le_refl _) (fun k hk _ t _ lt e => le_trans e lt.le)
    have lt := ao.2.1 g hg p memP
    omega
  obtain ⟨D,o,ho,sz,out,wire⟩ := cut_network ao stack
  have sig {k t : ℕ} (hk : k<C.size) (ak : (gateAt C k).op = GateOp.and) (m : t ∈ (gateAt C k).inputs)
      (nn : ¬ OrFrom n C (n+g) t) : Signal D (R n C t) := by
    have valid : t < n+C.size := by have := ao.2.1 k hk t m; omega
    have onlyT := onlyAnd_operand ao hk m (stack k hk ak)
    have sem := operand_expansion ao valid onlyT (fun _ => true)
    have h := sem.mp (all_high ao valid)
    obtain ⟨v,hv,_⟩ := h.resolve_right (fun h => nn h.1)
    exact wire t _ ⟨v,hv⟩ onlyT (residual_support ao ag valid onlyT nn)
  obtain ⟨a,ha,pa,va⟩ := sig hg ag memP npp
  obtain ⟨b,hb,pb,vb⟩ := sig hj opJ qmem npq
  obtain ⟨H,r,hr,used,_,_,_,result⟩ := add_star D o ho a b ha hb pa pb
  obtain ⟨E,legal,size,sem,flat⟩ := reify H (some r)
  have paid := two_credits computes live dirty
  refine ⟨E,legal,by omega,?_,flat⟩
  funext x
  apply Bool.eq_iff_iff.mpr
  change E.eval (List.ofFn x) = true ↔ _
  rw [sem]
  change bit H x r = true ↔ _
  rw [result,Bool.or_eq_true,Bool.and_eq_true,out,va,vb]
  constructor
  · rintro (cutOn | ⟨⟨u,hu,xu⟩,v,hv,xv⟩)
    · exact (congrFun computes x).symm.trans (cut_sub ao x _ cutOn)
    · simpa [graphFun] using (show ∃ c d, G.Adj c d ∧ x c = true ∧ x d = true from ⟨u,v,sound u hu v hv,xu,xv⟩)
  · intro yes
    by_cases stays : cut n g C x C.output = true
    · exact Or.inl stays
    obtain ⟨gx,hq⟩ := direct_loss ao computes ag dirty form unique opJ inputs only x yes stays
    have px := ((W_and_iff n C x g hg ag).mp gx p memP).2
    have valid : p < n+C.size := by have := ao.2.1 g hg p memP; omega
    have expanded := (operand_expansion ao valid (onlyAnd_operand ao hg memP (stack g hg ag)) x).mp px
    exact Or.inr ⟨expanded.resolve_right (fun t => npp t.1),hq⟩

lemma other_top_excludes_edge {k w : ℕ} {u v : Fin n} (ao : IsAO2 n C)
    (form : TopForm G C) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.size, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (opJ : (gateAt C j).op = GateOp.and) (only : ∀ i < C.size, n+g ∈ (gateAt C i).inputs → i=j)
    (hk : k<C.size) (ak : (gateAt C k).op = GateOp.and) (clean : BelowF G C k) (kj : k ≠ j)
    (hw : w ∈ (gateAt C k).inputs) (hu : u ∈ R n C w) (hv : v ∈ R n C w) (edge : G.Adj u v)
    (s : Fin n → Bool) (bip : ∀ u v, G.Adj u v → s u ≠ s v) : False := by
  obtain ⟨p,q,perm,nq,sem⟩ := clean_top_expansion ao form unique dirty hk ak clean
  have np : ¬ OrFrom n C (n+g) p := by
    intro path
    have eq := no_or_exit (fun i hi m e => by rw [only i hi m,opJ] at e; contradiction) path
    apply kj (only k hk (perm.mem_iff.mpr (by simp [eq])))
  have full := (sem (fun _ => true)).mp (all_high ao (w:=n+k) (Nat.add_lt_add_left hk n))
  obtain ⟨a,ha,_⟩ := full.1.resolve_right (fun h => np h.1)
  obtain ⟨b,hb,_⟩ := full.2
  have cross (c : Fin n) (hc : c ∈ R n C p) (d : Fin n) (hd : d ∈ R n C q) : G.Adj c d := by
    apply (pair_edge c d).mp (clean _ ((sem _).mpr ?_))
    exact ⟨Or.inl ⟨c,hc,by simp [pairInput]⟩,d,hd,by simp [pairInput]⟩
  have impossible {z : Fin n} (uz : G.Adj u z) (vz : G.Adj v z) : False := by
    have h1 := bip u v edge
    have h2 := bip u z uz
    have h3 := bip v z vz
    revert h1 h2 h3
    generalize s u = i, s v = l, s z = m
    cases i <;> cases l <;> cases m <;> decide
  rcases List.mem_cons.mp (perm.mem_iff.mp hw) with rfl | h
  · exact impossible (cross _ hu b hb) (cross _ hv b hb)
  · obtain rfl := List.mem_singleton.mp h
    exact impossible (cross a ha _ hu).symm (cross a ha _ hv).symm

end Direct3700

namespace Isolate3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Cover3700 Direct3700
variable {n g j : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma propagate_live {d : ℕ} {P : ℕ → Prop} (live : InOutputCone n C d) (start : P (n+d))
    (step : ∀ k < C.size, ∀ w ∈ (gateAt C k).inputs, P w → P (n+k)) : P C.output := by
  obtain ⟨_,out | ⟨lo,path⟩⟩ := live
  · exact out ▸ start
  have bound : C.output-n < C.gates.length := by
    by_contra h
    have len : (cones n C).length = C.gates.length := by simp [cones,coneFold_length]
    have off := List.getD_eq_default (cones n C) ([] : List ℕ) (show (cones n C).length ≤ C.output-n by omega)
    unfold InCone at path
    rw [off] at path
    exact List.not_mem_nil path
  suffices walk : ∀ k < C.size, InCone n C d k → P (n+k) by
    simpa only [Nat.add_sub_of_le lo] using walk _ bound path
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk path
    obtain ⟨w,hw,lo,lt,prev⟩ := (inCone_iff n C d k hk).mp path
    apply step k hk w hw
    have eq : n+(w-n)=w := by omega
    rcases prev with h | h
    · exact eq ▸ (h ▸ start)
    · exact eq ▸ ih (w-n) (by omega) (by omega) h

lemma private_opposite {a b q : ℕ} {u v : Fin n} (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (dirty : ¬ BelowF G C g) (ag : (gateAt C g).op = GateOp.and)
    (unique : ∀ i < C.size, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (opJ : (gateAt C j).op = GateOp.and) (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j)
    (live : ∀ k < C.size, InOutputCone n C k) (ins : (gateAt C g).inputs = [a,b])
    (js : (gateAt C j).inputs.Perm [n+g,q]) (disj : Disjoint (R n C a) (R n C b))
    (ua : u ∈ R n C a) (vb : v ∈ R n C b) (uq : u ∈ R n C q) (vq : v ∈ R n C q) (edge : G.Adj u v)
    (s : Fin n → Bool) (bip : ∀ u v, G.Adj u v → s u ≠ s v) :
    ∀ k < C.size, q ∈ (gateAt C k).inputs → k=j := by
  have impossible {k w : ℕ} (hk : k<C.size) (ak : (gateAt C k).op = GateOp.and) (kj : k≠j)
      (m : w ∈ (gateAt C k).inputs) (uw : u ∈ R n C w) (vw : v ∈ R n C w) : False := by
    by_cases kg : k=g
    · subst k
      simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at m
      rcases m with rfl | rfl
      · exact Finset.disjoint_left.mp disj vw vb
      · exact Finset.disjoint_left.mp disj ua uw
    · exact other_top_excludes_edge ao form dirty unique opJ only hk ak (unique k hk ak kg) kj m uw vw edge s bip
  have notG : u ∉ R n C (n+g) := by
    intro h
    rcases reach_inv n C u _ ((mem_R ..).mp h) with eq | ⟨k,_,e,op,_⟩
    · have := u.isLt; omega
    · have kg : k=g := by omega
      rw [kg,ag] at op
      contradiction
  let P := fun w => q<w ∧ u ∈ R n C w ∧ v ∈ R n C w
  have orNext {k w : ℕ} (hk : k<C.size) (ok : (gateAt C k).op = GateOp.or) (m : w ∈ (gateAt C k).inputs)
      {z : Fin n} (zw : z ∈ R n C w) : z ∈ R n C (n+k) :=
    (mem_R ..).mpr (reach_step n C z k hk ok w m (ao.2.1 k hk w m) ((mem_R ..).mp zw))
  intro k hk mem
  by_contra kj
  rcases ao.1 _ (gate_mem hk) with ak | ok
  · exact impossible hk ak kj mem uq vq
  · have start : P (n+k) := ⟨ao.2.1 k hk q mem,orNext hk ok mem uq,orNext hk ok mem vq⟩
    have step (t : ℕ) (ht : t<C.size) (w : ℕ) (m : w ∈ (gateAt C t).inputs) (hw : P w) : P (n+t) := by
      rcases ao.1 _ (gate_mem ht) with at' | ot
      · by_cases tj : t=j
        · subst t
          rcases List.mem_cons.mp (js.mem_iff.mp m) with rfl | h
          · exact (notG hw.2.1).elim
          · exact ((Nat.ne_of_gt hw.1) (List.mem_singleton.mp h)).elim
        · exact (impossible ht at' tj m hw.2.1 hw.2.2).elim
      · exact ⟨lt_trans hw.1 (ao.2.1 t ht w m),orNext ht ot m hw.2.1,orNext ht ot m hw.2.2⟩
    have output := propagate_live (live k hk) start step
    have yu : pairInput u u u = true := by simp [pairInput]
    have accepted := reach_val n C u C.output (pairInput u u) yu ((mem_R ..).mp output.2.1)
    exact G.irrefl ((pair_edge u u).mp ((congrFun computes _).symm.trans accepted))

end Isolate3700

namespace Splice3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700
variable {n : ℕ} {C : Circuit}

lemma extend (D : Network n) (op : GateOp) (a b : ℕ) (ha : a < bound D) (hb : b < bound D)
    (hop : op = .and ∨ op = .or) (mark : Prop) (noAnd : op = .and → ¬ mark)
    (ready : op = .and ∨ mark → D.pure a ∧ D.pure b) :
    ∃ E : Network n, E.gates.length = D.gates.length+1 ∧
      (∀ w < bound D, D.pure w → E.pure w) ∧ (mark → E.pure (bound D)) ∧
      (∀ x : Fin n → Bool, ∀ w < bound D, bit E x w = bit D x w) ∧
      ∀ x : Fin n → Bool, bit E x (bound D) = op.eval [bit D x a,bit D x b] := by
  let H := append D op a b ha hb hop (fun h => ready (Or.inl h))
  let Q := Function.update D.pure (bound D) mark
  have marked : Marked n H.gates Q := by
    intro i hi
    by_cases lt : i < D.gates.length
    · have eq : gateAt ⟨H.gates,0⟩ i = gateAt ⟨D.gates,0⟩ i := List.getD_append _ _ _ _ lt
      simpa only [eq] using preserve_mark (q:=mark) D.marks D.ao i lt
    · have id : i=D.gates.length := by change i < (D.gates++[_]).length at hi; simp at hi; omega
      subst i
      have eq : gateAt ⟨H.gates,0⟩ D.gates.length = ⟨op,[a,b]⟩ := by simp [H,append,gateAt]
      simp only [eq,Q,Function.update_self]
      refine ⟨noAnd,?_⟩
      intro ok w mem
      rcases List.mem_cons.mp mem with rfl | h
      · simpa [Function.update_of_ne (Nat.ne_of_lt ha)] using (ready ok).1
      · obtain rfl := List.mem_singleton.mp h
        simpa [Function.update_of_ne (Nat.ne_of_lt hb)] using (ready ok).2
  let E : Network n := ⟨H.gates,Q,H.ao,marked⟩
  refine ⟨E,by simp [E,H,append],?_,?_,fun x w hw => old_bit D E rfl x hw,fun x => new_bit D E op rfl x⟩
  · intro w hw h; simpa [E,Q,Function.update_of_ne (Nat.ne_of_lt hw)] using h
  · simp [E,Q]

lemma two_stars (D : Network n) (a b c d : ℕ) (ha : a<bound D) (hb : b<bound D)
    (hc : c<bound D) (hd : d<bound D) (pa : D.pure a) (pb : D.pure b) (pc : D.pure c) (pd : D.pure d) :
    ∃ E : Network n, ∃ r < bound E, E.gates.length=D.gates.length+3 ∧
      (∀ w < bound D, D.pure w → E.pure w) ∧ (∀ x : Fin n → Bool, ∀ w < bound D, bit E x w = bit D x w) ∧
      ∀ x : Fin n → Bool, bit E x r = ((bit D x a && bit D x b) || (bit D x c && bit D x d)) := by
  obtain ⟨H,lH,mH,_,oldH,vH⟩ := extend D .and a b ha hb (.inl rfl) False (by simp) (fun _ => ⟨pa,pb⟩)
  have dh : bound D < bound H := Nat.add_lt_add_left (by omega) n
  obtain ⟨I,lI,mI,_,oldI,vI⟩ := extend H .and c d (hc.trans dh) (hd.trans dh) (.inl rfl) False (by simp)
      (fun _ => ⟨mH c hc pc,mH d hd pd⟩)
  have hi : bound H < bound I := Nat.add_lt_add_left (by omega) n
  obtain ⟨E,lE,mE,_,oldE,vE⟩ := extend I .or (bound D) (bound H) (dh.trans hi) hi (.inr rfl) False (by simp) (by simp)
  refine ⟨E,bound I,Nat.add_lt_add_left (by omega) n,by omega,?_,?_,?_⟩
  · intro w hw h; exact mE _ ((hw.trans dh).trans hi) (mI _ (hw.trans dh) (mH _ hw h))
  · intro x w hw; rw [oldE x w ((hw.trans dh).trans hi),oldI x w (hw.trans dh),oldH x w hw]
  · intro x; simp [vE,GateOp.eval,oldI x _ dh,vH,vI,oldH x c hc,oldH x d hd]

def Rep (D : Network n) (P : ℕ → Prop) (test : (Fin n → Bool) → Prop) (C : Circuit) (w : ℕ) :=
  ∃ t < bound D, (P w → D.pure t) ∧ ∀ x : Fin n → Bool, test x → bit D x t = W n C x w

lemma carry_rep {D E : Network n} {P test w} (grow : D.gates.length ≤ E.gates.length)
    (marks : ∀ t < bound D, D.pure t → E.pure t) (values : ∀ x : Fin n → Bool, ∀ t < bound D, bit E x t = bit D x t)
    (h : Rep D P test C w) : Rep E P test C w := by
  obtain ⟨t,ht,hm,hv⟩ := h
  exact ⟨t,lt_of_lt_of_le ht (Nat.add_le_add_left grow n),fun p => marks t ht (hm p),fun x ok => (values x t ht).trans (hv x ok)⟩

private def spent (k m : ℕ) := if k < m then 1 else 0
private lemma spent_step (k m : ℕ) : spent k (m+1) = spent k m + (if k=m then 1 else 0) := by
  unfold spent; split_ifs <;> omega

lemma splice {g h j a b c d : ℕ} {P : ℕ → Prop} {test : (Fin n → Bool) → Prop}
    (ao : IsAO2 n C) (mark : SourceMarks n g C P) (gj : g<j) (hj : h<j) (gh : g≠h) (endJ : j<C.size)
    (used : ∀ k < C.size, ∀ w ∈ (gateAt C k).inputs, w=n+g ∨ w=n+h → k=j)
    (out : C.output < n+C.size) (keptOut : C.output ≠ n+g ∧ C.output ≠ n+h)
    (wires : ∀ w ∈ [a,b,c,d], w<n+j ∧ w≠n+g ∧ w≠n+h ∧ P w) (top : ¬ P (n+j))
    (agrees : ∀ x : Fin n → Bool, test x → W n C x (n+j) =
        ((W n C x a && W n C x b) || (W n C x c && W n C x d))) :
    ∃ E : Circuit, IsAO2 n E ∧ E.size=C.size ∧ (∀ x, test x → circuitFun n E x = circuitFun n C x) ∧
      ∀ i < E.gates.length, ∀ k < E.gates.length, (gateAt E i).op = GateOp.and →
        (gateAt E k).op = GateOp.and → ¬ InCone n E i k := by
  let Keeps (D : Network n) (m : ℕ) := ∀ w < n+m, w≠n+g → w≠n+h → Rep D P test C w
  have run (m : ℕ) (hm : m≤C.size) : ∃ D : Network n, Keeps D m ∧
      D.gates.length + spent g m + spent h m = m + 2*spent j m := by
    induction m with
    | zero =>
      let D : Network n := ⟨[],fun _ => True,by
        refine ⟨?_,?_,?_⟩ <;> simp [AndOrOnly,ReadsBack],by intro k hk; simp at hk⟩
      refine ⟨D,?_,by simp [D,spent]⟩
      intro w hw _ _
      have lt : w<n := by simpa using hw
      exact ⟨w,lt,by simp [D],fun x _ => (W_input n _ x w lt).trans (W_input n C x w lt).symm⟩
    | succ m ih =>
      obtain ⟨D,old,count⟩ := ih (by omega)
      have hm' : m<C.size := hm
      rw [spent_step,spent_step,spent_step]
      by_cases erased : m=g ∨ m=h
      · refine ⟨D,?_,?_⟩
        · intro w hw wg wh
          exact old w (by rcases erased with rfl | rfl <;> omega) wg wh
        · rcases erased with rfl | rfl <;> split_ifs <;> omega
      have mg : m≠g := fun e => erased (Or.inl e)
      have mh : m≠h := fun e => erased (Or.inr e)
      have next {E : Network n} (grow : D.gates.length ≤ E.gates.length)
          (marks : ∀ t < bound D, D.pure t → E.pure t) (values : ∀ x : Fin n → Bool, ∀ t < bound D, bit E x t = bit D x t)
          (latest : Rep E P test C (n+m)) : Keeps E (m+1) := by
        intro w hw wg wh
        by_cases eq : w=n+m
        · exact eq ▸ latest
        · exact carry_rep grow marks values (old w (by omega) wg wh)
      by_cases mj : m=j
      · subst m
        have ref {w} (mem : w ∈ [a,b,c,d]) := old w (wires w mem).1 (wires w mem).2.1 (wires w mem).2.2.1
        obtain ⟨a',ha,pa,va⟩ := ref (w:=a) (by simp)
        obtain ⟨b',hb,pb,vb⟩ := ref (w:=b) (by simp)
        obtain ⟨c',hc,pc,vc⟩ := ref (w:=c) (by simp)
        obtain ⟨d',hd,pd,vd⟩ := ref (w:=d) (by simp)
        obtain ⟨E,r,hr,len,marks,vals,vr⟩ := two_stars D a' b' c' d' ha hb hc hd
          (pa (wires a (by simp)).2.2.2) (pb (wires b (by simp)).2.2.2)
          (pc (wires c (by simp)).2.2.2) (pd (wires d (by simp)).2.2.2)
        refine ⟨E,next (by omega) marks vals ⟨r,hr,fun h => (top h).elim,?_⟩,?_⟩
        · intro x t; rw [vr,va x t,vb x t,vc x t,vd x t,agrees x t]
        · split_ifs <;> omega
      · obtain ⟨u,v,ins⟩ := inputs_two ao hm'
        have ru {w} (mem : w ∈ (gateAt C m).inputs) : Rep D P test C w :=
          old w (ao.2.1 m hm' w mem) (fun e => mj (used m hm' w mem (Or.inl e)))
            (fun e => mj (used m hm' w mem (Or.inr e)))
        have um : u ∈ (gateAt C m).inputs := by simp [ins]
        have vm : v ∈ (gateAt C m).inputs := by simp [ins]
        obtain ⟨u',hu,pu,vu⟩ := ru um
        obtain ⟨v',hv,pv,vv⟩ := ru vm
        have props := mark m hm' mg
        obtain ⟨E,len,marks,pure,vals,vr⟩ := extend D (gateAt C m).op u' v' hu hv (ao.1 _ (gate_mem hm'))
          (P (n+m)) props.1 (fun h => ⟨pu (props.2 h u um),pv (props.2 h v vm)⟩)
        refine ⟨E,next (by omega) marks vals ⟨bound D,Nat.add_lt_add_left (by omega) n,pure,?_⟩,?_⟩
        · intro x t; rw [vr,vu x t,vv x t,W_gate n C x m hm']
          simp [ins,ao.2.1 m hm' u um,ao.2.1 m hm' v vm]
        · split_ifs <;> omega
  obtain ⟨D,sim,len⟩ := run C.size (le_refl _)
  obtain ⟨w,_,_,value⟩ := sim C.output out keptOut.1 keptOut.2
  obtain ⟨E,legal,num,output,flat⟩ := reify D (some w)
  simp only [spent,lt_trans gj endJ,lt_trans hj endJ,endJ,ite_true] at len
  exact ⟨E,legal,by omega,fun x hx => (output x).trans (value x hx),flat⟩

end Splice3700

namespace Double3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700 Direct3700 Isolate3700 Splice3700
variable {n g j : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def Test (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :=
  (∃ u v, x = pairInput u v) ∨ graphFun G ∅ x ≠ true

lemma wire_mono (ao : IsAO2 n C) {x y : Fin n → Bool} (le : ∀ u, x u = true → y u = true)
    (w : ℕ) : W n C x w = true → W n C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro on
    by_cases primary : w<n
    · rw [W_input n C y w primary]; apply le; simpa [W_input n C x w primary] using on
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by
      by_contra h
      exact Bool.noConfusion ((LMeta616.wires_oob C x (n+k) (by omega)).symm.trans on)
    rcases ao.1 _ (gate_mem hk) with ak | ok
    · apply (W_and_iff n C y k hk ak).mpr
      intro t ht
      obtain ⟨lt,act⟩ := (W_and_iff n C x k hk ak).mp on t ht
      exact ⟨lt,ih t lt act⟩
    · obtain ⟨t,ht,lt,act⟩ := (W_or_iff n C x k hk ok).mp on
      exact (W_or_iff n C y k hk ok).mpr ⟨t,ht,lt,ih t lt act⟩

lemma graph_of_tests (ao : IsAO2 n C) (eq : ∀ x, Test G x → circuitFun n C x = graphFun G ∅ x) :
    circuitFun n C = graphFun G ∅ := by
  funext x
  by_cases good : graphFun G ∅ x = true
  · obtain ⟨u,v,uv,xu,xv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by simpa [graphFun] using good
    have pair := (eq (pairInput u v) (Or.inl ⟨u,v,rfl⟩)).trans ((pair_edge u v).mpr uv)
    rw [good]
    apply wire_mono ao (x:=pairInput u v) _ C.output pair
    intro t ht
    rcases (show t=u ∨ t=v by simpa [pairInput] using ht) with rfl | rfl
    · exact xu
    · exact xv
  · exact eq x (Or.inr good)

lemma live_bounds (live : InOutputCone n C j) : n+j ≤ C.output ∧ C.output<n+C.size := by
  obtain ⟨hj,eq | ⟨lo,path⟩⟩ := live
  · exact ⟨eq.ge,eq ▸ Nat.add_lt_add_left hj n⟩
  · have hk : C.output-n < C.gates.length := by
      by_contra h
      have len : (cones n C).length = C.gates.length := by simp [cones,coneFold_length]
      have off := List.getD_eq_default (cones n C) ([] : List ℕ) (show (cones n C).length ≤ C.output-n by omega)
      unfold InCone at path; rw [off] at path; exact List.not_mem_nil path
    have lt := inCone_lt n C _ hk j path
    change _ ∧ C.output<n+C.gates.length
    omega

lemma double_reader {a b q : ℕ} {u v : Fin n} (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ k < C.size, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (live : ∀ k < C.size, InOutputCone n C k) (c4 : NoFourCycle G) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v) (hj : j<C.size) (aj : (gateAt C j).op = GateOp.and)
    (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j) (js : (gateAt C j).inputs.Perm [n+g,q])
    (ins : (gateAt C g).inputs = [a,b]) (disj : Disjoint (R n C a) (R n C b))
    (ua : u ∈ R n C a) (vb : v ∈ R n C b) (uq : u ∈ R n C q) (vq : v ∈ R n C q) : Goal G C := by
  let A := R n C a
  let B := R n C b
  let Y := R n C q
  have gm : n+g ∈ (gateAt C j).inputs := js.mem_iff.mpr (by simp)
  have qm : q ∈ (gateAt C j).inputs := js.mem_iff.mpr (by simp)
  have am : a ∈ (gateAt C g).inputs := by simp [ins]
  have bm : b ∈ (gateAt C g).inputs := by simp [ins]
  have gj : g<j := by have := ao.2.1 j hj _ gm; omega
  have clean := unique j hj aj (Nat.ne_of_gt gj)
  have stack (k : ℕ) (hk : k<C.size) (ak : (gateAt C k).op = GateOp.and) (i : ℕ)
      (h : InCone n C i k) (ai : (gateAt C i).op = GateOp.and) :=
    only_dirty_below_and form unique (lt_trans (inCone_lt n C k hk i h) hk) hk ai ak h
  have pure (i : ℕ) (h : InCone n C i g) (ai : (gateAt C i).op = GateOp.and) : False :=
    (Nat.ne_of_lt (inCone_lt n C g hg i h)) (stack g hg ag i h ai)
  have aSem (x : Fin n → Bool) := pure_operand ao hg pure am x
  have bSem (x : Fin n → Bool) := pure_operand ao hg pure bm x
  have gSem (x : Fin n → Bool) : gateVal n C g x = true ↔ Hits A x ∧ Hits B x := by
    change W n C x (n+g) = true ↔ _
    rw [W_and n C x g hg ag a b ins (ao.2.1 g hg a am) (ao.2.1 g hg b bm),Bool.and_eq_true,aSem,bSem]; rfl
  have jSem (x : Fin n → Bool) : gateVal n C j x = true ↔ gateVal n C g x = true ∧ W n C x q = true := by
    rw [show gateVal n C j x = W n C x (n+j) from rfl,W_and_iff n C x j hj aj]
    constructor
    · intro h; exact ⟨(h _ gm).2,(h _ qm).2⟩
    · intro ⟨gx,qx⟩ t ht
      refine ⟨ao.2.1 j hj t ht,?_⟩
      rcases List.mem_cons.mp (js.mem_iff.mp ht) with rfl | h
      · exact gx
      · exact (List.mem_singleton.mp h) ▸ qx
  have sound (x : Fin n → Bool) (ha : Hits A x) (hb : Hits B x) (hy : Hits Y x) : graphFun G ∅ x = true := by
    obtain ⟨z,hz,xz⟩ := hy
    exact clean x ((jSem x).mpr ⟨(gSem x).mpr ⟨ha,hb⟩, reach_val n C z q x xz ((mem_R ..).mp hz)⟩)
  obtain ⟨left,right⟩ := route_complete A B Y sound
  have uAll := left u (Finset.mem_inter.mpr ⟨ua,uq⟩)
  have vAll (i : Fin n) (hi : i∈A) := (right v (Finset.mem_inter.mpr ⟨vb,vq⟩) i hi).symm
  have uv := uAll v vb
  have privateQ := private_opposite ao computes form dirty ag unique aj only live ins js disj ua vb uq vq uv s bip
  have sem (x : Fin n → Bool) (test : Test G x) : W n C x (n+j) =
      ((W n C x u && W n C x b) || (W n C x v && W n C x a)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,Bool.and_eq_true,W_input n C x u.val u.isLt,W_input n C x v.val v.isLt,aSem,bSem]
    constructor
    · intro jx
      rcases test with ⟨k,l,rfl⟩ | off
      · have pair := (pair_edge k l).mp (clean _ jx)
        obtain ⟨ha,hb⟩ := (gSem _).mp ((jSem _).mp jx).1
        have h1 := (hits_pair A k l).mp ha
        have h2 := (hits_pair B k l).mp hb
        have oriented {k l : Fin n} (ka : k∈A) (lb : l∈B) (kl : G.Adj k l) : k=u ∨ l=v :=
          (double_star c4 ua vb uAll vAll ka lb).mp kl
        rcases h1 with ka | la <;> rcases h2 with kb | lb
        · exact (Finset.disjoint_left.mp disj ka kb).elim
        · rcases oriented ka lb pair with rfl | rfl
          · exact Or.inl ⟨by simp [pairInput],hb⟩
          · exact Or.inr ⟨by simp [pairInput],ha⟩
        · rcases oriented la kb pair.symm with rfl | rfl
          · exact Or.inl ⟨by simp [pairInput],hb⟩
          · exact Or.inr ⟨by simp [pairInput],ha⟩
        · exact (Finset.disjoint_left.mp disj la lb).elim
      · exact (off (clean _ jx)).elim
    · rintro (⟨xu,hb⟩ | ⟨xv,ha⟩)
      · exact (jSem x).mpr ⟨(gSem x).mpr ⟨⟨u,ua,xu⟩,hb⟩,reach_val n C u q x xu ((mem_R ..).mp uq)⟩
      · exact (jSem x).mpr ⟨(gSem x).mpr ⟨ha,⟨v,vb,xv⟩⟩,reach_val n C v q x xv ((mem_R ..).mp vq)⟩
  have qgate : n≤q := by
    by_contra h
    have e {t : Fin n} (m : t ∈ R n C q) : q=t.val := by
      rcases reach_inv n C t q ((mem_R ..).mp m) with e | ⟨k,_,e,_⟩
      · exact e
      · omega
    exact G.irrefl ((show u=v from Fin.ext ((e uq).symm.trans (e vq))) ▸ uv)
  obtain ⟨h,qeq⟩ : ∃ h, q=n+h := ⟨q-n,by omega⟩
  have hj' : h<j := by have := ao.2.1 j hj q qm; omega
  have gh : g≠h := by
    rintro rfl
    rcases reach_inv n C u q ((mem_R ..).mp uq) with eq | ⟨k,_,eq,op,_⟩
    · have := u.isLt; omega
    · have kg : k=g := by omega
      rw [kg,ag] at op; contradiction
  have used (k : ℕ) (hk : k<C.size) (w : ℕ) (mem : w ∈ (gateAt C k).inputs) (e : w=n+g ∨ w=n+h) : k=j := by
    rcases e with e | e
    · exact only k hk (e ▸ mem)
    · exact privateQ k hk ((e.trans qeq.symm) ▸ mem)
  have wires : ∀ w ∈ [u.val,b,v.val,a], w<n+j ∧ w≠n+g ∧ w≠n+h ∧ OnlyAnd n C g w := by
    have input (t : Fin n) : t.val<n+j ∧ t.val≠n+g ∧ t.val≠n+h ∧ OnlyAnd n C g t.val := by
      have lt := t.isLt; refine ⟨by omega,by omega,by omega,?_⟩; intro k eq; omega
    have operand (w : ℕ) (m : w ∈ (gateAt C g).inputs) : w<n+j ∧ w≠n+g ∧ w≠n+h ∧ OnlyAnd n C g w := by
      have lo := ao.2.1 g hg w m
      exact ⟨by omega,by omega,fun e => (Nat.ne_of_lt gj) (used g hg w m (Or.inr e)),onlyAnd_operand ao hg m (stack g hg ag)⟩
    intro w m
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m
    rcases m with rfl | rfl | rfl | rfl
    · exact input _
    · exact operand _ bm
    · exact input _
    · exact operand _ am
  have bounds := live_bounds (live j hj)
  have unmarked : ¬ OnlyAnd n C g (n+j) := fun mark => (Nat.ne_of_gt gj) (mark j rfl j (Or.inl rfl) aj)
  obtain ⟨E,legal,len,tests,flat⟩ := splice ao (source_marks ao stack) gj hj' gh hj used bounds.2
    ⟨by omega,by omega⟩ wires unmarked sem
  exact ⟨E,legal,len.le,graph_of_tests legal (fun x t => (tests x t).trans (congrFun computes x)),flat⟩

end Double3700

namespace DirectLarge3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Cover3700 Restore3700 Reader3700 Direct3700 Double3700
variable {n g j : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma direct_cover {q : ℕ} (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ k < C.size, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (hj : j<C.size) (aj : (gateAt C j).op = GateOp.and) (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j)
    (js : (gateAt C j).inputs.Perm [n+g,q]) (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨ gateVal n C g x = true ∧ Hits (R n C q) x := by
  constructor
  · intro on
    by_cases kept : cut n g C x C.output = true
    · exact Or.inl kept
    · exact Or.inr (direct_loss ao computes ag dirty form unique aj js only x on kept)
  · rintro (h | ⟨gx,z,hz,xz⟩)
    · exact (congrFun computes x).symm.trans (cut_sub ao x _ h)
    · have m : n+g ∈ (gateAt C j).inputs := js.mem_iff.mpr (by simp)
      have gj : g<j := by have := ao.2.1 j hj _ m; omega
      apply unique j hj aj (Nat.ne_of_gt gj) x ((W_and_iff n C x j hj aj).mpr ?_)
      intro t ht; refine ⟨ao.2.1 j hj t ht,?_⟩
      rcases List.mem_cons.mp (js.mem_iff.mp ht) with rfl | h
      · exact gx
      · exact (List.mem_singleton.mp h) ▸ reach_val n C z q x xz ((mem_R ..).mp hz)

lemma direct_small_centres {q : ℕ} (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ k < C.size, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (units : ∀ v : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput v) = false)
    (live : ∀ k < C.size, InOutputCone n C k) (c4 : NoFourCycle G) (s : Fin n → Bool)
    (bip : ∀ u v, G.Adj u v → s u ≠ s v) (hj : j<C.size) (aj : (gateAt C j).op = GateOp.and)
    (only : ∀ k < C.size, n+g ∈ (gateAt C k).inputs → k=j) (js : (gateAt C j).inputs.Perm [n+g,q])
    (small : (∀ w ∈ (gateAt C g).inputs, 1 < (R n C w).card) ∨
      (∀ w ∈ (gateAt C g).inputs, (R n C w ∩ R n C q).card ≤ 1)) : Goal G C := by
  obtain ⟨a,b,ins,_,_,disj,rect⟩ := dirty_rectangle_at ao hg ag form unique units
  let A := R n C a
  let B := R n C b
  let Y := R n C q
  have am : a ∈ (gateAt C g).inputs := by simp [ins]
  have bm : b ∈ (gateAt C g).inputs := by simp [ins]
  have cover := direct_cover ao computes form ag dirty unique hj aj only js
  obtain ⟨left,right⟩ := route_complete A B Y (fun x ha hb hy => (cover x).mpr (Or.inr ⟨(rect x).mpr ⟨ha,hb⟩,hy⟩))
  have cards : (A ∩ Y).card ≤ 1 ∧ (B ∩ Y).card ≤ 1 := by
    rcases small with big | cap
    · exact ⟨star_centres c4 (big b bm) left,star_centres c4 (big a am) right⟩
    · exact ⟨cap a am,cap b bm⟩
  by_cases both : (A ∩ Y).Nonempty ∧ (B ∩ Y).Nonempty
  · obtain ⟨⟨u,hu⟩,v,hv⟩ := both
    obtain ⟨ua,uq⟩ := Finset.mem_inter.mp hu
    obtain ⟨vb,vq⟩ := Finset.mem_inter.mp hv
    exact double_reader ao computes form hg ag dirty unique live c4 s bip hj aj only js ins disj ua vb uq vq
  · apply restore_subset ao computes form hg ag dirty unique units Y cover
    intro d e eq
    obtain ⟨rfl,rfl⟩ : a=d ∧ b=e := by simpa using ins.symm.trans eq
    change 2*((A ∩ Y).card + (B ∩ Y).card) ≤ _
    have paid := two_credits computes (live g hg) dirty
    simp only [←Finset.card_pos] at both
    omega

end DirectLarge3700

namespace Two3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700 Unique3700 LMeta616
variable {n g j k : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma separate_readers (ao : IsAO2 n C) (form : TopForm G C) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.size, (gateAt C i).op = GateOp.and → i ≠ g → BelowF G C i)
    (hj : j<C.size) (aj : (gateAt C j).op = GateOp.and) (mj : n+g ∈ (gateAt C j).inputs)
    (hk : k<C.size) (mk : n+g ∈ (gateAt C k).inputs) : ¬ InCone n C k j := by
  intro inside
  have gj : g<j := by have := ao.2.1 j hj _ mj; omega
  have gk : g<k := by have := ao.2.1 k hk _ mk; omega
  have stack (i : ℕ) (h : InCone n C i j) (ai : (gateAt C i).op = GateOp.and) : i=g :=
    only_dirty_below_and form unique (lt_trans (inCone_lt n C j hj i h) hj) hj ai aj h
  have ko : (gateAt C k).op = GateOp.or := (ao.1 _ (gate_mem hk)).resolve_left (fun ak => (Nat.ne_of_gt gk) (stack k inside ak))
  obtain ⟨w,mem,lo,lt,sub⟩ := (inCone_iff n C k j hj).mp inside
  have propagate {t : ℕ} (only : OnlyAnd n C g (n+t)) (ht : t<C.size) (path : k=t ∨ InCone n C k t) : OrFrom n C (n+g) (n+t) := by
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      rcases path with rfl | path
      · exact fun P start step => step k hk ko _ mk (ao.2.1 k hk _ mk) start
      · have kt := inCone_lt n C t ht k path
        have ot := (ao.1 _ (gate_mem ht)).resolve_left (fun at' => (show t≠g by omega) (only t rfl t (.inl rfl) at'))
        obtain ⟨v,m,l,b,h⟩ := (inCone_iff n C k t ht).mp path
        have eq : n+(v-n)=v := by omega
        have ov := onlyAnd_operand ao ht m (fun i hi => only t rfl i (.inr hi))
        have p := ih (v-n) (by omega) (eq.symm ▸ ov) (by omega) h
        exact fun P start step => step t ht ot v m b (eq ▸ p P start step)
  have eq : n+(w-n)=w := by omega
  have pw := propagate (t:=w-n) (eq.symm ▸ onlyAnd_operand ao hj mem stack) (by omega) sub
  have kw : k ≤ w-n := sub.elim (fun e => e.le) (fun h => Nat.le_of_lt (inCone_lt n C _ (show w-n<C.size by omega) _ h))
  have diff : w ≠ n+g := by omega
  obtain ⟨a,b,ins⟩ := inputs_two ao hj
  have exhaust : ∀ v ∈ (gateAt C j).inputs, v=n+g ∨ v=w := by
    simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at mem mj ⊢
    grind
  apply dirty
  intro x gx
  apply unique j hj aj (Nat.ne_of_gt gj) x ((W_and_iff n C x j hj aj).mpr ?_)
  intro v mv
  refine ⟨ao.2.1 j hj v mv,?_⟩
  rcases exhaust v mv with rfl | rfl
  · exact gx
  · exact eq ▸ orFrom_val pw x gx

lemma no_shared_consumer (least : IsLeastAO G C) (hj : j<C.size) (aj : (gateAt C j).op = GateOp.and)
    (mj : n+g ∈ (gateAt C j).inputs) (hk : k<C.size) (mk : n+j ∈ (gateAt C k).inputs) : n+g ∉ (gateAt C k).inputs := by
  intro both
  have gj : g<j := by have := least.1.2.1 j hj _ mj; omega
  have exhaust : ∀ v ∈ (gateAt C k).inputs, v=n+g ∨ v=n+j := by
    obtain ⟨a,b,ins⟩ := inputs_two least.1 hk
    simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at mk both ⊢
    grind
  have below (x : Fin n → Bool) (jx : W n C x (n+j) = true) := ((W_and_iff n C x j hj aj).mp jx _ mj).2
  rcases least.1.1 _ (gate_mem hk) with ak | ok
  · apply no_alias least hk (least.1.2.1 k hk _ mk)
    intro x; apply Bool.eq_iff_iff.mpr
    refine ⟨fun h => ((W_and_iff n C x k hk ak).mp h _ mk).2, fun h => (W_and_iff n C x k hk ak).mpr ?_⟩
    intro t mt; refine ⟨least.1.2.1 k hk _ mt,?_⟩
    rcases exhaust t mt with rfl | rfl
    · exact below x h
    · exact h
  · apply no_alias least hk (least.1.2.1 k hk _ both)
    intro x; apply Bool.eq_iff_iff.mpr
    refine ⟨?_,fun h => (W_or_iff n C x k hk ok).mpr ⟨_,both,least.1.2.1 k hk _ both,h⟩⟩
    intro h; obtain ⟨t,mt,_,act⟩ := (W_or_iff n C x k hk ok).mp h
    rcases exhaust t mt with rfl | rfl
    · exact act
    · exact below x act

def skipped (n g : ℕ) (C : Circuit) (t : ℕ) : Bool := (emitted n g t C (build n g C t)).2.isNone

lemma count_skipped (n g : ℕ) (C : Circuit) (t : ℕ) :
    (build n g C t).gates.length + ((Finset.range t).filter (fun k => skipped n g C k = true)).card = t := by
  induction t with
  | zero => simp [build]
  | succ t ih =>
    rw [Finset.range_add_one,Finset.filter_insert]
    have fresh : t ∉ (Finset.range t).filter (fun k => skipped n g C k = true) := by simp
    cases e : (emitted n g t C (build n g C t)).2 <;>
      simp [build,skipped,e] at * <;> omega

lemma false_and_reader (ao : IsAO2 n C) (hj : j<C.size) (aj : (gateAt C j).op = GateOp.and)
    (mj : n+g ∈ (gateAt C j).inputs) {t : ℕ} (lt : j<t) : (build n g C t).wire (n+j) = .inl false := by
  have gj : g<j := by have := ao.2.1 j hj _ mj; omega
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases jt : j=t
    · subst t
      have ne := Nat.ne_of_gt gj
      obtain ⟨a,b,ins⟩ := inputs_two ao hj
      simp only [build,Function.update_self,emitted,ne,ite_false,ins,List.map_cons,List.map_nil,aj]
      simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at mj
      rcases mj with rfl | rfl
      · rw [masked n g C j gj]; rfl
      · rw [masked n g C j gj]; cases (build n g C j).wire a with
        | inl x => cases x <;> rfl
        | inr w => rfl
    · simp only [build,Function.update_of_ne (show n+j≠n+t by omega)]
      exact ih (by omega)

lemma extra_skip (ao : IsAO2 n C) (hj : j<C.size) (aj : (gateAt C j).op = GateOp.and)
    (mj : n+g ∈ (gateAt C j).inputs) (hk : k<C.size) (mk : n+j ∈ (gateAt C k).inputs) : skipped n g C k = true := by
  have jk : j<k := by have := ao.2.1 k hk _ mk; omega
  have gj : g<j := by have := ao.2.1 j hj _ mj; omega
  obtain ⟨a,b,ins⟩ := inputs_two ao hk
  have h := false_and_reader ao hj aj mj jk
  simp only [skipped,emitted,show k≠g by omega,ite_false,ins,List.map_cons,List.map_nil]
  rw [no_gate_with_false]; rfl
  simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at mk
  rcases mk with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

lemma two_with_and (least : IsLeastAO G C) (form : TopForm G C) (live : ∀ i<C.size, InOutputCone n C i)
    (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i < C.size, (gateAt C i).op = GateOp.and → i≠g → BelowF G C i)
    (units : ∀ v : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput v) = false)
    (c4 : NoFourCycle G) (big : ∀ w ∈ (gateAt C g).inputs, 1 < (R n C w).card)
    (hj : j<C.size) (aj : (gateAt C j).op = GateOp.and) (mj : n+g ∈ (gateAt C j).inputs)
    (hk : k<C.size) (kj : k≠j) (mk : n+g ∈ (gateAt C k).inputs) : Goal G C := by
  apply large_actual least.1 least.2.1 form hg ag dirty unique units c4 big
  have bounds := Double3700.live_bounds (live j hj)
  have gj : g<j := by have := least.1.2.1 j hj _ mj; omega
  have gk : g<k := by have := least.1.2.1 k hk _ mk; omega
  obtain ⟨_,jout | ⟨_,sub⟩⟩ := live j hj
  · exfalso
    obtain ⟨_,out | ⟨_,sub⟩⟩ := live k hk
    · omega
    · apply separate_readers least.1 form dirty unique hj aj mj hk mk
      have eq : C.output-n=j := by omega
      rwa [eq] at sub
  · obtain ⟨r,hr,jr,mr⟩ := has_reader (C:=C) (show C.output-n<C.size by omega) sub
    have rk : r≠k := fun e => no_shared_consumer least hj aj mj hr mr (e ▸ mk)
    let S := (Finset.range C.size).filter (fun t => skipped n g C t = true)
    have old {i : ℕ} (hi : i<C.size) (c : charged n g C i) : i ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,by simp [skipped,no_emit least.1 hi c]⟩
    have rm : r∈S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,extra_skip least.1 hj aj mj hr mr⟩
    have sub4 : ({g,j,k,r} : Finset ℕ) ⊆ S := by
      intro t ht; simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact old hg (.inl rfl)
      · exact old hj (.inr mj)
      · exact old hk (.inr mk)
      · exact rm
    have card := Finset.card_le_card sub4
    have e4 : ({g,j,k,r} : Finset ℕ).card = 4 := by simp [Finset.card_insert_of_notMem,show g≠j by omega,show g≠k by omega,show g≠r by omega,Ne.symm kj,show j≠r by omega,Ne.symm rk]
    rw [e4] at card
    have exactSize := count_skipped n g C C.size
    change (build n g C C.size).gates.length + S.card = C.size at exactSize
    omega

end Two3700

namespace Arm3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700 Reader3700 Unique3700
variable {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma routed_neighbour_unique {A B S : Finset (Fin n)} {u v a z : Fin n}
    (s : Fin n → Bool) (bip : ∀ i j, G.Adj i j → s i ≠ s j) (c4 : NoFourCycle G)
    (sound : ∀ x, Hits A x → Hits B x → Hits S x → graphFun G ∅ x = true)
    (ua : u∈A) (vb : v∈B) (ub : ∀ i∈B, G.Adj u i) (va : ∀ i∈A, G.Adj i v)
    (aa : a∈A) (au : a≠u) (az : a≠z) (zv : G.Adj z v) (big : 1<B.card)
    {w : Fin n} (ws : w∈S) (zw : G.Adj z w) : w=v := by
  obtain ⟨b,hb,bv⟩ : ∃ b∈B, b≠v := by
    by_contra! h
    have small : B.card ≤ 1 := Finset.card_le_one.mpr (fun b hb c hc => (h b hb).trans (h c hc).symm)
    omega
  have ab : ¬ G.Adj a b := fun e => ((double_star c4 ua vb ub va aa hb).mp e).elim au bv
  have ub' := bip _ _ (ub b hb)
  have uv := bip _ _ (ub v vb)
  have zv' := bip _ _ zv
  have zw' := bip _ _ zw
  have same : s b = s w := by
    revert ub' uv zv' zw'; generalize s b = t, s u = m, s v = h, s z = p, s w = q
    cases t <;> cases m <;> cases h <;> cases p <;> cases q <;> decide
  have on := sound (fun t => decide (t=a ∨ t=b ∨ t=w)) ⟨a,aa,by simp⟩ ⟨b,hb,by simp⟩ ⟨w,ws,by simp⟩
  have aw := ((triple_edge on).resolve_left ab).resolve_right (fun e => bip _ _ e same)
  exact common_neighbour_unique c4 az aw zw (va a aa) zv

lemma or_first {w : ℕ} (src : OrFrom n C (n+g) w) : w=n+g ∨ ∃ j<C.size, (gateAt C j).op = GateOp.or ∧
    n+g ∈ (gateAt C j).inputs ∧ OrFrom n C (n+j) w := by
  apply src _ (.inl rfl)
  intro k hk ok t mt lt h
  rcases h with rfl | ⟨j,hj,oj,mj,path⟩
  · exact .inr ⟨k,hk,ok,mt,fun _ h _ => h⟩
  · exact .inr ⟨j,hj,oj,mj,fun P start step => step k hk ok t mt lt (path P start step)⟩

lemma reach_through {z : Fin n} {j w : ℕ} (start : Reach n C z (n+j)) (path : OrFrom n C (n+j) w) : Reach n C z w :=
  path _ start (fun k hk ok t mt ht h => reach_step n C z k hk ok t mt ht h)

lemma lost_witness (least : IsLeastAO G C) (fixed : IsLiftFixedPoint G C) (live : ∀ k<C.size, InOutputCone n C k)
    (form : TopForm G C) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i<C.size, (gateAt C i).op = GateOp.and → i≠g → BelowF G C i)
    (allOr : ∀ k<C.size, n+g ∈ (gateAt C k).inputs → (gateAt C k).op = GateOp.or)
    (x : Fin n → Bool) (on : graphFun G ∅ x = true) (off : cut n g C x C.output ≠ true) :
    ∃ j<C.size, n+g ∈ (gateAt C j).inputs ∧ (∃ z : Fin n, Reach n C z (n+j)) ∧
      ∃ v ∈ routes G C g, x v = true ∧ ∀ z : Fin n, Reach n C z (n+j) → x z ≠ true ∧ G.Adj z v := by
  let ao := least.1
  have eq (y : Fin n → Bool) : W n C y C.output = graphFun G ∅ y := congrFun least.2.1 y
  obtain ⟨k,hk,ak,out,before,after⟩ := trace_loss ao ag x C.output ((eq x).trans on) off
  have clean : BelowF G C k := fun y hy => (eq y).symm.trans (orFrom_val out y hy)
  have ne : k≠g := fun e => dirty (e ▸ clean)
  obtain ⟨p,q,perm,_,sem⟩ := clean_top_expansion ao form unique dirty hk ak clean
  obtain ⟨left,v,hv,xv⟩ := (sem x).mp before
  have qOn := survives ao ag x xv ((mem_R ..).mp hv)
  have pOff (hp : cut n g C x p = true) : False := by
    apply after ((cut_and ao x hk ne ak).mpr ?_)
    intro t ht; rcases List.mem_cons.mp (perm.mem_iff.mp ht) with rfl | h
    · exact hp
    · exact (List.mem_singleton.mp h) ▸ qOn
  rcases left with ⟨u,hu,xu⟩ | ⟨gp,_⟩
  · exact (pOff (survives ao ag x xu ((mem_R ..).mp hu))).elim
  rcases or_first gp with e | ⟨j,hj,oj,mj,path⟩
  · have mem : n+g ∈ (gateAt C k).inputs := perm.mem_iff.mpr (by simp [e])
    rw [allOr k hk mem] at ak; contradiction
  obtain ⟨z,rz⟩ := reader_has_primary least fixed live unique dirty hj oj mj
  refine ⟨j,hj,mj,⟨z,rz⟩,v,route_iff.mpr ?_,xv,?_⟩
  · exact fun y gy yv => clean y ((sem y).mpr ⟨Or.inr ⟨gp,gy⟩,v,hv,yv⟩)
  · intro z rz
    have zp := reach_through rz path
    refine ⟨fun h => pOff (survives ao ag x h zp),?_⟩
    exact (pair_edge z v).mp (clean _ ((sem _).mpr ⟨Or.inl ⟨z,(mem_R ..).mpr zp,by simp [pairInput]⟩,v,hv,by simp [pairInput]⟩))

end Arm3700

namespace Rewire3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700
variable {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def arg (n g : ℕ) (pick : ℕ → ℕ) (k w : ℕ) := if w=n+g then pick k else w

def reroute (n g : ℕ) (C : Circuit) (pick : ℕ → ℕ) : Circuit :=
  ⟨List.ofFn (fun k : Fin C.size => ⟨(gateAt C k).op,(gateAt C k).inputs.map (arg n g pick k)⟩), C.output⟩

@[simp] lemma size_reroute (pick : ℕ → ℕ) : (reroute n g C pick).gates.length = C.size := by simp [reroute]
lemma gate_reroute (pick : ℕ → ℕ) {k : ℕ} (hk : k<C.size) : gateAt (reroute n g C pick) k =
    ⟨(gateAt C k).op,(gateAt C k).inputs.map (arg n g pick k)⟩ := by simp [gateAt,reroute,List.getD_eq_getElem?_getD,Circuit.size] at *; simp_all

lemma legal (ao : IsAO2 n C) (hg : g<C.size) (pick : ℕ → ℕ) (select : ∀ k, pick k ∈ (gateAt C g).inputs) : IsAO2 n (reroute n g C pick) := by
  have each {d} (mem : d ∈ (reroute n g C pick).gates) : ∃ k : Fin C.size, d = ⟨(gateAt C k).op,(gateAt C k).inputs.map (arg n g pick k)⟩ := by
    simpa [reroute,eq_comm] using mem
  refine ⟨?_,?_,?_⟩
  · intro d hd; obtain ⟨k,rfl⟩ := each hd; exact ao.1 (gateAt C k) (gate_mem k.isLt)
  · intro k hk w mw; rw [size_reroute] at hk; rw [gate_reroute pick hk] at mw
    obtain ⟨t,mt,rfl⟩ := List.mem_map.mp mw
    have bound := ao.2.1 k hk _ mt
    have before := ao.2.1 g hg _ (select k)
    unfold arg; split_ifs <;> omega
  · intro d hd; obtain ⟨k,rfl⟩ := each hd; simpa using ao.2.2 _ (gate_mem k.isLt)

lemma flat (ao : IsAO2 n C) (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and)
    (stack : ∀ j<C.size, (gateAt C j).op = GateOp.and → ∀ i, InCone n C i j → (gateAt C i).op = GateOp.and → i=g)
    (pick : ℕ → ℕ) (select : ∀ k, pick k ∈ (gateAt C g).inputs) :
    let D := reroute n g C pick
    ∀ i<D.size, ∀ j<D.size, (gateAt D i).op = GateOp.and → (gateAt D j).op = GateOp.and → ¬ InCone n D i j := by
  let D := reroute n g C pick
  let P := fun w => OnlyAnd n C g w ∧ w≠n+g
  have marks : Marked n D.gates P := by
    intro k hk
    have hk' : k<C.size := by simpa [D] using hk
    have eq : gateAt ⟨D.gates,0⟩ k = gateAt D k := rfl
    rw [eq,gate_reroute pick hk']
    refine ⟨?_,?_⟩
    · intro ak pure; exact pure.2 (congrArg (n+·) (pure.1 k rfl k (.inl rfl) ak))
    · intro h w mw; obtain ⟨t,mt,rfl⟩ := List.mem_map.mp mw
      by_cases e : t=n+g
      · simp only [arg,e,ite_true]; exact ⟨onlyAnd_operand ao hg (select k) (stack g hg ag),Nat.ne_of_lt (ao.2.1 g hg _ (select k))⟩
      · simp only [arg,e,ite_false]; refine ⟨onlyAnd_operand ao hk' mt ?_,e⟩
        rcases h with ak | pk
        · exact stack k hk' ak
        · exact fun i hi => pk.1 k rfl i (.inr hi)
  dsimp only
  intro i _ j hj ai aj path
  exact no_stacks marks j hj i path (Or.inl aj) ai

lemma gate_value {pick : ℕ → ℕ} (ao : IsAO2 n C) (hg : g<C.size) (select : ∀ k, pick k ∈ (gateAt C g).inputs)
    {k : ℕ} (hk : k<C.size) (x : Fin n → Bool) :
    W n (reroute n g C pick) x (n+k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (fun t => W n (reroute n g C pick) x (arg n g pick k t))) := by
  have hk' : k<(reroute n g C pick).gates.length := by simpa using hk
  have ok := legal ao hg pick select
  rw [W_gate n _ x k hk']
  have e : ∀ t∈(gateAt (reroute n g C pick) k).inputs, (if t<n+k then W n (reroute n g C pick) x t else false) = W n (reroute n g C pick) x t := fun t ht => ite_eq_left (ok.2.1 k hk' t ht)
  rw [List.map_congr_left e,gate_reroute pick hk]; simp [List.map_map,Function.comp_def]

lemma old_value (ao : IsAO2 n C) {k : ℕ} (hk : k<C.size) (x : Fin n → Bool) :
    W n C x (n+k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (W n C x)) := by
  rw [W_gate n C x k hk,List.map_congr_left (fun w hw => ite_eq_left (ao.2.1 k hk w hw))]

lemma grows (ao : IsAO2 n C) (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and)
    (pick : ℕ → ℕ) (select : ∀ k, pick k ∈ (gateAt C g).inputs) (x : Fin n → Bool)
    {w : ℕ} (valid : w<n+C.size) : W n C x w = true → W n (reroute n g C pick) x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases input : w<n
    · simp [W_input n _ x w input]
    obtain ⟨k,rfl⟩ : ∃ k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.size := by omega
    rw [gate_value ao hg select hk,old_value ao hk]
    apply LMeta616.gateOp_mono _ (ao.1 _ (gate_mem hk))
    intro t mt h
    have bound := ao.2.1 k hk t mt
    by_cases e : t=n+g
    · have before := ao.2.1 g hg _ (select k)
      simp only [arg,e,ite_true]; exact ih _ (by omega) (by omega) (((W_and_iff n C x g hg ag).mp (e ▸ h) _ (select k)).2)
    · simpa only [arg,e,ite_false] using ih t bound (by omega) h

end Rewire3700

namespace Negative3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700 Arm3700 Rewire3700
variable {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def Certified (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (pick : ℕ → ℕ) :=
  ∀ j<C.size, n+g ∈ (gateAt C j).inputs → ∃ z : Fin n, Reach n C z (n+j) ∧
    ∀ v ∈ routes G C g, G.Adj z v → ∀ x : Fin n → Bool, W n C x (pick j) = true → x v = true → graphFun G ∅ x = true

def Gain (n g : ℕ) (C : Circuit) (pick : ℕ → ℕ) (x : Fin n → Bool) (w : ℕ) :=
  ∃ j<C.size, n+g ∈ (gateAt C j).inputs ∧ OrFrom n C (n+j) w ∧ W n C x (pick j) = true

lemma path_order {a b : ℕ} (path : OrFrom n C a b) : a≤b := path (a≤·) (le_refl _) (fun _ _ _ _ _ lt h => h.trans lt.le)
lemma concat {a b c : ℕ} (p : OrFrom n C a b) (q : OrFrom n C b c) : OrFrom n C a c := fun P s k => q P (p P s k) k

lemma negative (ao : IsAO2 n C) (form : TopForm G C) (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and)
    (dirty : ¬ BelowF G C g) (unique : ∀ i<C.size, (gateAt C i).op = GateOp.and → i≠g → BelowF G C i)
    (allOr : ∀ k<C.size, n+g ∈ (gateAt C k).inputs → (gateAt C k).op = GateOp.or)
    (pick : ℕ → ℕ) (select : ∀ k, pick k ∈ (gateAt C g).inputs) (cert : Certified G C g pick)
    (x : Fin n → Bool) (neg : graphFun G ∅ x ≠ true) {w : ℕ} (valid : w<n+C.size) :
    W n (reroute n g C pick) x w = true → W n C x w = true ∨ Gain n g C pick x w := by
  let D := reroute n g C pick
  have impossible {t : ℕ} (bound : t≤n+g) (h : Gain n g C pick x t) : False := by
    obtain ⟨j,hj,mj,path,_⟩ := h; have := ao.2.1 j hj _ mj; have := path_order path; omega
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro on
    by_cases inp : w<n
    · exact Or.inl ((W_input n C x w inp).trans ((W_input n _ x w inp).symm.trans on))
    obtain ⟨k,rfl⟩ : ∃ k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.size := by omega
    rw [gate_value ao hg select hk] at on
    rcases ao.1 _ (gate_mem hk) with ak | ok
    · have unchanged {t} (mt : t∈(gateAt C k).inputs) : arg n g pick k t = t := by
        apply if_neg; rintro rfl; rw [allOr k hk mt] at ak; contradiction
      have act (t : ℕ) (mt : t∈(gateAt C k).inputs) : W n C x t = true ∨ Gain n g C pick x t := by
        have h : ∀ v ∈ (gateAt C k).inputs, W n D x (arg n g pick k v) = true := by simpa [ak,GateOp.eval,D,List.all_map] using on
        exact ih t (ao.2.1 k hk t mt) (by have := ao.2.1 k hk t mt; omega) (unchanged mt ▸ h t mt)
      by_cases stays : W n C x (n+k) = true
      · exact Or.inl stays
      exfalso
      by_cases kg : k=g
      · subst k; apply stays ((W_and_iff n C x g hg ag).mpr ?_)
        intro t mt; have lt := ao.2.1 g hg t mt
        exact ⟨lt,(act t mt).resolve_right (impossible lt.le)⟩
      have clean := unique k hk ak kg
      obtain ⟨p,q,perm,noQ,sem⟩ := clean_top_expansion ao form unique dirty hk ak clean
      have pm : p ∈ (gateAt C k).inputs := perm.mem_iff.mpr (by simp)
      have qm : q ∈ (gateAt C k).inputs := perm.mem_iff.mpr (by simp)
      have gp {j : ℕ} (hj : j<C.size) (mj : n+g∈(gateAt C j).inputs) : OrFrom n C (n+g) (n+j) :=
        fun _ start step => step j hj (allOr j hj mj) _ mj (ao.2.1 j hj _ mj) start
      have qold := (act q qm).resolve_right (fun ⟨j,hj,mj,path,_⟩ => noQ (concat (gp hj mj) path))
      obtain ⟨j,hj,mj,path,picked⟩ := (act p pm).resolve_left (fun pold => stays ((W_and_iff n C x k hk ak).mpr (by
        intro t mt; refine ⟨ao.2.1 k hk t mt,?_⟩; rcases List.mem_cons.mp (perm.mem_iff.mp mt) with rfl | h
        · exact pold
        · exact (List.mem_singleton.mp h) ▸ qold)))
      have pure := onlyAnd_operand ao hk qm (fun i sub ai => only_dirty_below_and form unique (lt_trans (inCone_lt n C k hk i sub) hk) hk ai ak sub)
      obtain ⟨v,hv,xv⟩ := ((operand_expansion ao (lt_trans (ao.2.1 k hk q qm) (Nat.add_lt_add_left hk n)) pure x).mp qold).resolve_right (fun h => noQ h.1)
      obtain ⟨z,rz,guard⟩ := cert j hj mj
      have pz := reach_through rz path
      have wroute : v ∈ routes G C g := route_iff.mpr (fun y gy yv => clean y ((sem y).mpr ⟨Or.inr ⟨concat (gp hj mj) path,gy⟩,v,hv,yv⟩))
      have adj := (pair_edge z v).mp (clean _ ((sem _).mpr ⟨Or.inl ⟨z,(mem_R ..).mpr pz,by simp [pairInput]⟩,v,hv,by simp [pairInput]⟩))
      exact neg (guard v wroute adj x picked xv)
    · obtain ⟨t,mt,act⟩ : ∃ t ∈ (gateAt C k).inputs, W n D x (arg n g pick k t) = true := by simpa [ok,GateOp.eval,D,List.any_map] using on
      have lt := ao.2.1 k hk t mt
      by_cases e : t=n+g
      · subst t; have before := ao.2.1 g hg _ (select k)
        have old := (ih (pick k) (by omega) (by omega) (by simpa [arg,D] using act)).resolve_right (impossible before.le)
        exact Or.inr ⟨k,hk,mt,fun _ h _ => h,old⟩
      · rcases ih t lt (by omega) (by simpa [arg,e,D] using act) with old | ⟨j,hj,mj,path,picked⟩
        · exact Or.inl ((W_or_iff n C x k hk ok).mpr ⟨t,mt,lt,old⟩)
        · exact Or.inr ⟨j,hj,mj,fun P start step => step k hk ok t mt lt (path P start step),picked⟩

lemma certified_goal (least : IsLeastAO G C) (form : TopForm G C) (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and)
    (dirty : ¬ BelowF G C g) (unique : ∀ i<C.size, (gateAt C i).op = GateOp.and → i≠g → BelowF G C i)
    (live : InOutputCone n C g) (allOr : ∀ k<C.size, n+g ∈ (gateAt C k).inputs → (gateAt C k).op = GateOp.or)
    (pick : ℕ → ℕ) (select : ∀ k, pick k ∈ (gateAt C g).inputs) (cert : Certified G C g pick) : Goal G C := by
  let D := reroute n g C pick
  have ok := legal least.1 hg pick select
  refine ⟨D,ok,(size_reroute pick).le,?_,flat least.1 hg ag (fun k hk ak i sub ai => only_dirty_below_and form unique (lt_trans (inCone_lt n C k hk i sub) hk) hk ai ak sub) pick select⟩
  funext x; apply Bool.eq_iff_iff.mpr
  have eq (y : Fin n → Bool) : W n C y C.output = graphFun G ∅ y := congrFun least.2.1 y
  have bound := (Double3700.live_bounds live).2
  constructor
  · intro on; by_contra neg
    rcases negative least.1 form hg ag dirty unique allOr pick select cert x neg bound on with old | ⟨j,hj,mj,path,_⟩
    · exact neg ((eq x).symm.trans old)
    · obtain ⟨z,rz,_⟩ := cert j hj mj
      exact G.irrefl ((pair_edge z z).mp ((eq _).symm.trans (reach_val n C z C.output (pairInput z z) (by simp [pairInput]) (reach_through rz path))))
  · intro on; exact grows least.1 hg ag pick select x bound ((eq x).trans on)

end Negative3700

namespace Branches3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700 Reader3700 Arm3700 Negative3700
variable {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma one_arm {A B : Finset (Fin n)} {u v : Fin n} (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i<C.size, (gateAt C i).op = GateOp.and → i≠g → BelowF G C i)
    (units : ∀ v : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput v) = false) (live : InOutputCone n C g)
    (ur : u∈routes G C g) (ua : u∈A) (vb : v∈B) (rect : ∀ x, gateVal n C g x = true ↔ Hits A x ∧ Hits B x)
    (cover : ∀ x, graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨ (x u=true ∧ Hits B x) ∨ (x v=true ∧ Hits A x))
    (kept : ∀ a∈A, a≠u → cut n g C (pairInput a v) C.output = true) : Goal G C := by
  apply restore_subset ao computes form hg ag dirty unique units {u}
  · intro x
    simp only [Hits,Finset.mem_singleton,exists_eq_left] at ⊢
    constructor
    · intro on; rcases (cover x).mp on with stay | ⟨xu,hb⟩ | ⟨xv,a,ha,xa⟩
      · exact .inl stay
      · exact .inr ⟨(rect x).mpr ⟨⟨u,ua,xu⟩,hb⟩,xu⟩
      · by_cases e : a=u
        · exact .inr ⟨(rect x).mpr ⟨⟨a,ha,xa⟩,v,vb,xv⟩,e ▸ xa⟩
        · apply Or.inl (cut_mono ao (x:=pairInput a v) (fun t h => ?_) (le_refl _) C.output (kept a ha e))
          rcases (show t=a ∨ t=v by simpa [pairInput] using h) with rfl | rfl
          · exact xa
          · exact xv
    · rintro (stay | ⟨gx,xu⟩)
      · exact (congrFun computes x).symm.trans (cut_sub ao x _ stay)
      · exact (route_iff.mp ur) x gx xu
  · obtain ⟨a,b,ins,_,_,disj,_⟩ := dirty_rectangle_at ao hg ag form unique units
    intro c d cd; obtain ⟨rfl,rfl⟩ : a=c ∧ b=d := by simpa using ins.symm.trans cd
    have paid := two_credits computes live dirty
    by_cases aMem : u ∈ R n C a
    · have bNo := Finset.disjoint_left.mp disj aMem
      simpa [Finset.inter_singleton_of_mem aMem,Finset.inter_singleton_of_notMem bNo] using paid
    · by_cases bMem : u ∈ R n C b
      · simpa [Finset.inter_singleton_of_notMem aMem,Finset.inter_singleton_of_mem bMem] using paid
      · simp [Finset.inter_singleton_of_notMem aMem,Finset.inter_singleton_of_notMem bMem]

lemma arm_reader {A B : Finset (Fin n)} {u v a : Fin n} (least : IsLeastAO G C) (fixed : IsLiftFixedPoint G C)
    (live : ∀ i<C.size, InOutputCone n C i) (form : TopForm G C) (ag : (gateAt C g).op = GateOp.and)
    (dirty : ¬ BelowF G C g) (unique : ∀ i<C.size, (gateAt C i).op = GateOp.and → i≠g → BelowF G C i)
    (allOr : ∀ k<C.size, n+g ∈ (gateAt C k).inputs → (gateAt C k).op = GateOp.or)
    (s : Fin n → Bool) (bip : ∀ i j, G.Adj i j → s i ≠ s j) (c4 : NoFourCycle G)
    (sound : ∀ x, Hits A x → Hits B x → Hits (routes G C g) x → graphFun G ∅ x = true)
    (ua : u∈A) (vb : v∈B) (ub : ∀ i∈B, G.Adj u i) (va : ∀ i∈A, G.Adj i v) (big : 1<B.card)
    (one : A ∩ routes G C g = {u}) (aa : a∈A) (au : a≠u) (off : cut n g C (pairInput a v) C.output ≠ true) :
    ∃ j<C.size, n+g ∈ (gateAt C j).inputs ∧ (∃ z : Fin n, Reach n C z (n+j)) ∧
      ∀ z : Fin n, Reach n C z (n+j) → G.Adj z v ∧ ∀ w ∈ routes G C g, G.Adj z w → w=v := by
  obtain ⟨j,hj,mj,existsZ,w,wr,xw,all⟩ := lost_witness least fixed live form ag dirty unique allOr (pairInput a v) ((pair_edge a v).mpr (va a aa)) off
  have wv : w=v := by
    rcases (show w=a ∨ w=v by simpa [pairInput] using xw) with rfl | e
    · have m := Finset.mem_inter.mpr ⟨aa,wr⟩; rw [one] at m; exact (au (Finset.mem_singleton.mp m)).elim
    · exact e
  subst w; refine ⟨j,hj,mj,existsZ,?_⟩
  intro z rz; obtain ⟨offZ,zv⟩ := all z rz
  have az : a≠z := by rintro rfl; exact offZ (by simp [pairInput])
  exact ⟨zv,fun w wr zw => routed_neighbour_unique s bip c4 sound ua vb ub va aa au az zv big wr zw⟩

end Branches3700

namespace TwoOr3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700 Reader3700 Arm3700 Negative3700 Branches3700
variable {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma two_or {j k : ℕ} (least : IsLeastAO G C) (fixed : IsLiftFixedPoint G C)
    (live : ∀ i<C.size, InOutputCone n C i) (form : TopForm G C) (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and)
    (dirty : ¬ BelowF G C g) (unique : ∀ i<C.size, (gateAt C i).op = GateOp.and → i≠g → BelowF G C i)
    (units : ∀ v : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput v) = false)
    (s : Fin n → Bool) (bip : ∀ i j, G.Adj i j → s i ≠ s j) (c4 : NoFourCycle G)
    (big : ∀ w ∈ (gateAt C g).inputs, 1 < (R n C w).card)
    (allOr : ∀ t<C.size, n+g ∈ (gateAt C t).inputs → (gateAt C t).op = GateOp.or)
    (only : ∀ t<C.size, n+g ∈ (gateAt C t).inputs → t=j ∨ t=k) : Goal G C := by
  classical
  obtain ⟨p,q,ins,_,_,disj,rect⟩ := dirty_rectangle_at least.1 hg ag form unique units
  let A := R n C p
  let B := R n C q
  let S := routes G C g
  have pm : p∈(gateAt C g).inputs := by simp [ins]
  have qm : q∈(gateAt C g).inputs := by simp [ins]
  have cover (x : Fin n → Bool) : graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨ Hits A x ∧ Hits B x ∧ Hits S x := by
    rw [global_cover least.1 least.2.1 form ag dirty unique,rect]; exact or_congr_right and_assoc
  have sound (x : Fin n → Bool) (a : Hits A x) (b : Hits B x) (h : Hits S x) := (cover x).mpr (Or.inr ⟨a,b,h⟩)
  obtain ⟨l,r⟩ := route_complete A B S sound
  have sa := star_centres c4 (big q qm) l
  have sb := star_centres c4 (big p pm) r
  by_cases both : (A ∩ S).Nonempty ∧ (B ∩ S).Nonempty
  case neg =>
    apply restore_if_budget least.1 least.2.1 form hg ag dirty unique units
    intro c d cd; obtain ⟨rfl,rfl⟩ : p=c ∧ q=d := by simpa using ins.symm.trans cd
    have paid := two_credits least.2.1 (live g hg) dirty
    simp only [← Finset.card_pos] at both
    change 2*((A ∩ S).card+(B ∩ S).card) ≤ _; omega
  obtain ⟨⟨u,hu⟩,v,hv⟩ := both
  have one {T : Finset (Fin n)} {z : Fin n} (sm : T.card ≤ 1) (m : z∈T) : T={z} := by
    ext i; simp only [Finset.mem_singleton]; exact ⟨fun h => Finset.card_le_one.mp sm i h z m, fun e => e ▸ m⟩
  have a1 := one sa hu
  have b1 := one sb hv
  obtain ⟨ua,us⟩ := Finset.mem_inter.mp hu
  obtain ⟨vb,vs⟩ := Finset.mem_inter.mp hv
  have uB := l u hu
  have vA := r v hv
  have arms (x : Fin n → Bool) : graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨ (x u=true ∧ Hits B x) ∨ (x v=true ∧ Hits A x) := by
    simpa only [a1,b1,Hits,Finset.mem_singleton,exists_eq_left] using two_star_cover (A:=A) (B:=B) (S:=S) least.1 disj cover x
  by_cases keptA : ∀ a ∈ A, a≠u → cut n g C (pairInput a v) C.output = true
  · exact one_arm least.1 least.2.1 form hg ag dirty unique units (live g hg) us ua vb rect arms keptA
  by_cases keptB : ∀ b ∈ B, b≠v → cut n g C (pairInput b u) C.output = true
  · exact one_arm least.1 least.2.1 form hg ag dirty unique units (live g hg) vs vb ua (fun x => (rect x).trans and_comm) (fun x => (arms x).trans (or_congr_right or_comm)) keptB
  push Not at keptA keptB
  obtain ⟨a,aa,au,offA⟩ := keptA
  obtain ⟨b,bb,bv,offB⟩ := keptB
  have va := fun i hi => (vA i hi).symm
  have ub := fun i hi => (uB i hi).symm
  obtain ⟨i,hi,mi,⟨z,rz⟩,guardi⟩ := arm_reader least fixed live form ag dirty unique allOr s bip c4 sound ua vb uB va (big q qm) a1 aa au (by simpa using offA)
  obtain ⟨h,hh,mh,⟨t,rt⟩,guardh⟩ := arm_reader least fixed live form ag dirty unique allOr s bip c4 (fun x b a => sound x a b) vb ua vA ub (big p pm) b1 bb bv (by simpa using offB)
  have ih : i≠h := by
    rintro rfl
    have zu := (guardh z rz).1
    have eq := (guardi z rz).2 u us zu
    exact G.irrefl (eq ▸ uB v vb)
  have all (m : ℕ) (hm : m<C.size) (mm : n+g∈(gateAt C m).inputs) : m=i ∨ m=h := by
    have := only m hm mm; have := only i hi mi; have := only h hh mh; omega
  let pick := fun m : ℕ => if m=i then p else q
  have select (m : ℕ) : pick m ∈ (gateAt C g).inputs := by simp only [pick]; split <;> assumption
  have pure (i : ℕ) (inside : InCone n C i g) (ai : (gateAt C i).op=.and) : False :=
    (Nat.ne_of_lt (inCone_lt n C g hg i inside)) (only_dirty_below_and form unique (lt_trans (inCone_lt n C g hg i inside) hg) hg ai ag inside)
  apply certified_goal least form hg ag dirty unique (live g hg) allOr pick select
  intro m hm mm; rcases all m hm mm with rfl | rfl
  · refine ⟨z,rz,?_⟩; intro w wr zw x px xw; obtain rfl := (guardi z rz).2 w wr zw
    have on : W n C x p = true := by simpa [pick] using px
    obtain ⟨d,hd,xd⟩ := (pure_operand least.1 hg pure pm x).mp on
    have edge := vA d hd
    simpa [graphFun] using (show ∃ l r, G.Adj l r ∧ x l=true ∧ x r=true from ⟨_,_,edge,xw,xd⟩)
  · refine ⟨t,rt,?_⟩; intro w wr tw x qx xw; obtain rfl := (guardh t rt).2 w wr tw
    have on : W n C x q = true := by simpa [pick,Ne.symm ih] using qx
    obtain ⟨d,hd,xd⟩ := (pure_operand least.1 hg pure qm x).mp on
    have edge := uB d hd
    simpa [graphFun] using (show ∃ l r, G.Adj l r ∧ x l=true ∧ x r=true from ⟨_,_,edge,xw,xd⟩)

end TwoOr3700

namespace Filter3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700 Splice3700
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

abbrev net (D : Network n) : Circuit := ⟨D.gates,0⟩
inductive Live (D : Network n) (out : ℕ) : ℕ → Prop where
  | root : Live D out out
  | arg {k w : ℕ} : k<D.gates.length → w ∈ (gateAt (net D) k).inputs → Live D out (n+k) → Live D out w

lemma nonpure_path {D : Network n} {out w : ℕ} (live : Live D out w) :
    ¬ D.pure w → OrFrom n (net D) w out := by
  induction live with
  | root => exact fun _ _ start _ => start
  | @arg k t hk m _ ih =>
    intro impure
    have marks := D.marks k hk
    have notAnd : (gateAt (net D) k).op ≠ GateOp.and := fun op => impure (marks.2 (Or.inl op) t m)
    have op := (D.ao.1 _ (gate_mem hk)).resolve_left notAnd
    have tail := ih (fun pure => impure (marks.2 (Or.inr pure) t m))
    exact fun P start next => tail P (next k hk op t m (D.ao.2.1 k hk t m) start) next

lemma pure_value (D : Network n) (w : ℕ) (valid : w<bound D) (pure : D.pure w) (x : Fin n → Bool) :
    bit D x w = true ↔ Hits (R n (net D) w) x := by
  constructor
  · intro on
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases primary : w<n
      · exact ⟨⟨w,primary⟩,(mem_R ..).mpr (reach_refl n (net D) ⟨w,primary⟩), (W_input n _ x w primary).symm.trans on⟩
      obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
      have hk : k<D.gates.length := by unfold bound at valid; omega
      have marks := D.marks k hk
      have op := (D.ao.1 _ (gate_mem hk)).resolve_left (fun a => marks.1 a pure)
      obtain ⟨t,ht,lt,active⟩ := (W_or_iff n _ x k hk op).mp on
      obtain ⟨z,hz,xz⟩ := ih t lt (lt.trans valid) (marks.2 (Or.inr pure) t ht) active
      exact ⟨z,(mem_R ..).mpr (reach_step n _ z k hk op t ht lt ((mem_R ..).mp hz)),xz⟩
  · rintro ⟨z,hz,xz⟩; exact reach_val n _ z w x xz ((mem_R ..).mp hz)

lemma live_support {D : Network n} {out w : ℕ} {a u v b : Fin n}
    (c4 : NoFourCycle G) (safe : ∀ x, bit D x out = true → graphFun G ∅ x = true)
    (live : Live D out w) (au : G.Adj a u) (av : G.Adj a v) (uv : u≠v) (ab : ¬ G.Adj a b) :
    u ∈ R n (net D) w → v ∈ R n (net D) w → b ∈ R n (net D) w → False := by
  induction live with
  | root =>
    intro hu _ _
    have on := reach_val n (net D) u out (pairInput u u) (by simp [pairInput]) ((mem_R ..).mp hu)
    exact G.irrefl ((pair_edge u u).mp (safe _ on))
  | @arg k t hk ht tail ih =>
    intro hu hv hb
    rcases D.ao.1 _ (gate_mem hk) with ak | ok
    · have marks := D.marks k hk
      have top := nonpure_path tail (marks.1 ak)
      obtain ⟨p,q,ins⟩ := inputs_two D.ao hk
      have mate (s : ℕ) (sm : s ∈ (gateAt (net D) k).inputs)
          (both : ∀ i ∈ (gateAt (net D) k).inputs, i=t ∨ i=s) : False := by
        have valid : s<bound D := (D.ao.2.1 k hk s sm).trans (Nat.add_lt_add_left hk n)
        obtain ⟨z,hz,_⟩ := (pure_value D s valid (marks.2 (Or.inl ak) s sm) (fun _ => true)).mp (all_high D.ao valid)
        have cross (y : Fin n) (hy : y ∈ R n (net D) t) : G.Adj z y := by
          apply (pair_edge z y).mp (safe _ (orFrom_val top _ ((W_and_iff n _ _ k hk ak).mpr ?_)))
          intro i hi
          refine ⟨D.ao.2.1 k hk i hi,?_⟩
          rcases both i hi with rfl | rfl
          · exact reach_val n _ y _ _ (by simp [pairInput]) ((mem_R ..).mp hy)
          · exact reach_val n _ z _ _ (by simp [pairInput]) ((mem_R ..).mp hz)
        have za := common_neighbour_unique c4 uv (cross u hu).symm (cross v hv).symm au.symm av.symm
        exact ab (za ▸ cross b hb)
      rcases List.mem_cons.mp (ins ▸ ht) with rfl | h
      · apply mate q (by simp [ins])
        simp [ins]
      · obtain rfl := List.mem_singleton.mp h
        apply mate p (by simp [ins]); simp [ins,or_comm]
    · have up {z} (h : z ∈ R n (net D) t) : z ∈ R n (net D) (n+k) :=
        (mem_R ..).mpr (reach_step n _ z k hk ok t ht (D.ao.2.1 k hk t ht) ((mem_R ..).mp h))
      exact ih (up hu) (up hv) (up hb)

end Filter3700

namespace Project3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700 Splice3700 Filter3700
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

noncomputable abbrev Pick (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n) (D : Network n) (w : ℕ) :=
  (R n (net D) w).filter (G.Adj a)

lemma small_signal (D : Network n) (inputs : ∀ z : Fin n, Signal D {z}) {S : Finset (Fin n)}
    (one : S.card ≤ 1) (nonempty : S.Nonempty) : Signal D S := by
  obtain ⟨z,rfl⟩ := Finset.card_eq_one.mp (le_antisymm one (Finset.card_pos.mpr nonempty))
  exact inputs z

lemma live_pick {D E : Network n} {out w : ℕ} (a : Fin n) (c4 : NoFourCycle G)
    (safe : ∀ x, bit D x out = true → graphFun G ∅ x = true) (live : Live D out w)
    (valid : w<bound D) (pure : D.pure w) (inputs : ∀ z : Fin n, Signal E {z})
    (hw : Rep E D.pure (fun _ => True) (net D) w) (nonempty : (Pick G a D w).Nonempty) : Signal E (Pick G a D w) := by
  classical
  by_cases all : ∀ z ∈ R n (net D) w, G.Adj a z
  · have eq : Pick G a D w = R n (net D) w := Finset.filter_true_of_mem all
    obtain ⟨r,hr,pr,vr⟩ := hw
    exact ⟨r,hr,pr pure,fun x => by rw [eq,vr x trivial]; exact pure_value D w valid pure x⟩
  · push Not at all
    obtain ⟨b,hb,ab⟩ := all
    apply small_signal E inputs _ nonempty
    apply Finset.card_le_one.mpr
    intro u hu v hv
    by_contra uv
    obtain ⟨uR,au⟩ := Finset.mem_filter.mp hu
    obtain ⟨vR,av⟩ := Finset.mem_filter.mp hv
    exact live_support c4 safe live au av uv ab uR vR hb

structure Extends (D E : Network n) : Prop where
  grow : D.gates.length ≤ E.gates.length
  marks : ∀ w < bound D, D.pure w → E.pure w
  values : ∀ x : Fin n → Bool, ∀ w < bound D, bit E x w = bit D x w

lemma Extends.id (D : Network n) : Extends D D := ⟨le_refl _,fun _ _ h => h,fun _ _ _ => rfl⟩
lemma Extends.signal {D E : Network n} (e : Extends D E) {S} (sig : Signal D S) : Signal E S := by
  obtain ⟨w,hw,p,v⟩ := sig
  exact ⟨w,lt_of_lt_of_le hw (Nat.add_le_add_left e.grow n),e.marks w hw p,fun x => (e.values x w hw) ▸ v x⟩

lemma combine (D : Network n) (A B : Finset (Fin n)) (a : A.Nonempty → Signal D A) (b : B.Nonempty → Signal D B) :
    ∃ E : Network n, Extends D E ∧ E.gates.length ≤ D.gates.length+1 ∧ ((A ∪ B).Nonempty → Signal E (A ∪ B)) := by
  classical
  by_cases az : A.Nonempty
  · by_cases bz : B.Nonempty
    · obtain ⟨p,hp,pp,vp⟩ := a az
      obtain ⟨q,hq,pq,vq⟩ := b bz
      obtain ⟨E,len,marks,pure,vals,new⟩ := extend D .or p q hp hq (.inr rfl) True (by simp) (fun _ => ⟨pp,pq⟩)
      refine ⟨E,⟨by omega,marks,vals⟩,len.le, fun _ => ⟨bound D,Nat.add_lt_add_left (by omega) n,pure trivial,?_⟩⟩
      intro x
      simp only [new,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_true,vp x,vq x]
      simp only [Hits,Finset.mem_union]; aesop
    · have e := Finset.not_nonempty_iff_eq_empty.mp bz
      exact ⟨D,.id _,by omega,by simpa [e] using a⟩
  · have e := Finset.not_nonempty_iff_eq_empty.mp az
    exact ⟨D,.id _,by omega,by simpa [e] using b⟩

lemma pick_union {D : Network n} {k p q : ℕ} (a : Fin n) (hk : k<D.gates.length)
    (ins : (gateAt (net D) k).inputs=[p,q]) (ok : (gateAt (net D) k).op = GateOp.or) :
    Pick G a D (n+k) = Pick G a D p ∪ Pick G a D q := by
  ext z
  simp only [Finset.mem_union,Finset.mem_filter]
  constructor
  · rintro ⟨h,az⟩
    obtain ⟨_,_,t,m,_,path⟩ := R_gate n (net D) k z h
    have h := (mem_R n (net D) t z).mpr path
    rcases List.mem_cons.mp (ins ▸ m) with rfl | e
    · exact Or.inl ⟨h,az⟩
    · exact Or.inr ⟨(List.mem_singleton.mp e) ▸ h,az⟩
  · have up {w} (m : w ∈ (gateAt (net D) k).inputs) (h : z ∈ R n (net D) w) :=
      (mem_R ..).mpr (reach_step n _ z k hk ok w m (D.ao.2.1 k hk w m) ((mem_R ..).mp h))
    rintro (⟨hp,az⟩ | ⟨hq,az⟩)
    · exact ⟨up (w:=p) (by simp [ins]) hp,az⟩
    · exact ⟨up (w:=q) (by simp [ins]) hq,az⟩

lemma project (a : Fin n) (D : Network n) (out : ℕ) (c4 : NoFourCycle G)
    (safe : ∀ x, bit D x out = true → graphFun G ∅ x = true) :
    ∃ E : Network n, E.gates.length ≤ D.gates.length ∧ (∀ z : Fin n, Signal E {z}) ∧
      (∀ w < bound D, Live D out w → Rep E D.pure (fun _ => True) (net D) w) ∧
      (∀ w < bound D, D.pure w → (Pick G a D w).Nonempty → Signal E (Pick G a D w)) := by
  classical
  let Keep := fun (E : Network n) w => Live D out w → Rep E D.pure (fun _ => True) (net D) w
  let Sel := fun (E : Network n) w => D.pure w → (Pick G a D w).Nonempty → Signal E (Pick G a D w)
  have run (k : ℕ) (lim : k≤D.gates.length) : ∃ E : Network n, E.gates.length ≤ k ∧
      (∀ z : Fin n, Signal E {z}) ∧ (∀ w < n+k, Keep E w) ∧ ∀ w < n+k, Sel E w := by
    induction k with
    | zero =>
      let E : Network n := ⟨[],fun _ => True,by refine ⟨?_,?_,?_⟩ <;> simp [AndOrOnly,ReadsBack],by intro i hi; simp at hi⟩
      have inputs (z : Fin n) : Signal E {z} := ⟨z.val,z.isLt,trivial,fun x => by rw [show bit E x z.val = x z from W_input n _ x z.val z.isLt]; simp [Hits]⟩
      refine ⟨E,le_refl _,inputs,?_,?_⟩
      · intro w hw _; have lt : w<n := by simpa using hw
        exact ⟨w,lt,fun _ => trivial,fun x _ => (W_input n _ x w lt).trans (W_input n _ x w lt).symm⟩
      · intro w hw _ nonempty
        exact small_signal E inputs ((Finset.card_filter_le ..).trans (R_card_input n (net D) w (by simpa using hw))) nonempty
    | succ k ih =>
      obtain ⟨E,len,inputs,keep,sel⟩ := ih (by omega)
      have hk : k<D.gates.length := lim
      have valid : n+k<bound D := Nat.add_lt_add_left hk n
      obtain ⟨p,q,ins⟩ := inputs_two D.ao hk
      have pm : p ∈ (gateAt (net D) k).inputs := by simp [ins]
      have qm : q ∈ (gateAt (net D) k).inputs := by simp [ins]
      have hp := D.ao.2.1 k hk p pm
      have hq := D.ao.2.1 k hk q qm
      have props := D.marks k hk
      suffices one : ∃ H : Network n, Extends E H ∧ H.gates.length ≤ E.gates.length+1 ∧ Keep H (n+k) ∧ Sel H (n+k) by
        obtain ⟨H,ext,sz,liveH,pickH⟩ := one
        refine ⟨H,by omega,fun z => ext.signal (inputs z),?_,?_⟩
        · intro w hw act; by_cases e : w=n+k
          · subst w; exact liveH act
          · exact carry_rep ext.grow ext.marks ext.values (keep w (by omega) act)
        · intro w hw pure nonempty; by_cases e : w=n+k
          · subst w; exact pickH pure nonempty
          · exact ext.signal (sel w (by omega) pure nonempty)
      by_cases live : Live D out (n+k)
      · obtain ⟨p',hp',pp,vp⟩ := keep p hp (.arg hk pm live)
        obtain ⟨q',hq',pq,vq⟩ := keep q hq (.arg hk qm live)
        obtain ⟨H,sz,marks,pure,values,new⟩ := extend E (gateAt (net D) k).op p' q' hp' hq' (D.ao.1 _ (gate_mem hk))
          (D.pure (n+k)) props.1 (fun need => ⟨pp (props.2 need p pm),pq (props.2 need q qm)⟩)
        have ext : Extends E H := ⟨by omega,marks,values⟩
        have rep : Rep H D.pure (fun _ => True) (net D) (n+k) := by
          refine ⟨bound E,Nat.add_lt_add_left (by omega) n,pure,?_⟩
          intro x _; rw [new,vp x trivial,vq x trivial,W_gate n (net D) x k hk]; simp [ins,hp,hq]
        exact ⟨H,ext,sz.le,fun _ => rep,fun pur => live_pick a c4 safe live valid pur (fun z => ext.signal (inputs z)) rep⟩
      · by_cases pure : D.pure (n+k)
        · have ok := (D.ao.1 _ (gate_mem hk)).resolve_left (fun op => props.1 op pure)
          obtain ⟨H,ext,sz,new⟩ := combine E (Pick G a D p) (Pick G a D q)
            (sel p hp (props.2 (Or.inr pure) p pm)) (sel q hq (props.2 (Or.inr pure) q qm))
          exact ⟨H,ext,sz,fun act => (live act).elim,fun _ => (pick_union (G:=G) a hk ins ok).symm ▸ new⟩
        · exact ⟨E,.id _,by omega,fun act => (live act).elim,fun pur => (pure pur).elim⟩
  exact run D.gates.length (le_refl _)

end Project3700

namespace Singleton3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Flat3700 Cover3700 Restore3700 Double3700 Filter3700 Project3700
variable {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma star_cover {a : Fin n} {B : Finset (Fin n)} (ao : IsAO2 n C) (apart : a ∉ B)
    (sub : ∀ x, cut n g C x C.output = true → graphFun G ∅ x = true)
    (lost : ∀ k l, G.Adj k l → cut n g C (pairInput k l) C.output ≠ true →
        pairInput k l a = true ∧ Hits B (pairInput k l)) (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ cut n g C x C.output = true ∨ (x a = true ∧ Hits (B.filter (G.Adj a)) x) := by
  constructor
  · intro on
    obtain ⟨k,l,kl,xk,xl⟩ : ∃ k l, G.Adj k l ∧ x k = true ∧ x l = true := by simpa [graphFun] using on
    by_cases kept : cut n g C (pairInput k l) C.output = true
    · refine Or.inl (cut_mono ao (fun t ht => ?_) (le_refl _) C.output kept)
      exact (show t=k ∨ t=l by simpa [pairInput] using ht).elim (fun e => e ▸ xk) (fun e => e ▸ xl)
    · obtain ⟨hit,hB⟩ := lost k l kl kept
      rcases (show a=k ∨ a=l by simpa [pairInput] using hit) with rfl | rfl
      · exact Or.inr ⟨xk,l,Finset.mem_filter.mpr ⟨((hits_pair ..).mp hB).resolve_left apart,kl⟩,xl⟩
      · exact Or.inr ⟨xl,k,Finset.mem_filter.mpr ⟨((hits_pair ..).mp hB).resolve_right apart,kl.symm⟩,xk⟩
  · rintro (h | ⟨xa,b,hb,xb⟩)
    · exact sub x h
    · simpa [graphFun] using (show ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true from ⟨a,b,(Finset.mem_filter.mp hb).2,xa,xb⟩)

lemma project_output {D : Network n} (a : Fin n) (o : Option ℕ) (ho : ∀ t ∈ o, t<bound D)
    (c4 : NoFourCycle G) (safe : ∀ x, readOut D x o = true → graphFun G ∅ x = true) :
    ∃ E : Network n, ∃ r : Option ℕ, (∀ t ∈ r, t<bound E) ∧ E.gates.length ≤ D.gates.length ∧
      (∀ x, readOut E x r = readOut D x o) ∧ (∀ z : Fin n, Signal E {z}) ∧
      ∀ B : Finset (Fin n), Signal D B → (B.filter (G.Adj a)).Nonempty → Signal E (B.filter (G.Adj a)) := by
  let out := o.getD (bound D)
  have val (x : Fin n → Bool) : bit D x out = readOut D x o := by
    cases o with
    | none => exact LMeta616.wires_oob (net D) x (bound D) (le_refl _)
    | some t => rfl
  obtain ⟨E,sz,inputs,keep,sel⟩ := project a D out c4 (fun x hx => safe x ((val x).symm.trans hx))
  have lift (B : Finset (Fin n)) (sig : Signal D B) (nonempty : (B.filter (G.Adj a)).Nonempty) : Signal E (B.filter (G.Adj a)) := by
    obtain ⟨w,hw,pure,sem⟩ := sig
    have eq : R n (net D) w = B := by
      ext t
      have pair := (pure_value D w hw pure (pairInput t t)).symm.trans (sem (pairInput t t))
      simpa [hits_pair] using pair
    have same : Pick G a D w = B.filter (G.Adj a) := by rw [Pick,eq]
    exact same ▸ sel w hw pure (same.symm ▸ nonempty)
  cases o with
  | none => exact ⟨E,none,by simp,sz,fun _ => rfl,inputs,lift⟩
  | some t =>
    obtain ⟨p,hp,_,vp⟩ := keep t (ho t (by simp)) (.root)
    exact ⟨E,some p,by simpa using hp,sz,fun x => vp x trivial,inputs,lift⟩

lemma singleton_operand (ao : IsAO2 n C) (computes : circuitFun n C = graphFun G ∅)
    (form : TopForm G C) (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ k < C.size, (gateAt C k).op = GateOp.and → k ≠ g → BelowF G C k)
    (units : ∀ v : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput v) = false)
    (live : InOutputCone n C g) (c4 : NoFourCycle G)
    (small : ∃ w ∈ (gateAt C g).inputs, (R n C w).card = 1) : Goal G C := by
  classical
  obtain ⟨p,q,ins,_,_,disj,rect⟩ := dirty_rectangle_at ao hg ag form unique units
  obtain ⟨w,mw,one⟩ := small
  obtain ⟨a,one⟩ := Finset.card_eq_one.mp one
  have extract : ∃ t ∈ (gateAt C g).inputs, a ∉ R n C t ∧
      ∀ x : Fin n → Bool, gateVal n C g x = true → x a = true ∧ Hits (R n C t) x := by
    rcases List.mem_cons.mp (ins ▸ mw) with rfl | eq
    · refine ⟨q,by simp [ins],Finset.disjoint_left.mp disj (one.symm ▸ Finset.mem_singleton_self _),?_⟩
      intro x h; have hit := (rect x).mp h
      simpa [one,Hits] using hit
    · obtain rfl := List.mem_singleton.mp eq
      refine ⟨p,by simp [ins],Finset.disjoint_left.mp disj.symm (one.symm ▸ Finset.mem_singleton_self _),?_⟩
      intro x h; have hit := ((rect x).mp h).symm
      simpa [one,Hits] using hit
  obtain ⟨t,mt,apart,hit⟩ := extract
  have sub (x : Fin n → Bool) (v : cut n g C x C.output = true) := (congrFun computes x).symm.trans (cut_sub ao x _ v)
  have cover := star_cover ao apart sub (fun k l edge off =>
    hit _ (((global_cover ao computes form ag dirty unique _).mp ((pair_edge k l).mpr edge)).resolve_left off).1)
  have stack (k : ℕ) (hk : k<C.size) (ak : (gateAt C k).op = GateOp.and) (i : ℕ)
      (h : InCone n C i k) (ai : (gateAt C i).op = GateOp.and) :=
    only_dirty_below_and form unique (lt_trans (inCone_lt n C k hk i h) hk) hk ai ak h
  obtain ⟨D,o,ho,sz,sem,_,sig⟩ := cut_base (hg:=hg) ao ag stack
  obtain ⟨E,r,hr,smaller,old,inputs,filter⟩ := project_output a o ho c4 (fun x on => sub x ((sem x).symm.trans on))
  let B := (R n C t).filter (G.Adj a)
  have paid := two_credits computes live dirty
  by_cases nonempty : B.Nonempty
  · obtain ⟨p',hp,pp,vp⟩ := inputs a
    obtain ⟨q',hq,pq,vq⟩ := filter _ (sig t mt) nonempty
    obtain ⟨H,s,hs,num,_,_,_,v⟩ := add_star E r hr p' q' hp hq pp pq
    obtain ⟨F,ok,flen,eval,flat⟩ := reify H (some s)
    refine ⟨F,ok,by omega,?_,flat⟩
    funext x; apply Bool.eq_iff_iff.mpr
    change F.eval (List.ofFn x) = true ↔ _
    rw [eval]; change bit H x s = true ↔ _
    rw [v,Bool.or_eq_true,Bool.and_eq_true,vp,vq,old,sem,cover x]
    simp [Hits]
  · obtain ⟨F,ok,flen,eval,flat⟩ := reify E r
    refine ⟨F,ok,by omega,?_,flat⟩
    have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    funext x; apply Bool.eq_iff_iff.mpr
    change F.eval (List.ofFn x) = true ↔ _
    rw [eval,old,sem,cover x]; change _ ↔ _ ∨ (_ ∧ Hits B x); simp [empty,Hits]

end Singleton3700

namespace Solve3700
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core WireTheory
open Exchange3700 Prune3700 Cover3700 Restore3700 Unique3700 DirectLarge3700 Two3700 TwoOr3700 Singleton3700
variable {n g : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma solve (s : Fin n → Bool) (bip : ∀ u v, G.Adj u v → s u ≠ s v) (c4 : NoFourCycle G)
    (least : IsLeastAO G C) (fixed : IsLiftFixedPoint G C) (form : TopForm G C)
    (live : ∀ k<C.size, InOutputCone n C k) (units : ∀ v : Fin n, gateVal n C g (PEqualNP.SplitCount.unitInput v) = false)
    (hg : g<C.size) (ag : (gateAt C g).op = GateOp.and) (dirty : ¬ BelowF G C g)
    (unique : ∀ i<C.size, (gateAt C i).op = GateOp.and → i≠g → BelowF G C i) : Goal G C := by
  classical
  obtain ⟨a,b,ins,na,nb,_,_⟩ := dirty_rectangle_at least.1 hg ag form unique units
  by_cases big : ∀ w∈(gateAt C g).inputs, 1<(R n C w).card
  case neg =>
    apply singleton_operand least.1 least.2.1 form hg ag dirty unique units (live g hg) c4
    push Not at big; obtain ⟨w,mw,small⟩ := big
    refine ⟨w,mw,le_antisymm small (Finset.card_pos.mpr ?_)⟩
    simp only [ins,List.mem_cons,List.not_mem_nil,or_false] at mw; rcases mw with rfl | rfl <;> assumption
  let T := (Finset.range C.size).filter (charged n g C)
  have mg : g∈T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg,.inl rfl⟩
  have paid : 2≤T.card := two_credits least.2.1 (live g hg) dirty
  obtain ⟨j,jt,jg⟩ : ∃ j∈T,j≠g := by
    by_contra! h; have h1 : T.card≤1 := Finset.card_le_one.mpr (fun t ht i hi => (h t ht).trans (h i hi).symm); omega
  have data {t : ℕ} (m : t∈T) (e : t≠g) : t<C.size ∧ n+g∈(gateAt C t).inputs :=
    ⟨Finset.mem_range.mp (Finset.mem_filter.mp m).1,Or.resolve_left (Finset.mem_filter.mp m).2 e⟩
  obtain ⟨hj,mj⟩ := data jt jg
  by_cases only : ∀ i<C.size, n+g ∈ (gateAt C i).inputs → i=j
  · rcases least.1.1 _ (gate_mem hj) with aj | oj
    · obtain ⟨p,q,hins⟩ := inputs_two least.1 hj
      have m := mj; simp only [hins,List.mem_cons,List.not_mem_nil,or_false] at m
      rcases m with rfl | rfl
      · exact direct_small_centres least.1 least.2.1 form hg ag dirty unique units live c4 s bip hj aj only (q:=q) (by rw [hins]) (.inl big)
      · exact direct_small_centres least.1 least.2.1 form hg ag dirty unique units live c4 s bip hj aj only (q:=p) (by rw [hins]; exact List.Perm.swap _ _ []) (.inl big)
    · exact single_or least fixed live form hg ag dirty unique units c4 ⟨s,bip⟩ hj oj mj only
  push Not at only; obtain ⟨k,hk,mk,kj⟩ := only
  by_cases enough : 4≤T.card
  · exact large_sides least.1 least.2.1 form hg ag dirty unique units c4 big enough
  have gj : g<j := by have := least.1.2.1 j hj _ mj; omega
  have gk : g<k := by have := least.1.2.1 k hk _ mk; omega
  have only2 (t : ℕ) (ht : t<C.size) (mt : n+g∈(gateAt C t).inputs) : t=j ∨ t=k := by
    by_contra! h
    have gt : g<t := by have := least.1.2.1 t ht _ mt; omega
    have include4 : ({g,j,k,t} : Finset ℕ) ⊆ T := by
      intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact mg
      · exact jt
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,.inr mk⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht,.inr mt⟩
    apply enough; simpa [Finset.card_insert_of_notMem,Nat.ne_of_lt gj,Nat.ne_of_lt gk,Nat.ne_of_lt gt,Ne.symm kj,Ne.symm h.1,Ne.symm h.2] using Finset.card_le_card include4
  rcases least.1.1 _ (gate_mem hj) with aj | oj
  · exact two_with_and least form live hg ag dirty unique units c4 big hj aj mj hk kj mk
  rcases least.1.1 _ (gate_mem hk) with ak | ok
  · exact two_with_and least form live hg ag dirty unique units c4 big hk ak mk hj kj.symm mj
  exact two_or least fixed live form hg ag dirty unique units s bip c4 big (fun t ht mt => (only2 t ht mt).elim (fun e => e ▸ oj) (fun e => e ▸ ok)) only2

end Solve3700

end PEqualNP.Outside.L_meta_3700_aux

theorem PEqualNP.Outside.L_meta_3700 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.Core.IsLiftFixedPoint G C →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
  (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) →
  g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
    PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    ∀ i < D.gates.length, ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ¬ PEqualNP.EdgeOwnership.InCone n D i j := by
  intro n G inst C s g bip c4 least fixed operands live units hg ag dirty unique
  exact PEqualNP.Outside.L_meta_3700_aux.Solve3700.solve s bip c4 least fixed
    (PEqualNP.Outside.L_meta_3700_aux.Exchange3700.topForm_of_fixed least.1 fixed live operands)
    live (units g hg ag) hg ag dirty unique
