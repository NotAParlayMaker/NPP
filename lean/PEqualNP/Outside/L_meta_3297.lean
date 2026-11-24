import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3297_aux

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

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩


open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

open PEqualNP.FactorSubst

def fsub (n c : ℕ) (sigma : ℕ → ℕ) (r i : ℕ) : ℕ := if i = n + c then sigma r else i

lemma sub_len (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).gates.length = C.gates.length := by
  simp [substReads]

lemma sub_gateAt (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (r : ℕ) :
    gateAt (substReads C n c sigma) r =
      ⟨(gateAt C r).op, (gateAt C r).inputs.map (fsub n c sigma r)⟩ := by
  unfold gateAt substReads fsub
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases h : C.gates[r]? <;> simp

lemma mem_readers {n : ℕ} {C : Circuit} {c k : ℕ} (hk : k < C.gates.length)
    (h : n + c ∈ (gateAt C k).inputs) : k ∈ PEqualNP.TopForm.readers n C c := by
  unfold PEqualNP.TopForm.readers
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, h⟩

lemma orC_mem {n : ℕ} {C : Circuit} {c h : ℕ} :
    h ∈ orClosure n C c ↔ h < C.gates.length ∧ h ≠ c ∧ OrReaches n C (n + h) c := by
  unfold orClosure
  rw [Finset.mem_filter, Finset.mem_range]

lemma orC_gt {n : ℕ} {C : Circuit} {c h : ℕ} (hh : h ∈ orClosure n C c) : c < h := by
  obtain ⟨_, hne, hr⟩ := orC_mem.mp hh
  have := orStep_le (orReaches_reach c _ hr).1
  omega

lemma orC_or {n : ℕ} {C : Circuit} {c h : ℕ} (hh : h ∈ orClosure n C c) :
    (gateAt C h).op = GateOp.or := by
  obtain ⟨_, hne, hr⟩ := orC_mem.mp hh
  rcases ((orReaches_iff n C h c).mp hr).2 with h1 | ⟨hop, _⟩
  · exact absurd h1.symm hne
  · exact hop

lemma reach_self {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩

lemma reach_val {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w g : ℕ}
    (hr : OrReaches n C w g) (hv : val C x (n + g) = true) : val C x w = true :=
  orStep_up hx (orReaches_reach g w hr).1 hv

lemma ins_reach {n : ℕ} {C : Circuit} {c w : ℕ} (hc : c < C.gates.length)
    (hw : w ∈ insert c (orClosure n C c)) : OrReaches n C (n + w) c := by
  rcases Finset.mem_insert.mp hw with rfl | h
  · exact reach_self hc
  · exact (orC_mem.mp h).2.2

lemma sub_mono {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ} {x : List Bool}
    (hx : x.length = n) (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ w, val C x w = true → val (substReads C n c sigma) x w = true := by
  have hab : a < n + c ∧ b < n + c :=
    ⟨hAO.2.1 c hc a (by simp [hcin]), hAO.2.1 c hc b (by simp [hcin])⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · rw [val_input hx hw] at hv; rw [val_input hx hw]; exact hv
    by_cases hlen : n + C.gates.length ≤ w
    · rw [val_ge hx hlen] at hv; cases hv
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hk' : k < (substReads C n c sigma).gates.length := by rw [sub_len]; exact hk
    rw [val_gate hx hk] at hv
    rw [val_gate hx hk', sub_gateAt]
    simp only [List.map_map]
    have hop := hAO.1 _ (gateAt_mem hk)
    have key := opMono_imp _ hop (gateAt C k).inputs
      (fun i => if i < n + k then val C x i else false)
      ((fun i => if i < n + k then val (substReads C n c sigma) x i else false) ∘
        fsub n c sigma k) ?_ hv
    · exact key
    intro i hi
    have hilt : i < n + k := hAO.2.1 k hk i hi
    simp only [Function.comp_apply, if_pos hilt]
    intro hvi
    unfold fsub
    by_cases hic : i = n + c
    · subst hic
      rw [if_pos rfl]
      have hrd : k ∈ PEqualNP.TopForm.readers n C c := mem_readers hk hi
      rw [val_and hx hc hcop, hcin] at hvi
      have hva := (hvi a (by simp)).2
      have hvb := (hvi b (by simp)).2
      have hsl : sigma k < n + k := by rcases hsig k hrd with h | h <;> omega
      rw [if_pos hsl]
      rcases hsig k hrd with h | h
      · rw [h]; exact ih a (by omega) hva
      · rw [h]; exact ih b (by omega) hvb
    · rw [if_neg hic, if_pos hilt]; exact ih i hilt hvi

lemma sub_eq {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ} (z : Fin n → Bool)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcop : (gateAt C c).op = GateOp.and) (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (hH2 : ∀ g ∈ frontier n C c, (gateAt C g).op = GateOp.and → ∀ u y : ℕ,
      ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
      (∃ w ∈ insert c (orClosure n C c), u = n + w) →
      (∀ w' ∈ insert c (orClosure n C c), y ≠ n + w') ∧
        ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ OrReaches n C u r) →
          (sigma r = b → val C (List.ofFn z) y = true → val C (List.ofFn z) a = true) ∧
          (sigma r = a → val C (List.ofFn z) y = true → val C (List.ofFn z) b = true)) :
    ∀ w, ((¬ ∃ h ∈ orClosure n C c, w = n + h) →
        val (substReads C n c sigma) (List.ofFn z) w = val C (List.ofFn z) w) ∧
      (val (substReads C n c sigma) (List.ofFn z) w = true →
        val C (List.ofFn z) w = true ∨ ∃ r ∈ PEqualNP.TopForm.readers n C c,
          OrReaches n C w r ∧ val C (List.ofFn z) (sigma r) = true) := by
  have hx : (List.ofFn z).length = n := by simp
  have hab : a < n + c ∧ b < n + c :=
    ⟨hAO.2.1 c hc a (by simp [hcin]), hAO.2.1 c hc b (by simp [hcin])⟩
  have hvc : val C (List.ofFn z) a = true → val C (List.ofFn z) b = true →
      val C (List.ofFn z) (n + c) = true := by
    intro h1 h2
    rw [val_and hx hc hcop, hcin]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨hab.1, h1⟩
    · exact ⟨hab.2, h2⟩
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  by_cases hw : w < n
  · have e : val (substReads C n c sigma) (List.ofFn z) w = val C (List.ofFn z) w := by
      rw [val_input hx hw, val_input hx hw]
    exact ⟨fun _ => e, fun h => Or.inl (e ▸ h)⟩
  by_cases hlen : n + C.gates.length ≤ w
  · have e : val (substReads C n c sigma) (List.ofFn z) w = val C (List.ofFn z) w := by
      rw [val_ge hx hlen, val_ge hx (by rw [sub_len]; exact hlen)]
    exact ⟨fun _ => e, fun h => Or.inl (e ▸ h)⟩
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hk : k < C.gates.length := by omega
  have hk' : k < (substReads C n c sigma).gates.length := by rw [sub_len]; exact hk
  have hEab : ∀ s, (s = a ∨ s = b) → s < n + k →
      val (substReads C n c sigma) (List.ofFn z) s = val C (List.ofFn z) s := by
    intro s hs hsk
    apply (ih s hsk).1
    rintro ⟨h, hh, rfl⟩
    have := orC_gt hh
    rcases hs with hs | hs <;> omega
  by_cases hO : k ∈ orClosure n C c
  · refine ⟨fun hn => absurd ⟨k, hO, rfl⟩ hn, ?_⟩
    intro hv'
    have hop := orC_or hO
    have hop' : (gateAt (substReads C n c sigma) k).op = GateOp.or := by
      rw [sub_gateAt]; exact hop
    obtain ⟨i', hi', hlt', hvi'⟩ := (val_or hx hk' hop').mp hv'
    rw [sub_gateAt] at hi'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi'
    have hilt : i < n + k := hAO.2.1 k hk i hi
    unfold fsub at hlt' hvi'
    by_cases hic : i = n + c
    · rw [if_pos hic] at hlt' hvi'
      subst hic
      have hrd : k ∈ PEqualNP.TopForm.readers n C c := mem_readers hk hi
      right
      refine ⟨k, hrd, reach_self hk, ?_⟩
      rw [← hEab (sigma k) (hsig k hrd) hlt']; exact hvi'
    · rw [if_neg hic] at hlt' hvi'
      rcases (ih i hilt).2 hvi' with h1 | ⟨r, hr, hreach, hvr⟩
      · left; exact (val_or hx hk hop).mpr ⟨i, hi, hilt, h1⟩
      · right
        exact ⟨r, hr, (orReaches_iff n C k r).mpr ⟨hk, Or.inr ⟨hop, i, hi, hilt, hreach⟩⟩, hvr⟩
  · suffices e : val (substReads C n c sigma) (List.ofFn z) (n + k) = val C (List.ofFn z) (n + k) by
      exact ⟨fun _ => e, fun h => Or.inl (e ▸ h)⟩
    have hop := hAO.1 _ (gateAt_mem hk)
    have hlen2 := hAO.2.2 _ (gateAt_mem hk)
    by_cases hfr : k ∈ frontier n C c
    · obtain ⟨_, hne, _, w0, hw0, hin0⟩ := Finset.mem_filter.mp hfr
      have hand : (gateAt C k).op = GateOp.and := by
        rcases hop with h | h
        · exact h
        · exfalso
          have hlt0 := hAO.2.1 k hk _ hin0
          have hr : OrReaches n C (n + k) c :=
            (orReaches_iff n C k c).mpr ⟨hk, Or.inr ⟨h, n + w0, hin0, hlt0, ins_reach hc hw0⟩⟩
          exact hO (orC_mem.mpr ⟨hk, hne, hr⟩)
      obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
      obtain ⟨u, y, hord, hu⟩ : ∃ u y, ((gateAt C k).inputs = [u, y] ∨
          (gateAt C k).inputs = [y, u]) ∧ ∃ w ∈ insert c (orClosure n C c), u = n + w := by
        rw [hpq] at hin0
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin0
        rcases hin0 with h | h
        · exact ⟨p, q, Or.inl hpq, w0, hw0, h.symm⟩
        · exact ⟨q, p, Or.inr hpq, w0, hw0, h.symm⟩
      obtain ⟨hy, hrr⟩ := hH2 k hfr hand u y hord hu
      have hmem : ∀ i, i ∈ (gateAt C k).inputs ↔ i = u ∨ i = y := by
        intro i
        rcases hord with h | h <;> rw [h] <;> simp <;> tauto
      have huin : u ∈ (gateAt C k).inputs := (hmem u).mpr (Or.inl rfl)
      have hyin : y ∈ (gateAt C k).inputs := (hmem y).mpr (Or.inr rfl)
      have hult := hAO.2.1 k hk u huin
      have hylt := hAO.2.1 k hk y hyin
      have hyc : y ≠ n + c := hy c (Finset.mem_insert_self _ _)
      have hyO : ¬ ∃ h ∈ orClosure n C c, y = n + h := by
        rintro ⟨h, hh, e⟩; exact hy h (Finset.mem_insert_of_mem hh) e
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hv'
        have hall := (val_and hx hk' (by rw [sub_gateAt]; exact hand)).mp hv'
        rw [sub_gateAt] at hall
        have hy' := (hall (fsub n c sigma k y) (List.mem_map_of_mem hyin)).2
        unfold fsub at hy'
        rw [if_neg hyc, (ih y hylt).1 hyO] at hy'
        have hu' := (hall (fsub n c sigma k u) (List.mem_map_of_mem huin))
        have hU : val C (List.ofFn z) u = true ∨ ∃ r ∈ PEqualNP.TopForm.readers n C c,
            (r = k ∨ OrReaches n C u r) ∧ val C (List.ofFn z) (sigma r) = true := by
          unfold fsub at hu'
          by_cases huc : u = n + c
          · rw [if_pos huc] at hu'
            have hrd : k ∈ PEqualNP.TopForm.readers n C c := mem_readers hk (huc ▸ huin)
            right
            refine ⟨k, hrd, Or.inl rfl, ?_⟩
            rw [← hEab (sigma k) (hsig k hrd) hu'.1]; exact hu'.2
          · rw [if_neg huc] at hu'
            rcases (ih u hult).2 hu'.2 with h1 | ⟨r, hr, hreach, hvr⟩
            · exact Or.inl h1
            · exact Or.inr ⟨r, hr, Or.inr hreach, hvr⟩
        have hvu : val C (List.ofFn z) u = true := by
          rcases hU with h1 | ⟨r, hr, hr', hvr⟩
          · exact h1
          · obtain ⟨w1, hw1, rfl⟩ := hu
            apply reach_val hx (ins_reach hc hw1)
            obtain ⟨hb, ha⟩ := hrr r hr hr'
            rcases hsig r hr with e | e
            · rw [e] at hvr; exact hvc hvr (ha e hy')
            · rw [e] at hvr; exact hvc (hb e hy') hvr
        rw [val_and hx hk hand]
        intro i hi
        rcases (hmem i).mp hi with rfl | rfl
        · exact ⟨hult, hvu⟩
        · exact ⟨hylt, hy'⟩
      · exact sub_mono hx hAO hc hcop hcin hsig _
    · have hgood : ∀ i ∈ (gateAt C k).inputs, i ≠ n + c ∧ ¬ ∃ h ∈ orClosure n C c, i = n + h := by
        intro i hi
        have hilt := hAO.2.1 k hk i hi
        by_cases hkc : k = c
        · constructor
          · omega
          · rintro ⟨h, hh, rfl⟩; have := orC_gt hh; omega
        · constructor
          · rintro rfl
            exact hfr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkc, hO, c,
              Finset.mem_insert_self _ _, hi⟩)
          · rintro ⟨h, hh, rfl⟩
            exact hfr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkc, hO, h,
              Finset.mem_insert_of_mem hh, hi⟩)
      rw [val_gate hx hk', val_gate hx hk, sub_gateAt]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      obtain ⟨h1, h2⟩ := hgood i hi
      have hilt := hAO.2.1 k hk i hi
      simp only [Function.comp_apply, fsub, if_neg h1, if_pos hilt]
      exact (ih i hilt).1 h2

lemma fsub_ne {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    {j : ℕ} (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) :
    fsub n c sigma j i ≠ n + c := by
  have hab : a < n + c ∧ b < n + c :=
    ⟨hAO.2.1 c hc a (by simp [hcin]), hAO.2.1 c hc b (by simp [hcin])⟩
  unfold fsub
  by_cases hic : i = n + c
  · rw [if_pos hic]
    subst hic
    rcases hsig j (mem_readers hj hi) with h | h <;> omega
  · rw [if_neg hic]; exact hic

lemma no_cone_c {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ j, ¬ InCone n (substReads C n c sigma) c j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro h
  obtain ⟨hjl, k, hkj, hin, hrest⟩ := (inCone_iff n _ c j).mp h
  rw [sub_len] at hjl
  rw [sub_gateAt] at hin
  obtain ⟨i0, hi0, he⟩ := List.mem_map.mp hin
  rcases hrest with rfl | hrest
  · exact fsub_ne hAO hc hcin hsig hjl hi0 he
  · exact ih k hkj hrest

lemma cone_sub {n : ℕ} {C : Circuit} {c a b : ℕ} {sigma : ℕ → ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hc : c < C.gates.length)
    (hcin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ j i, InCone n (substReads C n c sigma) i j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro i h
  obtain ⟨hjl, k, hkj, hin, hrest⟩ := (inCone_iff n _ i j).mp h
  rw [sub_len] at hjl
  rw [sub_gateAt] at hin
  obtain ⟨i0, hi0, he⟩ := List.mem_map.mp hin
  have hrest' : i = k ∨ InCone n C i k := hrest.imp id (ih k hkj i)
  unfold fsub at he
  by_cases hic : i0 = n + c
  · rw [if_pos hic] at he
    subst hic
    have hrd := mem_readers hjl hi0
    have hkc : n + k ∈ (gateAt C c).inputs := by
      rw [hcin]; rcases hsig j hrd with h | h <;> rw [← he, h] <;> simp
    have hklt : k < c := by have := hAO.2.1 c hc _ hkc; omega
    have hcj : c < j := by have := hAO.2.1 j hjl _ hi0; omega
    rw [inCone_iff]
    refine ⟨hjl, c, hcj, hi0, Or.inr ?_⟩
    rw [inCone_iff]
    exact ⟨hc, k, hklt, hkc, hrest'⟩
  · rw [if_neg hic] at he
    subst he
    rw [inCone_iff]
    exact ⟨hjl, k, hkj, hi0, hrest'⟩

lemma mem_live {n : ℕ} {C : Circuit} {j : ℕ} : j ∈ liveGates n C ↔
    j < C.gates.length ∧ n ≤ C.output ∧ (j = C.output - n ∨ InCone n C j (C.output - n)) := by
  unfold liveGates
  rw [Finset.mem_filter, Finset.mem_range]

end PEqualNP.Outside.L_meta_3297_aux

theorem PEqualNP.Outside.L_meta_3297 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  intro n C c a b sigma hAO hc hcop hcin hsig hH2 _ hout hlive
  refine ⟨?_, ?_⟩
  · intro k _ _ hkO z
    have hE := (PEqualNP.Outside.L_meta_3297_aux.sub_eq z hAO hc hcop hcin hsig
      (fun g hg hop u y h1 h2 =>
        let hh := hH2 g hg hop u y h1 h2
        ⟨hh.1, fun r hr hr' => ⟨fun e => (hh.2 r hr hr').1 e z,
          fun e => (hh.2 r hr hr').2 e z⟩⟩) (n + k)).1
    exact hE (by
      rintro ⟨h, hh, e⟩
      have : h = k := by omega
      subst this
      exact hkO hh)
  · have hsub : PEqualNP.FactorSubst.liveGates n (PEqualNP.FactorSubst.substReads C n c sigma) ⊆
        (PEqualNP.FactorSubst.liveGates n C).erase c := by
      intro j hj
      obtain ⟨hjl, hno, hj2⟩ := PEqualNP.Outside.L_meta_3297_aux.mem_live.mp hj
      rw [PEqualNP.Outside.L_meta_3297_aux.sub_len] at hjl
      have hjne : j ≠ c := by
        intro hjc
        rw [hjc] at hj2
        rcases hj2 with e | e
        · exact hout c (Finset.mem_insert_self _ _) (by
            have : (PEqualNP.FactorSubst.substReads C n c sigma).output = C.output := rfl
            omega)
        · exact PEqualNP.Outside.L_meta_3297_aux.no_cone_c hAO hc hcin hsig _ e
      refine Finset.mem_erase.mpr ⟨hjne, ?_⟩
      exact PEqualNP.Outside.L_meta_3297_aux.mem_live.mpr ⟨hjl, hno,
        hj2.imp id (PEqualNP.Outside.L_meta_3297_aux.cone_sub hAO hc hcin hsig _ j)⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hlive] at h1
    have h2 := Finset.card_pos.mpr ⟨c, hlive⟩
    unfold PEqualNP.FactorSubst.liveSize
    omega
