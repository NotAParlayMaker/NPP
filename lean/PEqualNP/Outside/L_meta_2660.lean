import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2660

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

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

lemma cone_lt {n : ℕ} {C : Circuit} : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h | h⟩ := (inCone_iff n C i j).mp h
    · omega
    · have := ih k hk i h
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


open PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma no4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    (a b c d : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have e1 := G.ne_of_adj hab
  have e2 := G.ne_of_adj hbc
  have e3 := G.ne_of_adj hcd
  have e4 := G.ne_of_adj hda
  have hcyc : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
    · simp [Sym2.eq_iff, e1, e2, e3, e4, hac, hbd, Ne.symm e1, Ne.symm e2,
        Ne.symm e3, Ne.symm e4, Ne.symm hac, Ne.symm hbd]
  have h5 := hg a _ hcyc
  simp at h5

lemma mem_orIn {n : ℕ} {C : Circuit} {w : ℕ} {i : Fin n} :
    i ∈ orIn n C w ↔ (i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs := by
  simp [orIn]

lemma orIn_input {n : ℕ} {C : Circuit} {w : ℕ} (hw : w < n) {i : Fin n} :
    i ∈ orIn n C w ↔ (i : ℕ) = w := by
  rw [mem_orIn]
  constructor
  · rintro (h | ⟨k, _, hr, _⟩)
    · exact h
    · have := hr.1; omega
  · exact Or.inl

lemma orIn_gate {n : ℕ} {C : Circuit} {k : ℕ} {i : Fin n} :
    i ∈ orIn n C (n + k) ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ i ∈ orIn n C w := by
  have hi := i.isLt
  constructor
  · intro h
    rw [mem_orIn] at h
    rcases h with h | ⟨j, hj, hr, hop, hin⟩
    · omega
    · rw [orReaches_iff] at hr
      obtain ⟨hk, hr⟩ := hr
      rcases hr with rfl | ⟨hopk, w, hw, hlt, hr⟩
      · exact ⟨hk, hop, i, hin, by omega, (orIn_input hi).mpr rfl⟩
      · exact ⟨hk, hopk, w, hw, hlt, mem_orIn.mpr (Or.inr ⟨j, hj, hr, hop, hin⟩)⟩
  · rintro ⟨hk, hop, w, hw, hlt, h⟩
    rw [mem_orIn] at h ⊢
    right
    rcases h with h | ⟨j, hj, hr, hopj, hin⟩
    · refine ⟨k, hk, ?_, hop, h ▸ hw⟩
      rw [orReaches_iff]; exact ⟨hk, Or.inl rfl⟩
    · refine ⟨j, hj, ?_, hopj, hin⟩
      rw [orReaches_iff]; exact ⟨hk, Or.inr ⟨hop, w, hw, hlt, hr⟩⟩

lemma val_of_orIn {n : ℕ} {C : Circuit} {x : Fin n → Bool} {i : Fin n} (hxi : x i = true) :
    ∀ w, i ∈ orIn n C w → val C (List.ofFn x) w = true := by
  have hx : (List.ofFn x).length = n := by simp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases hw : w < n
    · have e := (orIn_input hw).mp h
      subst e
      rw [val_input hx hw]
      simpa [List.getD_eq_getElem?_getD] using hxi
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      obtain ⟨hk, hop, u, hu, hlt, h⟩ := orIn_gate.mp h
      exact (val_or hx hk hop).mpr ⟨u, hu, hlt, ih u hlt h⟩

lemma orIn_of_val {n : ℕ} {C : Circuit} (hm : Monotone2 C) {u v : Fin n} :
    ∀ w, val C (List.ofFn (pairInput u v)) w = true →
      (∀ j < C.gates.length, (w = n + j ∨ ∃ k, w = n + k ∧ InCone n C j k) →
        (gateAt C j).op = GateOp.and → val C (List.ofFn (pairInput u v)) (n + j) = false) →
      u ∈ orIn n C w ∨ v ∈ orIn n C w := by
  have hx : (List.ofFn (pairInput u v)).length = n := by simp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hand
    by_cases hw : w < n
    · rw [val_input hx hw] at h
      have h' : pairInput u v ⟨w, hw⟩ = true := by
        simpa [List.getD_eq_getElem?_getD, hw] using h
      simp only [pairInput, decide_eq_true_eq] at h'
      rcases h' with h' | h'
      · left; rw [orIn_input hw, ← h']
      · right; rw [orIn_input hw, ← h']
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k < C.gates.length
      swap
      · rw [val_ge hx (by omega)] at h; cases h
      rcases (hm _ (gateAt_mem hk)).1 with hop | hop
      · have := hand k hk (Or.inl rfl) hop
        rw [this] at h; cases h
      · have hop : (gateAt C k).op = GateOp.or := hop
        obtain ⟨p, hp, hlt, hv⟩ := (val_or hx hk hop).mp h
        have h2 := ih p hlt hv (by
          intro j hj hjp hopj
          refine hand j hj (Or.inr ⟨k, rfl, ?_⟩) hopj
          rw [inCone_iff]
          rcases hjp with e | ⟨q, e, hq⟩
          · exact ⟨hk, j, by omega, e ▸ hp, Or.inl rfl⟩
          · exact ⟨hk, q, by omega, e ▸ hp, Or.inr hq⟩)
        rcases h2 with h2 | h2
        · exact Or.inl (orIn_gate.mpr ⟨hk, hop, p, hp, hlt, h2⟩)
        · exact Or.inr (orIn_gate.mpr ⟨hk, hop, p, hp, hlt, h2⟩)

section

attribute [local instance] gateOpDecEq

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (d : ℕ)

/-- The inputs reached from `w` that are not neighbours of `u`. -/
def off (w : ℕ) (u : Fin n) : Finset (Fin n) := (orIn n C w).filter fun i => ¬ G.Adj u i

/-- The inputs reached through the small operands of gate `g`. -/
def small (g : ℕ) : Finset (Fin n) :=
  (gateAt C g).inputs.toFinset.biUnion fun w =>
    if (orIn n C w).card ≤ 2 * d + 1 then orIn n C w else ∅

/-- The possible centres of a wire that reaches many inputs. -/
def centres (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => 2 * d + 1 < (orIn n C w).card ∧ (off G C w u).card ≤ d

def prods (P Q : Finset (Fin n)) : Finset (Sym2 (Fin n)) := (P ×ˢ Q).image fun p => s(p.1, p.2)

def budget (g : ℕ) : Finset (Sym2 (Fin n)) :=
  if (gateAt C g).op = GateOp.or then
    (centres G C d (n + g)).biUnion fun u => (small (n := n) C d g).image fun v => s(u, v)
  else
    if ((orIn n C ((gateAt C g).inputs.getD 0 0)).card ≤ d + 1 ∧
        (orIn n C ((gateAt C g).inputs.getD 1 0)).card ≤ 2 * d + 1) ∨
       ((orIn n C ((gateAt C g).inputs.getD 1 0)).card ≤ d + 1 ∧
        (orIn n C ((gateAt C g).inputs.getD 0 0)).card ≤ 2 * d + 1) then
      prods (orIn n C ((gateAt C g).inputs.getD 0 0)) (orIn n C ((gateAt C g).inputs.getD 1 0))
    else ∅

lemma pow_aux : ∀ m : ℕ, (m + 6) * (2 * m + 11) ≤ 2 ^ (m + 7) ∧ 2 * (2 * m + 11) ≤ 2 ^ (m + 7) := by
  intro m
  induction m with
  | zero => norm_num
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : 2 ^ (m + 1 + 7) = 2 ^ (m + 7) * 2 := by
      rw [show m + 1 + 7 = (m + 7) + 1 from by ring, pow_succ]
    rw [e]
    refine ⟨?_, by omega⟩
    have h4 : (m + 1 + 6) * (2 * (m + 1) + 11) ≤ (m + 6) * (2 * m + 11) * 2 := by nlinarith
    omega

lemma pow_bound : ∀ d : ℕ, 2 * (2 * d + 1) ≤ 2 ^ (d + 2) ∧ (d + 1) * (2 * d + 1) ≤ 2 ^ (d + 2)
  | 0 => by norm_num
  | 1 => by norm_num
  | 2 => by norm_num
  | 3 => by norm_num
  | 4 => by norm_num
  | m + 5 => by
    obtain ⟨h1, h2⟩ := pow_aux m
    have e : 2 * (m + 5) + 1 = 2 * m + 11 := by ring
    rw [show m + 5 + 2 = m + 7 from rfl, show m + 5 + 1 = m + 6 from rfl, e]
    exact ⟨h2, h1⟩

lemma centres_card
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) (w : ℕ) :
    (centres G C d w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu u' hu'
  by_contra hne
  simp only [centres, Finset.mem_filter, Finset.mem_univ, true_and] at hu hu'
  have hsub : (orIn n C w) ⊆ ((orIn n C w).filter fun i => G.Adj u i ∧ G.Adj u' i) ∪
      (off G C w u ∪ off G C w u') := by
    intro i hi
    simp only [Finset.mem_union, off, Finset.mem_filter]
    by_cases h1 : G.Adj u i <;> by_cases h2 : G.Adj u' i <;> simp [hi, h1, h2]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((orIn n C w).filter fun i => G.Adj u i ∧ G.Adj u' i)
    (off G C w u ∪ off G C w u')
  have h3 := Finset.card_union_le (off G C w u) (off G C w u')
  have h4 : 1 < ((orIn n C w).filter fun i => G.Adj u i ∧ G.Adj u' i).card := by omega
  obtain ⟨v, hv, v', hv', hvv⟩ := Finset.one_lt_card.mp h4
  simp only [Finset.mem_filter] at hv hv'
  exact no4 G hg u v u' v' hv.2.1 hv.2.2.symm hv'.2.2 hv'.2.1.symm hne hvv

lemma small_card (hm : Monotone2 C) {g : ℕ} (hgl : g < C.gates.length) :
    (small (n := n) C d g).card ≤ 2 * (2 * d + 1) := by
  have h1 : (gateAt C g).inputs.toFinset.card ≤ 2 :=
    (List.toFinset_card_le _).trans (hm _ (gateAt_mem hgl)).2
  refine (Finset.card_biUnion_le_card_mul _ _ (2 * d + 1) ?_).trans (Nat.mul_le_mul_right _ h1)
  intro w _
  split_ifs with h
  · exact h
  · simp

lemma budget_card (hm : Monotone2 C)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
    {g : ℕ} (hgl : g < C.gates.length) : (budget G C d g).card ≤ 2 ^ (d + 2) := by
  obtain ⟨hp1, hp2⟩ := pow_bound d
  unfold budget
  split_ifs with h1 h2
  · refine le_trans (Finset.card_biUnion_le_card_mul _ _ (2 * (2 * d + 1)) ?_) ?_
    · intro u _
      exact Finset.card_image_le.trans (small_card C d hm hgl)
    · exact (Nat.mul_le_mul_right _ (centres_card G C d hg (n + g))).trans (by omega)
  · refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product]
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact (Nat.mul_le_mul h3 h4).trans hp2
    · rw [mul_comm]; exact (Nat.mul_le_mul h3 h4).trans hp2
  · simp

lemma descend {u v : Fin n} : ∀ w, v ∈ orIn n C w → 2 * d + 1 < (orIn n C w).card →
    (off G C w u).card ≤ d → ∃ g < C.gates.length, s(u, v) ∈ budget G C d g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hbig hoff
    by_cases hw : w < n
    · exfalso
      have : (orIn n C w).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro i hi j hj
        rw [orIn_input hw] at hi hj
        exact Fin.ext (by omega)
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      obtain ⟨hk, hop, p, hp, hlt, hvp⟩ := orIn_gate.mp hv
      by_cases hs : (orIn n C p).card ≤ 2 * d + 1
      · refine ⟨k, hk, ?_⟩
        unfold budget
        rw [if_pos hop, Finset.mem_biUnion]
        refine ⟨u, ?_, Finset.mem_image_of_mem _ ?_⟩
        · simp only [centres, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hbig, hoff⟩
        · rw [small, Finset.mem_biUnion]
          exact ⟨p, List.mem_toFinset.mpr hp, by rw [if_pos hs]; exact hvp⟩
      · refine ih p hlt hvp (by omega) (le_trans (Finset.card_le_card ?_) hoff)
        intro i hi
        simp only [off, Finset.mem_filter] at hi ⊢
        exact ⟨orIn_gate.mpr ⟨hk, hop, p, hp, hlt, hi.1⟩, hi.2⟩

end

lemma two_of {l : List ℕ} (hl : l.length ≤ 2) {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    l = [a, b] ∨ l = [b, a] := by
  match l, hl with
  | [], _ => simp at ha
  | [p], _ => simp at ha hb; exact (hab (ha.trans hb.symm)).elim
  | [p, q], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hab rfl).elim
  | _ :: _ :: _ :: _, h => simp at h

lemma owned {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (hm : Monotone2 C)
    (hg : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) (d k : ℕ) (u v : Fin n)
    (hown : Owns n C k u v) (D : Finset (Fin n)) (hD : D.card ≤ d) (hu : u ∉ D) (hv : v ∉ D)
    (hcl : ∀ i ∉ D, ∀ j ∉ D, gateVal n C k (pairInput i j) = true → G.Adj i j) :
    ∃ g < C.gates.length, s(u, v) ∈ budget G C d g := by
  obtain ⟨hk, hop, htrue, hno⟩ := hown
  have hlen := (hm _ (gateAt_mem hk)).2
  have hx : ∀ i j : Fin n, (List.ofFn (pairInput i j)).length = n := by intro i j; simp
  have hp1 : ∀ i j : Fin n, pairInput i j i = true := by intro i j; simp [pairInput]
  have hp2 : ∀ i j : Fin n, pairInput i j j = true := by intro i j; simp [pairInput]
  rw [gateVal_eq_val, val_and (hx u v) hk hop] at htrue
  have hlt : ∀ p ∈ (gateAt C k).inputs, p < n + k := fun p hp => (htrue p hp).1
  have hor : ∀ p ∈ (gateAt C k).inputs, u ∈ orIn n C p ∨ v ∈ orIn n C p := by
    intro p hp
    refine orIn_of_val hm p (htrue p hp).2 ?_
    intro j hj hjp hopj
    have hcone : InCone n C j k := by
      rw [inCone_iff]
      have hpl := hlt p hp
      rcases hjp with e | ⟨q, e, hq⟩
      · exact ⟨hk, j, by omega, e ▸ hp, Or.inl rfl⟩
      · exact ⟨hk, q, by omega, e ▸ hp, Or.inr hq⟩
    have hjk : j < k := by
      have hpl := hlt p hp
      by_contra hge
      rcases hjp with e | ⟨q, e, hq⟩
      · omega
      · have := cone_lt q j hq
        omega
    have := hno j hjk hcone hopj
    rwa [gateVal_eq_val] at this
  have accept : ∀ i j : Fin n, (∀ p ∈ (gateAt C k).inputs, i ∈ orIn n C p ∨ j ∈ orIn n C p) →
      gateVal n C k (pairInput i j) = true := by
    intro i j h
    rw [gateVal_eq_val, val_and (hx i j) hk hop]
    intro p hp
    refine ⟨hlt p hp, ?_⟩
    rcases h p hp with h | h
    · exact val_of_orIn (hp1 i j) p h
    · exact val_of_orIn (hp2 i j) p h
  have hex : ∀ i : Fin n, i ∉ D → ∃ p ∈ (gateAt C k).inputs, i ∉ orIn n C p := by
    intro i hi
    by_contra hcon
    push Not at hcon
    exact G.loopless.irrefl i (hcl i hi i hi (accept i i fun p hp => Or.inl (hcon p hp)))
  obtain ⟨a, ha, hua⟩ := hex u hu
  obtain ⟨b, hb, hvb⟩ := hex v hv
  have hva : v ∈ orIn n C a := (hor a ha).resolve_left hua
  have hub : u ∈ orIn n C b := (hor b hb).resolve_right hvb
  have hab : a ≠ b := by intro e; subst e; exact hua hub
  have hin := two_of hlen hb ha hab.symm
  have hmem : ∀ p ∈ (gateAt C k).inputs, p = b ∨ p = a := by
    intro p hp
    rcases hin with e | e
    · rw [e] at hp; simpa using hp
    · rw [e] at hp; simpa [or_comm] using hp
  have hbic : ∀ i ∈ orIn n C b, i ∉ D → ∀ j ∈ orIn n C a, j ∉ D → G.Adj i j := by
    intro i hi hiD j hj hjD
    refine hcl i hiD j hjD (accept i j fun p hp => ?_)
    rcases hmem p hp with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hj
  have hne : (gateAt C k).op ≠ GateOp.or := by rw [hop]; exact fun h => by cases h
  -- the product of the two sides, when both are small
  have hsmall : ((orIn n C b).card ≤ d + 1 ∧ (orIn n C a).card ≤ 2 * d + 1) ∨
      ((orIn n C a).card ≤ d + 1 ∧ (orIn n C b).card ≤ 2 * d + 1) →
      s(u, v) ∈ budget G C d k := by
    intro h
    unfold budget
    rw [if_neg hne]
    rcases hin with e | e
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [if_pos h]
      exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hub, hva⟩, rfl⟩
    · rw [e]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [if_pos h.symm]
      exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨hva, hub⟩, Sym2.eq_swap⟩
  have side : ∀ (p q : ℕ) (x y : Fin n), x ∈ orIn n C p → x ∉ D → y ∈ orIn n C q →
      (∀ i ∈ orIn n C p, i ∉ D → i = x) → (∀ j ∈ orIn n C q, j ∉ D → G.Adj x j) →
      (orIn n C p).card ≤ d + 1 ∧ (off G C q x).card ≤ d := by
    intro p q x y hxp hxD hyq h1 h2
    constructor
    · have hs : orIn n C p ⊆ insert x D := by
        intro i hi
        rw [Finset.mem_insert]
        by_cases hiD : i ∈ D
        · exact Or.inr hiD
        · exact Or.inl (h1 i hi hiD)
      have := Finset.card_le_card hs
      have := Finset.card_insert_le x D
      omega
    · refine (Finset.card_le_card ?_).trans hD
      intro i hi
      simp only [off, Finset.mem_filter] at hi
      by_contra hiD
      exact hi.2 (h2 i hi.1 hiD)
  by_cases h1 : ∀ i ∈ orIn n C b, i ∉ D → i = u
  · obtain ⟨h2, h3⟩ := side b a u v hub hu hva h1 (hbic u hub hu)
    by_cases h4 : (orIn n C a).card ≤ 2 * d + 1
    · exact ⟨k, hk, hsmall (Or.inl ⟨h2, h4⟩)⟩
    · exact descend G C d a hva (by omega) h3
  · push Not at h1
    obtain ⟨u', hu', huD', hne'⟩ := h1
    have h1 : ∀ j ∈ orIn n C a, j ∉ D → j = v := by
      intro v' hv' hvD'
      by_contra hvv
      exact no4 G hg u v u' v' (hbic u hub hu v hva hv) (hbic u' hu' huD' v hva hv).symm
        (hbic u' hu' huD' v' hv' hvD') (hbic u hub hu v' hv' hvD').symm
        (Ne.symm hne') (Ne.symm hvv)
    obtain ⟨h2, h3⟩ := side a b v u hva hv hub h1 (fun i hi hiD => (hbic i hi hiD v hva hv).symm)
    by_cases h4 : (orIn n C b).card ≤ 2 * d + 1
    · exact ⟨k, hk, hsmall (Or.inr ⟨h2, h4⟩)⟩
    · obtain ⟨g, hgl, h5⟩ := descend G C d (u := v) (v := u) b hub (by omega) h3
      exact ⟨g, hgl, by rw [Sym2.eq_swap]; exact h5⟩

end PEqualNP.Outside.L_meta_2660

open PEqualNP.Outside.L_meta_2660 in
theorem PEqualNP.Outside.L_meta_2660 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → ∀ (x7 : ℕ), ∀ x8 ⊆ x2.edgeFinset, (∀ x10 ∈ x8, ∃ (x12 : Fin x1) (x13 : Fin x1), x10 = s(x12, x13) ∧ ∃ (x14 : Fin x5.gates.length), PEqualNP.EdgeOwnership.Owns x1 x5 (↑x14) x12 x13 ∧ ∃ (x15 : Finset (Fin x1)), x15.card ≤ x7 ∧ x12 ∉ x15 ∧ x13 ∉ x15 ∧ ∀ x16 ∉ x15, ∀ x18 ∉ x15, PEqualNP.EdgeOwnership.gateVal x1 x5 (↑x14) (PEqualNP.EdgeOwnership.pairInput x16 x18) = Bool.true → x2.Adj x16 x18) → x8.card ≤ (2 : ℕ) ^ (x7 + (2 : ℕ)) * x5.size := by
  intro n G _ hg C hm d T hT h
  have hsub : T ⊆ (Finset.range C.gates.length).biUnion fun g => budget G C d g := by
    intro e he
    obtain ⟨u, v, rfl, k, hown, D, hD, hu, hv, hcl⟩ := h e he
    obtain ⟨g, hgl, hb⟩ := owned G C hm hg d k u v hown D hD hu hv hcl
    rw [Finset.mem_biUnion]
    exact ⟨g, Finset.mem_range.mpr hgl, hb⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _ (2 ^ (d + 2)) ?_).trans ?_
  · intro g hgl
    exact budget_card G C d hm hg (Finset.mem_range.mp hgl)
  · rw [Finset.card_range, mul_comm]
    exact le_rfl
