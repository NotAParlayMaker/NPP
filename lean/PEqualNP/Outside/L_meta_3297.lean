import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3297

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge

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

def wv (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = wv C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    wv C x u = x.getD u false := by
  unfold wv; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : wv C x u = false := by
  unfold wv; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    wv C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then wv C x i else false) := by
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
    wv C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ wv C x i = true := by
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
    wv C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ wv C x i = true := by
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


lemma orReaches_le {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ k, OrReaches n C (n + k) g → g ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hr
    rcases (orReaches_iff n C k g).mp hr with ⟨_, heq | ⟨_, i, _, hlt, hri⟩⟩
    · omega
    · have hn : n ≤ i := hri.1
      obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      have := ih j (by omega) hri
      omega

lemma orReaches_val {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) (g : ℕ) :
    ∀ k, OrReaches n C (n + k) g → wv C x (n + g) = true → wv C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hr hg
    rcases (orReaches_iff n C k g).mp hr with ⟨hk, heq | ⟨hop, i, hi, hlt, hri⟩⟩
    · rw [← heq]; exact hg
    · have hn : n ≤ i := hri.1
      obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      exact (val_or hx hk hop).mpr ⟨n + j, hi, hlt, ih j (by omega) hri hg⟩

lemma subst_length (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (PEqualNP.FactorSubst.substReads C n c sigma).gates.length = C.gates.length := by
  simp [PEqualNP.FactorSubst.substReads]

lemma subst_gateAt (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (k : ℕ) :
    gateAt (PEqualNP.FactorSubst.substReads C n c sigma) k =
      ⟨(gateAt C k).op, (gateAt C k).inputs.map fun i => if i = n + c then sigma k else i⟩ := by
  unfold gateAt PEqualNP.FactorSubst.substReads
  simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  cases C.gates[k]? <;> simp

lemma two_iff (l : List ℕ) (u y : ℕ) (h : l = [u, y] ∨ l = [y, u]) (P : ℕ → Prop) :
    (∀ i ∈ l, P i) ↔ P u ∧ P y := by
  rcases h with rfl | rfl <;> simp [and_comm]

theorem sem (n : ℕ) (C C' : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAO : AndOrOnly C) (hRB : ReadsBack n C) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hc : c < C.gates.length) (hcop : (gateAt C c).op = GateOp.and)
    (hcin : (gateAt C c).inputs = [a, b])
    (hlen : C'.gates.length = C.gates.length)
    (hgate : ∀ k, gateAt C' k = ⟨(gateAt C k).op,
      (gateAt C k).inputs.map fun i => if i = n + c then sigma k else i⟩)
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b)
    (hfr : ∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (gateAt C g).op = GateOp.and →
      ∀ u y : ℕ, ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
      (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) →
      (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧
      ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ OrReaches n C u r) →
        (sigma r = b → ∀ x : Fin n → Bool, wireVal n C y x = true → wireVal n C a x = true) ∧
        (sigma r = a → ∀ x' : Fin n → Bool, wireVal n C y x' = true → wireVal n C b x' = true))
    (z : Fin n → Bool) :
    ∀ k, (k ∉ PEqualNP.FactorSubst.orClosure n C c →
        wv C' (List.ofFn z) (n + k) = wv C (List.ofFn z) (n + k)) ∧
      (k ∈ PEqualNP.FactorSubst.orClosure n C c →
        (wv C (List.ofFn z) (n + k) = true → wv C' (List.ofFn z) (n + k) = true) ∧
        (wv C' (List.ofFn z) (n + k) = true → wv C (List.ofFn z) (n + k) = true ∨
          ∃ r ∈ PEqualNP.TopForm.readers n C c, OrReaches n C (n + k) r ∧
            wv C (List.ofFn z) (sigma r) = true)) := by
  have hx : (List.ofFn z).length = n := by simp
  set x := List.ofFn z with hxdef
  set O := PEqualNP.FactorSubst.orClosure n C c with hOdef
  have memO : ∀ k, k ∈ O ↔ k < C.gates.length ∧ k ≠ c ∧ OrReaches n C (n + k) c := by
    intro k; simp [hOdef, PEqualNP.FactorSubst.orClosure]
  have memR : ∀ k, k ∈ PEqualNP.TopForm.readers n C c ↔
      k < C.gates.length ∧ n + c ∈ (gateAt C k).inputs := by
    intro k; simp [PEqualNP.TopForm.readers]
  have memF : ∀ k, k ∈ PEqualNP.FactorSubst.frontier n C c ↔ k < C.gates.length ∧ k ≠ c ∧
      k ∉ O ∧ ∃ w ∈ insert c O, n + w ∈ (gateAt C k).inputs := by
    intro k
    simp only [PEqualNP.FactorSubst.frontier, Finset.mem_filter, Finset.mem_range, hOdef]
  have Ogt : ∀ k ∈ O, c < k := by
    intro k hk
    obtain ⟨_, hne, hr⟩ := (memO k).mp hk
    have := orReaches_le c k hr
    omega
  have ha : a < n + c := hRB c hc a (by rw [hcin]; simp)
  have hb : b < n + c := hRB c hc b (by rw [hcin]; simp)
  have hvc : wv C x (n + c) = true ↔ wv C x a = true ∧ wv C x b = true := by
    rw [val_and hx hc hcop, hcin]
    simp [ha, hb]
  have hrc : OrReaches n C (n + c) c := (orReaches_iff n C c c).mpr ⟨hc, Or.inl rfl⟩
  have reachI : ∀ w ∈ insert c O, OrReaches n C (n + w) c := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hrc
    · exact ((memO w).mp hw).2.2
  have sigLt : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r < n + c := by
    intro r hr
    rcases hsig r hr with h | h <;> rw [h] <;> omega
  have lowNotO : ∀ i, i < n + c → ∀ w ∈ O, i ≠ n + w := by
    intro i hi w hw
    have := Ogt w hw
    omega
  have sigVal : ∀ r ∈ PEqualNP.TopForm.readers n C c,
      wv C x (n + c) = true → wv C x (sigma r) = true := by
    intro r hr h
    rcases hsig r hr with e | e <;> rw [e] <;> [exact (hvc.mp h).1; exact (hvc.mp h).2]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  have weq : ∀ i, i < n + k → (∀ w ∈ O, i ≠ n + w) → wv C' x i = wv C x i := by
    intro i hi hO
    by_cases hin : i < n
    · rw [val_input hx hin, val_input hx hin]
    · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
      exact (ih j (by omega)).1 (fun hj => hO j hj rfl)
  by_cases hk : k < C.gates.length
  swap
  · have hkO : k ∉ O := fun h => hk ((memO k).mp h).1
    refine ⟨fun _ => ?_, fun h => absurd h hkO⟩
    rw [val_ge hx (by omega), val_ge hx (by omega)]
  have hkC' : k < C'.gates.length := by omega
  have hgk' := hgate k
  have caseA : (∀ i ∈ (gateAt C k).inputs, ∀ w ∈ insert c O, i ≠ n + w) →
      wv C' x (n + k) = wv C x (n + k) := by
    intro hno
    rw [val_gate hx hkC', val_gate hx hk, hgk']
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hne : i ≠ n + c := hno i hi c (Finset.mem_insert_self _ _)
    have hlt : i < n + k := hRB k hk i hi
    simp only [Function.comp_apply, if_neg hne, if_pos hlt]
    exact weq i hlt (fun w hw => hno i hi w (Finset.mem_insert_of_mem hw))
  by_cases hkO : k ∈ O
  · -- k is an OR gate of the closure
    refine ⟨fun h => absurd hkO h, fun _ => ?_⟩
    obtain ⟨_, hkc, hrk⟩ := (memO k).mp hkO
    have hop : (gateAt C k).op = GateOp.or := by
      rcases (orReaches_iff n C k c).mp hrk with ⟨_, heq | ⟨hop, _⟩⟩
      · exact absurd heq.symm hkc
      · exact hop
    have hop' : (gateAt C' k).op = GateOp.or := by rw [hgk']; exact hop
    constructor
    · intro h
      obtain ⟨i, hi, hlt, hv⟩ := (val_or hx hk hop).mp h
      refine (val_or hx hkC' hop').mpr ⟨if i = n + c then sigma k else i,
        by rw [hgk']; exact List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
      by_cases hic : i = n + c
      · have hkR : k ∈ PEqualNP.TopForm.readers n C c := (memR k).mpr ⟨hk, hic ▸ hi⟩
        have hsl := sigLt k hkR
        rw [if_pos hic]
        refine ⟨by omega, ?_⟩
        rw [weq _ (by omega) (lowNotO _ hsl)]
        exact sigVal k hkR (hic ▸ hv)
      · rw [if_neg hic]
        refine ⟨hlt, ?_⟩
        by_cases hiO : ∃ w ∈ O, i = n + w
        · obtain ⟨w, hw, rfl⟩ := hiO
          exact ((ih w (by omega)).2 hw).1 hv
        · simp only [not_exists, not_and] at hiO
          rw [weq i hlt hiO]; exact hv
    · intro h
      obtain ⟨i', hi', hlt', hv'⟩ := (val_or hx hkC' hop').mp h
      rw [hgk'] at hi'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi'
      have hlt : i < n + k := hRB k hk i hi
      by_cases hic : i = n + c
      · have hkR : k ∈ PEqualNP.TopForm.readers n C c := (memR k).mpr ⟨hk, hic ▸ hi⟩
        have hsl := sigLt k hkR
        simp only [if_pos hic] at hv' hlt'
        rw [weq _ (by omega) (lowNotO _ hsl)] at hv'
        exact Or.inr ⟨k, hkR, (orReaches_iff n C k k).mpr ⟨hk, Or.inl rfl⟩, hv'⟩
      · simp only [if_neg hic] at hv' hlt'
        by_cases hiO : ∃ w ∈ O, i = n + w
        · obtain ⟨w, hw, rfl⟩ := hiO
          rcases ((ih w (by omega)).2 hw).2 hv' with h1 | ⟨r, hr, hrr, hsv⟩
          · exact Or.inl ((val_or hx hk hop).mpr ⟨n + w, hi, hlt, h1⟩)
          · exact Or.inr ⟨r, hr, (orReaches_iff n C k r).mpr
              ⟨hk, Or.inr ⟨hop, n + w, hi, hlt, hrr⟩⟩, hsv⟩
        · simp only [not_exists, not_and] at hiO
          rw [weq i hlt hiO] at hv'
          exact Or.inl ((val_or hx hk hop).mpr ⟨i, hi, hlt, hv'⟩)
  refine ⟨fun _ => ?_, fun h => absurd h hkO⟩
  by_cases hkF : k ∈ PEqualNP.FactorSubst.frontier n C c
  swap
  · apply caseA
    intro i hi w hw
    by_cases hkc : k = c
    · subst hkc
      have hlt : i < n + k := hRB k hk i hi
      rcases Finset.mem_insert.mp hw with rfl | hw
      · omega
      · exact lowNotO i hlt w hw
    · intro heq
      exact hkF ((memF k).mpr ⟨hk, hkc, hkO, w, hw, heq ▸ hi⟩)
  obtain ⟨_, hkc, _, w, hw, hwin⟩ := (memF k).mp hkF
  have hand : (gateAt C k).op = GateOp.and := by
    rcases hAO _ (gateAt_mem hk) with h | h
    · exact h
    · exfalso
      apply hkO
      refine (memO k).mpr ⟨hk, hkc, (orReaches_iff n C k c).mpr ⟨hk, Or.inr ⟨h, n + w, hwin,
        hRB k hk _ hwin, reachI w hw⟩⟩⟩
  have hand' : (gateAt C' k).op = GateOp.and := by rw [hgk']; exact hand
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem hk))
  obtain ⟨u, y, huy, rfl⟩ : ∃ u y, ((gateAt C k).inputs = [u, y] ∨ (gateAt C k).inputs = [y, u])
      ∧ u = n + w := by
    rw [hpq] at hwin
    rcases List.mem_pair.mp hwin with h | h
    · exact ⟨p, q, Or.inl hpq, h.symm⟩
    · exact ⟨q, p, Or.inr hpq, h.symm⟩
  obtain ⟨hy, hsr⟩ := hfr k hkF hand (n + w) y huy ⟨w, hw, rfl⟩
  have hyc : y ≠ n + c := hy c (Finset.mem_insert_self _ _)
  have hyin : y ∈ (gateAt C k).inputs := by rcases huy with h | h <;> rw [h] <;> simp
  have hyl : y < n + k := hRB k hk y hyin
  have hwl : n + w < n + k := hRB k hk _ hwin
  have hyv : wv C' x y = wv C x y := weq y hyl (fun w' hw' => hy w' (Finset.mem_insert_of_mem hw'))
  have eC : wv C x (n + k) = true ↔ wv C x (n + w) = true ∧ wv C x y = true := by
    rw [val_and hx hk hand, two_iff _ _ _ huy (fun i => i < n + k ∧ wv C x i = true)]
    simp [hyl, hwl]
  have eC' : wv C' x (n + k) = true ↔
      wv C' x (if n + w = n + c then sigma k else n + w) = true ∧
        (if n + w = n + c then sigma k else n + w) < n + k ∧ wv C x y = true := by
    rw [val_and hx hkC' hand', hgk']
    simp only [List.forall_mem_map]
    rw [two_iff _ _ _ huy (fun i => (if i = n + c then sigma k else i) < n + k ∧
      wv C' x (if i = n + c then sigma k else i) = true)]
    simp only [if_neg hyc, hyv]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, h4⟩; exact ⟨h2, h1, h4⟩
    · rintro ⟨h2, h1, h4⟩; exact ⟨⟨h1, h2⟩, hyl, h4⟩
  -- the bound: a reader with a true factor makes the old wire true
  have bound : ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = k ∨ OrReaches n C (n + w) r) →
      wv C x (sigma r) = true → wv C x y = true → wv C x (n + w) = true := by
    intro r hr hrr hs hyt
    have hcv : wv C x (n + c) = true := by
      rw [hvc]
      rcases hsig r hr with e | e
      · rw [e] at hs
        exact ⟨hs, (hsr r hr hrr).2 e z hyt⟩
      · rw [e] at hs
        exact ⟨(hsr r hr hrr).1 e z hyt, hs⟩
    exact orReaches_val hx c w (reachI w hw) hcv
  apply Bool.eq_iff_iff.mpr
  rw [eC', eC]
  rcases Finset.mem_insert.mp hw with hwc | hwO
  · subst hwc
    have hkR : k ∈ PEqualNP.TopForm.readers n C w := (memR k).mpr ⟨hk, hwin⟩
    have hsl := sigLt k hkR
    have e : (if n + w = n + w then sigma k else n + w) = sigma k := if_pos rfl
    rw [e]
    rw [weq _ (by omega) (lowNotO _ hsl)]
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨bound k hkR (Or.inl rfl) h1 h3, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨sigVal k hkR h1, by omega, h3⟩
  · have hwc : n + w ≠ n + c := by have := Ogt w hwO; omega
    simp only [if_neg hwc]
    have ihw := (ih w (by omega)).2 hwO
    constructor
    · rintro ⟨h1, _, h3⟩
      rcases ihw.2 h1 with h | ⟨r, hr, hrr, hs⟩
      · exact ⟨h, h3⟩
      · exact ⟨bound r hr (Or.inr hrr) hs h3, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨ihw.1 h1, hwl, h3⟩

theorem cone_sub (n : ℕ) (C C' : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hRB : ReadsBack n C) (hc : c < C.gates.length) (hcin : (gateAt C c).inputs = [a, b])
    (hlen : C'.gates.length = C.gates.length)
    (hgate : ∀ k, gateAt C' k = ⟨(gateAt C k).op,
      (gateAt C k).inputs.map fun i => if i = n + c then sigma k else i⟩)
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ k i, InCone n C' i k → InCone n C i k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro i h
  obtain ⟨hk', m, hmk, hmem, hrest⟩ := (inCone_iff n C' i k).mp h
  have hk : k < C.gates.length := by omega
  rw [hgate] at hmem
  obtain ⟨i0, hi0, hf⟩ := List.mem_map.mp hmem
  have hrest' : i = m ∨ InCone n C i m := by
    rcases hrest with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (ih m hmk i h1)
  by_cases hic : i0 = n + c
  · rw [if_pos hic] at hf
    have hkR : k ∈ PEqualNP.TopForm.readers n C c := by
      simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range]
      exact ⟨hk, hic ▸ hi0⟩
    have hck : n + c < n + k := hRB k hk _ (hic ▸ hi0)
    have hmc : n + m ∈ (gateAt C c).inputs := by
      rw [hcin, ← hf]; rcases hsig k hkR with e | e <;> rw [e] <;> simp
    have hmc' : n + m < n + c := hRB c hc _ hmc
    have hic' : i = m ∨ InCone n C i m := hrest'
    have h1 : InCone n C i c := (inCone_iff n C i c).mpr ⟨hc, m, by omega, hmc, hic'⟩
    exact (inCone_iff n C i k).mpr ⟨hk, c, by omega, hic ▸ hi0, Or.inr h1⟩
  · rw [if_neg hic] at hf
    exact (inCone_iff n C i k).mpr ⟨hk, m, hmk, hf ▸ hi0, hrest'⟩

theorem cone_c (n : ℕ) (C C' : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hRB : ReadsBack n C) (hc : c < C.gates.length) (hcin : (gateAt C c).inputs = [a, b])
    (hlen : C'.gates.length = C.gates.length)
    (hgate : ∀ k, gateAt C' k = ⟨(gateAt C k).op,
      (gateAt C k).inputs.map fun i => if i = n + c then sigma k else i⟩)
    (hsig : ∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ k, ¬ InCone n C' c k := by
  have ha : a < n + c := hRB c hc a (by rw [hcin]; simp)
  have hb : b < n + c := hRB c hc b (by rw [hcin]; simp)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro h
  obtain ⟨hk', m, hmk, hmem, hrest⟩ := (inCone_iff n C' c k).mp h
  rcases hrest with hcm | h1
  · subst hcm
    have hk : k < C.gates.length := by omega
    rw [hgate] at hmem
    obtain ⟨i0, hi0, hf⟩ := List.mem_map.mp hmem
    by_cases hic : i0 = n + c
    · rw [if_pos hic] at hf
      have hkR : k ∈ PEqualNP.TopForm.readers n C c := by
        simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range]
        exact ⟨hk, hic ▸ hi0⟩
      rcases hsig k hkR with e | e <;> rw [e] at hf <;> omega
    · rw [if_neg hic] at hf
      exact hic hf
  · exact ih m hmk h1

end PEqualNP.Outside.L_meta_3297

theorem PEqualNP.Outside.L_meta_3297 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  intro n C c a b sigma hAO2 hc hcop hcin hsig hfr _ hout hlive
  obtain ⟨hAO, hRB, h2⟩ := hAO2
  have hlen := PEqualNP.Outside.L_meta_3297.subst_length C n c sigma
  have hgate := PEqualNP.Outside.L_meta_3297.subst_gateAt C n c sigma
  refine ⟨?_, ?_⟩
  · intro k _ _ hkO z
    exact (PEqualNP.Outside.L_meta_3297.sem n C _ c a b sigma hAO hRB h2 hc hcop hcin hlen hgate
      hsig hfr z k).1 hkO
  · unfold PEqualNP.FactorSubst.liveSize
    have hsub : PEqualNP.FactorSubst.liveGates n (PEqualNP.FactorSubst.substReads C n c sigma) ⊆
        (PEqualNP.FactorSubst.liveGates n C).erase c := by
      intro j hj
      simp only [PEqualNP.FactorSubst.liveGates, Finset.mem_filter, Finset.mem_range] at hj
      have hout' : (PEqualNP.FactorSubst.substReads C n c sigma).output = C.output := rfl
      rw [hout', hlen] at hj
      obtain ⟨hjl, hno, hj2⟩ := hj
      have hoc : C.output - n ≠ c := by
        intro e
        exact hout c (Finset.mem_insert_self _ _) (by omega)
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hjc
        rw [hjc] at hj2
        rcases hj2 with e | e
        · exact hoc e.symm
        · exact PEqualNP.Outside.L_meta_3297.cone_c n C _ c a b sigma hRB hc hcin hlen hgate
            hsig _ e
      · simp only [PEqualNP.FactorSubst.liveGates, Finset.mem_filter, Finset.mem_range]
        refine ⟨hjl, hno, ?_⟩
        rcases hj2 with e | e
        · exact Or.inl e
        · exact Or.inr (PEqualNP.Outside.L_meta_3297.cone_sub n C _ c a b sigma hRB hc hcin hlen
            hgate hsig _ _ e)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hlive] at h1
    have h0 : 0 < (PEqualNP.FactorSubst.liveGates n C).card := Finset.card_pos.mpr ⟨c, hlive⟩
    omega
